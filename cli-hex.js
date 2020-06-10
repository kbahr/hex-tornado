#!/usr/bin/env node
// Temporary demo client
// Works both in browser and node.js
const fs = require('fs')
const axios = require('axios')
const assert = require('assert')
const snarkjs = require('snarkjs')
const crypto = require('crypto')
const circomlib = require('circomlib')
const bigInt = snarkjs.bigInt
const merkleTree = require('./lib/MerkleTree')
const Web3 = require('web3')
const HDWalletProvider = require('@truffle/hdwallet-provider');
const readline = require('readline-sync');
const buildGroth16 = require('websnark/src/groth16')
const websnarkUtils = require('websnark/src/utils')
const { toWei, fromWei } = require('web3-utils')

// erc20tornado
let web3, tenKHex, hundredKHex, millionHex, circuit, proving_key, groth16, erc20, senderAccount, sessionNetId
let MERKLE_TREE_HEIGHT, TOKEN_AMOUNT, ERC20_TOKEN

const tornados = {};

const fullNumber = {
  "10k": "Ten Thousand",
  "1000000000000" : "Ten Thousand",
  "100k": "One Hundred Thousand",
  "10000000000000" : "One Hundred Thousand",
  "1000k": "One Million",
  "100000000000000" : "One Million"
}

/** Whether we are in a browser or node.js */
const inBrowser = (typeof window !== 'undefined')

/** Generate random number of specified byte length */
const rbigint = nbytes => snarkjs.bigInt.leBuff2int(crypto.randomBytes(nbytes))

/** Compute pedersen hash */
const pedersenHash = data => circomlib.babyJub.unpackPoint(circomlib.pedersenHash.hash(data))[0]

/** BigNumber to hex string of specified length */
function toHex(number, length = 32) {
  let str = number instanceof Buffer ? number.toString('hex') : bigInt(number).toString(16)
  return '0x' + str.padStart(length * 2, '0')
}

/** Display account balance */
async function printBalance(account, name) {
  console.log(`${name} ETH balance is`, web3.utils.fromWei(await web3.eth.getBalance(account)))
  console.log(`${name} Token Balance is`, await erc20.methods.balanceOf(account).call())
}

/**
 * Create deposit object from secret and nullifier
 */
function createDeposit(nullifier, secret) {
  let deposit = { nullifier, secret }
  deposit.preimage = Buffer.concat([deposit.nullifier.leInt2Buff(31), deposit.secret.leInt2Buff(31)])
  deposit.commitment = pedersenHash(deposit.preimage)
  deposit.nullifierHash = pedersenHash(deposit.nullifier.leInt2Buff(31))
  return deposit
}

/**
 * 
 * parses the network id, amount, and note itsef from the notestring
 */
function parseNote(noteString) {
  const noteRegex = /hexmix-(?<amount>[\d.]+)-(?<netId>\d+)-0x(?<note>[0-9a-fA-F]{124})/g
  const match = noteRegex.exec(noteString)
  if (!match) {
    throw new Error('The note has invalid format')
  }

  const buf = Buffer.from(match.groups.note, 'hex')
  const nullifier = bigInt.leBuff2int(buf.slice(0, 31))
  const secret = bigInt.leBuff2int(buf.slice(31, 62))
  const deposit = createDeposit(nullifier, secret)
  const netId = Number(match.groups.netId)

  return { amount: match.groups.amount, netId, deposit }
}

/**
 * Make an ERC20 deposit
 */
async function depositErc20(erc20tornado) {
  const deposit = createDeposit(rbigint(31), rbigint(31))

  const note = toHex(deposit.preimage, 62)
  const noteString = `hexmix-${erc20tornado.tokenAmount}-${sessionNetId}-${note}`;
  console.log('Your commitment:', deposit.commitment)
  console.log('Your note:', noteString)
  readline.keyIn("Record your note. You will need it to withdraw. When recorded, press any key to continue...");

  const allowance = await erc20.methods.allowance(senderAccount, erc20tornado._address).send({from: senderAccount});
  console.log(`Current allowance is ${allowance}`);
  if(allowance.lt(erc20tornado.tokenAmount)){
    console.log(`Approving ${erc20tornado.tokenAmount} tokens for deposit`)
    await erc20.methods.approve(erc20tornado._address, erc20tornado.tokenAmount).send({ from: senderAccount})
  }
  
  console.log('Submitting deposit transaction')
  await erc20tornado.methods.deposit(toHex(deposit.commitment)).send({ from: senderAccount, gas:2e6 })

  return noteString
}

/**
 * Generate merkle tree for a deposit.
 * Download deposit events from the contract, reconstructs merkle tree, finds our deposit leaf
 * in it and generates merkle proof
 * @param contract Tornado contract address
 * @param deposit Deposit object
 */
async function generateMerkleProof(contract, deposit) {
  // Get all deposit events from smart contract and assemble merkle tree from them
  console.log('Getting current state from tornado contract')
  const events = await contract.getPastEvents('Deposit', { fromBlock: contract.deployedBlock, toBlock: 'latest' })
  const leaves = events
    .sort((a, b) => a.returnValues.leafIndex - b.returnValues.leafIndex) // Sort events in chronological order
    .map(e => e.returnValues.commitment)
  const tree = new merkleTree(MERKLE_TREE_HEIGHT, leaves)
  
  // Find current commitment in the tree
  let depositEvent = events.find(e => e.returnValues.commitment === toHex(deposit.commitment))
  let leafIndex = depositEvent ? depositEvent.returnValues.leafIndex : -1

  // Validate that our data is correct
  const isValidRoot = await contract.methods.isKnownRoot(toHex(await tree.root())).call()
  const isSpent = await contract.methods.isSpent(toHex(deposit.nullifierHash)).call()
  assert(isValidRoot === true, 'Merkle tree is corrupted')
  assert(isSpent === false, 'The note is already spent')
  assert(leafIndex >= 0, 'The deposit is not found in the tree')

  // Compute merkle proof of our commitment
  return await tree.path(leafIndex)
}

/**
 * Generate SNARK proof for withdrawal
 * @param contract Tornado contract address
 * @param note Note string
 * @param recipient Funds recipient
 * @param relayer Relayer address
 * @param fee Relayer fee
 * @param refund Receive ether for exchanged tokens
 */
async function generateProof(contract, deposit, recipient, relayer = 0, fee = 0, refund = 0) {
  // Decode hex string and restore the deposit object
  // let buf = Buffer.from(note.slice(2), 'hex')
  // let deposit = createDeposit(bigInt.leBuff2int(buf.slice(0, 31)), bigInt.leBuff2int(buf.slice(31, 62)))

  // Compute merkle proof of our commitment
  const { root, path_elements, path_index } = await generateMerkleProof(contract, deposit)

  // Prepare circuit input
  const input = {
    // Public snark inputs
    root: root,
    nullifierHash: deposit.nullifierHash,
    recipient: bigInt(recipient),
    relayer: bigInt(relayer),
    fee: bigInt(fee),
    refund: bigInt(refund),

    // Private snark inputs
    nullifier: deposit.nullifier,
    secret: deposit.secret,
    pathElements: path_elements,
    pathIndices: path_index,
  }

  console.log('Generating SNARK proof')
  console.time('Proof time')
  const proofData = await websnarkUtils.genWitnessAndProve(groth16, input, circuit, proving_key)
  const { proof } = websnarkUtils.toSolidityInput(proofData)
  console.timeEnd('Proof time')

  const args = [
    toHex(input.root),
    toHex(input.nullifierHash),
    toHex(input.recipient, 20),
    toHex(input.relayer, 20),
    toHex(input.fee),
    toHex(input.refund)
  ]

  return { proof, args }
}

/**
 * Do a ERC20 withdrawal
 * @param note Note to withdraw
 * @param recipient Recipient address
 */
async function withdrawErc20(erc20tornado, deposit, recipient) {
  
  if(readline.keyInYN(`Do you wish to withdraw to ${recipient}? (y/n)`)){
    
    const { proof, args } = await generateProof(erc20tornado, deposit, recipient)

    console.log('Submitting withdraw transaction')
    await erc20tornado.methods.withdraw(proof, ...args).send({ from: senderAccount, gas: 1e6 })
    console.log('Done')
  } else {
    console.log("Exiting without taking action...");
  }
}

/**
 * Do a ERC20 withdrawal through relay
 * @param note Note to withdraw
 * @param recipient Recipient address
 * @param relayUrl Relay url address
 */
async function withdrawRelayErc20(erc20tornado, deposit, recipient, relayUrl) {
  const resp = await axios.get(relayUrl + '/status')
  const { relayerAddress, netId, gasPrices, ethPriceInDai } = resp.data
  assert(netId === await web3.eth.net.getId() || netId === '*', 'This relay is for different network')
  console.log('Relay address: ', relayerAddress)

  const refund = bigInt(toWei('0.001'))
  const fee = bigInt(toWei(gasPrices.fast.toString(), 'gwei')).mul(bigInt(1e6)).add(refund).mul(bigInt(fromWei(ethPriceInDai.toString())))
  const { proof, args } = await generateProof(erc20tornado, deposit, recipient, relayerAddress, fee, refund)

  console.log('Sending withdraw transaction through relay')
  const resp2 = await axios.post(relayUrl + '/relay', { contract: erc20tornado._address, proof: { proof, publicSignals: args } })
  console.log(`Transaction submitted through relay, tx hash: ${resp2.data.txHash}`)

  let receipt = await waitForTxReceipt(resp2.data.txHash)
  console.log('Transaction mined in block', receipt.blockNumber)
  console.log('Done')
}

/**
 * Waits for transaction to be mined
 * @param txHash Hash of transaction
 * @param attempts
 * @param delay
 */
function waitForTxReceipt(txHash, attempts = 60, delay = 1000) {
  return new Promise((resolve, reject) => {
    const checkForTx = async (txHash, retryAttempt = 0) => {
      const result = await web3.eth.getTransactionReceipt(txHash)
      if (!result || !result.blockNumber) {
        if (retryAttempt <= attempts) {
          setTimeout(() => checkForTx(txHash, retryAttempt + 1), delay)
        } else {
          reject(new Error('tx was not mined'))
        }
      } else {
        resolve(result)
      }
    }
    checkForTx(txHash)
  })
}

/**
 * Init web3, contracts, and snark
 */
async function init() {
  let erc20ContractJson, erc20tornadoJson, erc20DenominationsJson
  // if (inBrowser) {
  //   // Initialize using injected web3 (Metamask)
  //   // To assemble web version run `npm run browserify`
  //   web3 = new Web3(window.web3.currentProvider, null, { transactionConfirmationBlocks: 1 })
  //   contractJson = await (await fetch('build/contracts/ETHTornado.json')).json()
  //   circuit = await (await fetch('build/circuits/withdraw.json')).json()
  //   proving_key = await (await fetch('build/circuits/withdraw_proving_key.bin')).arrayBuffer()
  //   MERKLE_TREE_HEIGHT = 16
  //   ETH_AMOUNT = 1e18
  //   TOKEN_AMOUNT = 1e19
  // } else {
    
    const seed = readline.question("Please enter your wallet seed (needed each time): ");
    const provider = new HDWalletProvider(
      seed,
      'https://ethereum-rpc.trustwalletapp.com'
    );
    
    web3 = new Web3(provider);
    circuit = require('./build/circuits/withdraw.json')
    proving_key = fs.readFileSync('build/circuits/withdraw_proving_key.bin').buffer
    require('dotenv').config()
    MERKLE_TREE_HEIGHT = process.env.MERKLE_TREE_HEIGHT || 20
    ETH_AMOUNT = process.env.ETH_AMOUNT
    TOKEN_AMOUNT = process.env.TOKEN_AMOUNT
    ERC20_TOKEN = process.env.ERC20_TOKEN
    erc20ContractJson = require('./build/contracts/ERC20Mock.json')
    erc20tornadoJson = require('./build/contracts/ERC20Tornado.json')
  //}
  
  groth16 = await buildGroth16()
  //let netId = await web3.eth.net.getId()
  sessionNetId = 1;

  erc20DenominationsJson = require('./scripts/tornado-deployments.json');

  const tx3 = await web3.eth.getTransaction(erc20DenominationsJson["10kHex"].transactionHash);
  tenKHex = new web3.eth.Contract(erc20tornadoJson.abi, erc20DenominationsJson["10kHex"].address);
  tenKHex.deployedBlock = tx3.blockNumber;
  tenKHex.tokenAmount = erc20DenominationsJson["10kHex"].tokenAmount;

  const tx4 = await web3.eth.getTransaction(erc20DenominationsJson["100kHex"].transactionHash);
  hundredKHex = new web3.eth.Contract(erc20tornadoJson.abi, erc20DenominationsJson["100kHex"].address);
  hundredKHex.deployedBlock = tx4.blockNumber;
  hundredKHex.tokenAmount = erc20DenominationsJson["100kHex"].tokenAmount;

  const tx5 = await web3.eth.getTransaction(erc20DenominationsJson["1MHex"].transactionHash);
  millionHex = new web3.eth.Contract(erc20tornadoJson.abi, erc20DenominationsJson["1MHex"].address);
  millionHex.deployedBlock = tx5.blockNumber;
  millionHex.tokenAmount = erc20DenominationsJson["1MHex"].tokenAmount;


  tornados["10k"] = tenKHex;
  tornados[tenKHex.tokenAmount] = tenKHex;

  tornados["100k"] = hundredKHex;
  tornados[hundredKHex.tokenAmount] = hundredKHex;

  tornados["1000k"] = millionHex;
  tornados[millionHex.tokenAmount] = millionHex;
  // const tx3 = await web3.eth.getTransaction(erc20tornadoJson.networks[netId].transactionHash)
  // erc20tornado = new web3.eth.Contract(erc20tornadoJson.abi, erc20tornadoJson.networks[netId].address)
  // erc20tornado.deployedBlock = tx3.blockNumber
  
  erc20 = new web3.eth.Contract(erc20ContractJson.abi, erc20ContractJson.networks[sessionNetId].address)
  const tx2 = await web3.eth.getTransaction(erc20ContractJson.networks[sessionNetId].transactionHash)
  erc20.deployedBlock = tx2.blockNumber

  senderAccount = (await web3.eth.getAccounts())[0]
  console.log('Loaded')
}

// ========== CLI related stuff below ==============

/** confirm intended bill size */
async function confirm(size, action){
  const denom = fullNumber[size];
  if(!denom){return false;}

  return readline.keyInYN(`Do you wish to ${action} ${size} HEX? (y/n)`);
}

/** Print command line help */
function printHelp(code = 0) {
  console.log(`Usage:
  Submit a deposit from default eth account for 10k, 100k, or 1000k and return the resulting note
  $ ./cli-hex.js depositErc20 <10k|100k|1000k>

  Withdraw an existing note to 'recipient' account
  $ ./cli-hex.js withdrawErc20 <note> <recipient> [relayUrl]

  Check address balance
  $ ./cli-hex.js balance <address>

  Perform an automated test
  $ ./cli-hex.js test
  $ ./cli-hex.js testRelay

Example:
  $ ./cli.js depositErc20 10k
  Do you wish to deposit Ten Thousand HEX? (y/n) y
  Your note: 0x1941fa999e2b4bfeec3ce53c2440c3bc991b1b84c9bb650ea19f8331baf621001e696487e2a2ee54541fa12f49498d71e24d00b1731a8ccd4f5f5126f3d9f400
  Record your note. You will need it to withdraw. When recorded, press any key to continue...
  Done

  $ ./cli.js withdraw 0x1941fa999e2b4bfeec3ce53c2440c3bc991b1b84c9bb650ea19f8331baf621001e696487e2a2ee54541fa12f49498d71e24d00b1731a8ccd4f5f5126f3d9f400 0xee6249BA80596A4890D1BD84dbf5E4322eA4E7f0
`)
  process.exit(code)
}

/** Process command line args and run */
async function runConsole(args) {
  if (args.length === 0) {
    printHelp()
  } else {
    switch (args[0]) {
    case 'depositErc20':
      if (args.length === 2) {
        await init()
        const erc20tornado = tornados[args[1]];
        if(erc20tornado){
          let confirmed = await confirm(args[1], "deposit")
          if(!confirmed){
            console.log('Exiting without taking action...');
            return;
          }
          await printBalance(erc20tornado._address, 'Tornado')
          await printBalance(senderAccount, 'Sender account')
          await depositErc20(erc20tornado)
          await printBalance(erc20tornado._address, 'Tornado')
          await printBalance(senderAccount, 'Sender account')
        } else {
          printHelp(1)
        }
      } else {
        printHelp(1)
      }
      break
    case 'balance':
      if (args.length === 2 && /^0x[0-9a-fA-F]{40}$/.test(args[1])) {
        await init()
        await printBalance(args[1])
      } else {
        printHelp(1)
      }
      break
    case 'withdrawErc20':
      
      if (args.length >= 3 && 
          args.length <= 4 && 
          ///^0x[0-9a-fA-F]{124}$/.test(args[1]) && 
          /^0x[0-9a-fA-F]{40}$/.test(args[2])) {
        await init()
        const {amount, netId, deposit } = parseNote(args[1]);
        const erc20tornado = tornados[amount];
        console.log(`Lookup for tornado with amount ${amount} and keys\n${Object.keys(tornados)}\n ${erc20tornado ? "succeeded" : "failed"}`);
        if(sessionNetId !== netId){
          throw `This note is for a different network: ${sessionNetId} vs ${netId}`;
        }

        if(!erc20tornado){printHelp(1);}

        const confirmed = await confirm(amount, "withdraw")
        if(!confirmed){
          console.log('Exiting without taking action...');
          return;
        }
        await printBalance(erc20tornado._address, 'Tornado')
        await printBalance(args[2], 'Recipient account')
        if (args[3]) {
          await withdrawRelayErc20(erc20tornado, deposit, args[2], args[3])
        } else {
          await withdrawErc20(erc20tornado, deposit, args[2])
        }
        await printBalance(erc20tornado._address, 'Tornado')
        await printBalance(args[2], 'Recipient account')
      } else {
        printHelp(1)
      }
      break
      // Tests broken for the moment
    // case 'test':
    //   if (args.length === 1) {
    //     await init()

    //     const note2 = await depositErc20()
    //     const {amount, noteNetId, note2note } = parseNote(note2);
    //     const erc20tornado = tornados[amount];
    //     await withdrawErc20(erc20tornado, note2note, senderAccount)
    //   } else {
    //     printHelp(1)
    //   }
    //   break
    // case 'testRelay':
    //   if (args.length === 1) {
    //     await init()

    //     const note2 = await depositErc20()
    //     const {amount, noteNetId, note2note } = parseNote(note2);
    //     const erc20tornado = tornados[amount];
    //     await withdrawRelayErc20(erc20tornado, note2note, senderAccount, 'http://localhost:8000')
    //   } else {
    //     printHelp(1)
    //   }
    //   break

    default:
      printHelp(1)
    }
  }
}

if (inBrowser) {
  window.deposit = deposit
  window.depositErc20 = depositErc20
  window.withdraw = async () => {
    const note = prompt('Enter the note to withdraw')
    const recipient = (await web3.eth.getAccounts())[0]
    await withdraw(note, recipient)
  }
  init()
} else {
  runConsole(process.argv.slice(2))
    .then(() => process.exit(0))
    .catch(err => { console.log(err); process.exit(1) })
}
