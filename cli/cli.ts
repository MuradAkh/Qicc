'use-strict';

console.log("STARTING TOOL....");

const exec = require('util').promisify(require('child_process').exec);
const tools = require("./utils")



let yargs = require("yargs")
            .demandOption("file");

const filename : string = yargs.argv.file;

tools.cleanUp()
    .then(tools.createWorkdir())
    .then(() => tools.extractMLC(filename))
    .then(tools.verify)
    .then(console.log)
    // .then(tools.cleanUp)
    .catch(console.error)




console.log("DONE.")