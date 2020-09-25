'use-strict';

console.log("STARTING TOOL....");

const exec = require('util').promisify(require('child_process').exec);
const tools = require("./utils")



let yargs = require("yargs")
            .demandOption("file")
            .option("ua")
            .option("v2")
            .option("sync")

const filename : string = yargs.argv.file;
const solver : string = yargs.argv.ua ? "ua" : "cbmc"


tools.cleanUp()
    .then(tools.createWorkdir)
    .then(() => tools.extractMLC(filename, solver, yargs.argv.v2))
    .then((atts : any)  => tools.verify(atts, solver, yargs.argv.sync))
    .then(JSON.stringify)
    .then(console.log)
    // .then(tools.cleanUp)
    .catch(console.error)




// console.log("DONE.")