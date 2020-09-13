const fs = require('fs');
const {performance} = require('perf_hooks');
const util = require('util');
const exec = util.promisify(require('child_process').exec);

async function evaluatate(){
    await exec("cbmc --unwind 201 --unwinding-assertions  ./test/v2/target/double_2block/large_large/baseline.c > /dev/null")
}

evaluatate()