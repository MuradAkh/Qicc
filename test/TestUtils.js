const assert = require('assert');
const util = require('util');
const exec = util.promisify(require('child_process').exec);


const loadCaml = (progs) =>{
  return progs
         .map(prog => `--load=_build/src/${prog}.cmxs`)
         .join(' ')
}
const cillyCommand = (filename, progs) => `cilly --gcc=/usr/bin/gcc-6 ${loadCaml(progs)} test/progs/find/${filename}.c`
const npmCommand = (filename) => `npm run verify -- --file test/progs/assert/${filename}.c`

const parseFind = (stderr) => {

  const parsevalue = (field, val) => {
    switch (field) {
      case 'wellstructured':
        return val === 'true'
      case 'total':
      case 'totalnonlocal':
        return parseInt(val)
      case 'nonlocals':
      case 'locals':
        if (val === '') return []
        return val.split(' ').map(it => parseInt(it))
    }
  }

  return stderr
    .split("\n")
    .filter(it => it !== '')
    .map(it => it.split(": "))
    .map(it => {
      const o = {}
      o[it[0]] = parsevalue(it[0], it[1])
      return o
    })
    .reduce((acc, cur) => ({ ...acc, ...cur }))

}

parseCli = (stdout) => {
    const json = stdout.match(/\[[\s\S]*\]/g)[0].replace('\\', '');
    return JSON.parse(json)
}

const basicTest = (progs) => {
  return  async (data) => {
    const { stderr } = await exec(cillyCommand(data.test, progs))
    const result = parseFind(stderr);
    assert.equal(result.total, data.total, "total");
    assert.equal(result.totalnonlocal, data.totalnonlocal);
    assert.equal(result.wellstructured, data.wellstructured);
    assert.deepEqual(result.locals, data.locals);
    assert.deepEqual(result.nonlocals, data.nonlocals);
  }
}

const cliTest = () => {
  return  async (prog, data) => {
    const { stdout } = await exec(npmCommand(prog))
    const result = parseCli(stdout);

    assert.deepEqual(result, data);
  }
}



module.exports = { basicTest, cliTest }