const assert = require('assert');
const util = require('util');
const exec = util.promisify(require('child_process').exec);


const cillyCommand = (filename) => {
    return `cilly --gcc=/usr/bin/gcc-6 --load=_build/countCFG.cmxs test/${filename}.c`
} 

const parse = (stderr) => {

    const parsevalue = (field, val) => {
        switch(field){
            case 'wellstructured': 
                return val === 'true'
            case 'total':
            case 'totalnonlocal':
                return parseInt(val)
            case 'nonlocals':
            case 'locals':
                if(val === '') return []
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
             .reduce((acc, cur) => ({...acc, ...cur}))
        
}


const basicTest =  async (data) => {
    const { stderr, stdout } = await exec(cillyCommand(data.test))
    const result = parse(stderr);
    assert.equal(result.total, data.total);
    assert.equal(result.totalnonlocal, data.totalnonlocal);
    assert.equal(result.wellstructured, data.wellstructured);
    assert.deepEqual(result.locals, data.locals);
    assert.deepEqual(result.nonlocals, data.nonlocals);
}

module.exports = {cillyCommand, parse, basicTest}