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
             }).reduce((acc, cur) => ({...acc, ...cur}))
        
}

module.exports = {cillyCommand, parse}