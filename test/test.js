const assert = require('assert');
const util = require('util');
const exec = util.promisify(require('child_process').exec);
const {cillyCommand, parse, basicTest} = require('./TestUtils.js')

describe('CFG Test', () => {
    before(async () => {
        await exec(`make countAST countCFG`)
    })

    it('noloops', async () => {
        await basicTest({
            test: 'noloops',
            total: 0,
            totalnonlocal: 0,
            wellstructured: true,
            locals: [],
            nonlocals: []
        })
    });

    it('twolocal', async () => {
        await basicTest({
            test: 'twolocal',
            total: 2,
            totalnonlocal: 0,
            wellstructured: true,
            locals: [6, 2],
            nonlocals: []
        })
    });

    it('oneeach', async () => {
        await basicTest({
            test: 'oneeach',
            total: 2,
            totalnonlocal: 1,
            wellstructured: false,
            locals: [2],
            nonlocals: [6]
        })
    });

    it('goto', async () => {
        await basicTest({
            test: 'goto',
            total: 1,
            totalnonlocal: 0,
            wellstructured: true,
            locals: [2],
            nonlocals: []
        })

    });


})
