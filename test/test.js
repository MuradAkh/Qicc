const assert = require('assert');
const util = require('util');
const exec = util.promisify(require('child_process').exec);
const {cillyCommand, parse} = require('./TestUtils.js')

describe('Sample Test', () => {
    before(async () => {
        await exec(`make countAST countCFG`)
    })

    it('Hello World', async () => {
        const str = 'Hello World'
        const { stdout } = await exec(`echo ${str}`)
        assert.equal(stdout, `${str}\n`);
    });
});

describe('CFG Test', () => {
    before(async () => {
        await exec(`make countAST countCFG`)
    })

    it('noloops', async () => {
        const str = 'Hello World'
        const { stderr, stdout } = await exec(cillyCommand('noloops'))
        const result = parse(stderr);
        assert.equal(result.total, 0);
        assert.equal(result.totalnonlocal, 0);
        assert.equal(result.wellstructured, true);
        assert.deepEqual(result.locals, []);
        assert.deepEqual(result.nonlocals, []);
    });

    it('twolocal', async () => {
        const str = 'Hello World'
        const { stderr, stdout } = await exec(cillyCommand('noloops'))
        const result = parse(stderr);
        assert.equal(result.total, 0);
        assert.equal(result.totalnonlocal, 0);
        assert.equal(result.wellstructured, true);
        assert.deepEqual(result.locals, []);
        assert.deepEqual(result.nonlocals, []);
    });

    it('oneach', async () => {
        const str = 'Hello World'
        const { stderr, stdout } = await exec(cillyCommand('noloops'))
        const result = parse(stderr);
        assert.equal(result.total, 0);
        assert.equal(result.totalnonlocal, 0);
        assert.equal(result.wellstructured, true);
        assert.deepEqual(result.locals, []);
        assert.deepEqual(result.nonlocals, []);
    });

    it('goto', async () => {
        const str = 'Hello World'
        const { stderr, stdout } = await exec(cillyCommand('noloops'))
        const result = parse(stderr);
        assert.equal(result.total, 0);
        assert.equal(result.totalnonlocal, 0);
        assert.equal(result.wellstructured, true);
        assert.deepEqual(result.locals, []);
        assert.deepEqual(result.nonlocals, []);
    });


});
