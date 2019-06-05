const assert = require('assert');
const util = require('util');
const exec = util.promisify(require('child_process').exec);


describe('Sample Test', () => {
    before(async () => {
        await exec(`make countAST countCFG`)
    })

    it('Example test', async () => {
        const str = 'Hello World'
        const { stdout } = await exec(`echo ${str}`)
        assert.equal(stdout, `${str}\n`);
    });
});
