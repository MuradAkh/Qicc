const util = require('util');
const exec = util.promisify(require('child_process').exec);
const { basicTest, cliTest } = require('./TestUtils.js')



describe('CFG Standard Tarjan', () => {
  before(async () => {
    this.test = basicTest(["countCFG"])
    await exec(`make countCFG`)
  })

  it('noloops', async () => {
    await this.test({
      test: 'noloops',
      total: 0,
      totalnonlocal: 0,
      wellstructured: true,
      locals: [],
      nonlocals: []
    })
  });

  it('twolocal', async () => {
    await this.test({
      test: 'twolocal',
      total: 2,
      totalnonlocal: 0,
      wellstructured: true,
      locals: [6, 2],
      nonlocals: []
    })
  });

  it('oneeach', async () => {
    await this.test({
      test: 'oneeach',
      total: 2,
      totalnonlocal: 1,
      wellstructured: false,
      locals: [2],
      nonlocals: [6]
    })
  });

  it('goto', async () => {
    await this.test({
      test: 'goto',
      total: 1,
      totalnonlocal: 0,
      wellstructured: true,
      locals: [2],
      nonlocals: []
    })
  });

  it('localnested', async () => {
    await this.test({
      test: 'localnested',
      total: 1,
      totalnonlocal: 0,
      wellstructured: true,
      locals: [2],
      nonlocals: []
    })
  });


  it('mixednested', async () => {
    await this.test({
      test: 'mixednested',
      total: 1,
      totalnonlocal: 0,
      wellstructured: true,
      locals: [2],
      nonlocals: []
    })
  });

})

describe('Custom Tarjan', () => {
  before(async () => {
    this.test = basicTest(["findLoops", "countCFGnested"])
    await exec(`make countCFGnested`)
  })

  it('noloops', async () => {
    await this.test({
      test: 'noloops',
      total: 0,
      totalnonlocal: 0,
      wellstructured: true,
      locals: [],
      nonlocals: []
    })
  });

  it('twolocal', async () => {
    await this.test({
      test: 'twolocal',
      total: 2,
      totalnonlocal: 0,
      wellstructured: true,
      locals: [6, 2],
      nonlocals: []
    })
  });

  it('oneeach', async () => {
    await this.test({
      test: 'oneeach',
      total: 2,
      totalnonlocal: 1,
      wellstructured: false,
      locals: [2],
      nonlocals: [6]
    })
  });

  it('goto', async () => {
    await this.test({
      test: 'goto',
      total: 1,
      totalnonlocal: 0,
      wellstructured: true,
      locals: [2],
      nonlocals: []
    })
  });

  it('localnested', async () => {
    await this.test({
      test: 'localnested',
      total: 3,
      totalnonlocal: 0,
      wellstructured: true,
      locals: [10, 6, 2],
      nonlocals: []
    })
  });

  it('mixednested', async () => {
    await this.test({
      test: 'mixednested',
      total: 3,
      totalnonlocal: 1,
      wellstructured: false,
      locals: [12, 2],
      nonlocals: [6]
    })
  });
})


describe('Verification Tool', function () {
  this.timeout(15000);

  before(async () => {
    await exec(`make findFuncs`)
    await exec(`make extractMLC`)
    this.test = cliTest()
  })

  it('nested', async () => {
    await this.test('nested',
      [
        { "9": { "isTrue": true, "provedAt": "main" } },
        { "16": { "isTrue": true, "provedAt": "main" } },
        { "21": { "isTrue": true, "provedAt": "21" } }
      ]
    )
  });

  it('nonlocal', async () => {
    await this.test('nonlocal',
      [
        { "main": { "isTrue": true, "provedAt": "main" } }
      ]
    )
  });

  it('onelocal', async () => {
    await this.test('onelocal',
      [
        { "8": { "isTrue": true, "provedAt": "8" } }
      ]
    )
  });
})



