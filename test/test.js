const assert = require('assert');
const util = require('util');
const exec = util.promisify(require('child_process').exec);
const { basicTest } = require('./TestUtils.js')

describe('CFG Standard Tarjan', () => {
  before(async () => {
    this.test = basicTest("countCFG")
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
    this.test = basicTest("countCFGnested")
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

