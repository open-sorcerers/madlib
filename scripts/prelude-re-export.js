const { pipe, fork } = require('snang/script')
const { generateMultiFiles } = require('./prelude-re-export-core')

module.exports = pipe(
  generateMultiFiles,
  fork(console.error, console.log)
)(process.argv.slice(2))
