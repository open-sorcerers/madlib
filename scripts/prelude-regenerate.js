const path = require('path')
const fs = require('fs')
const F = require('fluture')
const {
  curry,
  trace,
  fork,
  map,
  chain,
  pipe,
  readFile,
  toPairs,
  split,
  init,
  join,
  ifElse,
  length,
  equals,
  nth
} = require('snang/script')
const { generateMultiFiles } = require('./prelude-re-export-core')

const getPathFromFilePath = path.dirname

const relative = curry((scope, x) =>
  path.resolve(getPathFromFilePath(scope), x)
)

module.exports = pipe(file => {
  const nearby = relative(file)
  return pipe(
    readFile,
    chain(
      pipe(
        JSON.parse,
        toPairs,
        map(([k, v]) => {
          const name = k + '.mad'
          return map(
            raw => [name, raw],
            generateMultiFiles(map(nearby, v))
          )
        }),
        F.parallel(10)
      )
    ),
    chain(
      pipe(
        map(([filename, raw]) => {
          return new F((reject, resolve) => {
            const filepath = path.normalize(
              getPathFromFilePath(file) + '/' + filename
            )
            // can't use torpor b/c fluture version incompatibility
            fs.writeFile(filepath, raw, 'utf8', e =>
              e ? reject(e) : resolve(filepath)
            )
            return () => {}
          })
        }),
        F.parallel(10)
      )
    )
  )(file)
}, fork(console.error, console.log))(process.argv.slice(2)[0])
