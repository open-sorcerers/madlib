const F = require('fluture')
const {
  $,
  reduce,
  C,
  identity: I,
  chain,
  curry,
  either,
  equals,
  filter,
  fork,
  ifElse,
  includes,
  join,
  last,
  length,
  gt,
  lt,
  map,
  nth,
  pipe,
  readFile,
  reject,
  slice,
  split,
  trace
} = require('snang/script')

const prepend = curry((a, b) => a + b)
const getKind = pipe(split('/'), slice(-2, -1), nth(0))
const lastPart = pipe(split('/'), last, z =>
  z.slice(0, z.indexOf('.'))
)

const printImport = file =>
  pipe(
    getKind,
    kind => `import ${kind} from "./${kind}/${lastPart(file)}"`
  )(file)

const printExports = curry((file, raw) =>
  pipe(getKind, kind =>
    pipe(
      split(C.n),
      filter(includes('export')),
      map(split(C._)),
      map(slice(1, 3)),
      map(reject(equals('='))),
      map(
        ifElse(
          pipe(length, equals(2)),
          ([w, x]) => `export ${w} ${x} = ${kind}.${x}`,
          x => `export ${x} = ${kind}.${x}`
        )
      ),
      join(C.n),
      prepend('\n')
    )(raw)
  )(file)
)
const generateFile = curry((addImport, file) =>
  pipe(
    readFile,
    map(printExports(file)),
    map(addImport ? prepend(printImport(file) + '\n') : I)
  )(file)
)

const generateMultiFiles = files =>
  pipe(
    map(generateFile(false)),
    F.parallel(10),
    map(
      pipe(
        join('\n'),
        prepend('\n'),
        prepend(pipe(map(printImport), join('\n'))(files))
      )
    )
  )(files)

module.exports = pipe(
  generateMultiFiles,
  fork(console.error, console.log)
)(process.argv.slice(2))
