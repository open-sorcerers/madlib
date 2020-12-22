const F = require('fluture')
const {
  $,
  C,
  ap,
  chain,
  curry,
  either,
  equals,
  filter,
  fork,
  gt,
  identity: I,
  ifElse,
  includes,
  join,
  last,
  length,
  lt,
  map,
  nth,
  of,
  pipe,
  readFile,
  reduce,
  reject,
  replace,
  slice,
  split,
  tail,
  trace
} = require('snang/script')

const prepend = curry((a, b) => a + b)
const getKind = pipe(split('/'), slice(-2, -1), nth(0))
const getConflictFreeName = pipe(
  split('/'),
  slice(-2, Infinity),
  map(replace('.mad', '')),
  join('')
)
const lastPart = pipe(split('/'), last, z =>
  z.slice(0, z.indexOf('.'))
)

const printImport = file =>
  pipe(
    of,
    ap([getKind, getConflictFreeName]),
    ([kind, name]) =>
      `import ${name} from "./${kind}/${lastPart(file)}"`
  )(file)

const printExports = curry((file, raw) =>
  pipe(getConflictFreeName, name =>
    pipe(
      split(C.n),
      filter(includes('export')),
      map(split(C._)),
      map(slice(1, 3)),
      map(reject(equals('='))),
      map(
        ifElse(
          pipe(length, equals(2)),
          ([w, x]) =>
            w !== 'data'
              ? `export ${w} ${x} = ${name}.${x}`
              : `export alias ${x} = ${name}.${x}`,
          x => `export ${x} = ${name}.${x}`
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

module.exports = { generateMultiFiles }