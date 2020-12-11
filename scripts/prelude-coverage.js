const {
  C,
  identity: I,
  trace,
  equals,
  filter,
  fork,
  join,
  last,
  map,
  matches,
  pipe,
  readFile,
  reject,
  slice,
  split
} = require('snang/script')

module.exports = pipe(file =>
  pipe(
    readFile,
    map(
      pipe(
        split(C.n),
        filter(matches('export')),
        map(split(C._)),
        map(slice(0, 2)),
        reject(pipe(last, equals('data'))),
        map(last),
        filter(I),
        z => {
          const imported = file.slice(
            file.lastIndexOf('/') + 1,
            file.indexOf('.mad')
          )
          const initials = imported.slice(0, 2).toUpperCase()

          return z
            ? `import ${imported} from "${imported}"
${z.map(zz => imported + zz + ' = ' + imported + '.' + zz).join(C.n)}`
            : `// nothing exported from ${file}`
        }
      )
    ),
    fork(console.error, console.log)
  )(file)
)(process.argv.slice(2)[0])
