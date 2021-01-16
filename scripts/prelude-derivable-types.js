const F = require('fluture')
const {
  merge,
  objOf,
  C,
  chain,
  concat,
  filter,
  fork,
  includes,
  j2,
  map,
  match,
  pipe,
  prop,
  readDir,
  readFile,
  reduce,
  reject,
  slice,
  split,
  tackOn,
  trace,
  uniq
} = require('snang/script')

const isCommonType = x => ['Number', 'String', 'Boolean'].includes(x)

module.exports = pipe(
  map(x => x + '/*.mad'),
  readDir,
  chain(files =>
    pipe(
      map(file =>
        pipe(
          readFile,
          map(raw => ({ file, raw }))
        )(file)
      ),
      F.parallel(10)
    )(files)
  ),
  map(future =>
    pipe(
      map(
        pipe(({ raw, file }) =>
          pipe(
            split(C.n),
            filter(includes('::')),
            map(split(C._)),
            map(slice(2, Infinity)),
            map(
              filter(z => {
                const init = z[0]
                return (
                  match(/[A-Z]/, init).length &&
                  init === init.toUpperCase()
                )
              })
            ),
            reduce(concat, []),
            map(z =>
              z.indexOf('.') > -1 ? z.slice(z.indexOf('.')) : z
            ),
            map(z => z.replace(/[()<>,\.]/g, '')),
            uniq,
            reject(isCommonType),
            list => [file, list]
          )(raw)
        )
      ),
      reduce((agg, [k, v]) => merge(agg, objOf(k, v)), {})
    )(future)
  ),
  fork(console.error, console.log)
)(process.argv.slice(2))
