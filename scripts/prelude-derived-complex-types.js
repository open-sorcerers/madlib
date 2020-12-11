const {
  C,
  match,
  concat,
  filter,
  fork,
  includes,
  j2,
  map,
  pipe,
  readFile,
  reduce,
  reject,
  slice,
  split,
  trace,
  uniq
} = require('snang/script')

module.exports = pipe(
  readFile,
  map(
    pipe(
      split(C.n),
      filter(includes('::')),
      map(split(C._)),
      map(slice(2, Infinity)),
      map(
        filter(z => {
          const init = z[0]
          return (
            match(/[A-Z]/, init).length && init === init.toUpperCase()
          )
        })
      ),
      reduce(concat, []),
      map(z => (z[1] === '.' ? z.slice(2) : z)),
      map(z => z.replace(/[()<>,\.]/g, '')),
      reject(x => ['Number', 'Boolean', 'String'].includes(x)),
      uniq
    )
  ),
  fork(console.error, console.log)
)(process.argv.slice(2)[0])
