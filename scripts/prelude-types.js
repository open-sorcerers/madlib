const {
  C,
  uniq,
  addIndex,
  concat,
  fork,
  last,
  groupWith,
  map,
  pipe,
  readFile,
  reduce,
  split
} = require('snang/script')

module.exports = pipe(
  readFile,
  map(
    pipe(
      split(C.n),
      addIndex(map)((z, i) => [i, z]),
      reduce((g, [num, line]) => {
        const prev = last(g) || []
        const [pnum, pline] = prev
        return g.concat(
          line.includes('data') ||
            (pnum + 1 === num &&
              (line.includes('=') || line.includes('|')))
            ? [[num, line.trim()]]
            : []
        )
      }, []),
      reduce((g, [num, line]) => {
        const prev = last(g) || []
        const [pnum, pline] = prev
        if (g.length === 0) return g.concat([[num, line]])
        const out = Array.isArray(pline)
          ? pline.concat(line)
          : [pline, line]
        if (Math.abs(num - pnum) === 1)
          return g.slice(0, -1).concat([[num, out]])
        return g.concat([[num, line]])
      }, []),
      reduce((acc, [eol, content]) => {
        return concat(
          acc,
          Array.isArray(content) ? [[content.join(C._)]] : [[content]]
        )
      }, []),
      map(([exported]) => {
        const splits = exported.split(C._)
        const type = splits[2]
        const parts = uniq(
          splits.slice(2).filter(z => z.toLowerCase() !== z)
        )
        return { type, parts }
      })
    )
  ),
  fork(console.error, console.log)
)(process.argv.slice(2)[0])
