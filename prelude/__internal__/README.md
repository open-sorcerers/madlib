# Prelude Files

These are predefined types / API you can work with in Madlib out of the box.

## Folder Structure

* < *internal* >         - the folder you're in right now
* < *internal* > /atomic  - prelude types which have no dependencies to their definition
* < *internal* > /derived - prelude types which have dependencies in their definition

## Segmented API regeneration

It's a PITA if we force our users to keep track of shit like `List` vs. `ListMaybe` when it's not clear from the outside what the distinction is. So by regenerating a internal level file which references the internal `/atomic` / `/derived` structure, we can provide a sane API to the users and blackbox the rest of it.

1. See `regeneration-map.json` in the < *internal* > folder.

It takes the form of:

{
  PublicPreludeApiName: [files, to, reference]
}

2. See `scripts/prelude-re-export.js` in the base /scripts folder.

It takes a list of files and generates a conflict-free re-exported definition of all of those files.

```
node scripts/prelude-re-export.js prelude/__internal__/atomic/List.mad prelude/__internal__/derived/ListMaybe.mad
```

3. See `scripts/prelude-regenerate.js` in the base /scripts folder.

It takes the mapping from `regeneration-map.json` (1) and applies it to the tooling described in (2), which regenerates all of the prelude top-level files.
