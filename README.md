This is a work-in-progress port of the [Isabelle/HOL address translation
simplification proof for Arm v8-A][isabelleproof].  At present there is much of
the background machinery for the proof.  It should build with the snapshot of
the Arm model in commit `ad30a51` of the [sail-arm repository][sailarm].
See the [Isabelle proof's README file][isapfreadme] for details of what can be
found in the files.  There are also some results about bitvectors in `Mword.v`
that might move to the main library later.

Brian Campbell, 22nd June 2020.

[isabelleproof]: https://github.com/rems-project/armv8a-address-translation
[isapfreadme]: https://github.com/rems-project/armv8a-address-translation/blob/master/README.md
[sailarm]: https://github.com/rems-project/sail-arm

