# Version 0.3.1

* COMPILER ASSISTED BREAKING CHANGE: Fixed `TypeApplications` for `flay1` so
  that @c@ comes first.

* COMPILER ASSISTED BREAKING CHANGE: Not exporting `GFlay'`, `gflay'`,
  `gterminal` anymore.

* COMPILER ASSISTED BREAKING CHANGE: `GFlay1` and `All` are now type synonyms
  rather than classes.

* Added `pump`, `dump`, `Pump` and `GPump`.

* Added `GFlay1`, `gflay1`.

* Added `GTerminal` instance for `GHC.Generics.U1`.

* Added overlappable `GFlay'` instance for `GHC.Generics.K1` not wrapped by @f@.

* Added `Fields`, `GFields`, `Fields1` and `GFields1`.


# Version 0.3

* BREAKING CHANGE: `zip`, `zip1` and `unsafeZip` now take a monadic pairing function, and return
  `Maybe` where `Nothing` happens in the target indexes do not match.

* BREAKING CHANGE: Remove `Record` and `GRecord`.

* Added `trivialize`.

* Generalized type of `trivial'`.


# Version 0.2

* BREAKING CHANGE: The `m` parameter in in `Flay` and `Flayable` has been
  existentialized, to be chosen by the caller.

* BREAKING CHANGE: We don't use `DefaultSignatures` for `flay = gflay` anymore.
  This is very sad, but unfortunately type inferrence for the `c` type variable
  in new `Flayable` instances doesn't work.

* Added `Flayable1`, `trivial1`, `collect1`, `Terminal`, `GTerminal`, `zip1`,
  `zip`, `Record`, `GRecord`.

* Removed `outer`.

* Made compatible with GHC 8.2.2.


# Version 0.1

* Initial version.
