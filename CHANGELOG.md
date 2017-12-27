# Version 0.3

* `zip`, `zip1` and `unsafeZip` now take a monadic pairing function, and return
  `Maybe` where `Nothing` happens in the target indexes do not match.

* Added `Terminal` instances for `Maybe` and `[]`.


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
