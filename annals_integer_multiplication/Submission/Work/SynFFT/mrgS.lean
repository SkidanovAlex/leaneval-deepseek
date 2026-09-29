import Mathlib

/-!
# The index map of one interleave ("merge") pass

`mrgS s p` is the index map of the scale-`s` interleave pass `mrgN` of the synthetic FFT
(`Submission/Work/SynFFT/kit2.lean`): inside each block of `2s` consecutive positions, the
position `2j + ε` receives what was at `j + ε*s` (see `mrgN`).  It is stated here on its own so
that the (purely arithmetic) facts about it can be proved without importing the whole kit.
-/

set_option autoImplicit false

namespace Work.SynFFT

/-- The index map of one interleave pass of scale `s`: inside every block of size `2s`,
position `2j + ε` receives what was at `j + ε * s`. -/
def mrgS (s p : ℕ) : ℕ := p / (2 * s) * (2 * s) + (p / 2 % s) + (p % 2) * s

end Work.SynFFT
