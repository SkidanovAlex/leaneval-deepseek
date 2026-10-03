/-
# The deep/shallow cut level of the low-pass Ionescu--Wainger walk

This module isolates the *cut level*

  `cutLevel ρ l₁ := Nat.clog 2 (3 · iwQl ρ l₁) + 2`

of the deep/shallow split of `Work.KMTAreas.A7Hi2.SupPiece`
(see `NOTES_A7Hi2_supPieceClean_SESSION2.md`).  It lives on its own so that the two halves of the
split (`Work.KMTAreas.A7Hi2.supDeepLe`, `Work.KMTAreas.A7Hi2.supShallowLe`) can import it *without*
importing `supPieceClean` itself, which in turn imports them.

`iwQl ρ l₁` is the common denominator (the lcm of the admissible denominators `iwP ρ l₁`) of the
Ionescu--Wainger arithmetic frequency set `(ℚ/ℤ)_{≤l₁}`; the level `L` at which
`2^L > 3 · iwQl ρ l₁` is exactly where the bump `η_{≤−L}` becomes *narrower* than the lattice
spacing `1/iwQl ρ l₁`, i.e. where the Magyar–Stein–Wainger decimation factorisation
`Work.KMTAreas.A7Hi.lpf_decim_fact` becomes available.
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.Pset

namespace Work.KMTAreas.A7Hi2

/-- The cut level of the deep/shallow split: the least level `L` with `3 · iwQl ρ l₁ ≤ 2^L`.
(This is where the decimation factorisation of `Work.KMTAreas.A7Hi.lpf_decim_fact` becomes
available.) -/
noncomputable def cutLevel (ρ : ℝ) (l₁ : ℕ) : ℕ :=
  Nat.clog 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l₁) + 2

end Work.KMTAreas.A7Hi2
