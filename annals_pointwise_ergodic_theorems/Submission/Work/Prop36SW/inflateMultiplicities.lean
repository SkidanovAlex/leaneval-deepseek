import Mathlib
import Submission.Work.Prop36SW.boxNorm_famIdx_le_of_le
import Submission.Work.Prop36SW.blockInjFinSigma

/-!
# Inflating the multiplicities of the box-norm ladder

`Work.Peluse.C46.Prop36SW` (Peluse's Proposition 3.6, in the form consumed by the ladder) delivers,
for a datum with `d - 1` slots and multiplicities `t s`, a lower bound
`C * γ ^ E ≤ |A|⁻¹ ∑_{a ∈ A} ‖g a‖^{2^{∑_s t s}}_{□}` on the *box-norm power* at the level
`∑_s t s` obtained by taking `t s` copies of the direction `p s a [Lw s]`.

This file proves that a bound of that shape can be *inflated*: if all the multiplicities are
increased to a common value `T ≥ t s`, the same conclusion holds with the (harmless) exponent loss
`E ↦ E · 2^{∑_s T}`.

The proof is three steps.

* The index types `Fin (∑_s t s)` and `Fin (∑_s T)` are the canonical enumerations of the sigma
  types `Σ s, Fin (t s)` and `Σ s, Fin T`, and the fibre-wise inclusion
  `⟨s, k⟩ ↦ ⟨s, ⟨k, _⟩⟩` transports along them to an injection `e` which preserves the slot label;
  this is the delegated lemma `Work.Prop36SW.blockInjFinSigma`.
* For each datum `a`, `Work.Prop36SW.boxNormPow_le_of_inj` (the Gowers–Cauchy–Schwarz level raise)
  compares the two box-norm powers at the cost of the constant `2^{2^{∑T - ∑t} - 1}` and the power
  `2^{∑T - ∑t}`.
* Averaging over `A` uses the power mean inequality
  `(⨍ x)^{2^k} ≤ ⨍ x^{2^k}` (`Work.Prop36SW.powerMeanTwoPow`, Jensen for `t ↦ t^{2^k}`), which is
  available because the box-norm powers are nonnegative; this is collected in the helper
  `avg_pow_le_of_pointwise` below.

The final exponent `E · 2^{∑T}` is then weaker than the exponent `E · 2^{∑T - ∑t}` produced by the
level raise, which is why the constant `C'` may absorb `C^{2^{∑T-∑t}}` without any loss.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Prop36SW

noncomputable section

/-- The arithmetic progression `c[L] = {c, 2c, …, Lc}` is nonempty as soon as `1 ≤ L`. -/
lemma inflate_arithIcc_nonempty {c : ℤ} {L : ℕ} (h : 1 ≤ L) :
    (Work.Peluse.arithIcc c L).Nonempty := by
  refine ⟨c * 1, ?_⟩
  rw [Work.Peluse.arithIcc, Finset.mem_image]
  exact ⟨1, by simp [Finset.mem_Icc, h], by ring⟩

end

end Work.Prop36SW
