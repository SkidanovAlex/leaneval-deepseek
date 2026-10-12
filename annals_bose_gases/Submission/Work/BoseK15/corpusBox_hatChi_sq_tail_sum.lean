import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseK15.ChiReg_corpus
import Submission.Work.BoseK15.sum_inv_one_add_norm_tail
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.corpusBox_hatChi_sq_tail_sum` — the `χ̂²`-tail of the corpus bump

The corpus localization function `χ = Submission.BoseGases.chi` is `C^∞` with compact
support, so its (real, even) cosine transform `χ̂(p) = ∫ χ(x) cos⟪p,x⟫ dx`
(`Work.BoseB4.BoxData.hatChi`) decays faster than any polynomial:
`Work.BoseK15.ChiReg_corpus` (FS `lem:DecaychiHat`) gives, for **every** order `s`, a
constant `Cchi` with

    `|χ̂(p)| · (1 + ‖p‖²)^s ≤ Cchi`      for all `p`.

This module feeds that decay into the lattice tail sum
`Work.BoseK15.sum_inv_one_add_norm_tail` (the dyadic-annulus count of the dual lattice
`vec n = 2πn`): a lattice set all of whose momenta lie outside the ball of radius
`R ≥ 1` contributes at most `C/R^M` to `∑ (1+‖vec n‖²)^{-s}`, provided `M + 3 ≤ 2s`.

Concretely, at order `52` the pointwise decay gives `χ̂(vec n)² ≤ Cchi²·(1+‖vec n‖²)^{-104}`,
and the tail sum at `(s, M) = (104, 101)` (allowed since `M + 3 = 104 ≤ 208 = 2s`)
bounds the result by `Cchi²·128/R^101`.  Only existence of a
constant is used downstream; the constant produced here is `Cchi²·128`.

This is the tail estimate consumed by the low-momentum (`R^Hi`) sums of the
`BoseBoxFock` chapter, where the vacuum is projected onto the modes with
`‖k‖ ≥ R`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseK15

/-- **The `χ̂²`-tail of the corpus bump.**  There is a constant `C ≥ 0` such that for
every `R ≥ 1` and every finite set `S` of dual-lattice indices whose momenta
`vec n = 2πn` all have norm at least `R`, the sum of `χ̂(vec n)²` over `S` is at most
`C/R^101`.

The proof: `ChiReg_corpus 52` gives `|χ̂(p)|(1+‖p‖²)^52 ≤ Cchi`, hence
`χ̂(p)² ≤ Cchi²·(1+‖p‖²)^{-104}`; summing over `S` and applying the lattice tail
estimate `sum_inv_one_add_norm_tail 104 101` (legal since `101 + 3 ≤ 2·104`) gives
the claim with `C = 128·Cchi²`. -/
theorem corpusBox_hatChi_sq_tail_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (S : Finset (Fin 3 → ℤ)), 1 ≤ R →
      (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) →
      (∑ n ∈ S, (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2) ≤ C / R ^ 101 := by
  -- the χ̂-decay at order `52` and the lattice tail sum at `(s, M) = (104, 101)`
  obtain ⟨Cchi, hCchi_nn, hChi, _⟩ := ChiReg_corpus 52
  obtain ⟨Ctail, _hCtail_nn, hCtail⟩ := sum_inv_one_add_norm_tail 104 101 (by norm_num)
  refine ⟨Cchi ^ 2 * Ctail, by positivity, ?_⟩
  intro R S hR hS
  -- the pointwise bound `χ̂(p)² ≤ Cchi²·(1+‖p‖²)^{-104}`
  have hpoint : ∀ n ∈ S, (corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2
      ≤ Cchi ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 104)⁻¹ := by
    intro n _hn
    have hD : (0 : ℝ) < (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by positivity
    have hK : 0 ≤ Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := div_nonneg hCchi_nn hD.le
    have hle : corpusBox.hatChi (Work.BoseB4.vec n)
        ≤ Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by
      rw [le_div_iff₀ hD]
      exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) (hChi _)
    have hge : -corpusBox.hatChi (Work.BoseB4.vec n)
        ≤ Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by
      rw [le_div_iff₀ hD]
      exact le_trans (mul_le_mul_of_nonneg_right (neg_le_abs _) (by positivity)) (hChi _)
    have habs : |corpusBox.hatChi (Work.BoseB4.vec n)|
        ≤ Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := abs_le.mpr ⟨by linarith, hle⟩
    have hpow : (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52) ^ 2
        = ((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 104 := by
      rw [← pow_mul]
    calc (corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2
        ≤ (Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52) ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg hK]; exact habs
      _ = Cchi ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 104)⁻¹ := by
          rw [div_pow, div_eq_mul_inv, hpow]
  calc (∑ n ∈ S, (corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2)
      ≤ ∑ n ∈ S, Cchi ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 104)⁻¹ :=
        Finset.sum_le_sum hpoint
    _ = Cchi ^ 2 * ∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 104)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ Cchi ^ 2 * (Ctail / R ^ 101) :=
        mul_le_mul_of_nonneg_left (hCtail R S hR hS) (by positivity)
    _ = (Cchi ^ 2 * Ctail) / R ^ 101 := by ring

end Work.BoseK15
