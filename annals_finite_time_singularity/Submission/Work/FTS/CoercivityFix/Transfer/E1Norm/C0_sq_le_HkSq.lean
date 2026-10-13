/-
# `(C₀ f)² ≤ 64 |f|²_{ℋⁿ}` in the coercivity class `CoerAdm`

`C₀ f = L₁₂(Transport f)(0)` is the constant of the projector term `Z7` of the `D_z`
decomposition of `𝓛_Γ^T` (see `Work.Coercivity.C0`).  The estimate needed by the transfer
layer (`Transfer/E1Norm`) is that `C₀ f` is dominated by *any* of the `ℋⁿ`-norms of `f`,
`n ≥ 0`, with the same constant `64`:

  `(C₀ f)² ≤ 64 · HkSq α n f`.

The two halves of the proof, which are independent of each other:

* `(C₀ f)² ≤ 64 · Ef f` for `f` in the interior class `CoerAdm α f` and `0 < α ≤ 1`
  (`Work.FTS.CoercivityFix.Transfer.E1Norm.Pieces.C0_sq_le_Ef_CoerAdm` — the interior-class
  port of `Work.Coercivity.C0_sq_le_Ef`/`C0_sq_le_Ef_Q`; Cauchy–Schwarz against the fixed
  angular kernel plus `C0Ih · C0D ≤ 729/16 ≤ 64`);
* `Ef f ≤ HkSq α n f` for every `α` and `n` (`Ef_le_HkSq` below): the `i = 0` summand of
  `HkIntegrand α n f` is `(f · w / sin(2θ)^{η/2})² ≥ (f · w)²` off the two endpoints of
  `Iθ`, and the endpoint set is null.

Everything here rests only on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Coer1T.slotDz_LGammaT
import Submission.Work.Coercivity.C0_sq_le_Ef
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Pieces.C0_sq_le_Ef_CoerAdm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

set_option autoImplicit false

/-! ## The pointwise comparison `(A W)² ≤ (A (W / s^{η/2}))²` -/

/-- For `0 < s ≤ 1` and reals `A`, `W`: `(A·W)² ≤ (A·(W/s^{η/2}))²`.  In the application
`s = sin(2θ)`, so that `A·(W/s^{η/2})` is the `i = 0` summand of the `ℋⁿ`-integrand. -/
private lemma sq_le_sq_div_sin (A W s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    (A * W) ^ 2 ≤ (A * (W / s ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have heta : s ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs) hs1 (by norm_num [Work.Spaces.eta])
  have hpos : 0 < s ^ Work.Spaces.eta := Real.rpow_pos_of_pos hs _
  have h1 : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ Work.Spaces.eta := by
    rw [← Real.rpow_natCast (s ^ (Work.Spaces.eta / 2)) 2]
    rw [← Real.rpow_mul (le_of_lt hs)]
    norm_num [Work.Spaces.eta]
  simp only [mul_pow, div_pow, h1]
  rw [← mul_div_assoc, le_div_iff₀ hpos]
  exact mul_le_of_le_one_right (by positivity) heta

/-! ## `Ef ≤ HkSq α n` -/

/-- The level-`0` energy is dominated by the `ℋⁿ`-norm for every `n`: the `i = 0` summand of
the integrand of `HkSq α n f` is `(f · w / sin(2θ)^{η/2})²`, which dominates `(f · w)²`
because `sin(2θ)^{η} ≤ 1` on `(0,π/2)` — and the two endpoints of `Iθ` are null. -/
theorem Ef_le_HkSq (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α n f) :
    Work.Coercivity.Ef f ≤ Work.Spaces.HkSq α n f := by
  rw [Work.Coercivity.Ef, Work.Spaces.L2Sq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hmem.2 ?_
  show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz => ?_
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hz) ?_
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  calc (f z θ * Work.Spaces.w z) ^ 2
      ≤ (f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
        sq_le_sq_div_sin _ _ _ hsin (Real.sin_le_one _)
    _ = (Work.Spaces.DzIter 0 f z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        simp
    _ ≤ Work.Spaces.HkIntegrand α n f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α n f z θ 0 (Nat.zero_le n)

/-! ## The target -/

theorem C0_sq_le_HkSq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) (hmem : Work.Spaces.HkMem α n f) :
    (Work.Coercivity.C0 f) ^ 2 ≤ 64 * Work.Spaces.HkSq α n f := by
  have hC0 : (Work.Coercivity.C0 f) ^ 2
      ≤ 64 * Work.Coercivity.Ef f :=
    Work.FTS.CoercivityFix.Transfer.E1Norm.Pieces.C0_sq_le_Ef_CoerAdm α hα hα1 hf
  have hEf : Work.Coercivity.Ef f ≤ Work.Spaces.HkSq α n f := Ef_le_HkSq α n hmem
  linarith

end Work.FTS.CoercivityFix.Transfer.E1Norm
