import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1P.bsFamilyFormUnproj_fsKinCoeff_final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Smear.bsFamilyFormUnproj_le_mix`

The transfer step turning a **pointwise** bound on the symbol `symA a (fsKinCoeff c)` of the
*unprojected* moving-box family into a bound on the family form itself.  This is the companion of
`Work.BoseFixB1.Smear.bsFamilyForm_le_mix` (the *projected* sibling), which is proved by the same
argument with `famSym` in place of `symA`.

The identity

    `bsFamilyFormUnproj a (fsKinCoeff c) ψ
        = (2π)⁻³ ∫_q symA a (fsKinCoeff c) q · ‖kinFT ψ q‖² dq`

for the FS cut-off `fsKinCoeff c = [·−c]₊²` is
`Work.BoseFixB1P.bsFamilyFormUnproj_fsKinCoeff_final` (the `L¹` case
`Work.OneBodyKin.bsFamilyFormUnproj_eq_symbol` plus monotone convergence along the radial
truncations).  The only thing that can go wrong in passing from the pointwise bound to the
integral bound is *integrability* of the left integrand, so the content of this file is:

* `symA_fsKinCoeff_abs_bound`: the symbol at the FS cutoff grows at most quadratically,
  `|symA a (fsKinCoeff c) q| ≤ A‖q‖² + B`, obtained as the pointwise limit of the uniform
  truncated bound `Work.BoseFixB1P.symA_Ftrunc_quad_bound` along
  `Work.BoseFixB1P.symA_Ftrunc_pt`;
* `aeStronglyMeasurable_symA_mul`: the `q`-integrand is a.e. strongly measurable (limit of the
  `L¹` truncants `Work.OneBodyKin.integrable_q_pieces`, via `aestronglyMeasurable_of_tendsto_ae`);
* `integrable_symA_mul`: hence the `q`-integrand is `L¹`, using the Schwartz decay of `kinFT ψ`
  (`Work.OneBodyKin.kinFT_decay_le`) against the quadratic growth;
* `bsFamilyFormUnproj_le_mix`: rewrite the left side by the symbol identity and compare
  integrands pointwise (`MeasureTheory.integral_mono_ae`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Smear

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 1. Quadratic growth of the unprojected symbol at the full FS cutoff -/

/-- **The symbol of the unprojected moving-box family at the FS cutoff grows at most
quadratically.**  The bound is uniform in the cutoff parameter and follows from the uniform
truncated bound `Work.BoseFixB1P.symA_Ftrunc_quad_bound` by passing to the pointwise limit
`Work.BoseFixB1P.symA_Ftrunc_pt`. -/
private lemma symA_fsKinCoeff_abs_bound {a c : ℝ} (ha : 0 < a) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ q : ℝ³,
      |Work.OneBodyKin.symA a (Submission.BoseGases.fsKinCoeff c) q| ≤ A * ‖q‖ ^ 2 + B := by
  obtain ⟨A, B, hA0, hB0, hbnd⟩ :=
    Work.BoseFixB1P.symA_Ftrunc_quad_bound (ℓ := a) (c := c) ha
  refine ⟨A, B, hA0, hB0, fun q => ?_⟩
  refine le_of_tendsto ((Work.BoseFixB1P.symA_Ftrunc_pt (ℓ := a) (c := c) ha q).abs) ?_
  exact Filter.Eventually.of_forall (fun n => hbnd n q)

/-! ## 2. A.e. strong measurability of the integrand -/

/-- **The `q`-integrand of the symbol identity is a.e. strongly measurable.**  The truncated
symbols `Ftrunc c n` are `L¹`, so each member of the approximating sequence is `L¹`
(`Work.OneBodyKin.integrable_q_pieces`) and the pointwise limit is a.e. strongly measurable. -/
private lemma aeStronglyMeasurable_symA_mul {a c : ℝ} (ha : 0 < a) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    AEStronglyMeasurable (fun q : ℝ³ =>
      Work.OneBodyKin.symA a (Submission.BoseGases.fsKinCoeff c) q *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2) := by
  let w : ℝ³ → ℝ := fun q => ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
  have hInt : ∀ n : ℕ, Integrable (fun q : ℝ³ =>
      Work.OneBodyKin.symA a (Work.OneBodyKin.Ftrunc c n) q * w q) := fun n =>
    (Work.OneBodyKin.integrable_q_pieces (ℓ := a) ha (Work.OneBodyKin.integrable_Ftrunc c n)
      (Work.OneBodyKin.Ftrunc_nonneg c n) ψ hψ hcs).1
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun q : ℝ³ =>
      Work.OneBodyKin.symA a (Work.OneBodyKin.Ftrunc c n) q * w q) :=
    fun n => (hInt n).aestronglyMeasurable
  have hlim : ∀ᵐ q ∂(volume : Measure ℝ³), Filter.Tendsto
      (fun n : ℕ => Work.OneBodyKin.symA a (Work.OneBodyKin.Ftrunc c n) q * w q)
      Filter.atTop
      (nhds (Work.OneBodyKin.symA a (Submission.BoseGases.fsKinCoeff c) q * w q)) :=
    Filter.Eventually.of_forall (fun q =>
      (Work.BoseFixB1P.symA_Ftrunc_pt (ℓ := a) (c := c) ha q).mul_const (w q))
  exact aestronglyMeasurable_of_tendsto_ae Filter.atTop hmeas hlim

/-! ## 3. Integrability of the integrand -/

/-- **The `q`-integrand of the symbol identity at the FS cutoff is `L¹`** for every smooth
compactly supported `ψ`: quadratic growth of the symbol against the Schwartz decay of `kinFT ψ`. -/
private lemma integrable_symA_mul {a c : ℝ} (ha : 0 < a) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun q : ℝ³ =>
      Work.OneBodyKin.symA a (Submission.BoseGases.fsKinCoeff c) q *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2) := by
  obtain ⟨A, B, hA0, hB0, hbnd⟩ := symA_fsKinCoeff_abs_bound (c := c) ha
  have hψc : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => (ψ z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hψ
  have hcsc : HasCompactSupport (fun z : ℝ³ => (ψ z : ℂ)) :=
    hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  obtain ⟨D, _hD0, hDdec⟩ := Work.OneBodyKin.kinFT_decay_le 6 hψc hcsc
  have hone : Integrable (fun q : ℝ³ => (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))) := by
    refine integrable_one_add_norm (E := ℝ³) (μ := volume) (r := ((10 : ℕ) : ℝ)) ?_
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hGint : Integrable (fun q : ℝ³ => (A + B) * D ^ 2 * (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))) :=
    hone.const_mul _
  refine Integrable.mono' hGint (aeStronglyMeasurable_symA_mul ha hψ hcs) ?_
  refine Filter.Eventually.of_forall (fun q => ?_)
  have hpos : (0 : ℝ) < 1 + ‖q‖ := by positivity
  -- the symbol grows at most quadratically in `q`
  have h1 : |Work.OneBodyKin.symA a (Submission.BoseGases.fsKinCoeff c) q|
      ≤ (A + B) * (1 + ‖q‖) ^ 2 := by
    have hsq : ‖q‖ ^ 2 ≤ (1 + ‖q‖) ^ 2 := by nlinarith [norm_nonneg q]
    have hone2 : (1 : ℝ) ≤ (1 + ‖q‖) ^ 2 := by nlinarith [norm_nonneg q]
    have hA' : A * ‖q‖ ^ 2 ≤ A * (1 + ‖q‖) ^ 2 := mul_le_mul_of_nonneg_left hsq hA0
    have hB' : B ≤ B * (1 + ‖q‖) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hone2 hB0, hB0]
    have hsum : A * (1 + ‖q‖) ^ 2 + B * (1 + ‖q‖) ^ 2 = (A + B) * (1 + ‖q‖) ^ 2 := by ring
    linarith [hbnd q, hA', hB', hsum]
  -- and the test function decays like `(1+‖q‖)⁻⁶`
  have h2 : ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
      ≤ D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ)) := by
    calc ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
        ≤ (D / (1 + ‖q‖) ^ 6) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hDdec q) 2
      _ = D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ)) := by
          rw [div_pow, div_eq_mul_inv, show ((1 + ‖q‖) ^ 6) ^ 2 = (1 + ‖q‖) ^ 12 by ring,
            Real.rpow_neg hpos.le, Real.rpow_natCast]
  have hrw : (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))
      = (1 + ‖q‖) ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ)) := by
    rw [show (-((10 : ℕ) : ℝ)) = (2:ℝ) + (-((12 : ℕ) : ℝ)) by norm_num, Real.rpow_add hpos]
    norm_num
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖), hrw]
  calc |Work.OneBodyKin.symA a (Submission.BoseGases.fsKinCoeff c) q| *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
      ≤ ((A + B) * (1 + ‖q‖) ^ 2) * (D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ))) :=
        mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    _ = (A + B) * D ^ 2 * ((1 + ‖q‖) ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ))) := by ring

/-! ## 4. The transfer step -/

/-- **The pointwise symbol bound transfers to the *unprojected* family form.**

The companion of `Work.BoseFixB1.Smear.bsFamilyForm_le_mix` for the *unprojected* moving-box
family (whose symbol is `Work.OneBodyKin.symA`, the object of the smearing crux
`Work.BoseFixB1.Smear.symA_le_mix`, which is PROVED): if `symA a (fsKinCoeff c)` is pointwise
dominated by the two-cut mixture plus the constant payment `p`, then the unprojected family form
of a smooth compactly supported state is dominated by the corresponding fixed-state words.

The family form is the Fourier integral of its symbol —
`Work.OneBodyKin.bsFamilyFormUnproj_eq_symbol` for `L¹` symbols, extended to the FS cutoff
`fsKinCoeff c = [·-c]₊²` by monotone convergence exactly as
`Work.OneBodyKin.SymbolIntegral_fsKinCoeff` does for the projected sibling (the truncation
machinery is `Submission.Work.OneBodyKin.TruncDefs`/`symA_Ftrunc_pt`/`symA_Ftrunc_quad_bound`,
and `Submission.Work.BoseFixB1P/bsFamilyFormUnproj_fsKinCoeff_final.lean` states the identity) —
so once the identity is available the transfer is the same `integral_mono_ae` + `(2π)⁻³`-scaling
argument as in the *projected* sibling `Smear/bsFamilyForm_le_mix` (PROVED, use as a template).
Integrability of `symA a (fsKinCoeff c) q · ‖kinFT ψ q‖²` may be assumed as `hint`. -/
theorem bsFamilyFormUnproj_le_mix {a c c₁ c₂ ε p : ℝ} (ha : 0 < a) (hε : 0 ≤ ε)
    (hsym : ∀ q : EuclideanSpace ℝ (Fin 3),
      Work.OneBodyKin.symA a (Submission.BoseGases.fsKinCoeff c) q ≤
        (1 - ε) * Submission.BoseGases.fsKinCoeff c₁ ‖q‖
          + ε * Submission.BoseGases.fsKinCoeff c₂ ‖q‖ + p)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ)
    (hint : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      ((1 - ε) * Submission.BoseGases.fsKinCoeff c₁ ‖q‖
        + ε * Submission.BoseGases.fsKinCoeff c₂ ‖q‖ + p) *
        ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2)) :
    Work.BSKinetic.bsFamilyFormUnproj a (Submission.BoseGases.fsKinCoeff c) ψ
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          ((1 - ε) * Submission.BoseGases.fsKinCoeff c₁ ‖q‖
            + ε * Submission.BoseGases.fsKinCoeff c₂ ‖q‖ + p) *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 := by
  -- the symbol identity: the (unprojected) family form *is* the Fourier integral of its symbol
  rw [Work.BoseFixB1P.bsFamilyFormUnproj_fsKinCoeff_final (ℓ := a) (c := c) ha hψ hcs]
  -- the integrands are pointwise ordered and both are `L¹`, so the integrals are ordered
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact MeasureTheory.integral_mono_ae (integrable_symA_mul ha hψ hcs) hint
    (Filter.Eventually.of_forall (fun q =>
      mul_le_mul_of_nonneg_right (hsym q) (sq_nonneg _)))

end Work.BoseFixB1.Smear
