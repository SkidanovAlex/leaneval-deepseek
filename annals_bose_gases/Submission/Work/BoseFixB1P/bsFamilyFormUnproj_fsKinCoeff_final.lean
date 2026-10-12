import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.bsFamilyFormUnproj_fsKinCoeff
import Submission.Work.BoseFixB1P.symA_Ftrunc_pt
import Submission.Work.BoseFixB1P.symA_Ftrunc_quad_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1P.bsFamilyFormUnproj_fsKinCoeff_final`

The **unprojected** moving-box one-body family form of FS's `lem:LocKinEn` at the FS cut-off
symbol `fsKinCoeff c = [· − c]₊²` is diagonal in the `p`-convention Fourier transform:

  `bsFamilyFormUnproj ℓ (fsKinCoeff c) ψ
      = (2π)⁻³ ∫_q symA ℓ (fsKinCoeff c) q · ‖kinFT ψ q‖² dq`.

## The argument (monotone convergence along the radial truncations)

The cut-off `fsKinCoeff c = [· − c]₊²` grows quadratically and is *not* `L¹` in the radial
variable, so the `L¹` symbol identity `Work.OneBodyKin.bsFamilyFormUnproj_eq_symbol` does not apply
to it directly.  It is the increasing pointwise limit of the truncated symbols
`Ftrunc c n` (`Work.OneBodyKin.TruncDefs`), which *are* `L¹`, nonnegative and bounded.  So for
every smooth compactly supported `ψ`

  `bsFamilyFormUnproj ℓ (Ftrunc c n) ψ
      = (2π)⁻³ ∫_q symA ℓ (Ftrunc c n) q ‖kinFT ψ q‖² dq`   (`bsFamilyFormUnproj_eq_symbol`),

and it remains to let `n → ∞` on both sides:

* **the left side** is `Work.BoseFixB1.bsFamilyFormUnproj_Ftrunc_tendsto` (monotone convergence in
  the box centre `u`, already in the corpus);
* **the right side** is `symA_integral_tendsto_aux` below: the `q`-integrand is dominated by
  `(A + B) D² (1 + ‖q‖)^{-10}`, the three inputs being the uniform-in-`n` quadratic growth of the
  truncated symbol (`symA_Ftrunc_quad_bound`), the Schwartz decay of `kinFT ψ`
  (`Work.OneBodyKin.kinFT_decay_le`) and the pointwise convergence `symA_Ftrunc_pt`, so that
  dominated convergence in `q` applies.

The two limits coincide because `ℝ` is Hausdorff (`tendsto_nhds_unique`).
-/

namespace Work.BoseFixB1P

noncomputable section

open MeasureTheory Filter
open scoped Topology Real ContDiff

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 0. The two inputs of the dominated-convergence step

These are the proved child lemmas of `Submission/Work/BoseFixB1P/`
(`symA_Ftrunc_pt.lean`, `symA_Ftrunc_quad_bound.lean`); they are the only analytic content of the
right-hand-side passage, everything else below is the standard dominated-convergence assembly. -/

/-- **The right-hand side converges along the radial truncations** (dominated convergence in `q`),
given the pointwise convergence of the symbol and its uniform-in-`n` quadratic growth. -/
private theorem symA_integral_tendsto_aux {ℓ c : ℝ} (hℓ : 0 < ℓ)
    (hpt : ∀ q : ℝ³, Filter.Tendsto
      (fun n : ℕ => Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q)
      Filter.atTop (nhds (Work.OneBodyKin.symA ℓ (Submission.BoseGases.fsKinCoeff c) q)))
    (hqb : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (n : ℕ) (q : ℝ³),
      |Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q| ≤ A * ‖q‖ ^ 2 + B)
    {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Filter.Tendsto (fun n : ℕ => ∫ q : ℝ³,
        Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q *
          ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
      Filter.atTop
      (nhds (∫ q : ℝ³,
        Work.OneBodyKin.symA ℓ (Submission.BoseGases.fsKinCoeff c) q *
          ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)) := by
  obtain ⟨A, B, hA0, hB0, hbnd⟩ := hqb
  -- ## 1. Schwartz decay of the test function: `‖kinFT ψ q‖ ≤ D (1+‖q‖)⁻⁶`
  obtain ⟨D, _hD0, hDdec⟩ := Work.OneBodyKin.kinFT_decay_le 6
    (Complex.ofRealCLM.contDiff.comp hψ) (hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0))
  -- ## 2. the dominating function `(A+B)D²(1+‖q‖)⁻¹⁰` is integrable in dimension three
  have hone : MeasureTheory.Integrable (fun q : ℝ³ => (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))) := by
    refine integrable_one_add_norm (E := ℝ³) (μ := volume) (r := ((10 : ℕ) : ℝ)) ?_
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hGint : MeasureTheory.Integrable
      (fun q : ℝ³ => (A + B) * D ^ 2 * (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))) :=
    hone.const_mul _
  -- ## 3. pointwise domination of the integrands
  have hbound : ∀ n : ℕ, ∀ᵐ q ∂(volume : Measure ℝ³),
      ‖Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q *
          ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2‖
        ≤ (A + B) * D ^ 2 * (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ)) := by
    intro n
    refine Eventually.of_forall (fun q => ?_)
    have hpos : (0 : ℝ) < 1 + ‖q‖ := by positivity
    -- the symbol grows at most quadratically in `q`, uniformly in `n`
    have h1 : |Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q|
        ≤ (A + B) * (1 + ‖q‖) ^ 2 := by
      have hsq : ‖q‖ ^ 2 ≤ (1 + ‖q‖) ^ 2 := by nlinarith [norm_nonneg q]
      have hone2 : (1 : ℝ) ≤ (1 + ‖q‖) ^ 2 := by nlinarith [norm_nonneg q]
      have hA' : A * ‖q‖ ^ 2 ≤ A * (1 + ‖q‖) ^ 2 := mul_le_mul_of_nonneg_left hsq hA0
      have hB' : B ≤ B * (1 + ‖q‖) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hone2 hB0, hB0]
      have hsum : A * (1 + ‖q‖) ^ 2 + B * (1 + ‖q‖) ^ 2
          = (A + B) * (1 + ‖q‖) ^ 2 := by ring
      linarith [hbnd n q, hA', hB', hsum]
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
      rw [show (-((10 : ℕ) : ℝ)) = (2 : ℝ) + (-((12 : ℕ) : ℝ)) by norm_num, Real.rpow_add hpos]
      norm_num
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖), hrw]
    calc |Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q|
            * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
        ≤ ((A + B) * (1 + ‖q‖) ^ 2) * (D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ))) :=
          mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = (A + B) * D ^ 2 * ((1 + ‖q‖) ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ))) := by ring
  -- ## 4. each member of the sequence is integrable (via `integrable_q_pieces`), hence a.e. strongly
  -- measurable
  have hInt : ∀ n : ℕ, MeasureTheory.Integrable (fun q : ℝ³ =>
      Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2) := fun n =>
    (Work.OneBodyKin.integrable_q_pieces hℓ (Work.OneBodyKin.integrable_Ftrunc c n)
      (Work.OneBodyKin.Ftrunc_nonneg c n) ψ hψ hcs).1
  -- ## 5. pointwise convergence in `n`, then dominated convergence
  have hlim : ∀ᵐ q ∂(volume : Measure ℝ³), Filter.Tendsto
      (fun n : ℕ => Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
      Filter.atTop
      (nhds (Work.OneBodyKin.symA ℓ (Submission.BoseGases.fsKinCoeff c) q *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)) :=
    Eventually.of_forall (fun q => (hpt q).mul_const _)
  exact tendsto_integral_of_dominated_convergence _
    (fun n => (hInt n).aestronglyMeasurable) hGint hbound hlim

/-- **The right-hand side of the FS cut-off identity converges along the radial truncations.**

This is the public form of `symA_integral_tendsto_aux` with its two analytic inputs supplied by the
child lemmas `Work.BoseFixB1P.symA_Ftrunc_pt` (pointwise convergence of the symbol) and
`Work.BoseFixB1P.symA_Ftrunc_quad_bound` (its uniform-in-`n` quadratic growth). -/
theorem symA_Ftrunc_integral_tendsto {ℓ c : ℝ} (hℓ : 0 < ℓ)
    {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Filter.Tendsto (fun n : ℕ => ∫ q : ℝ³,
        Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q *
          ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
      Filter.atTop
      (nhds (∫ q : ℝ³,
        Work.OneBodyKin.symA ℓ (Submission.BoseGases.fsKinCoeff c) q *
          ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)) :=
  symA_integral_tendsto_aux hℓ
    (fun q => Work.BoseFixB1P.symA_Ftrunc_pt (ℓ := ℓ) (c := c) hℓ q)
    (Work.BoseFixB1P.symA_Ftrunc_quad_bound (ℓ := ℓ) (c := c) hℓ) hψ hcs

/-- **The FS cut-off identity for the unprojected moving-box family form.** -/
theorem bsFamilyFormUnproj_fsKinCoeff_final {ℓ c : ℝ} (hℓ : 0 < ℓ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Work.BSKinetic.bsFamilyFormUnproj ℓ (Submission.BoseGases.fsKinCoeff c) ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          Work.OneBodyKin.symA ℓ (Submission.BoseGases.fsKinCoeff c) q *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 := by
  -- the two sides converge along the truncations
  have hL := Work.BoseFixB1.bsFamilyFormUnproj_Ftrunc_tendsto (ℓ := ℓ) (c := c) hℓ hψ hcs
  have hrhs := symA_Ftrunc_integral_tendsto (ℓ := ℓ) (c := c) hℓ hψ hcs
  -- the truncated identity
  have hstep : ∀ n : ℕ,
      Work.BSKinetic.bsFamilyFormUnproj ℓ (Work.OneBodyKin.Ftrunc c n) ψ
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
            Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q *
              ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 :=
    fun n => Work.OneBodyKin.bsFamilyFormUnproj_eq_symbol hℓ
      (Work.OneBodyKin.integrable_Ftrunc c n) (Work.OneBodyKin.Ftrunc_nonneg c n) ψ hψ hcs
  have hL' := hL.congr' (Filter.Eventually.of_forall hstep)
  have hR' := hrhs.const_mul (((2 * Real.pi) ^ 3)⁻¹)
  exact tendsto_nhds_unique hL' hR'

end

end Work.BoseFixB1P
