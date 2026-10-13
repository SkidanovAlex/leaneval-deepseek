/-
# `FTS/GalFields/Tail/FrBoxAux` — factor bounds for the box estimate of the right-hand side

This module collects the `L²`-bounds over the box `bx a b δ` of the individual *factors* which the
per-mode bound (`Tail/perMode_of_slotDom`, via `Tail/FrBox`) needs when it bounds the right-hand
side `Fr α Φs EllSol u` term by term:

* the `u`-side factors (the derivatives `D_z^jD_θ^i u` of the Galerkin profile, the moment
  functionals `L₁₂(u)`, `FK(u)`, and the elliptic atoms `Rop(Φ̃_u)`, `Uop(Φ̃_u)/sin 2θ`,
  `Vop(Φ̃_u)`) are controlled by the a-priori energy `Xn α u = |u|_{ℋ⁴}`;
* each *fixed* atom (`F_*`, its derivatives, `L₁₂(F_*)`, `FK(F_*)`, `AK`, the star atoms,
  `sin 2θ`, `cos 2θ - sin²θ`) is bounded by a constant, since it is a smooth function of `(z,θ)`
  on the (compact) box — for the star atoms and `F_*` this uses `StarPkgo2`, and the boundedness
  on the box is the only thing used (so no global sup bound is needed for the atoms whose angular
  behaviour degenerates at `θ = 0`, such as `∂_θF_*`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.Tail.BoxCalc
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.GalFields.Tail.boxInt_mixed_le_HkSq
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.GalFields.RHS.smoothOpen_atoms_of_gal
import Submission.Work.FTS.GalFields.Norm.abs_mubar_le
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Tail

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Generic helpers -/

/-- `HkSq` is the square of `HkNorm`. -/
theorem HkSq_eq_HkNorm_sq (α : ℝ) (k : ℕ) (f : Fn) :
    Work.Spaces.HkSq α k f = Work.Spaces.HkNorm α k f ^ 2 :=
  (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f)).symm

/-- **A smooth function is bounded on the box.** -/
theorem exists_bound_on_bx {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ2 : δ < Real.pi / 2)
    {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ bx a b δ, |f p.1 p.2| ≤ B := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_bx a b δ)
    ((hf.continuousOn.mono (bx_subset_Q0 ha hδ hδ2)))
  refine ⟨max C 0, le_max_right _ _, fun p hp => ?_⟩
  have h1 : ‖f p.1 p.2‖ ≤ C := hC p hp
  rw [Real.norm_eq_abs] at h1
  exact le_trans h1 (le_max_left _ _)

/-- **The box `L²`-integral of a slot derivative is controlled by the `ℋ⁴`-energy.** -/
theorem binL2_mixed_le' {α : ℝ} (hα : 0 < α) {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hδ2 : δ < Real.pi / 2 - δ) (j i : ℕ) (hji : j + i ≤ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : Fn}, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 4 f →
      binL2 a b δ (fun z θ => Work.Spaces.mixed j i f z θ)
        ≤ C * Work.FTS.Nonlin.Xn α f ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := boxInt_mixed_le_HkSq (α := α) hα a b δ ha hδ hδ2 j i hji
  refine ⟨C, hC0, fun {f} hf hm => ?_⟩
  refine le_trans (hC hf hm) ?_
  rw [HkSq_eq_HkNorm_sq]

/-- **The box `L²`-integral of a bounded smooth function.** -/
theorem binL2_le_of_smoothOpen_bound {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hδ2 : δ < Real.pi / 2) {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∃ B : ℝ, 0 ≤ B ∧
      binL2 a b δ f ≤ B ^ 2 * (volume (bx a b δ)).toReal := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_on_bx ha hδ hδ2 hf
  refine ⟨B, hB0, binL2_le_of_bound ?_ hB⟩
  exact integrableOn_bx_of_continuousOn'
    (((hf.continuousOn.mono (bx_subset_Q0 ha hδ hδ2)).pow 2))

/-- The `L²`-integral of the angular coefficient `sin 2θ` (bounded by `1`). -/
theorem binL2_sin_two_le {a b δ : ℝ} :
    binL2 a b δ (fun _ θ => Real.sin (2 * θ)) ≤ 1 ^ 2 * (volume (bx a b δ)).toReal := by
  refine binL2_le_of_bound ?_ (fun p hp => ?_)
  · exact integrableOn_bx_of_continuousOn'
      (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).pow 2)
  · exact Real.abs_sin_le_one _

/-- The `L²`-integral of the angular coefficient `cos 2θ - sin²θ` (bounded by `2`). -/
theorem binL2_c2m_le {a b δ : ℝ} :
    binL2 a b δ (fun _ θ => Work.Construction.c2m θ) ≤ 2 ^ 2 * (volume (bx a b δ)).toReal := by
  refine binL2_le_of_bound ?_ (fun p _ => ?_)
  · exact integrableOn_bx_of_continuousOn' (((ContinuousOn.sub
      (Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn
      ((Real.continuous_sin.comp continuous_snd).continuousOn.pow 2)).pow 2))
  · rw [abs_le]
    constructor
    · have h1 : -1 ≤ Real.cos (2 * p.2) := Real.neg_one_le_cos _
      have h2 : Real.sin p.2 ^ 2 ≤ 1 := by
        have := Real.sin_sq_le_one p.2; linarith
      simp only [Work.Construction.c2m]; linarith
    · have h1 : Real.cos (2 * p.2) ≤ 1 := Real.cos_le_one _
      have h2 : 0 ≤ Real.sin p.2 ^ 2 := sq_nonneg _
      simp only [Work.Construction.c2m]; linarith

/-- The `L²`-integral of `sin²θ` (bounded by `1`). -/
theorem binL2_sinSq_le {a b δ : ℝ} :
    binL2 a b δ (fun _ θ => Real.sin θ ^ 2) ≤ 1 ^ 2 * (volume (bx a b δ)).toReal := by
  refine binL2_le_of_bound ?_ (fun p _ => ?_)
  · exact integrableOn_bx_of_continuousOn'
      (((Real.continuous_sin.comp continuous_snd).continuousOn.pow 2).pow 2)
  · rw [abs_of_nonneg (sq_nonneg _)]
    exact Real.sin_sq_le_one p.2

end Work.FTS.GalFields.Tail
