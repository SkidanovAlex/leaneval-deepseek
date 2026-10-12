import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseBoxFock.L1Tails.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.chiChiCoulAux` — the vocabulary of the `χχ`-images Coulomb pairing

This module fixes the objects used by `Work.BoseBoxFock.L1Tails.chiChiImages_pairing_coul`
(the design's `T7`, `sources/boseDCF/bose_L1tails.md` §Q1(b)).

The pairing of the `χχ`-images kernel against a smooth `G` is decomposed by the substitution
`z = w − y + ℓ•latVec m` into the `Ḣ⁻¹`–`Ḣ¹` duality (`Work.BoseBoxFock.L1Tails.coulombDual`)
applied to the auxiliary function

  `psiM ℓ m G z = ∫_{‖y‖ ≤ ℓ/2} χ_ℓ(y)·χ_ℓ(z + y − ℓ•latVec m)·G (z + y − ℓ•latVec m) y dy`,

localised by the cutoff `pairTheta R = χ_𝟜R` (un-normalised bump scaled to the closed ball of
radius `4R`, hence `= 1` on the closed ball of radius `R ⊇ tsupport W` and supported in the closed
ball of radius `2R`).

The energy on the right-hand side of `T7` is `pairEnergy`, split as
`pairEnergy = pairDir + pairMass` (the `w`-Dirichlet part and the `ℓ⁻²`-mass part).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real Topology ContDiff

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## 1. The cutoff at scale `R` -/

/-- A bound for `‖fderiv chiBase‖` (exists because `chiBase` is `C¹` with compact support). -/
lemma chiGB_exists : ∃ M : ℝ, ∀ x : E3, ‖fderiv ℝ Submission.BoseGases.chiBase x‖ ≤ M :=
  (Submission.BoseGases.chiBase_hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (Submission.BoseGases.chiBase_contDiff.continuous_fderiv (by simp))

/-- A fixed bound for `‖∇ chiBase‖`. -/
noncomputable def chiGB : ℝ := Classical.choose chiGB_exists

lemma chiBase_fderiv_le_chiGB (x : E3) :
    ‖fderiv ℝ Submission.BoseGases.chiBase x‖ ≤ chiGB := Classical.choose_spec chiGB_exists x

lemma chiGB_nonneg : 0 ≤ chiGB := le_trans (norm_nonneg _) (chiBase_fderiv_le_chiGB 0)

/-- The smooth cutoff `θ_R = χ_{4R}`: equal to `1` on the closed ball of radius `R` and vanishing
off the closed ball of radius `2R`. -/
def pairTheta (R : ℝ) : E3 → ℝ := fun z => Submission.BoseGases.chiBase (((4 * R)⁻¹) • z)

lemma pairTheta_nonneg (R : ℝ) (z : E3) : 0 ≤ pairTheta R z :=
  Submission.BoseGases.chiBase_nonneg _

lemma pairTheta_le_one (R : ℝ) (z : E3) : pairTheta R z ≤ 1 :=
  Submission.BoseGases.chiBase_le_one _

lemma pairTheta_eq_one {R : ℝ} (hR : 0 < R) {z : E3} (hz : ‖z‖ ≤ R) : pairTheta R z = 1 := by
  refine Submission.BoseGases.chiBase_eq_one_of_norm_le ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h4 : (0 : ℝ) < 4 * R := by linarith
  rw [inv_mul_eq_div, div_le_iff₀ h4]
  linarith

lemma pairTheta_eq_zero {R : ℝ} (hR : 0 < R) {z : E3} (hz : 2 * R ≤ ‖z‖) :
    pairTheta R z = 0 := by
  have h4 : (0 : ℝ) < 4 * R := by linarith
  refine Submission.BoseGases.chiBump.zero_of_le_dist ?_
  have hnorm : ‖((4 * R)⁻¹) • z‖ = ‖z‖ / (4 * R) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_eq_div]
  rw [dist_eq_norm, sub_zero, hnorm]
  show (1 : ℝ) / 2 ≤ ‖z‖ / (4 * R)
  rw [le_div_iff₀ h4]
  linarith

lemma pairTheta_contDiff (R : ℝ) : ContDiff ℝ ∞ (pairTheta R) :=
  Submission.BoseGases.chiBase_contDiff.comp (contDiff_id.const_smul _)

lemma pairTheta_hasCompactSupport {R : ℝ} (hR : 0 < R) : HasCompactSupport (pairTheta R) := by
  have hsub : Function.support (pairTheta R) ⊆ Metric.closedBall (0 : E3) (2 * R) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    by_contra hc
    rw [not_le] at hc
    exact hz (pairTheta_eq_zero hR hc.le)
  exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E3) (2 * R))
    (isClosed_tsupport _) (closure_minimal hsub Metric.isClosed_closedBall)

lemma fderiv_pairTheta_apply (R : ℝ) (z w : E3) :
    fderiv ℝ (pairTheta R) z w
      = (4 * R)⁻¹ * fderiv ℝ Submission.BoseGases.chiBase ((4 * R)⁻¹ • z) w := by
  have h1 : HasFDerivAt (fun y : E3 => (4 * R)⁻¹ • y)
      ((4 * R)⁻¹ • ContinuousLinearMap.id ℝ E3) z :=
    (ContinuousLinearMap.id ℝ E3).hasFDerivAt.const_smul ((4 * R)⁻¹)
  have h2 : HasFDerivAt Submission.BoseGases.chiBase
      (fderiv ℝ Submission.BoseGases.chiBase ((4 * R)⁻¹ • z)) ((4 * R)⁻¹ • z) :=
    ((Submission.BoseGases.chiBase_contDiff.differentiable (by simp)).differentiableAt).hasFDerivAt
  have h3 : HasFDerivAt (pairTheta R)
      ((fderiv ℝ Submission.BoseGases.chiBase ((4 * R)⁻¹ • z)).comp
        ((4 * R)⁻¹ • ContinuousLinearMap.id ℝ E3)) z := h2.comp z h1
  rw [h3.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma norm_fderiv_pairTheta_le {R : ℝ} (hR : 0 < R) (z w : E3) :
    ‖fderiv ℝ (pairTheta R) z w‖ ≤ (4 * R)⁻¹ * chiGB * ‖w‖ := by
  rw [fderiv_pairTheta_apply]
  calc ‖(4 * R)⁻¹ * fderiv ℝ Submission.BoseGases.chiBase ((4 * R)⁻¹ • z) w‖
      = |(4 * R)⁻¹| * ‖fderiv ℝ Submission.BoseGases.chiBase ((4 * R)⁻¹ • z) w‖ := by
        rw [norm_mul, Real.norm_eq_abs]
    _ ≤ (4 * R)⁻¹ * (chiGB * ‖w‖) := by
        have h4 : (0 : ℝ) < 4 * R := by linarith
        have h1 : |(4 * R)⁻¹| = (4 * R)⁻¹ := abs_of_nonneg (by positivity)
        rw [h1]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖fderiv ℝ Submission.BoseGases.chiBase ((4 * R)⁻¹ • z) w‖
            ≤ ‖fderiv ℝ Submission.BoseGases.chiBase ((4 * R)⁻¹ • z)‖ * ‖w‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ chiGB * ‖w‖ := mul_le_mul_of_nonneg_right (chiBase_fderiv_le_chiGB _) (norm_nonneg _)
    _ = (4 * R)⁻¹ * chiGB * ‖w‖ := by ring

/-! ## 2. The `χ`-window, the Dirichlet integrand and the auxiliary function `psiM` -/

/-- The complexified window `χ_ℓ`. -/
def chiC (ℓ : ℝ) (x : E3) : ℂ := ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)

/-- The `w`-derivative integrand `V_j(w,y) = ∂_{w_j}(χ_ℓ(w)·G(w,y))` of the energy. -/
def pairVj (ℓ : ℝ) (G : E3 → E3 → ℂ) (j : Fin 3) (w y : E3) : ℂ :=
  fderiv ℝ (fun w' => chiC ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))

/-- The integration domain of the `y`-variable in `psiM`: the closed ball of radius `ℓ/2`. -/
def halfBall (ℓ : ℝ) : Set E3 := Metric.closedBall (0 : E3) (ℓ / 2)

/-- **The auxiliary function `ψ_m`** of the `χχ`-images pairing: the `y`-fold of the two windows
along the image `w = z + y − ℓ•latVec m`. -/
def psiM (ℓ : ℝ) (m : Fin 3 → ℤ) (G : E3 → E3 → ℂ) : E3 → ℂ :=
  fun z => ∫ y in halfBall ℓ,
    chiC ℓ y * chiC ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m) * G (z + y - ℓ • Work.BoseBoxFock.latVec m) y

/-- The `w`-Dirichlet part of the energy (the first summand of the target's right-hand side). -/
def pairDir (ℓ : ℝ) (G : E3 → E3 → ℂ) : ℝ :=
  ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
    ∑ j : Fin 3, ‖pairVj ℓ G j w y‖ ^ 2

/-- The mass part of the energy (the second summand of the target's right-hand side). -/
def pairMass (ℓ : ℝ) (G : E3 → E3 → ℂ) : ℝ :=
  ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
    (ℓ ^ 2)⁻¹ * ‖chiC ℓ w * G w y‖ ^ 2

/-- The `w`-Dirichlet part of the energy, with the order of integration interchanged (the order
produced by the substitution `w = z + y − ℓ•latVec m` of the pairing estimate). -/
def pairDir' (ℓ : ℝ) (G : E3 → E3 → ℂ) : ℝ :=
  ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
    ∑ j : Fin 3, ‖pairVj ℓ G j w y‖ ^ 2

/-- The mass part of the energy, with the order of integration interchanged. -/
def pairMass' (ℓ : ℝ) (G : E3 → E3 → ℂ) : ℝ :=
  ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
    (ℓ ^ 2)⁻¹ * ‖chiC ℓ w * G w y‖ ^ 2

/-- The energy appearing on the right-hand side of `chiChiImages_pairing_coul`, verbatim. -/
def pairEnergy (ℓ : ℝ) (G : E3 → E3 → ℂ) : ℝ :=
  ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
    (∑ j : Fin 3, ‖fderiv ℝ (fun w' =>
        ((Submission.BoseGases.chiScale ℓ w' : ℝ) : ℂ) * G w' y) w
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      + (ℓ ^ 2)⁻¹ * ‖((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * G w y‖ ^ 2)

end Work.BoseBoxFock.L1Tails
