import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.chiChiCoulAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.pairEnergy_bookkeeping`

The bookkeeping identities for the energy `pairEnergy` of the `χχ`-images pairing
(`Work.BoseBoxFock.L1Tails.chiChiImages_pairing_coul`, the design's `T7`):

    `pairEnergy ℓ G = pairDir ℓ G + pairMass ℓ G`,   `pairDir = pairDir'`,
    `pairMass = pairMass'`,   `0 ≤ pairDir`,   `0 ≤ pairMass`.

Splitting the integrand pointwise corresponds exactly to splitting the *iterated* integral, by
Fubini/additivity for the Bochner integral.  Both summands are jointly continuous
(`pairVj` is the derivative in the *first* variable of the smooth uncurried product
`pairF ℓ G (w,y) = χ_ℓ(w)·G(w,y)`, applied to a fixed direction), hence integrable on the compact
box `Λ(ℓ) × Λ(ℓ)`; the order swap is Fubini (`integral_integral_swap`) and the two signs are
`integral_nonneg_of_ae`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real Topology ContDiff

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## 1. The integrands -/

/-- The corpus box `Λ(ℓ)` of side `ℓ`. -/
abbrev pairBox (ℓ : ℝ) : Set E3 := Work.BoseK15.corpusBox.boxL ℓ

/-- The smooth uncurried windowed product `χ_ℓ(w)·G(w,y)`. -/
def pairF (ℓ : ℝ) (G : E3 → E3 → ℂ) : E3 × E3 → ℂ :=
  fun p => chiC ℓ p.1 * G p.1 p.2

/-- The Dirichlet integrand `Σ_j ‖∂_{w_j}(χ_ℓ G)‖²` of `pairDir`. -/
def pairRowA (ℓ : ℝ) (G : E3 → E3 → ℂ) : E3 → E3 → ℝ :=
  fun w y => ∑ j : Fin 3, ‖pairVj ℓ G j w y‖ ^ 2

/-- The mass integrand `ℓ⁻²‖χ_ℓ G‖²` of `pairMass`. -/
def pairRowM (ℓ : ℝ) (G : E3 → E3 → ℂ) : E3 → E3 → ℝ :=
  fun w y => (ℓ ^ 2)⁻¹ * ‖chiC ℓ w * G w y‖ ^ 2

/-! ## 2. The unfolding of the five definitions -/

lemma pairEnergy_eq (ℓ : ℝ) (G : E3 → E3 → ℂ) :
    pairEnergy ℓ G = ∫ w in pairBox ℓ, ∫ y in pairBox ℓ,
      (pairRowA ℓ G w y + pairRowM ℓ G w y) := by
  simp only [pairEnergy, pairRowA, pairRowM, pairVj, chiC, pairBox]

lemma pairDir_eq (ℓ : ℝ) (G : E3 → E3 → ℂ) :
    pairDir ℓ G = ∫ w in pairBox ℓ, ∫ y in pairBox ℓ, pairRowA ℓ G w y := by
  simp only [pairDir, pairRowA, pairVj, chiC, pairBox]

lemma pairMass_eq (ℓ : ℝ) (G : E3 → E3 → ℂ) :
    pairMass ℓ G = ∫ w in pairBox ℓ, ∫ y in pairBox ℓ, pairRowM ℓ G w y := by
  simp only [pairMass, pairRowM, chiC, pairBox]

lemma pairDir'_eq (ℓ : ℝ) (G : E3 → E3 → ℂ) :
    pairDir' ℓ G = ∫ y in pairBox ℓ, ∫ w in pairBox ℓ, pairRowA ℓ G w y := by
  simp only [pairDir', pairRowA, pairVj, chiC, pairBox]

lemma pairMass'_eq (ℓ : ℝ) (G : E3 → E3 → ℂ) :
    pairMass' ℓ G = ∫ y in pairBox ℓ, ∫ w in pairBox ℓ, pairRowM ℓ G w y := by
  simp only [pairMass', pairRowM, chiC, pairBox]

/-! ## 3. Smoothness of `pairF` and the derivative in the first variable -/

lemma contDiff_pairF {ℓ : ℝ} (hℓ : ℓ ≠ 0) {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    ContDiff ℝ (⊤ : ℕ∞) (pairF ℓ G) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : E3 × E3 => ((Submission.BoseGases.chiScale ℓ p.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((Submission.BoseGases.chiScale_contDiff hℓ).comp contDiff_fst)
  exact h1.mul hG

/-- The derivative of `w' ↦ pairF ℓ G (w', y)` at `w`, as the total derivative composed with
the inclusion `E3 → E3 × E3`, `w ↦ (w, y)`. -/
lemma fderiv_pairF_fst {ℓ : ℝ} {G : E3 → E3 → ℂ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (pairF ℓ G)) (w y : E3) :
    fderiv ℝ (fun w' : E3 => pairF ℓ G (w', y)) w
      = (fderiv ℝ (pairF ℓ G) (w, y)).comp (ContinuousLinearMap.inl ℝ E3 E3) := by
  have hd : HasFDerivAt (pairF ℓ G) (fderiv ℝ (pairF ℓ G) (w, y)) (w, y) :=
    ((hF.differentiable (by simp)) (w, y)).hasFDerivAt
  have hi : HasFDerivAt (fun w' : E3 => (w', y)) (ContinuousLinearMap.inl ℝ E3 E3) w := by
    have h : HasFDerivAt (fun w' : E3 => (ContinuousLinearMap.inl ℝ E3 E3) w' + ((0 : E3), y))
        (ContinuousLinearMap.inl ℝ E3 E3) w :=
      (ContinuousLinearMap.inl ℝ E3 E3).hasFDerivAt.add_const ((0 : E3), y)
    simpa using h
  exact (hd.comp w hi).fderiv

/-! ## 4. Continuity of the two integrands -/

private lemma continuous_pairVj {ℓ : ℝ} (hℓ : ℓ ≠ 0) {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) (j : Fin 3) :
    Continuous (fun p : E3 × E3 => pairVj ℓ G j p.1 p.2) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (pairF ℓ G) := contDiff_pairF hℓ hG
  have hd : Continuous (fun p : E3 × E3 => fderiv ℝ (pairF ℓ G) p) :=
    hF.continuous_fderiv (by simp)
  have hv : Continuous (fun _ : E3 × E3 =>
      (ContinuousLinearMap.inl ℝ E3 E3) (EuclideanSpace.single j 1)) := continuous_const
  refine (Continuous.clm_apply hd hv).congr ?_
  intro p
  obtain ⟨w, y⟩ := p
  have h1 : fderiv ℝ (fun w' : E3 => pairF ℓ G (w', y)) w (EuclideanSpace.single j 1)
      = pairVj ℓ G j w y := by
    simp only [pairVj, chiC, pairF]
  rw [← h1, fderiv_pairF_fst hF w y]
  simp [ContinuousLinearMap.comp_apply]

lemma continuous_pairRowA {ℓ : ℝ} (hℓ : ℓ ≠ 0) {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    Continuous (fun p : E3 × E3 => pairRowA ℓ G p.1 p.2) := by
  simp only [pairRowA]
  exact continuous_finsetSum Finset.univ
    (fun j _ => (continuous_pairVj hℓ hG j).norm.pow 2)

lemma continuous_pairRowM {ℓ : ℝ} {G : E3 → E3 → ℂ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (pairF ℓ G)) :
    Continuous (fun p : E3 × E3 => pairRowM ℓ G p.1 p.2) := by
  have h : Continuous (fun p : E3 × E3 => ‖chiC ℓ p.1 * G p.1 p.2‖ ^ 2) :=
    hF.continuous.norm.pow 2
  exact h.const_mul ((ℓ ^ 2)⁻¹)

/-! ## 5. The bookkeeping -/

theorem pairEnergy_bookkeeping {ℓ : ℝ} (hℓ : 0 < ℓ) {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    Work.BoseBoxFock.L1Tails.pairEnergy ℓ G
        = Work.BoseBoxFock.L1Tails.pairDir ℓ G + Work.BoseBoxFock.L1Tails.pairMass ℓ G
      ∧ Work.BoseBoxFock.L1Tails.pairDir ℓ G = Work.BoseBoxFock.L1Tails.pairDir' ℓ G
      ∧ Work.BoseBoxFock.L1Tails.pairMass ℓ G = Work.BoseBoxFock.L1Tails.pairMass' ℓ G
      ∧ 0 ≤ Work.BoseBoxFock.L1Tails.pairDir ℓ G
      ∧ 0 ≤ Work.BoseBoxFock.L1Tails.pairMass ℓ G := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hF : ContDiff ℝ (⊤ : ℕ∞) (pairF ℓ G) := contDiff_pairF hℓne hG
  have hAcont := continuous_pairRowA hℓne hG
  have hMcont := continuous_pairRowM hF
  have hBc : IsCompact (pairBox ℓ) := Work.BoseB4.BoxData.boxL_compact _ ℓ
  have hK : IsCompact (pairBox ℓ ×ˢ pairBox ℓ) := hBc.prod hBc
  have hAi : Integrable (fun p : E3 × E3 => pairRowA ℓ G p.1 p.2)
      ((volume.restrict (pairBox ℓ)).prod (volume.restrict (pairBox ℓ))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact hK hAcont.continuousOn
  have hMi : Integrable (fun p : E3 × E3 => pairRowM ℓ G p.1 p.2)
      ((volume.restrict (pairBox ℓ)).prod (volume.restrict (pairBox ℓ))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact hK hMcont.continuousOn
  have hE := pairEnergy_eq ℓ G
  have hD := pairDir_eq ℓ G
  have hMa := pairMass_eq ℓ G
  have hD' := pairDir'_eq ℓ G
  have hMa' := pairMass'_eq ℓ G
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hE, hD, hMa]
    exact integral_integral_add hAi hMi
  · rw [hD, hD']
    exact integral_integral_swap hAi
  · rw [hMa, hMa']
    exact integral_integral_swap hMi
  · rw [hD]
    refine integral_nonneg_of_ae ?_
    filter_upwards with w
    refine integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => ?_)
    exact Finset.sum_nonneg fun j _ => by positivity
  · rw [hMa]
    refine integral_nonneg_of_ae ?_
    filter_upwards with w
    refine integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => ?_)
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg ℓ)) (by positivity)

end Work.BoseBoxFock.L1Tails
