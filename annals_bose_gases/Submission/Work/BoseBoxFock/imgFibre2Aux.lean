import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.imagesFibre
import Submission.Work.BoseBoxFock.setIntegral_insertCoord2_slice
import Submission.Work.BoseFixB1S.integral_sq_le_measure_mul_integral_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibre2Aux` — the analytic toolkit of the mirror fibre `imgFibre₂`

This module collects the elementary lemmas that the energy bound
`Work.BoseBoxFock.imgFibre2EnergyLe` for the *mirror* position-space fibre
`imgFibre₂ ℓ p F₁ G` (the `p.2`-slot average, `imagesFibre`) rests on.

The fibre is

    imgFibre₂ ℓ p F₁ G u v = ℓ⁻³ ∫_{x'} ∫_{s ∈ boxL} F₁ (ins p u s x') · G (ins p u v x')

and the energy bound differentiates it in the *first* variable `u` (which sits in the slot `p.1`
of both `F₁` and `G`).  The hypothesis of the target is that `F₁` is **independent of the slot
`p.1`** (`F₁ (Function.update x p.1 t) = F₁ x`); hence

* the `F₁`-factor of the fibre is `u`-independent (so the `u`-derivative falls on `G` alone), and
* the `u`-slice content `∫_{x'}∫_s F₁(ins p u s x')²` is *constant* in `u`,

which is exactly what makes the two Cauchy–Schwarz bounds of the target (the mass row and the
`χ`-weighted Dirichlet row) close with the announced constants.

## Contents

* `slotInsCLM` — the (continuous linear) insertion `w ↦ Function.update 0 i w`, together with
  `slotInsCLM_apply` and its value at a basis vector `EuclideanSpace.single j 1`;
* `insertCoord2_update_fst` — `ins p u v x' = Function.update (ins p 0 v x') p.1 u`;
* the chain rule for the insertion (`hasFDerivAt_insertCoord2_fst`, `fderiv_...`);
* independence of the inserted `F₁` under `hF₁ind`, and the vanishing of its `u`-derivative;
* the product/chain rule for the parametrised integrand
  `u ↦ F₁ (ins p u s x') * G (ins p u v x')`, whose derivative is
  `F₁ (ins p 0 s x') • ((fderiv ℝ G (ins p u v x')).comp (slotInsCLM p.1))`;
* `img2Integrand` — the joint integrand of the fibre, and the smoothness of the fibre
  (`contDiff_one_imgFibre₂`, `continuous_imgFibre₂`);
* `fderiv_imgFibre₂_fst_apply` — the derivative formula used by the Cauchy–Schwarz step.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- The complementary fibre index type of the two removed slots `p.1`, `p.2`. -/
abbrev pairFib2 (n : ℕ) (p : Fin n × Fin n) : Type := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}

/-! ## 1. The linear insertion of a slot value -/

/-- **The linear insertion** `w ↦ Function.update 0 i w`: the continuous linear map that puts `w`
in the slot `i` of the zero configuration and leaves all other slots `0`.  Its image is exactly the
`i`-th coordinate line of `Xn n`, so it is the derivative of every coordinate insertion. -/
noncomputable def slotInsCLM (n : ℕ) (i : Fin n) : E3 →L[ℝ] (Xn n) :=
  ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ E3))

/-- The value of `slotInsCLM n i` at `w` is the one-slot insertion. -/
lemma slotInsCLM_apply {n : ℕ} (i : Fin n) (w : E3) :
    slotInsCLM n i w = Function.update (0 : Xn n) i w := by
  funext k
  simp only [slotInsCLM, ContinuousLinearMap.pi_apply, Function.update_apply]
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

/-- The value of `slotInsCLM n i` at a basis vector is the slot-direction vector `slotDirVec`. -/
lemma slotInsCLM_single {n : ℕ} (i : Fin n) (j : Fin 3) :
    slotInsCLM n i (EuclideanSpace.single j (1 : ℝ)) = slotDirVec i j := by
  rw [slotInsCLM_apply]
  rfl

/-! ## 2. The insertion as an update of the `p.1`-slot -/

/-- **The two-slot insertion is an update of its `p.1`-slot**: inserting `u` in the slot `p.1` is
the same as taking the configuration with `0` in that slot and updating it to `u`. -/
lemma insertCoord2_update_fst {n : ℕ} (p : Fin n × Fin n) (v : E3)
    (x' : pairFib2 n p → E3) (u : E3) :
    insertCoord2 p u v x' = Function.update (insertCoord2 p 0 v x') p.1 u := by
  funext k
  simp only [insertCoord2_eq, Function.update_apply]
  by_cases h1 : k = p.1 <;> simp [h1]

/-- The function-level form of `insertCoord2_update_fst`. -/
lemma insertCoord2_update_fst_fun {n : ℕ} (p : Fin n × Fin n) (v : E3)
    (x' : pairFib2 n p → E3) :
    (fun u : E3 => insertCoord2 p u v x') = Function.update (insertCoord2 p 0 v x') p.1 := by
  funext u
  exact insertCoord2_update_fst p v x' u

/-- **The derivative of the coordinate insertion** (in the `p.1`-slot) is the linear insertion. -/
lemma hasFDerivAt_insertCoord2_fst {n : ℕ} (p : Fin n × Fin n) (v : E3)
    (x' : pairFib2 n p → E3) (u : E3) :
    HasFDerivAt (fun u' : E3 => insertCoord2 p u' v x') (slotInsCLM n p.1) u := by
  have h := hasFDerivAt_update (𝕜 := ℝ)
    (x := insertCoord2 p 0 v x') (i := p.1) (y := u)
  rw [show (ContinuousLinearMap.pi (Pi.single p.1 (ContinuousLinearMap.id ℝ E3)))
      = slotInsCLM n p.1 from rfl] at h
  rwa [← insertCoord2_update_fst_fun p v x'] at h

/-- The `fderiv` form of `hasFDerivAt_insertCoord2_fst`. -/
lemma fderiv_insertCoord2_fst {n : ℕ} (p : Fin n × Fin n) (v : E3)
    (x' : pairFib2 n p → E3) (u : E3) :
    fderiv ℝ (fun u' : E3 => insertCoord2 p u' v x') u = slotInsCLM n p.1 :=
  (hasFDerivAt_insertCoord2_fst p v x' u).fderiv

/-- **The chain rule for a function of the inserted configuration**: the `p.1`-slot derivative of
`u ↦ F (ins p u v x')` is the `p.1`-slot derivative of `F` at the inserted configuration. -/
lemma fderiv_comp_insertCoord2_fst {n : ℕ} (p : Fin n × Fin n) (v : E3)
    (x' : pairFib2 n p → E3) (u : E3) {F : Xn n → ℝ}
    (hF : DifferentiableAt ℝ F (insertCoord2 p u v x')) :
    fderiv ℝ (fun u' : E3 => F (insertCoord2 p u' v x')) u
      = (fderiv ℝ F (insertCoord2 p u v x')).comp (slotInsCLM n p.1) := by
  have h1 : HasFDerivAt (fun u' : E3 => insertCoord2 p u' v x') (slotInsCLM n p.1) u :=
    hasFDerivAt_insertCoord2_fst p v x' u
  have h := (hF.hasFDerivAt).comp u h1
  rw [show (fun u' : E3 => F (insertCoord2 p u' v x'))
      = (F ∘ fun u' : E3 => insertCoord2 p u' v x') from rfl, h.fderiv]

/-- **The chain rule at a basis vector**: the `j`-th `p.1`-slot derivative of `u ↦ F (ins p u v x')`
is `fderiv ℝ F (ins p u v x') (slotDirVec p.1 j)`. -/
lemma fderiv_comp_insertCoord2_fst_apply {n : ℕ} (p : Fin n × Fin n) (v : E3)
    (x' : pairFib2 n p → E3) (u : E3) {F : Xn n → ℝ}
    (hF : DifferentiableAt ℝ F (insertCoord2 p u v x')) (j : Fin 3) :
    fderiv ℝ (fun u' : E3 => F (insertCoord2 p u' v x')) u (EuclideanSpace.single j (1 : ℝ))
      = fderiv ℝ F (insertCoord2 p u v x') (slotDirVec p.1 j) := by
  rw [fderiv_comp_insertCoord2_fst p v x' u hF, ContinuousLinearMap.comp_apply,
    slotInsCLM_single]

/-! ## 3. Independence of the inserted `F₁` in the `p.1`-slot -/

/-- **Independence**: if `F` does not depend on the slot `p.1`, then the same is true after the
two-slot insertion. -/
lemma insertCoord2_indep_fst {n : ℕ} (p : Fin n × Fin n) {F : Xn n → ℝ}
    (hF : ∀ (x : Xn n) (t : E3), F (Function.update x p.1 t) = F x)
    (v : E3) (x' : pairFib2 n p → E3) (u u' : E3) :
    F (insertCoord2 p u v x') = F (insertCoord2 p u' v x') := by
  have h1 : F (insertCoord2 p u v x') = F (insertCoord2 p 0 v x') := by
    rw [insertCoord2_update_fst p v x' u]; exact hF (insertCoord2 p 0 v x') u
  have h2 : F (insertCoord2 p u' v x') = F (insertCoord2 p 0 v x') := by
    rw [insertCoord2_update_fst p v x' u']; exact hF (insertCoord2 p 0 v x') u'
  rw [h1, h2]

/-- The `u`-derivative of the inserted independent `F` vanishes. -/
lemma fderiv_insertCoord2_indep {n : ℕ} (p : Fin n × Fin n) {F : Xn n → ℝ}
    (hF : ∀ (x : Xn n) (t : E3), F (Function.update x p.1 t) = F x)
    (v : E3) (x' : pairFib2 n p → E3) (u : E3) :
    fderiv ℝ (fun u' : E3 => F (insertCoord2 p u' v x')) u = 0 := by
  have hconst : (fun u' : E3 => F (insertCoord2 p u' v x'))
      = Function.const E3 (F (insertCoord2 p u v x')) := by
    funext u'
    exact insertCoord2_indep_fst p hF v x' u' u
  rw [hconst]
  simp

/-! ## 4. The derivative of the parametrised integrand -/

/-- **The `u`-derivative of the integrand of the mirror fibre.**  With `F₁` independent of the slot
`p.1`, the integrand `u ↦ F₁ (ins p u s x') * G (ins p u v x')` has the derivative
`F₁ (ins p 0 s x') • ((fderiv ℝ G (ins p u v x')).comp (slotInsCLM p.1))`: the first factor is
constant in `u`. -/
lemma fderiv_prodImg2 {n : ℕ} (p : Fin n × Fin n) {F₁ G : Xn n → ℝ}
    (hF₁ind : ∀ (x : Xn n) (t : E3), F₁ (Function.update x p.1 t) = F₁ x)
    (hG : Differentiable ℝ G) (s v : E3) (x' : pairFib2 n p → E3) (u : E3) :
    fderiv ℝ (fun u' : E3 => F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x')) u
      = (F₁ (insertCoord2 p 0 s x')) •
          ((fderiv ℝ G (insertCoord2 p u v x')).comp (slotInsCLM n p.1)) := by
  have hconst : (fun u' : E3 => F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x'))
      = fun u' => F₁ (insertCoord2 p 0 s x') * G (insertCoord2 p u' v x') := by
    funext u'
    rw [insertCoord2_indep_fst p hF₁ind s x' u' 0]
  have hdiff : DifferentiableAt ℝ (fun u' : E3 => G (insertCoord2 p u' v x')) u :=
    ((hG (insertCoord2 p u v x')).hasFDerivAt.comp u
      (hasFDerivAt_insertCoord2_fst p v x' u)).differentiableAt
  rw [hconst, fderiv_const_mul hdiff]
  congr 1
  exact fderiv_comp_insertCoord2_fst p v x' u (hG (insertCoord2 p u v x'))

/-- The basis-vector form of `fderiv_prodImg2`. -/
lemma fderiv_prodImg2_apply {n : ℕ} (p : Fin n × Fin n) {F₁ G : Xn n → ℝ}
    (hF₁ind : ∀ (x : Xn n) (t : E3), F₁ (Function.update x p.1 t) = F₁ x)
    (hG : Differentiable ℝ G) (s v : E3) (x' : pairFib2 n p → E3) (u : E3) (j : Fin 3) :
    fderiv ℝ (fun u' : E3 => F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x')) u
        (EuclideanSpace.single j (1 : ℝ))
      = F₁ (insertCoord2 p 0 s x')
          * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j) := by
  rw [fderiv_prodImg2 p hF₁ind hG s v x' u]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    slotInsCLM_single]

/-! ## 5. The joint integrand of the fibre and its smoothness -/

/-- **The joint integrand of the mirror fibre**, as a function of the configuration parameters
`(u, v)`, the free fibre `x'` and the averaged slot `s`. -/
def img2Integrand {n : ℕ} (p : Fin n × Fin n) (F₁ G : Xn n → ℝ)
    (z : ((E3 × E3) × (pairFib2 n p → E3)) × E3) : ℝ :=
  F₁ (insertCoord2 p z.1.1.1 z.2 z.1.2) * G (insertCoord2 p z.1.1.1 z.1.1.2 z.1.2)

/-- The joint integrand is `C^∞`. -/
lemma contDiff_img2Integrand {n : ℕ} (p : Fin n × Fin n) {F₁ G : Xn n → ℝ}
    (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (img2Integrand p F₁ G) := by
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ((E3 × E3) × (pairFib2 n p → E3)) × E3 =>
        insertCoord2 p z.1.1.1 z.2 z.1.2) :=
    contDiff_insertCoord2_comp p (contDiff_fst.comp (contDiff_fst.comp contDiff_fst))
      contDiff_snd (contDiff_snd.comp contDiff_fst)
  have hB : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ((E3 × E3) × (pairFib2 n p → E3)) × E3 =>
        insertCoord2 p z.1.1.1 z.1.1.2 z.1.2) :=
    contDiff_insertCoord2_comp p (contDiff_fst.comp (contDiff_fst.comp contDiff_fst))
      (contDiff_snd.comp (contDiff_fst.comp contDiff_fst)) (contDiff_snd.comp contDiff_fst)
  exact (hF₁.comp hA).mul (hG.comp hB)

/-- The box of the free fibre coordinates is compact. -/
lemma isCompact_boxPi2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) :
    IsCompact (boxPiSet (pairFib2 n p) ℓ) :=
  isCompact_boxPiSet (ι := pairFib2 n p) hℓ

/-- The box of the averaged slot is compact. -/
lemma isCompact_boxL2 {ℓ : ℝ} (hℓ : 0 < ℓ) : IsCompact (boxL ℓ) := by
  rw [corpusBox_boxL_eq_acube hℓ]; exact Submission.BoseGases.acube_compact hℓ

/-- **The uncurried fibre is `C^1`**: the two nested parametric integrals over the compact boxes of
a jointly `C^∞` integrand. -/
theorem contDiff_one_imgFibre₂ {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (1 : ℕ∞) (Function.uncurry (imgFibre₂ ℓ p F₁ G)) := by
  have hK1 : IsCompact (boxL ℓ) := isCompact_boxL2 hℓ
  have hK2 : IsCompact (boxPiSet (pairFib2 n p) ℓ) := isCompact_boxPi2 hℓ p
  have hjoint : ContDiff ℝ (1 : ℕ∞) (img2Integrand p F₁ G) :=
    (contDiff_img2Integrand p hF₁ hG).of_le (by simp)
  have hinner : ContDiff ℝ (1 : ℕ∞) (fun r : (E3 × E3) × (pairFib2 n p → E3) =>
      ∫ s in boxL ℓ, img2Integrand p F₁ G (r, s)) :=
    contDiff_setIntegral_compact_aux (P := (E3 × E3) × (pairFib2 n p → E3))
      (G := E3) hK1 1 ℝ (fun r s => img2Integrand p F₁ G (r, s))
      (by
        rw [show (Function.uncurry fun r s => img2Integrand p F₁ G (r, s))
            = img2Integrand p F₁ G from rfl]
        exact hjoint)
  have houter : ContDiff ℝ (1 : ℕ∞) (fun q : E3 × E3 =>
      ∫ x' in boxPiSet (pairFib2 n p) ℓ,
        ∫ s in boxL ℓ, img2Integrand p F₁ G ((q, x'), s)) :=
    contDiff_setIntegral_compact_aux (P := E3 × E3) (G := pairFib2 n p → E3)
      hK2 1 ℝ
      (fun (q : E3 × E3) (x' : pairFib2 n p → E3) =>
        ∫ s in boxL ℓ, img2Integrand p F₁ G ((q, x'), s))
      (by
        rw [show (Function.uncurry fun (q : E3 × E3) (x' : pairFib2 n p → E3) =>
              ∫ s in boxL ℓ, img2Integrand p F₁ G ((q, x'), s))
            = (fun r : (E3 × E3) × (pairFib2 n p → E3) =>
                ∫ s in boxL ℓ, img2Integrand p F₁ G (r, s)) from rfl]
        exact hinner)
  have hfin : ContDiff ℝ (1 : ℕ∞) (fun q : E3 × E3 => (ℓ ^ 3)⁻¹ •
      (∫ x' in boxPiSet (pairFib2 n p) ℓ,
        ∫ s in boxL ℓ, img2Integrand p F₁ G ((q, x'), s))) :=
    ContDiff.const_smul ((ℓ ^ 3)⁻¹) houter
  rw [show (Function.uncurry (imgFibre₂ ℓ p F₁ G)) = (fun q : E3 × E3 => (ℓ ^ 3)⁻¹ •
      (∫ x' in boxPiSet (pairFib2 n p) ℓ,
        ∫ s in boxL ℓ, img2Integrand p F₁ G ((q, x'), s))) from by
    funext q
    rfl]
  exact hfin

/-- The fibre is continuous. -/
theorem continuous_imgFibre₂ {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    Continuous (Function.uncurry (imgFibre₂ ℓ p F₁ G)) :=
  (contDiff_one_imgFibre₂ hℓ p hF₁ hG).continuous

/-! ## 6. The derivative formula for the mirror fibre -/

/-- **The derivative formula for the mirror fibre in its first variable.**  At every `(u, v)`, the
`j`-th `p.1`-slot derivative of the fibre is `ℓ⁻³` times the double integral of the `F₁`-factor
(which is `u`-independent, hence evaluated at `0`) against the `p.1`-slot derivative of `G`. -/
theorem fderiv_imgFibre₂_fst_apply {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hF₁ind : ∀ (x : Xn n) (t : E3), F₁ (Function.update x p.1 t) = F₁ x)
    (v u : E3) (j : Fin 3) :
    fderiv ℝ (fun u' : E3 => imgFibre₂ ℓ p F₁ G u' v) u (EuclideanSpace.single j (1 : ℝ))
      = (ℓ ^ 3)⁻¹ * ∫ x' in boxPiSet (pairFib2 n p) ℓ,
          ∫ s in boxL ℓ, F₁ (insertCoord2 p 0 s x')
            * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j) := by
  classical
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hK1 : IsCompact (boxL ℓ) := isCompact_boxL2 hℓ
  have hK2 : IsCompact (boxPiSet (pairFib2 n p) ℓ) := isCompact_boxPi2 hℓ p
  -- the joint integrand with the second parameter frozen at `v`
  have hHj : ContDiff ℝ (1 : ℕ∞)
      (fun z : (E3 × (pairFib2 n p → E3)) × E3 =>
        F₁ (insertCoord2 p z.1.1 z.2 z.1.2) * G (insertCoord2 p z.1.1 v z.1.2)) := by
    have hA : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : (E3 × (pairFib2 n p → E3)) × E3 => insertCoord2 p z.1.1 z.2 z.1.2) :=
      contDiff_insertCoord2_comp p (contDiff_fst.comp contDiff_fst) contDiff_snd
        (contDiff_snd.comp contDiff_fst)
    have hB : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : (E3 × (pairFib2 n p → E3)) × E3 => insertCoord2 p z.1.1 v z.1.2) :=
      contDiff_insertCoord2_comp p (contDiff_fst.comp contDiff_fst) contDiff_const
        (contDiff_snd.comp contDiff_fst)
    exact ((hF₁.comp hA).mul (hG.comp hB)).of_le (by simp)
  -- the `(u, s)`-integrand at a fixed fibre `x'` is `C^1`
  have hxs : ∀ x' : pairFib2 n p → E3, ContDiff ℝ (1 : ℕ∞)
      (Function.uncurry (fun (u : E3) (s : E3) =>
        F₁ (insertCoord2 p u s x') * G (insertCoord2 p u v x'))) := by
    intro x'
    have hφ : ContDiff ℝ (1 : ℕ∞) (fun z : E3 × E3 => ((z.1, x'), z.2)) := by
      have h1 : ContDiff ℝ (1 : ℕ∞) (fun z : E3 × E3 => (z.1, x')) :=
        (contDiff_fst (𝕜 := ℝ) (n := (1 : ℕ∞)) (E := E3) (F := E3)).prodMk contDiff_const
      exact h1.prodMk (contDiff_snd (𝕜 := ℝ) (n := (1 : ℕ∞)) (E := E3) (F := E3))
    have h2 := hHj.comp hφ
    rw [show (Function.uncurry fun (u : E3) (s : E3) =>
          F₁ (insertCoord2 p u s x') * G (insertCoord2 p u v x'))
        = (fun z : E3 × E3 => F₁ (insertCoord2 p z.1 z.2 x') * G (insertCoord2 p z.1 v x'))
        from rfl]
    exact h2
  -- inner differentiation under the integral (variable `s`, parameters `(u, x')`)
  have hinner : ∀ x' : pairFib2 n p → E3,
      HasFDerivAt (fun u' : E3 => ∫ s in boxL ℓ,
          F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x'))
        (∫ s in boxL ℓ, fderiv ℝ (fun u' : E3 =>
          F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x')) u) u :=
    fun x' => hasFDerivAt_setIntegral_compact_gen hK1 (hxs x') u
  -- the family `(u, x') ↦ ∫_s ...` is `C^1`
  have hfamily : ContDiff ℝ (1 : ℕ∞) (fun q : E3 × (pairFib2 n p → E3) =>
      ∫ s in boxL ℓ, F₁ (insertCoord2 p q.1 s q.2) * G (insertCoord2 p q.1 v q.2)) := by
    refine contDiff_setIntegral_compact_aux (P := E3 × (pairFib2 n p → E3))
      (G := E3) hK1 1 ℝ
      (fun (q : E3 × (pairFib2 n p → E3)) (s : E3) =>
        F₁ (insertCoord2 p q.1 s q.2) * G (insertCoord2 p q.1 v q.2)) ?_
    rw [show (Function.uncurry fun (q : E3 × (pairFib2 n p → E3)) (s : E3) =>
          F₁ (insertCoord2 p q.1 s q.2) * G (insertCoord2 p q.1 v q.2))
        = (fun z : (E3 × (pairFib2 n p → E3)) × E3 =>
            F₁ (insertCoord2 p z.1.1 z.2 z.1.2) * G (insertCoord2 p z.1.1 v z.1.2)) from rfl]
    exact hHj
  -- outer differentiation under the integral (variable `x'`, parameter `u`)
  have houter : HasFDerivAt (fun u' : E3 => ∫ x' in boxPiSet (pairFib2 n p) ℓ,
        ∫ s in boxL ℓ, F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x'))
      (∫ x' in boxPiSet (pairFib2 n p) ℓ,
        fderiv ℝ (fun u' : E3 => ∫ s in boxL ℓ,
          F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x')) u) u := by
    refine hasFDerivAt_setIntegral_compact_gen hK2 ?_ u
    rw [show (Function.uncurry fun (u : E3) (x' : pairFib2 n p → E3) =>
          ∫ s in boxL ℓ, F₁ (insertCoord2 p u s x') * G (insertCoord2 p u v x'))
        = (fun q : E3 × (pairFib2 n p → E3) =>
            ∫ s in boxL ℓ, F₁ (insertCoord2 p q.1 s q.2) * G (insertCoord2 p q.1 v q.2))
        from rfl]
    exact hfamily
  -- continuity (and hence integrability on the compact boxes) of the CLM-valued integrands
  have hcontT : Continuous (fun x' : pairFib2 n p → E3 =>
      fderiv ℝ (fun u' : E3 => ∫ s in boxL ℓ,
        F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x')) u) := by
    have h := Commons.Analysis.Calculus.contDiff_uncurry_partialFDeriv (F := fun (u : E3)
        (x' : pairFib2 n p → E3) =>
        ∫ s in boxL ℓ, F₁ (insertCoord2 p u s x') * G (insertCoord2 p u v x'))
      (by
        rw [show (Function.uncurry fun (u : E3) (x' : pairFib2 n p → E3) =>
              ∫ s in boxL ℓ, F₁ (insertCoord2 p u s x') * G (insertCoord2 p u v x'))
            = (fun q : E3 × (pairFib2 n p → E3) =>
                ∫ s in boxL ℓ, F₁ (insertCoord2 p q.1 s q.2) * G (insertCoord2 p q.1 v q.2))
            from rfl]
        exact hfamily)
    exact h.continuous.comp (continuous_const.prodMk continuous_id)
  have hIntT : Integrable (fun x' : pairFib2 n p → E3 =>
      fderiv ℝ (fun u' : E3 => ∫ s in boxL ℓ,
        F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x')) u)
      ((volume : Measure (pairFib2 n p → E3)).restrict (boxPiSet (pairFib2 n p) ℓ)) :=
    hcontT.continuousOn.integrableOn_compact hK2
  have hfib : (fun u' : E3 => imgFibre₂ ℓ p F₁ G u' v)
      = fun u' : E3 => (ℓ ^ 3)⁻¹ * (∫ x' in boxPiSet (pairFib2 n p) ℓ,
          ∫ s in boxL ℓ, F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x')) := rfl
  rw [hfib, (houter.const_mul ((ℓ ^ 3)⁻¹)).fderiv]
  rw [smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.integral_apply hIntT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
  change (fderiv ℝ (fun u' : E3 => ∫ s in boxL ℓ,
      F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x')) u)
        (EuclideanSpace.single j (1 : ℝ))
      = (∫ s in boxL ℓ, F₁ (insertCoord2 p 0 s x')
          * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j))
  rw [(hinner x').fderiv]
  have hcontT' : Continuous (fun s : E3 => fderiv ℝ (fun u' : E3 =>
      F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x')) u) := by
    have h := Commons.Analysis.Calculus.contDiff_uncurry_partialFDeriv (F := fun (u : E3) (s : E3) =>
        F₁ (insertCoord2 p u s x') * G (insertCoord2 p u v x')) (hxs x')
    exact h.continuous.comp (continuous_const.prodMk continuous_id)
  have hIntT' : Integrable (fun s : E3 => fderiv ℝ (fun u' : E3 =>
      F₁ (insertCoord2 p u' s x') * G (insertCoord2 p u' v x')) u)
      ((volume : Measure E3).restrict (boxL ℓ)) :=
    hcontT'.continuousOn.integrableOn_compact hK1
  rw [ContinuousLinearMap.integral_apply hIntT']
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  exact fderiv_prodImg2_apply p hF₁ind hGd s v x' u j

end Work.BoseBoxFock
