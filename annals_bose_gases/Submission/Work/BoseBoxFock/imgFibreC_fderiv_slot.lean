import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.imgFibre2Aux
import Submission.Work.BoseBoxFock.imgFibreEnergyDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibreC_fderiv_slot`

The `p.1`-slot derivative of the position-space fibre `imgFibreC ℓ p F₁ G` of the `χχ`-images
words (`Submission/Work/BoseBoxFock/imagesFibre.lean`), i.e. the Leibniz rule for the double box
integral

    imgFibre ℓ p F₁ G u v = (ℓ³)⁻¹ ∫_{x'} ∫_{s ∈ boxL} F₁ (ins p s v x') · G (ins p u v x')

in its *first* (`u`-)variable: the `u`-dependence sits only in the `G`-factor (the `F₁`-factor
carries the dummy `s` in the slot `p.1` and the frozen `v` in the slot `p.2`), so the derivative is
the double integral of the `F₁`-factor against the `p.1`-slot derivative of `G`.

Both integration domains (`boxPiSet (pairFib23 n p) ℓ` and `boxL ℓ`) are compact and the integrand
is jointly `C^∞`, so differentiation under the integral sign is
`Work.BoseBoxFock.hasFDerivAt_setIntegral_compact_gen` (the general-space version of the corpus's
`Commons.Analysis.Calculus.hasFDerivAt_setIntegral_isCompact`), applied once for the `s`-integral
and once for the `x'`-integral.  The pointwise chain rule for the insertion is
`Work.BoseBoxFock.fderiv_comp_insertCoord2_fst`, and the linear insertion of a basis vector is
`Work.BoseBoxFock.slotInsCLM_single`; since the `F₁`-factor is `u`-free *by construction*, no
independence hypothesis is needed (contrast `Work.BoseBoxFock.fderiv_imgFibre₂_fst_apply`, where the
analogous statement carries `hF₁ind`).

The last step is the bookkeeping between the `ℝ`-valued integral of the Leibniz formula and the
`ℂ`-valued integral of the statement (`integral_ofReal` twice, then `Complex.ofReal_mul`).

Every declaration in this file is proved outright.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- The `u`-dependent double integral of the `imgFibre` fibre: the `s`-averaged `F₁`-factor paired
against the `u`-inserted `G`.  The fibre itself is `(ℓ³)⁻¹` times this (`imgFibre_eq_slotReal`). -/
noncomputable def imgFibreSlotReal {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    (F₁ G : Xn n → ℝ) (u v : E3) : ℝ :=
  ∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
    F₁ (insertCoord2 p s v x') * G (insertCoord2 p u v x')

/-- The fibre is `(ℓ³)⁻¹` times the `u`-dependent double integral. -/
lemma imgFibre_eq_slotReal {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (F₁ G : Xn n → ℝ) (u v : E3) :
    imgFibre ℓ p F₁ G u v = (ℓ ^ 3)⁻¹ * imgFibreSlotReal ℓ p F₁ G u v := rfl

/-- **The `slot`-derivative of the parametrised integrand.**  The factor `F₁ (ins p s v x')` does
not depend on `u'`, so the derivative of
`u' ↦ F₁ (ins p s v x') · G (ins p u' v x')` is `F₁ (ins p s v x')` times the `p.1`-slot derivative
of `G` at the inserted configuration. -/
lemma fderiv_prodImg_slot {n : ℕ} (p : Fin n × Fin n) {F₁ G : Xn n → ℝ}
    (hG : Differentiable ℝ G) (s v : E3) (x' : pairFib23 n p → E3) (u : E3) (j : Fin 3) :
    fderiv ℝ (fun u' : E3 => F₁ (insertCoord2 p s v x') * G (insertCoord2 p u' v x')) u
        (EuclideanSpace.single j (1 : ℝ))
      = F₁ (insertCoord2 p s v x')
          * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j) := by
  have hdiff : DifferentiableAt ℝ (fun u' : E3 => G (insertCoord2 p u' v x')) u :=
    ((hG (insertCoord2 p u v x')).hasFDerivAt.comp u
      (hasFDerivAt_insertCoord2_fst p v x' u)).differentiableAt
  rw [fderiv_const_mul hdiff]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_comp_insertCoord2_fst p v x' u (hG (insertCoord2 p u v x'))]
  simp only [ContinuousLinearMap.comp_apply, slotInsCLM_single]

/-- **The joint integrand of the `s`-integral is `C^∞`** (with the parameter `u`, the free fibre
coordinates `x'` and the averaged slot `s`). -/
lemma contDiff_slotIntegrand {n : ℕ} (p : Fin n × Fin n) {F₁ G : Xn n → ℝ}
    (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (v : E3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : (E3 × (pairFib23 n p → E3)) × E3 =>
      F₁ (insertCoord2 p z.2 v z.1.2) * G (insertCoord2 p z.1.1 v z.1.2)) := by
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (E3 × (pairFib23 n p → E3)) × E3 => insertCoord2 p z.2 v z.1.2) :=
    contDiff_insertCoord2_comp p contDiff_snd contDiff_const (contDiff_snd.comp contDiff_fst)
  have hB : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (E3 × (pairFib23 n p → E3)) × E3 => insertCoord2 p z.1.1 v z.1.2) :=
    contDiff_insertCoord2_comp p (contDiff_fst.comp contDiff_fst) contDiff_const
      (contDiff_snd.comp contDiff_fst)
  exact (hF₁.comp hA).mul (hG.comp hB)

/-- **The `s`-parametric integral is `C^1`**: the `s`-integral of the jointly smooth integrand,
over the compact box `boxL ℓ`, as a function of the parameter `(u, x')`. -/
lemma contDiff_slotFamily {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (v : E3) :
    ContDiff ℝ (1 : ℕ∞) (fun q : E3 × (pairFib23 n p → E3) =>
      ∫ s in boxL ℓ, F₁ (insertCoord2 p s v q.2) * G (insertCoord2 p q.1 v q.2)) := by
  have hK1 : IsCompact (boxL ℓ) := isCompact_boxL2 hℓ
  have hJ : ContDiff ℝ (1 : ℕ∞) (fun z : (E3 × (pairFib23 n p → E3)) × E3 =>
      F₁ (insertCoord2 p z.2 v z.1.2) * G (insertCoord2 p z.1.1 v z.1.2)) :=
    (contDiff_slotIntegrand p hF₁ hG v).of_le (by simp)
  refine contDiff_setIntegral_compact_aux (P := E3 × (pairFib23 n p → E3))
    (G := E3) hK1 1 ℝ
    (fun (q : E3 × (pairFib23 n p → E3)) (s : E3) =>
      F₁ (insertCoord2 p s v q.2) * G (insertCoord2 p q.1 v q.2)) ?_
  rw [show (Function.uncurry fun (q : E3 × (pairFib23 n p → E3)) (s : E3) =>
        F₁ (insertCoord2 p s v q.2) * G (insertCoord2 p q.1 v q.2))
      = (fun z : (E3 × (pairFib23 n p → E3)) × E3 =>
          F₁ (insertCoord2 p z.2 v z.1.2) * G (insertCoord2 p z.1.1 v z.1.2)) from rfl]
  exact hJ

/-- **Differentiation of the fibre's double integral in its first variable.**  The `u`-derivative of
`imgFibreSlotReal ℓ p F₁ G · v` is the `x'`-integral of the `u`-derivative of the inner
`s`-integral. -/
theorem hasFDerivAt_imgFibreSlotReal {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (v u : E3) :
    HasFDerivAt (fun u' : E3 => imgFibreSlotReal ℓ p F₁ G u' v)
      (∫ x' in boxPiSet (pairFib23 n p) ℓ,
        fderiv ℝ (fun u' : E3 => ∫ s in boxL ℓ,
          F₁ (insertCoord2 p s v x') * G (insertCoord2 p u' v x')) u) u := by
  have hK2 : IsCompact (boxPiSet (pairFib23 n p) ℓ) := isCompact_boxPiSet (ι := pairFib23 n p) hℓ
  rw [show (fun u' : E3 => imgFibreSlotReal ℓ p F₁ G u' v)
      = (fun u' : E3 => ∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
          F₁ (insertCoord2 p s v x') * G (insertCoord2 p u' v x')) from rfl]
  refine hasFDerivAt_setIntegral_compact_gen hK2 ?_ u
  rw [show (Function.uncurry fun (u : E3) (x' : pairFib23 n p → E3) =>
        ∫ s in boxL ℓ, F₁ (insertCoord2 p s v x') * G (insertCoord2 p u v x'))
      = (fun q : E3 × (pairFib23 n p → E3) =>
          ∫ s in boxL ℓ, F₁ (insertCoord2 p s v q.2) * G (insertCoord2 p q.1 v q.2)) from rfl]
  exact contDiff_slotFamily hℓ p hF₁ hG v

/-- **The applied form of the derivative of the fibre's double integral**: at the basis vector
`EuclideanSpace.single j 1` the derivative is the double integral of the `F₁`-factor against the
`p.1`-slot derivative of `G`. -/
theorem fderiv_imgFibreSlotReal_apply {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (v u : E3) (j : Fin 3) :
    fderiv ℝ (fun u' : E3 => imgFibreSlotReal ℓ p F₁ G u' v) u
        (EuclideanSpace.single j (1 : ℝ))
      = ∫ x' in boxPiSet (pairFib23 n p) ℓ,
          ∫ s in boxL ℓ, F₁ (insertCoord2 p s v x')
            * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j) := by
  classical
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hK1 : IsCompact (boxL ℓ) := isCompact_boxL2 hℓ
  have hK2 : IsCompact (boxPiSet (pairFib23 n p) ℓ) := isCompact_boxPiSet (ι := pairFib23 n p) hℓ
  have hxs : ∀ x' : pairFib23 n p → E3, ContDiff ℝ (1 : ℕ∞)
      (Function.uncurry (fun (u : E3) (s : E3) =>
        F₁ (insertCoord2 p s v x') * G (insertCoord2 p u v x'))) := by
    intro x'
    have hφ : ContDiff ℝ (1 : ℕ∞) (fun z : E3 × E3 => ((z.1, x'), z.2)) := by
      have h1 : ContDiff ℝ (1 : ℕ∞) (fun z : E3 × E3 => (z.1, x')) :=
        (contDiff_fst (𝕜 := ℝ) (n := (1 : ℕ∞)) (E := E3) (F := E3)).prodMk contDiff_const
      exact h1.prodMk (contDiff_snd (𝕜 := ℝ) (n := (1 : ℕ∞)) (E := E3) (F := E3))
    have h2 := (contDiff_slotIntegrand p hF₁ hG v).of_le (by simp) |>.comp hφ
    rw [show (Function.uncurry fun (u : E3) (s : E3) =>
          F₁ (insertCoord2 p s v x') * G (insertCoord2 p u v x'))
        = (fun z : E3 × E3 => F₁ (insertCoord2 p z.2 v x') * G (insertCoord2 p z.1 v x'))
        from rfl]
    exact h2
  have hinner : ∀ x' : pairFib23 n p → E3,
      HasFDerivAt (fun u' : E3 => ∫ s in boxL ℓ,
          F₁ (insertCoord2 p s v x') * G (insertCoord2 p u' v x'))
        (∫ s in boxL ℓ, fderiv ℝ (fun u' : E3 =>
          F₁ (insertCoord2 p s v x') * G (insertCoord2 p u' v x')) u) u :=
    fun x' => hasFDerivAt_setIntegral_compact_gen hK1 (hxs x') u
  have hcontT : Continuous (fun x' : pairFib23 n p → E3 =>
      fderiv ℝ (fun u' : E3 => ∫ s in boxL ℓ,
        F₁ (insertCoord2 p s v x') * G (insertCoord2 p u' v x')) u) := by
    have h := Commons.Analysis.Calculus.contDiff_uncurry_partialFDeriv (F := fun (u : E3)
        (x' : pairFib23 n p → E3) =>
        ∫ s in boxL ℓ, F₁ (insertCoord2 p s v x') * G (insertCoord2 p u v x'))
      (by
        rw [show (Function.uncurry fun (u : E3) (x' : pairFib23 n p → E3) =>
              ∫ s in boxL ℓ, F₁ (insertCoord2 p s v x') * G (insertCoord2 p u v x'))
            = (fun q : E3 × (pairFib23 n p → E3) =>
                ∫ s in boxL ℓ, F₁ (insertCoord2 p s v q.2) * G (insertCoord2 p q.1 v q.2))
            from rfl]
        exact contDiff_slotFamily hℓ p hF₁ hG v)
    exact h.continuous.comp (continuous_const.prodMk continuous_id)
  have hIntT : Integrable (fun x' : pairFib23 n p → E3 =>
      fderiv ℝ (fun u' : E3 => ∫ s in boxL ℓ,
        F₁ (insertCoord2 p s v x') * G (insertCoord2 p u' v x')) u)
      ((volume : Measure (pairFib23 n p → E3)).restrict (boxPiSet (pairFib23 n p) ℓ)) :=
    hcontT.continuousOn.integrableOn_compact hK2
  rw [(hasFDerivAt_imgFibreSlotReal hℓ p hF₁ hG v u).fderiv]
  rw [ContinuousLinearMap.integral_apply hIntT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
  change (fderiv ℝ (fun u' : E3 => ∫ s in boxL ℓ,
      F₁ (insertCoord2 p s v x') * G (insertCoord2 p u' v x')) u)
        (EuclideanSpace.single j (1 : ℝ))
      = (∫ s in boxL ℓ, F₁ (insertCoord2 p s v x')
          * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j))
  rw [(hinner x').fderiv]
  have hcontT' : Continuous (fun s : E3 => fderiv ℝ (fun u' : E3 =>
      F₁ (insertCoord2 p s v x') * G (insertCoord2 p u' v x')) u) := by
    have h := Commons.Analysis.Calculus.contDiff_uncurry_partialFDeriv
      (F := fun (u : E3) (s : E3) =>
        F₁ (insertCoord2 p s v x') * G (insertCoord2 p u v x')) (hxs x')
    exact h.continuous.comp (continuous_const.prodMk continuous_id)
  have hIntT' : Integrable (fun s : E3 => fderiv ℝ (fun u' : E3 =>
      F₁ (insertCoord2 p s v x') * G (insertCoord2 p u' v x')) u)
      ((volume : Measure E3).restrict (boxL ℓ)) :=
    hcontT'.continuousOn.integrableOn_compact hK1
  rw [ContinuousLinearMap.integral_apply hIntT']
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  exact fderiv_prodImg_slot p hGd s v x' u j

/-- **The `ℂ`-complexification of the double integral of the Leibniz formula.**  Both levels are
`integral_ofReal`; no integrability hypothesis is needed. -/
lemma imgFibreSlotReal_eq_cplx {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (F₁ G : Xn n → ℝ)
    (u v : E3) (j : Fin 3) :
    (((∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
        F₁ (insertCoord2 p s v x')
          * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) : ℝ) : ℂ)
      = ∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
          ((F₁ (insertCoord2 p s v x') : ℝ) : ℂ)
            * (((fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) : ℝ) : ℂ) := by
  have h2 : (((∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
        F₁ (insertCoord2 p s v x')
          * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) : ℝ) : ℂ)
      = ∫ x' in boxPiSet (pairFib23 n p) ℓ,
          (((∫ s in boxL ℓ, F₁ (insertCoord2 p s v x')
              * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) : ℝ) : ℂ) :=
    integral_ofReal.symm
  rw [h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
  change (((∫ s in boxL ℓ, F₁ (insertCoord2 p s v x')
        * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) : ℝ) : ℂ)
      = ∫ s in boxL ℓ, ((F₁ (insertCoord2 p s v x') : ℝ) : ℂ)
          * (((fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) : ℝ) : ℂ)
  have h1 : (∫ s in boxL ℓ, (((F₁ (insertCoord2 p s v x')
          * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) : ℝ) : ℂ))
      = (((∫ s in boxL ℓ, F₁ (insertCoord2 p s v x')
          * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) : ℝ) : ℂ) :=
    integral_ofReal
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  change (((F₁ (insertCoord2 p s v x')
      * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) : ℝ) : ℂ)
      = ((F₁ (insertCoord2 p s v x') : ℝ) : ℂ)
          * (((fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) : ℝ) : ℂ)
  simp only [Complex.ofReal_mul]

theorem imgFibreC_fderiv_slot {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {F₁ G : Submission.BoseGases.X n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (u v : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    fderiv ℝ (fun w' => Work.BoseBoxFock.imgFibreC ℓ p F₁ G w' v) u
        (EuclideanSpace.single j (1 : ℝ))
      = (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) *
          ∫ x' in Work.BoseBoxFock.boxPiSet (Work.BoseBoxFock.pairFib23 n p) ℓ,
            ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
              ((F₁ (Work.BoseBoxFock.insertCoord2 p s v x') : ℝ) : ℂ) *
                (((fderiv ℝ G (Work.BoseBoxFock.insertCoord2 p u v x')
                    (Work.BoseBoxFock.slotDirVec p.1 j)) : ℝ) : ℂ) := by
  classical
  have _ : p.1 ≠ p.2 := hp
  have hprod : HasFDerivAt (fun u' : E3 => imgFibre ℓ p F₁ G u' v)
      (((ℓ ^ 3)⁻¹) • (∫ x' in boxPiSet (pairFib23 n p) ℓ,
        fderiv ℝ (fun u' : E3 => ∫ s in boxL ℓ,
          F₁ (insertCoord2 p s v x') * G (insertCoord2 p u' v x')) u)) u := by
    rw [show (fun u' : E3 => imgFibre ℓ p F₁ G u' v)
        = (fun u' : E3 => (ℓ ^ 3)⁻¹ * imgFibreSlotReal ℓ p F₁ G u' v) from
      funext fun u' => imgFibre_eq_slotReal ℓ p F₁ G u' v]
    exact (hasFDerivAt_imgFibreSlotReal hℓ p hF₁ hG v u).const_mul ((ℓ ^ 3)⁻¹)
  have hcomp := (Complex.ofRealCLM.hasFDerivAt (x := imgFibre ℓ p F₁ G u v)).comp u hprod
  rw [show (fun w' : E3 => imgFibreC ℓ p F₁ G w' v)
      = Complex.ofRealCLM ∘ (fun u' : E3 => imgFibre ℓ p F₁ G u' v) from rfl,
    hcomp.fderiv]
  rw [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul]
  rw [← (hasFDerivAt_imgFibreSlotReal hℓ p hF₁ hG v u).fderiv,
    fderiv_imgFibreSlotReal_apply hℓ p hF₁ hG v u j]
  rw [show Complex.ofRealCLM (((ℓ ^ 3)⁻¹) * (∫ x' in boxPiSet (pairFib23 n p) ℓ,
        ∫ s in boxL ℓ, F₁ (insertCoord2 p s v x')
          * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)))
      = ((((ℓ ^ 3)⁻¹) * (∫ x' in boxPiSet (pairFib23 n p) ℓ,
        ∫ s in boxL ℓ, F₁ (insertCoord2 p s v x')
          * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) : ℝ) : ℂ) from rfl]
  rw [Complex.ofReal_mul, imgFibreSlotReal_eq_cplx]

end Work.BoseBoxFock
