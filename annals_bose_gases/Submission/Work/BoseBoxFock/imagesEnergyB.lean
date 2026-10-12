import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.imgFibre2_dchi_integral
import Submission.Work.BoseBoxFock.imgFibre2_deriv_sq_le
import Submission.Work.BoseBoxFock.imgFibre2_mf_integral
import Submission.Work.BoseBoxFock.imgFibre2_sq_le
import Submission.Work.BoseBoxFock.integralBoundsChiParam
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imagesEnergyB` — a cone-local copy of the mirror fibre-energy bound

Verbatim copy of `Submission/Work/BoseBoxFock/imgFibre2EnergyLe.lean` in which the local helper
`setIntegral_boxL_const` has been renamed to `setIntegral_boxL_constBE`.

**Why.**  The proved sibling `Work.BoseBoxFock.pairGc13_core` (in the import cone of
`Work.BoseBoxFock.imgFibreEnergyLe`) also declares `Work.BoseBoxFock.setIntegral_boxL_const`, so
the two modules cannot coexist in one import cone.  The assembly `imagesWordLe` needs both energy
bounds; this copy provides the mirror one under a cone-local renamed helper.
# (original title) — the energy bound for the mirror fibre `imgFibre₂`

This module proves the bound

    pairEnergy ℓ (imgFibre₂C ℓ p F₁ G)
      ≤ max (2·Kg + ℓ⁻²·Kc) 2 · (N(F₁)·(N(G) + Dχ(G)) / ℓ⁶)

for the *mirror* position-space fibre `imgFibre₂ ℓ p F₁ G` of `imagesFibre.lean`, under the
hypotheses that `F₁` is independent of the slot `p.1` (`hF₁ind`) and that the window data
`Kg ⊇ Σ_j‖∂_jχ_ℓ‖²`, `Kc ⊇ ‖χ_ℓ‖²` are given.

## Structure

* `imgFibre2B`, `imgFibre2Q` — the two `p.2`-frozen Cauchy–Schwarz densities of `G`;
* the glue lemmas: continuity of the densities, the `s`-dummy collapse `∫_s = ℓ³·(·)`, the
  complexification transfers (`‖·‖²` and `fderiv` of `imgFibre₂C` versus `imgFibre₂`), the
  constancy of the `F₁`-slice `imgFibreMG ℓ p F₁ u` under `hF₁ind`, and the box-integral identity
  `imgFibre2_Bint` for the value density (via the peel `setIntegral_insertCoord2_slice`);
* `imgFibre2EnergyLe_of_inputs` — the assembly, given the two pointwise Cauchy–Schwarz rows and
  the box-integral identities as hypotheses;
* `imgFibre2EnergyLe` — the target, obtained from the four inputs `imgFibre2_sq_le`,
  `imgFibre2_deriv_sq_le`, `imgFibre2_mf_integral`, `imgFibre2_dchi_integral`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-! ## 1. The two Cauchy–Schwarz densities of `G` -/

/-- The `L²`-content of `G` over the *free* fibre box at the inserted configuration
`insertCoord2 p u v x'` (the second factor of the value row of the Cauchy–Schwarz bound). -/
noncomputable def imgFibre2B {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (G : Xn n → ℝ)
    (u v : E3) : ℝ :=
  ∫ x' in boxPiSet (pairFib2 n p) ℓ, (G (insertCoord2 p u v x')) ^ 2

/-- The `p.1`-slot derivative content of `G` over the free fibre box at the inserted configuration
`insertCoord2 p u v x'` (the second factor of the Dirichlet row). -/
noncomputable def imgFibre2Q {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (G : Xn n → ℝ)
    (u v : E3) : ℝ :=
  ∫ x' in boxPiSet (pairFib2 n p) ℓ,
    ∑ j : Fin 3, (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2

lemma imgFibre2B_nonneg {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (G : Xn n → ℝ) (u v : E3) :
    0 ≤ imgFibre2B ℓ p G u v :=
  integral_nonneg fun _ => sq_nonneg _

lemma imgFibre2Q_nonneg {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (G : Xn n → ℝ) (u v : E3) :
    0 ≤ imgFibre2Q ℓ p G u v :=
  integral_nonneg fun _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-! ## 2. The `s`-dummy collapse -/

/-- The integral of a constant over the box is `ℓ³` times the constant. -/
lemma setIntegral_boxL_constBE {ℓ c : ℝ} (hℓ : 0 < ℓ) : (∫ _s in boxL ℓ, c) = ℓ ^ 3 * c := by
  rw [MeasureTheory.setIntegral_const, measureReal_def,
    Work.BoseB4.BoxData.volume_boxL_toReal Work.BoseK15.corpusBox hℓ, smul_eq_mul]

/-- The inner `s`-integral of the value row: the integrand does not depend on `s`. -/
lemma imgFibre2B_sIntegral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (G : Xn n → ℝ)
    (u v : E3) :
    (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ, (G (insertCoord2 p u v x')) ^ 2)
      = ℓ ^ 3 * imgFibre2B ℓ p G u v := by
  have hfun : (fun x' : pairFib2 n p → E3 => ∫ s in boxL ℓ, (G (insertCoord2 p u v x')) ^ 2)
      = fun x' => ℓ ^ 3 * (G (insertCoord2 p u v x')) ^ 2 := by
    funext x'
    rw [setIntegral_boxL_constBE hℓ]
  rw [hfun, MeasureTheory.integral_const_mul, imgFibre2B]

/-- The inner `s`-integral of the Dirichlet row: the integrand does not depend on `s`. -/
lemma imgFibre2Q_sIntegral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (G : Xn n → ℝ)
    (u v : E3) :
    (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
        ∑ j : Fin 3, (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2)
      = ℓ ^ 3 * imgFibre2Q ℓ p G u v := by
  have hfun : (fun x' : pairFib2 n p → E3 => ∫ s in boxL ℓ,
        ∑ j : Fin 3, (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2)
      = fun x' => ℓ ^ 3 * (∑ j : Fin 3,
          (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2) := by
    funext x'
    rw [setIntegral_boxL_constBE hℓ]
  rw [hfun, MeasureTheory.integral_const_mul, imgFibre2Q]

/-! ## 3. Continuity of the two densities -/

lemma continuous_imgFibre2B {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {G : Xn n → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    Continuous (fun z : E3 × E3 => imgFibre2B ℓ p G z.1 z.2) := by
  have hK : IsCompact (boxPiSet (pairFib2 n p) ℓ) := isCompact_boxPiSet (ι := pairFib2 n p) hℓ
  have hins : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E3 × E3) × (pairFib2 n p → E3) =>
      insertCoord2 p w.1.1 w.1.2 w.2) :=
    contDiff_insertCoord2_comp p (contDiff_fst.comp contDiff_fst)
      (contDiff_snd.comp contDiff_fst) contDiff_snd
  have hjoint : Continuous (fun w : (E3 × E3) × (pairFib2 n p → E3) =>
      (G (insertCoord2 p w.1.1 w.1.2 w.2)) ^ 2) :=
    (hG.continuous.comp hins.continuous).pow 2
  rw [continuous_iff_continuousAt]
  intro q₀
  exact continuousAt_setIntegral_compact_gen hK hjoint q₀

lemma continuous_imgFibre2Q {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {G : Xn n → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    Continuous (fun z : E3 × E3 => imgFibre2Q ℓ p G z.1 z.2) := by
  have hK : IsCompact (boxPiSet (pairFib2 n p) ℓ) := isCompact_boxPiSet (ι := pairFib2 n p) hℓ
  have hins : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E3 × E3) × (pairFib2 n p → E3) =>
      insertCoord2 p w.1.1 w.1.2 w.2) :=
    contDiff_insertCoord2_comp p (contDiff_fst.comp contDiff_fst)
      (contDiff_snd.comp contDiff_fst) contDiff_snd
  have hd : Continuous (fun w : (E3 × E3) × (pairFib2 n p → E3) =>
      fderiv ℝ G (insertCoord2 p w.1.1 w.1.2 w.2)) :=
    (hG.continuous_fderiv (by simp)).comp hins.continuous
  have hjoint : Continuous (fun w : (E3 × E3) × (pairFib2 n p → E3) =>
      ∑ j : Fin 3, (fderiv ℝ G (insertCoord2 p w.1.1 w.1.2 w.2)
        (slotDirVec p.1 j)) ^ 2) :=
    continuous_finsetSum _ fun j _ => (hd.clm_apply continuous_const).pow 2
  rw [continuous_iff_continuousAt]
  intro q₀
  exact continuousAt_setIntegral_compact_gen hK hjoint q₀

/-! ## 4. Complexification transfers -/

/-- The derivative of the complexification of a real function. -/
lemma ofReal_fderiv' {f : E3 → ℝ} {x : E3} (hf : DifferentiableAt ℝ f x) (v : E3) :
    fderiv ℝ (fun y => ((f y : ℝ) : ℂ)) x v = ((fderiv ℝ f x v : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun y : E3 => ((f y : ℝ) : ℂ))
      ((Complex.ofRealCLM).comp (fderiv ℝ f x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt
  rw [h1.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

/-- The squared norm of the complexified fibre value. -/
lemma normSq_imgFibre₂C {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (F₁ G : Xn n → ℝ) (u v : E3) :
    ‖imgFibre₂C ℓ p F₁ G u v‖ ^ 2 = (imgFibre₂ ℓ p F₁ G u v) ^ 2 := by
  have h : imgFibre₂C ℓ p F₁ G u v = ((imgFibre₂ ℓ p F₁ G u v : ℝ) : ℂ) := rfl
  rw [h, Complex.sq_norm, Complex.normSq_ofReal]
  ring

/-- The `fderiv` of the complexified fibre in its first variable. -/
lemma fderiv_imgFibre₂C_fst {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n} {F₁ G : Xn n → ℝ}
    {v : E3} {w : E3} (h : DifferentiableAt ℝ (fun w' => imgFibre₂ ℓ p F₁ G w' v) w) :
    fderiv ℝ (fun w' => imgFibre₂C ℓ p F₁ G w' v) w
      = (Complex.ofRealCLM).comp (fderiv ℝ (fun w' => imgFibre₂ ℓ p F₁ G w' v) w) := by
  have h1 : (fun w' : E3 => imgFibre₂C ℓ p F₁ G w' v)
      = (fun y : ℝ => (y : ℂ)) ∘ (fun w' : E3 => imgFibre₂ ℓ p F₁ G w' v) := rfl
  rw [h1]
  exact (Complex.ofRealCLM.hasFDerivAt.comp w h.hasFDerivAt).fderiv

/-- The norm of the `fderiv` of the complexified fibre in its first variable. -/
lemma norm_fderiv_imgFibre₂C_fst {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n} {F₁ G : Xn n → ℝ}
    {v : E3} {w : E3} (h : DifferentiableAt ℝ (fun w' => imgFibre₂ ℓ p F₁ G w' v) w) (a : E3) :
    ‖(fderiv ℝ (fun w' => imgFibre₂C ℓ p F₁ G w' v) w) a‖
      = ‖(fderiv ℝ (fun w' => imgFibre₂ ℓ p F₁ G w' v) w) a‖ := by
  rw [fderiv_imgFibre₂C_fst h, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  exact RCLike.norm_ofReal _

/-- The real fibre is differentiable in its first variable. -/
lemma differentiableAt_imgFibre₂_fst {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (v w : E3) : DifferentiableAt ℝ (fun w' => imgFibre₂ ℓ p F₁ G w' v) w := by
  have hd : Differentiable ℝ (Function.uncurry (imgFibre₂ ℓ p F₁ G)) :=
    (contDiff_one_imgFibre₂ hℓ p hF₁ hG).differentiable (by simp)
  have h1 : HasFDerivAt (fun w' : E3 => (w', v)) (ContinuousLinearMap.inl ℝ E3 E3) w :=
    hasFDerivAt_prodMk_left w v
  exact ((hd (w, v)).hasFDerivAt.comp w h1).differentiableAt

/-- The complexified fibre is differentiable in its first variable. -/
lemma differentiableAt_imgFibre₂C_fst {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (z : E3 × E3) : DifferentiableAt ℝ (fun w' => imgFibre₂C ℓ p F₁ G w' z.2) z.1 := by
  have h2 : DifferentiableAt ℝ (fun w' => imgFibre₂ ℓ p F₁ G w' z.2) z.1 :=
    differentiableAt_imgFibre₂_fst hℓ p hF₁ hG z.2 z.1
  have h3 : DifferentiableAt ℝ (fun y : ℝ => (y : ℂ)) (imgFibre₂ ℓ p F₁ G z.1 z.2) :=
    Complex.ofRealCLM.differentiableAt
  exact h3.comp z.1 h2

/-- The complexified fibre is continuous. -/
lemma continuous_uncurry_imgFibre₂C {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    Continuous (Function.uncurry (imgFibre₂C ℓ p F₁ G)) := by
  have h : Function.uncurry (imgFibre₂C ℓ p F₁ G)
      = (fun y : ℝ => (y : ℂ)) ∘ Function.uncurry (imgFibre₂ ℓ p F₁ G) := rfl
  rw [h]
  exact Complex.ofRealCLM.continuous.comp (continuous_imgFibre₂ hℓ p hF₁ hG)

/-! ## 5. The window data in the `chiS` spelling -/

lemma chiS_hKg {ℓ Kg : ℝ} (hℓ : 0 < ℓ)
    (hKg : ∀ w : E3, ∑ j : Fin 3,
      ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ Kg) :
    ∀ w : E3, ∑ j : Fin 3,
      ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg := by
  intro w
  have h2 : ∀ j : Fin 3,
      ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖
        = ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) w
            (EuclideanSpace.single j (1 : ℝ))‖ := by
    intro j
    rw [show chiS ℓ = fun y => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ) from
      funext (chiS_eq ℓ)]
    rw [ofReal_fderiv' ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).differentiable
      (by simp) w) (EuclideanSpace.single j (1 : ℝ))]
    exact RCLike.norm_ofReal _
  calc ∑ j : Fin 3, ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      = ∑ j : Fin 3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) w
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [h2 j]
    _ ≤ Kg := hKg w

lemma chiS_hKc {ℓ Kc : ℝ}
    (hKc : ∀ w : E3, (Submission.BoseGases.chiScale ℓ w) ^ 2 ≤ Kc) :
    ∀ w : E3, ‖chiS ℓ w‖ ^ 2 ≤ Kc := by
  intro w
  rw [chiS_sq]
  exact hKc w

/-! ## 6. The constancy of the `F₁`-slice -/

lemma imgFibreMG_const {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) {F₁ : Xn n → ℝ}
    (hF₁ind : ∀ (x : Xn n) (t : E3), F₁ (Function.update x p.1 t) = F₁ x) (u : E3) :
    imgFibreMG ℓ p F₁ u = imgFibreMG ℓ p F₁ 0 := by
  rw [imgFibreMG, imgFibreMG]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [insertCoord2_indep_fst p hF₁ind s x' u 0]

/-! ## 7. The box integral of the value density (the peel identity) -/

theorem imgFibre2_Bint {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {G : Xn n → ℝ} (hG : Continuous G) :
    (∫ z in boxL ℓ ×ˢ boxL ℓ, imgFibre2B ℓ p G z.1 z.2) = imgFibreN ℓ G := by
  have hcont : Continuous (fun z : E3 × E3 => imgFibre2B ℓ p G z.1 z.2) := by
    have hK : IsCompact (boxPiSet (pairFib2 n p) ℓ) :=
      isCompact_boxPiSet (ι := pairFib2 n p) hℓ
    have hins : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E3 × E3) × (pairFib2 n p → E3) =>
        insertCoord2 p w.1.1 w.1.2 w.2) :=
      contDiff_insertCoord2_comp p (contDiff_fst.comp contDiff_fst)
        (contDiff_snd.comp contDiff_fst) contDiff_snd
    have hjoint : Continuous (fun w : (E3 × E3) × (pairFib2 n p → E3) =>
        (G (insertCoord2 p w.1.1 w.1.2 w.2)) ^ 2) :=
      (hG.comp hins.continuous).pow 2
    rw [continuous_iff_continuousAt]
    intro q₀
    exact continuousAt_setIntegral_compact_gen hK hjoint q₀
  have hKbox : IsCompact (boxL ℓ ×ˢ boxL ℓ) :=
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have hIntOn : IntegrableOn (fun z : E3 × E3 => imgFibre2B ℓ p G z.1 z.2)
      (boxL ℓ ×ˢ boxL ℓ) :=
    hcont.continuousOn.integrableOn_compact hKbox
  have hInt : Integrable (fun z : E3 × E3 => imgFibre2B ℓ p G z.1 z.2)
      (((volume : Measure E3).prod (volume : Measure E3)).restrict (boxL ℓ ×ˢ boxL ℓ)) := by
    rw [← MeasureTheory.Measure.volume_eq_prod]
    exact hIntOn
  have hprod : (∫ z in boxL ℓ ×ˢ boxL ℓ, imgFibre2B ℓ p G z.1 z.2)
      = ∫ u in boxL ℓ, ∫ v in boxL ℓ, imgFibre2B ℓ p G u v := by
    show (∫ z in boxL ℓ ×ˢ boxL ℓ, imgFibre2B ℓ p G z.1 z.2
      ∂((volume : Measure E3).prod (volume : Measure E3))) = _
    exact MeasureTheory.setIntegral_prod _ hInt
  rw [hprod]
  change (∫ u in boxL ℓ, ∫ v in boxL ℓ,
      ∫ x' in boxPiSet (pairFib2 n p) ℓ, (G (insertCoord2 p u v x')) ^ 2) = imgFibreN ℓ G
  exact setIntegral_insertCoord2_slice hℓ p hp (hG.pow 2)

/-! ## 8. The assembly -/

/-- **The fibre-energy bound from the two pointwise Cauchy–Schwarz rows and the box-integral
identities.** -/
theorem imgFibre2EnergyLe_of_inputs {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    {Kg Kc A0 : ℝ} (hKg0 : 0 ≤ Kg) (hKc0 : 0 ≤ Kc) (hA00 : 0 ≤ A0)
    (hKg : ∀ w : E3, ∑ j : Fin 3,
      ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg)
    (hKc : ∀ w : E3, (Submission.BoseGases.chiScale ℓ w) ^ 2 ≤ Kc)
    (hA0N : ℓ ^ 3 * A0 = imgFibreN ℓ F₁)
    (hval : ∀ u v : E3, (imgFibre₂ ℓ p F₁ G u v) ^ 2
      ≤ (ℓ ^ 3)⁻¹ * A0 * imgFibre2B ℓ p G u v)
    (hdb : ∀ u v : E3, ∑ j : Fin 3,
      (fderiv ℝ (fun u' => imgFibre₂ ℓ p F₁ G u' v) u (EuclideanSpace.single j (1 : ℝ))) ^ 2
        ≤ (ℓ ^ 3)⁻¹ * A0 * imgFibre2Q ℓ p G u v)
    (hBint : (∫ z in boxL ℓ ×ˢ boxL ℓ, imgFibre2B ℓ p G z.1 z.2) = imgFibreN ℓ G)
    (hQint : (∫ z in boxL ℓ ×ˢ boxL ℓ,
        (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * imgFibre2Q ℓ p G z.1 z.2)
      = imgFibreDχ ℓ p G) :
    L1Tails.pairEnergy ℓ (imgFibre₂C ℓ p F₁ G)
      ≤ max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2
        * (imgFibreN ℓ F₁ * (imgFibreN ℓ G + imgFibreDχ ℓ p G) / ℓ ^ 6) := by
  have hℓ3 : (0 : ℝ) < ℓ ^ 3 := by positivity
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hinv3 : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
  set P : E3 × E3 → ℝ := fun z => (ℓ ^ 3)⁻¹ * A0 * imgFibre2B ℓ p G z.1 z.2 with hPdef
  set Q : E3 × E3 → ℝ := fun z => (ℓ ^ 3)⁻¹ * A0 * imgFibre2Q ℓ p G z.1 z.2 with hQdef
  have hP0 : ∀ z, 0 ≤ P z := fun z => by
    rw [hPdef]
    exact mul_nonneg (mul_nonneg hinv3 hA00) (imgFibre2B_nonneg ℓ p G z.1 z.2)
  have hQ0 : ∀ z, 0 ≤ Q z := fun z => by
    rw [hQdef]
    exact mul_nonneg (mul_nonneg hinv3 hA00) (imgFibre2Q_nonneg ℓ p G z.1 z.2)
  have hcontB : Continuous (fun z : E3 × E3 => imgFibre2B ℓ p G z.1 z.2) :=
    continuous_imgFibre2B hℓ p hG
  have hcontQ : Continuous (fun z : E3 × E3 => imgFibre2Q ℓ p G z.1 z.2) :=
    continuous_imgFibre2Q hℓ p hG
  have hPcont : Continuous P := by
    rw [hPdef]; exact (continuous_const.mul continuous_const).mul hcontB
  have hQcont : Continuous Q := by
    rw [hQdef]; exact (continuous_const.mul continuous_const).mul hcontQ
  have hKbox : IsCompact (boxL ℓ ×ˢ boxL ℓ) :=
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have hPint : IntegrableOn P (boxL ℓ ×ˢ boxL ℓ) :=
    hPcont.continuousOn.integrableOn_compact hKbox
  have hWQcont : Continuous (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2 * Q z) :=
    (((continuous_chiS ℓ).comp continuous_fst).norm.pow 2).mul hQcont
  have hWQint : IntegrableOn (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2 * Q z)
      (boxL ℓ ×ˢ boxL ℓ) :=
    hWQcont.continuousOn.integrableOn_compact hKbox
  have hval' : ∀ z : E3 × E3, ‖imgFibre₂C ℓ p F₁ G z.1 z.2‖ ^ 2 ≤ P z := fun z => by
    rw [normSq_imgFibre₂C, hPdef]
    exact hval z.1 z.2
  have hdb' : ∀ z : E3 × E3, ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => imgFibre₂C ℓ p F₁ G w' z.2) z.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Q z := by
    intro z
    have hd : DifferentiableAt ℝ (fun w' => imgFibre₂ ℓ p F₁ G w' z.2) z.1 :=
      differentiableAt_imgFibre₂_fst hℓ p hF₁ hG z.2 z.1
    calc ∑ j : Fin 3, ‖fderiv ℝ (fun w' => imgFibre₂C ℓ p F₁ G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        = ∑ j : Fin 3, ‖fderiv ℝ (fun w' => imgFibre₂ ℓ p F₁ G w' z.2) z.1
            (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [norm_fderiv_imgFibre₂C_fst hd]
      _ = ∑ j : Fin 3, (fderiv ℝ (fun w' => imgFibre₂ ℓ p F₁ G w' z.2) z.1
            (EuclideanSpace.single j (1 : ℝ))) ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
      _ ≤ (ℓ ^ 3)⁻¹ * A0 * imgFibre2Q ℓ p G z.1 z.2 := hdb z.1 z.2
      _ = Q z := by rw [hQdef]
  have hPintEq : (∫ z in boxL ℓ ×ˢ boxL ℓ, P z)
      = (ℓ ^ 3)⁻¹ * A0 * (∫ z in boxL ℓ ×ˢ boxL ℓ, imgFibre2B ℓ p G z.1 z.2) := by
    rw [hPdef]
    exact MeasureTheory.integral_const_mul ((ℓ ^ 3)⁻¹ * A0) _
  have hWQintEq : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * Q z)
      = (ℓ ^ 3)⁻¹ * A0
        * (∫ z in boxL ℓ ×ˢ boxL ℓ,
            (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * imgFibre2Q ℓ p G z.1 z.2) := by
    have hpt : ∀ z : E3 × E3, ‖chiS ℓ z.1‖ ^ 2 * Q z
        = (ℓ ^ 3)⁻¹ * A0
          * ((Submission.BoseGases.chiScale ℓ z.1) ^ 2 * imgFibre2Q ℓ p G z.1 z.2) := by
      intro z
      rw [chiS_sq, hQdef]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_const_mul]
  have hA0 : 0 ≤ imgFibreN ℓ F₁ * imgFibreN ℓ G / ℓ ^ 6 :=
    div_nonneg (mul_nonneg (imgFibreN_nonneg ℓ F₁) (imgFibreN_nonneg ℓ G)) (by positivity)
  have hB0 : 0 ≤ imgFibreN ℓ F₁ * imgFibreDχ ℓ p G / ℓ ^ 6 :=
    div_nonneg (mul_nonneg (imgFibreN_nonneg ℓ F₁) (imgFibreDχ_nonneg ℓ p G)) (by positivity)
  have hPleA : (∫ z in boxL ℓ ×ˢ boxL ℓ, P z) ≤ imgFibreN ℓ F₁ * imgFibreN ℓ G / ℓ ^ 6 := by
    rw [hPintEq, hBint, ← hA0N, div_eq_mul_inv]
    field_simp
    exact le_refl _
  have hWQleB : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * Q z)
      ≤ imgFibreN ℓ F₁ * imgFibreDχ ℓ p G / ℓ ^ 6 := by
    rw [hWQintEq, hQint, ← hA0N, div_eq_mul_inv]
    field_simp
    exact le_refl _
  have hmain := pairEnergy_le_of_integral_bounds_chi_param (ℓ := ℓ) (Kg := Kg) (Kc := Kc)
    hℓ hKg0 hKc0 (chiS_hKg hℓ hKg) (chiS_hKc hKc)
    hA0 hB0 hP0 hQ0 hval' hdb' (fun z => differentiableAt_imgFibre₂C_fst hℓ p hF₁ hG z)
    (continuous_uncurry_imgFibre₂C hℓ p hF₁ hG) hPint hWQint hPleA hWQleB
  calc L1Tails.pairEnergy ℓ (imgFibre₂C ℓ p F₁ G)
      ≤ max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2
          * (imgFibreN ℓ F₁ * imgFibreN ℓ G / ℓ ^ 6
            + imgFibreN ℓ F₁ * imgFibreDχ ℓ p G / ℓ ^ 6) := hmain
    _ = max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2
          * (imgFibreN ℓ F₁ * (imgFibreN ℓ G + imgFibreDχ ℓ p G) / ℓ ^ 6) := by ring

/-! ## 9. The four inputs of the assembly -/

/-- `imgFibreMG` is the iterated double integral of the squared inserted state. -/
lemma imgFibreMG_unfold {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (F : Xn n → ℝ) (u : E3) :
    imgFibreMG ℓ p F u
      = ∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
          (F (insertCoord2 p u s x')) ^ 2 := rfl

/-- `imgFibre2Q` is the box integral of the summed squared slot derivatives. -/
lemma imgFibre2Q_unfold {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (G : Xn n → ℝ) (u v : E3) :
    imgFibre2Q ℓ p G u v
      = ∫ x' in boxPiSet (pairFib2 n p) ℓ,
          ∑ j : Fin 3, (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2 := rfl

/-- A continuous function on `E3 × E3` is integrable against the product measure restricted to
the square of the box. -/
lemma integrable_prod_restrict_of_continuous {ℓ : ℝ} {f : E3 × E3 → ℝ} (hf : Continuous f) :
    Integrable f (((volume : Measure E3).prod (volume : Measure E3)).restrict
      (boxL ℓ ×ˢ boxL ℓ)) := by
  have hKbox : IsCompact (boxL ℓ ×ˢ boxL ℓ) :=
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have h : IntegrableOn f (boxL ℓ ×ˢ boxL ℓ) := hf.continuousOn.integrableOn_compact hKbox
  rwa [MeasureTheory.Measure.volume_eq_prod] at h

/-- The `s`-integral of a single slot derivative collapses to `ℓ³` times the `x'`-integral. -/
lemma imgFibre2Qj_sIntegral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (G : Xn n → ℝ)
    (u v : E3) (j : Fin 3) :
    (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
        (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2)
      = ℓ ^ 3 * (∫ x' in boxPiSet (pairFib2 n p) ℓ,
          (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2) := by
  have hfun : (fun x' : pairFib2 n p → E3 => ∫ s in boxL ℓ,
        (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2)
      = fun x' => ℓ ^ 3 * (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2 := by
    funext x'
    rw [setIntegral_boxL_constBE hℓ]
  rw [hfun, MeasureTheory.integral_const_mul]

/-- The sum over the three directions of the single-direction `s`-integrals is `ℓ³` times
`imgFibre2Q`. -/
lemma imgFibre2Qj_sum {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {G : Xn n → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (u v : E3) :
    (∑ j : Fin 3, ∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
        (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2)
      = ℓ ^ 3 * imgFibre2Q ℓ p G u v := by
  rw [Finset.sum_congr rfl (fun j _ => imgFibre2Qj_sIntegral hℓ p G u v j),
    ← Finset.mul_sum, imgFibre2Q_unfold]
  congr 1
  exact (MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin 3))
    (μ := (volume : Measure (pairFib2 n p → E3)).restrict (boxPiSet (pairFib2 n p) ℓ))
    (f := fun j (x' : pairFib2 n p → E3) =>
      (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2)
    (fun j _ => (by
      have hc : Continuous (fun x' : pairFib2 n p → E3 =>
          (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2) :=
        (((hG.continuous_fderiv (by simp)).comp
          (contDiff_insertCoord2_comp p contDiff_const contDiff_const contDiff_id).continuous
            ).clm_apply continuous_const).pow 2
      exact hc.continuousOn.integrableOn_compact (isCompact_boxPiSet (ι := pairFib2 n p) hℓ)))).symm

/-! ## 10. The target -/

theorem imgFibre2EnergyLe {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {F₁ G : Submission.BoseGases.X n → ℝ}
    (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hF₁ind : ∀ (x : Submission.BoseGases.X n) (t : EuclideanSpace ℝ (Fin 3)),
      F₁ (Function.update x p.1 t) = F₁ x)
    {Kg Kc : ℝ} (hKg0 : 0 ≤ Kg) (hKc0 : 0 ≤ Kc)
    (hKg : ∀ w : EuclideanSpace ℝ (Fin 3),
      ∑ j : Fin 3,
        ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg)
    (hKc : ∀ w : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale ℓ w) ^ 2 ≤ Kc) :
    Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.imgFibre₂C ℓ p F₁ G)
      ≤ max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2
        * (Work.BoseBoxFock.imgFibreN ℓ F₁
            * (Work.BoseBoxFock.imgFibreN ℓ G + Work.BoseBoxFock.imgFibreDχ ℓ p G) / ℓ ^ 6) := by
  have hA00 : (0 : ℝ) ≤ imgFibreMG ℓ p F₁ 0 := imgFibreMG_nonneg ℓ p F₁ 0
  -- the `u`-slice `imgFibreMG ℓ p F₁ u` is constant, and its `u`-marginal is `N(F₁)`
  have hA0N : ℓ ^ 3 * imgFibreMG ℓ p F₁ 0 = imgFibreN ℓ F₁ := by
    have hmf := imgFibre2_mf_integral hℓ p hp hF₁.continuous
    have h1 : (∫ u in boxL ℓ, imgFibreMG ℓ p F₁ u) = imgFibreN ℓ F₁ := by
      rw [← hmf]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      rw [imgFibreMG_unfold]
    have h2 : (∫ u in boxL ℓ, imgFibreMG ℓ p F₁ u) = ℓ ^ 3 * imgFibreMG ℓ p F₁ 0 := by
      rw [show (∫ u in boxL ℓ, imgFibreMG ℓ p F₁ u)
          = ∫ _u in boxL ℓ, imgFibreMG ℓ p F₁ 0 from
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun u => imgFibreMG_const p hF₁ind u)]
      rw [setIntegral_boxL_constBE hℓ]
    rw [← h2, h1]
  -- the value row of Cauchy–Schwarz
  have hval : ∀ u v : E3, (imgFibre₂ ℓ p F₁ G u v) ^ 2
      ≤ (ℓ ^ 3)⁻¹ * imgFibreMG ℓ p F₁ 0 * imgFibre2B ℓ p G u v := by
    intro u v
    have hsq := imgFibre2_sq_le hℓ p hF₁.continuous hG.continuous u v
    have h1 : (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
        (F₁ (insertCoord2 p u s x')) ^ 2) = imgFibreMG ℓ p F₁ 0 := by
      rw [← imgFibreMG_unfold]
      exact imgFibreMG_const p hF₁ind u
    have h2 : (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
        (G (insertCoord2 p u v x')) ^ 2) = ℓ ^ 3 * imgFibre2B ℓ p G u v :=
      imgFibre2B_sIntegral hℓ p G u v
    rw [h1, h2] at hsq
    refine hsq.trans (le_of_eq ?_)
    field_simp
  -- the Dirichlet row of Cauchy–Schwarz
  have hdb : ∀ u v : E3, ∑ j : Fin 3,
      (fderiv ℝ (fun u' => imgFibre₂ ℓ p F₁ G u' v) u (EuclideanSpace.single j (1 : ℝ))) ^ 2
        ≤ (ℓ ^ 3)⁻¹ * imgFibreMG ℓ p F₁ 0 * imgFibre2Q ℓ p G u v := by
    intro u v
    have hper : ∀ j : Fin 3,
        (fderiv ℝ (fun u' => imgFibre₂ ℓ p F₁ G u' v) u
          (EuclideanSpace.single j (1 : ℝ))) ^ 2
        ≤ ((ℓ ^ 3)⁻¹) ^ 2 * imgFibreMG ℓ p F₁ 0
          * (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
              (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2) := by
      intro j
      have hd := imgFibre2_deriv_sq_le hℓ p hF₁ hG hF₁ind v u j
      have h1 : (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
          (F₁ (insertCoord2 p u s x')) ^ 2) = imgFibreMG ℓ p F₁ 0 := by
        rw [← imgFibreMG_unfold]
        exact imgFibreMG_const p hF₁ind u
      rw [h1] at hd
      exact hd
    refine (Finset.sum_le_sum fun j _ => hper j).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, imgFibre2Qj_sum hℓ p hG u v]
    field_simp
  -- the box integral of the Dirichlet density
  have hQint : (∫ z in boxL ℓ ×ˢ boxL ℓ,
        (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * imgFibre2Q ℓ p G z.1 z.2)
      = imgFibreDχ ℓ p G := by
    have hchild := imgFibre2_dchi_integral hℓ p hp hG
    rw [← hchild]
    have hprod : (∫ z in boxL ℓ ×ˢ boxL ℓ,
          (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * imgFibre2Q ℓ p G z.1 z.2)
        = ∫ u in boxL ℓ, ∫ v in boxL ℓ,
            (Submission.BoseGases.chiScale ℓ u) ^ 2 * imgFibre2Q ℓ p G u v := by
      show (∫ z in boxL ℓ ×ˢ boxL ℓ,
          (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * imgFibre2Q ℓ p G z.1 z.2
        ∂((volume : Measure E3).prod (volume : Measure E3))) = _
      refine MeasureTheory.setIntegral_prod _ ?_
      exact integrable_prod_restrict_of_continuous
        (((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.comp
          continuous_fst).pow 2 |>.mul (continuous_imgFibre2Q hℓ p hG))
    rw [hprod]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [imgFibre2Q_unfold]
  exact imgFibre2EnergyLe_of_inputs hℓ hp hF₁ hG hKg0 hKc0 hA00 hKg hKc hA0N hval hdb
    (imgFibre2_Bint hℓ p hp hG.continuous) hQint

end Work.BoseBoxFock
