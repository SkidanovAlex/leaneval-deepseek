import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.W1omega_weight_facts
import Submission.Work.BoseBoxFock.chiChiImages_pairing_boxSmooth
import Submission.Work.BoseBoxFock.chiRow_muEvalAux
import Submission.Work.BoseBoxFock.exists_threshold_sideAt_ge_mul
import Submission.Work.BoseBoxFock.fibreEnergyExp
import Submission.Work.BoseBoxFock.kinFormBLeLowBudgetB
import Submission.Work.BoseBoxFock.pairRowS3Defs
import Submission.Work.BoseBoxFock.pinCond_norm_sq
import Submission.Work.BoseBoxFock.pinDirChiExp
import Submission.Work.BoseBoxFock.rowPairSubC_img_ae
import Submission.Work.BoseBoxFock.stripImages_arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.stripImages_cost_le` — the cost of stripping the `χχ`-images off the `Q₂` row

The node's `Q₂` row is `rowPairSubC (ℓ³)⁻¹ Θ pinCond KI KII` with the honest **limit** kernels
`KI = K1lim ℓ W₁'`, `KII = K1lim ℓ W₂'` (`W₁' = W1fun + W1omegaFun`, `W₂' = W1fun`).  Step (S3)
of `FINDING_PotPairRows_exists.md` replaces them by the *image-free* kernels
`pairRowNice ℓ Wᵢ'` (`K1lim = pairRowNice + chiChiImages`, `K1lim_eq_parts`).  This file proves
that **the images strip costs at most `½·errKafz v R μ C·normB`**, uniformly in the state.

## The route

* the row-level strip `rowPairSubC_stripImages` reduces the whole thing to the *pairing* estimate
  `|∫∫ chiChiImages ℓ W·G| ≤ ε·(√pairEnergy + √massBox)`, whose content is the PROVED Coulomb
  tail `chiChiImages_pairing_boxSmooth K`, with the **explicit** constant
  `Cimg = Classical.choose (chiChiImages_pairing_boxSmooth K)` — a *fixed* number, independent of
  `ℓ`, `R`, `W` (its `∃C` sits *before* `ℓ`), so no `ℓ`-dependent constant can hide in it;
* the row sum `Σ_{p} roots` is bounded through the fibre bounds `fibreEnergyExp`, which carry the
  window data `Kg`, `Kc` as **hypotheses** (so that no `Classical.choose` at a variable `ℓ` enters),
  and the state's Dirichlet content `pinDirChi`, bounded through `pinDirChiExp` (likewise with the
  window derivative bound as a hypothesis) + `kinFormBLeLowBudgetB` (`kap` is a *fixed* number);
* the arithmetic is then a comparison of explicit monomials in the diluteness `t = μ(a v)³` and the
  box side `ℓ = a (μa³)^{-163/323}` (via `sideAt_eq_rpow`), with the free constants `ε₀`, `C`.

**VERDICT: TRUE.**
-/

noncomputable section

set_option maxHeartbeats 4000000

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

/-! ## 0. Window data at a *fixed* constant

The corpus bounds `exists_chiS_bound` / `exists_chiS_grad_bound` produce, for each `ℓ`, a constant
through `Classical.choose`; a bound *uniform in `μ`* must not use them.  The window
`chiS ℓ = chiScale ℓ` is an explicit rescaling of the corpus bump, so both constants are explicit:
`Kc = chiPlateau²` and `Kg = 3·(chiGB·chiPlateau/ℓ)²`. -/

/-- `Theta` is nondecreasing in its threshold `J` when `A ≥ 0` (the difference is
`4πρ²A·J√(ρA³)`). -/
theorem Theta_le_Theta_zero {A J ρ : ℝ} (hA : 0 ≤ A) (hJ : J ≤ 0) :
    Work.UBB.Theta A J ρ ≤ Work.UBB.Theta A 0 ρ := by
  unfold Work.UBB.Theta
  have hcoef : 0 ≤ 4 * Real.pi * ρ ^ 2 * A :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (sq_nonneg ρ)) hA
  have hle1 : (1 : ℝ) ≤ 1 - J * Real.sqrt (ρ * A ^ 3) := by
    have : J * Real.sqrt (ρ * A ^ 3) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hJ (Real.sqrt_nonneg _)
    linarith
  have key : 4 * Real.pi * ρ ^ 2 * A * (1 - 0 * Real.sqrt (ρ * A ^ 3))
      ≤ 4 * Real.pi * ρ ^ 2 * A * (1 - J * Real.sqrt (ρ * A ^ 3)) := by
    have h := mul_le_mul_of_nonneg_left hle1 hcoef
    simpa [zero_mul] using h
  linarith [key]

/-- `pinCond` at a box side equal to its `ellH` value.  (`pinCond v μ c` unfolds to
`c · θ_{Λ(ellH v μ)}`; the row's box side is `sideAt μ (a v)`, propositionally equal.) -/
theorem pinCond_congr {v : ℝ³ → ℝ} {μ ℓ : ℝ} (h : ℓ = Work.BoseBoxFock.ellH v μ) (c : ℂ) :
    Work.BoseBoxFock.pinCond v μ c
      = fun x : ℝ³ => c * Work.BoseK15.corpusBox.thetaFun ℓ x := by
  rw [h]
  rfl

/-- The derivative of the corpus bump at scale `ℓ`, with the explicit constant
`chiGB·chiPlateau/ℓ`: `chiScale ℓ = chi(ℓ⁻¹·) = chiBase(ℓ⁻¹·)·(√chiNormSq)⁻¹`. -/
theorem chiScale_fderiv_bound (ℓ : ℝ) (hℓ : 0 < ℓ) (x v : ℝ³) :
    |fderiv ℝ (Submission.BoseGases.chiScale ℓ) x v|
      ≤ (L1Tails.chiGB * Work.BoseFixB1S.chiPlateau / ℓ) * ‖v‖ := by
  have hscale : HasFDerivAt (fun y : ℝ³ => (ℓ⁻¹ : ℝ) • y)
      ((ℓ⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℝ³) x :=
    (hasFDerivAt_id x).const_smul (ℓ⁻¹)
  have hcomp : HasFDerivAt (fun y : ℝ³ => Submission.BoseGases.chiBase ((ℓ⁻¹ : ℝ) • y))
      ((fderiv ℝ Submission.BoseGases.chiBase ((ℓ⁻¹ : ℝ) • x)) ∘SL
        ((ℓ⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℝ³)) x :=
    (Submission.BoseGases.chiBase_contDiff.differentiable (by simp) _).hasFDerivAt.comp x hscale
  have hfderiv : fderiv ℝ (Submission.BoseGases.chiScale ℓ) x
      = (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ •
          ((fderiv ℝ Submission.BoseGases.chiBase ((ℓ⁻¹ : ℝ) • x)) ∘SL
            ((ℓ⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℝ³)) := by
    have hfun : Submission.BoseGases.chiScale ℓ
        = fun y : ℝ³ => Submission.BoseGases.chiBase ((ℓ⁻¹ : ℝ) • y)
            * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := rfl
    rw [hfun]
    rw [fderiv_mul_const]
    · rw [hcomp.fderiv]
    · exact (Submission.BoseGases.chiBase_contDiff.differentiable (by simp) _).comp x
        (differentiableAt_id.const_smul (ℓ⁻¹))
  have hbase : ‖fderiv ℝ Submission.BoseGases.chiBase ((ℓ⁻¹ : ℝ) • x)‖ ≤ L1Tails.chiGB :=
    L1Tails.chiBase_fderiv_le_chiGB _
  have happ : |fderiv ℝ Submission.BoseGases.chiBase ((ℓ⁻¹ : ℝ) • x) ((ℓ⁻¹ : ℝ) • v)|
      ≤ L1Tails.chiGB * ((ℓ⁻¹ : ℝ) * ‖v‖) := by
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ Submission.BoseGases.chiBase ((ℓ⁻¹ : ℝ) • x) ((ℓ⁻¹ : ℝ) • v)‖
        ≤ ‖fderiv ℝ Submission.BoseGases.chiBase ((ℓ⁻¹ : ℝ) • x)‖ * ‖(ℓ⁻¹ : ℝ) • v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ L1Tails.chiGB * ‖(ℓ⁻¹ : ℝ) • v‖ :=
          mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
      _ = L1Tails.chiGB * ((ℓ⁻¹ : ℝ) * ‖v‖) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
  have hs : 0 ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
    le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos))
  rw [hfderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, abs_mul, abs_of_nonneg hs]
  refine (mul_le_mul_of_nonneg_left happ hs).trans ?_
  rw [show Work.BoseFixB1S.chiPlateau = (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ from rfl,
    show (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
      * (L1Tails.chiGB * ((ℓ⁻¹ : ℝ) * ‖v‖))
      = (L1Tails.chiGB * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ / ℓ) * ‖v‖ by
      rw [inv_mul_eq_div]; ring]

/-- The derivative of the complexification of a real function. -/
theorem ofReal_fderiv (f : ℝ³ → ℝ) (hf : Differentiable ℝ f) (x v : ℝ³) :
    fderiv ℝ (fun y => ((f y : ℝ) : ℂ)) x v = ((fderiv ℝ f x v : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun y : ℝ³ => ((f y : ℝ) : ℂ))
      ((Complex.ofRealCLM).comp (fderiv ℝ f x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hf x).hasFDerivAt
  rw [h1.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

/-- The explicit bound `Kg` for the squared gradient of the window `chiS ℓ`. -/
theorem chiS_grad_bound (ℓ : ℝ) (hℓ : 0 < ℓ) (w : ℝ³) :
    ∑ j : Fin 3, ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ 3 * (L1Tails.chiGB * Work.BoseFixB1S.chiPlateau / ℓ) ^ 2 := by
  have hbound : ∀ j : Fin 3,
      ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖
        ≤ L1Tails.chiGB * Work.BoseFixB1S.chiPlateau / ℓ := by
    intro j
    have h1 := chiScale_fderiv_bound ℓ hℓ w (EuclideanSpace.single j (1 : ℝ))
    have hn : ‖(EuclideanSpace.single j (1 : ℝ) : ℝ³)‖ = 1 := by simp
    have h2 : ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖
        = |fderiv ℝ (Submission.BoseGases.chiScale ℓ) w (EuclideanSpace.single j (1 : ℝ))| := by
      rw [show chiS ℓ = fun y => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ) from
        funext (chiS_eq ℓ)]
      rw [ofReal_fderiv (Submission.BoseGases.chiScale ℓ)
        ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).differentiable (by simp))
        w (EuclideanSpace.single j (1 : ℝ))]
      exact RCLike.norm_ofReal _
    rw [← h2, hn, mul_one] at h1
    exact h1
  calc ∑ j : Fin 3, ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ ∑ _j : Fin 3, (L1Tails.chiGB * Work.BoseFixB1S.chiPlateau / ℓ) ^ 2 :=
        Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hbound j) 2)
    _ = 3 * (L1Tails.chiGB * Work.BoseFixB1S.chiPlateau / ℓ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-- The explicit bound `Kc` for the squared window `chiS ℓ`. -/
theorem chiS_sq_bound (ℓ : ℝ) (w : ℝ³) :
    ‖chiS ℓ w‖ ^ 2 ≤ Work.BoseFixB1S.chiPlateau ^ 2 := by
  have h1 : ‖chiS ℓ w‖ = |Submission.BoseGases.chiScale ℓ w| := by
    rw [chiS_eq]; exact RCLike.norm_ofReal _
  rw [h1]
  have h2 : |Submission.BoseGases.chiScale ℓ w| ≤ Work.BoseFixB1S.chiPlateau := by
    simpa only [Work.BoseFixB1S.chiPlateau] using Submission.BoseGases.abs_chiScale_le ℓ w
  exact pow_le_pow_left₀ (abs_nonneg _) h2 2

/-! ## 1. The Coulomb energy of the two-block weight `W₁' = W1fun + W1omegaFun` -/

/-- The dominating scattering weight `g₀ = v(1−ω)` bounds the Coulomb energy of the *sum*
`W₁ + W₁ω ≤ 4g₀` a.e. (`W₁ ≤ (1+δ)g₀`, `W₁ω ≤ (1+δ)g₀`, `δ ≤ 1`). -/
theorem coulInt_sum_le {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R ℓ r₁ C : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |Submission.BoseGases.conv3 Submission.BoseGases.chi
      Submission.BoseGases.chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    (∫ p, coulInt (fun x : ℝ³ =>
        Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x) p)
      ≤ 1024 * Real.pi ^ 2 * BoseGases.a v := by
  set g : ℝ³ → ℝ := Submission.BoseGases.g0 v h with hgdef
  set δ : ℝ := 2 * C * (R / ℓ) ^ 2 with hδdef
  have hδ0 : 0 ≤ δ := by
    rw [hδdef]; exact mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg _)
  have hδle : δ ≤ 1 := by rw [hδdef]; linarith [hcond]
  -- facts about the dominating weight `g = g₀`
  have hgI : MeasureTheory.Integrable g := by
    rw [hgdef]; exact Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0 : ∀ᵐ x : ℝ³, 0 ≤ g x := by
    rw [hgdef]; exact Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  have hslice : ∀ᵐ x : ℝ³,
      (∫⁻ y, ENNReal.ofReal (g y * ‖x - y‖⁻¹)) ≤ ENNReal.ofReal (8 * Real.pi) := by
    have hh := Work.BoseFixR.FarLat.g0_coulPot_lintegral_ae_le (v := v) h hv hvrad hR hv_supp
    simpa [hgdef] using hh
  -- the a.e. domination of the two weights
  have hsand := Submission.BoseGases.wScaled_g0_ae_bounds (v := v) (R := R) (ℓ := ℓ)
    (r₁ := r₁) (C := C) hR hv hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
  obtain ⟨hW1I, hW10, hW1supp⟩ :=
    W1fun_integrable_of_regime (v := v) (h := h) (R := R) (ℓ := ℓ) (r₁ := r₁) (C := C)
      hR hv hvrad hv_supp hC hr₁ hT hℓ hreg hcond
  obtain ⟨hW2I, hW20, hW2le0, _hW2supp⟩ :=
    Work.BoseBoxFock.L1Tails.w1omegaFun_facts (v := v) (R := R) (ℓ := ℓ) (r₁ := r₁) (C := C)
      hR hv hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
  have hg0pt : ∀ᵐ x : ℝ³, 0 ≤ Submission.BoseGases.g0 v h x := hg0
  have hW1le : ∀ᵐ x : ℝ³, Work.BoseFixR.W1fun v h ℓ x ≤ 2 * g x := by
    filter_upwards [hsand, hg0pt] with x hx hgx
    have h2 : Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) x
        ≤ (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x := by nlinarith [hx.2]
    have h2' : Work.BoseFixR.W1fun v h ℓ x
        ≤ (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x := by
      simpa [Work.BoseFixR.W1fun] using h2
    have h3 : 2 * C * (R / ℓ) ^ 2 = δ := hδdef.symm
    have hcf : (1 + 2 * C * (R / ℓ) ^ 2) ≤ 2 := by linarith [hδle, le_of_eq h3]
    calc Work.BoseFixR.W1fun v h ℓ x
        ≤ (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x := h2'
      _ ≤ 2 * Submission.BoseGases.g0 v h x := mul_le_mul_of_nonneg_right hcf hgx
      _ = 2 * g x := by rw [hgdef]
  have hW2le : ∀ᵐ x : ℝ³, Work.BoseFixR.W1omegaFun v h ℓ x ≤ 2 * g x := by
    filter_upwards [hW2le0, hW20] with x hx hx0
    have hx' : Work.BoseFixR.W1omegaFun v h ℓ x
        ≤ (1 + 2 * C * (R / ℓ) ^ 2) * g x := by simpa [hgdef] using hx
    have hc0 : 0 < 1 + 2 * C * (R / ℓ) ^ 2 := by positivity
    have hgx : 0 ≤ g x := by
      by_contra hcon
      have hneg : (1 + 2 * C * (R / ℓ) ^ 2) * g x < 0 :=
        mul_neg_of_pos_of_neg hc0 (lt_of_not_ge hcon)
      linarith
    have h3 : 2 * C * (R / ℓ) ^ 2 = δ := hδdef.symm
    have hcf : (1 + 2 * C * (R / ℓ) ^ 2) ≤ 2 := by linarith [hδle, le_of_eq h3]
    exact hx'.trans (mul_le_mul_of_nonneg_right hcf hgx)
  have hsumle : ∀ᵐ x : ℝ³,
      Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x ≤ 4 * g x := by
    filter_upwards [hW1le, hW2le] with x h1 h2
    linarith
  have hsum0 : ∀ᵐ x : ℝ³,
      0 ≤ Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x := by
    filter_upwards [hW10, hW20] with x h1 h2
    linarith
  have hsumI : MeasureTheory.Integrable (fun x : ℝ³ =>
      Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x) := hW1I.add hW2I
  have hc : (0 : ℝ) ≤ 4 := by norm_num
  have hκ : (0 : ℝ) ≤ 8 * Real.pi := by positivity
  obtain ⟨_, hbound⟩ := L1Tails.coulInt_integrable_of_le (g := g)
    (A := fun x : ℝ³ => Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x)
    (c := 4) (κ := 8 * Real.pi) hc hκ hgI hg0 hsumI hsum0 hsumle hslice
  refine hbound.trans ?_
  have hgm : (∫ x, g x) = 8 * Real.pi * BoseGases.a v := by
    rw [hgdef]; exact Submission.BoseGases.chosen_scattering_integral h
  rw [hgm]
  nlinarith [Real.pi_pos]

/-! ## 2. Dilute-regime facts about the box side, with explicit thresholds -/

/-- For `μ (a v)³` small enough (`ε₀ = min 1 (min a^{323/163} a²)`), the box side
`ℓ = sideAt μ (a v)` satisfies `a v ≤ ℓ`, `1 ≤ ℓ`, `μ a v ≤ 1`, `1 ≤ μ ℓ³`, and the two-cutoff
constant `κ = (1−ε_T)(2sℓ)⁻² + ε_T(2dsℓ)⁻²` of `mainWord` is at most `1/(2 (a v)²)`. -/
theorem sideAt_regime {v : ℝ³ → ℝ} (hav : 0 < BoseGases.a v) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ μ : ℝ, 0 < μ → μ * (BoseGases.a v) ^ 3 ≤ ε →
      BoseGases.a v ≤ Work.BoseBox.sideAt μ (BoseGases.a v) ∧
      1 ≤ Work.BoseBox.sideAt μ (BoseGases.a v) ∧
      (μ * BoseGases.a v ≤ 1) ∧
      1 ≤ μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 ∧
      (1 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT)
          * ((2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).s
              * Work.BoseBox.sideAt μ (BoseGases.a v)))⁻¹) ^ 2
        + (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
          * ((2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d
              * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
              * Work.BoseBox.sideAt μ (BoseGases.a v)))⁻¹) ^ 2
        ≤ 1 / (2 * (BoseGases.a v) ^ 2) := by
  refine ⟨min 1 (min ((BoseGases.a v) ^ ((323 : ℝ) / 163)) ((BoseGases.a v) ^ 2)),
    lt_min one_pos (lt_min (Real.rpow_pos_of_pos hav _) (pow_pos hav 2)), min_le_left _ _, ?_⟩
  intro μ hμ ht
  set a := BoseGases.a v with ha
  have ha0 : 0 < a := hav
  have ht1 : μ * a ^ 3 ≤ 1 := le_trans ht (min_le_left _ _)
  have hta : μ * a ^ 3 ≤ a ^ ((323 : ℝ) / 163) :=
    le_trans ht (le_trans (min_le_right _ _) (min_le_left _ _))
  have hta2 : μ * a ^ 3 ≤ a ^ 2 := le_trans ht (le_trans (min_le_right _ _) (min_le_right _ _))
  set t : ℝ := μ * a ^ 3 with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht1' : t ≤ 1 := ht1
  have hℓ : Work.BoseBox.sideAt μ a = a * t ^ (-(163 / 323 : ℝ)) := by
    rw [htdef]; exact Work.BoseBox.sideAt_eq_rpow ha0 hμ
  have hpow1 : 1 ≤ t ^ (-(163 / 323 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos htpos ht1' (show (-(163 / 323 : ℝ)) ≤ 0 by norm_num)
    rwa [Real.one_rpow] at h
  have ha_le_ℓ : a ≤ Work.BoseBox.sideAt μ a := by
    rw [hℓ]
    calc a = a * 1 := by ring
      _ ≤ a * t ^ (-(163 / 323 : ℝ)) := mul_le_mul_of_nonneg_left hpow1 ha0.le
  have hpowa : t ^ (163 / 323 : ℝ) ≤ a := by
    have h1 : t ^ (163 / 323 : ℝ) ≤ (a ^ ((323 : ℝ) / 163)) ^ (163 / 323 : ℝ) :=
      Real.rpow_le_rpow htpos.le (by rw [htdef]; exact hta) (by norm_num)
    have h2 : (a ^ ((323 : ℝ) / 163)) ^ (163 / 323 : ℝ) = a := by
      rw [← Real.rpow_mul ha0.le]
      norm_num
    linarith [h1, le_of_eq h2]
  have hone_le_ℓ : 1 ≤ Work.BoseBox.sideAt μ a := by
    rw [hℓ]
    have h1 : a⁻¹ ≤ t ^ (-(163 / 323 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos htpos _) hpowa
        (show (-1 : ℝ) ≤ 0 by norm_num)
      rw [← Real.rpow_mul htpos.le,
        show (163 / 323 : ℝ) * (-1) = -(163 / 323 : ℝ) by norm_num] at h
      rw [Real.rpow_neg_one] at h
      exact h
    calc (1 : ℝ) = a * a⁻¹ := by field_simp
      _ ≤ a * t ^ (-(163 / 323 : ℝ)) := mul_le_mul_of_nonneg_left h1 ha0.le
  have hμa : μ * a ≤ 1 := by
    have h : μ * a = t / a ^ 2 := by
      rw [htdef]; field_simp
    rw [h, div_le_one (by positivity)]
    exact hta2
  have hμℓ3 : 1 ≤ μ * Work.BoseBox.sideAt μ a ^ 3 := by
    have h := Work.BoseBox.mu_ell_cube_fsParams (μ := μ) (a := a) hμ ha0
    have hside : Work.BoseBox.boxSide (Work.BoseBox.fsParams (μ * a ^ 3)) μ a
        = Work.BoseBox.sideAt μ a := by
      simp only [Work.BoseBox.sideAt, Work.BoseBox.paramsAt]
    rw [hside] at h
    rw [h]
    have h2 := Real.rpow_le_rpow_of_nonpos (show 0 < μ * a ^ 3 by positivity) ht1
      (show (-(166 / 323 : ℝ)) ≤ 0 by norm_num)
    rwa [Real.one_rpow] at h2
  have heT0 : 0 ≤ (Work.BoseBox.paramsAt μ a).eT := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
    exact Real.rpow_nonneg htpos.le _
  have heT1 : (Work.BoseBox.paramsAt μ a).eT ≤ 1 := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
    exact Real.rpow_le_one htpos.le ht1' (by norm_num)
  have hs : (Work.BoseBox.paramsAt μ a).s = t ^ ((1 : ℝ) / 323) := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp, htdef]
  have hd : (Work.BoseBox.paramsAt μ a).d = t ^ ((6 : ℝ) / 323) := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp, htdef]
  have hpow162 : 1 ≤ t ^ (-(162 / 323 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos htpos ht1' (show (-(162 / 323 : ℝ)) ≤ 0 by norm_num)
    rwa [Real.one_rpow] at h
  have hpow156 : 1 ≤ t ^ (-(156 / 323 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos htpos ht1' (show (-(156 / 323 : ℝ)) ≤ 0 by norm_num)
    rwa [Real.one_rpow] at h
  have hsℓ : a ≤ (Work.BoseBox.paramsAt μ a).s * Work.BoseBox.sideAt μ a := by
    rw [hs, hℓ]
    have hid : t ^ ((1 : ℝ) / 323) * (a * t ^ (-(163 / 323 : ℝ)))
        = a * t ^ (-(162 / 323 : ℝ)) := by
      have h1 : t ^ ((1 : ℝ) / 323) * t ^ (-(163 / 323 : ℝ)) = t ^ (-(162 / 323 : ℝ)) := by
        rw [← Real.rpow_add htpos]
        congr 1
        norm_num
      calc t ^ ((1 : ℝ) / 323) * (a * t ^ (-(163 / 323 : ℝ)))
          = a * (t ^ ((1 : ℝ) / 323) * t ^ (-(163 / 323 : ℝ))) := by ring
        _ = a * t ^ (-(162 / 323 : ℝ)) := by rw [h1]
    rw [hid]
    calc a = a * 1 := by ring
      _ ≤ a * t ^ (-(162 / 323 : ℝ)) := mul_le_mul_of_nonneg_left hpow162 ha0.le
  have hdsℓ : a ≤ (Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s
      * Work.BoseBox.sideAt μ a := by
    rw [hd, hs, hℓ]
    have hid : t ^ ((6 : ℝ) / 323) * t ^ ((1 : ℝ) / 323) * (a * t ^ (-(163 / 323 : ℝ)))
        = a * t ^ (-(156 / 323 : ℝ)) := by
      have h1 : t ^ ((6 : ℝ) / 323) * t ^ ((1 : ℝ) / 323) * t ^ (-(163 / 323 : ℝ))
          = t ^ (-(156 / 323 : ℝ)) := by
        rw [← Real.rpow_add htpos, ← Real.rpow_add htpos]
        congr 1
        norm_num
      calc t ^ ((6 : ℝ) / 323) * t ^ ((1 : ℝ) / 323) * (a * t ^ (-(163 / 323 : ℝ)))
          = a * (t ^ ((6 : ℝ) / 323) * t ^ ((1 : ℝ) / 323)
              * t ^ (-(163 / 323 : ℝ))) := by ring
        _ = a * t ^ (-(156 / 323 : ℝ)) := by rw [h1]
    rw [hid]
    calc a = a * 1 := by ring
      _ ≤ a * t ^ (-(156 / 323 : ℝ)) := mul_le_mul_of_nonneg_left hpow156 ha0.le
  have hsidepos : 0 < Work.BoseBox.sideAt μ a := lt_of_lt_of_le ha0 ha_le_ℓ
  have hb1 : ((2 * ((Work.BoseBox.paramsAt μ a).s * Work.BoseBox.sideAt μ a))⁻¹) ^ 2
      ≤ 1 / (4 * a ^ 2) := by
    have hpos : 0 < 2 * ((Work.BoseBox.paramsAt μ a).s * Work.BoseBox.sideAt μ a) := by
      have h0 : 0 < (Work.BoseBox.paramsAt μ a).s := by rw [hs]; positivity
      positivity
    have h2 : (2 * ((Work.BoseBox.paramsAt μ a).s * Work.BoseBox.sideAt μ a))⁻¹ ≤ (2 * a)⁻¹ :=
      inv_anti₀ (by positivity : (0 : ℝ) < 2 * a) (by linarith)
    calc ((2 * ((Work.BoseBox.paramsAt μ a).s * Work.BoseBox.sideAt μ a))⁻¹) ^ 2
        ≤ ((2 * a)⁻¹) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) h2 2
      _ = 1 / (4 * a ^ 2) := by field_simp; ring
  have hb2 : ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s
      * Work.BoseBox.sideAt μ a))⁻¹) ^ 2 ≤ 1 / (4 * a ^ 2) := by
    have hpos : 0 < 2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s
        * Work.BoseBox.sideAt μ a) := by
      have h0 : 0 < (Work.BoseBox.paramsAt μ a).d := by rw [hd]; positivity
      have h1 : 0 < (Work.BoseBox.paramsAt μ a).s := by rw [hs]; positivity
      positivity
    have h2 : (2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s
        * Work.BoseBox.sideAt μ a))⁻¹ ≤ (2 * a)⁻¹ :=
      inv_anti₀ (by positivity : (0 : ℝ) < 2 * a) (by linarith)
    calc ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s
          * Work.BoseBox.sideAt μ a))⁻¹) ^ 2
        ≤ ((2 * a)⁻¹) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) h2 2
      _ = 1 / (4 * a ^ 2) := by field_simp; ring
  refine ⟨ha_le_ℓ, hone_le_ℓ, hμa, hμℓ3, ?_⟩
  have hfin : (1 - (Work.BoseBox.paramsAt μ a).eT)
        * ((2 * ((Work.BoseBox.paramsAt μ a).s * Work.BoseBox.sideAt μ a))⁻¹) ^ 2
      + (Work.BoseBox.paramsAt μ a).eT
        * ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s
          * Work.BoseBox.sideAt μ a))⁻¹) ^ 2
      ≤ 1 * (1 / (4 * a ^ 2)) + 1 * (1 / (4 * a ^ 2)) := by
    refine add_le_add ?_ ?_
    · exact mul_le_mul (by linarith) hb1 (sq_nonneg _) (by norm_num)
    · exact mul_le_mul heT1 hb2 (sq_nonneg _) (by norm_num)
  rw [show (1 : ℝ) * (1 / (4 * a ^ 2)) + 1 * (1 / (4 * a ^ 2)) = 1 / (2 * a ^ 2) by ring]
    at hfin
  exact hfin


theorem stripImages_cost_le (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          0 < Work.BoseBoxFix.normB v μ n Φ →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
            (Φ : Submission.BoseGases.X n → ℝ) →
          ∀ (c : ℂ), (starRingEnd ℂ) c * c = ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ →
            ‖Work.BoseBoxFock.rowPairSubC (((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹)
                (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
                (Work.BoseBoxFock.pinCond v μ c)
                (Work.BoseBoxFock.K1lim (Work.BoseBoxFock.ellH v μ)
                  (fun x => Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x
                    + Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ) x))
                (Work.BoseBoxFock.K1lim (Work.BoseBoxFock.ellH v μ)
                  (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
              - Work.BoseBoxFock.rowPairSubC (((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹)
                (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
                (Work.BoseBoxFock.pinCond v μ c)
                (Work.BoseBoxFock.pairRowNice (Work.BoseBoxFock.ellH v μ)
                  (fun x => Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x
                    + Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ) x))
                (Work.BoseBoxFock.pairRowNice (Work.BoseBoxFock.ellH v μ)
                  (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))‖
              ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ := by
  classical
  -- ## 0. constants
  obtain ⟨Cimg, hCimg0, hCimg⟩ := chiChiImages_pairing_boxSmooth 6
  obtain ⟨chiC, hchiC0, rchi, hrchi, hchiT⟩ := Submission.BoseGases.conv3chi_second_order_bound
  obtain ⟨kap, εkap, hkappos, hεkappos, hkap⟩ :=
    kinFormBLeLowBudgetB (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε_sr, hε_srpos, hε_srle1, hε_sr⟩ := sideAt_regime (v := v) hav
  set rm : ℝ := (Real.sqrt (2 * chiC + 1))⁻¹ with hrmdef
  have hrmpos : 0 < rm := by
    rw [hrmdef]; exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hrmsq : chiC * rm ^ 2 ≤ 1 / 2 := by
    have h1 : rm ^ 2 = (2 * chiC + 1)⁻¹ := by
      rw [hrmdef, inv_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * chiC + 1)]
    rw [h1, mul_inv_le_iff₀ (by linarith : (0 : ℝ) < 2 * chiC + 1)]
    linarith
  set rr : ℝ := min (1 / 4) (min rchi rm) with hrrdef
  have hrrpos : 0 < rr := lt_min (by norm_num) (lt_min hrchi hrmpos)
  have hrr4 : rr ≤ 1 / 4 := min_le_left _ _
  have hrrr : rr ≤ rchi := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrrm : rr ≤ rm := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨ε_R, hε_Rpos, hε_Rle1, hε_R⟩ :=
    exists_threshold_sideAt_ge_mul (v := v) hav hR hrrpos
  set a : ℝ := BoseGases.a v with hadef
  have ha0 : 0 < a := hav
  set P : ℝ := Work.BoseFixB1S.chiPlateau with hPdef
  have hP0 : 0 ≤ P := Work.BoseFixB1S.chiPlateau_nonneg
  set K10 : ℝ := 4 + 16 * (1 / (2 * a ^ 2)) * P ^ 2
      + 24 * (L1Tails.chiGB * P / a) ^ 2 with hK10def
  have hK100 : 0 ≤ K10 := by rw [hK10def]; positivity
  set Cwin0 : ℝ := max (2 * (3 * (L1Tails.chiGB * P / a) ^ 2) + (1 / a ^ 2) * P ^ 2) 2 with hCwin0def
  have hCwin00 : 0 ≤ Cwin0 := le_trans (by norm_num) (le_max_right _ _)
  set Croot0 : ℝ := 3 * (Real.sqrt Cwin0 + 1) with hCroot0def
  have hCroot00 : 0 ≤ Croot0 := by rw [hCroot0def]; positivity
  set Ccoef : ℝ := 256 * Real.pi * Real.sqrt a * Cimg * Croot0 * R ^ 6
      * Real.sqrt (2 * K10 * (kap + 2)) with hCcoefdef
  have hCcoef0 : 0 ≤ Ccoef := by rw [hCcoefdef]; positivity
  refine ⟨min (min ε_R ε_sr) (min εkap 1),
    4 * Ccoef * a ^ (-(11 / 2) : ℝ) + 1,
    lt_min (lt_min hε_Rpos hε_srpos) (lt_min hεkappos one_pos), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ a ^ (-(11 / 2) : ℝ) := Real.rpow_nonneg ha0.le _
    nlinarith [hCcoef0, h1]
  intro μ hAdm hJ
  set ℓ : ℝ := Work.BoseBox.sideAt μ a with hℓdef
  have hℓpos : 0 < ℓ := by rw [hℓdef]; exact Work.BoseBox.sideAt_pos hAdm.1 ha0
  have hℓeq : Work.BoseBoxFock.ellH v μ = ℓ := by
    rw [Work.BoseBoxFock.ellH, if_pos (by rw [← hℓdef]; exact hℓpos), hℓdef]
  intro n Φ hn hnorm hlow hspec c hc
  -- ## 1. the thresholds and the dilute regime
  have hμ : 0 < μ := hAdm.1
  have htε : μ * a ^ 3 ≤ min (min ε_R ε_sr) (min εkap 1) := hAdm.2.1
  have hPOK : Work.BoseBox.ParamsOK (Work.BoseBox.paramsAt μ a) (μ * a ^ 3) := hAdm.2.2
  obtain ⟨_hXp, hdP, hsP, heT0P, heT1P, hbP, _hKlP⟩ := Work.BoseBox.paramsAt_facts hμ hPOK
  have ht1 : μ * a ^ 3 ≤ 1 :=
    le_trans htε (le_trans (min_le_right _ _) (min_le_right _ _))
  have htR : μ * a ^ 3 ≤ ε_R := le_trans htε (le_trans (min_le_left _ _) (min_le_left _ _))
  have htSR : μ * a ^ 3 ≤ ε_sr := le_trans htε (le_trans (min_le_left _ _) (min_le_right _ _))
  have htk : μ * a ^ 3 ≤ εkap := le_trans htε (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc' : (starRingEnd ℂ) c * c = ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ := hc
  rw [hℓeq] at hc ⊢
  have hℓ : 0 < ℓ := hℓpos
  obtain ⟨ha_le_ℓ, hone_le_ℓ, hμa, hμℓ3, hκbr⟩ := hε_sr μ hμ htSR
  set pL : ℝ := Work.BoseBoxFix.normB v μ n Φ with hpLdef
  have hpL : 0 ≤ pL := Work.BoseFixB1.normB_nonneg Φ
  have hRrr : R ≤ ℓ * rr := hε_R μ hμ htR
  have hRdiv : R / ℓ ≤ rr := by
    rw [div_le_iff₀ hℓ, mul_comm]
    exact hRrr
  have hRℓ4 : R ≤ ℓ / 4 := by
    calc R ≤ ℓ * rr := hRrr
      _ ≤ ℓ * (1 / 4) := mul_le_mul_of_nonneg_left hrr4 hℓ.le
      _ = ℓ / 4 := by ring
  have hreg : R / ℓ ≤ rchi := le_trans hRdiv hrrr
  have hcond : chiC * (R / ℓ) ^ 2 ≤ 1 / 2 := by
    have hRl0 : 0 ≤ R / ℓ := by positivity
    have h1 : R / ℓ ≤ rm := le_trans hRdiv hrrm
    have hsq : (R / ℓ) ^ 2 ≤ rm ^ 2 := by
      have hmul := mul_le_mul h1 h1 hRl0 hrmpos.le
      simpa [pow_two] using hmul
    calc chiC * (R / ℓ) ^ 2 ≤ chiC * rm ^ 2 := mul_le_mul_of_nonneg_left hsq hchiC0
      _ ≤ 1 / 2 := hrmsq
  -- ## 2. the weights and their `L¹`/Coulomb data
  obtain ⟨hW1i, hW10, hW1s⟩ := W1fun_integrable_of_regime (v := v) (h := h) (R := R) (ℓ := ℓ)
    (r₁ := rchi) (C := chiC) hR hv hvrad hv_supp hchiC0 hrchi hchiT hℓ hreg hcond
  obtain ⟨hW2i, hW20, hW2s, _hW2e, _hW2J, hWsumJ⟩ := W1omega_weight_facts (v := v) (h := h)
    (R := R) (ℓ := ℓ) (r₁ := rchi) (C := chiC) hR hv hvrad hv_supp hchiC0 hrchi hchiT hℓ hreg hcond
  obtain ⟨hW1Jint, hW1J, _hW2Jint, _hW2J⟩ := L1Tails.W1fun_coulomb_le (v := v) (R := R) (ℓ := ℓ)
    (r₁ := rchi) (C := chiC) hR hv hvrad hv_supp h hchiC0 hrchi hchiT hℓ hreg hcond
  set W₁ : ℝ³ → ℝ := fun x => Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x
    with hW1def
  set W₂ : ℝ³ → ℝ := Work.BoseFixR.W1fun v h ℓ with hW2def
  have hW₁i : MeasureTheory.Integrable W₁ := hW1i.add hW2i
  have hW₁0 : ∀ᵐ x : ℝ³, 0 ≤ W₁ x := by
    filter_upwards [hW10, hW20] with x h1 h2
    simp only [hW1def]; linarith
  have hW₁s : ∀ x : ℝ³, R ≤ ‖x‖ → W₁ x = 0 := by
    intro x hx
    simp only [hW1def]; rw [hW1s x hx, hW2s x hx, add_zero]
  have hW₂i : MeasureTheory.Integrable W₂ := hW1i
  have hW₂0 : ∀ᵐ x : ℝ³, 0 ≤ W₂ x := by
    filter_upwards [hW10] with x h1; simpa only [hW2def] using h1
  have hW₂s : ∀ x : ℝ³, R ≤ ‖x‖ → W₂ x = 0 := by
    intro x hx; simpa only [hW2def] using hW1s x hx
  have hW₁Jint : MeasureTheory.Integrable (coulInt W₁) := by rw [hW1def]; exact hWsumJ
  have hW₂Jint : MeasureTheory.Integrable (coulInt W₂) := by rw [hW2def]; exact hW1Jint
  have hcoul₁ : (∫ p, coulInt W₁ p) ≤ 1024 * Real.pi ^ 2 * a := by
    rw [hW1def]
    exact coulInt_sum_le (v := v) (h := h) (R := R) (ℓ := ℓ) (r₁ := rchi) (C := chiC)
      hR hv hvrad hv_supp hchiC0 hrchi hchiT hℓ hreg hcond
  have hcoul₂ : (∫ p, coulInt W₂ p) ≤ 1024 * Real.pi ^ 2 * a := by
    rw [hW2def, hadef]
    have hX0 : (0 : ℝ) ≤ Real.pi ^ 2 * BoseGases.a v :=
      mul_nonneg (pow_nonneg Real.pi_pos.le 2) hav.le
    have hle : (256 : ℝ) * (Real.pi ^ 2 * BoseGases.a v)
        ≤ 1024 * (Real.pi ^ 2 * BoseGases.a v) := by linarith
    calc (∫ p, coulInt (Work.BoseFixR.W1fun v h ℓ) p)
        ≤ 256 * Real.pi ^ 2 * BoseGases.a v := hW1J
      _ = 256 * (Real.pi ^ 2 * BoseGases.a v) := by ring
      _ ≤ 1024 * (Real.pi ^ 2 * BoseGases.a v) := hle
      _ = 1024 * Real.pi ^ 2 * BoseGases.a v := by ring
  have hsqrt_a : Real.sqrt (1024 * Real.pi ^ 2 * a) = 32 * Real.pi * Real.sqrt a := by
    rw [show (1024 : ℝ) * Real.pi ^ 2 * a = (32 * Real.pi) ^ 2 * a by ring,
      Real.sqrt_mul (by positivity) a, Real.sqrt_sq (by positivity)]
  -- ## 3. the state data
  set Θ : Work.BoseDict.Xn n → ℂ := Work.BoseBoxFock.boxRestrictC ℓ Φ with hΘdef
  set A : ℝ³ → ℂ := Work.BoseBoxFock.pinCond v μ c with hAdef
  set Θ₀ : Work.BoseDict.Xn n → ℂ := fun x => ((Φ x : ℝ) : ℂ) with hΘ₀def
  set εimg : ℝ := Cimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a) * (ℓ * Real.sqrt ℓ)
    with hεimgdef
  have hεimg0 : 0 ≤ εimg := by rw [hεimgdef]; positivity
  have hΘm : Measurable Θ := by
    rw [hΘdef]
    exact Work.BoseBoxFock.boxRestrictC_measurable ℓ Φ.contDiff.continuous
  have hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C := by
    rw [hΘdef]
    obtain ⟨C, _hC0, hC⟩ := Work.BoseBoxFock.boxRestrictC_norm_bound hℓ Φ.contDiff.continuous
    exact ⟨C, hC⟩
  have hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ := by
    intro x hx
    have h1 := Work.BoseBoxFock.boxRestrictC_support_subset ℓ Φ hx
    rw [Submission.BoseGases.abox_eq_pi_acube] at h1
    rw [Work.MB.boxPow, Work.BoseBoxFock.corpusBox_boxL_eq_acube hℓ]
    exact h1
  have hΘind : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x := by
    intro x
    rw [hΘdef, hΘ₀def]
    simp only [Work.BoseBoxFock.boxRestrictC]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hboxpt : ∀ x : Submission.BoseGases.X n, ‖Work.BoseBoxFock.boxRestrictC ℓ Φ x‖ ^ 2
      = (Submission.BoseGases.abox n ℓ).indicator (fun x => (Φ x) ^ 2) x := by
    intro x
    rw [show Work.BoseBoxFock.boxRestrictC ℓ Φ x
        = ((Φ x : ℝ) : ℂ) * ((((Submission.BoseGases.abox n ℓ).indicator
            (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) from rfl]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Complex.ofReal_one, mul_one,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp
  have hΘL : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n => ‖Θ x‖ ^ 2) := by
    rw [hΘdef, funext hboxpt]
    exact MeasureTheory.IntegrableOn.integrable_indicator
      (ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
        ((Φ.contDiff.continuous.pow 2).continuousOn))
      (Submission.BoseGases.abox_measurable n ℓ)
  have hAc : A = fun x : ℝ³ => c * Work.BoseK15.corpusBox.thetaFun ℓ x :=
    hAdef.trans (pinCond_congr hℓeq.symm c)
  have hAm : Measurable A := by
    rw [hAc]
    exact measurable_const.mul (Work.BoseBoxFock.k1thetaFun_measurable ℓ)
  have hAb' : ∀ x : ℝ³, ‖A x‖ ≤ ‖c‖ := by
    intro x
    rw [hAc, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg c) ?_
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [if_pos hx]; simp
    · rw [if_neg hx]; simp
  have hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C := ⟨‖c‖, hAb'⟩
  have hAL : MeasureTheory.Integrable (fun x : ℝ³ => ‖A x‖ ^ 2) := by
    rw [hAc]
    have hpt : ∀ x : ℝ³, ‖c * Work.BoseK15.corpusBox.thetaFun ℓ x‖ ^ 2
        = ‖c‖ ^ 2 * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : ℝ³ => (1 : ℝ)) x := by
      intro x
      rw [norm_mul, mul_pow, Work.BoseB4.BoxData.thetaFun_apply]
      by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [if_pos hx, Set.indicator_of_mem hx]; simp
      · rw [if_neg hx, Set.indicator_of_notMem hx]; simp
    rw [funext hpt]
    refine MeasureTheory.Integrable.const_mul ?_ _
    have hfin : (volume : Measure ℝ³) (Work.BoseK15.corpusBox.boxL ℓ) < ⊤ :=
      (Work.BoseBoxFock.isCompact_boxL hℓ).measure_lt_top
    exact (MeasureTheory.integrable_indicator_iff
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)).mpr
      (MeasureTheory.integrableOn_const (C := (1 : ℝ)) (hs := ne_of_lt hfin))
  have hCutA : Work.BoseBoxFock.CutSmooth1 ℓ A := by
    rw [hAc]
    refine ⟨fun _ => c, contDiff_const, fun x => ?_⟩
    simp only [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [if_pos hx, Set.indicator_of_mem hx, mul_one]
    · rw [if_neg hx, Set.indicator_of_notMem hx, mul_zero]
  have hCutΘ : Work.BoseBoxFock.CutSmooth ℓ Θ :=
    ⟨Θ₀, Complex.ofRealCLM.contDiff.comp Φ.contDiff, hΘind⟩
  have hA2 : (∫ x : ℝ³, ‖A x‖ ^ 2) = 1 := by
    rw [hAdef]; exact Work.BoseBoxFock.pinCond_norm_sq hc'
  have hnormB : (∫ x : Work.BoseDict.Xn n, ‖Θ x‖ ^ 2) = pL := by
    rw [hΘdef, hpLdef]
    simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    rw [funext hboxpt, MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable n ℓ)]
  -- ## 4. the pairing hypothesis at the images kernel
  have hpair_at (W : ℝ³ → ℝ) (hWi : MeasureTheory.Integrable W)
      (hW0 : ∀ᵐ x : ℝ³, 0 ≤ W x) (hWs : ∀ x : ℝ³, R ≤ ‖x‖ → W x = 0)
      (hWJint : MeasureTheory.Integrable (coulInt W))
      (hWJ : (∫ p, coulInt W p) ≤ 1024 * Real.pi ^ 2 * a)
      {G : ℝ³ → ℝ³ → ℂ} (hG : Work.BoseBoxFock.BoxSmooth ℓ G) :
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
        ≤ εimg * (Real.sqrt (L1Tails.pairEnergy ℓ G) + Real.sqrt (massBox ℓ G)) := by
    have h1 := hCimg hℓ hR hRℓ4 hWi hW0 hWs hWJint hG
    have h2 : Real.sqrt (∫ p, coulInt W p) ≤ 32 * Real.pi * Real.sqrt a := by
      calc Real.sqrt (∫ p, coulInt W p) ≤ Real.sqrt (1024 * Real.pi ^ 2 * a) :=
            Real.sqrt_le_sqrt hWJ
        _ = 32 * Real.pi * Real.sqrt a := hsqrt_a
    have h3 : Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ G)
        = (ℓ * Real.sqrt ℓ) * Real.sqrt (L1Tails.pairEnergy ℓ G) := by
      rw [Real.sqrt_mul (by positivity),
        show Real.sqrt (ℓ ^ 3) = ℓ * Real.sqrt ℓ by
          rw [show ℓ ^ 3 = ℓ ^ 2 * ℓ by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq hℓ.le]]
    have hPE : 0 ≤ Real.sqrt (L1Tails.pairEnergy ℓ G) := Real.sqrt_nonneg _
    have hMB : 0 ≤ Real.sqrt (massBox ℓ G) := Real.sqrt_nonneg _
    have hCnn : 0 ≤ Cimg * (R / ℓ) ^ 6 := mul_nonneg hCimg0 (by positivity)
    have hstep : Real.sqrt (∫ p, coulInt W p) * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ G)
        ≤ (32 * Real.pi * Real.sqrt a) * ((ℓ * Real.sqrt ℓ)
            * Real.sqrt (L1Tails.pairEnergy ℓ G)) := by
      rw [h3]
      exact mul_le_mul h2 (le_refl _) (by positivity) (by positivity)
    have h4 : Cimg * (R / ℓ) ^ 6 * Real.sqrt (∫ p, coulInt W p)
          * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ G)
        ≤ Cimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a)
          * ((ℓ * Real.sqrt ℓ) * Real.sqrt (L1Tails.pairEnergy ℓ G)) := by
      rw [show Cimg * (R / ℓ) ^ 6 * Real.sqrt (∫ p, coulInt W p)
            * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ G)
          = (Cimg * (R / ℓ) ^ 6)
            * (Real.sqrt (∫ p, coulInt W p) * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ G))
          from by ring]
      exact (mul_le_mul_of_nonneg_left hstep hCnn).trans_eq (by ring)
    have h5 : Cimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a)
          * ((ℓ * Real.sqrt ℓ) * Real.sqrt (L1Tails.pairEnergy ℓ G))
        = εimg * Real.sqrt (L1Tails.pairEnergy ℓ G) := by
      rw [hεimgdef]; ring
    calc ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
        ≤ Cimg * (R / ℓ) ^ 6 * Real.sqrt (∫ p, coulInt W p)
            * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ G) := h1
      _ ≤ εimg * Real.sqrt (L1Tails.pairEnergy ℓ G) := h4.trans (le_of_eq h5)
      _ ≤ εimg * (Real.sqrt (L1Tails.pairEnergy ℓ G) + Real.sqrt (massBox ℓ G)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hMB) hεimg0
  -- ## 5. the two stripped kernels: `K1lim = pairRowNice + chiChiImages`
  have hk1 : (fun w y : ℝ³ => Work.BoseBoxFock.K1lim ℓ W₁ w y
        - Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W₁ z : ℝ) : ℂ)) w y)
      = Work.BoseBoxFock.pairRowNice ℓ W₁ := by
    funext w y
    rw [Work.BoseBoxFock.K1lim_eq_parts hℓ (fun z hz => hW₁s z hz.le) w y]
    simp only [Work.BoseBoxFock.pairRowNice]
    ring
  have hk2 : (fun w y : ℝ³ => Work.BoseBoxFock.K1lim ℓ W₂ w y
        - Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W₂ z : ℝ) : ℂ)) w y)
      = Work.BoseBoxFock.pairRowNice ℓ W₂ := by
    funext w y
    rw [Work.BoseBoxFock.K1lim_eq_parts hℓ (fun z hz => hW₂s z hz.le) w y]
    simp only [Work.BoseBoxFock.pairRowNice]
    ring
  rw [← hk1, ← hk2]
  -- ## 6. the row-level images strip
  set S : ℝ := ∑ p ∈ Submission.BoseGases.pairSet n,
      ((Real.sqrt (L1Tails.pairEnergy ℓ (pairG13 p Θ A A))
          + Real.sqrt (massBox ℓ (pairG13 p Θ A A)))
        + (Real.sqrt (L1Tails.pairEnergy ℓ (pairG21 p Θ A))
          + Real.sqrt (massBox ℓ (pairG21 p Θ A)))
        + (Real.sqrt (L1Tails.pairEnergy ℓ (pairG23 p Θ A A))
          + Real.sqrt (massBox ℓ (pairG23 p Θ A A)))) with hSdef
  have hstrip :
      ‖Work.BoseBoxFock.rowPairSubC ((ℓ ^ 3)⁻¹) Θ A
          (Work.BoseBoxFock.K1lim ℓ W₁) (Work.BoseBoxFock.K1lim ℓ W₂)
        - Work.BoseBoxFock.rowPairSubC ((ℓ ^ 3)⁻¹) Θ A
          (fun w y => Work.BoseBoxFock.K1lim ℓ W₁ w y
            - Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W₁ z : ℝ) : ℂ)) w y)
          (fun w y => Work.BoseBoxFock.K1lim ℓ W₂ w y
            - Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W₂ z : ℝ) : ℂ)) w y)‖
        ≤ 2 * |(ℓ ^ 3)⁻¹| * εimg * S := by
    exact Work.BoseBoxFock.rowPairSubC_img_ae (n := n) (ℓ := ℓ) (a := (ℓ ^ 3)⁻¹)
      (ε := εimg) (Θ := Θ) (A := A) (Θ₀ := Θ₀) (W₁ := W₁) (W₂ := W₂)
      (W₁' := W₁) (W₂' := W₂)
      hℓ hεimg0 hΘm hΘb (Complex.ofRealCLM.contDiff.comp Φ.contDiff) hΘind hΘs hΘL
      hAm hAb hAL hCutA
      hW₁i hW₂i hW₁i hW₂i
      (fun G hG => hpair_at W₁ hW₁i hW₁0 hW₁s hW₁Jint hcoul₁ hG)
      (fun G hG => hpair_at W₂ hW₂i hW₂0 hW₂s hW₂Jint hcoul₂ hG)
  -- ## 7. the pinning constant and the state's L²/Dirichlet content
  have hcn : ‖c‖ ^ 2 = (ℓ ^ 3)⁻¹ := by
    have h1 : ((Complex.normSq c : ℝ) : ℂ) = (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.mul_conj c, mul_comm]
      exact hc
    have h2 : Complex.normSq c = (ℓ ^ 3)⁻¹ := Complex.ofReal_inj.mp h1
    rwa [Complex.normSq_eq_norm_sq] at h2
  have hcc : ℓ ^ 6 * ‖c‖ ^ 2 * ‖c‖ ^ 2 = 1 := by
    rw [hcn]
    have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
    field_simp
  have hΦ2 : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) = pL := by
    rw [hpLdef]
    simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    rfl
  have hL2p : Work.BoseBoxFock.pinL2 ℓ Θ₀ = pL := by
    rw [Work.BoseBoxFock.pinL2, hΘ₀def, hpLdef]
    simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ) ?_
    intro x _
    simp
  have hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀ := Complex.ofRealCLM.contDiff.comp Φ.contDiff
  have hD0 : 0 ≤ Work.BoseBoxFock.pinDirChi ℓ Θ₀ := Work.BoseBoxFock.pinDirChi_nonneg ℓ Θ₀
  have hchiGB0 : 0 ≤ L1Tails.chiGB :=
    le_trans (norm_nonneg (fderiv ℝ Submission.BoseGases.chiBase (0 : ℝ³)))
      (L1Tails.chiBase_fderiv_le_chiGB 0)
  have hKinB : Work.BoseKinLoc.kinFormB n ℓ (Work.BoseBox.paramsAt μ a).d
        (Work.BoseBox.paramsAt μ a).s (Work.BoseBox.paramsAt μ a).eT
        (Work.BoseBox.paramsAt μ a).b (Φ : Submission.BoseGases.X n → ℝ)
      ≤ kap * μ ^ 2 * a * ℓ ^ 3 * pL := by
    have hAdmkap : Work.BoseBoxFix.Adm v εkap μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
    rcases le_or_gt 0 J with hJ0 | hJneg
    · exact hkap μ hAdmkap J hJ0 hJ n Φ hlow hn
    · have hθ : Work.UBB.Theta (BoseGases.a v) J μ ≤ Work.UBB.Theta (BoseGases.a v) 0 μ :=
        Theta_le_Theta_zero hav.le hJneg.le
      have hstep : Work.BoseBox.sideAt μ a ^ 3 * Work.UBB.Theta (BoseGases.a v) J μ
            * Work.BoseBoxFix.normB v μ n Φ
          ≤ Work.BoseBox.sideAt μ a ^ 3 * Work.UBB.Theta (BoseGases.a v) 0 μ
            * Work.BoseBoxFix.normB v μ n Φ := by
        refine mul_le_mul_of_nonneg_right ?_ (Work.BoseFixB1.normB_nonneg Φ)
        exact mul_le_mul_of_nonneg_left hθ (pow_nonneg hℓpos.le 3)
      have hlow0 : Work.BoseBoxFix.IsLowB v h 0 μ n Φ := by
        have hall := hlow
        simp only [Work.BoseBoxFix.IsLowB] at hall ⊢
        exact hall.trans hstep
      have hKB0 : 0 ≤ (Work.BoseBox.paramsAt μ a).KB ^ 3 := by
        have hKBpos : 0 < (Work.BoseBox.paramsAt μ a).KB := by
          simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
          exact Real.rpow_pos_of_pos (mul_pos hμ (pow_pos ha0 3)) _
        exact pow_nonneg hKBpos.le 3
      exact hkap μ hAdmkap 0 (le_refl 0) hKB0 n Φ hlow0 hn
  have hDbound : Work.BoseBoxFock.pinDirChi ℓ Θ₀ ≤ K10 * (2 + kap) * μ * ℓ ^ 3 * pL := by
    have hD : ∀ x v : ℝ³, |fderiv ℝ (Submission.BoseGases.chiScale ℓ) x v|
        ≤ (L1Tails.chiGB * P / a) * ‖v‖ := by
      intro x v
      refine (chiScale_fderiv_bound ℓ hℓ x v).trans ?_
      have h1 : ℓ⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 ha_le_ℓ
      have h2 : L1Tails.chiGB * P / ℓ ≤ L1Tails.chiGB * P / a := by
        calc L1Tails.chiGB * P / ℓ = (L1Tails.chiGB * P) * ℓ⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ (L1Tails.chiGB * P) * a⁻¹ := mul_le_mul_of_nonneg_left h1 (mul_nonneg hchiGB0 hP0)
          _ = L1Tails.chiGB * P / a := by rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg v)
    have hpd := Work.BoseBoxFock.pinDirChiExp (l := ℓ) (d := (Work.BoseBox.paramsAt μ a).d)
      (s := (Work.BoseBox.paramsAt μ a).s) (εT := (Work.BoseBox.paramsAt μ a).eT)
      (b := (Work.BoseBox.paramsAt μ a).b) (D := L1Tails.chiGB * P / a)
      hℓ hdP hsP hbP heT0P heT1P (by positivity) hD Φ
    have hK10' : 4 + 16 * ((1 - (Work.BoseBox.paramsAt μ a).eT)
          * ((2 * ((Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2
        + (Work.BoseBox.paramsAt μ a).eT
          * ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2)
        * P ^ 2 + 24 * (L1Tails.chiGB * P / a) ^ 2 ≤ K10 := by
      rw [hK10def]
      have h1 : 16 * ((1 - (Work.BoseBox.paramsAt μ a).eT)
            * ((2 * ((Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2
          + (Work.BoseBox.paramsAt μ a).eT
            * ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2)
          * P ^ 2 ≤ 16 * (1 / (2 * a ^ 2)) * P ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκbr (by norm_num)) (sq_nonneg P)
      linarith [h1]
    have hCbig0 : 0 ≤ 4 + 16 * ((1 - (Work.BoseBox.paramsAt μ a).eT)
          * ((2 * ((Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2
        + (Work.BoseBox.paramsAt μ a).eT
          * ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2)
        * P ^ 2 + 24 * (L1Tails.chiGB * P / a) ^ 2 := by
      have h2 : 0 ≤ ((1 - (Work.BoseBox.paramsAt μ a).eT)
            * ((2 * ((Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2
          + (Work.BoseBox.paramsAt μ a).eT
            * ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2) :=
        add_nonneg (mul_nonneg (by linarith [heT1P]) (sq_nonneg _))
          (mul_nonneg heT0P (sq_nonneg _))
      have h3 : 0 ≤ (4 + 16 * ((1 - (Work.BoseBox.paramsAt μ a).eT)
            * ((2 * ((Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2
          + (Work.BoseBox.paramsAt μ a).eT
            * ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2)
          * P ^ 2 + 24 * (L1Tails.chiGB * P / a) ^ 2) :=
        add_nonneg (add_nonneg (by norm_num)
          (mul_nonneg (mul_nonneg (by norm_num) h2) (sq_nonneg P)))
          (mul_nonneg (by norm_num) (sq_nonneg _))
      exact h3
    have hsum : Work.BoseKinLoc.kinFormB n ℓ (Work.BoseBox.paramsAt μ a).d
          (Work.BoseBox.paramsAt μ a).s (Work.BoseBox.paramsAt μ a).eT
          (Work.BoseBox.paramsAt μ a).b (Φ : Submission.BoseGases.X n → ℝ)
        + (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
        ≤ (2 + kap) * μ * ℓ ^ 3 * pL := by
      have h2 : (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
          ≤ 2 * μ * ℓ ^ 3 * pL := by
        rw [hΦ2]
        exact mul_le_mul_of_nonneg_right hn hpL
      have h3 : kap * μ ^ 2 * a * ℓ ^ 3 * pL ≤ kap * μ * ℓ ^ 3 * pL := by
        have h1 : μ ^ 2 * a ≤ μ := by
          calc μ ^ 2 * a = μ * (μ * a) := by ring
            _ ≤ μ * 1 := mul_le_mul_of_nonneg_left hμa hμ.le
            _ = μ := by ring
        calc kap * μ ^ 2 * a * ℓ ^ 3 * pL = kap * (μ ^ 2 * a) * ℓ ^ 3 * pL := by ring
          _ ≤ kap * μ * ℓ ^ 3 * pL := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h1 hkappos.le)
                (pow_nonneg hℓpos.le 3)) hpL
      linarith [hKinB, h2, h3]
    calc Work.BoseBoxFock.pinDirChi ℓ Θ₀
        ≤ (4 + 16 * ((1 - (Work.BoseBox.paramsAt μ a).eT)
            * ((2 * ((Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2
          + (Work.BoseBox.paramsAt μ a).eT
            * ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2)
          * P ^ 2 + 24 * (L1Tails.chiGB * P / a) ^ 2)
          * (Work.BoseKinLoc.kinFormB n ℓ (Work.BoseBox.paramsAt μ a).d
              (Work.BoseBox.paramsAt μ a).s (Work.BoseBox.paramsAt μ a).eT
              (Work.BoseBox.paramsAt μ a).b (Φ : Submission.BoseGases.X n → ℝ)
            + (n : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ,
                ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := hpd
      _ ≤ K10 * ((2 + kap) * μ * ℓ ^ 3 * pL) := by
          have hsum0 : 0 ≤ Work.BoseKinLoc.kinFormB n ℓ (Work.BoseBox.paramsAt μ a).d
                (Work.BoseBox.paramsAt μ a).s (Work.BoseBox.paramsAt μ a).eT
                (Work.BoseBox.paramsAt μ a).b (Φ : Submission.BoseGases.X n → ℝ)
              + (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :=
            add_nonneg (Work.BoseKinLoc.Word.kinFormB_nonneg hℓ hdP hsP heT0P heT1P hbP Φ)
              (mul_nonneg (Nat.cast_nonneg n) (MeasureTheory.integral_nonneg fun x => sq_nonneg _))
          exact mul_le_mul hK10' hsum hsum0 hK100
      _ = K10 * (2 + kap) * μ * ℓ ^ 3 * pL := by ring
  -- ## 8. the fibre roots
  set Kg : ℝ := 3 * (L1Tails.chiGB * P / ℓ) ^ 2 with hKgdef
  set Kc : ℝ := P ^ 2 with hKcdef
  have hKg0 : 0 ≤ Kg := by rw [hKgdef]; exact mul_nonneg (by norm_num) (sq_nonneg _)
  have hKc0 : 0 ≤ Kc := by rw [hKcdef]; exact sq_nonneg _
  have hKg : ∀ w : ℝ³, ∑ j : Fin 3,
      ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg := by
    intro w; rw [hKgdef]; exact chiS_grad_bound ℓ hℓ w
  have hKc : ∀ w : ℝ³, ‖chiS ℓ w‖ ^ 2 ≤ Kc := by
    intro w; rw [hKcdef]; exact chiS_sq_bound ℓ w
  set Cwin : ℝ := max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 with hCwindef
  have hCwin0 : 0 ≤ Cwin := le_trans (by norm_num) (le_max_right _ _)
  obtain ⟨hPE13, hPE23, hPE21⟩ := fibreEnergyExp (l := ℓ) hℓ hKg0 hKc0 hKg hKc
  have hroot : ∀ p ∈ Submission.BoseGases.pairSet n,
      ((Real.sqrt (L1Tails.pairEnergy ℓ (pairG13 p Θ A A))
          + Real.sqrt (massBox ℓ (pairG13 p Θ A A)))
        + (Real.sqrt (L1Tails.pairEnergy ℓ (pairG21 p Θ A))
          + Real.sqrt (massBox ℓ (pairG21 p Θ A)))
        + (Real.sqrt (L1Tails.pairEnergy ℓ (pairG23 p Θ A A))
          + Real.sqrt (massBox ℓ (pairG23 p Θ A A))))
      ≤ 3 * (Real.sqrt Cwin + 1)
          * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
    intro p hp
    have hp' : p.1 ≠ p.2 := mem_pairSet_iff.mp hp
    obtain ⟨hCs13, hCs23, hCs21⟩ := pairG_supports (A := A) (B := A) p hp' hΘs
    have hΘm' : MeasureTheory.AEStronglyMeasurable Θ := hΘm.aestronglyMeasurable
    have hAm' : MeasureTheory.AEStronglyMeasurable A := hAm.aestronglyMeasurable
    -- fibres 13 and 23
    have hM13 : massBox ℓ (pairG13 p Θ A A) ≤ pL ^ 2 := by
      have h := pairG13_L2 p hp' hCs13 hΘm' hΘL hAm' hAL hAm' hAL
      rw [hA2, hnormB] at h
      change (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG13 p Θ A A w y‖ ^ 2) ≤ pL ^ 2
      simpa using h
    have hM23 : massBox ℓ (pairG23 p Θ A A) ≤ pL ^ 2 := by
      have h := pairG23_L2 p hp' hCs23 hΘm' hΘL hAm' hAL hAm' hAL
      rw [hA2, hnormB] at h
      change (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG23 p Θ A A w y‖ ^ 2) ≤ pL ^ 2
      simpa using h
    have hM21 : massBox ℓ (pairG21 p Θ A) ≤ pL ^ 2 := by
      have h := pairG21_L2 p hp' hCs21 hΘm' hΘL hAm' hAL
      rw [hA2, hnormB] at h
      change (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG21 p Θ A w y‖ ^ 2) ≤ pL ^ 2
      simpa using h
    have hsM13 : Real.sqrt (massBox ℓ (pairG13 p Θ A A)) ≤ pL := by
      calc Real.sqrt (massBox ℓ (pairG13 p Θ A A)) ≤ Real.sqrt (pL ^ 2) := Real.sqrt_le_sqrt hM13
        _ = pL := Real.sqrt_sq hpL
    have hsM23 : Real.sqrt (massBox ℓ (pairG23 p Θ A A)) ≤ pL := by
      calc Real.sqrt (massBox ℓ (pairG23 p Θ A A)) ≤ Real.sqrt (pL ^ 2) := Real.sqrt_le_sqrt hM23
        _ = pL := Real.sqrt_sq hpL
    have hsM21 : Real.sqrt (massBox ℓ (pairG21 p Θ A)) ≤ pL := by
      calc Real.sqrt (massBox ℓ (pairG21 p Θ A)) ≤ Real.sqrt (pL ^ 2) := Real.sqrt_le_sqrt hM21
        _ = pL := Real.sqrt_sq hpL
    -- the fibre Dirichlet energies
    have hE13 : L1Tails.pairEnergy ℓ (pairG13 p Θ A A)
        ≤ Cwin * (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
      have h := hPE13 p hp' hΘ₀ hΘind hAm hAm hAb' hAb' (norm_nonneg c) (norm_nonneg c)
      rw [hCwindef]
      calc L1Tails.pairEnergy ℓ (pairG13 p Θ A A)
          ≤ ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 * ‖c‖ ^ 2 * ‖c‖ ^ 2
              * Work.BoseBoxFock.pinL2 ℓ Θ₀
              * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + Work.BoseBoxFock.pinL2 ℓ Θ₀) := h
        _ = max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 * (ℓ ^ 6 * ‖c‖ ^ 2 * ‖c‖ ^ 2)
              * Work.BoseBoxFock.pinL2 ℓ Θ₀
              * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + Work.BoseBoxFock.pinL2 ℓ Θ₀) := by ring
        _ = max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2
              * (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
            rw [hcc, hL2p, mul_one]; ring
    have hE23 : L1Tails.pairEnergy ℓ (pairG23 p Θ A A)
        ≤ Cwin * (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
      have h := hPE23 p hp' hΘ₀ hΘind hAm hAm hAb' hAb' (norm_nonneg c) (norm_nonneg c)
      rw [hCwindef]
      calc L1Tails.pairEnergy ℓ (pairG23 p Θ A A)
          ≤ ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 * ‖c‖ ^ 2 * ‖c‖ ^ 2
              * Work.BoseBoxFock.pinL2 ℓ Θ₀
              * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + Work.BoseBoxFock.pinL2 ℓ Θ₀) := h
        _ = max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 * (ℓ ^ 6 * ‖c‖ ^ 2 * ‖c‖ ^ 2)
              * Work.BoseBoxFock.pinL2 ℓ Θ₀
              * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + Work.BoseBoxFock.pinL2 ℓ Θ₀) := by ring
        _ = max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2
              * (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
            rw [hcc, hL2p, mul_one]; ring
    have hE21 : L1Tails.pairEnergy ℓ (pairG21 p Θ A)
        ≤ Cwin * (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
      have h := hPE21 p hp' hΘ₀ hΘind hAm hAb' (norm_nonneg c)
      rw [hCwindef]
      calc L1Tails.pairEnergy ℓ (pairG21 p Θ A)
          ≤ ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 * ‖c‖ ^ 4
              * Work.BoseBoxFock.pinL2 ℓ Θ₀
              * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + Work.BoseBoxFock.pinL2 ℓ Θ₀) := h
        _ = max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 * (ℓ ^ 6 * ‖c‖ ^ 2 * ‖c‖ ^ 2)
              * Work.BoseBoxFock.pinL2 ℓ Θ₀
              * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + Work.BoseBoxFock.pinL2 ℓ Θ₀) := by ring
        _ = max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2
              * (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
            rw [hcc, hL2p, mul_one]; ring
    have hLL : pL ≤ Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
      calc pL = Real.sqrt (pL ^ 2) := (Real.sqrt_sq hpL).symm
        _ ≤ Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) :=
            Real.sqrt_le_sqrt (by nlinarith [hD0, hpL])
    have hsE13 : Real.sqrt (L1Tails.pairEnergy ℓ (pairG13 p Θ A A))
        ≤ Real.sqrt Cwin * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
      rw [← Real.sqrt_mul hCwin0 (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL))]
      exact Real.sqrt_le_sqrt hE13
    have hsE23 : Real.sqrt (L1Tails.pairEnergy ℓ (pairG23 p Θ A A))
        ≤ Real.sqrt Cwin * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
      rw [← Real.sqrt_mul hCwin0 (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL))]
      exact Real.sqrt_le_sqrt hE23
    have hsE21 : Real.sqrt (L1Tails.pairEnergy ℓ (pairG21 p Θ A))
        ≤ Real.sqrt Cwin * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
      rw [← Real.sqrt_mul hCwin0 (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL))]
      exact Real.sqrt_le_sqrt hE21
    set X : ℝ := Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) with hXdef
    have h13 : Real.sqrt (L1Tails.pairEnergy ℓ (pairG13 p Θ A A))
          + Real.sqrt (massBox ℓ (pairG13 p Θ A A)) ≤ (Real.sqrt Cwin + 1) * X := by
      rw [hXdef] at hsE13 ⊢
      linarith [hsE13, hsM13, hLL]
    have h23 : Real.sqrt (L1Tails.pairEnergy ℓ (pairG23 p Θ A A))
          + Real.sqrt (massBox ℓ (pairG23 p Θ A A)) ≤ (Real.sqrt Cwin + 1) * X := by
      rw [hXdef] at hsE23 ⊢
      linarith [hsE23, hsM23, hLL]
    have h21 : Real.sqrt (L1Tails.pairEnergy ℓ (pairG21 p Θ A))
          + Real.sqrt (massBox ℓ (pairG21 p Θ A)) ≤ (Real.sqrt Cwin + 1) * X := by
      rw [hXdef] at hsE21 ⊢
      linarith [hsE21, hsM21, hLL]
    rw [hXdef]
    linarith [h13, h23, h21]
  -- ## 9. the pair sum
  have hS : S ≤ 3 * (Real.sqrt Cwin + 1) * (n : ℝ) ^ 2
          * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
    rw [hSdef]
    have hX0 : 0 ≤ 3 * (Real.sqrt Cwin + 1)
        * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) :=
      mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (Real.sqrt_nonneg _) zero_le_one))
        (Real.sqrt_nonneg _)
    have h1 : (∑ p ∈ Submission.BoseGases.pairSet n,
          ((Real.sqrt (L1Tails.pairEnergy ℓ (pairG13 p Θ A A))
              + Real.sqrt (massBox ℓ (pairG13 p Θ A A)))
            + (Real.sqrt (L1Tails.pairEnergy ℓ (pairG21 p Θ A))
              + Real.sqrt (massBox ℓ (pairG21 p Θ A)))
            + (Real.sqrt (L1Tails.pairEnergy ℓ (pairG23 p Θ A A))
              + Real.sqrt (massBox ℓ (pairG23 p Θ A A)))))
        ≤ ((Submission.BoseGases.pairSet n).card : ℝ)
            * (3 * (Real.sqrt Cwin + 1)
              * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL))) := by
      have h := Finset.sum_le_sum (fun p hp => hroot p hp)
      rw [Finset.sum_const, nsmul_eq_mul] at h
      exact h
    have hcard : ((Submission.BoseGases.pairSet n).card : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hc : (Submission.BoseGases.pairSet n).card ≤ n ^ 2 := by
        calc (Submission.BoseGases.pairSet n).card
            ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = n ^ 2 := by simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, pow_two]
      exact_mod_cast hc
    calc (∑ p ∈ Submission.BoseGases.pairSet n, _)
        ≤ ((Submission.BoseGases.pairSet n).card : ℝ)
            * (3 * (Real.sqrt Cwin + 1)
              * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL))) := h1
      _ ≤ (n : ℝ) ^ 2 * (3 * (Real.sqrt Cwin + 1)
            * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL))) :=
          mul_le_mul_of_nonneg_right hcard hX0
      _ = 3 * (Real.sqrt Cwin + 1) * (n : ℝ) ^ 2
            * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by ring
  -- ## 10. the final monomial comparison
  have hCwinle : Cwin ≤ Cwin0 := by
    rw [hCwindef, hCwin0def]
    refine max_le_max ?_ le_rfl
    have hKg' : Kg ≤ 3 * (L1Tails.chiGB * P / a) ^ 2 := by
      rw [hKgdef]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine pow_le_pow_left₀ (div_nonneg (mul_nonneg hchiGB0 hP0) hℓpos.le) ?_ 2
      have h1 : ℓ⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 ha_le_ℓ
      calc L1Tails.chiGB * P / ℓ = (L1Tails.chiGB * P) * ℓ⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ (L1Tails.chiGB * P) * a⁻¹ := mul_le_mul_of_nonneg_left h1 (mul_nonneg hchiGB0 hP0)
        _ = L1Tails.chiGB * P / a := by rw [div_eq_mul_inv]
    have hKc' : (ℓ ^ 2)⁻¹ * Kc ≤ (a ^ 2)⁻¹ * P ^ 2 := by
      rw [hKcdef]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg P)
      exact inv_anti₀ (pow_pos ha0 2) (pow_le_pow_left₀ ha0.le ha_le_ℓ 2)
    have h2 : 2 * Kg ≤ 2 * (3 * (L1Tails.chiGB * P / a) ^ 2) := by linarith [hKg']
    rw [one_div]
    linarith [h2, hKc']
  have hCroot : 3 * (Real.sqrt Cwin + 1) ≤ Croot0 := by
    rw [hCroot0def]
    have h1 : Real.sqrt Cwin ≤ Real.sqrt Cwin0 := Real.sqrt_le_sqrt hCwinle
    calc 3 * (Real.sqrt Cwin + 1) = 3 * Real.sqrt Cwin + 3 := by ring
      _ ≤ 3 * Real.sqrt Cwin0 + 3 := by linarith [h1]
      _ = 3 * (Real.sqrt Cwin0 + 1) := by ring
  have hmu_rpow : μ ^ ((5 : ℝ) / 2) = μ ^ 2 * Real.sqrt μ := by
    have h1 : μ ^ ((5 : ℝ) / 2) = μ ^ (2 : ℝ) * μ ^ ((1 : ℝ) / 2) := by
      rw [show ((5 : ℝ) / 2) = 2 + 1 / 2 by norm_num, Real.rpow_add hμ]
    rw [h1]
    congr 1
    · exact Real.rpow_natCast μ 2
    · exact (Real.sqrt_eq_rpow μ).symm
  have hsqrt_muℓ : Real.sqrt (μ * ℓ ^ 3) = Real.sqrt μ * (ℓ * Real.sqrt ℓ) := by
    rw [show μ * ℓ ^ 3 = μ * (ℓ ^ 2 * ℓ) by ring, Real.sqrt_mul hμ.le,
      Real.sqrt_mul (pow_nonneg hℓpos.le 2), Real.sqrt_sq hℓpos.le]
  have hA0 : 0 ≤ 2 * K10 * (kap + 2) := by
    have hK4 : (4 : ℝ) ≤ K10 := by
      rw [hK10def]
      have h1 : 0 ≤ 16 * (1 / (2 * a ^ 2)) * P ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num)
          (div_nonneg zero_le_one (mul_nonneg (by norm_num) (sq_nonneg a)))) (sq_nonneg P)
      have h2 : 0 ≤ 24 * (L1Tails.chiGB * P / a) ^ 2 :=
        mul_nonneg (by norm_num) (sq_nonneg _)
      linarith
    have hka : (2 : ℝ) ≤ kap + 2 := by linarith [hkappos.le]
    exact mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) hK4))
      (by linarith [hkappos.le])
  have hB0 : 0 ≤ μ * ℓ ^ 3 := mul_nonneg hμ.le (pow_nonneg hℓpos.le 3)
  have haux : Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL))
      ≤ Real.sqrt (2 * K10 * (kap + 2)) * (Real.sqrt μ * (ℓ * Real.sqrt ℓ)) * pL := by
    have hDp : Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL
        ≤ 2 * K10 * (kap + 2) * μ * ℓ ^ 3 * pL := by
      have h2 : 1 ≤ K10 * (kap + 2) * μ * ℓ ^ 3 := by
        have hK4 : (4 : ℝ) ≤ K10 := by
          rw [hK10def]
          have h1 : 0 ≤ 16 * (1 / (2 * a ^ 2)) * P ^ 2 :=
            mul_nonneg (mul_nonneg (by norm_num)
              (div_nonneg zero_le_one (mul_nonneg (by norm_num) (sq_nonneg a)))) (sq_nonneg P)
          have h1' : 0 ≤ 24 * (L1Tails.chiGB * P / a) ^ 2 :=
            mul_nonneg (by norm_num) (sq_nonneg _)
          linarith
        have hka : (2 : ℝ) ≤ kap + 2 := by linarith [hkappos.le]
        have hs1 : (4 : ℝ) * 2 ≤ K10 * (kap + 2) :=
          mul_le_mul hK4 hka (by norm_num) (by linarith)
        have hs2 : (4 : ℝ) * 2 * 1 ≤ K10 * (kap + 2) * (μ * ℓ ^ 3) :=
          mul_le_mul hs1 hμℓ3 (by norm_num) (by linarith)
        linarith [hs2]
      have h3 : pL ≤ K10 * (kap + 2) * μ * ℓ ^ 3 * pL := by
        calc pL = 1 * pL := by ring
          _ ≤ (K10 * (kap + 2) * μ * ℓ ^ 3) * pL := mul_le_mul_of_nonneg_right h2 hpL
          _ = K10 * (kap + 2) * μ * ℓ ^ 3 * pL := by ring
      linarith [hDbound, h3]
    calc Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL))
        ≤ Real.sqrt ((2 * K10 * (kap + 2) * (μ * ℓ ^ 3)) * (pL ^ 2)) := by
          refine Real.sqrt_le_sqrt ?_
          rw [show (2 * K10 * (kap + 2) * (μ * ℓ ^ 3)) * pL ^ 2
              = pL * (2 * K10 * (kap + 2) * μ * ℓ ^ 3 * pL) by ring]
          exact mul_le_mul_of_nonneg_left hDp hpL
      _ = Real.sqrt (2 * K10 * (kap + 2) * (μ * ℓ ^ 3)) * pL := by
          rw [Real.sqrt_mul (mul_nonneg hA0 hB0), Real.sqrt_sq hpL]
      _ = Real.sqrt (2 * K10 * (kap + 2)) * Real.sqrt (μ * ℓ ^ 3) * pL := by
          rw [Real.sqrt_mul hA0]
      _ = Real.sqrt (2 * K10 * (kap + 2)) * (Real.sqrt μ * (ℓ * Real.sqrt ℓ)) * pL := by
          rw [hsqrt_muℓ]
  have hε2 : 2 * (ℓ ^ 3)⁻¹ * εimg * Croot0 * 4 * μ ^ 2 * ℓ ^ 6
        * Real.sqrt (2 * K10 * (kap + 2)) * (Real.sqrt μ * (ℓ * Real.sqrt ℓ)) * pL
      = Ccoef * (μ ^ 2 * Real.sqrt μ) * pL := by
    rw [hεimgdef, hCcoefdef, div_pow]
    have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
    have hℓ60 : ℓ ^ 6 ≠ 0 := pow_ne_zero 6 hℓ0
    have hsℓ0 : Real.sqrt ℓ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hℓpos)
    field_simp
    ring_nf
    rw [Real.sq_sqrt hℓpos.le]
    ring
  have hpow_main : 2 * (ℓ ^ 3)⁻¹ * εimg * (3 * (Real.sqrt Cwin + 1)) * (n : ℝ) ^ 2
      * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL))
      ≤ Ccoef * μ ^ ((5 : ℝ) / 2) * pL := by
    have hE0 : 0 ≤ εimg := hεimg0
    have hi0 : 0 ≤ (ℓ ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg hℓpos.le 3)
    have hB : 0 ≤ 2 * (ℓ ^ 3)⁻¹ * εimg :=
      mul_nonneg (mul_nonneg (by norm_num) hi0) hE0
    have hBc : 0 ≤ 2 * (ℓ ^ 3)⁻¹ * εimg * Croot0 := mul_nonneg hB hCroot00
    have hX0 : 0 ≤ Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := Real.sqrt_nonneg _
    have hXp0 : 0 ≤ Real.sqrt (2 * K10 * (kap + 2)) * (Real.sqrt μ * (ℓ * Real.sqrt ℓ)) * pL :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg hℓpos.le (Real.sqrt_nonneg _)))) hpL
    have hn2 : (n : ℝ) ^ 2 ≤ 4 * μ ^ 2 * ℓ ^ 6 := by
      calc (n : ℝ) ^ 2 ≤ (2 * μ * ℓ ^ 3) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 2
        _ = 4 * μ ^ 2 * ℓ ^ 6 := by ring
    calc 2 * (ℓ ^ 3)⁻¹ * εimg * (3 * (Real.sqrt Cwin + 1)) * (n : ℝ) ^ 2
          * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL))
        = (2 * (ℓ ^ 3)⁻¹ * εimg * (3 * (Real.sqrt Cwin + 1))) * (n : ℝ) ^ 2
            * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by ring
      _ ≤ (2 * (ℓ ^ 3)⁻¹ * εimg * Croot0) * (n : ℝ) ^ 2
            * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCroot hB) (sq_nonneg _)) hX0
      _ = 2 * (ℓ ^ 3)⁻¹ * εimg * Croot0 * (n : ℝ) ^ 2
            * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by ring
      _ ≤ 2 * (ℓ ^ 3)⁻¹ * εimg * Croot0 * (4 * μ ^ 2 * ℓ ^ 6)
            * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn2 hBc) hX0
      _ ≤ 2 * (ℓ ^ 3)⁻¹ * εimg * Croot0 * (4 * μ ^ 2 * ℓ ^ 6)
            * (Real.sqrt (2 * K10 * (kap + 2)) * (Real.sqrt μ * (ℓ * Real.sqrt ℓ)) * pL) := by
          refine mul_le_mul_of_nonneg_left haux ?_
          refine mul_nonneg hBc ?_
          exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg μ)) (pow_nonneg hℓpos.le 6)
      _ = 2 * (ℓ ^ 3)⁻¹ * εimg * Croot0 * 4 * μ ^ 2 * ℓ ^ 6
            * Real.sqrt (2 * K10 * (kap + 2)) * (Real.sqrt μ * (ℓ * Real.sqrt ℓ)) * pL := by ring
      _ = Ccoef * (μ ^ 2 * Real.sqrt μ) * pL := hε2
      _ = Ccoef * μ ^ ((5 : ℝ) / 2) * pL := by rw [hmu_rpow]
  -- ## 11. the final assembly
  have hi0 : 0 ≤ (ℓ ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg hℓpos.le 3)
  have habs : |(ℓ ^ 3)⁻¹| = (ℓ ^ 3)⁻¹ := abs_of_nonneg hi0
  rw [habs] at hstrip
  refine hstrip.trans ?_
  refine stripImages_arith (v := v) (R := R) (μ := μ) (Ccoef := Ccoef) hav hR hμ ht1
    hCcoef0 hpL ?_
  calc 2 * (ℓ ^ 3)⁻¹ * εimg * S
      ≤ 2 * (ℓ ^ 3)⁻¹ * εimg * (3 * (Real.sqrt Cwin + 1) * (n : ℝ) ^ 2
          * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL))) :=
        mul_le_mul_of_nonneg_left hS
          (mul_nonneg (mul_nonneg (by norm_num) hi0) hεimg0)
    _ = 2 * (ℓ ^ 3)⁻¹ * εimg * (3 * (Real.sqrt Cwin + 1)) * (n : ℝ) ^ 2
          * Real.sqrt (pL * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + pL)) := by ring
    _ ≤ Ccoef * μ ^ ((5 : ℝ) / 2) * pL := hpow_main



end Work.BoseBoxFock
