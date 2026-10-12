import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BSKinetic.Decomp.continuous_bsPsi
import Submission.Work.BoseFixB1.RegimeAux
import Submission.Work.BoseFixB1S.corrAuxKin
import Submission.Work.OneBodyKin.ProfHatDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.corrCutWordsSharp` — the sharp correlation-word bound

The one-body window `χ_{B(u)}` (the corpus `chiB ℓ d u`, `ℓ = sideAt μ (a v)`, `d = (paramsAt μ
(a v)).d`) has a `p`-space form with the **sharp** small-box scaling:
both `∫_p [‖p‖−(dsℓ)^{-1}]₊² ‖𝓕χ_{B(u)}‖²` and its `[·]₊⁴`-analogue are `≤ C ℓ^{-2}`, uniformly in
the shift `u` and in the admissible chemical potential `μ`.  This is the quantitative form of "the
window is smooth on its own scale `ℓd`, so its transform is concentrated at `‖p‖ ≲ (ℓd)^{-1}`, and
`(ℓd)^{-1} ≤ (dsℓ)^{-1}`-far momenta are strongly suppressed".

The proof is the `N = 265`-fold integration by parts of `corrAuxKin`: the decay
`‖p‖^265‖𝓕χ_{B(u)}(p)‖ ≤ (2π)^265 C_{265} ℓ³ ((ℓd)^265)^{-1}` turns both integrals into the closed
exterior integrals `∫_{‖p‖>c}‖p‖^{-n} = 4π/(n-3)c^{3-n}` (`n = 528, 526`), and the parameter
comparison is the `fsXp` bookkeeping of `Work.BoseFixB1.RegimeAux`
(`ℓ = a X^{-163}`, `d = X⁶`, `s = X`).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Real BigOperators

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-! ## 0. The parameter arithmetic (`N = 265` bookkeeping) -/

/-- `ℓ³ d^{-5} s^{525} ≤ a³`: the `ℓ³`-form of the sharp comparison, from `ℓ = aX^{-163}`,
`d = X⁶`, `s = X`, i.e. `ℓ³d^{-5}s^{525} = a³X⁶ = a³d ≤ a³`. -/
private lemma corrSharp_param_le_one {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (ht1 : μ * A^3 ≤ 1) :
    Work.BoseBox.sideAt μ A * (((Work.BoseBox.paramsAt μ A).d) ^ 5)⁻¹
        * ((Work.BoseBox.paramsAt μ A).s) ^ 525
      ≤ A^3 * ((Work.BoseBox.sideAt μ A)⁻¹)^2 := by
  have ht : 0 < μ * A^3 := by positivity
  have hℓf : Work.BoseBox.sideAt μ A = A * Work.BoseBox.fsXp (μ*A^3) (-163) :=
    Work.BoseFixB1.sideAt_eq_fsXp hA hμ
  have hd5 : (((Work.BoseBox.paramsAt μ A).d) ^ 5)⁻¹ = Work.BoseBox.fsXp (μ*A^3) (-30) := by
    rw [Work.BoseFixB1.d_eq_fsXp, Work.BoseBox.fsXp_pow ht.le,
      show (6:ℝ) * (5:ℕ) = 30 by norm_num, Work.BoseBox.fsXp_inv ht]
  have hs525 : ((Work.BoseBox.paramsAt μ A).s) ^ 525 = Work.BoseBox.fsXp (μ*A^3) 525 := by
    rw [show (Work.BoseBox.paramsAt μ A).s = Work.BoseBox.fsXp (μ*A^3) 1 from rfl,
      Work.BoseBox.fsXp_pow ht.le, show (1:ℝ) * (525:ℕ) = 525 by norm_num]
  have hX : Work.BoseBox.fsXp (μ*A^3) (-163) * Work.BoseBox.fsXp (μ*A^3) (-30)
      * Work.BoseBox.fsXp (μ*A^3) 525 = Work.BoseBox.fsXp (μ*A^3) 332 := by
    rw [Work.BoseBox.fsXp_mul ht, Work.BoseBox.fsXp_mul ht]; norm_num
  have hXinv : ((Work.BoseBox.fsXp (μ*A^3) (-163))⁻¹)^2 = Work.BoseBox.fsXp (μ*A^3) 326 := by
    rw [inv_pow]
    have h1 : (Work.BoseBox.fsXp (μ*A^3) (-163))^2 = Work.BoseBox.fsXp (μ*A^3) (-326) := by
      rw [Work.BoseBox.fsXp_pow ht.le]; norm_num
    rw [h1, Work.BoseBox.fsXp_inv ht]; norm_num
  rw [hℓf, hd5, hs525]
  have hd1 : Work.BoseBox.fsXp (μ*A^3) 6 ≤ 1 := Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)
  calc A * Work.BoseBox.fsXp (μ*A^3) (-163) * Work.BoseBox.fsXp (μ*A^3) (-30)
        * Work.BoseBox.fsXp (μ*A^3) 525
      = A * Work.BoseBox.fsXp (μ*A^3) 332 := by rw [← hX]; ring
    _ = A * (Work.BoseBox.fsXp (μ*A^3) 326 * Work.BoseBox.fsXp (μ*A^3) 6) := by
        rw [show (332:ℝ) = 326 + 6 by norm_num, ← Work.BoseBox.fsXp_mul ht]
    _ ≤ A * (Work.BoseBox.fsXp (μ*A^3) 326 * 1) := by
        apply mul_le_mul_of_nonneg_left _ hA.le
        exact mul_le_mul_of_nonneg_left hd1 (Work.BoseBox.fsXp_nonneg ht.le)
    _ = A^3 * ((A * Work.BoseBox.fsXp (μ*A^3) (-163))⁻¹)^2 := by
        rw [mul_inv, mul_pow, hXinv]
        field_simp

/-- `ℓ d^{-7} s^{523} ≤ a`: `ℓ d^{-7} s^{523} = a X^{318} ≤ a`. -/
private lemma corrSharp_param_le_two {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (ht1 : μ * A^3 ≤ 1) :
    Work.BoseBox.sideAt μ A * (((Work.BoseBox.paramsAt μ A).d) ^ 7)⁻¹
        * ((Work.BoseBox.paramsAt μ A).s) ^ 523
      ≤ A := by
  have ht : 0 < μ * A^3 := by positivity
  have hℓf : Work.BoseBox.sideAt μ A = A * Work.BoseBox.fsXp (μ*A^3) (-163) :=
    Work.BoseFixB1.sideAt_eq_fsXp hA hμ
  have hd7 : (((Work.BoseBox.paramsAt μ A).d) ^ 7)⁻¹ = Work.BoseBox.fsXp (μ*A^3) (-42) := by
    rw [Work.BoseFixB1.d_eq_fsXp, Work.BoseBox.fsXp_pow ht.le,
      show (6:ℝ) * (7:ℕ) = 42 by norm_num, Work.BoseBox.fsXp_inv ht]
  have hs523 : ((Work.BoseBox.paramsAt μ A).s) ^ 523 = Work.BoseBox.fsXp (μ*A^3) 523 := by
    rw [show (Work.BoseBox.paramsAt μ A).s = Work.BoseBox.fsXp (μ*A^3) 1 from rfl,
      Work.BoseBox.fsXp_pow ht.le, show (1:ℝ) * (523:ℕ) = 523 by norm_num]
  have hX : Work.BoseBox.fsXp (μ*A^3) (-163) * Work.BoseBox.fsXp (μ*A^3) (-42)
      * Work.BoseBox.fsXp (μ*A^3) 523 = Work.BoseBox.fsXp (μ*A^3) 318 := by
    rw [Work.BoseBox.fsXp_mul ht, Work.BoseBox.fsXp_mul ht]; norm_num
  rw [hℓf, hd7, hs523]
  calc A * Work.BoseBox.fsXp (μ*A^3) (-163) * Work.BoseBox.fsXp (μ*A^3) (-42)
        * Work.BoseBox.fsXp (μ*A^3) 523
      = A * Work.BoseBox.fsXp (μ*A^3) 318 := by rw [← hX]; ring
    _ ≤ A * 1 := by
        apply mul_le_mul_of_nonneg_left _ hA.le
        exact Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)
    _ = A := by ring

/-- The expansion of the squared decay constant times the exterior integral weight. -/
private lemma corrSharp_A2_sq_one {ℓ d s CB : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) :
    ((2 * Real.pi)^265 * CB * (ℓ^3 * ((ℓ*d)^265)⁻¹))^2 * ((d*s*ℓ)⁻¹)^((-525:ℝ))
      = (2 * Real.pi)^(2*265) * CB^2 * (ℓ * (d^5)⁻¹ * s^525) := by
  rw [Real.inv_rpow (le_of_lt (by positivity : (0:ℝ) < d*s*ℓ))]
  norm_num
  field_simp

/-- The expansion of the squared decay constant times the exterior integral weight (quartic). -/
private lemma corrSharp_A2_sq_two {ℓ d s CB : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) :
    ((2 * Real.pi)^265 * CB * (ℓ^3 * ((ℓ*d)^265)⁻¹))^2 * ((d*s*ℓ)⁻¹)^((-523:ℝ))
      = (2 * Real.pi)^(2*265) * CB^2 * (ℓ⁻¹ * (d^7)⁻¹ * s^523) := by
  rw [Real.inv_rpow (le_of_lt (by positivity : (0:ℝ) < d*s*ℓ))]
  norm_num
  field_simp

/-! ## 1. The target -/

/-- The `‖p‖^2`-algebra of the quartic small-`p` bound. -/
private lemma corrSharp_sq_alg (r A₂ : ℝ) (hr : 0 < r) :
    r^2 * (A₂ * (r^265)⁻¹)^2 = A₂^2 * (r^528)⁻¹ := by
  rw [mul_pow, inv_pow, ← pow_mul]
  field_simp
  ring

/-- The `‖p‖^4`-algebra of the quartic small-`p` bound. -/
private lemma corrSharp_qu_alg (r A₂ : ℝ) (hr : 0 < r) :
    (r^2)^2 * (A₂ * (r^265)⁻¹)^2 = A₂^2 * (r^526)⁻¹ := by
  rw [mul_pow, inv_pow, ← pow_mul]
  field_simp
  ring

/-! ## 1. The target -/

theorem corrCutWordsSharp {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : EuclideanSpace ℝ (Fin 3),
        MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖) ^ 2 *
              ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z) p‖ ^ 2)
        ∧ (Work.BSKinetic.Decomp.bsW
              (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
              (fun z : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z)
            ≤ C * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
        ∧ (∫ p : EuclideanSpace ℝ (Fin 3),
              (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖) ^ 2 *
                ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
                  Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z) p‖ ^ 2)
            ≤ C * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2 := by
  obtain ⟨CB, hCB0, hCB⟩ := exists_iteratedFDeriv_chiB_L1_le
  have hCBnn : (0:ℝ) ≤ CB 265 := hCB0 265
  have h2πpos : (0:ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h2πnn : (0:ℝ) ≤ 2 * Real.pi := h2πpos.le
  have hF525 : (0:ℝ) ≤ 4 * Real.pi / 525 := by positivity
  have hF523 : (0:ℝ) ≤ 4 * Real.pi / 523 := by positivity
  refine ⟨(2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525) * |BoseGases.a v|^3
      + (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523) * |BoseGases.a v| + 1,
    ?_, 1, one_pos, ?_⟩
  · have h1 : (0:ℝ) ≤ (2 * Real.pi)^(2*265) := pow_nonneg h2πnn _
    have h2 : (0:ℝ) ≤ (CB 265)^2 := sq_nonneg _
    have h3 : (0:ℝ) ≤ |BoseGases.a v|^3 := pow_nonneg (abs_nonneg _) 3
    have h4 : (0:ℝ) ≤ |BoseGases.a v| := abs_nonneg _
    have hT1 : (0:ℝ) ≤ (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525)
        * |BoseGases.a v|^3 := mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hF525) h3
    have hT2 : (0:ℝ) ≤ (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523)
        * |BoseGases.a v| := mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hF523) h4
    linarith
  · intro μ hAdm u
    have hμpos : 0 < μ := hAdm.1
    have htle : μ * (BoseGases.a v)^3 ≤ 1 := hAdm.2.1
    have ha : 0 < BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
    set ℓ : ℝ := Work.BoseBox.sideAt μ (BoseGases.a v) with hℓdef
    set d : ℝ := (Work.BoseBox.paramsAt μ (BoseGases.a v)).d with hddef
    set s : ℝ := (Work.BoseBox.paramsAt μ (BoseGases.a v)).s with hsdef
    set c : ℝ := Work.BoseFixB1.sbCut μ (BoseGases.a v) with hcdef
    have hℓ : 0 < ℓ := Work.BoseFixB1.adm_ell_pos hAdm
    have hd : 0 < d := Work.BoseFixB1.adm_d_pos hAdm
    have hs : 0 < s := Work.BoseFixB1.adm_s_pos hAdm
    have ht1 : μ * (BoseGases.a v)^3 ≤ 1 := htle
    have hd1 : d ≤ 1 := by
      rw [hddef, Work.BoseFixB1.d_eq_fsXp]
      exact Work.BoseBox.fsXp_le_one (by positivity) ht1 (by norm_num)
    have hcpos : 0 < c := by
      rw [hcdef]
      show 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹
      exact inv_pos.mpr (by positivity)
    -- ## the state and the decay of its transform
    have hcdtop : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : E3 => (Submission.BoseGases.chiB ℓ d u z : ℂ)) :=
      (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).continuousLinearMap_comp Complex.ofRealCLM
    have hcs : HasCompactSupport (fun z : E3 => (Submission.BoseGases.chiB ℓ d u z : ℂ)) :=
      (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u).comp_left
        (g := fun x : ℝ => (x : ℂ)) (by norm_num)
    have hcd265 : ContDiff ℝ 265 (fun z : E3 => (Submission.BoseGases.chiB ℓ d u z : ℂ)) :=
      hcdtop.of_le (WithTop.coe_le_coe.mpr le_top)
    have hint : ∀ k : ℕ, k ≤ 265 →
        Integrable (iteratedFDeriv ℝ k (fun z : E3 => (Submission.BoseGases.chiB ℓ d u z : ℂ))) :=
      fun k _ => integrable_iteratedFDeriv_of_contDiff hcdtop hcs k
    set A₂ : ℝ := (2 * Real.pi)^265 * CB 265 * (ℓ^3 * ((ℓ*d)^265)⁻¹) with hA₂def
    have hA₂nn : 0 ≤ A₂ := by
      rw [hA₂def]
      exact mul_nonneg (mul_nonneg (pow_nonneg h2πnn 265) hCBnn)
        (mul_nonneg (pow_nonneg hℓ.le 3)
          (inv_nonneg.mpr (pow_nonneg (mul_nonneg hℓ.le hd.le) 265)))
    have hdec : ∀ p : E3,
        ‖p‖^265 * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖
          ≤ A₂ := by
      intro p
      have hpsi : Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p
          = Submission.BoseGases.kinFT
              (fun z : E3 => (Submission.BoseGases.chiB ℓ d u z : ℂ)) p := rfl
      rw [hpsi, hA₂def]
      calc ‖p‖^265 * ‖Submission.BoseGases.kinFT
              (fun z : E3 => (Submission.BoseGases.chiB ℓ d u z : ℂ)) p‖
          ≤ (2 * Real.pi)^265 *
              ∫ z, ‖iteratedFDeriv ℝ 265
                (fun z : E3 => (Submission.BoseGases.chiB ℓ d u z : ℂ)) z‖ :=
            norm_kinFT_mul_norm_pow_le 265 hcd265 hint p
        _ ≤ (2 * Real.pi)^265 * (CB 265 * (ℓ^3 * ((ℓ*d)^265)⁻¹)) :=
            mul_le_mul_of_nonneg_left (hCB 265 ℓ d hℓ hd hd1 u) (pow_nonneg h2πnn 265)
        _ = (2 * Real.pi)^265 * CB 265 * (ℓ^3 * ((ℓ*d)^265)⁻¹) := by ring
    have hpt : ∀ p : E3, c < ‖p‖ →
        ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖
          ≤ A₂ * ((‖p‖ : ℝ)^265)⁻¹ := by
      intro p hp
      have hp0 : 0 < ‖p‖ := lt_trans hcpos hp
      have hpos : 0 < ‖p‖^265 := pow_pos hp0 265
      rw [le_mul_inv_iff₀ hpos]
      calc ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖
            * ‖p‖^265
          = ‖p‖^265 * ‖Work.BSKinetic.Decomp.bsPsi
              (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖ := by ring
        _ ≤ A₂ := hdec p
    -- ## the two tail bounds
    have hF_le : ∀ r : ℝ, 0 ≤ r → Submission.BoseGases.fsKinCoeff c r ≤ r^2 := by
      intro r hr
      have h1 : max (r - c) 0 ≤ r := max_le (by linarith [hcpos.le]) hr
      have h2 : 0 ≤ max (r - c) 0 := le_max_right _ _
      show (max (r - c) 0)^2 ≤ r^2
      exact pow_le_pow_left₀ h2 h1 2
    have hbd1 : ∀ p : E3, c < ‖p‖ →
        Submission.BoseGases.fsKinCoeff c ‖p‖
            * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2
          ≤ A₂^2 * ((‖p‖ : ℝ)^528)⁻¹ := by
      intro p hp
      have hp0 : 0 < ‖p‖ := lt_trans hcpos hp
      have hF := hF_le ‖p‖ hp0.le
      have hψ := hpt p hp
      have hsq : (Submission.BoseGases.fsKinCoeff c ‖p‖)
          * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2
          ≤ ‖p‖^2 * (A₂ * ((‖p‖ : ℝ)^265)⁻¹)^2 := by
        refine mul_le_mul hF (pow_le_pow_left₀ (norm_nonneg _) hψ 2) (sq_nonneg _) ?_
        exact pow_nonneg hp0.le 2
      rw [corrSharp_sq_alg ‖p‖ A₂ hp0] at hsq
      exact hsq
    have hbd2 : ∀ p : E3, c < ‖p‖ →
        (Submission.BoseGases.fsKinCoeff c ‖p‖)^2
            * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2
          ≤ A₂^2 * ((‖p‖ : ℝ)^526)⁻¹ := by
      intro p hp
      have hp0 : 0 < ‖p‖ := lt_trans hcpos hp
      have hF := hF_le ‖p‖ hp0.le
      have hψ := hpt p hp
      have hsq : (Submission.BoseGases.fsKinCoeff c ‖p‖)^2
          * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2
          ≤ (‖p‖^2)^2 * (A₂ * ((‖p‖ : ℝ)^265)⁻¹)^2 := by
        refine mul_le_mul (pow_le_pow_left₀ (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) hF 2)
          (pow_le_pow_left₀ (norm_nonneg _) hψ 2) (sq_nonneg _) ?_
        exact pow_nonneg (pow_nonneg hp0.le 2) 2
      rw [corrSharp_qu_alg ‖p‖ A₂ hp0] at hsq
      exact hsq
    have hzero1 : ∀ p : E3, ¬ (c < ‖p‖) →
        Submission.BoseGases.fsKinCoeff c ‖p‖
            * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2
          = 0 := by
      intro p hp
      rw [Submission.BoseGases.fsKinCoeff_of_le (not_lt.mp hp), zero_mul]
    have hzero2 : ∀ p : E3, ¬ (c < ‖p‖) →
        (Submission.BoseGases.fsKinCoeff c ‖p‖)^2
            * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2
          = 0 := by
      intro p hp
      rw [Submission.BoseGases.fsKinCoeff_of_le (not_lt.mp hp), zero_pow (by norm_num), zero_mul]
    have hnonneg1 : ∀ p : E3, 0 ≤ Submission.BoseGases.fsKinCoeff c ‖p‖
        * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2 := by
      intro p
      exact mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _)
    have hnonneg2 : ∀ p : E3, 0 ≤ (Submission.BoseGases.fsKinCoeff c ‖p‖)^2
        * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2 := by
      intro p
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hψc : Continuous (fun p : E3 =>
        Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p) :=
      Work.BSKinetic.Decomp.continuous_bsPsi (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u)
        (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u)
    have hFc : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
      unfold Submission.BoseGases.fsKinCoeff
      fun_prop
    have hmeas1 : AEStronglyMeasurable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖
        * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2)
        volume := (hFc.mul (hψc.norm.pow 2)).aestronglyMeasurable
    have hmeas2 : AEStronglyMeasurable (fun p : E3 => (Submission.BoseGases.fsKinCoeff c ‖p‖)^2
        * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2)
        volume := ((hFc.pow 2).mul (hψc.norm.pow 2)).aestronglyMeasurable
    have hint1 : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖
        * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2) :=
      integrable_of_tail_bound hcpos (sq_nonneg A₂) 528 (by norm_num) hbd1 hzero1 hnonneg1 hmeas1
    have hint2 : Integrable (fun p : E3 => (Submission.BoseGases.fsKinCoeff c ‖p‖)^2
        * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2) :=
      integrable_of_tail_bound hcpos (sq_nonneg A₂) 526 (by norm_num) hbd2 hzero2 hnonneg2 hmeas2
    have hbdint1 : ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖
        * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2
        ≤ A₂^2 * (4*Real.pi/((528:ℝ) - 3) * c^((3:ℝ) - (528:ℝ))) :=
      integral_le_tail_bound hcpos (sq_nonneg A₂) 528 (by norm_num) hbd1 hzero1 hnonneg1
    have hbdint2 : ∫ p : E3, (Submission.BoseGases.fsKinCoeff c ‖p‖)^2
        * ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2
        ≤ A₂^2 * (4*Real.pi/((526:ℝ) - 3) * c^((3:ℝ) - (526:ℝ))) :=
      integral_le_tail_bound hcpos (sq_nonneg A₂) 526 (by norm_num) hbd2 hzero2 hnonneg2
    -- ## the parameter comparison
    have hparam1 : ℓ * (d^5)⁻¹ * s^525 ≤ (BoseGases.a v)^3 * (ℓ⁻¹)^2 := by
      rw [hℓdef, hddef, hsdef]
      exact corrSharp_param_le_one ha hμpos ht1
    have hparam2 : ℓ * (d^7)⁻¹ * s^523 ≤ BoseGases.a v := by
      rw [hℓdef, hddef, hsdef]
      exact corrSharp_param_le_two ha hμpos ht1
    have heq1 : A₂^2 * c^((3:ℝ) - (528:ℝ))
        = (2 * Real.pi)^(2*265) * (CB 265)^2 * (ℓ * (d^5)⁻¹ * s^525) := by
      rw [show (3:ℝ) - (528:ℝ) = -525 by norm_num]
      rw [hA₂def, hcdef]
      exact corrSharp_A2_sq_one hℓ hd hs
    have heq2 : A₂^2 * c^((3:ℝ) - (526:ℝ))
        = (2 * Real.pi)^(2*265) * (CB 265)^2 * (ℓ⁻¹ * (d^7)⁻¹ * s^523) := by
      rw [show (3:ℝ) - (526:ℝ) = -523 by norm_num]
      rw [hA₂def, hcdef]
      exact corrSharp_A2_sq_two hℓ hd hs
    have h1nn : (0:ℝ) ≤ (2 * Real.pi)^(2*265) := pow_nonneg h2πnn _
    have h2nn : (0:ℝ) ≤ (CB 265)^2 := sq_nonneg _
    have h3nn : (0:ℝ) ≤ |BoseGases.a v|^3 := pow_nonneg (abs_nonneg _) 3
    have h4nn : (0:ℝ) ≤ |BoseGases.a v| := abs_nonneg _
    have hT1 : (0:ℝ) ≤ (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525)
        * |BoseGases.a v|^3 := mul_nonneg (mul_nonneg (mul_nonneg h1nn h2nn) hF525) h3nn
    have hT2 : (0:ℝ) ≤ (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523)
        * |BoseGases.a v| := mul_nonneg (mul_nonneg (mul_nonneg h1nn h2nn) hF523) h4nn
    have hC1 : (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525) * |BoseGases.a v|^3
        ≤ (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525) * |BoseGases.a v|^3
          + (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523) * |BoseGases.a v| + 1 := by
      linarith [hT2]
    have hC2 : (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523) * |BoseGases.a v|
        ≤ (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525) * |BoseGases.a v|^3
          + (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523) * |BoseGases.a v| + 1 := by
      linarith [hT1]
    have hKV1 : (0:ℝ) ≤ 4*Real.pi/525 * ((2 * Real.pi)^(2*265) * (CB 265)^2) :=
      mul_nonneg hF525 (mul_nonneg h1nn h2nn)
    have hKV2 : (0:ℝ) ≤ 4*Real.pi/523 * ((2 * Real.pi)^(2*265) * (CB 265)^2) :=
      mul_nonneg hF523 (mul_nonneg h1nn h2nn)
    have hfin1 : A₂^2 * (4*Real.pi/((528:ℝ) - 3) * c^((3:ℝ) - (528:ℝ)))
        ≤ ((2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525) * |BoseGases.a v|^3
            + (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523) * |BoseGases.a v| + 1)
          * (ℓ⁻¹)^2 := by
      have hstep : A₂^2 * (4*Real.pi/525 * c^((3:ℝ) - (528:ℝ)))
          ≤ (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525) * (BoseGases.a v)^3
            * (ℓ⁻¹)^2 := by
        rw [show A₂^2 * (4*Real.pi/525 * c^((3:ℝ) - (528:ℝ)))
            = 4*Real.pi/525 * (A₂^2 * c^((3:ℝ) - (528:ℝ))) by ring, heq1]
        calc 4*Real.pi/525 * ((2 * Real.pi)^(2*265) * (CB 265)^2 * (ℓ * (d^5)⁻¹ * s^525))
            ≤ 4*Real.pi/525 * ((2 * Real.pi)^(2*265) * (CB 265)^2
                * ((BoseGases.a v)^3 * (ℓ⁻¹)^2)) := by
              apply mul_le_mul_of_nonneg_left _ hF525
              exact mul_le_mul_of_nonneg_left hparam1 (mul_nonneg h1nn h2nn)
          _ = (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525) * (BoseGases.a v)^3
                * (ℓ⁻¹)^2 := by ring
      rw [show ((528:ℝ) - 3) = 525 by norm_num]
      refine hstep.trans ?_
      calc (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525) * (BoseGases.a v)^3 * (ℓ⁻¹)^2
          ≤ (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525) * |BoseGases.a v|^3
              * (ℓ⁻¹)^2 := by
            have habs : |BoseGases.a v|^3 = (BoseGases.a v)^3 := by rw [abs_of_pos ha]
            rw [habs]
        _ ≤ ((2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525) * |BoseGases.a v|^3
              + (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523) * |BoseGases.a v| + 1)
              * (ℓ⁻¹)^2 := by
            exact mul_le_mul_of_nonneg_right hC1 (sq_nonneg _)
    have hfin2 : A₂^2 * (4*Real.pi/((526:ℝ) - 3) * c^((3:ℝ) - (526:ℝ)))
        ≤ ((2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525) * |BoseGases.a v|^3
            + (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523) * |BoseGases.a v| + 1)
          * (ℓ⁻¹)^2 := by
      have hstep : A₂^2 * (4*Real.pi/523 * c^((3:ℝ) - (526:ℝ)))
          ≤ (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523) * (BoseGases.a v)
            * (ℓ⁻¹)^2 := by
        rw [show A₂^2 * (4*Real.pi/523 * c^((3:ℝ) - (526:ℝ)))
            = 4*Real.pi/523 * (A₂^2 * c^((3:ℝ) - (526:ℝ))) by ring, heq2]
        calc 4*Real.pi/523 * ((2 * Real.pi)^(2*265) * (CB 265)^2 * (ℓ⁻¹ * (d^7)⁻¹ * s^523))
            ≤ 4*Real.pi/523 * ((2 * Real.pi)^(2*265) * (CB 265)^2
                * (BoseGases.a v * (ℓ⁻¹)^2)) := by
              apply mul_le_mul_of_nonneg_left _ hF523
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg h1nn h2nn)
              calc ℓ⁻¹ * (d^7)⁻¹ * s^523 = (ℓ * (d^7)⁻¹ * s^523) * (ℓ⁻¹)^2 := by
                    field_simp
                  _ ≤ BoseGases.a v * (ℓ⁻¹)^2 :=
                    mul_le_mul_of_nonneg_right hparam2 (sq_nonneg _)
          _ = (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523) * (BoseGases.a v)
                * (ℓ⁻¹)^2 := by ring
      rw [show ((526:ℝ) - 3) = 523 by norm_num]
      refine hstep.trans ?_
      calc (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523) * (BoseGases.a v) * (ℓ⁻¹)^2
          ≤ (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523) * |BoseGases.a v| * (ℓ⁻¹)^2 := by
            have habs : |BoseGases.a v| = BoseGases.a v := abs_of_pos ha
            rw [habs]
        _ ≤ ((2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/525) * |BoseGases.a v|^3
              + (2 * Real.pi)^(2*265) * (CB 265)^2 * (4*Real.pi/523) * |BoseGases.a v| + 1)
              * (ℓ⁻¹)^2 := by
            exact mul_le_mul_of_nonneg_right hC2 (sq_nonneg _)
    refine ⟨?_, ?_, ?_⟩
    · rw [hcdef]
      exact hint2
    · rw [show Work.BSKinetic.Decomp.bsW
          (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (BoseGases.a v)))
          (fun z : E3 => Submission.BoseGases.chiB ℓ d u z)
          = ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖
              * ‖Work.BSKinetic.Decomp.bsPsi
                  (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖^2
          from rfl]
      exact le_trans hbdint1 hfin1
    · rw [hcdef]
      exact le_trans hbdint2 hfin2

end Work.BoseFixB1S
