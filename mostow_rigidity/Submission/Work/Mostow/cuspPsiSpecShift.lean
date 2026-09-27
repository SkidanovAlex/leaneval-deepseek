import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cuspMap
import Submission.Work.Mostow.levYcFormula

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

variable {n : ℕ}

/-- The level-shifted cusp map: `u ↦ hptOf η (ψ (yc ξ u)) (lam * lev ξ u)`. It is the cusp map
with the output level scaled by `lam`; used to match the cusp levels of the source and target
horoball families. -/
noncomputable def cuspPsiShift (ψ : E n → E n) (ξ η : E n) (lam : ℝ) (u : E n) : E n :=
  hptOf η (ψ (yc ξ u)) (lam * lev ξ u)

theorem cuspPsiSpecShift (n : ℕ) (hA : Work.Mostow.POBasic n) (hI : Work.Mostow.HypIsoData n)
    {Γ Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)} (f : Γ ≃* Λ)
    {ξ η : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hη : η ∈ Submission.Mostow.Sph n) (tΓ tΛ lam : ℝ) (hlam : 0 < lam)
    (ψ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hpsiperp : ∀ x : Submission.Mostow.E n, inner ℝ x ξ = 0 → inner ℝ (ψ x) η = 0)
    (hpsilip : ∃ L C : ℝ, 0 ≤ L ∧ 0 ≤ C ∧
      ∀ x y : Submission.Mostow.E n, inner ℝ x ξ = 0 → inner ℝ y ξ = 0 →
        ‖ψ x - ψ y‖ ≤ L * ‖x - y‖ + C)
    (hpsisurj : ∃ C : ℝ, ∀ z : Submission.Mostow.E n, inner ℝ z η = 0 →
      ∃ x : Submission.Mostow.E n, inner ℝ x ξ = 0 ∧ ‖ψ x - z‖ ≤ C)
    (hstab : ∀ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Submission.Mostow.bd ((f γ : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) η = η)
    (hlevξ : ∀ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.lev ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : Submission.Mostow.E n)) = 1)
    (hlevη : ∀ m : Λ, Submission.Mostow.bd ((m : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.lev η (((m : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : Submission.Mostow.E n)) = 1)
    (hpsieq : ∃ Cψ : ℝ, ∀ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      ∀ x : Submission.Mostow.E n, inner ℝ x ξ = 0 →
        ‖ψ (Work.Mostow.flatAct ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)) x)
          - Work.Mostow.flatAct η (((f γ : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1)) (ψ x)‖ ≤ Cψ)
    (R : ℝ) :
    ∃ Ψ : Submission.Mostow.E n → Submission.Mostow.E n,
      (∀ u : Submission.Mostow.E n, Ψ u = Work.Mostow.hptOf η (ψ (Work.Mostow.yc ξ u))
        (lam * Work.Mostow.lev ξ u)) ∧
      (∃ C : ℝ, ∀ u v : Submission.Mostow.E n, Work.Mostow.lev ξ u ≤ Real.exp tΓ →
        Work.Mostow.lev ξ v ≤ Real.exp tΓ → Submission.Mostow.hdist u v ≤ R →
        Submission.Mostow.hdist (Ψ u) (Ψ v) ≤ C) ∧
      (∃ C : ℝ, ∀ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
        ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ u ≤ Real.exp tΓ →
          Submission.Mostow.hdist
            (Ψ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • u))
            (((f γ : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) • Ψ u) ≤ C) ∧
      (∃ C : ℝ, ∀ w : Submission.Mostow.E n, Work.Mostow.lev η w ≤ Real.exp tΛ →
        ∃ u : Submission.Mostow.E n, Work.Mostow.lev ξ u ≤ Real.exp tΛ / lam ∧
          Submission.Mostow.hdist (Ψ u) w ≤ C) := by
  refine ⟨cuspPsiShift ψ ξ η lam, fun u => rfl, ?_, ?_, ?_⟩
  · -- (a) local bound
    obtain ⟨Lq, Cq, hLq0, hCq0, hfwd⟩ := hpsilip
    set X : ℝ := Lq * Real.sqrt (2 * (Real.cosh R - 1)) + Cq * Real.exp tΓ with hXdef
    refine ⟨Real.arcosh (Real.cosh R + lam ^ 2 * X ^ 2 / 2), ?_⟩
    intro u v hu hv hd
    have hKa_ge : (1 : ℝ) ≤ Real.cosh R + lam ^ 2 * X ^ 2 / 2 := by
      have hc1 := Real.one_le_cosh R
      have hsq : 0 ≤ lam ^ 2 * X ^ 2 / 2 :=
        div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)
      linarith
    have hKey := levYcFormula hξ u v
    have hcoshR : Real.cosh (hdist u v) ≤ Real.cosh R := by
      refine Real.cosh_le_cosh.mpr ?_
      rw [abs_of_nonneg (hI.nonneg u v)]
      exact le_trans hd (le_abs_self R)
    have hlog1 : (1 : ℝ) ≤ Real.cosh (Real.log (lev ξ u / lev ξ v)) := Real.one_le_cosh _
    have hAZ : (lev ξ u * lev ξ v / 2) * ‖yc ξ u - yc ξ v‖ ^ 2 ≤ Real.cosh R - 1 := by
      linarith [hKey, hcoshR, hlog1]
    have hZ : lev ξ u * lev ξ v * ‖yc ξ u - yc ξ v‖ ^ 2 ≤ 2 * (Real.cosh R - 1) := by
      linarith [hAZ]
    have hA0 : 0 ≤ lev ξ u * lev ξ v :=
      mul_nonneg (le_of_lt (lev_pos ξ hξ u)) (le_of_lt (lev_pos ξ hξ v))
    have hM0 : 0 ≤ 2 * (Real.cosh R - 1) := by
      have h := Real.one_le_cosh R
      linarith
    have hsA : Real.sqrt (lev ξ u * lev ξ v) * ‖yc ξ u - yc ξ v‖
        ≤ Real.sqrt (2 * (Real.cosh R - 1)) := by
      have hs : (Real.sqrt (lev ξ u * lev ξ v) * ‖yc ξ u - yc ξ v‖) ^ 2
          ≤ (Real.sqrt (2 * (Real.cosh R - 1))) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hM0]
        exact hZ
      have hs' : Real.sqrt ((Real.sqrt (lev ξ u * lev ξ v) * ‖yc ξ u - yc ξ v‖) ^ 2)
          ≤ Real.sqrt ((Real.sqrt (2 * (Real.cosh R - 1))) ^ 2) := Real.sqrt_le_sqrt hs
      rwa [Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)),
        Real.sqrt_sq (Real.sqrt_nonneg _)] at hs'
    have hpsi_le : ‖ψ (yc ξ u) - ψ (yc ξ v)‖ ≤ Lq * ‖yc ξ u - yc ξ v‖ + Cq :=
      hfwd (yc ξ u) (yc ξ v) (yc_orth hξ) (yc_orth hξ)
    have hsAexp : Real.sqrt (lev ξ u * lev ξ v) ≤ Real.exp tΓ := by
      have hAexp : lev ξ u * lev ξ v ≤ Real.exp tΓ * Real.exp tΓ :=
        mul_le_mul hu hv (le_of_lt (lev_pos ξ hξ v)) (le_of_lt (Real.exp_pos tΓ))
      have h2 : Real.exp tΓ * Real.exp tΓ = Real.exp (2 * tΓ) := by
        rw [← Real.exp_add]; ring_nf
      rw [h2] at hAexp
      have h3 : Real.exp (2 * tΓ) = (Real.exp tΓ) ^ 2 := by
        rw [two_mul, Real.exp_add]; ring
      calc Real.sqrt (lev ξ u * lev ξ v) ≤ Real.sqrt (Real.exp (2 * tΓ)) :=
            Real.sqrt_le_sqrt hAexp
        _ = Real.exp tΓ := by
            rw [h3, Real.sqrt_sq (le_of_lt (Real.exp_pos tΓ))]
    have hprod : Real.sqrt (lev ξ u * lev ξ v) * ‖ψ (yc ξ u) - ψ (yc ξ v)‖ ≤ X := by
      have h1 : Real.sqrt (lev ξ u * lev ξ v) * ‖ψ (yc ξ u) - ψ (yc ξ v)‖
          ≤ Real.sqrt (lev ξ u * lev ξ v) * (Lq * ‖yc ξ u - yc ξ v‖ + Cq) :=
        mul_le_mul_of_nonneg_left hpsi_le (Real.sqrt_nonneg _)
      have h2 : Real.sqrt (lev ξ u * lev ξ v) * (Lq * ‖yc ξ u - yc ξ v‖ + Cq)
          = Lq * (Real.sqrt (lev ξ u * lev ξ v) * ‖yc ξ u - yc ξ v‖)
            + Cq * Real.sqrt (lev ξ u * lev ξ v) := by ring
      have h3 : Lq * (Real.sqrt (lev ξ u * lev ξ v) * ‖yc ξ u - yc ξ v‖)
          ≤ Lq * Real.sqrt (2 * (Real.cosh R - 1)) :=
        mul_le_mul_of_nonneg_left hsA hLq0
      have h4 : Cq * Real.sqrt (lev ξ u * lev ξ v) ≤ Cq * Real.exp tΓ :=
        mul_le_mul_of_nonneg_left hsAexp hCq0
      rw [hXdef]
      linarith [h1, h2, h3, h4]
    have hB : (lam ^ 2 * lev ξ u * lev ξ v / 2) * ‖ψ (yc ξ u) - ψ (yc ξ v)‖ ^ 2
        ≤ lam ^ 2 * X ^ 2 / 2 := by
      have h1 : (lam ^ 2 * lev ξ u * lev ξ v / 2) * ‖ψ (yc ξ u) - ψ (yc ξ v)‖ ^ 2
          = lam ^ 2 * ((Real.sqrt (lev ξ u * lev ξ v) * ‖ψ (yc ξ u) - ψ (yc ξ v)‖) ^ 2 / 2) := by
        rw [mul_pow, Real.sq_sqrt hA0]; ring
      rw [h1]
      have h2 := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hprod 2
      have h3 : (Real.sqrt (lev ξ u * lev ξ v) * ‖ψ (yc ξ u) - ψ (yc ξ v)‖) ^ 2 / 2
          ≤ X ^ 2 / 2 := by linarith [h2]
      nlinarith [h3, sq_nonneg lam]
    have hlevu : lev η (cuspPsiShift ψ ξ η lam u) = lam * lev ξ u :=
      (hptOfLevelYc η hη (hpsiperp (yc ξ u) (yc_orth hξ))
        (mul_pos hlam (lev_pos ξ hξ u))).1
    have hycu : yc η (cuspPsiShift ψ ξ η lam u) = ψ (yc ξ u) :=
      (hptOfLevelYc η hη (hpsiperp (yc ξ u) (yc_orth hξ))
        (mul_pos hlam (lev_pos ξ hξ u))).2.1
    have hlevv : lev η (cuspPsiShift ψ ξ η lam v) = lam * lev ξ v :=
      (hptOfLevelYc η hη (hpsiperp (yc ξ v) (yc_orth hξ))
        (mul_pos hlam (lev_pos ξ hξ v))).1
    have hycv : yc η (cuspPsiShift ψ ξ η lam v) = ψ (yc ξ v) :=
      (hptOfLevelYc η hη (hpsiperp (yc ξ v) (yc_orth hξ))
        (mul_pos hlam (lev_pos ξ hξ v))).2.1
    have hK1 := levYcFormula hη (cuspPsiShift ψ ξ η lam u) (cuspPsiShift ψ ξ η lam v)
    rw [hlevu, hlevv, hycu, hycv] at hK1
    -- simplify the level ratio and the flat coefficient
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    have hratio : lam * lev ξ u / (lam * lev ξ v) = lev ξ u / lev ξ v := by
      rw [mul_div_mul_left _ _ hlamne]
    have hcoef : (lam * lev ξ u) * (lam * lev ξ v) / 2
        = lam ^ 2 * lev ξ u * lev ξ v / 2 := by ring
    rw [hratio, hcoef] at hK1
    have hlogle : Real.cosh (Real.log (lev ξ u / lev ξ v)) ≤ Real.cosh R := by
      have h0 : 0 ≤ (lev ξ u * lev ξ v / 2) * ‖yc ξ u - yc ξ v‖ ^ 2 :=
        mul_nonneg (div_nonneg hA0 (by norm_num)) (sq_nonneg _)
      linarith [hKey, hcoshR, h0]
    have hmain : Real.cosh (hdist (cuspPsiShift ψ ξ η lam u) (cuspPsiShift ψ ξ η lam v))
        ≤ Real.cosh R + lam ^ 2 * X ^ 2 / 2 := by
      rw [hK1]
      exact add_le_add hlogle hB
    calc hdist (cuspPsiShift ψ ξ η lam u) (cuspPsiShift ψ ξ η lam v)
        = Real.arcosh (Real.cosh (hdist (cuspPsiShift ψ ξ η lam u)
            (cuspPsiShift ψ ξ η lam v))) :=
          (Real.arcosh_cosh (hI.nonneg _ _)).symm
      _ ≤ Real.arcosh (Real.cosh R + lam ^ 2 * X ^ 2 / 2) :=
          (Real.arcosh_le_arcosh (Real.cosh_pos _) (lt_of_lt_of_le zero_lt_one hKa_ge)).mpr hmain
  · -- (b) equivariance
    obtain ⟨Cψ, hCψ⟩ := hpsieq
    refine ⟨Real.arcosh (1 + (lam * Real.exp tΓ * Cψ) ^ 2 / 2), ?_⟩
    intro γ hγ u hu
    have hγ0 : lev ξ (((γ : Γ) : PO n 1) • (0 : E n)) = 1 := hlevξ γ hγ
    have hm : bd (((f γ : Λ) : PO n 1)) η = η := hstab γ hγ
    have hm0 : lev η ((((f γ : Λ) : PO n 1)) • (0 : E n)) = 1 := hlevη (f γ) hm
    have hycu : inner ℝ (yc ξ u) ξ = 0 := yc_orth hξ
    have hu' : ((γ : Γ) : PO n 1) • u
        = hptOf ξ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u)) (lev ξ u) := by
      conv_lhs => rw [← hptOf_yc_lev hξ u]
      exact hptOf_smul_level hA hI hξ hγ hγ0 hycu (lev_pos ξ hξ u)
    have hlevγu : lev ξ (((γ : Γ) : PO n 1) • u) = lev ξ u := by
      rw [hu', (hptOfLevelYc ξ hξ (flatAct_mem hξ (((γ : Γ) : PO n 1)) (yc ξ u))
        (lev_pos ξ hξ u)).1]
    have hycγu : yc ξ (((γ : Γ) : PO n 1) • u)
        = flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u) := by
      rw [hu', (hptOfLevelYc ξ hξ (flatAct_mem hξ (((γ : Γ) : PO n 1)) (yc ξ u))
        (lev_pos ξ hξ u)).2.1]
    have hΨγu : cuspPsiShift ψ ξ η lam (((γ : Γ) : PO n 1) • u)
        = hptOf η (ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))) (lam * lev ξ u) := by
      simp only [cuspPsiShift, hycγu, hlevγu]
    have hΨu : cuspPsiShift ψ ξ η lam u = hptOf η (ψ (yc ξ u)) (lam * lev ξ u) := by
      simp only [cuspPsiShift]
    have hmΨ : (((f γ : Λ) : PO n 1)) • cuspPsiShift ψ ξ η lam u
        = hptOf η (flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))) (lam * lev ξ u) := by
      rw [hΨu]
      exact hptOf_smul_level hA hI hη hm hm0 (hpsiperp (yc ξ u) hycu)
        (mul_pos hlam (lev_pos ξ hξ u))
    have horth1 : inner ℝ (ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))) η = 0 :=
      hpsiperp _ (flatAct_mem hξ (((γ : Γ) : PO n 1)) (yc ξ u))
    have horth2 : inner ℝ (flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))) η = 0 :=
      flatAct_mem hη (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))
    have hb := hptOf_hdist η hη (lam * lev ξ u) (mul_pos hlam (lev_pos ξ hξ u))
      (ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u)))
      (flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))) horth1 horth2
    have hle : ‖ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))
        - flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))‖ ≤ Cψ := hCψ γ hγ (yc ξ u) hycu
    have harg : 1 + (lam * lev ξ u * ‖ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))
          - flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))‖) ^ 2 / 2
        ≤ 1 + (lam * Real.exp tΓ * Cψ) ^ 2 / 2 := by
      have h1 : lam * lev ξ u * ‖ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))
            - flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))‖ ≤ lam * Real.exp tΓ * Cψ := by
        have hleq : lam * lev ξ u ≤ lam * Real.exp tΓ :=
          mul_le_mul_of_nonneg_left hu (le_of_lt hlam)
        calc lam * lev ξ u * ‖ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))
              - flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))‖
            ≤ lam * lev ξ u * Cψ := mul_le_mul_of_nonneg_left hle (mul_nonneg (le_of_lt hlam) (le_of_lt (lev_pos ξ hξ u)))
          _ ≤ lam * Real.exp tΓ * Cψ := by
              have : (0:ℝ) ≤ Cψ := le_trans (norm_nonneg _) hle
              nlinarith [hleq, this]
      have h2 : 0 ≤ lam * lev ξ u * ‖ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))
            - flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))‖ :=
        mul_nonneg (mul_nonneg (le_of_lt hlam) (le_of_lt (lev_pos ξ hξ u))) (norm_nonneg _)
      have h3 := pow_le_pow_left₀ h2 h1 2
      linarith [h3]
    rw [hΨγu, hmΨ]
    calc hdist (hptOf η (ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))) (lam * lev ξ u))
          (hptOf η (flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))) (lam * lev ξ u))
        = Real.arcosh (1 + (lam * lev ξ u * ‖ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))
            - flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))‖) ^ 2 / 2) := hb
      _ ≤ Real.arcosh (1 + (lam * Real.exp tΓ * Cψ) ^ 2 / 2) :=
          (Real.arcosh_le_arcosh (by positivity) (by positivity)).mpr harg
  · -- (c) surjectivity
    obtain ⟨Cψ, hCψ⟩ := hpsisurj
    refine ⟨Real.arcosh (Real.cosh (|Real.log lam| + |tΓ| + |tΛ|)
      + (lam * Real.exp (tΓ + tΛ)) * Cψ ^ 2 / 2), ?_⟩
    intro w hw
    obtain ⟨y, hy, hyC⟩ := hCψ (yc η w) (yc_orth hη)
    set L' : ℝ := min (lev η w / lam) (Real.exp tΓ) with hL'
    have hL'pos : 0 < L' := by
      rw [hL']
      exact lt_min (div_pos (lev_pos η hη w) hlam) (Real.exp_pos tΓ)
    have hL'le : L' ≤ Real.exp tΓ := by rw [hL']; exact min_le_right _ _
    have hL'le' : L' ≤ lev η w / lam := by rw [hL']; exact min_le_left _ _
    refine ⟨hptOf ξ y L', ?_, ?_⟩
    · rw [(hptOfLevelYc ξ hξ hy hL'pos).1]
      exact le_trans hL'le' (div_le_div_of_nonneg_right hw (le_of_lt hlam))
    · have hψorth : inner ℝ (ψ y) η = 0 := hpsiperp y hy
      have hDw : lam * L' ≤ lev η w := by
        have := hL'le'; rw [le_div_iff₀ hlam] at this; linarith [this]
      have hgen := hdist_hptOf_gen (ξ := η) hη hI (ψ y) (yc η w) (lam * L') (lev η w) hψorth
        (yc_orth hη) (mul_pos hlam hL'pos) (lev_pos η hη w)
      rw [hptOf_yc_lev hη w] at hgen
      have h1 : cuspPsiShift ψ ξ η lam (hptOf ξ y L') = hptOf η (ψ y) (lam * L') := by
        simp only [cuspPsiShift, (hptOfLevelYc ξ hξ hy hL'pos).1, (hptOfLevelYc ξ hξ hy hL'pos).2.1]
      rw [h1, hgen]
      -- cosh (log ((lam*L')/lev η w)) ≤ cosh (|log lam| + |tΓ| + |tΛ|)
      have hLpos : 0 < lev η w := lev_pos η hη w
      have hlogb : |Real.log (lam * L' / lev η w)| ≤ |Real.log lam| + |tΓ| + |tΛ| := by
        by_cases hcase : lev η w / lam ≤ Real.exp tΓ
        · have hLeq : L' = lev η w / lam := by rw [hL']; exact min_eq_left hcase
          have hone : lam * L' / lev η w = 1 := by
            rw [hLeq, mul_div_cancel₀ _ (ne_of_gt hlam), div_self (ne_of_gt hLpos)]
          rw [hone, Real.log_one, abs_zero]
          positivity
        · have hLeq : L' = Real.exp tΓ := by
            rw [hL']; exact min_eq_right (le_of_lt (not_le.mp hcase))
          have hlt : lam * Real.exp tΓ < lev η w := by
            have hh := not_le.mp hcase
            rw [lt_div_iff₀ hlam] at hh
            linarith [hh]
          have h1 : 0 < lam * Real.exp tΓ := mul_pos hlam (Real.exp_pos tΓ)
          have hle1 : lam * Real.exp tΓ / lev η w ≤ 1 := (div_le_one hLpos).mpr (le_of_lt hlt)
          have hlog_le : Real.log (lam * Real.exp tΓ / lev η w) ≤ 0 :=
            Real.log_nonpos (le_of_lt (div_pos h1 hLpos)) hle1
          have hlog_eq : Real.log (lam * Real.exp tΓ / lev η w)
              = Real.log lam + tΓ - Real.log (lev η w) := by
            rw [Real.log_div (ne_of_gt h1) (ne_of_gt hLpos),
              Real.log_mul (ne_of_gt hlam) (ne_of_gt (Real.exp_pos tΓ)), Real.log_exp]
          have hlog_le' : Real.log lam + tΓ - Real.log (lev η w) ≤ 0 := by
            rw [← hlog_eq]; exact hlog_le
          rw [hLeq, hlog_eq, abs_of_nonpos hlog_le']
          have hlt2 : Real.log (lev η w) ≤ tΛ := by
            rw [← Real.log_exp tΛ]; exact Real.log_le_log hLpos hw
          have ha : -Real.log lam ≤ |Real.log lam| := neg_le_abs _
          have hb : -tΓ ≤ |tΓ| := neg_le_abs _
          have hc : tΛ ≤ |tΛ| := le_abs_self _
          linarith
      have hcoshlog : Real.cosh (Real.log (lam * L' / lev η w))
          ≤ Real.cosh (|Real.log lam| + |tΓ| + |tΛ|) := by
        refine Real.cosh_le_cosh.mpr ?_
        have h2 : |(|Real.log lam| + |tΓ| + |tΛ|)| = |Real.log lam| + |tΓ| + |tΛ| :=
          abs_of_nonneg (by positivity)
        rw [h2]; exact hlogb
      have hflat : ((lam * L') * lev η w / 2) * ‖ψ y - yc η w‖ ^ 2
          ≤ (lam * Real.exp (tΓ + tΛ)) * Cψ ^ 2 / 2 := by
        have hDw2 : (lam * L') * lev η w ≤ (lam * Real.exp tΓ) * Real.exp tΛ := by
          have h1 : lam * L' ≤ lam * Real.exp tΓ :=
            mul_le_mul_of_nonneg_left hL'le (le_of_lt hlam)
          exact mul_le_mul h1 hw (le_of_lt hLpos) (le_of_lt (mul_pos hlam (Real.exp_pos tΓ)))
        have hψ2 : ‖ψ y - yc η w‖ ^ 2 ≤ Cψ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hyC 2
        have hb2 : 0 ≤ lam * Real.exp tΓ * Real.exp tΛ / 2 :=
          div_nonneg (mul_nonneg (mul_nonneg (le_of_lt hlam)
            (le_of_lt (Real.exp_pos tΓ))) (le_of_lt (Real.exp_pos tΛ))) (by norm_num)
        calc ((lam * L') * lev η w / 2) * ‖ψ y - yc η w‖ ^ 2
            ≤ ((lam * Real.exp tΓ) * Real.exp tΛ / 2) * Cψ ^ 2 :=
              mul_le_mul (by linarith) hψ2 (sq_nonneg _) hb2
          _ = (lam * Real.exp (tΓ + tΛ)) * Cψ ^ 2 / 2 := by rw [Real.exp_add]; ring
      refine (Real.arcosh_le_arcosh (by positivity) (by positivity)).mpr ?_
      linarith [hcoshlog, hflat]

end Work.Mostow
