import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.Est1.ComZarith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.ComZarith` — the arithmetic of the `χ̂²` half

The two scalar inequalities of the assembly of `Est1.estT2sum_comZ`, at the FS
parameter point:

* the **gap** inequality
  `dlt·K₀ + Λ·cbeta + erm·Λ·NPL·(1+2β_m+β_m²) ≤ (b/400)ℓ⁻²`,
* the **error bracket** inequality
  `Λ·cbeta·NPL + erm·Λ·(β_m+β_m²)·NPL² ≤ C·e1A`.

Both are proved by writing every quantity as a monomial in `X = (μa³)^{1/323}`
(`Work.BoseB7.FSParamsVals`) times `ℓ⁻²`.
-/

noncomputable section
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace Work.BoseC3QAll
namespace Est1
open Work.BoseB7 Work.BoseBox
variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
/-- The arithmetic of the `χ̂²` half: the gap and error-bracket inequalities. -/
theorem comZ_arith (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
          (Work.BoseC3QAll.Est1.dlt K₀ E * K₀ + Work.BoseC3QAll.Est1.LamBound K₀ E * Work.BoseC3QAll.Est1.cbeta K₀ E
              + Work.BoseC3QAll.Est1.erm K₀ E * Work.BoseC3QAll.Est1.LamBound K₀ E * Work.BoseC3QAll.Est1.NPL E
                * (1 + 2 * Work.BoseC3QAll.Est1.bm K₀ E + Work.BoseC3QAll.Est1.bm K₀ E ^ 2)
              ≤ (E.b / 400) * (E.ell ^ 2)⁻¹)
          ∧ (Work.BoseC3QAll.Est1.LamBound K₀ E * Work.BoseC3QAll.Est1.cbeta K₀ E * Work.BoseC3QAll.Est1.NPL E
              + Work.BoseC3QAll.Est1.erm K₀ E * Work.BoseC3QAll.Est1.LamBound K₀ E
                * (Work.BoseC3QAll.Est1.bm K₀ E + Work.BoseC3QAll.Est1.bm K₀ E ^ 2) * Work.BoseC3QAll.Est1.NPL E ^ 2
              ≤ C * Work.BoseC3QAll.e1A E) := by
  obtain ⟨t₁, ht₁, h₁⟩ := fsXp_le_of_pos_exp (A := 58)
    (c := b₀ / (400 * (24 * (K₀ + 1) ^ 2 + 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4
      + 12 * (2 : ℝ) ^ 24 * (K₀ + 1) ^ 4 + 1))) (by norm_num)
    (div_pos hb₀ (by positivity))
  obtain ⟨t₂, ht₂, h₂⟩ := fsXp_le_of_pos_exp (A := 58) (c := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨t₃, ht₃, h₃⟩ := fsXp_le_of_pos_exp (A := 58) (c := 1 / (2 ^ 12 * ((K₀ + 1) ^ 2 + 1)))
    (by norm_num) (div_pos one_pos (by positivity))
  refine ⟨(2 : ℝ) ^ 40 * (K₀ + 1) ^ 8, min (min t₁ t₂) t₃,
    by positivity, lt_min (lt_min ht₁ ht₂) ht₃, ?_⟩
  intro Mode _ _ _ F T E hv hle hb hK
  have ht : 0 < hv.t := hv.t_pos
  have hle₁ : hv.t ≤ t₁ := le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hle₂ : hv.t ≤ t₂ := le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hle₃ : hv.t ≤ t₃ := le_trans hle (min_le_right _ _)
  have hXa : fsXp hv.t 58 ≤ b₀ / (400 * (24 * (K₀ + 1) ^ 2 + 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4
      + 12 * (2 : ℝ) ^ 24 * (K₀ + 1) ^ 4 + 1)) := h₁ hv.t ht hle₁
  have hXb : fsXp hv.t 58 ≤ 1 / 2 := h₂ hv.t ht hle₂
  have hXc : fsXp hv.t 58 ≤ 1 / (2 ^ 12 * ((K₀ + 1) ^ 2 + 1)) := h₃ hv.t ht hle₃
  have hmono : ∀ e : ℝ, 58 ≤ e → fsXp hv.t e ≤ fsXp hv.t 58 :=
    fun e he => fsXp_le_fsXp ht hv.t_le_one he
  have hk0 : 0 ≤ K₀ := K₀_nonneg_of_kernel K₀ F T E hv hK
  have hK1 : 0 ≤ K₀ + 1 := by linarith
  have hae : 0 ≤ E.aScat := le_of_lt hv.a_pos
  have hlile : 0 ≤ E.lille := le_of_lt (lille_pos E hv)
  have hKle : 0 ≤ E.Kl := le_of_lt (by linarith [hv.one_le_Kl])
  have hKLe : 0 ≤ E.KL := le_of_lt (by linarith [hv.one_le_KL])
  have hKHe : 0 ≤ E.KH := le_of_lt (KH_pos E hv)
  have hKHinve : 0 ≤ E.KH⁻¹ := inv_nonneg.mpr hKHe
  have hKHinv : E.KH⁻¹ ≤ 1 := by
    rw [KHinv_val hv]; exact fsXp_le_one ht hv.t_le_one (by norm_num)
  have hρe : 0 ≤ E.rho := le_of_lt (Work.BoseB7.rho_pos E hv)
  have hivl : 0 ≤ (E.ell ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg E.ell)
  have hW1nn : 0 ≤ E.W1omega0 := hK.W1omega0_nonneg
  have hXnn : ∀ c : ℝ, 0 ≤ fsXp hv.t c := fun c => fsXp_nonneg ht.le
  have hXnn3 : 0 ≤ fsXp hv.t (-3) := hXnn (-3)
  have hXnn36 : 0 ≤ fsXp hv.t (-36) := hXnn (-36)
  have hXnn58 : 0 ≤ fsXp hv.t 58 := hXnn 58
  have hXnn94 : 0 ≤ fsXp hv.t 94 := hXnn 94
  have hXnn97 : 0 ≤ fsXp hv.t 97 := hXnn 97
  have hXnn119 : 0 ≤ fsXp hv.t 119 := hXnn 119
  have hdile : 0 ≤ dil E (1 / 2) := dil_nonneg E hv (1 / 2)
  have hdile4 : 0 ≤ dil E (1 / 4) := dil_nonneg E hv (1 / 4)
  have hetae : 0 ≤ eta E := by rw [eta_eq E hv]; exact fsXp_nonneg ht.le
  have hbpos : 0 < E.b := lt_of_lt_of_le hb₀ hb
  have h97nn : 0 ≤ fsXp hv.t 97 := hXnn 97
  have hX97b : fsXp hv.t 97 ≤ 1 / 2 := le_trans (hmono 97 (by norm_num)) hXb
  have hX97c : fsXp hv.t 97 ≤ 1 / (2 ^ 12 * ((K₀ + 1) ^ 2 + 1)) :=
    le_trans (hmono 97 (by norm_num)) hXc
  have hMuA : E.mu * E.aScat = fsXp hv.t (-3) * (E.ell ^ 2)⁻¹ := by
    rw [mu_mul_aScat_eq E hv, Kl_sq hv, div_eq_mul_inv]
  have hRhoA : E.rho * E.aScat ≤ (3 / 2) * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹) := by
    calc E.rho * E.aScat ≤ (3 * E.mu / 2) * E.aScat :=
          mul_le_mul_of_nonneg_right (rho_le E hv) hae
      _ = (3 / 2) * (E.mu * E.aScat) := by ring
      _ = (3 / 2) * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹) := by rw [hMuA]
  have hBm : bm K₀ E = 2 ^ 12 * K₀ ^ 2 * fsXp hv.t 97 := by rw [bm, lille_sq hv]
  have hbm0 : 0 ≤ bm K₀ E := bm_nonneg hk0
  have hbm1 : bm K₀ E ≤ 1 := by
    rw [hBm]
    calc 2 ^ 12 * K₀ ^ 2 * fsXp hv.t 97 ≤ 2 ^ 12 * (K₀ + 1) ^ 2 * fsXp hv.t 97 := by
          have h4 : 2 ^ 12 * K₀ ^ 2 ≤ 2 ^ 12 * (K₀ + 1) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right h4 h97nn
      _ ≤ 2 ^ 12 * (K₀ + 1) ^ 2 * (1 / (2 ^ 12 * ((K₀ + 1) ^ 2 + 1))) :=
          mul_le_mul_of_nonneg_left hX97c (by positivity)
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]
          linarith [sq_nonneg (K₀ + 1)]
  have hKHv : E.KH⁻¹ = fsXp hv.t (549 / 4) := KHinv_val hv
  have hlil2 : E.lille ^ 2 ≤ 1 / 2 := by rw [lille_sq hv]; exact hX97b
  have hlilKH : E.KH⁻¹ ≤ E.lille ^ 2 := by
    rw [lille_sq hv, hKHv]
    exact fsXp_le_fsXp ht hv.t_le_one (by norm_num : (97 : ℝ) ≤ 549 / 4)
  have hcb0 : 0 ≤ cbeta K₀ E := by rw [cbeta]; positivity
  have hLam0 : 0 ≤ LamBound K₀ E := by
    rw [LamBound]
    have h1 : 0 ≤ E.W1omega0 + K₀ * E.aScat * E.KH⁻¹ :=
      add_nonneg hW1nn (mul_nonneg (mul_nonneg hk0 hae) hKHinve)
    exact mul_nonneg (mul_nonneg (by linarith) h1) (by nlinarith [sq_nonneg E.lille])
  have herm0 : 0 ≤ erm K₀ E := by
    rw [erm]
    exact add_nonneg (devc_nonneg hk0)
      (mul_nonneg (add_nonneg zero_le_one (devc_nonneg hk0))
        (mul_nonneg (sq_nonneg K₀) (sq_nonneg _)))
  have hNPL0 : 0 ≤ NPL E := NPL_nonneg E
  have hTA0 : 0 ≤ K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹) :=
    mul_nonneg hk0 (mul_nonneg (hXnn (-3)) hivl)
  have hLamB : LamBound K₀ E ≤ 12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹) := by
    have hA2 : E.W1omega0 + K₀ * E.aScat * E.KH⁻¹ ≤ 2 * (K₀ * E.aScat) := by
      have h1 : K₀ * E.aScat * E.KH⁻¹ ≤ K₀ * E.aScat := by
        calc K₀ * E.aScat * E.KH⁻¹ ≤ K₀ * E.aScat * 1 :=
              mul_le_mul_of_nonneg_left hKHinv (mul_nonneg hk0 hae)
          _ = K₀ * E.aScat := by ring
      linarith [hK.W1omega0_le]
    have hB2 : 1 + 2 * E.lille ^ 2 ≤ 2 := by linarith [hlil2]
    have hKA : 0 ≤ K₀ * E.aScat := mul_nonneg hk0 hae
    have hstep : 2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) * (1 + 2 * E.lille ^ 2)
        ≤ 2 * E.rho * (2 * (K₀ * E.aScat)) * 2 := by
      have h1 : 2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹)
          ≤ 2 * E.rho * (2 * (K₀ * E.aScat)) :=
        mul_le_mul_of_nonneg_left hA2 (by linarith)
      exact mul_le_mul h1 hB2 (by nlinarith [sq_nonneg E.lille]) (by nlinarith [hKA, hρe])
    calc LamBound K₀ E
        = 2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) * (1 + 2 * E.lille ^ 2) := rfl
      _ ≤ 2 * E.rho * (2 * (K₀ * E.aScat)) * 2 := hstep
      _ = 8 * (E.rho * E.aScat) * K₀ := by ring
      _ ≤ 8 * ((3 / 2) * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹)) * K₀ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRhoA (by norm_num)) hk0
      _ = 12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹) := by ring
  have hDltB : dlt K₀ E ≤ 24 * K₀ * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹) := by
    have h2 : E.lille ^ 2 + E.KH⁻¹ ≤ 2 * E.lille ^ 2 := by linarith [hlilKH]
    have h5 : 0 ≤ 8 * E.rho * K₀ * E.aScat := by positivity
    have hstep : 8 * E.rho * K₀ * E.aScat * (E.lille ^ 2 + E.KH⁻¹)
        ≤ 8 * E.rho * K₀ * E.aScat * (2 * E.lille ^ 2) := mul_le_mul_of_nonneg_left h2 h5
    have h6 : E.rho * E.aScat ≤ (3 / 2) * (E.mu * E.aScat) := by
      calc E.rho * E.aScat ≤ (3 * E.mu / 2) * E.aScat :=
            mul_le_mul_of_nonneg_right (rho_le E hv) hae
        _ = (3 / 2) * (E.mu * E.aScat) := by ring
    have hKH2 : 0 ≤ 2 * E.lille ^ 2 := by positivity
    have hstep2 : 8 * E.rho * K₀ * E.aScat * (2 * E.lille ^ 2)
        ≤ 8 * (3 / 2) * K₀ * (E.mu * E.aScat) * (2 * E.lille ^ 2) := by
      have h7 : 8 * E.rho * K₀ * E.aScat ≤ 8 * (3 / 2) * K₀ * (E.mu * E.aScat) := by
        nlinarith [h6, hk0, hae]
      exact mul_le_mul_of_nonneg_right h7 hKH2
    have hMuL : E.mu * E.aScat * E.lille ^ 2 = fsXp hv.t 94 * (E.ell ^ 2)⁻¹ := by
      rw [hMuA, lille_sq hv,
        show fsXp hv.t (-3) * (E.ell ^ 2)⁻¹ * fsXp hv.t 97
          = fsXp hv.t (-3) * fsXp hv.t 97 * (E.ell ^ 2)⁻¹ by ring,
        fsXp_mul ht]
      congr 1; norm_num
    calc dlt K₀ E = 8 * E.rho * K₀ * E.aScat * (E.lille ^ 2 + E.KH⁻¹) := rfl
      _ ≤ 8 * (3 / 2) * K₀ * (E.mu * E.aScat) * (2 * E.lille ^ 2) := le_trans hstep hstep2
      _ = 24 * K₀ * (E.mu * E.aScat * E.lille ^ 2) := by ring
      _ = 24 * K₀ * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹) := by rw [hMuL]
  have hCBB : cbeta K₀ E ≤ 2 ^ 15 * (K₀ + 1) * K₀ ^ 2 * fsXp hv.t 97 := by
    rw [cbeta]
    have h1 : 4 * bm K₀ E + 4 * bm K₀ E ^ 2 ≤ 8 * bm K₀ E := by nlinarith [hbm0, hbm1]
    calc (K₀ + 1) * (4 * bm K₀ E + 4 * bm K₀ E ^ 2) ≤ (K₀ + 1) * (8 * bm K₀ E) :=
          mul_le_mul_of_nonneg_left h1 hK1
      _ = 2 ^ 15 * (K₀ + 1) * K₀ ^ 2 * fsXp hv.t 97 := by rw [hBm]; ring
  have hEta2le : eta E ^ 2 ≤ E.lille ^ 2 := by
    rw [eta_sq hv, lille_sq hv]
    exact fsXp_le_fsXp ht hv.t_le_one (by norm_num : (97 : ℝ) ≤ 2472)
  have hErmB : erm K₀ E ≤ 2 ^ 10 * bm K₀ E := by
    rw [erm, devc]
    have hdev : 2 ^ 20 * K₀ ^ 2 * E.lille ^ 2 = 2 ^ 8 * bm K₀ E := by
      rw [hBm, lille_sq hv]; ring
    have hK02lil2 : K₀ ^ 2 * eta E ^ 2 ≤ bm K₀ E := by
      have h1 : K₀ ^ 2 * eta E ^ 2 ≤ K₀ ^ 2 * E.lille ^ 2 :=
        mul_le_mul_of_nonneg_left hEta2le (sq_nonneg K₀)
      rw [hBm]
      have h2 : K₀ ^ 2 * E.lille ^ 2 ≤ 2 ^ 12 * K₀ ^ 2 * fsXp hv.t 97 := by
        have h3 := mul_le_mul_of_nonneg_left (lille_sq hv).le (sq_nonneg K₀)
        nlinarith
      linarith
    rw [hdev]
    have h2 : (1 + 2 ^ 8 * bm K₀ E) * (K₀ ^ 2 * eta E ^ 2) ≤ (1 + 2 ^ 8) * bm K₀ E := by
      have h1 : 1 + 2 ^ 8 * bm K₀ E ≤ 1 + 2 ^ 8 := by linarith
      exact mul_le_mul h1 hK02lil2 (mul_nonneg (sq_nonneg K₀) (sq_nonneg _))
        (by positivity)
    have h3 : (1 + 2 ^ 8) * bm K₀ E ≤ 2 ^ 9 * bm K₀ E := by nlinarith [hbm0]
    nlinarith [h2, h3, hbm0]
  have hNPLB : NPL E ≤ K₀ * fsXp hv.t (-36) := by
    have h1 : E.Kl * E.KL = fsXp hv.t (-12) := by
      rw [Kl_val E hv, KL_val E hv, fsXp_mul ht]
      congr 1; norm_num
    have h2 := hK.count_PL
    change (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) ≤ K₀ * fsXp hv.t (-36)
    have h3 : (fsXp hv.t (-12)) ^ 3 = fsXp hv.t (-36) := by
      rw [← Real.rpow_natCast, fsXp_rpow ht.le]
      congr 1; norm_num
    rw [h1, h3] at h2
    exact h2
  have ha1 : dlt K₀ E * K₀ ≤ 24 * K₀ ^ 2 * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹) := by
    calc dlt K₀ E * K₀ ≤ 24 * K₀ * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹) * K₀ :=
          mul_le_mul_of_nonneg_right hDltB hk0
      _ = 24 * K₀ ^ 2 * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹) := by ring
  have ha2 : LamBound K₀ E * cbeta K₀ E
      ≤ 12 * (2 : ℝ) ^ 15 * (K₀ + 1) * K₀ ^ 3 * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹) := by
    have h1 : LamBound K₀ E * cbeta K₀ E
        ≤ 12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹)
          * (2 ^ 15 * (K₀ + 1) * K₀ ^ 2 * fsXp hv.t 97) :=
      mul_le_mul hLamB hCBB hcb0 (by linarith [hTA0])
    have h2 : 12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹)
        * (2 ^ 15 * (K₀ + 1) * K₀ ^ 2 * fsXp hv.t 97)
        = 12 * (2 : ℝ) ^ 15 * (K₀ + 1) * K₀ ^ 3
          * (fsXp hv.t (-3) * fsXp hv.t 97 * (E.ell ^ 2)⁻¹) := by ring
    rw [h2, fsXp_mul ht] at h1
    rw [show (-3 : ℝ) + 97 = 94 by norm_num] at h1
    exact h1
  have ha3 : erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2)
      ≤ 12 * (2 : ℝ) ^ 24 * K₀ ^ 4 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) := by
    have hK0X36 : 0 ≤ K₀ * fsXp hv.t (-36) := mul_nonneg hk0 (hXnn (-36))
    have h1b : erm K₀ E * LamBound K₀ E ≤
        (2 ^ 10 * bm K₀ E) * (12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹)) :=
      mul_le_mul hErmB hLamB hLam0 (by positivity)
    have h2b : erm K₀ E * LamBound K₀ E * NPL E
        ≤ (2 ^ 10 * bm K₀ E) * (12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹))
          * (K₀ * fsXp hv.t (-36)) :=
      mul_le_mul h1b hNPLB hNPL0 (by positivity)
    have h3b : 1 + 2 * bm K₀ E + bm K₀ E ^ 2 ≤ 4 := by nlinarith [hbm0, hbm1]
    have h4b : 0 ≤ (2 ^ 10 * bm K₀ E) * (12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹))
        * (K₀ * fsXp hv.t (-36)) := by positivity
    have h5b : (2 ^ 10 * bm K₀ E) * (12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹))
          * (K₀ * fsXp hv.t (-36)) * (1 + 2 * bm K₀ E + bm K₀ E ^ 2)
        ≤ (2 ^ 10 * bm K₀ E) * (12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹))
          * (K₀ * fsXp hv.t (-36)) * 4 :=
      mul_le_mul_of_nonneg_left h3b h4b
    have h6b : (2 ^ 10 * bm K₀ E) * (12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹))
          * (K₀ * fsXp hv.t (-36)) * 4
        = 12 * (2 : ℝ) ^ 24 * K₀ ^ 4 * (fsXp hv.t 97 * fsXp hv.t (-3) * fsXp hv.t (-36)
            * (E.ell ^ 2)⁻¹) := by
      rw [hBm]; ring
    have h7b : fsXp hv.t 97 * fsXp hv.t (-3) * fsXp hv.t (-36) = fsXp hv.t 58 := by
      rw [fsXp_mul ht, fsXp_mul ht]
      congr 1; norm_num
    have h8b : erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2)
        ≤ (2 ^ 10 * bm K₀ E) * (12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹))
          * (K₀ * fsXp hv.t (-36)) * 4 :=
      le_trans (mul_le_mul_of_nonneg_right h2b (by nlinarith [hbm0, sq_nonneg (bm K₀ E)])) h5b
    rw [h6b, h7b] at h8b
    exact h8b
  have ha : dlt K₀ E * K₀ + LamBound K₀ E * cbeta K₀ E
      + erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2)
      ≤ (24 * (K₀ + 1) ^ 2 + 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4 + 12 * (2 : ℝ) ^ 24 * (K₀ + 1) ^ 4)
        * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) := by
    have hX94 : fsXp hv.t 94 ≤ fsXp hv.t 58 := hmono 94 (by norm_num)
    have h1 : 24 * K₀ ^ 2 * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹)
        ≤ 24 * (K₀ + 1) ^ 2 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) := by
      have h2 : K₀ ^ 2 ≤ (K₀ + 1) ^ 2 := by nlinarith
      have h3 : fsXp hv.t 94 * (E.ell ^ 2)⁻¹ ≤ fsXp hv.t 58 * (E.ell ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hX94 hivl
      calc 24 * K₀ ^ 2 * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹)
          ≤ 24 * (K₀ + 1) ^ 2 * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹) := by
            exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ ≤ 24 * (K₀ + 1) ^ 2 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
    have h2 : 12 * (2 : ℝ) ^ 15 * (K₀ + 1) * K₀ ^ 3 * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹)
        ≤ 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) := by
      have h3 : (K₀ + 1) * K₀ ^ 3 ≤ (K₀ + 1) ^ 4 := by
        have h4 : K₀ ^ 3 ≤ (K₀ + 1) ^ 3 := pow_le_pow_left₀ hk0 (by linarith) 3
        nlinarith [h4, hK1]
      have h7 : fsXp hv.t 94 * (E.ell ^ 2)⁻¹ ≤ fsXp hv.t 58 * (E.ell ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hX94 hivl
      calc 12 * (2 : ℝ) ^ 15 * (K₀ + 1) * K₀ ^ 3 * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹)
          = 12 * (2 : ℝ) ^ 15 * ((K₀ + 1) * K₀ ^ 3) * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹) := by ring
        _ ≤ 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4 * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
        _ ≤ 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left h7 (by positivity)
    have h3 : 12 * (2 : ℝ) ^ 24 * K₀ ^ 4 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹)
        ≤ 12 * (2 : ℝ) ^ 24 * (K₀ + 1) ^ 4 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk0 (by linarith) 4) (by positivity))
        (by positivity)
    have hsum : dlt K₀ E * K₀ + LamBound K₀ E * cbeta K₀ E
        + erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2)
        ≤ 24 * (K₀ + 1) ^ 2 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹)
          + 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹)
          + 12 * (2 : ℝ) ^ 24 * (K₀ + 1) ^ 4 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) := by
      linarith [ha1, ha2, ha3, h1, h2, h3]
    calc dlt K₀ E * K₀ + LamBound K₀ E * cbeta K₀ E
        + erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2)
        ≤ _ := hsum
      _ = (24 * (K₀ + 1) ^ 2 + 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4
          + 12 * (2 : ℝ) ^ 24 * (K₀ + 1) ^ 4) * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) := by ring
  have hfinA : dlt K₀ E * K₀ + LamBound K₀ E * cbeta K₀ E
      + erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2)
      ≤ (E.b / 400) * (E.ell ^ 2)⁻¹ := by
    have hDcne : (24 * (K₀ + 1) ^ 2 + 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4
        + 12 * (2 : ℝ) ^ 24 * (K₀ + 1) ^ 4 + 1) ≠ 0 := by positivity
    have hD1 : (24 * (K₀ + 1) ^ 2 + 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4
        + 12 * (2 : ℝ) ^ 24 * (K₀ + 1) ^ 4) * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹)
        ≤ (24 * (K₀ + 1) ^ 2 + 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4
          + 12 * (2 : ℝ) ^ 24 * (K₀ + 1) ^ 4 + 1)
          * ((b₀ / (400 * (24 * (K₀ + 1) ^ 2 + 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4
            + 12 * (2 : ℝ) ^ 24 * (K₀ + 1) ^ 4 + 1))) * (E.ell ^ 2)⁻¹) := by
      refine mul_le_mul (by linarith) ?_ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hXa hivl
    have hD2 : (24 * (K₀ + 1) ^ 2 + 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4
          + 12 * (2 : ℝ) ^ 24 * (K₀ + 1) ^ 4 + 1)
          * ((b₀ / (400 * (24 * (K₀ + 1) ^ 2 + 12 * (2 : ℝ) ^ 15 * (K₀ + 1) ^ 4
            + 12 * (2 : ℝ) ^ 24 * (K₀ + 1) ^ 4 + 1))) * (E.ell ^ 2)⁻¹)
        = (b₀ / 400) * (E.ell ^ 2)⁻¹ := by
      field_simp
    have hD3 : (b₀ / 400) * (E.ell ^ 2)⁻¹ ≤ (E.b / 400) * (E.ell ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) hivl
    linarith [ha, hD1, hD2, hD3]
  refine ⟨hfinA, ?_⟩
  have hb1 : LamBound K₀ E * cbeta K₀ E * NPL E
      ≤ 12 * (2 : ℝ) ^ 15 * (K₀ + 1) * K₀ ^ 4 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) := by
    have h1 : LamBound K₀ E * cbeta K₀ E * NPL E
        ≤ 12 * (2 : ℝ) ^ 15 * (K₀ + 1) * K₀ ^ 3 * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹)
          * (K₀ * fsXp hv.t (-36)) :=
      mul_le_mul ha2 hNPLB hNPL0 (by positivity)
    have h2 : fsXp hv.t 94 * fsXp hv.t (-36) = fsXp hv.t 58 := by
      rw [fsXp_mul ht]; congr 1; norm_num
    calc LamBound K₀ E * cbeta K₀ E * NPL E
        ≤ 12 * (2 : ℝ) ^ 15 * (K₀ + 1) * K₀ ^ 3 * (fsXp hv.t 94 * (E.ell ^ 2)⁻¹)
          * (K₀ * fsXp hv.t (-36)) := h1
      _ = 12 * (2 : ℝ) ^ 15 * (K₀ + 1) * K₀ ^ 4 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) := by
          rw [← h2]; ring
  have hb2 : erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2
      ≤ 12 * (2 : ℝ) ^ 35 * K₀ ^ 7 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) := by
    have hbm2 : bm K₀ E + bm K₀ E ^ 2 ≤ 2 * bm K₀ E := by nlinarith [hbm0, hbm1]
    have h1 : erm K₀ E * LamBound K₀ E ≤
        (2 ^ 10 * bm K₀ E) * (12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹)) :=
      mul_le_mul hErmB hLamB hLam0 (by positivity)
    have h2 : erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2
        ≤ (2 ^ 10 * bm K₀ E) * (12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹))
          * (2 * bm K₀ E) * (K₀ * fsXp hv.t (-36)) ^ 2 := by
      have h4 : NPL E ^ 2 ≤ (K₀ * fsXp hv.t (-36)) ^ 2 :=
        pow_le_pow_left₀ hNPL0 hNPLB 2
      exact mul_le_mul (mul_le_mul h1 hbm2 (by positivity) (by positivity)) h4
        (by positivity) (by positivity)
    have h5 : (2 ^ 10 * bm K₀ E) * (12 * K₀ * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹))
          * (2 * bm K₀ E) * (K₀ * fsXp hv.t (-36)) ^ 2
        = 12 * (2 : ℝ) ^ 35 * K₀ ^ 7 * (fsXp hv.t 97 * fsXp hv.t 97 * fsXp hv.t (-3)
            * fsXp hv.t (-36) * fsXp hv.t (-36) * (E.ell ^ 2)⁻¹) := by
      rw [hBm]; ring
    have h6 : fsXp hv.t 97 * fsXp hv.t 97 * fsXp hv.t (-3) * fsXp hv.t (-36) * fsXp hv.t (-36)
        = fsXp hv.t 119 := by
      rw [fsXp_mul ht, fsXp_mul ht, fsXp_mul ht, fsXp_mul ht]
      congr 1; norm_num
    have h7 : fsXp hv.t 119 ≤ fsXp hv.t 58 := hmono 119 (by norm_num)
    have h8 : erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2
        ≤ 12 * (2 : ℝ) ^ 35 * K₀ ^ 7 * (fsXp hv.t 119 * (E.ell ^ 2)⁻¹) := by
      calc erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2
          ≤ 12 * (2 : ℝ) ^ 35 * K₀ ^ 7 * (fsXp hv.t 97 * fsXp hv.t 97 * fsXp hv.t (-3)
              * fsXp hv.t (-36) * fsXp hv.t (-36) * (E.ell ^ 2)⁻¹) := by
            rw [← h5]; exact h2
        _ = 12 * (2 : ℝ) ^ 35 * K₀ ^ 7 * (fsXp hv.t 119 * (E.ell ^ 2)⁻¹) := by rw [h6]
    calc erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2
        ≤ 12 * (2 : ℝ) ^ 35 * K₀ ^ 7 * (fsXp hv.t 119 * (E.ell ^ 2)⁻¹) := h8
      _ ≤ 12 * (2 : ℝ) ^ 35 * K₀ ^ 7 * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h7 hivl) (by positivity)
  have hfinB : LamBound K₀ E * cbeta K₀ E * NPL E
      + erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2
      ≤ ((2 : ℝ) ^ 40 * (K₀ + 1) ^ 8) * e1A E := by
    have h1 : LamBound K₀ E * cbeta K₀ E * NPL E
        + erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2
        ≤ (12 * (2 : ℝ) ^ 15 * (K₀ + 1) * K₀ ^ 4 + 12 * (2 : ℝ) ^ 35 * K₀ ^ 7)
          * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) := by
      have h2 : 0 ≤ fsXp hv.t 58 * (E.ell ^ 2)⁻¹ := mul_nonneg (hXnn 58) hivl
      nlinarith [hb1, hb2, h2]
    have h3 : (12 * (2 : ℝ) ^ 15 * (K₀ + 1) * K₀ ^ 4 + 12 * (2 : ℝ) ^ 35 * K₀ ^ 7)
        ≤ (2 : ℝ) ^ 40 * (K₀ + 1) ^ 8 := by
      have h4 : K₀ ^ 4 ≤ (K₀ + 1) ^ 8 := by
        have h5 : K₀ ^ 4 ≤ (K₀ + 1) ^ 4 := pow_le_pow_left₀ hk0 (by linarith) 4
        have h6 : (K₀ + 1) ^ 4 ≤ (K₀ + 1) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
        linarith
      have h7 : K₀ ^ 7 ≤ (K₀ + 1) ^ 8 := by
        have h5 : K₀ ^ 7 ≤ (K₀ + 1) ^ 7 := pow_le_pow_left₀ hk0 (by linarith) 7
        have h6 : (K₀ + 1) ^ 7 ≤ (K₀ + 1) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
        linarith
      nlinarith [h4, h7, hK1]
    have h4 : 0 ≤ fsXp hv.t 58 * (E.ell ^ 2)⁻¹ := mul_nonneg (hXnn 58) hivl
    have h5 := e1A_ge hv (lt_of_lt_of_le hb₀ hb)
    have h6 : (12 * (2 : ℝ) ^ 15 * (K₀ + 1) * K₀ ^ 4 + 12 * (2 : ℝ) ^ 35 * K₀ ^ 7)
          * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹)
        ≤ ((2 : ℝ) ^ 40 * (K₀ + 1) ^ 8) * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_right h3 h4
    have h7 : ((2 : ℝ) ^ 40 * (K₀ + 1) ^ 8) * (fsXp hv.t 58 * (E.ell ^ 2)⁻¹)
        ≤ ((2 : ℝ) ^ 40 * (K₀ + 1) ^ 8) * e1A E :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    linarith [h1, h6, h7]
  exact hfinB

end Est1

end Work.BoseC3QAll
