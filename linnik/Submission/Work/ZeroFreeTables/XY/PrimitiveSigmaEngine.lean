import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.Table4.Engine8A
import Submission.Work.ZeroFreeTables.Table4.HB83_base
import Submission.Work.ZeroFreeTables.P9.invNearSum_eq_tsum
import Submission.Work.ZeroFreeTables.P9.trivSeriesBound
import Submission.Work.LinnikAreas.ownRepelNW.completedLOrderShiftInvSqBound_rectFree
import Submission.Work.LinnikAreas.A5.LFunction_disc_zeroCount
import Submission.Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive

open DirichletCharacter Complex
open scoped Classical BigOperators
set_option maxHeartbeats 4000000
noncomputable section

namespace Work.ZeroFreeTables.XY

theorem invSqSum_bound_xy :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
      (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (s : ℂ), ‖s‖ ≤ 11 →
      Work.ZeroFreeTables.P9.invSqSum N χ s ≤ C * (Real.log (N : ℝ) + 2) := by
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.ownRepelNW.completedLOrderShiftInvSqBound_rectFree
  refine ⟨C, hCpos, ?_⟩
  intro N _ χ hχ hprim s hs
  have hnn : ∀ u : ℂ,
      0 ≤ (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)) := by
    intro u
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hsum : ∀ S : Finset ℂ, ∑ u ∈ S,
      (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))
      ≤ C * (Real.log (N : ℝ) + 2) := by
    intro S
    have h := hC N χ hχ hprim s hs S
    refine le_trans (le_of_eq ?_) h
    apply Finset.sum_congr rfl
    intro u _
    rw [Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u]
  have := Real.tsum_le_of_sum_le hnn hsum
  simpa [Work.ZeroFreeTables.P9.invSqSum] using this

theorem summable_triv_xy (k : ℕ) (hk : 2 ≤ k) {s : ℂ} (hs : (1 : ℝ) / 2 ≤ s.re) (par : ℕ) :
    Summable (fun n : ℕ => (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ k) := by
  have hbase : Summable (fun n : ℕ => (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k) := by
    have h0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) :=
      (Real.summable_one_div_nat_pow (p := k)).mpr (by omega)
    have h1 : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ k) :=
      (summable_nat_add_iff 1).mpr h0
    refine (h1.mul_left ((2 : ℝ) ^ k)).congr (fun n => ?_)
    rw [mul_one_div, Nat.cast_add, Nat.cast_one]
  refine Summable.of_norm_bounded hbase (fun n => ?_)
  set z : ℂ := s + ((par + 2 * n : ℕ) : ℂ) with hz
  have h1 : ((n : ℝ) + 1) / 2 ≤ ‖z‖ := by
    have hzre : z.re = s.re + ((par + 2 * n : ℕ) : ℝ) := by
      rw [hz, Complex.add_re, Complex.natCast_re]
    have h2 : ((par + 2 * n : ℕ) : ℝ) = (par : ℝ) + 2 * (n : ℝ) := by push_cast; ring
    have h3 : ((n : ℝ) + 1) / 2 ≤ z.re := by
      rw [hzre, h2]
      have : (0 : ℝ) ≤ (par : ℝ) := Nat.cast_nonneg par
      nlinarith [hs]
    calc ((n : ℝ) + 1) / 2 ≤ z.re := h3
      _ ≤ ‖z‖ := Complex.re_le_norm _
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by positivity
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hpos h1
  have hle : ‖z‖⁻¹ ≤ 2 / ((n : ℝ) + 1) := by
    rw [show (2 : ℝ) / ((n : ℝ) + 1) = (((n : ℝ) + 1) / 2)⁻¹ by rw [inv_div]]
    exact (inv_le_inv₀ hzpos hpos).mpr h1
  have hnorm : ‖(1 / z) ^ k‖ = (‖z‖⁻¹) ^ k := by
    rw [show (1 : ℂ) / z = z⁻¹ by simp, norm_pow, norm_inv]
  rw [hnorm, show (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k = (2 / ((n : ℝ) + 1)) ^ k by rw [div_pow]]
  exact pow_le_pow_left₀ (by positivity) hle k

theorem trivSeries_re_bound_xy :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ (s : ℂ) (par : ℕ), (1 : ℝ) / 2 ≤ s.re → par ≤ 1 →
      |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct ∧
      |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct := by
  obtain ⟨Ct, hCtpos, hCt⟩ := Work.ZeroFreeTables.P9.trivSeriesBound
  refine ⟨Ct, hCtpos, ?_⟩
  intro s par hs hpar
  obtain ⟨h2, h3⟩ := hCt s hs par hpar
  have key : ∀ k : ℕ, 2 ≤ k →
      |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ k)).re|
        ≤ ∑' n : ℕ, ‖(1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ k‖ := by
    intro k hk
    have hsumm := summable_triv_xy k hk hs par
    have hre : (∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ k)).re)
        = ((∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ k)).re :=
      (Complex.re_tsum hsumm).symm
    rw [hre]
    exact (Complex.abs_re_le_norm _).trans (norm_tsum_le_tsum_norm hsumm.norm)
  exact ⟨le_trans (key 2 (by norm_num)) h2, le_trans (key 3 (by norm_num)) h3⟩

theorem absorbAlphaError_xy {a δ e C Ct : ℝ} (ha : 0 < a) (he : 0 < e) (hδ : 0 < δ)
    (hC : 0 < C) (hCt : 0 < Ct) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ {L α J : ℝ}, L₀ ≤ L → 0 < α → α ≤ a + 1 → 0 ≤ J →
      J ≤ C * (L + 2) →
      α ^ 2 / L ^ 2 * ((1 + 4 / δ ^ 2) * J + Ct)
        + (2 / 3) * (α ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * J + Ct) ≤ α * e := by
  set D : ℝ := 1 + 4 / δ ^ 2 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  set E : ℝ := (2 / δ) * D with hE
  have hEpos : 0 < E := by rw [hE]; positivity
  set M1 : ℝ := 3 * D * C + Ct with hM1
  have hM1pos : 0 < M1 := by rw [hM1]; positivity
  set M2 : ℝ := (2 / 3) * (3 * E * C + Ct) with hM2
  have hM2pos : 0 < M2 := by rw [hM2]; positivity
  refine ⟨max 1 (max (2 * (a + 1) * M1 / e) (2 * (a + 1) ^ 2 * M2 / e)), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  intro L α J hL hα0 hα hJ hJL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hL1
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hrest : max (2 * (a + 1) * M1 / e) (2 * (a + 1) ^ 2 * M2 / e) ≤ L :=
    le_trans (le_max_right _ _) hL
  have hLa : 2 * (a + 1) * M1 / e ≤ L := le_trans (le_max_left _ _) hrest
  have hLb : 2 * (a + 1) ^ 2 * M2 / e ≤ L := le_trans (le_max_right _ _) hrest
  have hb1 : (a + 1) * M1 / L ≤ e / 2 := by
    rw [div_le_iff₀ hLpos]
    have h := (div_le_iff₀ he).mp hLa
    linarith
  have hb2 : (a + 1) ^ 2 * M2 / L ^ 2 ≤ e / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h := (div_le_iff₀ he).mp hLb
    have hL2 : L ≤ L ^ 2 := by nlinarith
    nlinarith
  have hDJ : D * J + Ct ≤ L * M1 := by
    rw [hM1]
    have h1 : D * J ≤ D * (C * (L + 2)) := mul_le_mul_of_nonneg_left hJL hDpos.le
    have h2 : (L : ℝ) + 2 ≤ 3 * L := by linarith
    have h3 : D * (C * (L + 2)) ≤ D * (C * (3 * L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC.le) hDpos.le
    have h4 : Ct ≤ Ct * L := by nlinarith
    nlinarith [h1, h3, h4]
  have hEJ : E * J + Ct ≤ L * (3 * E * C + Ct) := by
    have h1 : E * J ≤ E * (C * (L + 2)) := mul_le_mul_of_nonneg_left hJL hEpos.le
    have h2 : (L : ℝ) + 2 ≤ 3 * L := by linarith
    have h3 : E * (C * (L + 2)) ≤ E * (C * (3 * L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC.le) hEpos.le
    have h4 : Ct ≤ Ct * L := by nlinarith
    nlinarith [h1, h3, h4]
  have hα2 : α ^ 2 ≤ α * (a + 1) := by
    calc α ^ 2 = α * α := by ring
      _ ≤ α * (a + 1) := mul_le_mul_of_nonneg_left hα hα0.le
  have hα3 : α ^ 3 ≤ α * (a + 1) ^ 2 := by
    have h1 : α ^ 2 ≤ (a + 1) ^ 2 := pow_le_pow_left₀ hα0.le hα 2
    calc α ^ 3 = α * α ^ 2 := by ring
      _ ≤ α * (a + 1) ^ 2 := mul_le_mul_of_nonneg_left h1 hα0.le
  have hA2 : α ^ 2 / L ^ 2 * (D * J + Ct) ≤ α * ((a + 1) * M1 / L) := by
    have h3 : α ^ 2 / L ^ 2 * (D * J + Ct) ≤ α ^ 2 / L ^ 2 * (L * M1) :=
      mul_le_mul_of_nonneg_left hDJ (by positivity)
    have h4 : α ^ 2 / L ^ 2 * (L * M1) = α ^ 2 * M1 / L := by
      field_simp [hLne]
    have h5 : α ^ 2 * M1 / L ≤ α * ((a + 1) * M1 / L) := by
      rw [show α * ((a + 1) * M1 / L) = α * (a + 1) * M1 / L by ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hα2 hM1pos.le) hLpos.le
    linarith [h3, h4]
  have hA3 : (2 / 3) * (α ^ 3 / L ^ 3) * (E * J + Ct) ≤ α * ((a + 1) ^ 2 * M2 / L ^ 2) := by
    have h3 : (2 / 3) * (α ^ 3 / L ^ 3) * (E * J + Ct)
        ≤ (2 / 3) * (α ^ 3 / L ^ 3) * (L * (3 * E * C + Ct)) :=
      mul_le_mul_of_nonneg_left hEJ (by positivity)
    have h4 : (2 / 3) * (α ^ 3 / L ^ 3) * (L * (3 * E * C + Ct)) = α ^ 3 * M2 / L ^ 2 := by
      rw [hM2]; field_simp [hLne]
    have h5 : α ^ 3 * M2 / L ^ 2 ≤ α * ((a + 1) ^ 2 * M2 / L ^ 2) := by
      rw [show α * ((a + 1) ^ 2 * M2 / L ^ 2) = α * (a + 1) ^ 2 * M2 / L ^ 2 by ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hα3 hM2pos.le) (by positivity)
    linarith [h3, h4]
  have hmain : α ^ 2 / L ^ 2 * (D * J + Ct) + (2 / 3) * (α ^ 3 / L ^ 3) * (E * J + Ct)
      ≤ α * ((a + 1) * M1 / L + (a + 1) ^ 2 * M2 / L ^ 2) := by
    have hsplit : α * ((a + 1) * M1 / L) + α * ((a + 1) ^ 2 * M2 / L ^ 2)
        = α * ((a + 1) * M1 / L + (a + 1) ^ 2 * M2 / L ^ 2) := by ring
    linarith [hA2, hA3, hsplit]
  have hfin : (a + 1) * M1 / L + (a + 1) ^ 2 * M2 / L ^ 2 ≤ e := by linarith [hb1, hb2]
  linarith [hmain, mul_le_mul_of_nonneg_left hfin hα0.le]

theorem PrimitiveSigmaEngine {a δ c e : ℝ} (ha : 0 < a) (hδ0 : 0 < δ) (hδ1 : δ < 1) (he : 0 < e)
    (hc : 0 ≤ c) :
    ∃ L₀ : ℝ, ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hprim : χ.IsPrimitive) {L lam₁ : ℝ}, L₀ ≤ L → Real.log (N : ℝ) ≤ L → 0 ≤ lam₁ →
      lam₁ ≤ 1 → Work.ZeroFreeTables.LogDerivHyp χ δ L c →
      ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 3 →
        Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
          ≤ - Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ + (a + lam₁) * (c + e) := by
  obtain ⟨C, hCpos, hCbound⟩ := invSqSum_bound_xy
  obtain ⟨Ct, hCtpos, hCtbound⟩ := trivSeries_re_bound_xy
  obtain ⟨La, hLapos, hLabs⟩ :=
    absorbAlphaError_xy (a := a) (δ := δ) (e := e) (C := C) (Ct := Ct) ha he hδ0 hCpos hCtpos
  set L0 : ℝ := max La (max 3 (max (Real.exp a) (max (Real.exp (1 / a)) (max (2 * a / δ + 1) a))))
    with hL0
  refine ⟨L0, ?_⟩
  intro N _ χ hχ hprim L lam₁ hL hlogNL hlam0 hlam1 hLDH s hsre hsim
  rw [hL0] at hL
  have hLLa : La ≤ L := le_trans (le_max_left _ _) hL
  have hrest : max 3 (max (Real.exp a) (max (Real.exp (1 / a)) (max (2 * a / δ + 1) a))) ≤ L :=
    le_trans (le_max_right _ _) hL
  have hL3 : 3 ≤ L := le_trans (le_max_left _ _) hrest
  have hrest2 : max (Real.exp a) (max (Real.exp (1 / a)) (max (2 * a / δ + 1) a)) ≤ L :=
    le_trans (le_max_right _ _) hrest
  have hexpa : Real.exp a ≤ L := le_trans (le_max_left _ _) hrest2
  have hrest3 : max (Real.exp (1 / a)) (max (2 * a / δ + 1) a) ≤ L :=
    le_trans (le_max_right _ _) hrest2
  have hexp1a : Real.exp (1 / a) ≤ L := le_trans (le_max_left _ _) hrest3
  have hrest4 : max (2 * a / δ + 1) a ≤ L := le_trans (le_max_right _ _) hrest3
  have hLd : 2 * a / δ + 1 ≤ L := le_trans (le_max_left _ _) hrest4
  have hLae : a ≤ L := le_trans (le_max_right _ _) hrest4
  have hLpos : 0 < L := by linarith
  have hLt : 1 < L := by linarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
    exact Real.log_nonneg h1
  have hlogLa : a ≤ Real.log L := by
    have h1 : Real.log (Real.exp a) ≤ Real.log L := Real.log_le_log (Real.exp_pos a) hexpa
    rwa [Real.log_exp] at h1
  have hlogL1a : 1 / a ≤ Real.log L := by
    have h1 : Real.log (Real.exp (1 / a)) ≤ Real.log L :=
      Real.log_le_log (Real.exp_pos (1 / a)) hexp1a
    rwa [Real.log_exp] at h1
  have hδL : 2 * a ≤ δ * L := by
    have h1 : δ * (2 * a / δ + 1) ≤ δ * L := mul_le_mul_of_nonneg_left hLd hδ0.le
    have h2 : δ * (2 * a / δ + 1) = 2 * a + δ := by
      field_simp [ne_of_gt hδ0]
    linarith [h1, h2]
  have hlogLpos : 0 < Real.log L :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 3))
      (Real.log_le_log (by norm_num : (0 : ℝ) < 3) hL3)
  have hre_lo : 1 + 1 / (L * Real.log L) ≤ s.re := by
    rw [hsre]
    have hden : 0 < L * Real.log L := mul_pos hLpos hlogLpos
    have h1 : 1 / (L * Real.log L) ≤ a / L := by
      rw [div_le_div_iff₀ hden hLpos]
      have h3 := (div_le_iff₀ ha).mp hlogL1a
      rw [mul_comm] at h3
      nlinarith [h3]
    linarith
  have hre_hi : s.re ≤ 1 + Real.log L / L := by
    rw [hsre]
    have h1 : a / L ≤ Real.log L / L := by
      rw [div_le_div_iff₀ hLpos hLpos]
      exact mul_le_mul_of_nonneg_right hlogLa hLpos.le
    linarith
  have hre_im : |s.im| ≤ L := by linarith [hsim, hL3]
  have hlog' : (-logDeriv (DirichletCharacter.LFunction χ) s).re
      + Work.ZeroFreeTables.P9.nearInvSum N χ s δ ≤ c * L := by
    have h := hLDH s hre_lo hre_hi hre_im
    rw [Work.ZeroFreeTables.P9.invNearSum_eq_tsum (s := s) (δ := δ) χ hχ hprim
      (by linarith) hδ0 (le_of_lt hδ1)] at h
    exact h
  set par : ℕ := if χ.Even then 0 else 1 with hpar
  have hpar0 : χ.Even → par = 0 := by intro hE; rw [hpar]; simp [hE]
  have hpar1 : χ.Odd → par = 1 := by
    intro hO
    rw [hpar]
    have hne : ¬ χ.Even := by
      intro hE
      have h1 : χ (-1) = 1 := hE
      have h2 : χ (-1) = -1 := hO
      rw [h1] at h2
      norm_num at h2
    simp [hne]
  have hparle : par ≤ 1 := by
    rw [hpar]
    by_cases hE : χ.Even <;> simp [hE]
  have hsre_half : (1 : ℝ) / 2 ≤ s.re := by
    rw [hsre]
    have h : 0 ≤ a / L := div_nonneg ha.le hLpos.le
    linarith
  have hS2 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct :=
    (hCtbound s par hsre_half hparle).1
  have hS3 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct :=
    (hCtbound s par hsre_half hparle).2
  have hE8 := Work.ZeroFreeTables.Table4.engine8 (a := a) (lam₁ := lam₁) (δ := δ) (c := c)
    (L := L) (Ct := Ct) χ hχ hprim ha hlam0 hδ0 hδ1 hLt hδL hsre (by linarith) hlog' par
    hpar0 hpar1 hS2 hS3
  have hnorm11 : ‖s‖ ≤ 11 := by
    have hre0 : 0 ≤ s.re := by rw [hsre]; positivity
    have hre2 : s.re ≤ 2 := by
      rw [hsre]
      have h1 : a / L ≤ 1 := (div_le_one hLpos).mpr hLae
      linarith
    have hsq : Complex.normSq s ≤ 121 := by
      rw [Complex.normSq_apply]
      have him := abs_le.mp hsim
      nlinarith [hre0, hre2, him.1, him.2]
    have h2 : ‖s‖ ^ 2 = Complex.normSq s := Complex.sq_norm s
    nlinarith [norm_nonneg s]
  have hJ : Work.ZeroFreeTables.P9.invSqSum N χ s ≤ C * (L + 2) := by
    have h := hCbound χ hχ hprim s hnorm11
    have h1 : C * (Real.log (N : ℝ) + 2) ≤ C * (L + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hCpos.le
    linarith
  have hJnn : 0 ≤ Work.ZeroFreeTables.P9.invSqSum N χ s := by
    unfold Work.ZeroFreeTables.P9.invSqSum
    exact tsum_nonneg (fun u => mul_nonneg (Nat.cast_nonneg _) (by positivity))
  have habs := hLabs (L := L) (α := a + lam₁) (J := Work.ZeroFreeTables.P9.invSqSum N χ s)
    hLLa (by linarith) (by linarith) hJnn hJ
  calc Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      ≤ -Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ + (a + lam₁) * c +
          (a + lam₁) ^ 2 / L ^ 2 *
            ((1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct) +
          2 / 3 * ((a + lam₁) ^ 3 / L ^ 3) *
            (2 / δ * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct) := hE8
    _ ≤ -Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ + (a + lam₁) * c
          + (a + lam₁) * e := by linarith [habs]
    _ = -Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ + (a + lam₁) * (c + e) := by ring

end Work.ZeroFreeTables.XY
