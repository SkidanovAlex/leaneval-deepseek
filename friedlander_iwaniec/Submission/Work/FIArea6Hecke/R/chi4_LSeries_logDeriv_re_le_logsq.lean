import Mathlib
import Submission.Work.FIArea6Hecke.R.PrincipalCharAux
import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_region_awayFromAxis
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_inv_le_logPow_zeroFree
import Submission.Commons.NumberTheory.LSeries.exists_bound_LFunction_chi4_near_one
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open Complex Filter Metric Set
open scoped Real Topology BigOperators

open Commons.NumberTheory.DirichletCharacter (chi4 chi4Fun chi4_apply chi4Fun_zero chi4Fun_one
  chi4Fun_two chi4Fun_three zmod_four_eq LFunction_zeroFree_region_awayFromAxis
  LFunction_inv_le_logPow_zeroFree)

noncomputable section

/-! ## Elementary facts about `χ₄` -/

private lemma isUnit_three_four_local : IsUnit (3 : ZMod 4) := by
  rw [isUnit_iff_exists_inv]
  exact ⟨3, by decide⟩

private lemma chi4_apply_three_local : chi4 (3 : ZMod 4) = -1 := by
  rw [chi4_apply, chi4Fun_three]

private lemma chi4_ne_one_local : chi4 ≠ (1 : DirichletCharacter ℂ 4) := by
  intro h
  have h1 : chi4 (3 : ZMod 4) = (1 : DirichletCharacter ℂ 4) (3 : ZMod 4) := by rw [h]
  rw [chi4_apply_three_local, MulChar.one_apply isUnit_three_four_local] at h1
  norm_num at h1

private lemma chi4_isPrim_local : chi4.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd : chi4.conductor ∣ 4 := DirichletCharacter.conductor_dvd_level chi4
  have hne1 : chi4.conductor ≠ 1 := by
    intro h
    have : chi4 = (1 : DirichletCharacter ℂ 4) :=
      (DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h
    exact chi4_ne_one_local this
  have hne2 : chi4.conductor ≠ 2 := by
    intro h
    have hfac : DirichletCharacter.FactorsThrough chi4 2 := by
      rw [← h]; exact DirichletCharacter.conductor_mem_conductorSet chi4
    obtain ⟨hd, χ₀, hχ⟩ := hfac
    have h1 : (DirichletCharacter.changeLevel hd χ₀) ((3 : ℤ) : ZMod 4)
        = χ₀ ((3 : ℤ) : ZMod 2) :=
      DirichletCharacter.changeLevel_eq_cast_of_dvd' (χ := χ₀) hd (by norm_num)
    have h2 : χ₀ (((3 : ℤ)) : ZMod 2) = (1 : ℂ) := by
      have : (((3 : ℤ)) : ZMod 2) = 1 := by decide
      rw [this, MulChar.map_one]
    have h3 : chi4 (3 : ZMod 4) = 1 := by
      rw [hχ]
      exact h1.trans h2
    rw [chi4_apply_three_local] at h3
    norm_num at h3
  obtain ⟨n, hn, hc⟩ : ∃ n ≤ 2, chi4.conductor = 2 ^ n :=
    (Nat.dvd_prime_pow (p := 2) (by norm_num)).mp (by simpa using hdvd)
  interval_cases n
  · exact absurd hc hne1
  · exact absurd hc hne2
  · rw [hc]; norm_num

private lemma chi4Fun_eq_zmod (a : ZMod 4) :
    chi4Fun a = ((ZMod.χ₄ a : ℤ) : ℂ) := by
  rcases zmod_four_eq a with rfl | rfl | rfl | rfl
  · simp [chi4Fun_zero, show ZMod.χ₄ (0 : ZMod 4) = 0 from by decide]
  · simp [chi4Fun_one]
  · simp [chi4Fun_two, show ZMod.χ₄ (2 : ZMod 4) = 0 from by decide]
  · simp [chi4Fun_three, show ZMod.χ₄ (3 : ZMod 4) = -1 from by decide]

private lemma chi4fun_eq_chi4 (n : ℕ) :
    Work.FIArea6Hecke.R.chi4fun n = chi4 (n : ZMod 4) := by
  rw [Work.FIArea6Hecke.R.chi4fun, chi4_apply, chi4Fun_eq_zmod]

private lemma LSeries_chi4fun_eq (s : ℂ) (hs : 1 < s.re) :
    LSeries Work.FIArea6Hecke.R.chi4fun s
      = DirichletCharacter.LFunction chi4 s := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi4 hs]
  refine LSeries_congr (f := Work.FIArea6Hecke.R.chi4fun)
    (g := fun n : ℕ => chi4 (n : ZMod 4)) ?_ s
  intro n hn
  exact chi4fun_eq_chi4 n

/-! ## The compact-region bound -/

private lemma logDeriv_LFunction_chi4_compact :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, 1 ≤ z.re → z.re ≤ 2 → |z.im| ≤ 3 →
      ‖logDeriv (DirichletCharacter.LFunction chi4) z‖ ≤ B := by
  set Kset : Set ℂ := {z : ℂ | 1 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 3} with hKset
  have hKclosed : IsClosed Kset := by
    have h1 : IsClosed {z : ℂ | (1 : ℝ) ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {z : ℂ | z.re ≤ (2 : ℝ)} := isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {z : ℂ | |z.im| ≤ (3 : ℝ)} :=
      isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    have hEq : Kset = {z : ℂ | (1 : ℝ) ≤ z.re} ∩ {z : ℂ | z.re ≤ (2 : ℝ)}
        ∩ {z : ℂ | |z.im| ≤ (3 : ℝ)} := by
      ext z; simp only [hKset, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
    rw [hEq]
    exact (h1.inter h2).inter h3
  have hKbdd : Bornology.IsBounded Kset := by
    refine isBounded_iff_forall_norm_le.mpr ⟨5, ?_⟩
    intro z hz
    rw [hKset] at hz
    obtain ⟨hz1, hz2, hz3⟩ := hz
    have h4 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    have h5 : |z.re| = z.re := abs_of_nonneg (by linarith)
    rw [h5] at h4
    linarith
  have hKcompact : IsCompact Kset := (Metric.isCompact_iff_isClosed_bounded).mpr ⟨hKclosed, hKbdd⟩
  have hdiff : Differentiable ℂ (DirichletCharacter.LFunction chi4) :=
    DirichletCharacter.differentiable_LFunction chi4_ne_one_local
  have hne : ∀ z ∈ Kset, DirichletCharacter.LFunction chi4 z ≠ 0 := by
    intro z hz
    rw [hKset] at hz
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi4 (Or.inl chi4_ne_one_local) hz.1
  have hcont : ContinuousOn (logDeriv (DirichletCharacter.LFunction chi4)) Kset := by
    rw [show logDeriv (DirichletCharacter.LFunction chi4)
        = fun z : ℂ => deriv (DirichletCharacter.LFunction chi4) z
            / DirichletCharacter.LFunction chi4 z from rfl]
    exact ContinuousOn.div (hdiff.deriv.continuous.continuousOn) (hdiff.continuous.continuousOn) hne
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz1 hz2 hz3
  have hzK : z ∈ Kset := by rw [hKset]; exact ⟨hz1, hz2, hz3⟩
  exact le_trans (hC z hzK) (le_max_left _ _)

/-! ## The main analytic bound for large `|Im s|` -/

private theorem logDeriv_LFunction_chi4_bound_large :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → 3 ≤ |t| →
      ‖logDeriv (DirichletCharacter.LFunction chi4) ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (Real.log (|t| + 3)) ^ (2 : ℕ) := by
  obtain ⟨c_zf, hczf, hZ⟩ :=
    LFunction_zeroFree_region_awayFromAxis chi4 chi4_isPrim_local chi4_ne_one_local
  obtain ⟨C₁, c₁, hC₁, hc₁, hS⟩ :=
    Commons.NumberTheory.LSeries.exists_bound_LFunction_chi4_near_one
  obtain ⟨c₂, C₂, hc₂, hC₂, hInv⟩ :=
    LFunction_inv_le_logPow_zeroFree chi4 chi4_ne_one_local chi4_isPrim_local
  set cmin : ℝ := min (min c_zf c₁) (min c₂ 1) with hcmin
  have hcmin0 : 0 < cmin := by
    rw [hcmin]; exact lt_min (lt_min hczf hc₁) (lt_min hc₂ one_pos)
  have hcmin1 : cmin ≤ 1 := by
    rw [hcmin]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hcminzf : cmin ≤ c_zf := by
    rw [hcmin]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hcminc₁ : cmin ≤ c₁ := by
    rw [hcmin]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  set K : ℝ := Real.log (2 * (1 + C₁)) + |Real.log C₂| + C₂ * Real.log 4 + 1 with hK
  have hKpos : 0 < K := by
    have h1 : 0 < Real.log (2 * (1 + C₁)) := Real.log_pos (by linarith)
    have h2 : 0 ≤ |Real.log C₂| := abs_nonneg _
    have h3 : 0 ≤ C₂ * Real.log 4 := mul_nonneg hC₂.le (Real.log_nonneg (by norm_num))
    rw [hK]; linarith
  have hCpos : 0 < 128 * (3 * K + 1 + C₂) / cmin := by
    apply div_pos _ hcmin0
    linarith [hKpos, hC₂]
  refine ⟨128 * (3 * K + 1 + C₂) / cmin, hCpos, ?_⟩
  intro σ t hσ1 hσ2 ht3
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have ht1 : 1 ≤ |t| := by linarith
  set L : ℝ := Real.log (|t| + 3) with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    have h3 : (3 : ℝ) ≤ |t| + 3 := by linarith [abs_nonneg t]
    have hexp : Real.exp 1 ≤ |t| + 3 := le_trans (le_of_lt Real.exp_one_lt_three) h3
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (|t| + 3) := Real.log_le_log (Real.exp_pos 1) hexp
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  set R : ℝ := cmin / (8 * (L + 1)) with hR
  have hRpos : 0 < R := by
    rw [hR]; exact div_pos hcmin0 (by linarith)
  have hRle : R ≤ 1 / 8 := by
    rw [hR, div_le_iff₀ (by linarith)]
    nlinarith [hcmin1, hL1]
  have hZ_s : DirichletCharacter.LFunction chi4 s ≠ 0 := by
    have h2 : 1 - c_zf / Real.log (4 * (|t| + 2)) ≤ σ := by
      have h3 : 0 < c_zf / Real.log (4 * (|t| + 2)) :=
        div_pos hczf (Real.log_pos (by linarith [abs_nonneg t]))
      linarith
    have h4 := hZ σ t ht1 h2
    rwa [← hs] at h4
  set X : ℝ := max 1 (C₂ * (Real.log (4 * (|t| + 2)) + 1) ^ C₂) with hX
  have hXpos : 0 < X := by rw [hX]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  have hbase : 0 < Real.log (4 * (|t| + 2)) + 1 := by
    have h3 : (1 : ℝ) < 4 * (|t| + 2) := by
      have h4 : (0 : ℝ) ≤ |t| := abs_nonneg t
      linarith
    have h5 := Real.log_pos h3
    linarith
  set m : ℝ := 1 / X with hm
  set M : ℝ := 1 + C₁ * L with hM
  have hmpos : 0 < m := by rw [hm]; exact div_pos one_pos hXpos
  have hMpos : 0 < M := by rw [hM]; positivity
  have hmM : m ≤ M := by
    rw [hm, hM]
    have hle1 : 1 / X ≤ 1 := by
      rw [div_le_one hXpos]
      exact le_max_left _ _
    have hle2 : (1 : ℝ) ≤ 1 + C₁ * L := by
      have h3 : 0 ≤ C₁ * L := mul_nonneg hC₁.le hLpos.le
      linarith
    linarith
  have hgm : m ≤ ‖DirichletCharacter.LFunction chi4 s‖ := by
    have hnormpos : 0 < ‖DirichletCharacter.LFunction chi4 s‖ :=
      norm_pos_iff.mpr hZ_s
    have hInv_s : 1 / ‖DirichletCharacter.LFunction chi4 s‖
        ≤ C₂ * (Real.log (4 * (|t| + 2)) + 1) ^ C₂ := by
      have h2 : 1 - c₂ / Real.log (4 * (|t| + 2)) ≤ σ := by
        have h3 : 0 < c₂ / Real.log (4 * (|t| + 2)) :=
          div_pos hc₂ (Real.log_pos (by linarith [abs_nonneg t]))
        linarith
      have h4 := hInv σ t ht1 h2 hσ2
      rwa [← hs] at h4
    have hkey : 1 ≤ (C₂ * (Real.log (4 * (|t| + 2)) + 1) ^ C₂)
        * ‖DirichletCharacter.LFunction chi4 s‖ := by
      have := (div_le_iff₀ hnormpos).mp hInv_s
      linarith [this]
    have hdenpos : 0 < C₂ * (Real.log (4 * (|t| + 2)) + 1) ^ C₂ :=
      mul_pos hC₂ (Real.rpow_pos_of_pos hbase C₂)
    have hstep : 1 / (C₂ * (Real.log (4 * (|t| + 2)) + 1) ^ C₂)
        ≤ ‖DirichletCharacter.LFunction chi4 s‖ := by
      rw [div_le_iff₀ hdenpos]
      calc (1 : ℝ) ≤ (C₂ * (Real.log (4 * (|t| + 2)) + 1) ^ C₂)
            * ‖DirichletCharacter.LFunction chi4 s‖ := hkey
        _ = ‖DirichletCharacter.LFunction chi4 s‖
            * (C₂ * (Real.log (4 * (|t| + 2)) + 1) ^ C₂) := by ring
    rw [hm]
    refine le_trans ?_ hstep
    rw [hX]
    exact one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos hbase C₂ |> fun h => mul_pos hC₂ h) (le_max_right _ _)
  have hgan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction chi4) (Metric.ball s R) :=
    (DirichletCharacter.differentiable_LFunction chi4_ne_one_local).differentiableOn.analyticOnNhd
      Metric.isOpen_ball
  have hball_facts : ∀ w : ℂ, w ∈ Metric.ball s R →
      DirichletCharacter.LFunction chi4 w ≠ 0
        ∧ ‖DirichletCharacter.LFunction chi4 w‖ ≤ M := by
    intro w hw
    have hwlt : ‖w - s‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hre : |w.re - σ| < R := by
      have h1 : |(w - s).re| ≤ ‖w - s‖ := Complex.abs_re_le_norm _
      have h2 : (w - s).re = w.re - σ := by simp [hs]
      rw [h2] at h1
      exact lt_of_le_of_lt h1 hwlt
    have him : |w.im - t| < R := by
      have h1 : |(w - s).im| ≤ ‖w - s‖ := Complex.abs_im_le_norm _
      have h2 : (w - s).im = w.im - t := by simp [hs]
      rw [h2] at h1
      exact lt_of_le_of_lt h1 hwlt
    have hwre : σ - R < w.re := by
      have h3 := (abs_lt.mp hre).1
      linarith
    have hwim1 : 1 ≤ |w.im| := by
      have h0 : w.im - (w.im - t) = t := by ring
      have h1 : |t| ≤ |w.im| + |w.im - t| := by
        calc |t| = |w.im - (w.im - t)| := by rw [h0]
          _ = |w.im + -(w.im - t)| := by ring_nf
          _ ≤ |w.im| + |-(w.im - t)| := abs_add_le _ _
          _ = |w.im| + |w.im - t| := by rw [abs_neg]
      linarith [le_of_lt him, hRle, ht3]
    have hwim2 : |w.im| + 2 ≤ |t| + 3 := by
      have h1 : |w.im| ≤ |w.im - t| + |t| := by
        calc |w.im| = |(w.im - t) + t| := by ring
          _ ≤ |w.im - t| + |t| := abs_add_le _ _
      linarith [le_of_lt him, hRle]
    have himpos : 0 < |w.im| + 2 := by linarith [abs_nonneg w.im]
    have hlog4pos : 0 < Real.log (4 * (|w.im| + 2)) :=
      Real.log_pos (by linarith : (1 : ℝ) < 4 * (|w.im| + 2))
    have hlog4_ub : Real.log (4 * (|w.im| + 2)) ≤ 8 * (L + 1) := by
      have hle : 4 * (|w.im| + 2) ≤ 4 * (|t| + 3) := by linarith
      have h2 := Real.log_le_log (by linarith) hle
      have h3 : Real.log (4 * (|t| + 3)) = Real.log 4 + L := by
        rw [hL, Real.log_mul (by norm_num) (by linarith)]
      have h4 : Real.log 4 ≤ 2 := by
        have h5 : Real.log (2 : ℝ) ≤ 1 := by
          have h6 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
          linarith
        have h6 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 * 2 by norm_num,
            Real.log_mul (by norm_num) (by norm_num)]
          ring
        linarith
      rw [h3] at h2
      linarith [hL1]
    have hle_log : Real.log (|w.im| + 2) ≤ L := by
      rw [hL]
      exact Real.log_le_log himpos hwim2
    have hlogpos2 : 0 < 8 * (L + 1) := by linarith
    have hkey : cmin / (8 * (L + 1)) ≤ c_zf / Real.log (4 * (|w.im| + 2)) := by
      rw [div_le_div_iff₀ hlogpos2 hlog4pos]
      have h1 : cmin * Real.log (4 * (|w.im| + 2)) ≤ cmin * (8 * (L + 1)) :=
        mul_le_mul_of_nonneg_left hlog4_ub hcmin0.le
      have h2 : cmin * (8 * (L + 1)) ≤ c_zf * (8 * (L + 1)) :=
        mul_le_mul_of_nonneg_right hcminzf hlogpos2.le
      linarith
    have hkey2 : cmin / (8 * (L + 1)) ≤ c₁ / Real.log (|w.im| + 2) := by
      have hlogpos3 : 0 < Real.log (|w.im| + 2) :=
        Real.log_pos (by linarith : (1 : ℝ) < |w.im| + 2)
      rw [div_le_div_iff₀ hlogpos2 hlogpos3]
      have h1 : cmin * Real.log (|w.im| + 2) ≤ cmin * (8 * (L + 1)) := by
        have hle : Real.log (|w.im| + 2) ≤ 8 * (L + 1) := by linarith
        exact mul_le_mul_of_nonneg_left hle hcmin0.le
      have h2 : cmin * (8 * (L + 1)) ≤ c₁ * (8 * (L + 1)) :=
        mul_le_mul_of_nonneg_right hcminc₁ hlogpos2.le
      linarith
    constructor
    · have h2 : 1 - c_zf / Real.log (4 * (|w.im| + 2)) ≤ w.re := by
        rw [← hR] at hkey
        linarith [hkey, hwre]
      have h3 := hZ w.re w.im hwim1 h2
      rwa [show ((w.re : ℂ) + (w.im : ℂ) * Complex.I) = w from by
        apply Complex.ext <;> simp] at h3
    · have h2 : 1 - c₁ / Real.log (|w.im| + 2) ≤ w.re := by
        rw [← hR] at hkey2
        linarith [hkey2, hwre]
      have h3 := hS w.re w.im hwim1 h2
      rw [show ((w.re : ℂ) + (w.im : ℂ) * Complex.I) = w from by
        apply Complex.ext <;> simp] at h3
      have h4 : C₁ * Real.log (|w.im| + 2) ≤ C₁ * L := mul_le_mul_of_nonneg_left hle_log hC₁.le
      rw [hM]
      linarith
  have hgne : ∀ w : ℂ, w ∈ Metric.ball s R → DirichletCharacter.LFunction chi4 w ≠ 0 :=
    fun w hw => (hball_facts w hw).1
  have hgM : ∀ w : ℂ, w ∈ Metric.ball s R → ‖DirichletCharacter.LFunction chi4 w‖ ≤ M :=
    fun w hw => (hball_facts w hw).2
  have hball := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
    (g := DirichletCharacter.LFunction chi4) (c := s) (R := R) (m := m) (M := M)
    hRpos hmpos hmM hgan hgne hgM hgm
    (z₀ := s) (by rw [Metric.mem_ball, dist_self]; exact hRpos)
    (ρ := R / 2) (by linarith) (by simp only [sub_self, norm_zero]; linarith)
  have hstep1 : ‖logDeriv (DirichletCharacter.LFunction chi4) s‖
      ≤ 4 * (Real.log (2 * M) - Real.log m) / R := by
    simp only [sub_self, norm_zero, zero_add, sub_zero] at hball
    have hR2 : R - R / 2 = R / 2 := by ring
    rw [hR2] at hball
    have hfac : 2 * (Real.log (2 * M) - Real.log m) * (R / 2) / ((R / 2) * (R / 2))
        = 4 * (Real.log (2 * M) - Real.log m) / R := by
      field_simp
      ring
    rw [hfac] at hball
    rw [logDeriv_apply]
    exact hball
  have hA_le : Real.log (2 * M) - Real.log m ≤ (3 * K + 1 + C₂) * (1 + L) := by
    have hM2 : 2 * M ≤ 2 * (1 + C₁) * (1 + L) := by
      rw [hM]; nlinarith [hC₁.le, hLpos.le]
    have hlog2M : Real.log (2 * M) ≤ Real.log (2 * (1 + C₁)) + Real.log (1 + L) := by
      have h1 : Real.log (2 * M) ≤ Real.log (2 * (1 + C₁) * (1 + L)) :=
        Real.log_le_log (by rw [hM]; positivity) hM2
      calc Real.log (2 * M) ≤ Real.log (2 * (1 + C₁) * (1 + L)) := h1
        _ = Real.log (2 * (1 + C₁)) + Real.log (1 + L) := by
            rw [Real.log_mul (by positivity) (by linarith)]
    have hXbound : Real.log X
        ≤ |Real.log C₂| + C₂ * Real.log 4 + C₂ * Real.log (1 + L) := by
      have h1 : Real.log X
          ≤ max 0 (Real.log (C₂ * (Real.log (4 * (|t| + 2)) + 1) ^ C₂)) := by
        rw [hX]
        by_cases h : C₂ * (Real.log (4 * (|t| + 2)) + 1) ^ C₂ ≤ 1
        · rw [max_eq_left h, Real.log_one]; exact le_max_left _ _
        · rw [max_eq_right (le_of_lt (not_le.mp h))]; exact le_max_right _ _
      have h2 : Real.log (C₂ * (Real.log (4 * (|t| + 2)) + 1) ^ C₂)
          = Real.log C₂ + C₂ * Real.log (Real.log (4 * (|t| + 2)) + 1) := by
        rw [Real.log_mul hC₂.ne' (Real.rpow_pos_of_pos hbase C₂).ne', Real.log_rpow hbase]
      have h3 : Real.log C₂ ≤ |Real.log C₂| := le_abs_self _
      have h4 : Real.log (4 * (|t| + 2)) ≤ 2 * L := by
        have hsq : 4 * (|t| + 2) ≤ (|t| + 3) ^ 2 := by nlinarith [abs_nonneg t]
        have h1 : Real.log (4 * (|t| + 2)) ≤ Real.log ((|t| + 3) ^ 2) :=
          Real.log_le_log (by linarith [abs_nonneg t]) hsq
        rw [Real.log_pow, ← hL] at h1
        push_cast at h1
        linarith
      have h5 : Real.log (Real.log (4 * (|t| + 2)) + 1) ≤ Real.log 4 + Real.log (1 + L) := by
        have hlt : Real.log (4 * (|t| + 2)) + 1 ≤ 4 * (1 + L) := by linarith
        calc Real.log (Real.log (4 * (|t| + 2)) + 1) ≤ Real.log (4 * (1 + L)) :=
              Real.log_le_log hbase hlt
          _ = Real.log 4 + Real.log (1 + L) := by
              rw [Real.log_mul (by norm_num) (by linarith)]
      have h6 : max 0 (Real.log (C₂ * (Real.log (4 * (|t| + 2)) + 1) ^ C₂))
          = max 0 (Real.log C₂ + C₂ * Real.log (Real.log (4 * (|t| + 2)) + 1)) := by rw [h2]
      rw [h6] at h1
      have h7 : max 0 (Real.log C₂ + C₂ * Real.log (Real.log (4 * (|t| + 2)) + 1))
          ≤ |Real.log C₂| + C₂ * (Real.log 4 + Real.log (1 + L)) := by
        refine max_le ?_ ?_
        · have h8 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          have h9 : 0 ≤ Real.log (1 + L) := Real.log_nonneg (by linarith)
          have h10 : 0 ≤ C₂ * (Real.log 4 + Real.log (1 + L)) :=
            mul_nonneg hC₂.le (by linarith)
          linarith [abs_nonneg (Real.log C₂)]
        · linarith [h3, mul_le_mul_of_nonneg_left h5 hC₂.le]
      have h8 := le_trans h1 h7
      rw [mul_add] at h8
      linarith [h8]
    have hlog1L : Real.log (1 + L) ≤ 1 + L := by
      have h4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + L by linarith)
      linarith
    have hK1 : Real.log (2 * (1 + C₁)) ≤ K := by
      rw [hK]
      have h4 : 0 ≤ C₂ * Real.log 4 := mul_nonneg hC₂.le (Real.log_nonneg (by norm_num))
      linarith [abs_nonneg (Real.log C₂)]
    have hK2 : |Real.log C₂| ≤ K := by
      rw [hK]
      have h4 : 0 ≤ C₂ * Real.log 4 := mul_nonneg hC₂.le (Real.log_nonneg (by norm_num))
      have h5 : 0 < Real.log (2 * (1 + C₁)) := Real.log_pos (by linarith)
      linarith
    have hK3 : C₂ * Real.log 4 ≤ K := by
      rw [hK]
      have h4 : 0 < Real.log (2 * (1 + C₁)) := Real.log_pos (by linarith)
      linarith [abs_nonneg (Real.log C₂)]
    have hK4 : (1 : ℝ) ≤ K := by
      rw [hK]
      have h4 : 0 ≤ C₂ * Real.log 4 := mul_nonneg hC₂.le (Real.log_nonneg (by norm_num))
      have h5 : 0 < Real.log (2 * (1 + C₁)) := Real.log_pos (by linarith)
      linarith [abs_nonneg (Real.log C₂)]
    have hm_ub : -Real.log m ≤ |Real.log C₂| + C₂ * Real.log 4 + C₂ * Real.log (1 + L) := by
      have hm_eq : Real.log m = -Real.log X := by rw [hm, one_div, Real.log_inv]
      rw [hm_eq]
      linarith [hXbound]
    nlinarith [hlog2M, hm_ub, hlog1L, hK1, hK2, hK3, hK4, hL1, hLpos, hC₂.le, hKpos]
  have hstep2 : 4 * (Real.log (2 * M) - Real.log m) / R
      ≤ 128 * (3 * K + 1 + C₂) / cmin * L ^ (2 : ℕ) := by
    have hRinv : R⁻¹ = 8 * (L + 1) / cmin := by rw [hR, inv_div]
    have hdiv : 4 * (Real.log (2 * M) - Real.log m) / R
        = 32 * (Real.log (2 * M) - Real.log m) * (1 + L) / cmin := by
      rw [div_eq_mul_inv, hRinv]; ring
    rw [hdiv]
    have h2 : 128 * (3 * K + 1 + C₂) / cmin * L ^ (2 : ℕ)
        = 128 * (3 * K + 1 + C₂) * L ^ 2 / cmin := by ring
    rw [h2]
    rw [div_le_div_iff₀ hcmin0 hcmin0]
    have hL2 : (1 + L) ^ 2 ≤ 4 * L ^ 2 := by nlinarith [hL1]
    have hKnn : 0 ≤ 3 * K + 1 + C₂ := by linarith [hKpos, hC₂.le]
    have h1a : (Real.log (2 * M) - Real.log m) * (1 + L)
        ≤ (3 * K + 1 + C₂) * (1 + L) * (1 + L) :=
      mul_le_mul_of_nonneg_right hA_le (by linarith : (0 : ℝ) ≤ 1 + L)
    have h1 : 32 * (Real.log (2 * M) - Real.log m) * (1 + L)
        ≤ 32 * (3 * K + 1 + C₂) * (1 + L) ^ 2 := by nlinarith [h1a]
    have h3 : 32 * (3 * K + 1 + C₂) * (1 + L) ^ 2
        ≤ 128 * (3 * K + 1 + C₂) * L ^ 2 := by nlinarith [hL2, hKnn]
    nlinarith [h1, h3, hcmin0.le]
  calc ‖logDeriv (DirichletCharacter.LFunction chi4) ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖logDeriv (DirichletCharacter.LFunction chi4) s‖ := by rw [hs]
    _ ≤ 4 * (Real.log (2 * M) - Real.log m) / R := hstep1
    _ ≤ 128 * (3 * K + 1 + C₂) / cmin * L ^ (2 : ℕ) := hstep2
    _ = 128 * (3 * K + 1 + C₂) / cmin * (Real.log (|t| + 3)) ^ (2 : ℕ) := by rw [hL]

/-! ## The target -/

theorem chi4_LSeries_logDeriv_re_le_logsq :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
      (deriv (LSeries Work.FIArea6Hecke.R.chi4fun) (((σ : ℂ) + (t : ℂ) * Complex.I)) /
        LSeries Work.FIArea6Hecke.R.chi4fun (((σ : ℂ) + (t : ℂ) * Complex.I))).re
        ≤ C * (Real.log (|t| + 3)) ^ (2 : ℕ) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := logDeriv_LFunction_chi4_bound_large
  obtain ⟨B, hB0, hB⟩ := logDeriv_LFunction_chi4_compact
  refine ⟨max C₁ B, lt_max_of_lt_left hC₁pos, ?_⟩
  intro σ t hσ1 hσ2
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by simp [hs]
  have hLeq : LSeries Work.FIArea6Hecke.R.chi4fun =ᶠ[𝓝 s]
      DirichletCharacter.LFunction chi4 := by
    have hU : {z : ℂ | (1 : ℝ) < z.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by show (1 : ℝ) < s.re; rw [hsre]; exact hσ1)
    exact Filter.eventually_of_mem hU (fun z hz => LSeries_chi4fun_eq z hz)
  have hlogderiv : logDeriv (LSeries Work.FIArea6Hecke.R.chi4fun) s
      = logDeriv (DirichletCharacter.LFunction chi4) s :=
    (logDeriv_congr_nhds hLeq).eq_of_nhds
  have hre_le : (deriv (LSeries Work.FIArea6Hecke.R.chi4fun) s
        / LSeries Work.FIArea6Hecke.R.chi4fun s).re
      ≤ ‖logDeriv (DirichletCharacter.LFunction chi4) s‖ := by
    rw [← logDeriv_apply (LSeries Work.FIArea6Hecke.R.chi4fun) s, hlogderiv]
    exact Complex.re_le_norm _
  have hL1 : (1 : ℝ) ≤ (Real.log (|t| + 3)) ^ (2 : ℕ) := by
    have h3 : (3 : ℝ) ≤ |t| + 3 := by linarith [abs_nonneg t]
    have hexp : Real.exp 1 ≤ |t| + 3 := le_trans (le_of_lt Real.exp_one_lt_three) h3
    have hlog : (1 : ℝ) ≤ Real.log (|t| + 3) := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (|t| + 3) := Real.log_le_log (Real.exp_pos 1) hexp
    nlinarith [hlog]
  have hmaxnn : 0 ≤ max C₁ B := le_trans hC₁pos.le (le_max_left _ _)
  have hs_im : s.im = t := by simp [hs]
  by_cases ht : 3 ≤ |t|
  · have h := hC₁ σ t hσ1 hσ2 ht
    rw [← hs] at h
    calc (deriv (LSeries Work.FIArea6Hecke.R.chi4fun) s
          / LSeries Work.FIArea6Hecke.R.chi4fun s).re
        ≤ ‖logDeriv (DirichletCharacter.LFunction chi4) s‖ := hre_le
      _ ≤ C₁ * (Real.log (|t| + 3)) ^ (2 : ℕ) := h
      _ ≤ max C₁ B * (Real.log (|t| + 3)) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have ht3 : |t| ≤ 3 := by
      have h3 := not_le.mp ht
      linarith
    have h := hB s (by rw [hsre]; linarith)
      (by rw [hsre]; exact hσ2) (by rw [hs_im]; exact ht3)
    calc (deriv (LSeries Work.FIArea6Hecke.R.chi4fun) s
          / LSeries Work.FIArea6Hecke.R.chi4fun s).re
        ≤ ‖logDeriv (DirichletCharacter.LFunction chi4) s‖ := hre_le
      _ ≤ B := h
      _ ≤ max C₁ B * (Real.log (|t| + 3)) ^ (2 : ℕ) := by
          calc B ≤ max C₁ B := le_max_right _ _
            _ = max C₁ B * 1 := by ring
            _ ≤ max C₁ B * (Real.log (|t| + 3)) ^ (2 : ℕ) :=
                mul_le_mul_of_nonneg_left hL1 hmaxnn

end

end Work.FIArea6Hecke.R
