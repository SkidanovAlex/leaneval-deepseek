import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.A7.exists_isMin1
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
import Submission.Work.LinnikAreas.OtherCharRepel.threeCharPositivity
import Submission.Work.LinnikAreas.OtherCharRepel.changeLevelLogDerivLower

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 1600000

namespace Work.LinnikAreas.OtherCharRepel

/-- **Landau's repulsion for two real Dirichlet characters** (Principle 1 of Heath-Brown 1992,
p. 2; Landau 1918, "at most one exceptional zero").

There is an absolute constant `c > 0` such that for every sufficiently large modulus `q`, two
*distinct* real (quadratic) non-principal characters `χ₀ ≠ χ` modulo `q` cannot both have a real
zero with `λ = (1 - Re ρ)·log q` below `c`: at least one of `λ(ρ₀)`, `λ(ρ)` is `≥ c`.

This is Landau's repulsion `min(β,β') < 1 - B/log|D D'|` for distinct fundamental discriminants:
since the conductors of `χ₀, χ` both divide `q`, `|D D'| ≤ q²`, whence `max(λ(ρ₀),λ(ρ)) ≥ B/2`. -/
theorem twoRealCharRepel : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ) (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      χ₀ ≠ 1 → χ₀ ^ 2 = 1 → ρ₀.im = 0 → Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0 →
      χ ≠ 1 → χ ^ 2 = 1 → ρ.im = 0 → Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      χ ≠ χ₀ →
      c ≤ max (Work.LinnikContract.lamOf q ρ₀) (Work.LinnikContract.lamOf q ρ) := by
  -- the analytic inputs, each with an absolute constant
  obtain ⟨Cz, hCzpos, hCz⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
  obtain ⟨Cp, hCppos, hCp⟩ :=
    Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_re_pole_of_real_zero
  obtain ⟨Cl, hClpos, hCl⟩ :=
    Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_re_lower_of_ne_one
  obtain ⟨Ce, hCepos, hCe⟩ := changeLevelLogDerivLower
  -- aggregate constant
  set Lam : ℝ := Cz + 4 * Cp + 2 * Ce + 2 * Cl + 1 with hLamdef
  have hLampos : 0 < Lam := by rw [hLamdef]; linarith
  have hLamge : Cz + 4 * Cp + 2 * Ce + 2 * Cl ≤ Lam := by rw [hLamdef]; linarith
  -- the window parameter and the final constant
  set K : ℝ := min (1 / 4) (1 / (16 * (Lam + 1))) with hKdef
  have hKpos : 0 < K := lt_min (by norm_num) (by positivity)
  have hKle4 : K ≤ 1 / 4 := min_le_left _ _
  have hK16 : K * (Lam + 1) ≤ 1 / 16 := by
    have h := min_le_right (1 / 4 : ℝ) (1 / (16 * (Lam + 1)))
    rw [hKdef]
    have hden : 0 < 16 * (Lam + 1) := by linarith
    have hmul := mul_le_mul_of_nonneg_right h hden.le
    have heq : (1 / (16 * (Lam + 1))) * (16 * (Lam + 1)) = 1 := by field_simp
    have h2 : (16 * (Lam + 1)) * K ≤ 1 := by linarith [hmul, heq]
    nlinarith [h2, hden]
  refine ⟨K / 2, by positivity, 9, ?_⟩
  intro q hq hqne χ₀ ρ₀ χ ρ hχ₀1 hχ₀sq hρ₀im hzm₀ hχ1 hχsq hρim hzm hχχ₀
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hq1 : 1 < q := by omega
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by exact_mod_cast hq1)
  have hL2 : 2 ≤ L := by
    rw [hLdef]
    have he : Real.exp 2 ≤ (q : ℝ) := by
      have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
      have h3 : (9 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      nlinarith [h1, h2, Real.exp_pos 1, h3]
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos 2) he
  -- the evaluation point `σ = 1 + K/L`
  have hσpos : 0 < K / L := div_pos hKpos hLpos
  have hσ1 : 1 < 1 + K / L := by linarith
  have hσ54 : 1 + K / L ≤ 5 / 4 := by
    have h1 : K / L ≤ 1 / 4 := by
      rw [div_le_iff₀ hLpos]
      nlinarith [hKle4, hL2]
    linarith
  have hσ2 : 1 + K / L ≤ 2 := by linarith
  -- the two zeros are real
  have hρ₀eq : ρ₀ = ((ρ₀.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hρ₀im
  have hρeq : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hρim
  have hZ₀ : Work.LinnikContract.IsZ χ₀ ρ₀ := ⟨hχ₀1, hzm₀, by rw [hρ₀im]; norm_num⟩
  have hZ : Work.LinnikContract.IsZ χ ρ := ⟨hχ1, hzm, by rw [hρim]; norm_num⟩
  haveI hc₀ : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
  haveI hc : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨hz₀L, hb₀0, hb₀1⟩ := Work.A7.isZ_LFunction_zero χ₀ hZ₀
  obtain ⟨hzL, hb0, hb1⟩ := Work.A7.isZ_LFunction_zero χ hZ
  have hz₀' : DirichletCharacter.LFunction χ₀.primitiveCharacter ((ρ₀.re : ℝ) : ℂ) = 0 := by
    rw [← hρ₀eq]; exact hz₀L
  have hz' : DirichletCharacter.LFunction χ.primitiveCharacter ((ρ.re : ℝ) : ℂ) = 0 := by
    rw [← hρeq]; exact hzL
  -- the analytic inputs at `σ = 1 + K/L`
  have hpos := threeCharPositivity χ₀ χ hχ₀sq hχsq (1 + K / L) hσ1
  have hzeta : (-deriv riemannZeta (↑(1 + K / L)) / riemannZeta (↑(1 + K / L))).re
      ≤ 1 / (K / L) + Cz := by
    have h := hCz (1 + K / L) hσ1 hσ2
    have h1 : 1 + K / L - 1 = K / L := by ring
    rwa [h1] at h
  have hp₀ := hCp χ₀.conductor χ₀.primitiveCharacter (Work.A7.primitiveCharacter_ne_one hχ₀1)
    (DirichletCharacter.primitiveCharacter_isPrimitive χ₀) ρ₀.re hb₀0 hb₀1 hz₀'
    (1 + K / L) hσ1 hσ54
  have hp := hCp χ.conductor χ.primitiveCharacter (Work.A7.primitiveCharacter_ne_one hχ1)
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) ρ.re hb0 hb1 hz'
    (1 + K / L) hσ1 hσ54
  have he₀ := hCe q χ₀ hχ₀1 (1 + K / L) hσ1 hσ54
  have he := hCe q χ hχ1 (1 + K / L) hσ1 hσ54
  have hsq₀ : χ₀ * χ₀ = 1 := by rw [← pow_two]; exact hχ₀sq
  have hχ₀χ_ne1 : χ₀ * χ ≠ 1 := by
    intro h
    refine hχχ₀ ?_
    have h2 : χ₀ * (χ₀ * χ) = χ₀ * 1 := by rw [h]
    rw [← mul_assoc, hsq₀, one_mul, mul_one] at h2
    exact h2
  have hdl := hCl q (χ₀ * χ) hχ₀χ_ne1 (1 + K / L) hσ1 hσ54
  -- elementary bounds for the logarithm terms
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hlogq : Real.log (2 * (q : ℝ)) + 1 ≤ 2 * (L + 1) := by
    have h3 : Real.log (2 * (q : ℝ)) = Real.log 2 + L := by
      rw [hLdef, Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hlogq0 : Real.log (2 * (χ₀.conductor : ℝ)) + 1 ≤ 2 * (L + 1) := by
    have h1 : (χ₀.conductor : ℝ) ≤ (q : ℝ) :=
      Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ₀.conductor_dvd_level)
    have h2 : Real.log (2 * (χ₀.conductor : ℝ)) ≤ Real.log (2 * (q : ℝ)) := by
      apply Real.log_le_log
      · have : (0:ℝ) < (χ₀.conductor : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ₀.conductor)
        linarith
      · exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    have h3 : Real.log (2 * (q : ℝ)) = Real.log 2 + L := by
      rw [hLdef, Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hlogq1 : Real.log (2 * (χ.conductor : ℝ)) + 1 ≤ 2 * (L + 1) := by
    have h1 : (χ.conductor : ℝ) ≤ (q : ℝ) :=
      Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level)
    have h2 : Real.log (2 * (χ.conductor : ℝ)) ≤ Real.log (2 * (q : ℝ)) := by
      apply Real.log_le_log
      · have : (0:ℝ) < (χ.conductor : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
        linarith
      · exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    have h3 : Real.log (2 * (q : ℝ)) = Real.log 2 + L := by
      rw [hLdef, Real.log_mul (by norm_num) (by positivity)]
    linarith
  -- the core inequality
  have hmain : 1 / (1 + K / L - ρ₀.re) + 1 / (1 + K / L - ρ.re) ≤ L / K + Lam * (L + 1) := by
    have hsum : 1 / (1 + K / L - ρ₀.re) + 1 / (1 + K / L - ρ.re) ≤ 1 / (K / L) + Cz
        + (Cp * (Real.log (2 * (χ₀.conductor : ℝ)) + 1) + Ce * (L + 1))
        + (Cp * (Real.log (2 * (χ.conductor : ℝ)) + 1) + Ce * (L + 1))
        + Cl * (Real.log (2 * (q : ℝ)) + 1) := by
      linarith [hpos, hzeta, hp₀, hp, he₀, he, hdl]
    have hLKnz : L / K = 1 / (K / L) := by
      have : K / L ≠ 0 := ne_of_gt hσpos
      field_simp
    rw [hLKnz]
    have hb1 : Cp * (Real.log (2 * (χ₀.conductor : ℝ)) + 1) ≤ Cp * (2 * (L + 1)) :=
      mul_le_mul_of_nonneg_left hlogq0 hCppos.le
    have hb2 : Cp * (Real.log (2 * (χ.conductor : ℝ)) + 1) ≤ Cp * (2 * (L + 1)) :=
      mul_le_mul_of_nonneg_left hlogq1 hCppos.le
    have hb3 : Cl * (Real.log (2 * (q : ℝ)) + 1) ≤ Cl * (2 * (L + 1)) :=
      mul_le_mul_of_nonneg_left hlogq hClpos.le
    have hb4 : Cz ≤ Cz * (L + 1) := by nlinarith [hCzpos, hL2]
    have hLnn : 0 ≤ L + 1 := by linarith
    nlinarith [hsum, hb1, hb2, hb3, hb4, hLamge, hLnn, hCzpos, hCppos, hCepos, hClpos,
      hLampos]
  -- ------------------------------------------------------------------
  -- the arithmetic contradiction
  -- ------------------------------------------------------------------
  by_contra hcon
  push Not at hcon
  have hlam0 : Work.LinnikContract.lamOf q ρ₀ < K / 2 := lt_of_le_of_lt (le_max_left _ _) hcon
  have hlamZ : Work.LinnikContract.lamOf q ρ < K / 2 := lt_of_le_of_lt (le_max_right _ _) hcon
  have hlamEq0 : (1 - ρ₀.re) * L = Work.LinnikContract.lamOf q ρ₀ := by
    rw [Work.LinnikContract.lamOf, hLdef]
  have hlamEq : (1 - ρ.re) * L = Work.LinnikContract.lamOf q ρ := by
    rw [Work.LinnikContract.lamOf, hLdef]
  have hsub0 : (1 - ρ₀.re) * L < K / 2 := by rw [hlamEq0]; exact hlam0
  have hsubZ : (1 - ρ.re) * L < K / 2 := by rw [hlamEq]; exact hlamZ
  have hpos0 : 0 < (1 - ρ₀.re) * L := mul_pos (by linarith [hb₀1]) hLpos
  have hposZ : 0 < (1 - ρ.re) * L := mul_pos (by linarith [hb1]) hLpos
  have hd₀ : K + (1 - ρ₀.re) * L < K + K / 2 := by linarith
  have hd : K + (1 - ρ.re) * L < K + K / 2 := by linarith
  have hden0pos : 0 < 1 + K / L - ρ₀.re := by linarith [hb₀1]
  have hdenpos : 0 < 1 + K / L - ρ.re := by linarith [hb1]
  have hKK0 : 0 < K + (1 - ρ₀.re) * L := by linarith
  have hKKZ : 0 < K + (1 - ρ.re) * L := by linarith
  have hterm0 : 1 / (1 + K / L - ρ₀.re) = L / (K + (1 - ρ₀.re) * L) := by
    rw [div_eq_div_iff (ne_of_gt hden0pos) (ne_of_gt hKK0)]
    field_simp <;> ring
  have htermZ : 1 / (1 + K / L - ρ.re) = L / (K + (1 - ρ.re) * L) := by
    rw [div_eq_div_iff (ne_of_gt hdenpos) (ne_of_gt hKKZ)]
    field_simp <;> ring
  rw [hterm0, htermZ] at hmain
  have hlow : (4 / 3) * (L / K) < L / (K + (1 - ρ₀.re) * L) + L / (K + (1 - ρ.re) * L) := by
    have h1 : L / (K + K / 2) < L / (K + (1 - ρ₀.re) * L) :=
      div_lt_div_of_pos_left hLpos hKK0 hd₀
    have h2 : L / (K + K / 2) < L / (K + (1 - ρ.re) * L) :=
      div_lt_div_of_pos_left hLpos hKKZ hd
    have h3 : L / (K + K / 2) = (2 / 3) * (L / K) := by
      field_simp <;> ring
    linarith [h1, h2, h3]
  have hle : (4 / 3) * (L / K) < L / K + Lam * (L + 1) := lt_of_lt_of_le hlow hmain
  have hcancel : (1 / 3) * (L / K) < Lam * (L + 1) := by linarith
  have hfin1 : L < 3 * K * Lam * (L + 1) := by
    have h3K : (0 : ℝ) < 3 * K := by linarith
    have hmul := mul_lt_mul_of_pos_left hcancel h3K
    have hKne : K ≠ 0 := ne_of_gt hKpos
    have h4 : 3 * K * ((1 / 3) * (L / K)) = L := by
      field_simp <;> ring
    have h5 : 3 * K * (Lam * (L + 1)) = 3 * K * Lam * (L + 1) := by ring
    rw [h4, h5] at hmul
    exact hmul
  have hfin2 : 1 < 3 * K * Lam * (L + 1) / L := by
    rw [lt_div_iff₀ hLpos]
    linarith
  have hfin3 : 3 * K * Lam * (L + 1) / L ≤ (9 / 2) * (K * (Lam + 1)) := by
    have h : (L + 1) / L ≤ 3 / 2 := by
      rw [div_le_iff₀ hLpos]
      linarith
    have hnn : (0 : ℝ) ≤ 3 * K * Lam := by positivity
    have heq : 3 * K * Lam * (L + 1) / L = (3 * K * Lam) * ((L + 1) / L) := by ring
    have hstep : (3 * K * Lam) * ((L + 1) / L) ≤ (3 * K * Lam) * (3 / 2) :=
      mul_le_mul_of_nonneg_left h hnn
    have hstep2 : (3 * K * Lam) * (3 / 2) = (9 / 2) * (K * Lam) := by ring
    have hstep3 : (9 / 2) * (K * Lam) ≤ (9 / 2) * (K * (Lam + 1)) := by
      have hkk : K * Lam ≤ K * (Lam + 1) := by nlinarith [hKpos]
      linarith
    linarith [hstep, hstep2, hstep3]
  linarith [hfin2, hfin3, hK16]

end Work.LinnikAreas.OtherCharRepel
