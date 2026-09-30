import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.liouville.vk_endgame
import Submission.Work.BMF.liouville.mangoldt_twist_chebyshev
import Submission.Work.BMF.liouville.exp_decay_log_integral
import Submission.Work.BMF.liouville.mertens_recip_le
import Submission.Work.BMF.liouville.abel_step_twist
import Submission.Work.BMF.liouville.recip_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Polynomial BoundedMultiplicativeFunctions Finset Real MeasureTheory

noncomputable section

noncomputable def mangoldtTwistSum (t u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))

noncomputable def abelW (t : ℝ) : ℝ := (Real.log t + 1) / (t * Real.log t) ^ 2

noncomputable def mainc (u t : ℝ) : ℂ := (t : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)

noncomputable def gint (u t : ℝ) : ℂ := (t : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)) *
    (((1 + 1 / Real.log t) / Real.log t : ℝ) : ℂ)

lemma one_le_log_of_three {t : ℝ} (ht : 3 ≤ t) : 1 ≤ Real.log t := by
  have h : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have h13 : (1 : ℝ) < Real.log 3 := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
  linarith

lemma measurable_mangoldtTwistSum (u : ℝ) : Measurable (fun t : ℝ => mangoldtTwistSum t u) := by
  have h : (fun t : ℝ => mangoldtTwistSum t u) =
      fun t : ℝ => (fun n : ℕ => ∑ j ∈ Finset.Icc 1 n,
        ((ArithmeticFunction.vonMangoldt j : ℝ) : ℂ) * (j : ℂ) ^ (-(Complex.I * u))) ⌊t⌋₊ := by
    funext t; rw [mangoldtTwistSum]
  rw [h]; measurability

lemma measurable_abelW : Measurable abelW := by
  unfold abelW; fun_prop

lemma abelW_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ abelW t := by
  rw [abelW]
  have h1 : 0 < Real.log t := Real.log_pos ht
  positivity

lemma abelW_le {t : ℝ} (ht : 3 ≤ t) : abelW t ≤ 2 / (t ^ 2 * Real.log t) := by
  have hlog1 : 1 ≤ Real.log t := one_le_log_of_three (by linarith)
  have hlog : 0 < Real.log t := by linarith
  have ht0 : 0 < t := by linarith
  have h1 : Real.log t + 1 ≤ 2 * Real.log t := by linarith
  have h2 : (0:ℝ) < t ^ 2 * Real.log t := by positivity
  have hden : (0:ℝ) < (t * Real.log t) ^ 2 := by
    apply pow_pos
    exact mul_pos ht0 hlog
  rw [abelW, div_le_div_iff₀ hden h2]
  calc (Real.log t + 1) * (t ^ 2 * Real.log t)
      ≤ (2 * Real.log t) * (t ^ 2 * Real.log t) :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt h2)
    _ = 2 * (t * Real.log t) ^ 2 := by ring

lemma cpow_one_sub_sub_two {t : ℝ} (ht : 0 < t) (u : ℝ) :
    (t : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)) =
      (t : ℂ) ^ (1 - Complex.I * (u : ℂ)) * ((t : ℂ) ^ 2)⁻¹ := by
  have htC : (t : ℂ) ≠ 0 := by
    simp [show t ≠ 0 by linarith]
  rw [show (-(1 : ℂ) - Complex.I * (u : ℂ)) = (1 - Complex.I * (u : ℂ)) + (-(2:ℂ)) by ring,
    Complex.cpow_add _ _ htC, Complex.cpow_neg, Complex.cpow_ofNat]

lemma mainc_mul_abelW (u : ℝ) {t : ℝ} (ht : 1 < t) :
    mainc u t * ((abelW t : ℝ) : ℂ) = ((1 : ℂ) - Complex.I * (u : ℂ))⁻¹ * gint u t := by
  have ht0 : (0:ℝ) < t := by linarith
  have hL : mainc u t * ((abelW t : ℝ) : ℂ) =
      (t : ℂ) ^ (1 - Complex.I * (u : ℂ)) * ((1 : ℂ) - Complex.I * (u : ℂ))⁻¹ *
        (((Real.log t + 1) / (t * Real.log t) ^ 2 : ℝ) : ℂ) := by
    rw [mainc, abelW, div_eq_mul_inv]
  have hR : ((1 : ℂ) - Complex.I * (u : ℂ))⁻¹ * gint u t =
      ((1 : ℂ) - Complex.I * (u : ℂ))⁻¹ * ((t : ℂ) ^ (1 - Complex.I * (u : ℂ)) *
        ((t : ℂ) ^ 2)⁻¹ * (((1 + 1 / Real.log t) / Real.log t : ℝ) : ℂ)) := by
    rw [gint, cpow_one_sub_sub_two ht0 u]
  have hA : (((Real.log t + 1) / (t * Real.log t) ^ 2 : ℝ) : ℂ) =
      ((t : ℂ) ^ 2)⁻¹ * (((1 + 1 / Real.log t) / Real.log t : ℝ) : ℂ) := by
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
    have htne : t ≠ 0 := by linarith
    have hpow : (t : ℂ) ^ 2 = (((t : ℝ) ^ 2 : ℝ) : ℂ) := by rw [Complex.ofReal_pow]
    rw [hpow, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_inj]
    field_simp
  rw [hL, hR, hA]
  ring

lemma norm_inv_one_sub_I_mul_le_one (u : ℝ) : ‖((1 : ℂ) - Complex.I * (u : ℂ))⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have hre : ((1 : ℂ) - Complex.I * (u : ℂ)).re = 1 := by
    simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := by
    have := Complex.abs_re_le_norm ((1 : ℂ) - Complex.I * (u : ℂ))
    rw [hre] at this
    simpa using this
  exact inv_le_one_of_one_le₀ h1

lemma norm_mainc_le (u : ℝ) {t : ℝ} (ht : 0 < t) : ‖mainc u t‖ ≤ t := by
  rw [mainc, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hre : (1 - Complex.I * (u : ℂ)).re = 1 := by
    simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [hre, Real.rpow_one]
  have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := by
    have := Complex.abs_re_le_norm ((1 : ℂ) - Complex.I * (u : ℂ))
    rw [hre] at this
    simpa using this
  calc t / ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ ≤ t / 1 :=
        div_le_div_of_nonneg_left (le_of_lt ht) (by norm_num) h1
    _ = t := by ring

lemma cpow_sub_one_eq (p : ℕ) (hp : p ≠ 0) (u : ℝ) :
    (p : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)) = ((p : ℂ) ^ (-(Complex.I * u))) / p := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [show (-(1 : ℂ) - Complex.I * (u : ℂ)) = (-(Complex.I * u)) + (-1) by ring,
    Complex.cpow_add _ _ hpC, Complex.cpow_neg_one, div_eq_mul_inv]

lemma filter_prime_Icc (N M : ℕ) :
    (Finset.Icc N M).filter Nat.Prime = (M.primesLE).filter (fun p => N ≤ p) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3⟩, h1⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3, h1⟩, h2⟩


lemma norm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ = r := by
  have h := RCLike.norm_ofReal (K := ℂ) r
  rwa [abs_of_nonneg hr] at h



/-- The twisted reciprocal-prime sum `Σ_{p ≤ x} p^{-1-iu}`. -/
noncomputable def twistSum (x u : ℝ) : ℂ :=
  ∑ p ∈ ⌊x⌋₊.primesLE, ((p : ℂ) ^ (-(Complex.I * u))) / p

lemma cpow_re_eq_cos (p : ℕ) (hp : p ≠ 0) (u : ℝ) :
    (((p : ℂ) ^ (-(Complex.I * u))).re) = Real.cos (u * Real.log p) := by
  have hpc : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp
  rw [Complex.cpow_def_of_ne_zero hpc]
  have hlog : Complex.log ((p : ℂ)) = ((Real.log p : ℝ) : ℂ) := by
    rw [show ((p : ℂ)) = (((p : ℝ)) : ℂ) by simp,
      ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (p : ℝ))]
  rw [hlog]
  have hexp : ((Real.log p : ℂ)) * (-(Complex.I * (u : ℂ))) =
      (((-(Real.log p * u)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hexp, Complex.exp_ofReal_mul_I_re, Real.cos_neg, mul_comm]

lemma term_re_eq (p : ℕ) (hp : p ≠ 0) (u : ℝ) :
    ((((p : ℂ) ^ (-(Complex.I * u))) / p).re) = Real.cos (u * Real.log p) / p := by
  rw [div_eq_mul_inv, Complex.mul_re, cpow_re_eq_cos p hp u,
    show ((p : ℂ))⁻¹ = ((((p : ℝ))⁻¹ : ℝ) : ℂ) by simp, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, div_eq_mul_inv]

lemma twistSum_re_eq_cos (x u : ℝ) :
    (twistSum x u).re = ∑ p ∈ ⌊x⌋₊.primesLE, Real.cos (u * Real.log p) / p := by
  rw [twistSum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  obtain ⟨-, hpp⟩ := Nat.mem_primesLE.mp hp
  exact term_re_eq p hpp.ne_zero u

lemma twistSum_re_neg (x u : ℝ) : (twistSum x (-u)).re = (twistSum x u).re := by
  rw [twistSum_re_eq_cos, twistSum_re_eq_cos]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [neg_mul, Real.cos_neg]

lemma prime_term_re_le (p : ℕ) (u : ℝ) :
    ((((p : ℂ) ^ (-(Complex.I * u))) / p).re) ≤ (1 : ℝ) / p := by
  refine (Complex.re_le_norm _).trans ?_
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · have hnorm : ‖(p : ℂ) ^ (-(Complex.I * u))‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hp)]
      simp
    rw [norm_div, hnorm, Complex.norm_natCast, one_div]

/-- **The case `χ = 1`, `q = 1` of `vk_prime_sums`**, in the range needed below
(`|u| ≤ exp((log x)^{5/4})`, error `exp(−c (log x)^{1/10})`); supplied by
`Work.BMF.liouville.vk_chi_one_endgame`. -/
theorem vk_prime_sums_one :
    ∃ c C : ℝ, 0 < c ∧
      ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ, |u| ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) →
        ‖mangoldtTwistSum x u - (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖ ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ)) := by
  obtain ⟨c, C, hc, h⟩ := vk_chi_one_endgame
  exact ⟨c, C, hc, fun x hx u hu => by simpa only [mangoldtTwistSum] using h x hx u hu⟩

theorem abel_tail_bound
    (u : ℝ) (N : ℕ) (x : ℝ) (hx : 3 ≤ x) (hN : 3 ≤ N) (hNx : (N : ℝ) ≤ x)
    (c C : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hE : ∀ t : ℝ, (N : ℝ) ≤ t → t ≤ x →
      ‖mangoldtTwistSum t u - (t : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖ ≤
        C * t * Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)))
    (Kerr Cch Kmi : ℝ) (hCch0 : 0 ≤ Cch)
    (hKerr : ∫ t in (N : ℝ)..(⌊x⌋₊ : ℝ),
        Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t) ≤ Kerr)
    (hCch : ∀ t : ℝ, 1 ≤ t → ‖mangoldtTwistSum t u‖ ≤ Cch * t)
    (hKmi : (((1 : ℂ) - Complex.I * (u : ℂ))⁻¹ * ∫ t in (N : ℝ)..(⌊x⌋₊ : ℝ),
        (t : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)) *
          (((1 + 1 / Real.log t) / Real.log t : ℝ) : ℂ)).re ≤ Kmi) :
    (∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p => N ≤ p),
        ((p : ℂ) ^ (-(Complex.I * u))) / p).re ≤
      Kmi + 2 * C * Kerr + Cch + C + 2 := by
  let M : ℕ := ⌊x⌋₊
  have hMR : (M : ℝ) ≤ x := by show ((⌊x⌋₊ : ℕ) : ℝ) ≤ x; exact Nat.floor_le (by linarith)
  have hM3 : 3 ≤ M := by
    show 3 ≤ ⌊x⌋₊
    exact Nat.le_floor (by exact_mod_cast hx)
  have hNM : N ≤ M := by
    show N ≤ ⌊x⌋₊
    exact Nat.le_floor hNx
  have hNMR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM3r : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3
  have hlogN1 : 1 ≤ Real.log N := one_le_log_of_three hN3
  have hlogM1 : 1 ≤ Real.log M := one_le_log_of_three hM3r
  have hlogNpos : 0 < Real.log N := by linarith
  have hlogMpos : 0 < Real.log M := by linarith
  set a : ℕ → ℂ := fun j => ((ArithmeticFunction.vonMangoldt j : ℝ) : ℂ) * (j : ℂ) ^ (-(Complex.I * u)) with ha
  have hA : ∀ t : ℝ, (∑ j ∈ Finset.Icc 1 ⌊t⌋₊, a j) = mangoldtTwistSum t u := by
    intro t; rw [mangoldtTwistSum]
  have hAM : (∑ j ∈ Finset.Icc 1 M, a j) = mangoldtTwistSum (M : ℝ) u := by
    rw [← hA (M : ℝ), Nat.floor_natCast]
  have hAN : (∑ j ∈ Finset.Icc 1 (N - 1), a j) = mangoldtTwistSum ((N - 1 : ℕ) : ℝ) u := by
    rw [← hA ((N - 1 : ℕ) : ℝ), Nat.floor_natCast]
  have habel := abel_step_twist a N M (by omega) hNM
  rw [hAM, hAN] at habel
  have hLHS : (∑ n ∈ Finset.Icc N M, a n * ((1 / ((n : ℝ) * Real.log n) : ℝ) : ℂ)) =
      ∑ n ∈ Finset.Icc N M, (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((Real.log n : ℝ) : ℂ)) *
        (n : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    obtain ⟨hnN, -⟩ := Finset.mem_Icc.mp hn
    have hn1 : 1 < n := by omega
    have hn0 : ((n : ℂ)) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    have hlog0 : ((Real.log n : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt (Real.log_pos (by exact_mod_cast hn1))
    rw [ha]
    conv_rhs => rw [show (-(1 : ℂ) - Complex.I * (u : ℂ)) = (-(Complex.I * u)) + (-1) by ring,
      Complex.cpow_add _ _ hn0, Complex.cpow_neg_one]
    push_cast
    field_simp
  have hInt_congr : (∫ t in (N : ℝ)..(M : ℝ),
        (∑ j ∈ Finset.Icc 1 ⌊t⌋₊, a j) * (((Real.log t + 1) / (t * Real.log t) ^ 2 : ℝ) : ℂ))
      = ∫ t in (N : ℝ)..(M : ℝ), mangoldtTwistSum t u * ((abelW t : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hA t, abelW]
  have hlogSum_eq : (∑ n ∈ Finset.Icc N M, (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((Real.log n : ℝ) : ℂ)) *
        (n : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)))
      = mangoldtTwistSum (M : ℝ) u * ((1 / ((M : ℝ) * Real.log M) : ℝ) : ℂ)
        - mangoldtTwistSum ((N - 1 : ℕ) : ℝ) u * ((1 / ((N : ℝ) * Real.log N) : ℝ) : ℂ)
        + ∫ t in (N : ℝ)..(M : ℝ), mangoldtTwistSum t u * ((abelW t : ℝ) : ℂ) := by
    rw [← hLHS, habel, hInt_congr]
  have hAMbound : ‖mangoldtTwistSum (M : ℝ) u‖ ≤ (1 + C) * (M : ℝ) := by
    have hEst := hE (M : ℝ) hNMR hMR
    have hmain : ‖mainc u (M : ℝ)‖ ≤ (M : ℝ) := norm_mainc_le u (by positivity)
    have hexp1 : Real.exp (-c * (Real.log (M : ℝ)) ^ (1 / 10 : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h1 : (0:ℝ) ≤ (Real.log (M : ℝ)) ^ (1 / 10 : ℝ) :=
        Real.rpow_nonneg (le_of_lt hlogMpos) _
      nlinarith [hc, h1]
    have h3 : C * (M : ℝ) * Real.exp (-c * (Real.log (M : ℝ)) ^ (1 / 10 : ℝ)) ≤ C * (M : ℝ) := by
      calc C * (M : ℝ) * Real.exp (-c * (Real.log (M : ℝ)) ^ (1 / 10 : ℝ))
          ≤ C * (M : ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left hexp1
            positivity
        _ = C * (M : ℝ) := by ring
    calc ‖mangoldtTwistSum (M : ℝ) u‖
        = ‖(mangoldtTwistSum (M : ℝ) u - mainc u (M : ℝ)) + mainc u (M : ℝ)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖mangoldtTwistSum (M : ℝ) u - mainc u (M : ℝ)‖ + ‖mainc u (M : ℝ)‖ := norm_add_le _ _
      _ ≤ C * (M : ℝ) * Real.exp (-c * (Real.log (M : ℝ)) ^ (1 / 10 : ℝ)) + (M : ℝ) :=
          add_le_add hEst hmain
      _ ≤ C * (M : ℝ) + (M : ℝ) := by linarith [h3]
      _ = (1 + C) * (M : ℝ) := by ring
  have hAMphi : ‖mangoldtTwistSum (M : ℝ) u * ((1 / ((M : ℝ) * Real.log M) : ℝ) : ℂ)‖ ≤ 1 + C := by
    rw [norm_mul, norm_ofReal_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((M : ℝ) * Real.log M))]
    have hMne : ((M : ℝ) * Real.log M) ≠ 0 := by positivity
    calc ‖mangoldtTwistSum (M : ℝ) u‖ * (1 / ((M : ℝ) * Real.log M))
        ≤ ((1 + C) * (M : ℝ)) * (1 / ((M : ℝ) * Real.log M)) :=
          mul_le_mul_of_nonneg_right hAMbound (by positivity)
      _ = (1 + C) / Real.log M := by field_simp
      _ ≤ (1 + C) / 1 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hlogM1
      _ = 1 + C := by ring
  have hANphi : ‖mangoldtTwistSum ((N - 1 : ℕ) : ℝ) u * ((1 / ((N : ℝ) * Real.log N) : ℝ) : ℂ)‖ ≤ Cch := by
    rw [norm_mul, norm_ofReal_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((N : ℝ) * Real.log N))]
    have hN1 : (1 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
      have : 1 ≤ N - 1 := by omega
      exact_mod_cast this
    have hb := hCch ((N - 1 : ℕ) : ℝ) hN1
    have hNle : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have : N - 1 ≤ N := by omega
      exact_mod_cast this
    have hfrac : ((N - 1 : ℕ) : ℝ) * (1 / ((N : ℝ) * Real.log N)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      nlinarith [hNle, hlogN1, (show (0:ℝ) < (N:ℝ) by positivity)]
    calc ‖mangoldtTwistSum ((N - 1 : ℕ) : ℝ) u‖ * (1 / ((N : ℝ) * Real.log N))
        ≤ (Cch * ((N - 1 : ℕ) : ℝ)) * (1 / ((N : ℝ) * Real.log N)) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = Cch * (((N - 1 : ℕ) : ℝ) * (1 / ((N : ℝ) * Real.log N))) := by ring
      _ ≤ Cch * 1 := mul_le_mul_of_nonneg_left hfrac hCch0
      _ = Cch := by ring
  have hmainint : (∫ t in (N : ℝ)..(M : ℝ), mainc u t * ((abelW t : ℝ) : ℂ))
      = ((1 : ℂ) - Complex.I * (u : ℂ))⁻¹ * ∫ t in (N : ℝ)..(M : ℝ), gint u t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hNMR] at ht
    show mainc u t * ((abelW t : ℝ) : ℂ) = ((1 : ℂ) - Complex.I * (u : ℂ))⁻¹ * gint u t
    exact mainc_mul_abelW u (by linarith [ht.1] : 1 < t)
  have herr_pt : ∀ t ∈ Set.Ioc (N : ℝ) (M : ℝ),
      ‖(mangoldtTwistSum t u - mainc u t) * ((abelW t : ℝ) : ℂ)‖ ≤
        2 * C * (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t)) := by
    intro t ht
    have htN : (N : ℝ) ≤ t := le_of_lt ht.1
    have htM : t ≤ (M : ℝ) := ht.2
    have ht3 : 3 ≤ t := by
      have h3 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      linarith
    have ht1 : 1 < t := by linarith
    have hEst := hE t htN (le_trans htM hMR)
    have hw : abelW t ≤ 2 / (t ^ 2 * Real.log t) := abelW_le ht3
    have hwnn : 0 ≤ abelW t := abelW_nonneg ht1
    have hlogt : 0 < Real.log t := Real.log_pos ht1
    rw [norm_mul, norm_ofReal_of_nonneg hwnn]
    calc ‖mangoldtTwistSum t u - mainc u t‖ * abelW t
        ≤ (C * t * Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ))) * (2 / (t ^ 2 * Real.log t)) :=
          mul_le_mul hEst hw hwnn (by positivity)
      _ = 2 * C * (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t)) := by
          field_simp
  have hgint : Integrable (fun t : ℝ =>
      2 * C * (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t)))
      (volume.restrict (Set.Ioc (N : ℝ) (M : ℝ))) := by
    refine IntegrableOn.of_bound ?_ ?_ (2 * C * (1 / ((N : ℝ) * Real.log N))) ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact (by
        have h : Measurable (fun t : ℝ =>
            2 * C * (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t))) := by
          fun_prop
        exact h.aestronglyMeasurable)
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have htI : t ∈ Set.Ioc (N : ℝ) (M : ℝ) := ht
      have htN : (N : ℝ) ≤ t := le_of_lt htI.1
      have htM : t ≤ (M : ℝ) := htI.2
      have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
      have ht0 : (0:ℝ) < t := by linarith
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
      have hexp1 : Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have h1 : (0:ℝ) ≤ (Real.log t) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (le_of_lt hlogt) _
        nlinarith [hc, h1]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hden_le : 1 / (t * Real.log t) ≤ 1 / ((N : ℝ) * Real.log N) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul htN (Real.log_le_log hNpos htN) hlogNpos.le (by positivity)
      have h2C : (0:ℝ) ≤ 2 * C := by linarith
      calc 2 * C * (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t))
          = (2 * C) * (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) * (1 / (t * Real.log t))) := by ring
        _ ≤ (2 * C) * (1 * (1 / ((N : ℝ) * Real.log N))) := by
            apply mul_le_mul_of_nonneg_left _ h2C
            exact mul_le_mul hexp1 hden_le (by positivity) (by norm_num)
        _ = 2 * C * (1 / ((N : ℝ) * Real.log N)) := by ring
  have herr_bound : ‖∫ t in (N : ℝ)..(M : ℝ),
        (mangoldtTwistSum t u - mainc u t) * ((abelW t : ℝ) : ℂ)‖ ≤ 2 * C * Kerr := by
    have hmono : ∫ t in (N : ℝ)..(M : ℝ), ‖(mangoldtTwistSum t u - mainc u t) * ((abelW t : ℝ) : ℂ)‖
        ≤ ∫ t in (N : ℝ)..(M : ℝ),
            2 * C * (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t)) := by
      rw [intervalIntegral.integral_of_le hNMR, intervalIntegral.integral_of_le hNMR]
      refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hgint ?_
      show ∀ᵐ x ∂(volume.restrict (Set.Ioc (N : ℝ) (M : ℝ))),
        ‖(mangoldtTwistSum x u - mainc u x) * ((abelW x : ℝ) : ℂ)‖ ≤
          2 * C * (Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ)) / (x * Real.log x))
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun t ht => herr_pt t ht)
    have hval : ∫ t in (N : ℝ)..(M : ℝ),
        2 * C * (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t))
        = 2 * C * ∫ t in (N : ℝ)..(M : ℝ),
            (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t)) :=
      intervalIntegral.integral_const_mul (2 * C) _
    have hle : ∫ t in (N : ℝ)..(M : ℝ),
        (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t)) ≤ Kerr := hKerr
    calc ‖∫ t in (N : ℝ)..(M : ℝ),
          (mangoldtTwistSum t u - mainc u t) * ((abelW t : ℝ) : ℂ)‖
        ≤ ∫ t in (N : ℝ)..(M : ℝ), ‖(mangoldtTwistSum t u - mainc u t) * ((abelW t : ℝ) : ℂ)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hNMR
      _ ≤ ∫ t in (N : ℝ)..(M : ℝ),
            2 * C * (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t)) := hmono
      _ = 2 * C * ∫ t in (N : ℝ)..(M : ℝ),
            (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t)) := hval
      _ ≤ 2 * C * Kerr := mul_le_mul_of_nonneg_left hle (by linarith)
  have hint_main : IntervalIntegrable (fun t : ℝ => mainc u t * ((abelW t : ℝ) : ℂ)) volume (N : ℝ) (M : ℝ) := by
    rw [intervalIntegrable_iff]
    refine IntegrableOn.of_bound ?_ ?_ ((M : ℝ) * (2 / ((N : ℝ) ^ 2 * Real.log N))) ?_
    · rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
    · exact (by
        have h1 : Measurable (fun t : ℝ => mainc u t) := by unfold mainc; fun_prop
        have h3 : Measurable (fun t : ℝ => ((abelW t : ℝ) : ℂ)) := by unfold abelW; fun_prop
        exact (h1.mul h3).aestronglyMeasurable)
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have htI : t ∈ Set.Ioc (N : ℝ) (M : ℝ) := by rwa [Set.uIoc_of_le hNMR] at ht
      have htN : (N : ℝ) ≤ t := le_of_lt htI.1
      have htM : t ≤ (M : ℝ) := htI.2
      have ht3 : 3 ≤ t := by
        have h3 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
        linarith
      have ht1 : 1 < t := by linarith
      have hwnn : 0 ≤ abelW t := abelW_nonneg ht1
      rw [norm_mul, norm_ofReal_of_nonneg hwnn]
      have hb : ‖mainc u t‖ ≤ (M : ℝ) := le_trans (norm_mainc_le u (by linarith)) htM
      have hwle : abelW t ≤ 2 / ((N : ℝ) ^ 2 * Real.log N) := by
        refine (abelW_le ht3).trans ?_
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have hNsq : (N : ℝ) ^ 2 ≤ t ^ 2 := by
          have hNnn : (0:ℝ) ≤ N := by positivity
          have h : (N:ℝ) ≤ t := htN
          nlinarith
        exact mul_le_mul hNsq (Real.log_le_log (by positivity) htN) hlogNpos.le (by positivity)
      exact mul_le_mul hb hwle hwnn (by positivity)
  have hint_err : IntervalIntegrable
      (fun t : ℝ => (mangoldtTwistSum t u - mainc u t) * ((abelW t : ℝ) : ℂ)) volume (N : ℝ) (M : ℝ) := by
    rw [intervalIntegrable_iff]
    refine IntegrableOn.of_bound ?_ ?_ (2 * C * (1 / ((N : ℝ) * Real.log N))) ?_
    · rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
    · exact (by
        have h1 : Measurable (fun t : ℝ => mangoldtTwistSum t u) := measurable_mangoldtTwistSum u
        have h2 : Measurable (fun t : ℝ => mainc u t) := by unfold mainc; fun_prop
        have h3 : Measurable (fun t : ℝ => ((abelW t : ℝ) : ℂ)) := by unfold abelW; fun_prop
        exact ((h1.sub h2).mul h3).aestronglyMeasurable)
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have htI : t ∈ Set.Ioc (N : ℝ) (M : ℝ) := by rwa [Set.uIoc_of_le hNMR] at ht
      have htN : (N : ℝ) ≤ t := le_of_lt htI.1
      have htM : t ≤ (M : ℝ) := htI.2
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith [htI.1])
      have h1 := herr_pt t htI
      have hexp1 : Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hh : (0:ℝ) ≤ (Real.log t) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (le_of_lt hlogt) _
        nlinarith [hc, hh]
      have hmul : (N : ℝ) * Real.log N ≤ t * Real.log t := by
        have ht0 : (0:ℝ) ≤ t := by
          have h3 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
          linarith
        exact mul_le_mul htN (Real.log_le_log (by positivity) htN) hlogNpos.le ht0
      have htarget : 2 * C * (Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t))
          ≤ 2 * C * (1 / ((N : ℝ) * Real.log N)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        calc Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t)
            ≤ Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / ((N : ℝ) * Real.log N) :=
              div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity) hmul
          _ ≤ 1 / ((N : ℝ) * Real.log N) :=
              div_le_div_of_nonneg_right hexp1 (by positivity)
      exact h1.trans htarget
  have hInt_split : (∫ t in (N : ℝ)..(M : ℝ), mangoldtTwistSum t u * ((abelW t : ℝ) : ℂ))
      = (∫ t in (N : ℝ)..(M : ℝ), mainc u t * ((abelW t : ℝ) : ℂ))
        + ∫ t in (N : ℝ)..(M : ℝ), (mangoldtTwistSum t u - mainc u t) * ((abelW t : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_add hint_main hint_err]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hInt_bound : (∫ t in (N : ℝ)..(M : ℝ), mangoldtTwistSum t u * ((abelW t : ℝ) : ℂ)).re
      ≤ Kmi + 2 * C * Kerr := by
    rw [hInt_split, Complex.add_re, hmainint]
    have h1 : (((1 : ℂ) - Complex.I * (u : ℂ))⁻¹ * ∫ t in (N : ℝ)..(M : ℝ), gint u t).re ≤ Kmi := hKmi
    have h2 : (∫ t in (N : ℝ)..(M : ℝ),
        (mangoldtTwistSum t u - mainc u t) * ((abelW t : ℝ) : ℂ)).re ≤ 2 * C * Kerr :=
      (Complex.re_le_norm _).trans herr_bound
    linarith
  have hlogSum_bound : (∑ n ∈ Finset.Icc N M,
      (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((Real.log n : ℝ) : ℂ)) *
        (n : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ))).re ≤ Kmi + 2 * C * Kerr + (1 + C) + Cch := by
    rw [hlogSum_eq, Complex.add_re, Complex.sub_re]
    have h1 : (mangoldtTwistSum (M : ℝ) u * ((1 / ((M : ℝ) * Real.log M) : ℝ) : ℂ)).re ≤ 1 + C :=
      (Complex.re_le_norm _).trans hAMphi
    have h2 : -(mangoldtTwistSum ((N - 1 : ℕ) : ℝ) u *
        ((1 / ((N : ℝ) * Real.log N) : ℝ) : ℂ)).re ≤ Cch := by
      have h3 := Complex.abs_re_le_norm (mangoldtTwistSum ((N - 1 : ℕ) : ℝ) u *
        ((1 / ((N : ℝ) * Real.log N) : ℝ) : ℂ))
      have h4 := neg_le_abs (mangoldtTwistSum ((N - 1 : ℕ) : ℝ) u *
        ((1 / ((N : ℝ) * Real.log N) : ℝ) : ℂ)).re
      linarith [hANphi]
    linarith [hInt_bound]
  have hprime_bound : (∑ p ∈ (Finset.Icc N M).filter Nat.Prime,
      (p : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ))).re ≤ Kmi + 2 * C * Kerr + (1 + C) + Cch + 1 := by
    have hcorr := rcp_ppc u N M
    have hnorm : ‖(∑ p ∈ (Finset.Icc N M).filter Nat.Prime,
        (p : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)))
      - (∑ n ∈ Finset.Icc N M, (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((Real.log n : ℝ) : ℂ)) *
        (n : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)))‖ ≤ 1 := by
      rw [norm_sub_rev]
      exact hcorr
    have hre := Complex.re_le_norm ((∑ p ∈ (Finset.Icc N M).filter Nat.Prime,
        (p : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)))
      - (∑ n ∈ Finset.Icc N M, (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((Real.log n : ℝ) : ℂ)) *
        (n : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ))))
    rw [Complex.sub_re] at hre
    linarith [hlogSum_bound, hre, hnorm]
  have hrewrite : (∑ p ∈ (M.primesLE).filter (fun p => N ≤ p),
      (p : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)))
      = ∑ p ∈ (M.primesLE).filter (fun p => N ≤ p), ((p : ℂ) ^ (-(Complex.I * u))) / p := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    obtain ⟨hpM, -⟩ := Finset.mem_filter.mp hp
    have hpp : p.Prime := (Nat.mem_primesLE.mp hpM).2
    exact cpow_sub_one_eq p hpp.ne_zero u
  rw [filter_prime_Icc N M] at hprime_bound
  rw [hrewrite] at hprime_bound
  linarith [hprime_bound]


/-- **Conjunct 1**, from the `χ = 1` case of `vk_prime_sums` as a hypothesis. -/
theorem conj1_of_vk (c Cv : ℝ) (hc : 0 < c)
    (hvk : ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ, |u| ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) →
      ‖mangoldtTwistSum x u - (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖ ≤
        Cv * x * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ, 1 ≤ |u| →
    |u| ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) →
    (twistSum x u).re ≤ (4 / 5 : ℝ) * Real.log (Real.log (3 + |u|)) + C := by
  obtain ⟨Kerr, hKerrpos, hKerr⟩ := exp_decay_log_integral c hc
  obtain ⟨Cch, hCchpos, hCch⟩ := mangoldt_twist_chebyshev
  obtain ⟨Kl, hKlpos, hKl⟩ := rcp_int_large
  obtain ⟨Cmer, hCmer0, hMertens⟩ := mertens_recip_le
  refine ⟨max 0 (Kl + 2 * max Cv 0 * Kerr + Cch + max Cv 0 + 2 + Cmer + 1),
    le_max_left 0 _, ?_⟩
  intro x hx u hu1 hu2
  have hre : (twistSum x u).re = (twistSum x |u|).re := by
    rcases lt_trichotomy u 0 with h | h | h
    · rw [abs_of_neg h, twistSum_re_neg]
    · rw [h, abs_zero]
    · rw [abs_of_pos h]
  rw [hre]
  set v : ℝ := |u| with hv
  have hv1 : 1 ≤ v := hu1
  have hv2 : v ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) := hu2
  have hlogv0 : 0 ≤ Real.log v := Real.log_nonneg hv1
  set T : ℝ := Real.exp ((Real.log v) ^ (4 / 5 : ℝ)) with hT
  have hTx : T ≤ x := by
    have h1 : Real.log v ≤ (Real.log x) ^ (5 / 4 : ℝ) := by
      have h := Real.log_le_log (by linarith) hv2
      rwa [Real.log_exp] at h
    have h2 : ((Real.log v) ^ (4 / 5 : ℝ)) ≤ ((Real.log x) ^ (5 / 4 : ℝ)) ^ (4 / 5 : ℝ) :=
      Real.rpow_le_rpow hlogv0 h1 (by norm_num)
    have h3 : ((Real.log x) ^ (5 / 4 : ℝ)) ^ (4 / 5 : ℝ) = Real.log x := by
      rw [← Real.rpow_mul (le_of_lt (Real.log_pos (by linarith)))]; norm_num
    rw [h3] at h2
    calc T = Real.exp ((Real.log v) ^ (4 / 5 : ℝ)) := rfl
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr h2
      _ = x := Real.exp_log (by linarith)
  let N : ℕ := max ⌈T⌉₊ 4
  have hN4 : 4 ≤ N := le_max_right ⌈T⌉₊ 4
  have hN3 : 3 ≤ N := by omega
  have hN3r : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN3
  have hTN : T ≤ (N : ℝ) := by
    have h2 : T ≤ ((⌈T⌉₊ : ℕ) : ℝ) := Nat.le_ceil T
    exact h2.trans (by exact_mod_cast (le_max_left ⌈T⌉₊ 4))
  have hutt : ∀ t : ℝ, (N : ℝ) ≤ t → t ≤ x →
      v ≤ Real.exp ((Real.log t) ^ (5 / 4 : ℝ)) := by
    intro t htN htx
    have hTt : T ≤ t := hTN.trans htN
    have hlogt : Real.log T ≤ Real.log t := Real.log_le_log (by positivity) hTt
    rw [hT, Real.log_exp] at hlogt
    have h1 : ((Real.log v) ^ (4 / 5 : ℝ)) ^ (5 / 4 : ℝ) ≤ (Real.log t) ^ (5 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hlogt (by norm_num)
    have h2 : ((Real.log v) ^ (4 / 5 : ℝ)) ^ (5 / 4 : ℝ) = Real.log v := by
      rw [← Real.rpow_mul hlogv0]; norm_num
    rw [h2] at h1
    calc v = Real.exp (Real.log v) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp ((Real.log t) ^ (5 / 4 : ℝ)) := Real.exp_le_exp.mpr h1
  have hvk_le : ∀ y : ℝ, 3 ≤ y → ∀ w : ℝ, |w| ≤ Real.exp ((Real.log y) ^ (5 / 4 : ℝ)) →
      ‖mangoldtTwistSum y w - (y : ℂ) ^ (1 - Complex.I * w) / (1 - Complex.I * w)‖ ≤
        max Cv 0 * y * Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ)) := by
    intro y hy w hw
    refine (hvk y hy w hw).trans ?_
    have hy0 : (0:ℝ) ≤ y := by linarith
    have hexp0 : (0:ℝ) ≤ Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ)) := Real.exp_nonneg _
    have hxx : (0:ℝ) ≤ y * Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ)) := mul_nonneg hy0 hexp0
    calc Cv * y * Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ))
        = Cv * (y * Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ))) := by ring
      _ ≤ max Cv 0 * (y * Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left Cv 0) hxx
      _ = max Cv 0 * y * Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ)) := by ring
  have hsmall : (∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p => ¬ (N ≤ p)),
      ((p : ℂ) ^ (-(Complex.I * v))) / p).re ≤
      Real.log (Real.log ((N - 1 : ℕ) : ℝ)) + Cmer := by
    have h1 : (∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p => ¬ (N ≤ p)),
        ((p : ℂ) ^ (-(Complex.I * v))) / p).re ≤
        ∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p => ¬ (N ≤ p)), (1 : ℝ) / p := by
      rw [Complex.re_sum]
      exact Finset.sum_le_sum (fun p _ => prime_term_re_le p v)
    have h2 : (∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p => ¬ (N ≤ p)), (1 : ℝ) / p) ≤
        ∑ p ∈ ((N - 1 : ℕ)).primesLE, (1 : ℝ) / p := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Nat.mem_primesLE] at hp ⊢
        exact ⟨by omega, hp.1.2⟩
      · intro p _ _
        positivity
    have h3 := hMertens ((N - 1 : ℕ) : ℝ) (by exact_mod_cast (by omega : 3 ≤ N - 1))
    exact (h1.trans h2).trans (by simpa using h3)
  have hlog3le : Real.log (Real.log 3) ≤ 1 := by
    have h3pos : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have h1 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
    calc Real.log (Real.log 3) ≤ Real.log 2 := Real.log_le_log h3pos h1
      _ ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hloglog : Real.log (Real.log ((N - 1 : ℕ) : ℝ)) ≤
      (4 / 5 : ℝ) * Real.log (Real.log (3 + v)) + 1 := by
    have hlog3v0 : 0 ≤ Real.log (Real.log (3 + v)) :=
      Real.log_nonneg (one_le_log_of_three (by linarith))
    by_cases hT3 : T ≤ 3
    · have hN1 : ((N - 1 : ℕ) : ℝ) = 3 := by
        have h1 : ⌈T⌉₊ ≤ 3 := Nat.ceil_le.mpr hT3
        have h2 : N = 4 := by
          show max ⌈T⌉₊ 4 = 4
          exact max_eq_right (by omega : ⌈T⌉₊ ≤ 4)
        rw [h2]; norm_num
      rw [hN1]
      linarith [hlog3le, hlog3v0]
    · push Not at hT3
      have hlogv1 : 1 < Real.log v := by
        have h4 : Real.log 3 < (Real.log v) ^ (4 / 5 : ℝ) := by
          have h5 : Real.log 3 < Real.log T := Real.log_lt_log (by norm_num) hT3
          rwa [hT, Real.log_exp] at h5
        have h6 : (1:ℝ) < (Real.log v) ^ (4 / 5 : ℝ) :=
          lt_of_le_of_lt (le_of_lt (by
            have := Real.log_lt_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)
            have h7 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
            rw [Real.log_exp] at h7
            linarith)) h4
        have h7 : (1:ℝ) ^ (5 / 4 : ℝ) < ((Real.log v) ^ (4 / 5 : ℝ)) ^ (5 / 4 : ℝ) :=
          Real.rpow_lt_rpow (by norm_num) h6 (by norm_num)
        rw [Real.one_rpow, ← Real.rpow_mul hlogv0] at h7
        norm_num at h7
        exact h7
      have hN1le : ((N - 1 : ℕ) : ℝ) ≤ T := by
        have h1 : (N : ℝ) ≤ T + 1 := by
          have h2 : (N : ℝ) = max ((⌈T⌉₊ : ℕ) : ℝ) 4 := by
            rw [show ((N : ℝ)) = (((max ⌈T⌉₊ 4) : ℕ) : ℝ) from rfl, Nat.cast_max]
            norm_num
          have h3 : ((⌈T⌉₊ : ℕ) : ℝ) < T + 1 := Nat.ceil_lt_add_one (by positivity)
          have h4 : max ((⌈T⌉₊ : ℕ) : ℝ) 4 ≤ T + 1 := by
            apply max_le
            · linarith
            · linarith
          linarith
        have h6 : ((N - 1 : ℕ) : ℝ) = (N:ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ N)]; norm_num
        rw [h6]; linarith
      have hN1pos : (0:ℝ) < ((N - 1 : ℕ) : ℝ) := by
        have : (0:ℕ) < N - 1 := by omega
        exact_mod_cast this
      have h1 : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log T :=
        Real.log_le_log hN1pos hN1le
      have hlogN1pos : 0 < Real.log ((N - 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < N - 1))
      have h2 : Real.log (Real.log ((N - 1 : ℕ) : ℝ)) ≤ Real.log (Real.log T) :=
        Real.log_le_log hlogN1pos h1
      have h3 : Real.log (Real.log T) = (4 / 5 : ℝ) * Real.log (Real.log v) := by
        rw [hT, Real.log_exp, Real.log_rpow (by linarith : (0:ℝ) < Real.log v)]
      rw [h3] at h2
      have h4 : Real.log (Real.log v) ≤ Real.log (Real.log (3 + v)) :=
        Real.log_le_log (by linarith) (Real.log_le_log (by linarith) (by linarith))
      nlinarith [h2, h4, hlog3v0]
  have hmaxi : Kl + 2 * max Cv 0 * Kerr + Cch + max Cv 0 + 2 + Cmer + 1 ≤
      max 0 (Kl + 2 * max Cv 0 * Kerr + Cch + max Cv 0 + 2 + Cmer + 1) := le_max_right _ _
  by_cases hNM : N ≤ ⌊x⌋₊
  · have hNMr : (N : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hNM
    have hbig := abel_tail_bound v N x hx hN3
      (by
        have h1 : (N : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hNM
        exact h1.trans (Nat.floor_le (by linarith)))
      c (max Cv 0) hc.le (le_max_right Cv 0)
      (fun t htN htx => by
        have ht3 : (3:ℝ) ≤ t := le_trans hN3r htN
        refine hvk_le t ht3 v ?_
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v)]
        exact hutt t htN htx)
      Kerr Cch Kl hCchpos.le
      (hKerr (N:ℝ) ((⌊x⌋₊ : ℕ) : ℝ) hN3r hNMr)
      (fun t ht => hCch v t ht)
      (by
        have hav : 1 ≤ |v| := by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v)]; exact hv1
        have h2 := hKl v hav (N:ℝ) ((⌊x⌋₊ : ℕ) : ℝ) hN3r hNMr
        calc (((1 : ℂ) - Complex.I * (v : ℂ))⁻¹ *
              ∫ t in (N : ℝ)..((⌊x⌋₊ : ℕ) : ℝ), (t : ℂ) ^ (-(1 : ℂ) - Complex.I * (v : ℂ)) *
                (((1 + 1 / Real.log t) / Real.log t : ℝ) : ℂ)).re
            ≤ ‖((1 : ℂ) - Complex.I * (v : ℂ))⁻¹ *
              ∫ t in (N : ℝ)..((⌊x⌋₊ : ℕ) : ℝ), (t : ℂ) ^ (-(1 : ℂ) - Complex.I * (v : ℂ)) *
                (((1 + 1 / Real.log t) / Real.log t : ℝ) : ℂ)‖ := Complex.re_le_norm _
          _ ≤ ‖∫ t in (N : ℝ)..((⌊x⌋₊ : ℕ) : ℝ), (t : ℂ) ^ (-(1 : ℂ) - Complex.I * (v : ℂ)) *
                (((1 + 1 / Real.log t) / Real.log t : ℝ) : ℂ)‖ := by
              rw [norm_mul]
              exact mul_le_of_le_one_left (norm_nonneg _) (norm_inv_one_sub_I_mul_le_one v)
          _ ≤ Kl := by simpa only [rcpF] using h2)
    show (∑ p ∈ ⌊x⌋₊.primesLE, ((p : ℂ) ^ (-(Complex.I * v))) / p).re ≤ _
    rw [← Finset.sum_filter_add_sum_filter_not (⌊x⌋₊.primesLE) (fun p => N ≤ p)
      (fun p => ((p : ℂ) ^ (-(Complex.I * v))) / p), Complex.add_re]
    refine (add_le_add hbig hsmall).trans ?_
    have hCv0 : (0:ℝ) ≤ max Cv 0 := le_max_right Cv 0
    have h2Cv : (0:ℝ) ≤ 2 * max Cv 0 * Kerr := by
      exact mul_nonneg (by linarith) hKerrpos.le
    linarith [hloglog, hCmer0, hmaxi, hKlpos.le, hCchpos.le, hCv0, h2Cv]
  · push Not at hNM
    have hsub : (⌊x⌋₊.primesLE).filter (fun p => N ≤ p) = ∅ := by
      refine (Finset.filter_eq_empty_iff).mpr ?_
      intro p hp hple
      simp only [Nat.mem_primesLE] at hp
      omega
    show (∑ p ∈ ⌊x⌋₊.primesLE, ((p : ℂ) ^ (-(Complex.I * v))) / p).re ≤ _
    rw [← Finset.sum_filter_add_sum_filter_not (⌊x⌋₊.primesLE) (fun p => N ≤ p)
      (fun p => ((p : ℂ) ^ (-(Complex.I * v))) / p), hsub, Finset.sum_empty, zero_add]
    refine hsmall.trans ?_
    have hCv0 : (0:ℝ) ≤ max Cv 0 := le_max_right Cv 0
    have h2Cv : (0:ℝ) ≤ 2 * max Cv 0 * Kerr := by
      exact mul_nonneg (by linarith) hKerrpos.le
    linarith [hloglog, hCmer0, hmaxi, hKlpos.le, hCchpos.le, hCv0, h2Cv]

/-- **Conjunct 2**, from the `χ = 1` case of `vk_prime_sums` as a hypothesis. -/
theorem conj2_of_vk (c Cv : ℝ) (hc : 0 < c)
    (hvk : ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ, |u| ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) →
      ‖mangoldtTwistSum x u - (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖ ≤
        Cv * x * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ, 0 < |u| → |u| ≤ 1 →
    (twistSum x u).re ≤ Real.log (1 / |u|) + C := by
  obtain ⟨Kerr, hKerrpos, hKerr⟩ := exp_decay_log_integral c hc
  obtain ⟨Cch, hCchpos, hCch⟩ := mangoldt_twist_chebyshev
  obtain ⟨Ks, hKspos, hKs⟩ := rcp_int_small
  refine ⟨max 0 (Ks + 2 * max Cv 0 * Kerr + Cch + max Cv 0 + 2 + 1), le_max_left 0 _, ?_⟩
  intro x hx u hu1 hu2
  have hre : (twistSum x u).re = (twistSum x |u|).re := by
    rcases lt_trichotomy u 0 with h | h | h
    · rw [abs_of_neg h, twistSum_re_neg]
    · rw [h, abs_zero]
    · rw [abs_of_pos h]
  rw [hre]
  set v : ℝ := |u| with hv
  have hv1 : 0 < v := hu1
  have hv2 : v ≤ 1 := hu2
  have hx3 : (3:ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    have h1 : (3:ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx : ((3:ℕ):ℝ) ≤ x)
    exact_mod_cast h1
  have hutt : ∀ t : ℝ, (3:ℝ) ≤ t → t ≤ x → v ≤ Real.exp ((Real.log t) ^ (5 / 4 : ℝ)) := by
    intro t ht htx
    have h1 : (0:ℝ) ≤ (Real.log t) ^ (5 / 4 : ℝ) :=
      Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    calc v ≤ 1 := hv2
      _ = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp ((Real.log t) ^ (5 / 4 : ℝ)) := Real.exp_le_exp.mpr h1
  have hvk_le : ∀ y : ℝ, 3 ≤ y → ∀ w : ℝ, |w| ≤ Real.exp ((Real.log y) ^ (5 / 4 : ℝ)) →
      ‖mangoldtTwistSum y w - (y : ℂ) ^ (1 - Complex.I * w) / (1 - Complex.I * w)‖ ≤
        max Cv 0 * y * Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ)) := by
    intro y hy w hw
    refine (hvk y hy w hw).trans ?_
    have hy0 : (0:ℝ) ≤ y := by linarith
    have hexp0 : (0:ℝ) ≤ Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ)) := Real.exp_nonneg _
    have hxx : (0:ℝ) ≤ y * Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ)) := mul_nonneg hy0 hexp0
    calc Cv * y * Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ))
        = Cv * (y * Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ))) := by ring
      _ ≤ max Cv 0 * (y * Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left Cv 0) hxx
      _ = max Cv 0 * y * Real.exp (-c * (Real.log y) ^ (1 / 10 : ℝ)) := by ring
  have hx3' : (((3 : ℕ)) : ℝ) ≤ x := by
    rw [show (((3 : ℕ)) : ℝ) = 3 by norm_num]; exact hx
  have hbig := abel_tail_bound v 3 x hx (by norm_num) hx3'
    c (max Cv 0) hc.le (le_max_right Cv 0)
    (fun t ht3 htx => by
      refine hvk_le t ht3 v ?_
      rw [abs_of_nonneg (le_of_lt hv1)]
      exact hutt t ht3 htx)
    Kerr Cch (Real.log (1 / v) + Ks) hCchpos.le
    (hKerr 3 ((⌊x⌋₊ : ℕ) : ℝ) (by norm_num) hx3)
    (fun t ht => hCch v t ht)
    (by
      have h := hKs v (by rwa [abs_of_pos hv1]) (by rwa [abs_of_pos hv1]) ((⌊x⌋₊ : ℕ) : ℝ) hx3
      simpa only [rcpF, abs_of_pos hv1, Nat.cast_ofNat] using h)
  have hsmall : (∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p => ¬ (3 ≤ p)),
      ((p : ℂ) ^ (-(Complex.I * v))) / p).re ≤ 1 := by
    have h1 : (∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p => ¬ (3 ≤ p)),
        ((p : ℂ) ^ (-(Complex.I * v))) / p).re ≤
        ∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p => ¬ (3 ≤ p)), (1 : ℝ) / p := by
      rw [Complex.re_sum]
      exact Finset.sum_le_sum (fun p _ => prime_term_re_le p v)
    have hsub : (⌊x⌋₊.primesLE).filter (fun p => ¬ (3 ≤ p)) ⊆ ({2} : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_singleton]
      have h1 : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      have h2 : ¬ (3 ≤ p) := (Finset.mem_filter.mp hp).2
      have h3 : 2 ≤ p := h1.two_le
      have h4 : p ≤ 2 := by omega
      omega
    have h2 : (∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p => ¬ (3 ≤ p)), (1 : ℝ) / p) ≤ 1 := by
      calc (∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p => ¬ (3 ≤ p)), (1 : ℝ) / p)
          ≤ ∑ p ∈ ({2} : Finset ℕ), (1 : ℝ) / p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
        _ = 1 / 2 := by norm_num
        _ ≤ 1 := by norm_num
    exact h1.trans h2
  show (∑ p ∈ ⌊x⌋₊.primesLE, ((p : ℂ) ^ (-(Complex.I * v))) / p).re ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not (⌊x⌋₊.primesLE) (fun p => 3 ≤ p)
    (fun p => ((p : ℂ) ^ (-(Complex.I * v))) / p), Complex.add_re]
  have hmaxi2 : Ks + 2 * max Cv 0 * Kerr + Cch + max Cv 0 + 2 + 1 ≤
      max 0 (Ks + 2 * max Cv 0 * Kerr + Cch + max Cv 0 + 2 + 1) := le_max_right _ _
  refine (add_le_add hbig hsmall).trans ?_
  linarith [hmaxi2]

/-- **Conditional form**: the conclusion of `recip_twist_re_upper` from the `χ = 1` case of
`vk_prime_sums` stated as a hypothesis, so that downstream nodes can use this file while the
Vinogradov--Korobov node (`Work.BMF.vk_prime_sums`) is still being finished. -/
theorem recip_twist_re_upper_of_vk (c C : ℝ) (hc : 0 < c)
    (hvk : ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ, |u| ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) →
      ‖mangoldtTwistSum x u - (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖ ≤
        C * x * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ))) :
    (∃ C' : ℝ, 0 ≤ C' ∧ ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ, 1 ≤ |u| →
        |u| ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) →
        (∑ p ∈ ⌊x⌋₊.primesLE, ((p : ℂ) ^ (-(Complex.I * u))) / p).re ≤
          (4 / 5 : ℝ) * Real.log (Real.log (3 + |u|)) + C') ∧
    (∃ C' : ℝ, 0 ≤ C' ∧ ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ, 0 < |u| → |u| ≤ 1 →
        (∑ p ∈ ⌊x⌋₊.primesLE, ((p : ℂ) ^ (-(Complex.I * u))) / p).re ≤
          Real.log (1 / |u|) + C') := by
  constructor
  · simpa only [twistSum] using conj1_of_vk c C hc hvk
  · simpa only [twistSum] using conj2_of_vk c C hc hvk

/-- Upper bounds for the real part of the twisted reciprocal-prime sum
`∑_{p ≤ x} p^{-1-iu}`, deduced from `Work.BMF.vk_prime_sums`. -/
theorem recip_twist_re_upper :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ, 1 ≤ |u| →
        |u| ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) →
        (∑ p ∈ ⌊x⌋₊.primesLE, ((p : ℂ) ^ (-(Complex.I * u))) / p).re ≤
          (4 / 5 : ℝ) * Real.log (Real.log (3 + |u|)) + C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ, 0 < |u| → |u| ≤ 1 →
        (∑ p ∈ ⌊x⌋₊.primesLE, ((p : ℂ) ^ (-(Complex.I * u))) / p).re ≤
          Real.log (1 / |u|) + C) := by
  obtain ⟨c, C, hc, hvk⟩ := vk_prime_sums_one
  exact recip_twist_re_upper_of_vk c C hc hvk

end

end Work.BMF.liouville
