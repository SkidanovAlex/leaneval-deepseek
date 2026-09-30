import Mathlib
import Submission.Work.BMF.zeta_growth_defs
import Submission.Work.BMF.zeta_partial_sum_bound
import Submission.Work.BMF.zeta_approx_functional_eq
import Submission.Work.BMF.zeta_bdd_height
import Submission.Work.BMF.znl.zeta_bdd_box
import Submission.Work.BMF.VKPrimeSums.vk_block_bound_unshifted
import Submission.Work.BMF.sum_exp_le_integral_add_max
import Submission.Work.BMF.int_exp_cube_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKPrimeSums

open Finset
open scoped Real BigOperators

/-! ## Elementary `rpow` lemmas for dyadic blocks -/

/-- `((2^j : ℕ) : ℝ) ^ x = exp (log 2 * (j * x))`. -/
private lemma two_pow_cast_rpow (j : ℕ) (x : ℝ) :
    ((2^j : ℕ) : ℝ) ^ x = Real.exp (Real.log 2 * ((j:ℝ) * x)) := by
  have hcast : ((2^j : ℕ) : ℝ) = (2:ℝ) ^ j := by push_cast; ring
  rw [hcast, ← Real.rpow_natCast (2:ℝ) j, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]

/-- `log ((2^j : ℕ) : ℝ) = j log 2`. -/
private lemma log_two_pow_cast (j : ℕ) : Real.log ((2^j : ℕ) : ℝ) = (j:ℝ) * Real.log 2 := by
  have hcast : ((2^j : ℕ) : ℝ) = (2:ℝ) ^ j := by push_cast; ring
  rw [hcast, Real.log_pow]

/-- The exponent identity `j log 2 / (D (L / (j log 2))²) = (j log 2)³/(D L²)`. -/
private lemma delta_arith (D L : ℝ) (hD : 0 < D) (hL : 0 < L) (j : ℕ) (hj : 1 ≤ j) :
    (j:ℝ) * Real.log 2 / (D * (L / ((j:ℝ) * Real.log 2)) ^ 2)
      = ((j:ℝ) * Real.log 2) ^ 3 / (D * L ^ 2) := by
  have hj0 : (0:ℝ) < j := by exact_mod_cast hj
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : ((j:ℝ) * Real.log 2) ≠ 0 := by positivity
  field_simp

/-- `((2^j:ℕ):ℝ)^{-σ} ≤ 2^{-j}` for `σ ≥ 1`. -/
private lemma two_pow_neg_le (j : ℕ) {σ : ℝ} (hσ : 1 ≤ σ) :
    ((2^j : ℕ) : ℝ) ^ (-σ) ≤ (2:ℝ) ^ (-(j:ℝ)) := by
  rw [two_pow_cast_rpow j (-σ), Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [Real.exp_le_exp]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hkey : (j:ℝ) * (-σ) ≤ -((j:ℝ)) := by nlinarith
  exact mul_le_mul_of_nonneg_left hkey hlog2.le

/-- The VK saving for the dyadic block at scale `2^j`. -/
private lemma two_pow_delta_le (D L : ℝ) (hD : 0 < D) (hL : 0 < L) (j : ℕ) (hj : 1 ≤ j)
    {σ : ℝ} (hσ : 1 ≤ σ) :
    ((2^j : ℕ) : ℝ) ^ (1 - σ - 1 / (D * (L / Real.log ((2^j : ℕ) : ℝ)) ^ 2))
      ≤ Real.exp (-((((j:ℝ)*Real.log 2)^3)/(D * L^2))) := by
  rw [two_pow_cast_rpow j _, Real.exp_le_exp, log_two_pow_cast j]
  have hj0 : (0:ℝ) < j := by exact_mod_cast hj
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ := delta_arith D L hD hL j hj
  have hexpand : Real.log 2 * ((j:ℝ) * (1 - σ - 1 / (D * (L / ((j:ℝ) * Real.log 2)) ^ 2)))
      = Real.log 2 * ((j:ℝ) * (1 - σ)) - ((j:ℝ)*Real.log 2)^3/(D*L^2) := by
    rw [← hδ]; ring
  rw [hexpand]
  have h2 : (1 - σ) ≤ 0 := by linarith
  have h3 : (j:ℝ) * (1 - σ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hj0.le h2
  have h4 : Real.log 2 * ((j:ℝ) * (1 - σ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlog2.le h3
  linarith

/-- Block bound: for `j ≥ 1` and any truncation `M' ≤ 2 * 2^j`,
`‖∑_{2^j < n ≤ M'} n^{-σ-iT}‖ ≤ 2^{-j} + C exp(-(j log 2)³/(D (log T)²))`. -/
private lemma block_exp_bound (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hVK : Work.BMF.VKExpSum C D) {j M' : ℕ} (hj : 1 ≤ j) {T σ : ℝ}
    (hT2 : 2 ≤ T) (hNT : ((2^j : ℕ) : ℝ) ≤ T) (hM' : M' ≤ 2 * 2^j) (hσ : 1 ≤ σ) :
    ‖∑ n ∈ Finset.Ioc (2^j) M', ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖ ≤
      (2:ℝ) ^ (-(j:ℝ)) + C * Real.exp (-((((j:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) := by
  have hLpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hN2 : 2 ≤ 2^j := by
    have h : 1 < 2^j := Nat.one_lt_two_pow (by omega)
    omega
  have hσ0 : 0 ≤ σ := by linarith
  set X : ℝ := ((2^j : ℕ) : ℝ) with hXdef
  set δ : ℝ := 1 / (D * (Real.log T / Real.log ((2^j : ℕ) : ℝ)) ^ 2) with hδdef
  have hNpos : 0 < X := by rw [hXdef]; positivity
  have hbk : ‖∑ n ∈ Finset.Ioc (2^j) M', ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖
      ≤ (1 + C * X ^ (1 - δ)) * X ^ (-σ) := by
    have hraw := Work.BMF.vk_block_bound_unshifted C D hC hD hVK (2^j) M' hN2 T σ hT2 hNT hM' hσ0
    rw [← hδdef, ← hXdef] at hraw
    exact hraw
  have hstep : (1 + C * X ^ (1 - δ)) * X ^ (-σ) = X ^ (-σ) + C * X ^ (1 - σ - δ) := by
    have h1 : X ^ (1 - δ) * X ^ (-σ) = X ^ (1 - σ - δ) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    rw [add_mul, one_mul, mul_assoc, h1]
  calc ‖∑ n ∈ Finset.Ioc (2^j) M', ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖
      ≤ (1 + C * X ^ (1 - δ)) * X ^ (-σ) := hbk
    _ = X ^ (-σ) + C * X ^ (1 - σ - δ) := hstep
    _ ≤ (2:ℝ) ^ (-(j:ℝ)) + C * Real.exp (-((((j:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) := by
        apply add_le_add
        · rw [hXdef]; exact two_pow_neg_le j hσ
        · rw [hXdef, hδdef]
          exact mul_le_mul_of_nonneg_left
            (two_pow_delta_le D (Real.log T) hD hLpos j hj hσ) hC.le

/-- The dyadic telescoping `∑_{1 < n ≤ 2^J} g n = ∑_{j < J} ∑_{2^j < n ≤ 2^{j+1}} g n`. -/
private lemma sum_Ioc_two_pow (g : ℕ → ℂ) (J : ℕ) :
    ∑ n ∈ Finset.Ioc 1 (2^J), g n = ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), g n := by
  induction J with
  | zero => simp
  | succ J ih =>
      have h1 : (1:ℕ) ≤ 2^J := Nat.one_le_two_pow
      have h2 : 2^J ≤ 2^J * 2 := by omega
      have hdisj : Disjoint (Finset.Ioc 1 (2^J)) (Finset.Ioc (2^J) (2^J * 2)) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        simp only [Finset.mem_Ioc] at ha hb
        omega
      rw [Finset.sum_range_succ, pow_succ, ← Finset.Ioc_union_Ioc_eq_Ioc h1 h2, Finset.sum_union hdisj, ih]

/-- The geometric sum `∑_{j < J} (1/2)^j = 2 - 2 (1/2)^J`. -/
private lemma sum_half_pow (J : ℕ) :
    ∑ j ∈ Finset.range J, (1/2:ℝ)^j = 2 - 2*(1/2)^J := by
  induction J with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- Geometric bound `∑_{j < J} 2^{-j} ≤ 2`. -/
private lemma sum_two_pow_neg (J : ℕ) : ∑ j ∈ Finset.range J, (2:ℝ) ^ (-(j:ℝ)) ≤ 2 := by
  have hrewrite : ∀ j : ℕ, (2:ℝ) ^ (-(j:ℝ)) = (1/2:ℝ)^j := by
    intro j
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast (2:ℝ) j, one_div, inv_pow]
  simp only [hrewrite]
  rw [sum_half_pow J]
  have h2 : 0 ≤ 2*(1/2:ℝ)^J := by positivity
  linarith

/-- `1 < log 6`. -/
private lemma one_lt_log_six : (1:ℝ) < Real.log 6 := by
  have h : Real.log (Real.exp 1) < Real.log 6 :=
    Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
  rwa [Real.log_exp] at h

/-! ## Partial sums on `σ ≥ 1` -/

/-- Partial sums of `n^{-σ-iT}` for arbitrary truncation `M ≤ T`, on the half-plane `σ ≥ 1`. -/
theorem zeta_partial_sum_ge_one (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hVK : Work.BMF.VKExpSum C D) :
    ∃ A : ℝ, 0 < A ∧ ∀ σ T : ℝ, 1 ≤ σ → 3 ≤ T → ∀ M : ℕ, (M : ℝ) ≤ T →
      ‖∑ n ∈ Finset.Icc 1 M, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖ ≤
        A * Real.log (T + 3) ^ (6 / 7 : ℝ) := by
  set E : ℝ := (8 / Real.log 2) * D ^ (1/3:ℝ) with hEdef
  have hEnn : 0 ≤ E := by rw [hEdef]; positivity
  set A₀ : ℝ := C * (1 + E) with hA₀def
  have hA₀nn : 0 ≤ A₀ := by rw [hA₀def]; positivity
  have hCA₀ : C ≤ A₀ := by rw [hA₀def]; nlinarith [hEnn]
  refine ⟨4 + 2 * A₀, by linarith, ?_⟩
  intro σ T hσ1 hT3 M hMT
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTpos : 0 < T := by linarith
  have hLpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hT2 : 2 ≤ T := by linarith
  have hM01 : 1 ≤ Real.log (T + 3) := by
    have hle : Real.log 6 ≤ Real.log (T + 3) := Real.log_le_log (by norm_num) (by linarith)
    linarith [one_lt_log_six]
  have hlogM1 : 1 ≤ Real.log (T + 3) ^ (6/7:ℝ) := Real.one_le_rpow hM01 (by norm_num)
  set f : ℕ → ℂ := fun n => ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))) with hf
  have hfnorm : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ 1 := by
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    have hcastn : ((n : ℂ)) = (((n:ℝ)) : ℂ) := by push_cast; ring
    rw [hf]
    dsimp only
    rw [hcastn, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    have hre : (-((σ : ℂ) + (T : ℂ) * Complex.I)).re = -σ := by simp
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
  by_cases hM2 : M ≤ 2
  · have hcard : ‖∑ n ∈ Finset.Icc 1 M, f n‖ ≤ 2 := by
      have hsub : Finset.Icc 1 M ⊆ Finset.Icc 1 2 := by
        intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      have hcard2 : ((Finset.Icc 1 2 : Finset ℕ)).card = 2 := by decide
      calc ‖∑ n ∈ Finset.Icc 1 M, f n‖ ≤ ∑ n ∈ Finset.Icc 1 M, ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Icc 1 M, (1:ℝ) :=
            Finset.sum_le_sum (fun n hn => hfnorm n (by simp only [Finset.mem_Icc] at hn; omega))
        _ = ((Finset.Icc 1 M).card : ℝ) := by simp
        _ ≤ 2 := by
            have : (Finset.Icc 1 M).card ≤ (Finset.Icc 1 2 : Finset ℕ).card :=
              Finset.card_le_card hsub
            rw [hcard2] at this
            exact_mod_cast this
    have hfin : (2:ℝ) ≤ (4 + 2 * A₀) * Real.log (T + 3) ^ (6/7:ℝ) := by
      have h4 : (2:ℝ) ≤ 4 + 2 * A₀ := by linarith
      nlinarith [hlogM1, h4]
    linarith
  · have hMpos : M ≠ 0 := by omega
    have hM3 : 3 ≤ M := by omega
    set J : ℕ := Nat.log 2 M with hJdef
    have hJ1 : 1 ≤ J := by rw [hJdef]; exact Nat.log_pos_iff.mpr ⟨by omega, by norm_num⟩
    have h2J : 2^J ≤ M := by rw [hJdef]; exact Nat.pow_log_le_self 2 hMpos
    have hMlt : M < 2^(J+1) := by rw [hJdef]; exact Nat.lt_pow_succ_log_self (by norm_num) M
    have hNTlast : ((2^J : ℕ) : ℝ) ≤ T := by
      have h1 : ((2^J : ℕ) : ℝ) ≤ (M:ℝ) := by exact_mod_cast h2J
      linarith
    have hMlast : M ≤ 2 * 2^J := by
      have h : M < 2^J * 2 := by rw [← pow_succ]; exact hMlt
      omega
    have hblock : ∀ j ∈ Finset.range J,
        ‖∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n‖ ≤
          (2:ℝ) ^ (-(j:ℝ)) + C * Real.exp (-((((j:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        have hsingle : Finset.Ioc (2^0) (2^(0+1)) = ({2} : Finset ℕ) := by decide
        rw [hsingle, Finset.sum_singleton]
        have h21 : ‖f 2‖ ≤ 1 := hfnorm 2 (by norm_num)
        have hrhs : (1:ℝ) + C ≤ (2:ℝ) ^ (-(((0:ℕ):ℝ)))
            + C * Real.exp (-(((((0:ℕ):ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) := by
          have hq : (2:ℝ) ^ (-(((0:ℕ):ℝ))) = 1 := by simp
          have hq2 : Real.exp (-(((((0:ℕ):ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) = 1 := by simp
          rw [hq, hq2]
          linarith
        linarith
      · have hNTj : ((2^j : ℕ) : ℝ) ≤ T := by
          have h1 : 2^j ≤ 2^J := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2 : ((2^j : ℕ) : ℝ) ≤ (M:ℝ) := by exact_mod_cast (le_trans h1 h2J)
          linarith
        have hM'j : 2^(j+1) ≤ 2 * 2^j := by rw [pow_succ, mul_comm]
        exact block_exp_bound C D hC hD hVK hpos hT2 hNTj hM'j hσ1
    have hlast : ‖∑ n ∈ Finset.Ioc (2^J) M, f n‖ ≤
        (2:ℝ) ^ (-(J:ℝ)) + C * Real.exp (-((((J:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) :=
      block_exp_bound C D hC hD hVK hJ1 hT2 hNTlast hMlast hσ1
    have hdecomp : ∑ n ∈ Finset.Icc 1 M, f n
        = f 1 + ((∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n)
          + ∑ n ∈ Finset.Ioc (2^J) M, f n) := by
      have hdisj : Disjoint (Finset.Ioc 1 (2^J)) (Finset.Ioc (2^J) M) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        simp only [Finset.mem_Ioc] at ha hb
        omega
      rw [Finset.Icc_eq_cons_Ioc (by omega : 1 ≤ M), Finset.sum_cons]
      congr 1
      rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.one_le_two_pow (n := J)) h2J, Finset.sum_union hdisj,
        sum_Ioc_two_pow]
    have htri : ‖f 1 + ((∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n)
        + ∑ n ∈ Finset.Ioc (2^J) M, f n)‖
        ≤ 1 + (∑ j ∈ Finset.range J, ‖∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n‖)
          + ‖∑ n ∈ Finset.Ioc (2^J) M, f n‖ := by
      have h1 : ‖f 1‖ ≤ 1 := hfnorm 1 (le_refl 1)
      have h2 := norm_add_le (∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n)
        (∑ n ∈ Finset.Ioc (2^J) M, f n)
      have h3 := norm_sum_le (Finset.range J) (fun j => ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n)
      have h4 := norm_add_le (f 1) ((∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n)
        + ∑ n ∈ Finset.Ioc (2^J) M, f n)
      linarith
    have hsumblocks : (∑ j ∈ Finset.range J, ‖∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n‖)
        ≤ (∑ j ∈ Finset.range J, (2:ℝ) ^ (-(j:ℝ)))
          + C * ∑ j ∈ Finset.range J, Real.exp (-((((j:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) := by
      have hsplit : (∑ j ∈ Finset.range J, ((2:ℝ) ^ (-(j:ℝ))
            + C * Real.exp (-((((j:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2)))))
          = (∑ j ∈ Finset.range J, (2:ℝ) ^ (-(j:ℝ)))
            + C * ∑ j ∈ Finset.range J, Real.exp (-((((j:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      rw [← hsplit]
      exact Finset.sum_le_sum (fun j hj => hblock j hj)
    have hgeom : (∑ j ∈ Finset.range J, (2:ℝ) ^ (-(j:ℝ))) ≤ 2 := sum_two_pow_neg J
    have hsumexp : (∑ j ∈ Finset.range J, Real.exp (-((((j:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))))
        ≤ 1 + E * (Real.log T) ^ (2/3:ℝ) := by
      have h1 := Work.BMF.sum_exp_le_integral_add_max D (Real.log T) 0 hD hLpos le_rfl J
      have h2 := Work.BMF.int_exp_cube_le D (Real.log T) 0 hD hLpos le_rfl
      have h1' : (∑ j ∈ Finset.range J, Real.exp (-((((j:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))))
          ≤ 1 + 2 * ∫ x in Set.Ioi (0:ℝ),
              Real.exp (-(((x * Real.log 2)^3)/(D * (Real.log T)^2))) := by
        simpa using h1
      have h2' : (∫ x in Set.Ioi (0:ℝ), Real.exp (-(((x * Real.log 2)^3)/(D * (Real.log T)^2))))
          ≤ (4 / Real.log 2) * D ^ (1/3:ℝ) * (Real.log T) ^ (2/3:ℝ) := by
        simpa using h2
      calc (∑ j ∈ Finset.range J, Real.exp (-((((j:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))))
          ≤ 1 + 2 * ∫ x in Set.Ioi (0:ℝ),
              Real.exp (-(((x * Real.log 2)^3)/(D * (Real.log T)^2))) := h1'
        _ ≤ 1 + 2 * ((4 / Real.log 2) * D ^ (1/3:ℝ) * (Real.log T) ^ (2/3:ℝ)) := by linarith [h2']
        _ = 1 + (8 / Real.log 2) * D ^ (1/3:ℝ) * (Real.log T) ^ (2/3:ℝ) := by ring
        _ = 1 + E * (Real.log T) ^ (2/3:ℝ) := by rw [hEdef]
    have hlastB : ‖∑ n ∈ Finset.Ioc (2^J) M, f n‖
        ≤ 1 + C * Real.exp (-((((J:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) := by
      have h2Jpow : (2:ℝ) ^ (-(J:ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1:ℝ) ≤ 2)
          (neg_nonpos.mpr (Nat.cast_nonneg J))
      linarith [hlast]
    have hbound1 : ‖∑ n ∈ Finset.Icc 1 M, f n‖
        ≤ 4 + C * (1 + E * (Real.log T) ^ (2/3:ℝ))
          + C * Real.exp (-((((J:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) := by
      have h5 : C * (∑ j ∈ Finset.range J, Real.exp (-((((j:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))))
          ≤ C * (1 + E * (Real.log T) ^ (2/3:ℝ)) := mul_le_mul_of_nonneg_left hsumexp hC.le
      rw [hdecomp]
      linarith [htri, hsumblocks, hgeom, h5, hlastB]
    have hL23 : (Real.log T) ^ (2/3:ℝ) ≤ Real.log (T + 3) ^ (6/7:ℝ) := by
      have hle : Real.log T ≤ Real.log (T + 3) := Real.log_le_log hTpos (by linarith)
      have h1 : (Real.log T) ^ (2/3:ℝ) ≤ (Real.log (T + 3)) ^ (2/3:ℝ) :=
        Real.rpow_le_rpow hLpos.le hle (by norm_num)
      have h2 : (Real.log (T + 3)) ^ (2/3:ℝ) ≤ (Real.log (T + 3)) ^ (6/7:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hM01 (by norm_num)
      linarith
    have hexpJ : C * Real.exp (-((((J:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2)))
        ≤ C * Real.log (T + 3) ^ (6/7:ℝ) := by
      have h1 : Real.exp (-((((J:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) ≤ 1 := by
        rw [← Real.exp_zero, Real.exp_le_exp]
        have h2 : 0 ≤ (((J:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2) := by positivity
        linarith
      calc C * Real.exp (-((((J:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) ≤ C * 1 :=
            mul_le_mul_of_nonneg_left h1 hC.le
        _ ≤ C * Real.log (T + 3) ^ (6/7:ℝ) := mul_le_mul_of_nonneg_left hlogM1 hC.le
    have hfinal : ‖∑ n ∈ Finset.Icc 1 M, f n‖ ≤ (4 + 2 * A₀) * Real.log (T + 3) ^ (6/7:ℝ) := by
      have hE1 : E * (Real.log T) ^ (2/3:ℝ) ≤ E * Real.log (T + 3) ^ (6/7:ℝ) :=
        mul_le_mul_of_nonneg_left hL23 hEnn
      have hC1 : C * (1 + E * (Real.log T) ^ (2/3:ℝ)) ≤ C * (1 + E) * Real.log (T + 3) ^ (6/7:ℝ) := by
        have hb : (1:ℝ) + E * (Real.log T) ^ (2/3:ℝ)
            ≤ (1 + E) * Real.log (T + 3) ^ (6/7:ℝ) := by
          have h1 : (1:ℝ) ≤ 1 * Real.log (T + 3) ^ (6/7:ℝ) := by simpa using hlogM1
          calc (1:ℝ) + E * (Real.log T) ^ (2/3:ℝ)
              ≤ 1 * Real.log (T + 3) ^ (6/7:ℝ) + E * Real.log (T + 3) ^ (6/7:ℝ) :=
                add_le_add h1 hE1
            _ = (1 + E) * Real.log (T + 3) ^ (6/7:ℝ) := by ring
        calc C * (1 + E * (Real.log T) ^ (2/3:ℝ))
            ≤ C * ((1 + E) * Real.log (T + 3) ^ (6/7:ℝ)) := mul_le_mul_of_nonneg_left hb hC.le
          _ = C * (1 + E) * Real.log (T + 3) ^ (6/7:ℝ) := by ring
      have hsum2 : C * (1+E) + C ≤ 2 * A₀ := by rw [hA₀def]; nlinarith [hCA₀]
      have hM0nn : 0 ≤ Real.log (T + 3) ^ (6/7:ℝ) := Real.rpow_nonneg (le_trans zero_le_one hM01) _
      calc ‖∑ n ∈ Finset.Icc 1 M, f n‖
          ≤ 4 + C * (1 + E * (Real.log T) ^ (2/3:ℝ))
            + C * Real.exp (-((((J:ℝ)*Real.log 2)^3)/(D * (Real.log T)^2))) := hbound1
        _ ≤ 4 + (C * (1+E)) * Real.log (T + 3) ^ (6/7:ℝ) + C * Real.log (T + 3) ^ (6/7:ℝ) := by
            linarith [hC1, hexpJ]
        _ = 4 + (C * (1+E) + C) * Real.log (T + 3) ^ (6/7:ℝ) := by ring
        _ ≤ 4 + (2 * A₀) * Real.log (T + 3) ^ (6/7:ℝ) := by
            have := mul_le_mul_of_nonneg_right hsum2 hM0nn
            linarith
        _ ≤ (4 + 2 * A₀) * Real.log (T + 3) ^ (6/7:ℝ) := by
            have h4 : (4:ℝ) ≤ 4 * Real.log (T + 3) ^ (6/7:ℝ) := by linarith [hlogM1]
            linarith
    exact hfinal

/-! ## `ζ` on `1 ≤ σ ≤ 2` from the partial-sum bound -/

private lemma norm_re_im_le (σ T : ℝ) (hσ : 0 ≤ σ) (hT : 0 ≤ T) :
    ‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ σ + T := by
  have h := Complex.norm_le_abs_re_add_abs_im ((σ : ℂ) + (T : ℂ) * Complex.I)
  have h1 : (((σ : ℂ) + (T : ℂ) * Complex.I).re) = σ := by simp
  have h2 : (((σ : ℂ) + (T : ℂ) * Complex.I).im) = T := by simp
  rw [h1, h2, abs_of_nonneg hσ, abs_of_nonneg hT] at h
  exact h

theorem zeta_le_ge_one_of_psb (Aps : ℝ) (hAps : 0 < Aps)
    (hPS : ∀ σ T : ℝ, 1 ≤ σ → 3 ≤ T → ∀ M : ℕ, (M : ℝ) ≤ T →
      ‖∑ n ∈ Finset.Icc 1 M, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖ ≤
        Aps * Real.log (T + 3) ^ (6 / 7 : ℝ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ σ T : ℝ, 1 ≤ σ → σ ≤ 2 → 3 ≤ T →
      ‖riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        A * Real.log (T + 3) ^ (6 / 7 : ℝ) := by
  refine ⟨Aps + 5, by linarith, ?_⟩
  intro σ T hσ1 hσ2 hT3
  have hTpos : 0 < T := by linarith
  have hT0 : T ≠ 0 := by linarith
  set N : ℕ := ⌊T⌋₊ with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    apply Nat.le_floor
    push_cast
    linarith
  have hNle : (N : ℝ) ≤ T := by rw [hNdef]; exact Nat.floor_le hTpos.le
  have hNhalf : T / 2 ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one T
    rw [hNdef]
    linarith
  have hσ0 : 0 < σ := by linarith
  have hM0 : 1 ≤ Real.log (T + 3) ^ (6/7:ℝ) := by
    have h6 : (1:ℝ) < Real.log (T + 3) := by
      have hle : Real.log 6 ≤ Real.log (T + 3) := Real.log_le_log (by norm_num) (by linarith)
      linarith [one_lt_log_six]
    exact Real.one_le_rpow h6.le (by norm_num)
  have hem := Work.BMF.zeta_sub_Icc_sum_le (σ := σ) (t := T) hσ0 hT0 N hN1
  rw [abs_of_pos hTpos] at hem
  have hps := hPS σ T hσ1 hT3 N hNle
  have hrem : (N : ℝ) ^ (1 - σ) / T + (‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ) * (N : ℝ) ^ (-σ)
      ≤ 5 := by
    have hN1r : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    have h1 : (N:ℝ) ^ (1 - σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
    have h2 : (N:ℝ) ^ (1 - σ) / T ≤ 1 := by
      rw [div_le_one hTpos]
      linarith [h1, hT3]
    have h3 : ‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ σ + T :=
      norm_re_im_le σ T hσ0.le hTpos.le
    have h4 : ((σ : ℝ) + T) / σ ≤ 1 + T := by
      rw [div_le_iff₀ hσ0]
      nlinarith
    have h5 : (N:ℝ) ^ (-σ) ≤ (N:ℝ) ^ (-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    have h6 : (N:ℝ) ^ (-(1:ℝ)) ≤ 2 / T := by
      rw [Real.rpow_neg_one]
      have h7 : (N:ℝ)⁻¹ ≤ (T/2)⁻¹ := by
        have h7' := one_div_le_one_div_of_le (a := T/2) (b := (N:ℝ)) (by linarith) hNhalf
        rwa [one_div, one_div] at h7'
      have h8 : (T/2)⁻¹ = 2 / T := by field_simp
      linarith
    have h8 : (‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ) * (N : ℝ) ^ (-σ) ≤ (1 + T) * (2/T) := by
      apply mul_le_mul
      · calc ‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ ≤ ((σ : ℝ) + T) / σ :=
              div_le_div_of_nonneg_right h3 hσ0.le
          _ ≤ 1 + T := h4
      · exact le_trans h5 h6
      · positivity
      · positivity
    have h9 : (1 + T) * (2/T) ≤ 4 := by
      have : (1 + T) * 2 ≤ 4 * T := by linarith
      rw [mul_div_assoc', div_le_iff₀ hTpos]
      linarith
    linarith
  have htri : ‖riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ ‖riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I)
          - ∑ n ∈ Finset.Icc 1 N, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖
        + ‖∑ n ∈ Finset.Icc 1 N, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖ := by
    have h := norm_add_le
      (riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I)
        - ∑ n ∈ Finset.Icc 1 N, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))))
      (∑ n ∈ Finset.Icc 1 N, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))))
    have heq : (riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I)
          - ∑ n ∈ Finset.Icc 1 N, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))))
        + (∑ n ∈ Finset.Icc 1 N, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))))
        = riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I) := by ring
    rwa [heq] at h
  have hfinal : ‖riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ (Aps + 5) * Real.log (T + 3) ^ (6/7:ℝ) := by
    have h10 : ‖riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I)‖
        ≤ Aps * Real.log (T + 3) ^ (6/7:ℝ) + 5 := by
      linarith [le_trans htri (add_le_add hem hps)]
    have h11 : 5 ≤ 5 * Real.log (T + 3) ^ (6/7:ℝ) := by linarith [hM0]
    nlinarith [h10, h11]
  exact hfinal

/-! ## The main bound -/

/-- `(1 - σ)^{3/2} L ≤ 1` in the Vinogradov–Korobov region, for `L ≤ log(|t|+3)`. -/
private lemma vk_exponent_bound {σ M₀ L : ℝ} (hM01 : 1 ≤ M₀) (hL0 : 0 ≤ L) (hLM : L ≤ M₀)
    (hσ1 : σ < 1) (hσlo : 1 - (1/100) * M₀ ^ (-(6/7:ℝ)) ≤ σ) :
    (1 - σ) ^ (3/2:ℝ) * L ≤ 1 := by
  have hM0pos : 0 < M₀ := lt_of_lt_of_le zero_lt_one hM01
  have h1 : 1 - σ ≤ (1/100) * M₀ ^ (-(6/7:ℝ)) := by linarith
  have h0 : 0 ≤ 1 - σ := by linarith
  have h32 : (1 - σ) ^ (3/2:ℝ) ≤ (1/100)^(3/2:ℝ) * M₀ ^ (-(9/7:ℝ)) := by
    calc (1 - σ) ^ (3/2:ℝ) ≤ ((1/100) * M₀ ^ (-(6/7:ℝ))) ^ (3/2:ℝ) :=
          Real.rpow_le_rpow h0 h1 (by norm_num)
      _ = (1/100)^(3/2:ℝ) * (M₀ ^ (-(6/7:ℝ))) ^ (3/2:ℝ) := Real.mul_rpow (by norm_num) (by positivity)
      _ = (1/100)^(3/2:ℝ) * M₀ ^ (-(9/7:ℝ)) := by
          congr 1
          rw [← Real.rpow_mul hM0pos.le]
          norm_num
  have h9 : M₀ ^ (-(9/7:ℝ)) * M₀ = M₀ ^ (-(2/7:ℝ)) := by
    have h9a : M₀ ^ (-(9/7:ℝ)) * M₀ ^ (1:ℝ) = M₀ ^ (-(9/7:ℝ) + 1) :=
      (Real.rpow_add hM0pos (-(9/7:ℝ)) 1).symm
    rw [Real.rpow_one] at h9a
    rw [h9a]
    congr 1
    norm_num
  have h2 : (1/100:ℝ)^(3/2:ℝ) * M₀ ^ (-(2/7:ℝ)) ≤ 1 := by
    have ha : (1/100:ℝ)^(3/2:ℝ) ≤ 1 := by
      calc (1/100:ℝ)^(3/2:ℝ) ≤ (1:ℝ)^(3/2:ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        _ = 1 := Real.one_rpow _
    have hb : M₀ ^ (-(2/7:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM01 (by norm_num)
    calc (1/100:ℝ)^(3/2:ℝ) * M₀ ^ (-(2/7:ℝ)) ≤ 1 * 1 :=
          mul_le_mul ha hb (Real.rpow_nonneg hM0pos.le _) (by norm_num)
      _ = 1 := by ring
  calc (1 - σ) ^ (3/2:ℝ) * L ≤ ((1/100)^(3/2:ℝ) * M₀ ^ (-(9/7:ℝ))) * L :=
        mul_le_mul_of_nonneg_right h32 hL0
    _ ≤ ((1/100)^(3/2:ℝ) * M₀ ^ (-(9/7:ℝ))) * M₀ := by
        apply mul_le_mul_of_nonneg_left hLM
        positivity
    _ = (1/100)^(3/2:ℝ) * (M₀ ^ (-(9/7:ℝ)) * M₀) := by ring
    _ = (1/100)^(3/2:ℝ) * M₀ ^ (-(2/7:ℝ)) := by rw [h9]
    _ ≤ 1 := h2

theorem zeta_norm_le_region2 (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hVK : Work.BMF.VKExpSum C D) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ σ t : ℝ, 3 ≤ |t| →
      1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * Real.log (|t| + 3) ^ (6 / 7 : ℝ) := by
  obtain ⟨Aps, hAps, hPS⟩ := Work.BMF.zeta_partial_sum_bound C D hC hD hVK
  obtain ⟨Aps1, hAps1, hPS1⟩ := zeta_partial_sum_ge_one C D hC hD hVK
  obtain ⟨Age1, hAge1, hge1⟩ := zeta_le_ge_one_of_psb Aps1 hAps1 hPS1
  obtain ⟨C₁, T₀, hC₁, hT₀, hAFE⟩ := Work.BMF.zeta_approx_functional_eq
  obtain ⟨Ab1, hAb1, hb1⟩ := Work.BMF.zeta_bdd_height (max T₀ 3)
    (le_trans (by norm_num) (le_max_right T₀ 3))
  obtain ⟨Ab2, hAb2, hb2⟩ := Work.BMF.znl.zeta_bdd_box (max T₀ 3)
  set K : ℝ := (2/9) * Real.sqrt (3*D) with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  set A : ℝ := max Age1 (max (C₁ + Aps * Real.exp K) (max Ab1 Ab2)) with hAdef
  have hApos : 0 < A := lt_of_lt_of_le hAge1 (le_max_left _ _)
  refine ⟨A, 1/100, hApos, by norm_num, ?_⟩
  intro σ t ht hσlo hσhi
  set M₀ : ℝ := Real.log (|t| + 3) with hM0def
  have hT3 : 3 ≤ |t| := ht
  have hM01 : 1 ≤ M₀ := by
    rw [hM0def]
    have hle : Real.log 6 ≤ Real.log (|t| + 3) := Real.log_le_log (by norm_num) (by linarith)
    linarith [one_lt_log_six]
  have hM0pos : 0 < M₀ := lt_of_lt_of_le zero_lt_one hM01
  have hM0nn : 0 ≤ M₀ ^ (6/7:ℝ) := Real.rpow_nonneg hM0pos.le _
  have hlogM1 : 1 ≤ M₀ ^ (6/7:ℝ) := Real.one_le_rpow hM01 (by norm_num)
  have hσlow : 1 - (1/100) * M₀ ^ (-(6/7:ℝ)) ≤ σ := by
    rw [hM0def] at hσlo ⊢
    exact hσlo
  have hcM : (1/100:ℝ) * M₀ ^ (-(6/7:ℝ)) ≤ 1/16 := by
    have h : M₀ ^ (-(6/7:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM01 (by norm_num)
    linarith
  have hcM2 : (1/100:ℝ) * M₀ ^ (-(6/7:ℝ)) ≤ 1/2 := by linarith
  have hAage : Age1 ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hAafe : C₁ + Aps * Real.exp K ≤ A := by
    rw [hAdef]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hAb1le : Ab1 ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hAb2le : Ab2 ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  by_cases hH : |t| ≤ max T₀ 3
  · by_cases hσ1 : σ ≤ 1
    · have hσhalf : (1:ℝ)/2 ≤ σ := by linarith [hσlow, hcM2]
      have hb := hb1 σ t hσhalf hσ1 ht hH
      calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Ab1 := hb
        _ ≤ A * M₀ ^ (6/7:ℝ) := by
            have h : Ab1 ≤ A * 1 := by linarith
            calc Ab1 ≤ A * 1 := h
              _ ≤ A * M₀ ^ (6/7:ℝ) := mul_le_mul_of_nonneg_left hlogM1 hApos.le
        _ = A * Real.log (|t| + 3) ^ (6/7:ℝ) := by rw [hM0def]
    · have hσge1 : 1 ≤ σ := le_of_lt (not_le.mp hσ1)
      have h2t : (2:ℝ) ≤ |t| := by linarith
      have hb := hb2 σ t hσge1 hσhi h2t hH
      calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Ab2 := hb
        _ ≤ A * M₀ ^ (6/7:ℝ) := by
            have h : Ab2 ≤ A * 1 := by linarith
            calc Ab2 ≤ A * 1 := h
              _ ≤ A * M₀ ^ (6/7:ℝ) := mul_le_mul_of_nonneg_left hlogM1 hApos.le
        _ = A * Real.log (|t| + 3) ^ (6/7:ℝ) := by rw [hM0def]
  · have hT0le : T₀ ≤ |t| := le_of_lt (lt_of_le_of_lt (le_max_left T₀ 3) (lt_of_not_ge hH))
    by_cases hσ1 : σ < 1
    · have hσ15 : (15:ℝ)/16 ≤ σ := by linarith [hσlow, hcM]
      have hafe := hAFE σ t hσ15 (le_of_lt hσ1) hT0le
      have hps := hPS σ t (by linarith) hσ1 ht
      have hL0 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
      have hLM : Real.log |t| ≤ M₀ := by
        rw [hM0def]
        exact Real.log_le_log (by linarith) (by linarith)
      have hexp1 : (1 - σ) ^ (3/2:ℝ) * Real.log |t| ≤ 1 :=
        vk_exponent_bound hM01 hL0 hLM hσ1 hσlow
      have hKbound : |t| ^ (K * (1 - σ) ^ (3/2:ℝ)) ≤ Real.exp K := by
        rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < |t|)]
        rw [Real.exp_le_exp]
        have hle : Real.log |t| * (K * (1 - σ) ^ (3/2:ℝ))
            = K * ((1 - σ) ^ (3/2:ℝ) * Real.log |t|) := by ring
        rw [hle]
        calc K * ((1 - σ) ^ (3/2:ℝ) * Real.log |t|) ≤ K * 1 := mul_le_mul_of_nonneg_left hexp1 hKnn
          _ = K := by ring
      have hlog23 : (Real.log |t|) ^ (2/3:ℝ) ≤ M₀ ^ (6/7:ℝ) := by
        have h1 : (Real.log |t|) ^ (2/3:ℝ) ≤ M₀ ^ (2/3:ℝ) :=
          Real.rpow_le_rpow hL0 hLM (by norm_num)
        have h2 : M₀ ^ (2/3:ℝ) ≤ M₀ ^ (6/7:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hM01 (by norm_num)
        linarith
      have htri : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
              - ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖
            + ‖∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ := by
        have h := norm_add_le
          (riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
            - ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))
          (∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))
        have heq : (riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
              - ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))
            + (∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))
            = riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := by ring
        rwa [heq] at h
      have hstep : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C₁ + Aps * (Real.exp K) * M₀ ^ (6/7:ℝ) := by
        have h1 : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
              - ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ ≤ C₁ := hafe
        have h2 : ‖∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖
            ≤ Aps * Real.exp K * M₀ ^ (6/7:ℝ) := by
          calc ‖∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖
              ≤ Aps * |t| ^ (K * (1 - σ) ^ (3/2:ℝ)) * (Real.log |t|) ^ (2/3:ℝ) := hps
            _ ≤ Aps * Real.exp K * M₀ ^ (6/7:ℝ) := by
                apply mul_le_mul
                · apply mul_le_mul_of_nonneg_left hKbound hAps.le
                · exact hlog23
                · have := Real.rpow_nonneg hL0 (2/3:ℝ); positivity
                · positivity
        linarith
      calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C₁ + Aps * Real.exp K * M₀ ^ (6/7:ℝ) := hstep
        _ ≤ (C₁ + Aps * Real.exp K) * M₀ ^ (6/7:ℝ) := by
            have h : C₁ ≤ C₁ * M₀ ^ (6/7:ℝ) := by
              simpa using mul_le_mul_of_nonneg_left hlogM1 hC₁.le
            linarith
        _ ≤ A * M₀ ^ (6/7:ℝ) := mul_le_mul_of_nonneg_right hAafe hM0nn
        _ = A * Real.log (|t| + 3) ^ (6/7:ℝ) := by rw [hM0def]
    · have hσge1 : 1 ≤ σ := not_lt.mp hσ1
      have hb := hge1 σ |t| hσge1 hσhi ht
      have habs : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          = ‖riemannZeta ((σ : ℂ) + (((|t|:ℝ)) : ℂ) * Complex.I)‖ := by
        by_cases ht0 : 0 ≤ t
        · rw [abs_of_nonneg ht0]
        · rw [abs_of_neg (lt_of_not_ge ht0)]
          have h1 : riemannZeta ((σ:ℂ) + (t:ℂ)*Complex.I)
              = (starRingEnd ℂ) (riemannZeta ((σ:ℂ) + ((-t:ℝ):ℂ)*Complex.I)) := by
            have h2 : (starRingEnd ℂ) ((σ:ℂ) + ((-t:ℝ):ℂ)*Complex.I)
                = (σ:ℂ) + (t:ℂ)*Complex.I := by
              simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
              push_cast
              ring
            rw [← h2, riemannZeta_conj]
          rw [h1, Complex.norm_conj]
      calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          = ‖riemannZeta ((σ : ℂ) + (((|t|:ℝ)) : ℂ) * Complex.I)‖ := habs
        _ ≤ Age1 * M₀ ^ (6/7:ℝ) := hb
        _ ≤ A * M₀ ^ (6/7:ℝ) := mul_le_mul_of_nonneg_right hAage hM0nn
        _ = A * Real.log (|t| + 3) ^ (6/7:ℝ) := by rw [hM0def]

end Work.BMF.VKPrimeSums
