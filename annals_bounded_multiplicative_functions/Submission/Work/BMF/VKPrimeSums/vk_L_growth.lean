import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.VKStripDefs
import Submission.Work.BMF.VKGrowth
import Submission.Work.BMF.znl.zeta_norm_upper_log
import Submission.Work.BMF.zeta_approx_functional_eq
import Submission.Commons.Analysis.ExponentialSums.kusmin_landau

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace Work.BMF.VKPrimeSums

open Finset Complex
open scoped BigOperators

noncomputable section

/-! ## 1. Kusmin–Landau for a shifted exponential sum -/

/-- For `0 ≤ y ≤ 1/2` the distance to the nearest integer is `y` itself. -/
private lemma intDist_eq_self {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) :
    Submission.VanDerCorput.intDist y = y := by
  have hlt : y < 1 := by linarith
  have hfl : ⌊y⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, hlt⟩
  have hf : Int.fract y = y := by
    rw [← Submission.IntDistRegion.sub_floor_eq_fract y, hfl]
    simp
  rw [show Submission.VanDerCorput.intDist y = min (Int.fract y) (1 - Int.fract y) from rfl, hf]
  exact min_eq_left (by linarith)

/-- `exp (2πi · (-(T/2π) log (h+u))) = (h+u)^{-iT}`. -/
private lemma exp_eq_cpow_shift {u T : ℝ} (hu : 0 < u) (h : ℕ) :
    Complex.exp (((2 * Real.pi * (-(T / (2 * Real.pi)) * Real.log ((h : ℝ) + u)) : ℝ) : ℂ) *
        Complex.I) = ((((h : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (T : ℂ))) := by
  have hpos : 0 < (h : ℝ) + u := by positivity
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt hpos)),
    ← Complex.ofReal_log (le_of_lt hpos)]
  congr 1
  rw [show (2 * Real.pi * (-(T / (2 * Real.pi)) * Real.log ((h : ℝ) + u)))
      = -(T * Real.log ((h : ℝ) + u)) by field_simp]
  push_cast
  ring

/-- Kusmin–Landau (first-derivative test) for the shifted exponential sum: for `0 < u ≤ 1`,
`T ≥ 3` and `T/2 ≤ M ≤ m` the partial sums over `(M,m]` are bounded by `2π(m+u)/T`. -/
private lemma kl_shift {u T : ℝ} (hu : 0 < u) (hT : 3 ≤ T) :
    ∀ (M m : ℕ), T / 2 ≤ (M : ℝ) → M ≤ m →
      ‖∑ h ∈ Finset.Ioc M m, ((((h : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (T : ℂ)))‖ ≤
        2 * Real.pi * ((m : ℝ) + u) / T := by
  intro M m hMT hMm
  have hT0 : (0:ℝ) < T := by linarith
  have hM1r : (1 : ℝ) ≤ (M : ℝ) := by linarith [hT, hMT]
  have hMmZ : (M : ℤ) ≤ (m : ℤ) := by exact_mod_cast hMm
  have hmem : ∀ x ∈ Set.Icc ((M : ℤ) : ℝ) ((m : ℤ) : ℝ), (0 : ℝ) < x + u := by
    intro x hx
    have hx1 : ((M : ℤ) : ℝ) ≤ x := hx.1
    have hMnn : (0 : ℝ) ≤ ((M : ℤ) : ℝ) := by positivity
    linarith
  have hδ : 0 < T / (2 * Real.pi * ((m : ℝ) + u)) := by
    have h1 : (0:ℝ) < (m:ℝ) + u := by
      have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      linarith
    positivity
  have hderiv : ∀ x ∈ Set.Icc ((M : ℤ) : ℝ) ((m : ℤ) : ℝ),
      deriv (fun y : ℝ => -(T / (2 * Real.pi)) * Real.log (y + u)) x
        = -(T / (2 * Real.pi)) * (x + u)⁻¹ := by
    intro x hx
    have hne : x + u ≠ 0 := ne_of_gt (hmem x hx)
    have hd : HasDerivAt (fun y : ℝ => Real.log (y + u)) (1 / (x + u)) x := by
      have h0 : HasDerivAt (fun y : ℝ => y + u) 1 x := (hasDerivAt_id x).add_const u
      simpa using h0.log hne
    have hd2 : HasDerivAt (fun y : ℝ => -(T / (2 * Real.pi)) * Real.log (y + u))
        (-(T / (2 * Real.pi)) * (1 / (x + u))) x := hd.const_mul _
    rw [hd2.deriv]
    ring
  have hkl := Commons.Analysis.ExponentialSums.kusmin_landau hMmZ
    (f := fun x : ℝ => -(T / (2 * Real.pi)) * Real.log (x + u)) hδ
    (hf := by
      have h1 : ContDiffOn ℝ 1 (fun x : ℝ => x + u) (Set.Icc ((M : ℤ) : ℝ) ((m : ℤ) : ℝ)) := by
        fun_prop
      have h2 := h1.log (fun x hx => ne_of_gt (hmem x hx))
      have h3 := (contDiffOn_const (c := -(T / (2 * Real.pi)))).mul h2
      simpa using h3)
    (hmono := by
      left
      intro x hx y hy hxy
      rw [hderiv x hx, hderiv y hy]
      have ha : 0 < x + u := hmem x hx
      have hb : x + u ≤ y + u := by linarith
      have h1 : (y + u)⁻¹ ≤ (x + u)⁻¹ := inv_anti₀ ha hb
      exact mul_le_mul_of_nonpos_left h1
        (neg_nonpos.mpr (div_nonneg (by linarith) (by positivity))))
    (hdist := by
      intro x hx
      rw [hderiv x hx]
      have hxM : ((M : ℤ) : ℝ) ≤ x := hx.1
      have hxm : x ≤ ((m : ℤ) : ℝ) := hx.2
      have hxpu : 0 < x + u := hmem x hx
      have hy0 : 0 ≤ T / (2 * Real.pi * (x + u)) :=
        div_nonneg (by linarith) (by positivity)
      have hy1 : T / (2 * Real.pi * (x + u)) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        have h1 : T / 2 ≤ x := le_trans hMT (by simpa using hxM)
        have h2 : T ≤ Real.pi * (x + u) := by
          nlinarith [h1, hu, Real.pi_gt_three, hxpu]
        have h3 : (1:ℝ) / 2 * (2 * Real.pi * (x + u)) = Real.pi * (x + u) := by ring
        linarith
      have hval : -(T / (2 * Real.pi)) * (x + u)⁻¹ = -(T / (2 * Real.pi * (x + u))) := by
        field_simp
      rw [hval, Commons.Analysis.ExponentialSums.intDist_neg, intDist_eq_self hy0 hy1]
      have hxm' : x ≤ (m : ℝ) := by simpa using hxm
      have hxle : 2 * Real.pi * (x + u) ≤ 2 * Real.pi * ((m : ℝ) + u) := by
        have h1 : x + u ≤ (m : ℝ) + u := by linarith
        nlinarith [Real.pi_pos]
      have hfin := mul_le_mul_of_nonneg_left hxle (le_of_lt hT0)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [hfin])
  have hgoal : 1 / (T / (2 * Real.pi * ((m : ℝ) + u))) = 2 * Real.pi * ((m : ℝ) + u) / T := by
    field_simp
  have hconv : (∑ n ∈ Finset.Icc ((M : ℤ) + 1) (m : ℤ),
        Complex.exp (((2 * Real.pi * (-(T / (2 * Real.pi)) * Real.log ((n : ℝ) + u)) : ℝ) : ℂ) *
          Complex.I))
      = ∑ h ∈ Finset.Ioc M m,
        Complex.exp (((2 * Real.pi * (-(T / (2 * Real.pi)) * Real.log ((h : ℝ) + u)) : ℝ) : ℂ) *
          Complex.I) := by
    refine Finset.sum_bij
      (fun (n : ℤ) (_ : n ∈ Finset.Icc ((M : ℤ) + 1) (m : ℤ)) => n.toNat) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_Ioc]
      omega
    · intro n1 hn1 n2 hn2 h
      simp only [Finset.mem_Icc] at hn1 hn2
      omega
    · intro h hh
      refine ⟨(h : ℤ), ?_, ?_⟩
      · simp only [Finset.mem_Icc, Finset.mem_Ioc] at hh ⊢
        omega
      · simp
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      have hn0 : (0:ℤ) ≤ n := by omega
      have h1 : (((n.toNat : ℕ) : ℤ)) = n := by omega
      have hc : ((n : ℝ)) = ((n.toNat : ℕ) : ℝ) := by exact_mod_cast h1.symm
      rw [hc]
  rw [hgoal] at hkl
  rw [hconv] at hkl
  rw [Finset.sum_congr rfl (fun h (_ : h ∈ Finset.Ioc M m) => exp_eq_cpow_shift hu h)] at hkl
  exact hkl

/-! ## 2. The middle-range bound (Kusmin–Landau + Abel summation) -/

/-- The partial sums of `(m+u)^{-(σ+iT)}` over `(M,N]` with `T/2 ≤ M` and
`T^{3/2} ≤ N ≤ 2T^{3/2}` are bounded by an absolute constant. -/
private theorem mid_range_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (u σ T : ℝ) (M N : ℕ),
      0 < u → u ≤ 1 → (1 / 2 : ℝ) ≤ σ → σ ≤ 2 → 3 ≤ T →
      T / 2 ≤ (M : ℝ) → (M : ℝ) ≤ T →
      T ^ (3 / 2 : ℝ) ≤ (N : ℝ) → (N : ℝ) ≤ 2 * T ^ (3 / 2 : ℝ) →
      ‖∑ m ∈ Finset.Ioc M N, (((((m : ℝ) + u : ℝ))) : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))‖ ≤ K := by
  refine ⟨100, by norm_num, ?_⟩
  intro u σ T M N hu hu1 hσ1 hσ2 hT hMT1 hMT2 hNT1 hNT2
  have hT0 : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) ≤ T := by linarith
  by_cases hMN : M < N
  · set L : ℕ := N - M with hL
    have hLN : M + L = N := by omega
    set w : ℕ → ℝ := fun h => (((((M + h : ℕ) : ℝ) + u : ℝ)) ^ (-σ)) with hw
    set b : ℕ → ℂ := fun h => ((w h : ℝ) : ℂ) with hb
    set a : ℕ → ℂ := fun h =>
      (((((M + h : ℕ) : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (T : ℂ))) with ha
    have hxpos : ∀ h : ℕ, (0:ℝ) < ((M + h : ℕ) : ℝ) + u := fun h => by positivity
    have hprod : ∀ h : ℕ, a h * b h =
        (((((M + h : ℕ) : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)) := by
      intro h
      have h1 := hxpos h
      rw [ha, hb, hw]
      dsimp only
      have hcp := Complex.ofReal_cpow (le_of_lt h1) (-σ)
      rw [hcp, Work.BMF.cpow_mul_cpow_ofReal h1]
      congr 1
      push_cast
      ring
    have hE1 : ∀ m : ℕ, M ≤ m → m ≤ N →
        ‖∑ h ∈ Finset.Ioc M m, (((((h : ℝ) + u : ℝ))) : ℂ) ^ (-(Complex.I * (T : ℂ)))‖
          ≤ 2 * Real.pi * ((m : ℝ) + u) / T := by
      intro m hm1 hm2
      exact kl_shift hu hT M m hMT1 hm1
    have hNu : (0:ℝ) < (N:ℝ) + u := by
      have : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
      linarith
    have hMu : (0:ℝ) < (M:ℝ) + u := by
      have : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
      linarith
    have hN3 : (N:ℝ) + u ≤ 3 * T ^ (3/2:ℝ) := by
      have h1 : (1:ℝ) ≤ T ^ (3/2:ℝ) := Real.one_le_rpow hT1 (by norm_num)
      nlinarith
    have hM2 : T / 2 ≤ (M : ℝ) + u := by linarith [hMT1, hu]
    have hpow : ((M:ℝ)+u) ^ (-σ) ≤ (2:ℝ)^(1/2:ℝ) * T ^ (-(1/2:ℝ)) := by
      have ha : ((M:ℝ)+u) ^ (-σ) ≤ ((M:ℝ)+u) ^ (-(1/2:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hb : ((M:ℝ)+u) ^ (-(1/2:ℝ)) ≤ (T/2) ^ (-(1/2:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < T/2) hM2 (by norm_num)
      have hc : (T/2) ^ (-(1/2:ℝ)) = (2:ℝ)^(1/2:ℝ) * T ^ (-(1/2:ℝ)) := by
        rw [Real.div_rpow (le_of_lt hT0) (by norm_num : (0:ℝ) ≤ 2)]
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_neg (le_of_lt hT0),
          div_eq_mul_inv, inv_inv]
        ring
      calc ((M:ℝ)+u) ^ (-σ) ≤ ((M:ℝ)+u) ^ (-(1/2:ℝ)) := ha
        _ ≤ (T/2) ^ (-(1/2:ℝ)) := hb
        _ = (2:ℝ)^(1/2:ℝ) * T ^ (-(1/2:ℝ)) := hc
    have hA : (2 * Real.pi / T) * ((N : ℝ) + u) * (((M:ℝ)+u) ^ (-σ)) ≤ 20 * Real.pi := by
      have h1 : (2 * Real.pi / T) * ((N : ℝ) + u) ≤ (2 * Real.pi / T) * (3 * T ^ (3/2:ℝ)) := by
        apply mul_le_mul_of_nonneg_left hN3
        positivity
      have h2 : (2 * Real.pi / T) * (3 * T ^ (3/2:ℝ)) * (4 * T ^ (-(1/2:ℝ))) = 24 * Real.pi := by
        rw [show T ^ (3/2:ℝ) = T * T ^ (1/2:ℝ) by
          rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hT0, Real.rpow_one]]
        rw [show T ^ (-(1/2:ℝ)) = (T ^ (1/2:ℝ))⁻¹ by rw [Real.rpow_neg (le_of_lt hT0)]]
        field_simp
        ring
      have hp : (0:ℝ) ≤ (2 * Real.pi / T) * ((N : ℝ) + u) :=
        mul_nonneg (div_nonneg (by positivity) (le_of_lt hT0)) (le_of_lt hNu)
      have hp2 : (0:ℝ) ≤ (2:ℝ)^(1/2:ℝ) * T ^ (-(1/2:ℝ)) :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (le_of_lt hT0) _)
      calc (2 * Real.pi / T) * ((N : ℝ) + u) * (((M:ℝ)+u) ^ (-σ))
          ≤ (2 * Real.pi / T) * ((N : ℝ) + u) * ((2:ℝ)^(1/2:ℝ) * T ^ (-(1/2:ℝ))) :=
            mul_le_mul_of_nonneg_left hpow hp
        _ ≤ (2 * Real.pi / T) * (3 * T ^ (3/2:ℝ)) * ((2:ℝ)^(1/2:ℝ) * T ^ (-(1/2:ℝ))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN3
              (div_nonneg (by positivity) (le_of_lt hT0))) hp2
        _ = 6 * Real.pi * (2:ℝ)^(1/2:ℝ) := by
            have hTadd : T ^ (3/2:ℝ) * T ^ (-(1/2:ℝ)) * T⁻¹ = 1 := by
              rw [← Real.rpow_add hT0, show (3/2:ℝ) + (-(1/2)) = 1 by norm_num, Real.rpow_one]
              exact mul_inv_cancel₀ (ne_of_gt hT0)
            calc (2 * Real.pi / T) * (3 * T ^ (3/2:ℝ)) * ((2:ℝ)^(1/2:ℝ) * T ^ (-(1/2:ℝ)))
                = 6 * Real.pi * ((2:ℝ)^(1/2:ℝ) * (T ^ (3/2:ℝ) * T ^ (-(1/2:ℝ)) * T⁻¹)) := by ring
              _ = 6 * Real.pi * (2:ℝ)^(1/2:ℝ) := by rw [hTadd]; ring
        _ ≤ 20 * Real.pi := by
            have h3 : (2:ℝ)^(1/2:ℝ) ≤ 2 := by
              calc (2:ℝ)^(1/2:ℝ) ≤ (2:ℝ)^(1:ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
            nlinarith [Real.pi_pos, h3]
    have hB : (2 * Real.pi / T) * (((N : ℝ) + u) ^ (1 - σ)) ≤ 4 * Real.pi := by
      have hN1 : (1:ℝ) ≤ (N:ℝ) + u := by
        have h3 : (1:ℝ) ≤ T ^ (3/2:ℝ) := Real.one_le_rpow hT1 (by norm_num)
        linarith
      have h1 : ((N : ℝ) + u) ^ (1 - σ) ≤ ((N : ℝ) + u) ^ (1/2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      have h2 : ((N : ℝ) + u) ^ (1/2:ℝ) ≤ (3 * T ^ (3/2:ℝ)) ^ (1/2:ℝ) :=
        Real.rpow_le_rpow (by positivity) hN3 (by norm_num)
      have h3 : (3 * T ^ (3/2:ℝ)) ^ (1/2:ℝ) = (3:ℝ)^(1/2:ℝ) * T ^ (3/4:ℝ) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (le_of_lt hT0) _),
          ← Real.rpow_mul (le_of_lt hT0)]
        norm_num
      have h4 : (3:ℝ)^(1/2:ℝ) ≤ 2 := by
        have h45 : (3:ℝ)^(1/2:ℝ) ≤ (4:ℝ)^(1/2:ℝ) :=
          Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        have hsq : ((4:ℝ)^(1/2:ℝ))^2 = 4 := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sq_sqrt (by norm_num)
        nlinarith [h45, hsq, Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 4) (1/2:ℝ)]
      have h5 : T ^ (3/4:ℝ) ≤ T := by
        have h1 : T ^ (3/4:ℝ) ≤ T ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
        rwa [Real.rpow_one] at h1
      have h8 : ((N : ℝ) + u) ^ (1 - σ) ≤ 2 * T := by
        refine le_trans h1 (le_trans h2 ?_)
        rw [h3]
        have hT34 : (0:ℝ) < T ^ (3/4:ℝ) := Real.rpow_pos_of_pos hT0 _
        have h45 : (3:ℝ)^(1/2:ℝ) * T ^ (3/4:ℝ) ≤ 2 * T ^ (3/4:ℝ) :=
          mul_le_mul_of_nonneg_right h4 (le_of_lt hT34)
        have h56 : 2 * T ^ (3/4:ℝ) ≤ 2 * T := by linarith
        linarith
      have hp : (0:ℝ) ≤ 2 * Real.pi / T := div_nonneg (by positivity) (le_of_lt hT0)
      calc (2 * Real.pi / T) * ((N : ℝ) + u) ^ (1 - σ)
          ≤ (2 * Real.pi / T) * (2 * T) := mul_le_mul_of_nonneg_left h8 hp
        _ = 4 * Real.pi := by field_simp; ring
    have hEsum : ‖∑ h ∈ Finset.Icc 1 L, a h‖ ≤ 2 * Real.pi * ((N : ℝ) + u) / T := by
      have hshift : (∑ h ∈ Finset.Icc 1 L, a h)
          = ∑ m ∈ Finset.Ioc M N, (((((m : ℝ) + u : ℝ))) : ℂ) ^ (-(Complex.I * (T : ℂ))) := by
        rw [← Work.BMF.sum_Ioc_eq_sum_Icc_shift M L
          (fun m : ℕ => (((((m : ℝ) + u : ℝ))) : ℂ) ^ (-(Complex.I * (T : ℂ)))), hLN]
      rw [hshift]
      exact hE1 N hMN.le le_rfl
    have hbL : ‖b L‖ = ((N : ℝ) + u) ^ (-σ) := by
      have hwL : b L = ((((N:ℝ) + u) ^ (-σ) : ℝ) : ℂ) := by
        simp only [hb, hw, hLN]
      rw [hwL, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by linarith [hNu]) _)]
    have hdiff : ∀ h ∈ Finset.range L, ‖b (h + 1) - b h‖ = w h - w (h + 1) := by
      intro h hh
      have h1 : 0 < ((M + h : ℕ) : ℝ) + u := hxpos h
      have h2 : ((M + h : ℕ) : ℝ) + u ≤ ((M + (h + 1) : ℕ) : ℝ) + u := by
        push_cast
        linarith
      have hle : w (h+1) ≤ w h := by
        rw [hw]
        exact Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith)
      rw [hb]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have htail : ‖∑ h ∈ Finset.range L, (∑ h' ∈ Finset.Icc 1 h, a h') * (b (h + 1) - b h)‖
        ≤ (2 * Real.pi / T) * ((N : ℝ) + u) * (((M : ℝ) + u) ^ (-σ)) := by
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ h ∈ Finset.range L,
          ‖(∑ h' ∈ Finset.Icc 1 h, a h') * (b (h + 1) - b h)‖
            ≤ (2 * Real.pi / T) * ((N : ℝ) + u) * (w h - w (h + 1)) := by
        intro h hh
        have hhL : h < L := Finset.mem_range.mp hh
        have hhm : M + h < N := by omega
        have hbnd := hE1 (M + h) (by omega) (le_of_lt hhm)
        have hshift : (∑ h' ∈ Finset.Icc 1 h, a h')
            = ∑ m ∈ Finset.Ioc M (M + h),
                (((((m : ℝ) + u : ℝ))) : ℂ) ^ (-(Complex.I * (T : ℂ))) := by
          rw [← Work.BMF.sum_Ioc_eq_sum_Icc_shift M h
            (fun m : ℕ => (((((m : ℝ) + u : ℝ))) : ℂ) ^ (-(Complex.I * (T : ℂ))))]
        rw [norm_mul, hdiff h hh]
        have hnn : 0 ≤ w h - w (h+1) := by
          rw [← hdiff h hh]
          exact norm_nonneg _
        have hfac : (2 * Real.pi * (((M + h : ℕ) : ℝ) + u) / T)
            ≤ (2 * Real.pi / T) * ((N : ℝ) + u) := by
          have h1 : ((M + h : ℕ) : ℝ) + u ≤ (N : ℝ) + u := by
            have h2 : ((M + h : ℕ) : ℝ) ≤ (N : ℝ) := by
              exact_mod_cast (le_of_lt hhm)
            linarith
          have h2 : 0 ≤ 2 * Real.pi / T := div_nonneg (by positivity) (le_of_lt hT0)
          calc 2 * Real.pi * (((M + h : ℕ) : ℝ) + u) / T
              = (2 * Real.pi / T) * (((M + h : ℕ) : ℝ) + u) := by ring
            _ ≤ (2 * Real.pi / T) * ((N : ℝ) + u) := mul_le_mul_of_nonneg_left h1 h2
        calc ‖∑ h' ∈ Finset.Icc 1 h, a h'‖ * (w h - w (h + 1))
            = ‖∑ m ∈ Finset.Ioc M (M + h),
                (((((m : ℝ) + u : ℝ))) : ℂ) ^ (-(Complex.I * (T : ℂ)))‖ * (w h - w (h+1)) := by
              rw [hshift]
          _ ≤ (2 * Real.pi * (((M + h : ℕ) : ℝ) + u) / T) * (w h - w (h+1)) :=
              mul_le_mul_of_nonneg_right hbnd hnn
          _ ≤ ((2 * Real.pi / T) * ((N : ℝ) + u)) * (w h - w (h+1)) :=
              mul_le_mul_of_nonneg_right hfac hnn
          _ = (2 * Real.pi / T) * ((N : ℝ) + u) * (w h - w (h + 1)) := by ring
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.mul_sum]
      have htel : (∑ h ∈ Finset.range L, (w h - w (h + 1))) = w 0 - w L :=
        Finset.sum_range_sub' w L
      rw [htel]
      have hle : w 0 - w L ≤ w 0 := by
        have h1 : 0 ≤ w L := Real.rpow_nonneg (by positivity) _
        linarith
      have hw0 : w 0 = (((M : ℝ) + u) ^ (-σ)) := by
        rw [hw]
        norm_num
      rw [hw0]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    have hmain := Work.BMF.abel_identity L a b
    have hfinal : ‖∑ h ∈ Finset.Icc 1 L, a h * b h‖
        ≤ (2 * Real.pi / T) * (((N : ℝ) + u) ^ (1 - σ))
          + (2 * Real.pi / T) * ((N : ℝ) + u) * (((M : ℝ) + u) ^ (-σ)) := by
      rw [hmain]
      refine le_trans (norm_sub_le _ _) (add_le_add ?_ htail)
      rw [norm_mul, hbL]
      have h1 : 0 ≤ ((N : ℝ) + u) ^ (-σ) := Real.rpow_nonneg (by linarith [hNu]) _
      have h3 : ((N : ℝ) + u) * ((N : ℝ) + u) ^ (-σ) = ((N : ℝ) + u) ^ (1 - σ) := by
        calc ((N : ℝ) + u) * ((N : ℝ) + u) ^ (-σ)
            = ((N : ℝ) + u) ^ (1:ℝ) * ((N : ℝ) + u) ^ (-σ) := by rw [Real.rpow_one]
          _ = ((N : ℝ) + u) ^ ((1:ℝ) + (-σ)) := by rw [Real.rpow_add hNu]
          _ = ((N : ℝ) + u) ^ (1 - σ) := by
              rw [show (1:ℝ) + (-σ) = 1 - σ by ring]
      calc ‖∑ h ∈ Finset.Icc 1 L, a h‖ * ((N : ℝ) + u) ^ (-σ)
          ≤ (2 * Real.pi * ((N : ℝ) + u) / T) * ((N : ℝ) + u) ^ (-σ) :=
            mul_le_mul_of_nonneg_right hEsum h1
        _ = (2 * Real.pi / T) * ((N : ℝ) + u) ^ (1 - σ) := by
            rw [← h3]; ring
    have hsumid : (∑ h ∈ Finset.Icc 1 L, a h * b h)
        = ∑ m ∈ Finset.Ioc M N, (((((m : ℝ) + u : ℝ))) : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)) := by
      rw [Finset.sum_congr rfl (fun h _ => hprod h)]
      rw [← Work.BMF.sum_Ioc_eq_sum_Icc_shift M L
        (fun m : ℕ => (((((m : ℝ) + u : ℝ))) : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))), hLN]
    rw [hsumid] at hfinal
    nlinarith [hfinal, hA, hB, Real.pi_lt_four]
  · have hempty : Finset.Ioc M N = ∅ := Finset.Ioc_eq_empty_iff.mpr (by omega)
    rw [hempty, Finset.sum_empty, norm_zero]
    norm_num

/-- shifting a sum over `range X` by one. -/
private lemma sum_range_shift (f : ℕ → ℂ) (X : ℕ) :
    ∑ k ∈ Finset.range X, f (k+1) = ∑ n ∈ Finset.Icc 1 X, f n := by
  refine Finset.sum_bij (fun k (_ : k ∈ Finset.range X) => k+1) ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
  · intro k1 _ k2 _ h; omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    exact ⟨n-1, by simp only [Finset.mem_range]; omega, by omega⟩
  · intro k _; rfl

/-- The two Euler–Maclaurin correction terms at a cut-off `X` with `T^{3/2} ≤ X ≤ 2T^{3/2}`
are bounded by an absolute constant. -/
private theorem tail_arith_bounds :
    ∃ K : ℝ, 0 < K ∧ ∀ (σ T : ℝ) (X : ℕ) (a : ℝ),
      (2 / 3 : ℝ) ≤ σ → σ ≤ 2 → 3 ≤ T → T ^ (3 / 2 : ℝ) ≤ (X : ℝ) →
      (X : ℝ) ≤ 2 * T ^ (3 / 2 : ℝ) → 0 < a → a ≤ 1 →
      (X : ℝ) ^ (1 - σ) / T ≤ K ∧
      (‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ) * (X : ℝ) ^ (-σ) ≤ K ∧
      (‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ) * ((X : ℝ) + a) ^ (-σ) ≤ K := by
  refine ⟨10, by norm_num, ?_⟩
  intro σ T X a hσ1 hσ2 hT hX1 hX2 ha ha1
  have hT0 : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) ≤ T := by linarith
  have hX0 : (0:ℝ) < (X:ℝ) := by
    have h : (1:ℝ) ≤ T ^ (3/2:ℝ) := Real.one_le_rpow hT1 (by norm_num)
    linarith
  have hX1' : (1:ℝ) ≤ (X:ℝ) := by
    have h : (1:ℝ) ≤ T ^ (3/2:ℝ) := Real.one_le_rpow hT1 (by norm_num)
    linarith
  have hXa : (0:ℝ) < (X:ℝ) + a := by linarith
  -- the exponent `-σ` bound
  have hpow : (X:ℝ) ^ (-σ) ≤ T ^ (-(1:ℝ)) := by
    have h1 : (X:ℝ) ^ (-σ) ≤ (T ^ (3/2:ℝ)) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 _) hX1 (by linarith)
    have h2 : (T ^ (3/2:ℝ)) ^ (-σ) = T ^ (-(3/2:ℝ) * σ) := by
      rw [← Real.rpow_mul (le_of_lt hT0)]
      ring_nf
    have h3 : T ^ (-(3/2:ℝ) * σ) ≤ T ^ (-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hT1 (by nlinarith)
    linarith [h1, h2.le, h2.ge, h3]
  -- the complex norm bound
  have hnorm : ‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ 2 + T := by
    have h1 : ‖(T : ℂ) * Complex.I‖ = T := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt hT0)]
    calc ‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ ‖(σ : ℂ)‖ + ‖(T : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |σ| + T := by rw [h1, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 + T := by
          have h2 : |σ| ≤ 2 := by
            rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ σ)]
            exact hσ2
          linarith
  have hnorm2 : ‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ 2 * T := by
    have : 2 + T ≤ 2 * T := by linarith
    linarith
  have hσpos : 0 < σ := by linarith
  -- (1)
  have h1 : (X:ℝ) ^ (1 - σ) / T ≤ 10 := by
    have ha1' : (X:ℝ) ^ (1 - σ) ≤ (X:ℝ) ^ (1/2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1' (by linarith)
    have hb : (X:ℝ) ^ (1/2:ℝ) ≤ (2 * T ^ (3/2:ℝ)) ^ (1/2:ℝ) :=
      Real.rpow_le_rpow (le_of_lt hX0) hX2 (by norm_num)
    have hc : (2 * T ^ (3/2:ℝ)) ^ (1/2:ℝ) = (2:ℝ)^(1/2:ℝ) * T ^ (3/4:ℝ) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (le_of_lt hT0) _),
        ← Real.rpow_mul (le_of_lt hT0)]
      norm_num
    have hd : (2:ℝ)^(1/2:ℝ) ≤ 2 := by
      calc (2:ℝ)^(1/2:ℝ) ≤ (2:ℝ)^(1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have he : (X:ℝ) ^ (1 - σ) ≤ 2 * T ^ (3/4:ℝ) := by
      refine le_trans ha1' (le_trans hb ?_)
      rw [hc]
      have hT34 : (0:ℝ) ≤ T ^ (3/4:ℝ) := Real.rpow_nonneg (le_of_lt hT0) _
      nlinarith [hd, hT34]
    have hle : T ^ (3/4:ℝ) ≤ T := by
      have h := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num : (3/4:ℝ) ≤ 1)
      rwa [Real.rpow_one] at h
    rw [div_le_iff₀ hT0]
    nlinarith [he, hle, hT0]
  -- (2)
  have h2 : (‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ) * (X:ℝ) ^ (-σ) ≤ 10 := by
    have h1 : (‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ) * (X:ℝ) ^ (-σ)
        ≤ (2 * T / σ) * T ^ (-(1:ℝ)) := by
      have h3 : 0 ≤ T ^ (-(1:ℝ)) := Real.rpow_nonneg (le_of_lt hT0) _
      have h4 : (0:ℝ) < 1 / σ := by positivity
      have h5 : ‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ ≤ 2 * T / σ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have : (0:ℝ) ≤ (σ:ℝ)⁻¹ := by positivity
        nlinarith [hnorm2, this]
      calc (‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ) * (X:ℝ) ^ (-σ)
          ≤ (2 * T / σ) * T ^ (-(1:ℝ)) := by
            apply mul_le_mul h5 hpow (Real.rpow_nonneg (le_of_lt hX0) _) (by positivity)
        _ = (2 * T / σ) * T ^ (-(1:ℝ)) := rfl
    have h2 : (2 * T / σ) * T ^ (-(1:ℝ)) = 2 / σ := by
      rw [show T ^ (-(1:ℝ)) = T⁻¹ by rw [Real.rpow_neg (le_of_lt hT0), Real.rpow_one]]
      field_simp
    refine le_trans h1 ?_
    rw [h2, div_le_iff₀ hσpos]
    nlinarith
  -- (3)
  have h3 : (‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ) * ((X:ℝ) + a) ^ (-σ) ≤ 10 := by
    have hle : ((X:ℝ) + a) ^ (-σ) ≤ (X:ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hX0 (by linarith) (by linarith)
    have h4 : 0 ≤ (X:ℝ) ^ (-σ) := Real.rpow_nonneg (le_of_lt hX0) _
    have h5 : 0 ≤ ‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ := by positivity
    calc (‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ) * ((X:ℝ) + a) ^ (-σ)
        ≤ (‖((σ : ℂ) + (T : ℂ) * Complex.I)‖ / σ) * (X:ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_left hle h5
      _ ≤ 10 := h2
  exact ⟨h1, h2, h3⟩

/-- The Hurwitz zeta function (real shift in `(0,1]`) commutes with complex conjugation. -/
private lemma hurwitzZeta_conj {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (starRingEnd ℂ) (HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s) =
      HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((starRingEnd ℂ) s) := by
  have hconj_re : 0 < ((starRingEnd ℂ) s).re := by simpa using hs
  have hconj_ne : ((starRingEnd ℂ) s) ≠ 1 := by
    intro h
    apply hs1
    have h2 : (starRingEnd ℂ) ((starRingEnd ℂ) s) = (starRingEnd ℂ) (1:ℂ) := by rw [h]
    simpa using h2
  have hid := Work.BMF.hurwitzZeta_sub_riemannZeta_eq_tsum (a := a) ha ha1 (s := s) hs hs1
  have hid' : HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s
      = riemannZeta s + ∑' m, Work.BMF.shiftTerm a m s := by
    have h := hid
    rw [sub_eq_iff_eq_add] at h
    simpa only [add_comm] using h
  have hid2' : HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((starRingEnd ℂ) s)
      = riemannZeta ((starRingEnd ℂ) s)
        + ∑' m, Work.BMF.shiftTerm a m ((starRingEnd ℂ) s) := by
    have h := Work.BMF.hurwitzZeta_sub_riemannZeta_eq_tsum (a := a) ha ha1
      (s := (starRingEnd ℂ) s) hconj_re hconj_ne
    rw [sub_eq_iff_eq_add] at h
    simpa only [add_comm] using h
  have hterm : ∀ m : ℕ, (starRingEnd ℂ) (Work.BMF.shiftTerm a m s)
      = Work.BMF.shiftTerm a m ((starRingEnd ℂ) s) := by
    intro m
    have hx : (0:ℝ) ≤ ((m:ℝ)+a) := by positivity
    have h1 : (starRingEnd ℂ) (((((m:ℝ)+a:ℝ)):ℂ)^(-s))
        = ((((m:ℝ)+a:ℝ)):ℂ)^(-((starRingEnd ℂ) s)) := by
      rw [Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg hx (-s), map_neg]
    have h2 : (starRingEnd ℂ) (((((m+1:ℕ):ℝ)):ℂ)^(-s))
        = ((((m+1:ℕ):ℝ)):ℂ)^(-((starRingEnd ℂ) s)) := by
      rw [Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg (by positivity) (-s), map_neg]
    simp only [Work.BMF.shiftTerm, map_sub, h1, h2]
  have hsumm : Summable (fun m : ℕ => Work.BMF.shiftTerm a m s) := by
    have h := Work.BMF.summable_norm_shiftTerm ha ha1 (s := s) hs 0
    simpa using h.of_norm
  have hsum : (starRingEnd ℂ) (∑' m, Work.BMF.shiftTerm a m s)
      = ∑' m, Work.BMF.shiftTerm a m ((starRingEnd ℂ) s) := by
    rw [Complex.conj_tsum]
    exact tsum_congr (fun m => hterm m)
  rw [hid', map_add, ← riemannZeta_conj, hsum, hid2']

/-- The finite sum of `shiftTerm` telescopes. -/
private lemma sum_shiftTerm_range (a : ℝ) (s : ℂ) (X : ℕ) :
    ∑ m ∈ Finset.range X, Work.BMF.shiftTerm a m s =
      (∑ m ∈ Finset.range X, ((((m:ℝ)+a:ℝ)):ℂ)^(-s))
        - ∑ n ∈ Finset.range X, ((((n+1:ℕ):ℝ)):ℂ)^(-s) := by
  simp only [Work.BMF.shiftTerm]
  rw [Finset.sum_sub_distrib]

theorem vk_L_growth
    (hsh : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ (u : ℝ) (M : ℕ) (σ T : ℝ), 0 < u → u ≤ 1 →
        3 ≤ T → 0 < σ → σ ≤ 2 →
        1 - c * Real.log (T + 3) ^ (-(5 / 6 : ℝ)) ≤ σ → (M : ℝ) ≤ T →
        ‖∑ m ∈ Finset.Icc 0 M,
            ((((m : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))‖ ≤
          A * (u ^ (-σ) + Real.log (T + 3) ^ (5 / 6 : ℝ)))
    (hz : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ σ t : ℝ, 3 ≤ |t| →
      1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * Real.log (|t| + 3) ^ (6 / 7 : ℝ)) :
    ∃ Alg clg : ℝ, 0 < Alg ∧ 0 < clg ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (σ t : ℝ), 3 ≤ |t| →
        1 - clg * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
        ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          Alg * (N : ℝ) * Real.log (|t| + 3) ^ (6 / 7 : ℝ) := by
  obtain ⟨Ah, ch, hAh, hch, hshb⟩ := hsh
  obtain ⟨Az, cz, hAz, hcz, hzb⟩ := hz
  obtain ⟨K1, hK1pos, hK1⟩ := mid_range_bound
  obtain ⟨K2, hK2pos, hK2⟩ := tail_arith_bounds
  set c : ℝ := min ch (min cz (1/4)) with hcdef
  set A : ℝ := 2 * Az + Ah + K1 + 3 * K2 + 1 with hAdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcch : c ≤ ch := by rw [hcdef]; exact min_le_left _ _
  have hccz : c ≤ cz := by rw [hcdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hc4 : c ≤ 1/4 := by rw [hcdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hc12 : c ≤ 1/2 := by linarith
  have hApos : 0 < A := by rw [hAdef]; linarith
  have hAtop : (1:ℝ) ≤ A := by rw [hAdef]; linarith
  have hAzA : Az ≤ A := by rw [hAdef]; linarith
  have hAhA : Ah ≤ A := by rw [hAdef]; linarith
  -- The positive-height Hurwitz bound
  have hpos : ∀ (a T σ : ℝ), 0 < a → a ≤ 1 → 3 ≤ T →
      1 - c * Real.log (T + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        A * (a ^ (-σ) + Real.log (T + 3) ^ (6 / 7 : ℝ)) := by
    intro a T σ ha ha1 hT hσ hσ2
    have hT0 : (0:ℝ) < T := by linarith
    have hL1 : (1:ℝ) ≤ Real.log (T + 3) := by
      have h1 : (1:ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        exact le_of_lt Real.exp_one_lt_three
      have h2 : Real.log 3 ≤ Real.log (T + 3) := Real.log_le_log (by norm_num) (by linarith)
      linarith
    have hLnn : (0:ℝ) ≤ Real.log (T + 3) := le_trans zero_le_one hL1
    have hσ23 : (2/3:ℝ) ≤ σ := by
      have h4 : Real.log (T+3) ^ (-(6/7:ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
      have h5 : c * Real.log (T+3) ^ (-(6/7:ℝ)) ≤ 1/4 := by
        nlinarith [h4, hc4, hcpos]
      linarith [hσ]
    have hσhalf : (1/2:ℝ) ≤ σ := by linarith
    have hσpos : 0 < σ := by linarith
    have hσch : 1 - ch * Real.log (T+3) ^ (-(5/6:ℝ)) ≤ σ := by
      have h5 : Real.log (T+3) ^ (-(6/7:ℝ)) ≤ Real.log (T+3) ^ (-(5/6:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have h6 : 0 ≤ Real.log (T+3) ^ (-(6/7:ℝ)) := Real.rpow_nonneg hLnn _
      have h7 : c * Real.log (T+3) ^ (-(6/7:ℝ)) ≤ ch * Real.log (T+3) ^ (-(5/6:ℝ)) := by
        nlinarith [h5, h6, hcch]
      linarith [hσ]
    have hσcz : 1 - cz * Real.log (T+3) ^ (-(6/7:ℝ)) ≤ σ := by
      have h6 : 0 ≤ Real.log (T+3) ^ (-(6/7:ℝ)) := Real.rpow_nonneg hLnn _
      nlinarith [hσ, h6, hccz]
    set M : ℕ := ⌊T⌋₊ with hMdef
    set N1 : ℕ := ⌈T ^ (3/2:ℝ)⌉₊ with hN1def
    have hMT : (M:ℝ) ≤ T := by rw [hMdef]; exact Nat.floor_le (le_of_lt hT0)
    have hMT2 : T/2 ≤ (M:ℝ) := by
      have h1 : T < (M:ℝ) + 1 := by
        rw [hMdef]; exact Nat.lt_floor_add_one T
      linarith [hT]
    have hN1a : T ^ (3/2:ℝ) ≤ (N1:ℝ) := by
      rw [hN1def]; exact Nat.le_ceil _
    have hN1b : (N1:ℝ) ≤ 2 * T ^ (3/2:ℝ) := by
      have h1 : (N1:ℝ) < T ^ (3/2:ℝ) + 1 := by
        rw [hN1def]; exact Nat.ceil_lt_add_one (le_of_lt (Real.rpow_pos_of_pos hT0 _))
      have h2 : (1:ℝ) ≤ T^(3/2:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      have h3 : T ^ (3/2:ℝ) + 1 ≤ 2 * T ^ (3/2:ℝ) := by linarith [h2]
      linarith [h1, h3]
    have hT32 : T ≤ T ^ (3/2:ℝ) := by
      calc T = T^(1:ℝ) := (Real.rpow_one T).symm
        _ ≤ T^(3/2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hMN1 : M ≤ N1 := by
      have h1 : (M:ℝ) ≤ (N1:ℝ) := by linarith [hMT, hN1a, hT32]
      exact_mod_cast h1
    set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hsdef
    have hsre : s.re = σ := by simp [hsdef]
    have hspos : 0 < s.re := by rw [hsre]; exact hσpos
    have hsT : s.im = T := by simp [hsdef]
    have hsne : s ≠ 1 := by
      intro h
      have h2 : s.im = (1:ℂ).im := by rw [h]
      rw [hsT] at h2
      simp at h2
      linarith
    -- (hsh) for the range `[0,M]`
    have hb1 : ‖∑ m ∈ Finset.Icc 0 M, (((((m:ℝ)+a:ℝ))):ℂ)^(-s)‖ ≤ Ah*(a^(-σ) + Real.log (T+3)^(5/6:ℝ)) := by
      have h := hshb a M σ T ha ha1 hT hσpos hσ2 hσch hMT
      simpa only [hsdef] using h
    -- (Kusmin–Landau + Abel) for `(M,N1]`
    have hb2 : ‖∑ m ∈ Finset.Ioc M N1, (((((m:ℝ)+a:ℝ))):ℂ)^(-s)‖ ≤ K1 := by
      have h := hK1 a σ T M N1 ha ha1 hσhalf hσ2 hT hMT2 hMT hN1a hN1b
      simpa only [hsdef] using h
    -- the Euler–Maclaurin bound for the zeta partial sum
    have hb3 : ‖∑ n ∈ Finset.Icc 1 (N1+1), (((((n:ℕ):ℝ))):ℂ)^(-s)‖ ≤ Az * Real.log (T+3)^(6/7:ℝ) + 2*K2 := by
      have hEM := Work.BMF.zeta_sub_Icc_sum_le (σ := σ) (t := T) hσpos (ne_of_gt hT0) (N1+1) (by omega)
      rw [abs_of_pos hT0] at hEM
      have hEM' : ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 (N1+1), (((((n:ℕ):ℝ))):ℂ)^(-s)‖
          ≤ ((N1+1:ℕ):ℝ)^(1-σ)/T + (‖s‖/σ) * ((N1+1:ℕ):ℝ)^(-σ) := by
        have hsum : (∑ n ∈ Finset.Icc 1 (N1+1), (((((n:ℕ):ℝ))):ℂ)^(-s))
            = ∑ n ∈ Finset.Icc 1 (N1+1), (((n:ℕ)):ℂ)^(-s) := by
          apply Finset.sum_congr rfl
          intro n _
          push_cast
          try ring
        rw [hsum]
        simpa only [hsdef] using hEM
      have hX1 : T ^ (3/2:ℝ) ≤ ((N1+1:ℕ):ℝ) := by
        have h1 : (N1:ℝ) ≤ ((N1+1:ℕ):ℝ) := by push_cast; linarith
        linarith [hN1a, h1]
      have hX2 : ((N1+1:ℕ):ℝ) ≤ 2 * T ^ (3/2:ℝ) := by
        have h1 : ((N1+1:ℕ):ℝ) ≤ (N1:ℝ) + 1 := by push_cast; linarith
        have h0 : (N1:ℝ) < T ^ (3/2:ℝ) + 1 := by
          rw [hN1def]; exact Nat.ceil_lt_add_one (le_of_lt (Real.rpow_pos_of_pos hT0 _))
        have h3 : (2:ℝ) ≤ T^(3/2:ℝ) := le_trans (le_trans (by norm_num : (2:ℝ) ≤ 3) hT) hT32
        linarith [h1, h0, h3]
      have hK2a : (((N1+1:ℕ):ℝ))^(1-σ)/T ≤ K2 :=
        (hK2 σ T (N1+1) a hσ23 hσ2 hT hX1 hX2 ha ha1).1
      have hK2b : (‖s‖/σ) * (((N1+1:ℕ):ℝ))^(-σ) ≤ K2 := by
        have h := (hK2 σ T (N1+1) a hσ23 hσ2 hT hX1 hX2 ha ha1).2.1
        simpa only [hsdef] using h
      have hz1 : ‖riemannZeta s‖ ≤ Az * Real.log (T+3)^(6/7:ℝ) := by
        have hσcz' : 1 - cz * Real.log (|T|+3)^(-(6/7:ℝ)) ≤ σ := by
          rw [abs_of_pos hT0]; exact hσcz
        have h := hzb σ T (by rw [abs_of_pos hT0]; exact hT) hσcz' hσ2
        rw [abs_of_pos hT0] at h
        simpa only [hsdef] using h
      have h3 : ‖∑ n ∈ Finset.Icc 1 (N1+1), (((((n:ℕ):ℝ))):ℂ)^(-s)‖
          ≤ ‖riemannZeta s‖ + ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 (N1+1), (((((n:ℕ):ℝ))):ℂ)^(-s)‖ := by
        have h := norm_sub_le (riemannZeta s) (riemannZeta s - ∑ n ∈ Finset.Icc 1 (N1+1), (((((n:ℕ):ℝ))):ℂ)^(-s))
        rw [sub_sub_cancel] at h
        exact h
      linarith [h3, hz1, hEM', hK2a, hK2b]
    -- the shift-difference tail
    have hb4 : ‖∑' m, Work.BMF.shiftTerm a (N1+1+m) s‖ ≤ K2 := by
      have h := Work.BMF.norm_tsum_shiftTerm_tail_le (a := a) ha ha1 (s := s) hspos (N1+1)
      have hX1 : T ^ (3/2:ℝ) ≤ ((N1+1:ℕ):ℝ) := by
        have h1 : (N1:ℝ) ≤ ((N1+1:ℕ):ℝ) := by push_cast; linarith
        linarith [hN1a, h1]
      have hX2 : ((N1+1:ℕ):ℝ) ≤ 2 * T ^ (3/2:ℝ) := by
        have h1 : ((N1+1:ℕ):ℝ) ≤ (N1:ℝ) + 1 := by push_cast; linarith
        have h0 : (N1:ℝ) < T ^ (3/2:ℝ) + 1 := by
          rw [hN1def]; exact Nat.ceil_lt_add_one (le_of_lt (Real.rpow_pos_of_pos hT0 _))
        have h3 : (2:ℝ) ≤ T^(3/2:ℝ) := le_trans (le_trans (by norm_num : (2:ℝ) ≤ 3) hT) hT32
        linarith [h1, h0, h3]
      have h2 : (‖s‖/σ) * (((N1+1:ℕ):ℝ) + a)^(-σ) ≤ K2 := by
        have hh := (hK2 σ T (N1+1) a hσ23 hσ2 hT hX1 hX2 ha ha1).2.2
        simpa only [hsdef] using hh
      have h4 : ‖∑' m, Work.BMF.shiftTerm a (N1+1+m) s‖
          ≤ (‖s‖/σ) * (((N1+1:ℕ):ℝ) + a)^(-σ) := by
        simpa only [hsre] using h
      linarith [h4, h2]
    -- the identity and the split
    have hid := Work.BMF.hurwitzZeta_sub_riemannZeta_eq_tsum (a := a) ha ha1 (s := s) hspos hsne
    have hid' : HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s
        = riemannZeta s + ∑' m, Work.BMF.shiftTerm a m s := by
      have h := hid
      rw [sub_eq_iff_eq_add] at h
      simpa only [add_comm] using h
    have hsplit := Work.BMF.shiftTerm_split (a := a) ha ha1 (s := s) hspos (N1+1)
    have hsumid := sum_shiftTerm_range a s (N1+1)
    have hrange : Finset.range (N1+1) = Finset.Icc 0 N1 := by
      ext k; simp only [Finset.mem_range, Finset.mem_Icc]; omega
    have hIcc : Finset.Icc 0 N1 = Finset.Icc 0 M ∪ Finset.Ioc M N1 := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
    have hdisj : Disjoint (Finset.Icc 0 M) (Finset.Ioc M N1) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [Finset.mem_Icc] at hk1
      simp only [Finset.mem_Ioc] at hk2
      omega
    have hsplit2 : (∑ m ∈ Finset.range (N1+1), (((((m:ℝ)+a:ℝ))):ℂ)^(-s))
        = (∑ m ∈ Finset.Icc 0 M, (((((m:ℝ)+a:ℝ))):ℂ)^(-s))
          + ∑ m ∈ Finset.Ioc M N1, (((((m:ℝ)+a:ℝ))):ℂ)^(-s) := by
      rw [hrange, hIcc, Finset.sum_union hdisj]
    have hsplit3 : (∑ n ∈ Finset.range (N1+1), (((((n+1:ℕ):ℝ))):ℂ)^(-s))
        = ∑ n ∈ Finset.Icc 1 (N1+1), (((((n:ℕ):ℝ))):ℂ)^(-s) :=
      sum_range_shift (fun n : ℕ => (((((n:ℕ):ℝ))):ℂ)^(-s)) (N1+1)
    -- assemble
    have hstep1 : ‖∑' m, Work.BMF.shiftTerm a m s‖
        ≤ (Ah*(a^(-σ) + Real.log (T+3)^(5/6:ℝ)) + K1)
          + (Az * Real.log (T+3)^(6/7:ℝ) + 2*K2) + K2 := by
      rw [hsplit]
      have h1 : ‖(∑ m ∈ Finset.range (N1+1), Work.BMF.shiftTerm a m s)
          + ∑' m, Work.BMF.shiftTerm a (N1+1+m) s‖
          ≤ ‖∑ m ∈ Finset.range (N1+1), Work.BMF.shiftTerm a m s‖
            + ‖∑' m, Work.BMF.shiftTerm a (N1+1+m) s‖ := norm_add_le _ _
      have h2 : ‖∑ m ∈ Finset.range (N1+1), Work.BMF.shiftTerm a m s‖
          ≤ (Ah*(a^(-σ) + Real.log (T+3)^(5/6:ℝ)) + K1)
            + (Az * Real.log (T+3)^(6/7:ℝ) + 2*K2) := by
        rw [hsumid]
        have h3 : ‖(∑ m ∈ Finset.range (N1+1), (((((m:ℝ)+a:ℝ))):ℂ)^(-s))
            - ∑ n ∈ Finset.range (N1+1), (((((n+1:ℕ):ℝ))):ℂ)^(-s)‖
            ≤ ‖∑ m ∈ Finset.range (N1+1), (((((m:ℝ)+a:ℝ))):ℂ)^(-s)‖
              + ‖∑ n ∈ Finset.range (N1+1), (((((n+1:ℕ):ℝ))):ℂ)^(-s)‖ := norm_sub_le _ _
        have h4 : ‖∑ m ∈ Finset.range (N1+1), (((((m:ℝ)+a:ℝ))):ℂ)^(-s)‖
            ≤ Ah*(a^(-σ) + Real.log (T+3)^(5/6:ℝ)) + K1 := by
          rw [hsplit2]
          exact le_trans (norm_add_le _ _) (add_le_add hb1 hb2)
        have h5 : ‖∑ n ∈ Finset.range (N1+1), (((((n+1:ℕ):ℝ))):ℂ)^(-s)‖
            ≤ Az * Real.log (T+3)^(6/7:ℝ) + 2*K2 := by
          rw [hsplit3]
          exact hb3
        linarith [h3, h4, h5]
      linarith [h1, h2, hb4]
    -- final
    have hz1 : ‖riemannZeta s‖ ≤ Az * Real.log (T+3)^(6/7:ℝ) := by
      have hσcz' : 1 - cz * Real.log (|T|+3)^(-(6/7:ℝ)) ≤ σ := by
        rw [abs_of_pos hT0]; exact hσcz
      have h := hzb σ T (by rw [abs_of_pos hT0]; exact hT) hσcz' hσ2
      rw [abs_of_pos hT0] at h
      simpa only [hsdef] using h
    have hgoal1 : ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s‖
        ≤ 2*(Az * Real.log (T+3)^(6/7:ℝ)) + Ah*(a^(-σ) + Real.log (T+3)^(5/6:ℝ)) + K1 + 3*K2 := by
      rw [hid']
      have h1 : ‖riemannZeta s + ∑' m, Work.BMF.shiftTerm a m s‖
          ≤ ‖riemannZeta s‖ + ‖∑' m, Work.BMF.shiftTerm a m s‖ := norm_add_le _ _
      linarith [h1, hz1, hstep1]
    refine le_trans hgoal1 ?_
    set L6 : ℝ := Real.log (T+3)^(6/7:ℝ) with hL6def
    set L5 : ℝ := Real.log (T+3)^(5/6:ℝ) with hL5def
    have hL6pos : 0 < L6 := by rw [hL6def]; exact Real.rpow_pos_of_pos (by linarith) _
    have hL61 : (1:ℝ) ≤ L6 := by rw [hL6def]; exact Real.one_le_rpow hL1 (by norm_num)
    have hL65 : L5 ≤ L6 := by
      rw [hL5def, hL6def]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hL5nn : (0:ℝ) ≤ L5 := by rw [hL5def]; exact Real.rpow_nonneg hLnn _
    have hbound : 2*(Az*L6) + Ah*L5 + K1 + 3*K2 ≤ A * L6 := by
      have h1 : Ah * L5 ≤ Ah * L6 := mul_le_mul_of_nonneg_left hL65 (le_of_lt hAh)
      have h2 : K1 ≤ K1 * L6 := by nlinarith [hL61, hK1pos]
      have h3 : 3*K2 ≤ (3*K2) * L6 := by nlinarith [hL61, hK2pos]
      have h4 : (2*Az + Ah + K1 + 3*K2) * L6 ≤ A * L6 := by
        have h5 : 2*Az + Ah + K1 + 3*K2 ≤ A := by rw [hAdef]; linarith
        exact mul_le_mul_of_nonneg_right h5 hL6pos.le
      have h6 : 2*(Az*L6) + Ah*L5 + K1 + 3*K2 ≤ (2*Az + Ah + K1 + 3*K2) * L6 := by
        have h7 : (2*Az + Ah + K1 + 3*K2) * L6 = 2*Az*L6 + Ah*L6 + K1*L6 + 3*K2*L6 := by ring
        rw [h7]; linarith [h1, h2, h3]
      linarith [h6, h4]
    have hbound2 : Ah * a^(-σ) ≤ A * a^(-σ) :=
      mul_le_mul_of_nonneg_right hAhA (Real.rpow_nonneg (le_of_lt ha) _)
    rw [show 2*(Az*L6) + Ah*(a^(-σ) + L5) + K1 + 3*K2
          = (2*(Az*L6) + Ah*L5 + K1 + 3*K2) + Ah * a^(-σ) by ring,
        show A * (a^(-σ) + L6) = A * L6 + A * a^(-σ) by ring]
    linarith [hbound, hbound2]
  -- The full Hurwitz bound (both signs of t)
  have hHur : ∀ (a σ t : ℝ), 0 ≤ a → a ≤ 1 → 3 ≤ |t| →
      1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by
    intro a σ t ha0 ha1 ht hσ hσ2
    have hL3 : (1:ℝ) ≤ Real.log (|t| + 3) := by
      have h1 : (1:ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        exact le_of_lt Real.exp_one_lt_three
      have h2 : Real.log 3 ≤ Real.log (|t| + 3) :=
        Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
      linarith
    have hL3nn : (0:ℝ) ≤ Real.log (|t| + 3) := le_trans zero_le_one hL3
    rcases eq_or_lt_of_le ha0 with ha0' | hapos
    · -- a = 0
      subst ha0'
      rw [show ((0:ℝ) : UnitAddCircle) = 0 from rfl, HurwitzZeta.hurwitzZeta_zero]
      have hσpos : 0 < σ := by
        have h4 : Real.log (|t|+3) ^ (-(6/7:ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hL3 (by norm_num)
        have h6 : 0 ≤ Real.log (|t|+3) ^ (-(6/7:ℝ)) := Real.rpow_nonneg hL3nn _
        have h5 : c * Real.log (|t|+3) ^ (-(6/7:ℝ)) ≤ 1/4 := by nlinarith [h4, h6, hc4, hcpos]
        linarith [hσ]
      have h0r : (0:ℝ) ^ (-σ) = 0 := by
        rw [Real.rpow_neg (le_refl 0), Real.zero_rpow (ne_of_gt hσpos), inv_zero]
      have hzσ : 1 - cz * Real.log (|t|+3)^(-(6/7:ℝ)) ≤ σ := by
        have h6 : 0 ≤ Real.log (|t|+3) ^ (-(6/7:ℝ)) := Real.rpow_nonneg hL3nn _
        nlinarith [hσ, h6, hccz]
      have hz1 := hzb σ t ht hzσ hσ2
      rw [h0r, zero_add]
      refine le_trans hz1 ?_
      exact mul_le_mul_of_nonneg_right hAzA (Real.rpow_nonneg (Real.log_nonneg (by linarith [abs_nonneg t])) _)
    · -- a > 0
      by_cases ht0 : 0 ≤ t
      · have hT : 3 ≤ t := by rwa [abs_of_nonneg ht0] at ht
        have hσ' : 1 - c * Real.log (t + 3) ^ (-(6/7:ℝ)) ≤ σ := by rwa [abs_of_nonneg ht0] at hσ
        have hb := hpos a t σ hapos ha1 hT hσ' hσ2
        rw [abs_of_nonneg ht0]
        exact hb
      · push_neg at ht0
        have ht3 : 3 ≤ -t := by rw [abs_of_neg ht0] at ht; linarith
        have hσ' : 1 - c * Real.log ((-t) + 3) ^ (-(6/7:ℝ)) ≤ σ := by rwa [abs_of_neg ht0] at hσ
        have hbound := hpos a (-t) σ hapos ha1 ht3 hσ' hσ2
        have hgoalT : (-t) + 3 = |t| + 3 := by rw [abs_of_neg ht0]
        rw [hgoalT] at hbound
        have hs1 : ((σ:ℂ) + ((-t:ℝ):ℂ) * Complex.I).re = σ := by simp
        have hσpos2 : 0 < σ := by
          have h4 : Real.log ((-t)+3) ^ (-(6/7:ℝ)) ≤ 1 := by
            rw [hgoalT]
            exact Real.rpow_le_one_of_one_le_of_nonpos hL3 (by norm_num)
          have h6 : 0 ≤ Real.log ((-t)+3) ^ (-(6/7:ℝ)) := by
            rw [hgoalT]; exact Real.rpow_nonneg hL3nn _
          have h5 : c * Real.log ((-t)+3)^(-(6/7:ℝ)) ≤ 1/4 := by nlinarith [h4, h6, hc4, hcpos]
          linarith [hσ']
        have hspos : 0 < ((σ:ℂ) + ((-t:ℝ):ℂ) * Complex.I).re := by rw [hs1]; exact hσpos2
        have hsne : ((σ:ℂ) + ((-t:ℝ):ℂ) * Complex.I) ≠ 1 := by
          intro h
          have h2 : ((σ:ℂ) + ((-t:ℝ):ℂ) * Complex.I).im = (1:ℂ).im := by rw [h]
          simp at h2
          linarith
        have hc := hurwitzZeta_conj hapos ha1 (s := ((σ:ℂ) + ((-t:ℝ):ℂ) * Complex.I)) hspos hsne
        have hconj : ((starRingEnd ℂ) ((σ:ℂ) + ((-t:ℝ):ℂ) * Complex.I)) = ((σ:ℂ) + (t:ℂ) * Complex.I) := by
          rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
          push_cast
          ring
        rw [hconj] at hc
        have heq : ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((σ:ℂ) + (t:ℂ) * Complex.I)‖
            = ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((σ:ℂ) + ((-t:ℝ):ℂ) * Complex.I)‖ := by
          rw [← hc]
          simp
        rw [heq]
        exact hbound
  refine ⟨2 * A, c, by positivity, hcpos, ?_⟩
  intro N _inst χ σ t ht hσ hσ2
  exact Work.BMF.LFunction_growth_of_hurwitz (by positivity) hcpos hc12 hHur N χ σ t ht hσ hσ2

end

end Work.BMF.VKPrimeSums
