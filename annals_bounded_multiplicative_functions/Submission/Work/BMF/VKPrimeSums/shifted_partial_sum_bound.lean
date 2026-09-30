import Mathlib
import Submission.Work.BMF.zeta_growth_defs
import Submission.Work.BMF.zeta_partial_sum_bound
import Submission.Work.BMF.VKGrowth
import Submission.Work.BMF.VKBlockTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shifted partial-sum bound in the Vinogradov–Korobov strip

`Work.BMF.VKPrimeSums.shifted_partial_sum_bound`: given the Vinogradov–Korobov exponential-sum
input `Work.BMF.VKExpSum C D`, there are `A, c > 0` with

`‖∑_{m≤M} (m+u)^{-σ-iT}‖ ≤ A (u^{-σ} + (log (T+3))^{5/6})`

whenever `u ∈ (0,1]`, `3 ≤ T`, `M ≤ T`, `0 < σ ≤ 2` and `σ ≥ 1 - c (log (T+3))^{-5/6}`.

Route.  Write `L = log (T+3)`, `δ₀ = c L^{-5/6}`.  Split off the `m = 0` term (`u^{-σ}`) and the
terms `m = 1, 2` (bounded by `1`); the remaining range `Icc 1 M` is decomposed into dyadic blocks
`(2^j, 2^{j+1}]`, `1 ≤ j ≤ J-1`, together with the final block `(2^J, M]`, `J = Nat.log 2 M`.
On every block the Abel-summation block bound `shifted_vk_block` gives
`C · exp (δ x_j − x_j³/(D L²))`, `x_j = j log 2`, and the purely analytic estimate
`dyadic_exp_tail_bound` sums these over all `j ≤ J`.
-/

set_option maxHeartbeats 2000000

namespace Work.BMF.VKPrimeSums

open Finset

noncomputable section

/-! ## §1. The block bound from `VKExpSum` -/

/-- **Vinogradov–Korobov block bound for the shifted partial sum.**  From `Work.BMF.VKExpSum C D`,
any block `(K, R]` with `2 ≤ K ≤ T` and `R ≤ 2K` satisfies
`‖Σ_{K<m≤R} (m+u)^{-σ-iT}‖ ≤ C exp((1-σ) log K − (log K)³/(D (log T)²))`.

This is Abel summation (`Work.BMF.norm_sum_Ioc_mul_le`) with the nonincreasing weight
`m ↦ (m+u)^{-σ}` against `VKExpSum`, which bounds the partial sums of `m ↦ (m+u)^{-iT}` over
`(K, r]` by `C K^{1-1/(Dλ²)}`, `λ = log T/log K`. -/
theorem shifted_vk_block (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hVK : Work.BMF.VKExpSum C D)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) {σ T : ℝ} (hσ : 0 ≤ σ)
    {K R : ℕ} (hK2 : 2 ≤ K) (hR2K : (R : ℝ) ≤ 2 * K) (hKt : (K : ℝ) ≤ T) :
    ‖∑ m ∈ Finset.Ioc K R, ((((m : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))‖ ≤
      C * Real.exp ((1 - σ) * Real.log (K : ℝ)
        - (Real.log (K : ℝ)) ^ 3 / (D * (Real.log T) ^ 2)) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK1lt : (1 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 1 < K)
  have hT2 : (2 : ℝ) ≤ T := le_trans (by exact_mod_cast hK2) hKt
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogKpos : 0 < Real.log (K : ℝ) := Real.log_pos hK1lt
  set lam : ℝ := Real.log T / Real.log (K : ℝ) with hlam
  have hB : ∀ r ∈ Finset.Ioc K R,
      ‖∑ n ∈ Finset.Ioc K r, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (T : ℂ)))‖ ≤
        C * (K : ℝ) ^ (1 - 1 / (D * lam ^ 2)) := by
    intro r hr
    obtain ⟨hKr, hrR⟩ := Finset.mem_Ioc.mp hr
    have hr2K : ((r : ℕ) : ℝ) ≤ 2 * (K : ℝ) := le_trans (by exact_mod_cast hrR) hR2K
    have h2K : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
    have hmain := hVK (K : ℝ) T h2K hKt u hu hu1 (r : ℝ) (by exact_mod_cast hKr) hr2K
    simpa only [Nat.floor_natCast] using hmain
  have hB0 : 0 ≤ C * (K : ℝ) ^ (1 - 1 / (D * lam ^ 2)) :=
    mul_nonneg hC.le (Real.rpow_nonneg hKpos.le _)
  have hw : ∀ n : ℕ, 0 ≤ ((((n : ℝ) + u)) ^ (-σ)) := fun n =>
    Real.rpow_nonneg (by positivity) _
  have hmono : ∀ n : ℕ, ((((n + 1 : ℕ) : ℝ) + u)) ^ (-σ) ≤ ((((n : ℝ) + u))) ^ (-σ) := by
    intro n
    refine Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ) + u) ?_ (by linarith)
    push_cast
    linarith
  have habel := Work.BMF.norm_sum_Ioc_mul_le (K := K) (R := R) hw hmono hB0 hB
  have hsum_eq : ∑ n ∈ Finset.Ioc K R, (((((n : ℝ) + u) ^ (-σ) : ℝ)) : ℂ) *
        ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (T : ℂ))) =
      ∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have hx : (0 : ℝ) < (n : ℝ) + u := by positivity
    have hne : ((((n : ℝ) + u : ℝ)) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      linarith
    rw [Complex.ofReal_cpow hx.le (-σ), ← Complex.cpow_add _ _ hne]
    congr 1
    push_cast
    ring
  rw [hsum_eq] at habel
  refine le_trans habel ?_
  have hwK : ((((K + 1 : ℕ) : ℝ) + u)) ^ (-σ) ≤ (K : ℝ) ^ (-σ) := by
    refine Real.rpow_le_rpow_of_nonpos hKpos ?_ (by linarith)
    push_cast
    linarith
  have hstep : ((((K + 1 : ℕ) : ℝ) + u)) ^ (-σ) * (C * (K : ℝ) ^ (1 - 1 / (D * lam ^ 2))) ≤
      C * ((K : ℝ) ^ (-σ) * (K : ℝ) ^ (1 - 1 / (D * lam ^ 2))) := by
    have h := mul_le_mul_of_nonneg_right hwK hB0
    linarith [h]
  refine le_trans hstep ?_
  have hexp : C * ((K : ℝ) ^ (-σ) * (K : ℝ) ^ (1 - 1 / (D * lam ^ 2))) =
      C * Real.exp ((1 - σ) * Real.log (K : ℝ)
        - (Real.log (K : ℝ)) ^ 3 / (D * (Real.log T) ^ 2)) := by
    congr 1
    rw [← Real.rpow_add hKpos, Real.rpow_def_of_pos hKpos, hlam]
    have hlogKne : Real.log (K : ℝ) ≠ 0 := ne_of_gt hlogKpos
    have hlogTne : Real.log T ≠ 0 := ne_of_gt hlogTpos
    have hDne : D ≠ 0 := ne_of_gt hD
    have hkey : (1 : ℝ) / (D * (Real.log T / Real.log (K : ℝ)) ^ 2)
        = (Real.log (K : ℝ)) ^ 2 / (D * (Real.log T) ^ 2) := by
      rw [div_pow]
      field_simp
      try ring
    rw [hkey]
    field_simp
    try ring_nf
  rw [hexp]

/-! ## §2. The analytic dyadic geometric-sum bound -/

/-- **Dyadic geometric-sum bound.**  For `D, δ₀, h, L > 0` and `K ≥ exp(δ₀ √(2 δ₀ D) L)`,
`Σ_{j≤J} exp(δ₀ j h − (j h)³/(D L²)) ≤ 2K (1 + 1/(δ₀ h))`, uniformly in `J`.

With `X = √(2δ₀D) L` (so `X² = 2δ₀DL²`) one has `δ₀x − x³/(DL²) ≤ δ₀X − 5δ₀(x−X)` for `x ≥ X`,
from `x³ − X³ ≥ 3X²(x−X)`.  Splitting the sum at `j₁ = ⌈X/h⌉` gives two geometric series with
ratios `e^{−δ₀h}`, `e^{−5δ₀h}`, and `1/(1−e^{−t}) ≤ 1 + 1/t` (from `Real.add_one_le_exp`). -/
theorem dyadic_exp_tail_bound (D δ₀ h K L : ℝ) (hD : 0 < D) (hδ₀ : 0 < δ₀) (hh : 0 < h)
    (hL : 0 < L) (hK : Real.exp (δ₀ * (Real.sqrt (2 * δ₀ * D) * L)) ≤ K) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1),
        Real.exp (δ₀ * ((j : ℝ) * h) - ((j : ℝ) * h) ^ 3 / (D * L ^ 2))
      ≤ 2 * K * (1 + 1 / (δ₀ * h)) := by
  set X : ℝ := Real.sqrt (2 * δ₀ * D) * L with hX
  have hDL2 : 0 < D * L ^ 2 := by positivity
  have hXsq : X ^ 2 = 2 * δ₀ * D * L ^ 2 := by
    rw [hX, mul_pow, Real.sq_sqrt (by positivity)]
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hgeom : ∀ t : ℝ, 0 < t → (1 - Real.exp (-t))⁻¹ ≤ 1 + 1 / t := by
    intro t ht
    have hexp : Real.exp (-t) ≤ 1 / (1 + t) := by
      rw [Real.exp_neg]
      have h := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < 1 + t)
        (by linarith [Real.add_one_le_exp t] : 1 + t ≤ Real.exp t)
      simpa only [one_div] using h
    have hpos : 0 < 1 - Real.exp (-t) := by
      have h := Real.exp_lt_one_iff.mpr (by linarith : -t < 0)
      linarith
    have h1 : 1 ≤ (1 + 1 / t) * (1 - Real.exp (-t)) := by
      have h2 : Real.exp (-t) * (1 + 1 / t) ≤ 1 / t := by
        have h4 : Real.exp (-t) * (1 + 1 / t) ≤ (1 / (1 + t)) * (1 + 1 / t) :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
        have h5 : (1 / (1 + t)) * (1 + 1 / t) = 1 / t := by
          field_simp
          ring
        linarith [h4, h5]
      have h6 : (1 + 1 / t) * (1 - Real.exp (-t))
          = 1 + 1 / t - Real.exp (-t) * (1 + 1 / t) := by ring
      rw [h6]
      linarith
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    linarith
  have hgeo : ∀ t : ℝ, 0 < t → ∀ n : ℕ,
      ∑ k ∈ Finset.range n, Real.exp (-t * (k : ℝ)) ≤ (1 - Real.exp (-t))⁻¹ := by
    intro t ht n
    have hlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hc : ∑ k ∈ Finset.range n, Real.exp (-t * (k : ℝ))
        = ∑ k ∈ Finset.range n, (Real.exp (-t)) ^ k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [mul_comm, Real.exp_nat_mul]
    rw [hc, Finset.range_eq_Ico]
    have h := geom_sum_Ico_le_of_lt_one (x := Real.exp (-t)) (by positivity) hlt (m := 0) (n := n)
    simpa using h
  obtain ⟨j₁, hj₁le, hj₁lt⟩ : ∃ j₁ : ℕ, X ≤ (j₁ : ℝ) * h ∧ ((j₁ : ℝ) - 1) * h < X := by
    refine ⟨⌈X / h⌉₊, ?_, ?_⟩
    · have h1 : X / h ≤ ((⌈X / h⌉₊ : ℕ) : ℝ) := Nat.le_ceil (X / h)
      calc X = (X / h) * h := by field_simp
        _ ≤ ((⌈X / h⌉₊ : ℕ) : ℝ) * h := mul_le_mul_of_nonneg_right h1 hh.le
    · have h1 : ((⌈X / h⌉₊ : ℕ) : ℝ) < X / h + 1 := Nat.ceil_lt_add_one (by positivity)
      have h2 : ((⌈X / h⌉₊ : ℕ) : ℝ) - 1 < X / h := by linarith
      calc (((⌈X / h⌉₊ : ℕ) : ℝ) - 1) * h < (X / h) * h := mul_lt_mul_of_pos_right h2 hh
        _ = X := by field_simp
  have hcast : ∀ j : ℕ, j < j₁ → (((j₁ - 1 - j : ℕ)) : ℝ) = (j₁ : ℝ) - 1 - (j : ℝ) := by
    intro j hj
    rw [Nat.cast_sub (by omega : j ≤ j₁ - 1), Nat.cast_sub (by omega : 1 ≤ j₁)]
    ring
  have hterm1 : ∀ j : ℕ, j < j₁ →
      Real.exp (δ₀ * ((j : ℝ) * h) - ((j : ℝ) * h) ^ 3 / (D * L ^ 2)) ≤
        Real.exp (δ₀ * X) * Real.exp (-(δ₀ * h) * (((j₁ - 1 - j : ℕ)) : ℝ)) := by
    intro j hj
    have hXge : ((j₁ : ℝ) - 1) * h ≤ X := le_of_lt hj₁lt
    have hcube : 0 ≤ ((j : ℝ) * h) ^ 3 / (D * L ^ 2) := by positivity
    have hlin : δ₀ * (((j₁ : ℝ) - 1) * h) ≤ δ₀ * X := mul_le_mul_of_nonneg_left hXge hδ₀.le
    have hexpand : δ₀ * X + -(δ₀ * h) * ((j₁ : ℝ) - 1 - (j : ℝ))
        = δ₀ * X + δ₀ * ((j : ℝ) * h) - δ₀ * (((j₁ : ℝ) - 1) * h) := by ring
    have hkey : δ₀ * ((j : ℝ) * h) - ((j : ℝ) * h) ^ 3 / (D * L ^ 2)
        ≤ δ₀ * X + -(δ₀ * h) * (((j₁ - 1 - j : ℕ)) : ℝ) := by
      rw [hcast j hj, hexpand]
      linarith
    calc Real.exp (δ₀ * ((j : ℝ) * h) - ((j : ℝ) * h) ^ 3 / (D * L ^ 2))
        ≤ Real.exp (δ₀ * X + -(δ₀ * h) * (((j₁ - 1 - j : ℕ)) : ℝ)) := Real.exp_le_exp.mpr hkey
      _ = Real.exp (δ₀ * X) * Real.exp (-(δ₀ * h) * (((j₁ - 1 - j : ℕ)) : ℝ)) := by
          rw [Real.exp_add]
  have hterm2 : ∀ (n k : ℕ),
      Real.exp (δ₀ * ((((j₁ + k : ℕ)) : ℝ) * h) - ((((j₁ + k : ℕ)) : ℝ) * h) ^ 3 / (D * L ^ 2)) ≤
        Real.exp (δ₀ * X) * Real.exp (-(5 * δ₀ * h) * (k : ℝ)) := by
    intro n k
    set x : ℝ := (((j₁ + k : ℕ)) : ℝ) * h with hx
    have hxX : X ≤ x := by
      have h1 : (j₁ : ℝ) ≤ (((j₁ + k : ℕ)) : ℝ) := by push_cast; linarith
      have h2 : X ≤ (((j₁ + k : ℕ)) : ℝ) * h :=
        le_trans hj₁le (mul_le_mul_of_nonneg_right h1 hh.le)
      simpa [hx] using h2
    have hcube : 6 * δ₀ * (x - X) ≤ x ^ 3 / (D * L ^ 2) := by
      have hfac : x ^ 3 - X ^ 3 = (x - X) * (x ^ 2 + x * X + X ^ 2) := by ring
      have hge : 3 * X ^ 2 ≤ x ^ 2 + x * X + X ^ 2 := by nlinarith [sq_nonneg (x - X)]
      have hcancel : 3 * X ^ 2 = 6 * δ₀ * D * L ^ 2 := by rw [hXsq]; ring
      have hX3 : 0 ≤ X ^ 3 := by positivity
      have hxx : 0 ≤ x - X := by linarith
      rw [le_div_iff₀ hDL2]
      nlinarith [hfac, hge, hcancel, hX3, hxx]
    have hk : (k : ℝ) * h ≤ x - X := by
      have h2 : (((j₁ + k : ℕ)) : ℝ) = (j₁ : ℝ) + (k : ℝ) := by push_cast; ring
      rw [hx, h2]
      nlinarith [hj₁le]
    have hkey : δ₀ * x - x ^ 3 / (D * L ^ 2) ≤ δ₀ * X + -(5 * δ₀ * h) * (k : ℝ) := by
      have hmult : 0 ≤ 5 * δ₀ := by positivity
      nlinarith [hcube, hk, hmult]
    calc Real.exp (δ₀ * ((((j₁ + k : ℕ)) : ℝ) * h) - ((((j₁ + k : ℕ)) : ℝ) * h) ^ 3 / (D * L ^ 2))
        = Real.exp (δ₀ * x - x ^ 3 / (D * L ^ 2)) := by rw [hx]
      _ ≤ Real.exp (δ₀ * X + -(5 * δ₀ * h) * (k : ℝ)) := Real.exp_le_exp.mpr hkey
      _ = Real.exp (δ₀ * X) * Real.exp (-(5 * δ₀ * h) * (k : ℝ)) := by rw [Real.exp_add]
  have hpart1 : ∑ j ∈ Finset.range j₁,
      Real.exp (δ₀ * ((j : ℝ) * h) - ((j : ℝ) * h) ^ 3 / (D * L ^ 2)) ≤
        Real.exp (δ₀ * X) * (1 - Real.exp (-(δ₀ * h)))⁻¹ := by
    calc ∑ j ∈ Finset.range j₁,
          Real.exp (δ₀ * ((j : ℝ) * h) - ((j : ℝ) * h) ^ 3 / (D * L ^ 2))
        ≤ ∑ j ∈ Finset.range j₁,
            Real.exp (δ₀ * X) * Real.exp (-(δ₀ * h) * (((j₁ - 1 - j : ℕ)) : ℝ)) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          rw [Finset.mem_range] at hj
          exact hterm1 j hj
      _ = Real.exp (δ₀ * X) *
            ∑ j ∈ Finset.range j₁, Real.exp (-(δ₀ * h) * (((j₁ - 1 - j : ℕ)) : ℝ)) := by
          rw [Finset.mul_sum]
      _ = Real.exp (δ₀ * X) * ∑ k ∈ Finset.range j₁, Real.exp (-(δ₀ * h) * (k : ℝ)) := by
          rw [Finset.sum_range_reflect (fun k : ℕ => Real.exp (-(δ₀ * h) * (k : ℝ)))]
      _ ≤ Real.exp (δ₀ * X) * (1 - Real.exp (-(δ₀ * h)))⁻¹ :=
          mul_le_mul_of_nonneg_left (hgeo (δ₀ * h) (mul_pos hδ₀ hh) j₁) (Real.exp_pos _).le
  have hpart2 : ∀ n : ℕ, ∑ k ∈ Finset.range n,
      Real.exp (δ₀ * ((((j₁ + k : ℕ)) : ℝ) * h) - ((((j₁ + k : ℕ)) : ℝ) * h) ^ 3 / (D * L ^ 2)) ≤
        Real.exp (δ₀ * X) * (1 - Real.exp (-(5 * δ₀ * h)))⁻¹ := by
    intro n
    calc ∑ k ∈ Finset.range n,
          Real.exp (δ₀ * ((((j₁ + k : ℕ)) : ℝ) * h) - ((((j₁ + k : ℕ)) : ℝ) * h) ^ 3 / (D * L ^ 2))
        ≤ ∑ k ∈ Finset.range n, Real.exp (δ₀ * X) * Real.exp (-(5 * δ₀ * h) * (k : ℝ)) :=
          Finset.sum_le_sum (fun k _ => hterm2 n k)
      _ = Real.exp (δ₀ * X) * ∑ k ∈ Finset.range n, Real.exp (-(5 * δ₀ * h) * (k : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ Real.exp (δ₀ * X) * (1 - Real.exp (-(5 * δ₀ * h)))⁻¹ :=
          mul_le_mul_of_nonneg_left (hgeo (5 * δ₀ * h) (by positivity) n) (Real.exp_pos _).le
  have hKpos : 0 < K := lt_of_lt_of_le (Real.exp_pos _) hK
  have hg1 : (1 - Real.exp (-(δ₀ * h)))⁻¹ ≤ 1 + 1 / (δ₀ * h) := hgeom (δ₀ * h) (mul_pos hδ₀ hh)
  have hg2 : (1 - Real.exp (-(5 * δ₀ * h)))⁻¹ ≤ 1 + 1 / (δ₀ * h) := by
    have h1 := hgeom (5 * δ₀ * h) (by positivity)
    have h2 : 1 / (5 * δ₀ * h) ≤ 1 / (δ₀ * h) := by
      refine one_div_le_one_div_of_le (mul_pos hδ₀ hh) ?_
      linarith [mul_pos hδ₀ hh]
    linarith
  have hpos1 : 0 < 1 - Real.exp (-(δ₀ * h)) := by
    have h := Real.exp_lt_one_iff.mpr (by linarith [mul_pos hδ₀ hh] : -(δ₀ * h) < 0)
    linarith
  have hpos2 : 0 < 1 - Real.exp (-(5 * δ₀ * h)) := by
    have h := Real.exp_lt_one_iff.mpr (by linarith [mul_pos hδ₀ hh] : -(5 * δ₀ * h) < 0)
    linarith
  have hb1 : Real.exp (δ₀ * X) * (1 - Real.exp (-(δ₀ * h)))⁻¹ ≤ K * (1 + 1 / (δ₀ * h)) :=
    mul_le_mul hK hg1 (inv_pos.mpr hpos1).le hKpos.le
  have hb2 : Real.exp (δ₀ * X) * (1 - Real.exp (-(5 * δ₀ * h)))⁻¹ ≤ K * (1 + 1 / (δ₀ * h)) :=
    mul_le_mul hK hg2 (inv_pos.mpr hpos2).le hKpos.le
  have hgoal2 : K * (1 + 1 / (δ₀ * h)) ≤ 2 * K * (1 + 1 / (δ₀ * h)) := by
    have h : 0 ≤ K * (1 + 1 / (δ₀ * h)) := by positivity
    linarith
  rcases le_or_gt j₁ (J + 1) with hj1 | hj1
  · have hlen : j₁ + (J + 1 - j₁) = J + 1 := by omega
    rw [← hlen, Finset.sum_range_add
        (fun j : ℕ => Real.exp (δ₀ * ((j : ℝ) * h) - ((j : ℝ) * h) ^ 3 / (D * L ^ 2))) j₁ (J + 1 - j₁)]
    have h2 := hpart2 (J + 1 - j₁)
    linarith [hpart1, hb1, h2, hb2, hgoal2]
  · have hsub : Finset.range (J + 1) ⊆ Finset.range j₁ := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    have hmono : (∑ j ∈ Finset.range (J + 1),
          Real.exp (δ₀ * ((j : ℝ) * h) - ((j : ℝ) * h) ^ 3 / (D * L ^ 2)))
        ≤ ∑ j ∈ Finset.range j₁,
          Real.exp (δ₀ * ((j : ℝ) * h) - ((j : ℝ) * h) ^ 3 / (D * L ^ 2)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (f := fun j : ℕ =>
        Real.exp (δ₀ * ((j : ℝ) * h) - ((j : ℝ) * h) ^ 3 / (D * L ^ 2))) hsub
        (fun i _ _ => (Real.exp_pos _).le)
    linarith [hpart1, hb1, hmono, hgoal2]

/-! ## §3. The dyadic decomposition of `Finset.Icc 1 M` -/

private lemma sum_Icc_split_Ioc (f : ℕ → ℂ) (A B C : ℕ) (h1 : A ≤ B) (h2 : B ≤ C) :
    ∑ n ∈ Finset.Icc A C, f n = ∑ n ∈ Finset.Icc A B, f n + ∑ n ∈ Finset.Ioc B C, f n := by
  have hdisj : Disjoint (Finset.Icc A B) (Finset.Ioc B C) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_Ioc] at hx'
    omega
  rw [← Finset.sum_union hdisj]
  congr 1
  ext x
  simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
  omega

private lemma sum_Icc_two_pow (f : ℕ → ℂ) (J : ℕ) :
    ∑ n ∈ Finset.Icc 1 (2 ^ J), f n
      = f 1 + ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    exact sum_Icc_split_Ioc f 1 (2 ^ J) (2 ^ (J + 1)) (Nat.one_le_two_pow)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J))

private lemma sum_range_eq_zero_add (g : ℕ → ℂ) (J : ℕ) (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.range J, g j = g 0 + ∑ j ∈ Finset.Icc 1 (J - 1), g j := by
  have hset : Finset.range J = insert 0 (Finset.Icc 1 (J - 1)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]

private lemma dyadic_decomp (f : ℕ → ℂ) (T0 J : ℕ) (hJ : 1 ≤ J) (h2J : 2 ^ J ≤ T0) :
    ∑ n ∈ Finset.Icc 1 T0, f n
      = f 1 + f 2 + ∑ j ∈ Finset.Icc 1 (J - 1), ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n
        + ∑ n ∈ Finset.Ioc (2 ^ J) T0, f n := by
  have h1 := sum_Icc_two_pow f J
  have h2 := sum_range_eq_zero_add
    (fun j => ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n) J hJ
  have hz : (∑ n ∈ Finset.Ioc (2 ^ 0) (2 ^ (0 + 1)), f n) = f 2 := by
    have : Finset.Ioc (2 ^ 0) (2 ^ (0 + 1)) = ({2} : Finset ℕ) := by decide
    rw [this, Finset.sum_singleton]
  rw [sum_Icc_split_Ioc f 1 (2 ^ J) T0 Nat.one_le_two_pow h2J, h1, h2, hz]
  ring

/-! ## §4. The main bound -/

private lemma core_bound (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hVK : Work.BMF.VKExpSum C D) :
    ∀ (u : ℝ) (M : ℕ) (σ T : ℝ), 0 < u → u ≤ 1 →
      3 ≤ T → 0 < σ → σ ≤ 2 →
      1 - (1 / (100 * (1 + D))) * Real.log (T + 3) ^ (-(5 / 6 : ℝ)) ≤ σ → (M : ℝ) ≤ T →
      ‖∑ m ∈ Finset.Icc 0 M,
          ((((m : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))‖ ≤
        (3 + 10000 * C * (1 + D)) * (u ^ (-σ) + Real.log (T + 3) ^ (5 / 6 : ℝ)) := by
  intro u M σ T hu hu1 hT3 hσ0 hσ2 hreg hMT
  set L : ℝ := Real.log (T + 3) with hL
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hL1 : 1 ≤ L := by
    rw [hL]
    have h1 : (1 : ℝ) ≤ Real.log 6 :=
      (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 6)).mpr
        (by linarith [Real.exp_one_lt_three])
    exact le_trans h1 (Real.log_le_log (by norm_num) (by linarith))
  have hLnn : 0 ≤ L := le_of_lt hLpos
  set δ₀ : ℝ := (1 / (100 * (1 + D))) * L ^ (-(5 / 6 : ℝ)) with hδ₀def
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀def]; positivity
  have hδ : 1 - σ ≤ δ₀ := by linarith [hreg]
  have hL56 : 1 ≤ L ^ (5 / 6 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hδ₀inv : δ₀⁻¹ = 100 * (1 + D) * L ^ (5 / 6 : ℝ) := by
    rw [hδ₀def, mul_inv]
    rw [show (1 / (100 * (1 + D)))⁻¹ = 100 * (1 + D) by rw [one_div, inv_inv]]
    rw [show (L ^ (-(5 / 6 : ℝ)))⁻¹ = L ^ (5 / 6 : ℝ) by
      rw [← Real.rpow_neg hLnn (-(5 / 6 : ℝ))]
      norm_num]
  set f : ℕ → ℂ := fun m => ((((m : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)) with hf
  have hf0 : ‖f 0‖ = u ^ (-σ) := by
    simp only [hf]
    have hcast : ((((((0 : ℕ) : ℝ)) + u : ℝ)) : ℂ) = ((u : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hu]
    have hre : (-((σ : ℂ) + (T : ℂ) * Complex.I)).re = -σ := by simp
    rw [hre]
  have hnorm_le_one : ∀ m : ℕ, 1 ≤ m → ‖f m‖ ≤ 1 := by
    intro m hm
    simp only [hf]
    have hx : (0 : ℝ) < (((m : ℕ) : ℝ)) + u := by positivity
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hre : (-((σ : ℂ) + (T : ℂ) * Complex.I)).re = -σ := by simp
    rw [hre]
    refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
    have h1' : (1 : ℝ) ≤ (((m : ℕ) : ℝ)) := by exact_mod_cast hm
    linarith
  have hIcc : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  have htri0 : ‖f 0 + ∑ m ∈ Finset.Icc 1 M, f m‖ ≤ u ^ (-σ) + ‖∑ m ∈ Finset.Icc 1 M, f m‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [hf0]
  have hupos : 0 ≤ u ^ (-σ) := Real.rpow_nonneg hu.le _
  have hA1 : 1 ≤ 3 + 10000 * C * (1 + D) := by
    have h1 : 0 ≤ C * (1 + D) := by positivity
    linarith
  rcases le_or_gt M 1 with hM1 | hM2
  · have hsmall : ‖∑ m ∈ Finset.Icc 1 M, f m‖ ≤ 1 := by
      have hM01 : M = 0 ∨ M = 1 := by omega
      rcases hM01 with h | h
      · subst h; simp
      · subst h
        rw [Finset.Icc_self, Finset.sum_singleton]
        exact hnorm_le_one 1 le_rfl
    have h1 : u ^ (-σ) ≤ (3 + 10000 * C * (1 + D)) * u ^ (-σ) :=
      le_mul_of_one_le_left hupos hA1
    have h2 : 1 ≤ (3 + 10000 * C * (1 + D)) * L ^ (5 / 6 : ℝ) := by nlinarith [hA1, hL56]
    have hmain : ‖f 0 + ∑ m ∈ Finset.Icc 1 M, f m‖
        ≤ (3 + 10000 * C * (1 + D)) * (u ^ (-σ) + L ^ (5 / 6 : ℝ)) := by
      linarith [htri0, hsmall, h1, h2]
    simpa only [hf] using hmain
  · have hDnn : 0 ≤ D := hD.le
    have hCnn : 0 ≤ C := hC.le
    have hf1 : ‖f 1‖ ≤ 1 := hnorm_le_one 1 le_rfl
    have hf2 : ‖f 2‖ ≤ 1 := hnorm_le_one 2 (by norm_num)
    set J : ℕ := Nat.log 2 M with hJdef
    have hJ1 : 1 ≤ J := by rw [hJdef]; exact Nat.log_pos_iff.mpr ⟨hM2, by norm_num⟩
    have h2J : 2 ^ J ≤ M := by rw [hJdef]; exact Nat.pow_log_le_self 2 (by omega)
    have hMJ : M < 2 ^ (J + 1) := by rw [hJdef]; exact Nat.lt_pow_succ_log_self (by norm_num) M
    set G : ℕ → ℝ := fun j => Real.exp (δ₀ * ((j : ℝ) * Real.log 2)
      - ((j : ℝ) * Real.log 2) ^ 3 / (D * L ^ 2)) with hG
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hexp4 : Real.exp (δ₀ * (Real.sqrt (2 * δ₀ * D) * L)) ≤ 4 := by
      have hs : (0 : ℝ) ≤ 2 * δ₀ * D := by positivity
      have h1 : (δ₀ * (Real.sqrt (2 * δ₀ * D) * L)) ^ 2 = 2 * δ₀ ^ 3 * D * L ^ 2 := by
        have hsqr : (Real.sqrt (2 * δ₀ * D)) ^ 2 = 2 * δ₀ * D := Real.sq_sqrt hs
        calc (δ₀ * (Real.sqrt (2 * δ₀ * D) * L)) ^ 2
            = δ₀ ^ 2 * (Real.sqrt (2 * δ₀ * D)) ^ 2 * L ^ 2 := by ring
          _ = δ₀ ^ 2 * (2 * δ₀ * D) * L ^ 2 := by rw [hsqr]
          _ = 2 * δ₀ ^ 3 * D * L ^ 2 := by ring
      have hpow : (L ^ (-(5 / 6 : ℝ))) ^ 3 = L ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLnn]
        norm_num
      have hsplit : L ^ (-(5 / 2 : ℝ)) * L ^ 2 = L ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast L 2, ← Real.rpow_add hLpos]
        norm_num
      set E : ℝ := 1 / (100 * (1 + D)) ^ 3 with hE
      have hDle : 2 * D * E ≤ 1 := by
        have h1' : (1 : ℝ) ≤ 100 * (1 + D) := by linarith [hD]
        have h4 : (1 : ℝ) ≤ (100 * (1 + D)) ^ 2 := by nlinarith [h1']
        have h2' : 100 * (1 + D) ≤ (100 * (1 + D)) ^ 3 := by
          calc 100 * (1 + D) = 100 * (1 + D) * 1 := by ring
            _ ≤ 100 * (1 + D) * (100 * (1 + D)) ^ 2 :=
                mul_le_mul_of_nonneg_left h4 (by linarith)
            _ = (100 * (1 + D)) ^ 3 := by ring
        have h3' : 2 * D ≤ 100 * (1 + D) := by linarith [hD]
        have h5 : 2 * D / (100 * (1 + D)) ^ 3 ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith
        rw [hE, one_div]
        have h := h5
        rw [div_eq_mul_inv] at h
        exact h
      have hLhalf : L ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
      have hsq : (δ₀ * (Real.sqrt (2 * δ₀ * D) * L)) ^ 2 ≤ 1 := by
        rw [h1, hδ₀def]
        have h3 : ((1 / (100 * (1 + D))) * L ^ (-(5 / 6 : ℝ))) ^ 3
            = E * L ^ (-(5 / 2 : ℝ)) := by
          rw [mul_pow, hpow, hE, div_pow, one_pow]
        rw [h3]
        calc 2 * (E * L ^ (-(5 / 2 : ℝ))) * D * L ^ 2
            = (2 * D * E) * (L ^ (-(5 / 2 : ℝ)) * L ^ 2) := by ring
          _ = (2 * D * E) * L ^ (-(1 / 2 : ℝ)) := by rw [hsplit]
          _ ≤ 1 * 1 := mul_le_mul hDle hLhalf (by positivity) (by norm_num)
          _ = 1 := by ring
      have hnn : 0 ≤ δ₀ * (Real.sqrt (2 * δ₀ * D) * L) := by positivity
      have hle1 : δ₀ * (Real.sqrt (2 * δ₀ * D) * L) ≤ 1 := by
        nlinarith [hsq, hnn, sq_nonneg (δ₀ * (Real.sqrt (2 * δ₀ * D) * L) - 1)]
      have h2 : Real.exp (δ₀ * (Real.sqrt (2 * δ₀ * D) * L)) ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr hle1
      linarith [Real.exp_one_lt_three]
    have htail := dyadic_exp_tail_bound D δ₀ (Real.log 2) 4 L hD hδ₀pos hlog2pos hLpos hexp4 J
    have hexp_le : ∀ j : ℕ, 1 ≤ j →
        (1 - σ) * Real.log (((2 ^ j : ℕ) : ℝ))
            - (Real.log (((2 ^ j : ℕ) : ℝ))) ^ 3 / (D * (Real.log T) ^ 2) ≤
          δ₀ * ((j : ℝ) * Real.log 2) - ((j : ℝ) * Real.log 2) ^ 3 / (D * L ^ 2) := by
      intro j hj
      rw [show (((2 ^ j : ℕ) : ℝ)) = (2 : ℝ) ^ j by push_cast; ring, Real.log_pow]
      have hlogT_le : Real.log T ≤ L := by
        rw [hL]
        exact Real.log_le_log (by linarith) (by linarith)
      have hlogTpos' : 0 < Real.log T := Real.log_pos (by linarith)
      have h1 : (1 - σ) * ((j : ℝ) * Real.log 2) ≤ δ₀ * ((j : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonneg_right hδ (by positivity)
      have h2 : ((j : ℝ) * Real.log 2) ^ 3 / (D * L ^ 2)
          ≤ ((j : ℝ) * Real.log 2) ^ 3 / (D * (Real.log T) ^ 2) := by
        have hlogT2 : (Real.log T) ^ 2 ≤ L ^ 2 := by nlinarith [hlogT_le, hlogTpos'.le]
        have hden : D * (Real.log T) ^ 2 ≤ D * L ^ 2 :=
          mul_le_mul_of_nonneg_left hlogT2 hD.le
        exact div_le_div_of_nonneg_left (by positivity) (mul_pos hD (pow_pos hlogTpos' 2)) hden
      linarith
    have hmid : ∀ j ∈ Finset.Icc 1 (J - 1),
        ‖∑ m ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f m‖ ≤ C * G j := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      obtain ⟨hj1, hjJ⟩ := hj
      have hK2 : 2 ≤ 2 ^ j := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
      have hR2K : (((2 ^ (j + 1) : ℕ)) : ℝ) ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
        have h1 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ, Nat.mul_comm]
        rw [h1, Nat.cast_mul, Nat.cast_ofNat]
      have hKt : ((2 ^ j : ℕ) : ℝ) ≤ T := by
        have h1 : 2 ^ j ≤ M := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : j ≤ J)) h2J
        have h2 : (((2 ^ j : ℕ)) : ℝ) ≤ (((M : ℕ)) : ℝ) := by exact_mod_cast h1
        linarith
      have hb := shifted_vk_block C D hC hD hVK hu hu1 hσ0.le hK2 hR2K hKt
      simp only [hf] at hb ⊢
      refine le_trans hb ?_
      simp only [hG]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hexp_le j hj1)) hC.le
    have hlast : ‖∑ m ∈ Finset.Ioc (2 ^ J) M, f m‖ ≤ C * G J := by
      have hK2 : 2 ≤ 2 ^ J := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hJ1
      have hR2K : ((M : ℕ) : ℝ) ≤ 2 * ((2 ^ J : ℕ) : ℝ) := by
        have h1 : ((2 ^ (J + 1) : ℕ) : ℝ) = 2 * ((2 ^ J : ℕ) : ℝ) := by
          have h1' : 2 ^ (J + 1) = 2 * 2 ^ J := by rw [pow_succ, Nat.mul_comm]
          rw [h1', Nat.cast_mul, Nat.cast_ofNat]
        have h2 : (M : ℝ) < ((2 ^ (J + 1) : ℕ) : ℝ) := by exact_mod_cast hMJ
        linarith
      have hKt : ((2 ^ J : ℕ) : ℝ) ≤ T := by
        have h2 : (((2 ^ J : ℕ)) : ℝ) ≤ (((M : ℕ)) : ℝ) := by exact_mod_cast h2J
        linarith
      have hb := shifted_vk_block C D hC hD hVK hu hu1 hσ0.le hK2 hR2K hKt
      simp only [hf] at hb ⊢
      refine le_trans hb ?_
      simp only [hG]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hexp_le J hJ1)) hC.le
    have hinner : ‖∑ m ∈ Finset.Icc 1 M, f m‖
        ≤ 2 + C * (∑ j ∈ Finset.Icc 1 (J - 1), G j) + C * G J := by
      rw [dyadic_decomp f M J hJ1 h2J]
      have hmiddle : ‖∑ j ∈ Finset.Icc 1 (J - 1),
            ∑ m ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f m‖ ≤ C * ∑ j ∈ Finset.Icc 1 (J - 1), G j := by
        refine le_trans (norm_sum_le _ _) ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun j hj => hmid j hj)
      have ha := norm_add_le (f 1 + f 2 + (∑ j ∈ Finset.Icc 1 (J - 1),
          ∑ m ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f m)) (∑ m ∈ Finset.Ioc (2 ^ J) M, f m)
      have hb := norm_add_le (f 1 + f 2) (∑ j ∈ Finset.Icc 1 (J - 1),
          ∑ m ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f m)
      have hc := norm_add_le (f 1) (f 2)
      linarith [ha, hb, hc, hmiddle, hlast, hf1, hf2]
    have hGsum : ∑ j ∈ Finset.Icc 1 (J - 1), G j ≤ ∑ j ∈ Finset.range (J + 1), G j := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => (Real.exp_pos _).le)
      intro x hx
      rw [Finset.mem_Icc] at hx
      rw [Finset.mem_range]
      omega
    have hGJ : G J ≤ ∑ j ∈ Finset.range (J + 1), G j :=
      Finset.single_le_sum (f := G) (fun i _ => (Real.exp_pos _).le)
        (Finset.mem_range.mpr (Nat.lt_succ_self J))
    have hGtot : ∑ j ∈ Finset.range (J + 1), G j ≤ 8 * (1 + 1 / (δ₀ * Real.log 2)) := by
      have h := htail
      simp only [hG]
      linarith [h]
    have hlog2half : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hinv : (Real.log 2)⁻¹ ≤ 2 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hlog2half
      simpa using h
    have hfinv : 1 / (δ₀ * Real.log 2) ≤ 200 * (1 + D) * L ^ (5 / 6 : ℝ) := by
      rw [one_div, mul_inv, hδ₀inv]
      have h2 : 0 ≤ 100 * (1 + D) * L ^ (5 / 6 : ℝ) := by positivity
      calc 100 * (1 + D) * L ^ (5 / 6 : ℝ) * (Real.log 2)⁻¹
          ≤ 100 * (1 + D) * L ^ (5 / 6 : ℝ) * 2 := mul_le_mul_of_nonneg_left hinv h2
        _ = 200 * (1 + D) * L ^ (5 / 6 : ℝ) := by ring
    have hXnn : 0 ≤ C * (1 + D) * L ^ (5 / 6 : ℝ) := by positivity
    have hblocks : C * (∑ j ∈ Finset.Icc 1 (J - 1), G j) + C * G J
        ≤ 4000 * (C * (1 + D) * L ^ (5 / 6 : ℝ)) := by
      have hstep1 : C * (∑ j ∈ Finset.Icc 1 (J - 1), G j) + C * G J
          ≤ 16 * (C * (1 + 1 / (δ₀ * Real.log 2))) := by
        have hsum2 : (∑ j ∈ Finset.Icc 1 (J - 1), G j) + G J
            ≤ 16 * (1 + 1 / (δ₀ * Real.log 2)) := by linarith [hGsum, hGJ, hGtot]
        nlinarith [hsum2, hCnn]
      have hbase : (1 : ℝ) ≤ (1 + D) * L ^ (5 / 6 : ℝ) := by
        have := mul_le_mul hL56 (le_refl (1 + D)) (by linarith) (by linarith)
        linarith
      have h2 : 1 + 1 / (δ₀ * Real.log 2) ≤ 201 * ((1 + D) * L ^ (5 / 6 : ℝ)) := by
        have h1 : 1 + 1 / (δ₀ * Real.log 2) ≤ 1 + 200 * ((1 + D) * L ^ (5 / 6 : ℝ)) := by
          have h3 : 200 * (1 + D) * L ^ (5 / 6 : ℝ) = 200 * ((1 + D) * L ^ (5 / 6 : ℝ)) := by
            ring
          linarith [hfinv, h3]
        nlinarith [hbase, h1]
      calc C * (∑ j ∈ Finset.Icc 1 (J - 1), G j) + C * G J
          ≤ 16 * (C * (1 + 1 / (δ₀ * Real.log 2))) := hstep1
        _ = C * (16 * (1 + 1 / (δ₀ * Real.log 2))) := by ring
        _ ≤ C * (16 * (201 * ((1 + D) * L ^ (5 / 6 : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hCnn
            nlinarith [h2]
        _ = 3216 * (C * (1 + D) * L ^ (5 / 6 : ℝ)) := by ring
        _ ≤ 4000 * (C * (1 + D) * L ^ (5 / 6 : ℝ)) :=
            mul_le_mul_of_nonneg_right (by norm_num) hXnn
    have hfinal : u ^ (-σ) + 2 + 4000 * (C * (1 + D) * L ^ (5 / 6 : ℝ))
        ≤ (3 + 10000 * C * (1 + D)) * (u ^ (-σ) + L ^ (5 / 6 : ℝ)) := by
      have h2 : 2 ≤ 3 * L ^ (5 / 6 : ℝ) := by linarith [hL56]
      have h3 : 4000 * (C * (1 + D) * L ^ (5 / 6 : ℝ))
          ≤ 10000 * (C * (1 + D) * L ^ (5 / 6 : ℝ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hXnn
      have h4 : u ^ (-σ) ≤ 3 * u ^ (-σ) := by linarith [hupos]
      have h5 : 0 ≤ 10000 * (C * (1 + D)) * u ^ (-σ) := by positivity
      nlinarith [h2, h3, h4, h5]
    have hmain : ‖f 0 + ∑ m ∈ Finset.Icc 1 M, f m‖
        ≤ (3 + 10000 * C * (1 + D)) * (u ^ (-σ) + L ^ (5 / 6 : ℝ)) := by
      linarith [htri0, hinner, hblocks, hfinal]
    simpa only [hf] using hmain

theorem shifted_partial_sum_bound (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hVK : Work.BMF.VKExpSum C D) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ (u : ℝ) (M : ℕ) (σ T : ℝ), 0 < u → u ≤ 1 →
        3 ≤ T → 0 < σ → σ ≤ 2 →
        1 - c * Real.log (T + 3) ^ (-(5 / 6 : ℝ)) ≤ σ → (M : ℝ) ≤ T →
        ‖∑ m ∈ Finset.Icc 0 M,
            ((((m : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))‖ ≤
          A * (u ^ (-σ) + Real.log (T + 3) ^ (5 / 6 : ℝ)) :=
  ⟨3 + 10000 * C * (1 + D), 1 / (100 * (1 + D)), by positivity, by positivity,
    core_bound C D hC hD hVK⟩

end

end Work.BMF.VKPrimeSums
