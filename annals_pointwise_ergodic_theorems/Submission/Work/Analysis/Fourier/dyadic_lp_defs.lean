import Mathlib

/-!
# The dyadic Littlewood–Paley kernels on `ℤ` (definitions)

We build the classical dyadic decomposition of the identity on `ℤ` using *normalised Fejér*
(triangular) kernels.  For `N : ℕ` put

`fejerCoeff N n = (N+1)⁻¹ * max 0 (1 - |n| / (N+1))`,   `n : ℤ`,

the coefficients of the normalised Fejér kernel of degree `N`: they are nonnegative, supported at
`|n| ≤ N`, and satisfy `fejerCoeff N n ≤ (N+1)⁻¹`.

The dyadic kernels are obtained from the "base" family

`dyadBase 0 n = δ_{n,0}`,   `dyadBase l n = fejerCoeff (2^l) n`  (`l ≥ 1`)

by differencing: `dyadK l = dyadBase l - dyadBase (l+1)`.  Thus `dyadK 0 = δ_0 - v_2` and
`dyadK l = v_{2^l} - v_{2^{l+1}}` for `l ≥ 1`.  Every `dyadK l` is finitely supported in
`|n| ≤ 2^{l+1}`, is even, and has zero total mass.

As Fourier multipliers the kernels are the trigonometric polynomials

`dyadMult l θ = ∑_{|n| ≤ 2^{l+1}} dyadK l n * exp (-2 π i n θ)`,
`dyadMult 0 = 1 - fejerPoly 2`, `dyadMult l = fejerPoly (2^l) - fejerPoly (2^{l+1})`,

where `fejerPoly N θ = ∑_{|n| ≤ N} fejerCoeff N n * exp (-2 π i n θ)` is the level-`N` Fejér
polynomial.  Its closed form is the real function `fejerWin N θ` (the classical Fejér kernel
`(sin (π (N+1) θ) / ((N+1) sin (π θ)))²`), and `dyadMultR l θ = dyadBaseR l θ - dyadBaseR (l+1) θ`
with `dyadBaseR 0 = 1`, `dyadBaseR l = fejerWin (2^l)` is the corresponding real multiplier.
-/
namespace Work.Analysis.Fourier
open scoped BigOperators ENNReal
noncomputable section

def fejerCoeff (N : ℕ) (n : ℤ) : ℝ :=
  ((N : ℝ) + 1)⁻¹ * max 0 (1 - |(n : ℝ)| / ((N : ℝ) + 1))

def dyadBase (l : ℕ) (n : ℤ) : ℂ :=
  if l = 0 then (if n = 0 then 1 else 0) else (fejerCoeff (2 ^ l) n : ℂ)

def dyadK (l : ℕ) (n : ℤ) : ℂ := dyadBase l n - dyadBase (l + 1) n

def fejerPoly (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (fejerCoeff N n : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ)))

def fejerWin (N : ℕ) (θ : ℝ) : ℝ :=
  if Real.sin (Real.pi * θ) = 0 then 1
  else (Real.sin (Real.pi * ((N : ℝ) + 1) * θ)
        / (((N : ℝ) + 1) * Real.sin (Real.pi * θ))) ^ 2

def dyadBaseHat (l : ℕ) (θ : ℝ) : ℂ := if l = 0 then 1 else fejerPoly (2 ^ l) θ

def dyadMult (l : ℕ) (θ : ℝ) : ℂ := dyadBaseHat l θ - dyadBaseHat (l + 1) θ

def dyadBaseR (l : ℕ) (θ : ℝ) : ℝ := if l = 0 then 1 else fejerWin (2 ^ l) θ

def dyadMultR (l : ℕ) (θ : ℝ) : ℝ := dyadBaseR l θ - dyadBaseR (l + 1) θ

lemma fejerCoeff_nonneg (N : ℕ) (n : ℤ) : 0 ≤ fejerCoeff N n := by
  unfold fejerCoeff; positivity

lemma fejerCoeff_le (N : ℕ) (n : ℤ) : fejerCoeff N n ≤ ((N : ℝ) + 1)⁻¹ := by
  unfold fejerCoeff
  have hmax : max 0 (1 - |(n : ℝ)| / ((N : ℝ) + 1)) ≤ 1 := by
    apply max_le zero_le_one
    have : 0 ≤ |(n : ℝ)| / ((N : ℝ) + 1) := by positivity
    linarith
  calc ((N : ℝ) + 1)⁻¹ * max 0 (1 - |(n : ℝ)| / ((N : ℝ) + 1))
      ≤ ((N : ℝ) + 1)⁻¹ * 1 := mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = ((N : ℝ) + 1)⁻¹ := mul_one _

lemma fejerCoeff_eq_zero_of_lt_natAbs {N : ℕ} {n : ℤ} (h : N < n.natAbs) :
    fejerCoeff N n = 0 := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hcast : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hle : ((N : ℝ) + 1) ≤ |(n : ℝ)| := by
    have h1 : (N + 1 : ℕ) ≤ n.natAbs := Nat.succ_le_of_lt h
    have h2 : ((N : ℝ) + 1) ≤ (n.natAbs : ℝ) := by
      have : ((N + 1 : ℕ) : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast h1
      push_cast at this
      linarith
    rwa [hcast] at h2
  unfold fejerCoeff
  have hneg : 1 - |(n : ℝ)| / ((N : ℝ) + 1) ≤ 0 := by
    have h2 : (1 : ℝ) ≤ |(n : ℝ)| / ((N : ℝ) + 1) :=
      (le_div_iff₀ hN).mpr (by linarith)
    linarith
  rw [max_eq_left hneg, mul_zero]

lemma fejerCoeff_neg (N : ℕ) (n : ℤ) : fejerCoeff N (-n) = fejerCoeff N n := by
  unfold fejerCoeff
  rw [Int.cast_neg, abs_neg]

lemma dyadBase_even (l : ℕ) (n : ℤ) : dyadBase l (-n) = dyadBase l n := by
  unfold dyadBase
  by_cases hl : l = 0
  · subst hl
    by_cases hn : n = 0
    · subst hn; simp
    · have hn' : ¬ (-n) = 0 := by simpa [neg_eq_zero] using hn
      rw [if_neg hn', if_neg hn, fejerCoeff_neg]
  · rw [if_neg hl, if_neg hl, fejerCoeff_neg]

lemma dyadK_even (l : ℕ) (n : ℤ) : dyadK l (-n) = dyadK l n := by
  unfold dyadK
  rw [dyadBase_even, dyadBase_even]

lemma dyadBase_support {l : ℕ} {n : ℤ} (h : 2 ^ l < n.natAbs) : dyadBase l n = 0 := by
  unfold dyadBase
  by_cases hl : l = 0
  · subst hl
    have h2 : (1 : ℕ) < n.natAbs := by simpa using h
    have hne : n ≠ 0 := by intro h0; rw [h0] at h2; simp at h2
    rw [if_pos rfl, if_neg hne]
  · rw [if_neg hl, fejerCoeff_eq_zero_of_lt_natAbs h]
    exact Complex.ofReal_zero

lemma dyadK_support {l : ℕ} {n : ℤ} (h : 2 ^ (l + 1) < n.natAbs) : dyadK l n = 0 := by
  unfold dyadK
  have h1 : 2 ^ l < n.natAbs := by
    have hlt : (2:ℕ) ^ l < 2 ^ (l+1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self l)
    omega
  rw [dyadBase_support h1, dyadBase_support h, sub_self]

lemma dyadBase_support_finite (l : ℕ) : (Function.support (dyadBase l)).Finite := by
  by_cases hl : l = 0
  · subst hl
    refine Set.Finite.subset (s := ({0} : Set ℤ)) (Set.finite_singleton 0) ?_
    intro n hn
    simp only [Function.mem_support] at hn
    rw [Set.mem_singleton_iff]
    by_contra hne
    exact hn (by unfold dyadBase; rw [if_pos rfl, if_neg hne])
  · refine Set.Finite.subset
      (s := (Finset.Icc (-(((2 ^ l : ℕ) : ℤ))) (((2 ^ l : ℕ) : ℤ)) : Finset ℤ))
      (Finset.finite_toSet _) ?_
    intro n hn
    simp only [Function.mem_support] at hn
    rw [Finset.mem_coe, Finset.mem_Icc]
    have hle : n.natAbs ≤ 2 ^ l := by
      by_contra hc
      simp only [not_le] at hc
      exact hn (dyadBase_support hc)
    have h2 : (n.natAbs : ℤ) ≤ ((2 ^ l : ℕ) : ℤ) := by exact_mod_cast hle
    constructor
    · have h1 : -n ≤ (n.natAbs : ℤ) := by
        have h0 := Int.le_natAbs (a := -n)
        rwa [Int.natAbs_neg] at h0
      omega
    · have h1 : n ≤ (n.natAbs : ℤ) := Int.le_natAbs
      omega

lemma dyadK_support_finite (l : ℕ) : (Function.support (dyadK l)).Finite := by
  refine Set.Finite.subset ((dyadBase_support_finite l).union (dyadBase_support_finite (l+1))) ?_
  intro n hn
  rw [Function.mem_support] at hn
  rw [Set.mem_union, Function.mem_support, Function.mem_support]
  by_contra hc
  simp only [not_or, not_not] at hc
  exact hn (by unfold dyadK; rw [hc.1, hc.2, sub_self])

end
end Work.Analysis.Fourier
