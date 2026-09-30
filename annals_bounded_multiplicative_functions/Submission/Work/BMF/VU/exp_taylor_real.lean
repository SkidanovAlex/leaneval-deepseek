import Mathlib
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.abel_exp_sum
import Submission.Work.BMF.exp_sum_taylor_defs
import Submission.Work.BMF.abel_identity
import Submission.Work.BMF.betaP_hasDerivAt
import Submission.Work.BMF.taylor_remainder_deriv_fixed

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF
open Finset MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable


/-! ### Helpers for the corrected statement -/

private lemma eC_add_esb (x y : ℝ) : eC (x + y) = eC x * eC y := by
  rw [eC, eC, eC, ← Complex.exp_add]; congr 1; push_cast; ring

private lemma norm_eC_esb (t : ℝ) : ‖eC t‖ = 1 := by
  rw [eC, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

private lemma norm_eC_sub_le_two_pi (u v : ℝ) : ‖eC u - eC v‖ ≤ 2 * Real.pi * |u - v| := by
  have h1 : eC u - eC v = eC v * (eC (u - v) - 1) := by
    rw [mul_sub, mul_one, ← eC_add_esb, show v + (u - v) = u by ring]
  rw [h1, norm_mul, norm_eC_esb, one_mul]
  have h2 : eC (u - v) = Complex.exp (Complex.I * ((2 * Real.pi * (u - v) : ℝ) : ℂ)) := by
    rw [eC]; congr 1; push_cast; ring
  rw [h2, Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hsin : |Real.sin ((2 * Real.pi * (u - v)) / 2)| ≤ |(2 * Real.pi * (u - v)) / 2| :=
    Real.abs_sin_le_abs
  have habs : |(2 * Real.pi * (u - v)) / 2| = Real.pi * |u - v| := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_mul, abs_mul,
      abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    ring
  rw [habs] at hsin
  nlinarith [hsin]

private lemma taylor_term_le (k : ℕ) (hk : 2 ≤ k) {A lam H y : ℝ} (hH : 0 < H)
    (hAlam : A * lam ≤ H ^ (-(k:ℝ))) (hy : 0 ≤ y) (hyH : y ≤ H) :
    A * lam * y ^ (k - 1) / (Nat.factorial (k - 1) : ℝ) ≤ H⁻¹ := by
  have h1 : A * lam * y ^ (k-1) ≤ H ^ (-(k:ℝ)) * H ^ (k-1) :=
    mul_le_mul hAlam (pow_le_pow_left₀ hy hyH (k-1)) (pow_nonneg hy _)
      (Real.rpow_nonneg (le_of_lt hH) _)
  have hcast : ((k-1:ℕ):ℝ) = (k:ℝ) - 1 := by
    have : 1 ≤ k := by omega
    rw [Nat.cast_sub this]; norm_num
  have hpow : H ^ (-(k:ℝ)) * H ^ (k-1) = H⁻¹ := by
    rw [← Real.rpow_natCast H (k-1), ← Real.rpow_add hH]
    have : -(k:ℝ) + ((k-1:ℕ):ℝ) = -1 := by rw [hcast]; ring
    rw [this, Real.rpow_neg_one]
  rw [hpow] at h1
  refine (div_le_div_of_nonneg_right h1 (by positivity)).trans ?_
  exact div_le_self (inv_nonneg.mpr (le_of_lt hH))
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (k-1)))

private lemma tayP_eq_phase (k : ℕ) (f : ℝ → ℝ) (n : ℝ) (an : Fin (k-1) → ℝ)
    (han : ∀ j : Fin (k-1),
      an j = iteratedDeriv ((j:ℕ)+1) f n / (Nat.factorial ((j:ℕ)+1) : ℝ))
    (h : ℕ) : tayP k f n (h:ℝ) = phase (k-1) an h := by
  rw [tayP, ← Fin.sum_univ_eq_sum_range
    (fun i => iteratedDeriv (i+1) f n * (h:ℝ)^(i+1) / (Nat.factorial (i+1) : ℝ))]
  rw [phase]
  apply Finset.sum_congr rfl
  intro j _
  rw [han j]
  ring

/-- Discrete Abel summation against an exponential weight: the statement of
`Submission.Work.BMF.abel_exp_sum`, proved here inline so that the corrected theorem below does
not import a `sorry`. -/
private lemma abel_bound (L : ℕ) (a : ℕ → ℂ) (β : ℝ → ℝ) (Cβ : ℝ) (hCβnn : 0 ≤ Cβ)
    (hβ : ∀ y ∈ Set.Icc (1:ℝ) L, HasDerivAt β (deriv β y) y)
    (hCβ : ∀ y ∈ Set.Icc (1:ℝ) L, ‖deriv β y‖ ≤ Cβ) :
    ‖∑ h ∈ Finset.Icc 1 L, a h * eC (β h)‖ ≤
      ‖∑ h ∈ Finset.Icc 1 L, a h‖ +
        2 * Real.pi * Cβ * ∑ h ∈ Finset.range L, ‖∑ h' ∈ Finset.Icc 1 h, a h'‖ := by
  rw [abel_identity L a (fun h => eC (β h))]
  have hterm : ∀ h ∈ Finset.range L,
      ‖(∑ h' ∈ Finset.Icc 1 h, a h') * (eC (β ((h + 1 : ℕ) : ℝ)) - eC (β h))‖ ≤
        ‖∑ h' ∈ Finset.Icc 1 h, a h'‖ * (2 * Real.pi * Cβ) := by
    intro h hh
    by_cases h0 : h = 0
    · subst h0
      have hz : Finset.Icc 1 (0:ℕ) = (∅ : Finset ℕ) := by simp
      rw [hz]; simp
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr h0
      have hL : h + 1 ≤ L := by have := Finset.mem_range.mp hh; omega
      have hmem : (h:ℝ) ∈ Set.Icc (1:ℝ) L :=
        ⟨by exact_mod_cast h1, by exact_mod_cast (by omega : h ≤ L)⟩
      have hmem2 : ((h+1:ℕ):ℝ) ∈ Set.Icc (1:ℝ) L := by
        refine ⟨?_, ?_⟩
        · have hc : ((h+1:ℕ):ℝ) = (h:ℝ) + 1 := by push_cast; ring
          rw [hc]; linarith [show (0:ℝ) ≤ (h:ℝ) by positivity]
        · exact_mod_cast hL
      have hmvt : ‖β ((h+1:ℕ):ℝ) - β (h:ℝ)‖ ≤ Cβ * ‖((h+1:ℕ):ℝ) - (h:ℝ)‖ :=
        Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc (1:ℝ) L) (f := β) (C := Cβ)
          (fun x hx => (hβ x hx).differentiableAt) (fun x hx => hCβ x hx)
          (convex_Icc _ _) hmem hmem2
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        show ((h+1:ℕ):ℝ) - (h:ℝ) = 1 by push_cast; ring, abs_one, mul_one] at hmvt
      calc ‖eC (β ((h+1:ℕ):ℝ)) - eC (β (h:ℝ))‖
          ≤ 2 * Real.pi * |β ((h+1:ℕ):ℝ) - β (h:ℝ)| := norm_eC_sub_le_two_pi _ _
        _ ≤ 2 * Real.pi * Cβ := by
            rw [← Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left hmvt (by positivity)
  have hnorm := norm_sum_le (Finset.range L)
    (fun h => (∑ h' ∈ Finset.Icc 1 h, a h') * (eC (β ((h + 1 : ℕ) : ℝ)) - eC (β h)))
  calc ‖(∑ h ∈ Finset.Icc 1 L, a h) * eC (β L) -
        ∑ h ∈ Finset.range L,
          (∑ h' ∈ Finset.Icc 1 h, a h') * (eC (β ((h + 1 : ℕ) : ℝ)) - eC (β h))‖
      ≤ ‖(∑ h ∈ Finset.Icc 1 L, a h) * eC (β L)‖ +
          ‖∑ h ∈ Finset.range L,
            (∑ h' ∈ Finset.Icc 1 h, a h') * (eC (β ((h + 1 : ℕ) : ℝ)) - eC (β h))‖ :=
        norm_sub_le _ _
    _ = ‖∑ h ∈ Finset.Icc 1 L, a h‖ +
          ‖∑ h ∈ Finset.range L,
            (∑ h' ∈ Finset.Icc 1 h, a h') * (eC (β ((h + 1 : ℕ) : ℝ)) - eC (β h))‖ := by
        rw [norm_mul, norm_eC_esb, mul_one]
    _ ≤ ‖∑ h ∈ Finset.Icc 1 L, a h‖ +
          ∑ h ∈ Finset.range L,
            ‖(∑ h' ∈ Finset.Icc 1 h, a h') * (eC (β ((h + 1 : ℕ) : ℝ)) - eC (β h))‖ :=
        add_le_add le_rfl hnorm
    _ ≤ ‖∑ h ∈ Finset.Icc 1 L, a h‖ +
          ∑ h ∈ Finset.range L, ‖∑ h' ∈ Finset.Icc 1 h, a h'‖ * (2 * Real.pi * Cβ) :=
        add_le_add le_rfl (Finset.sum_le_sum hterm)
    _ = ‖∑ h ∈ Finset.Icc 1 L, a h‖ +
          2 * Real.pi * Cβ * ∑ h ∈ Finset.range L, ‖∑ h' ∈ Finset.Icc 1 h, a h'‖ := by
        rw [← Finset.sum_mul]; ring

/-- **Corrected form of `exp_sum_taylor_abel_bound`.**  Identical to the target statement except
that `hder` is quantified over the real interval `(0,N)`, written `Set.Ioo (0:ℝ) (N:ℝ)`; that is
what the statement was meant to say (and what makes it true). -/
theorem exp_sum_taylor_abel_bound_real (k : ℕ) (hk : 2 ≤ k) {N : ℕ} {f : ℝ → ℝ} {A lam H : ℝ}
    (hH : 0 < H) (hAlam : A * lam ≤ H ^ (-(k:ℝ))) (hlam : 0 ≤ A * lam)
    (hf : ContDiffOn ℝ k f (Set.Ioo (0:ℝ) (N:ℝ)))
    (hder : ∀ y ∈ Set.Ioo (0:ℝ) (N:ℝ), ‖iteratedDeriv k f y‖ ≤ A * lam)
    {L n : ℕ} (hn : 1 ≤ n) (hnL : n + L < N) (hLH : (L:ℝ) ≤ H) :
    ‖∑ h ∈ Finset.Icc 1 L, eC (f ((n + h : ℕ) : ℝ))‖ ≤
      ‖polySum (k-1) (fun j : Fin (k-1) => iteratedDeriv ((j:ℕ)+1) f (n : ℝ)
          / (Nat.factorial ((j:ℕ)+1) : ℝ)) (L : ℝ)‖
      + 2 * Real.pi * H⁻¹ * ∑ h ∈ Finset.range L,
          ‖polySum (k-1) (fun j : Fin (k-1) => iteratedDeriv ((j:ℕ)+1) f (n : ℝ)
            / (Nat.factorial ((j:ℕ)+1) : ℝ)) (h : ℝ)‖ := by
  set an : Fin (k-1) → ℝ :=
    fun j => iteratedDeriv ((j:ℕ)+1) f (n:ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ) with han
  have haneq : ∀ j : Fin (k-1),
      an j = iteratedDeriv ((j:ℕ)+1) f (n:ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ) := by
    intro j; rw [han]
  -- the chain-rule hypotheses for `abel_bound`
  have hbet : ∀ y ∈ Set.Icc (1:ℝ) L,
      HasDerivAt (betaP k f (n:ℝ)) (deriv (betaP k f (n:ℝ)) y) y := by
    intro y hy
    have hb := Work.BMF.betaP_hasDerivAt k hk hf hn hnL hy
    rw [hb.deriv]; exact hb
  have hbnd : ∀ y ∈ Set.Icc (1:ℝ) L, ‖deriv (betaP k f (n:ℝ)) y‖ ≤ H⁻¹ := by
    intro y hy
    have hy0 : 0 ≤ y := le_trans (by norm_num) hy.1
    have hyH : y ≤ H := le_trans hy.2 hLH
    have hb := Work.BMF.betaP_hasDerivAt k hk hf hn hnL hy
    have hx0 : 0 < (n:ℝ) := by exact_mod_cast hn
    have hxle : (n:ℝ) ≤ (n:ℝ) + y := by linarith
    have hxN : (n:ℝ) + y < (N:ℝ) := by
      have h2 : (n:ℝ) + (L:ℝ) < (N:ℝ) := by exact_mod_cast hnL
      linarith [hy.2]
    have hT := Work.BMF.taylor_remainder_deriv_fixed k hk hf hder hx0 hxle hxN
    rw [show (n:ℝ) + y - (n:ℝ) = y by ring] at hT
    rw [hb.deriv]
    exact hT.trans (taylor_term_le k hk hH hAlam hy0 hyH)
  -- identify the summand
  have hkey : ∑ h ∈ Finset.Icc 1 L, eC (f ((n + h : ℕ) : ℝ)) =
      ∑ h ∈ Finset.Icc 1 L, eC (phase (k-1) an h) * eC (betaP k f (n:ℝ) h) := by
    apply Finset.sum_congr rfl
    intro h _
    rw [← eC_add_esb]
    congr 1
    rw [betaP_apply, tayP_eq_phase k f (n:ℝ) an haneq h,
      show ((n + h : ℕ) : ℝ) = (n:ℝ) + (h:ℝ) by push_cast; ring]
    ring
  rw [hkey]
  refine (abel_bound L (fun h => eC (phase (k-1) an h)) (betaP k f (n:ℝ)) H⁻¹
      (inv_nonneg.mpr (le_of_lt hH)) hbet hbnd).trans ?_
  have hL : ‖∑ h ∈ Finset.Icc 1 L, eC (phase (k-1) an h)‖ = ‖polySum (k-1) an (L:ℝ)‖ := by
    rw [polySum]
    norm_num only [Nat.floor_natCast]
  have hR : ∀ h : ℕ, ‖∑ h' ∈ Finset.Icc 1 h, eC (phase (k-1) an h')‖ =
      ‖polySum (k-1) an (h:ℝ)‖ := by
    intro h
    rw [polySum]
    norm_num only [Nat.floor_natCast]
  rw [hL]
  refine add_le_add le_rfl ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro h _
  rw [hR h]

end Work.BMF
