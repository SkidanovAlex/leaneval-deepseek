/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.BoxNorm.boxNormPow_le_one
import Submission.Work.Peluse.Tools.dualFn_supportIn

/-!
# `Work.Peluse.ulowering_of`: elementary infrastructure

Facts about the Gowers box norm and the dual function `dualFn` used by the proof of
`Work.Peluse.PeluseULowering` (Peluse, Lemmas 3.9 + 2.4 + 3.10 and §9) before the two deep inputs
(`PeluseU2Inverse`, `PeluseMajorArc`) enter.

* `boxSumPow_scale` / `boxNormPow_eq_mul_card` : changing the support box `S` in the box norm only
  changes the normalising factor `|S|⁻¹`;
* `boxSumPow_smul` / `boxNormPow_smul` : the box norm is homogeneous of degree `2^t`,
  `‖c·f‖_{□} = ‖c‖^{2^t}‖f‖_{□}` (used to compare `dualFn N` with its truncation);
* `boxNormPow_le_of_bound` : `‖f‖_{□^t_{Q}(S)}^{2^t} ≤ M^{2^t}` when `‖f‖ ≤ M` and `f` vanishes
  off `S`.  In the situation of `PeluseULowering` (support box `symIcc (dSup P N₀ N)`, which
  contains the support of `F₂` by `dualFn_supportIn`) this says `δ ≤ ‖F₂‖_∞^{2^s}`;
* `dualFn_trunc` : `dualFn N P f₀ f₁ = (N''/N) • dualFn N'' P f₀ f₁` with `N'' = min N (2N₀)`
  when `f₀, f₁` are supported in `[-N₀,N₀]`, because `y = (x + y - P y) - (x - P y)`.  This is the
  reduction of the scale imbalance `N₀ ≤ A' N^d` of `PeluseULowering` to the balanced situation
  `N₀ ≍ N^d` of Peluse's Lemma 3.9.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## The support box enters the box sum only through `|S|⁻¹` -/

/-- The inner sum over `x` in `prodCubeSum` does not mention `S`, so changing the box `S` only
multiplies the box sum by a ratio of cardinalities.  Stated without inverses. -/
theorem boxSumPow_scale (t : ℕ) (Q : Fin t → Finset ℤ) (S S' : Finset ℤ) (f : ℤ → ℂ)
    (hS' : S'.Nonempty) :
    boxSumPow t Q S f = ((S.card : ℂ))⁻¹ * (S'.card : ℂ) * boxSumPow t Q S' f := by
  have hb : (S'.card : ℂ) ≠ 0 := by
    have h := Finset.card_ne_zero.mpr hS'
    simpa using h
  rw [boxSumPow, prodCubeSum_eq, boxSumPow, prodCubeSum_eq]
  field_simp

/-- The same relation for the box *norm*: changing `S` to `S'` multiplies by `|S'|/|S|`. -/
theorem boxNormPow_eq_mul_card (t : ℕ) (Q : Fin t → Finset ℤ) (S S' : Finset ℤ) (f : ℤ → ℂ)
    (hS' : S'.Nonempty) :
    boxNormPow t Q S f = ((S'.card : ℝ) / (S.card : ℝ)) * boxNormPow t Q S' f := by
  have h := boxSumPow_scale t Q S S' f hS'
  have hnorm : ‖((S.card : ℂ))⁻¹‖ = ((S.card : ℝ))⁻¹ := by
    rw [norm_inv]; simp
  rw [boxNormPow, h, norm_mul, norm_mul, boxNormPow, hnorm]
  simp only [Complex.norm_natCast]
  ring

/-! ## Homogeneity of the box sum -/

/-- Iterates of `star` are multiplicative. -/
lemma starIterate_mul (n : ℕ) (a b : ℂ) :
    (star^[n]) (a * b) = (star^[n]) a * (star^[n]) b := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
        Function.iterate_succ_apply', star_mul]
      ring

/-- Iterates of `star` preserve the norm. -/
lemma norm_starIterate (n : ℕ) (z : ℂ) : ‖(star^[n]) z‖ = ‖z‖ := by
  induction n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', norm_star, ih]

/-- **Homogeneity.**  Scaling `f` by a complex number `c` multiplies the box sum by the constant
`∏_{ω}(star^[|ω|]) c` (whose modulus is `‖c‖^{2^t}`). -/
theorem boxSumPow_smul (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (c : ℂ) (f : ℤ → ℂ) :
    boxSumPow t Q S (fun x => c * f x) =
      (∏ ω : Fin t → Bool, (star^[weight ω]) c) * boxSumPow t Q S f := by
  set lam : ℂ := ∏ ω : Fin t → Bool, (star^[weight ω]) c with hlam
  have hpt : ∀ (h h' : (i : Fin t) → {x : ℤ // x ∈ Q i}) (x : ℤ),
      (∏ ω : Fin t → Bool, (star^[weight ω])
          (c * f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))
        = lam * (∏ ω : Fin t → Bool, (star^[weight ω])
          (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) := by
    intro h h' x
    have h1 : (∏ ω : Fin t → Bool, (star^[weight ω])
        (c * f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))
        = ∏ ω : Fin t → Bool, ((star^[weight ω]) c *
            (star^[weight ω]) (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) :=
      Finset.prod_congr rfl (fun ω _ => starIterate_mul _ _ _)
    rw [h1, Finset.prod_mul_distrib, hlam]
  have hsum : (∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
          (c * f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))
      = lam * (∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
          (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h' _ => ?_)
    calc ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
          (c * f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))
        = ∑' x : ℤ, lam * (∏ ω : Fin t → Bool, (star^[weight ω])
          (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) :=
          tsum_congr (fun x => hpt h h' x)
      _ = lam * (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
          (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) := tsum_mul_left
  simp only [boxSumPow, prodCubeSum]
  rw [hsum]
  ring

/-- **Homogeneity of the box norm**: `‖c·f‖_{□^t_Q(S)}^{2^t} = ‖c‖^{2^t}‖f‖_{□^t_Q(S)}^{2^t}`. -/
theorem boxNormPow_smul (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (c : ℂ) (f : ℤ → ℂ) :
    boxNormPow t Q S (fun x => c * f x) = ‖c‖ ^ (2 ^ t) * boxNormPow t Q S f := by
  rw [boxNormPow, boxSumPow_smul, boxNormPow, norm_mul]
  congr 1
  rw [norm_prod]
  calc ∏ ω : Fin t → Bool, ‖(star^[weight ω]) c‖
      = ∏ _ω : Fin t → Bool, ‖c‖ := Finset.prod_congr rfl (fun ω _ => norm_starIterate _ _)
    _ = ‖c‖ ^ (2 ^ t) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun]
        simp

/-! ## The box norm is bounded by the sup norm -/

/-- **The box norm is at most `M^{2^t}`** when `‖f‖ ≤ M` and `f` vanishes off `S`. -/
theorem boxNormPow_le_of_bound {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) {f : ℤ → ℂ}
    {M : ℝ} (hM : 0 ≤ M) (hbd : ∀ x : ℤ, ‖f x‖ ≤ M) (hsupp : ∀ x : ℤ, x ∉ S → f x = 0) :
    boxNormPow t Q S f ≤ M ^ (2 ^ t) := by
  rcases eq_or_lt_of_le hM with hzero | hpos
  · have hf0 : f = 0 := by
      funext x
      have hx := hbd x
      rw [← hzero] at hx
      exact norm_eq_zero.mp (le_antisymm hx (norm_nonneg _))
    have h0 : boxNormPow t Q S (fun _ : ℤ => (0 : ℂ)) = 0 := by
      have h := boxNormPow_smul t Q S (0 : ℂ) f
      simpa using h
    have hz : (0 : ℝ) ^ (2 ^ t) = 0 := zero_pow (by positivity)
    rw [hf0, ← hzero]
    change boxNormPow t Q S (fun _ : ℤ => (0 : ℂ)) ≤ (0 : ℝ) ^ (2 ^ t)
    rw [h0, hz]
  · have hnorm : ‖((M : ℂ))⁻¹‖ = M⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hM]
    have hg : ∀ x : ℤ, ‖((M : ℂ))⁻¹ * f x‖ ≤ 1 := by
      intro x
      rw [norm_mul, hnorm]
      exact (inv_mul_le_one₀ hpos).mpr (hbd x)
    have hgs : ∀ x : ℤ, x ∉ S → ((M : ℂ))⁻¹ * f x = 0 := fun x hx => by
      rw [hsupp x hx, mul_zero]
    have h1 := Work.Peluse.BoxNorm.boxNormPow_le_one (t := t) (Q := Q) (S := S) hg hgs
    rw [boxNormPow_smul, hnorm] at h1
    have h2 : boxNormPow t Q S f ≤ 1 / (M⁻¹) ^ (2 ^ t) := by
      rw [le_div_iff₀ (by positivity)]
      simpa [mul_comm] using h1
    rwa [one_div, inv_pow, inv_inv] at h2

/-! ## Truncating the `y`-sum of the dual function -/

/-- **The dual function only sees `y ≤ 2N₀`.**  If `f₀, f₁` are supported in `[-N₀,N₀]` then the
summand of `dualFn N P f₀ f₁ x` vanishes for `2N₀ < y`, since
`y = (x + y - P y) - (x - P y)` is a difference of two values in the supports. -/
theorem dualFn_trunc {Ns N : ℕ} (hN : 1 ≤ N) (hNs : 1 ≤ Ns) (P : Polynomial ℤ)
    (f₀ f₁ : ℤ → ℂ) (h0 : SupportIn f₀ Ns) (h1 : SupportIn f₁ Ns) :
    dualFn N P f₀ f₁ =
      fun x => (((min N (2 * Ns) : ℕ) : ℂ)) * ((N : ℂ))⁻¹ *
        dualFn (min N (2 * Ns)) P f₀ f₁ x := by
  have hmin : 1 ≤ min N (2 * Ns) := le_min hN (by omega)
  funext x
  have hsub : Finset.Icc 1 (min N (2 * Ns)) ⊆ Finset.Icc 1 N := by
    intro y hy
    simp only [Finset.mem_Icc] at hy ⊢
    exact ⟨hy.1, le_trans hy.2 (min_le_left _ _)⟩
  have hvanish : ∀ y ∈ Finset.Icc 1 N, y ∉ Finset.Icc 1 (min N (2 * Ns)) →
      f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ)) = 0 := by
    intro y hy hy2
    have hyN : y ≤ N := (Finset.mem_Icc.mp hy).2
    have hygt : min N (2 * Ns) < y := by
      by_contra hcon
      push_neg at hcon
      exact hy2 (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hy).1, hcon⟩)
    have hy2Ns : 2 * Ns < y := by
      by_contra hcon
      push_neg at hcon
      exact absurd hygt (not_lt.mpr (le_min hyN hcon))
    by_contra hne
    have hb0 : f₀ (x - P.eval (y : ℤ)) ≠ 0 := fun hz => hne (by rw [hz, zero_mul])
    have hb1 : f₁ (x + (y : ℤ) - P.eval (y : ℤ)) ≠ 0 := fun hz => hne (by rw [hz, mul_zero])
    have hA : |x - P.eval (y : ℤ)| ≤ (Ns : ℤ) := by
      have hle : (x - P.eval (y : ℤ)).natAbs ≤ Ns := by
        by_contra hc
        exact hb0 (h0 _ (Nat.lt_of_not_le hc))
      have hle' : (((x - P.eval (y : ℤ)).natAbs : ℕ) : ℤ) ≤ ((Ns : ℕ) : ℤ) := by
        exact_mod_cast hle
      rwa [Int.natCast_natAbs] at hle'
    have hB : |x + (y : ℤ) - P.eval (y : ℤ)| ≤ (Ns : ℤ) := by
      have hle : (x + (y : ℤ) - P.eval (y : ℤ)).natAbs ≤ Ns := by
        by_contra hc
        exact hb1 (h1 _ (Nat.lt_of_not_le hc))
      have hle' : (((x + (y : ℤ) - P.eval (y : ℤ)).natAbs : ℕ) : ℤ) ≤ ((Ns : ℕ) : ℤ) := by
        exact_mod_cast hle
      rwa [Int.natCast_natAbs] at hle'
    have hdiff : (y : ℤ) = (x + (y : ℤ) - P.eval (y : ℤ)) - (x - P.eval (y : ℤ)) := by ring
    have hyabs : |(y : ℤ)| ≤ 2 * (Ns : ℤ) := by
      rw [hdiff]
      calc |(x + (y : ℤ) - P.eval (y : ℤ)) - (x - P.eval (y : ℤ))|
          ≤ |x + (y : ℤ) - P.eval (y : ℤ)| + |x - P.eval (y : ℤ)| := abs_sub _ _
        _ ≤ (Ns : ℤ) + (Ns : ℤ) := add_le_add hB hA
        _ = 2 * (Ns : ℤ) := by ring
    have : (y : ℤ) ≤ 2 * (Ns : ℤ) := by
      rw [abs_of_nonneg (by positivity : (0:ℤ) ≤ (y:ℤ))] at hyabs
      exact hyabs
    omega
  rw [dualFn, dualFn, Finset.sum_subset hsub hvanish]
  have hmC : (((min N (2 * Ns) : ℕ) : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  field_simp

end

end Work.Peluse.Ulower
