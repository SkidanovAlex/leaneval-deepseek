/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Tools.dualFn_supportIn

/-!
# The duality bound `N₀ ‖Λ‖ ≤ ∑_z ‖F₂ z‖`

This module proves the elementary duality step that turns a lower bound for the *multilinear*
average `Λ^{N₀,N}_{X,P}(f₀,f₁,f₂)` of Peluse's §3 into a lower bound for the `ℓ¹`-norm of the
*dual function* `F₂ = dualFn N P f₀ f₁` of her Corollary 3.8.

The identity behind it is a change of variables.  With `p_y = P.eval y`,

`Λ = (N₀ N)⁻¹ ∑_x f₀ x ∑_{y∈[N]} f₁ (x+y) f₂ (x+p_y)`

and substituting `x = z - p_y` in the (finite, because `f₀`) `x`-sum for each `y` gives

`N₀ Λ = (N)⁻¹ ∑_{y∈[N]} ∑_z f₀ (z-p_y) f₁ (z+y-p_y) f₂ z
     = ∑_z F₂(z) f₂ z ,`

`F₂(z) = (N)⁻¹ ∑_{y∈[N]} f₀ (z-p_y) f₁ (z+y-p_y)`.  Since `‖f₂‖ ≤ 1`, the triangle inequality then
gives `N₀ ‖Λ‖ ≤ ∑_z ‖F₂ z‖`.

Everything is a finite sum (`f₀, f₁, f₂` are supported in `[-N₀,N₀]`, and `F₂` in
`[-dSup P N₀ N, dSup P N₀ N]`), so no summability of any of the functions is required, and the
`tsum`s are rewritten with `tsum_eq_sum`.

## Main result

* `Work.Peluse.Crux.dualFn_tsum_norm_ge`.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Crux

noncomputable section

/-! ## Elementary support and reindexing lemmas -/

/-- Membership in the symmetric interval `[-N,N]`, in terms of `Int.natAbs`. -/
private lemma mem_symIcc_iff {N : ℕ} {x : ℤ} : x ∈ Work.Peluse.symIcc N ↔ x.natAbs ≤ N := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · intro h
    have h1 : |x| ≤ (N : ℤ) := abs_le.mpr h
    rw [← Int.natCast_natAbs] at h1
    exact_mod_cast h1
  · intro hx
    have h1 : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hx
    rw [Int.natCast_natAbs] at h1
    exact abs_le.mp h1

/-- The left end of the support box: `N₀ ≤ dSup P N₀ N`. -/
private lemma le_dSup_left (P : Polynomial ℤ) (N₀ N : ℕ) : N₀ ≤ Work.Peluse.dSup P N₀ N := by
  rw [Work.Peluse.dSup]
  exact Nat.le_add_right _ _

/-- Change of variables for an unconditional sum over `ℤ`: translating the argument by `p` is a
bijection of `ℤ`, so `∑' x, G (x + p) = ∑' x, G x`. -/
private lemma tsum_shift (G : ℤ → ℂ) (p : ℤ) : (∑' x : ℤ, G (x + p)) = ∑' x : ℤ, G x := by
  simpa [Equiv.coe_addRight] using Equiv.tsum_eq (Equiv.addRight p) G

/-- Shifting the argument of a finitely supported function does not change its sum over a finite
interval containing the support:

`∑_{x ∈ S} G (x + p) = ∑_{z ∈ S} G z`

whenever `G` vanishes off `S` and off `S + p` (i.e. `G z = 0` as soon as `z - p ∉ S`).

This is the finite-sum form of the change of variables `z = x + p`, valid because the sums extend
to unconditional sums over `ℤ` (both vanish outside `S`). -/
private lemma sum_shift_of_support {S : Finset ℤ} {G : ℤ → ℂ} {p : ℤ}
    (hA : ∀ z, z ∉ S → G z = 0) (hB : ∀ z, z - p ∉ S → G z = 0) :
    ∑ x ∈ S, G (x + p) = ∑ z ∈ S, G z := by
  have h1 : (∑' x : ℤ, G (x + p)) = ∑ z ∈ S, G z := by
    rw [tsum_shift G p]
    exact tsum_eq_sum (s := S) hA
  rw [← h1]
  exact (tsum_eq_sum (s := S) (fun x hx => hB (x + p) (by simpa using hx))).symm

/-! ## The support of `F₂` -/

/-- `F₂ = dualFn N P f₀ f₁` vanishes outside the box `[-dSup P N₀ N, dSup P N₀ N]`, whenever `f₀`
is supported in `[-N₀,N₀]`: this is `Tools.dualFn_supportIn`, without the (unused) hypothesis
`N ≤ N₀`. -/
private lemma dualFn_eq_zero_of_not_mem {N₀ N : ℕ} (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (hs0 : Work.Peluse.SupportIn f₀ N₀) {z : ℤ}
    (hz : z ∉ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N)) :
    Work.Peluse.dualFn N P f₀ f₁ z = 0 := by
  have hzlt : Work.Peluse.dSup P N₀ N < z.natAbs := by
    by_contra h
    exact hz (mem_symIcc_iff.mpr (le_of_not_gt h))
  have hzabs : ((Work.Peluse.dSup P N₀ N : ℕ) : ℤ) < |z| := by
    rw [← Int.natCast_natAbs z]
    exact_mod_cast hzlt
  have hzabs' : ((N₀ : ℕ) : ℤ) + ((Work.Peluse.polySup P N : ℕ) : ℤ) < |z| := by
    rw [Work.Peluse.dSup, Nat.cast_add] at hzabs
    exact hzabs
  simp only [Work.Peluse.dualFn]
  rw [Finset.sum_eq_zero (fun y hy => ?_), mul_zero]
  obtain ⟨-, hy2⟩ := Finset.mem_Icc.mp hy
  have hPy : |P.eval ((y : ℕ) : ℤ)| ≤ ((Work.Peluse.polySup P N : ℕ) : ℤ) :=
    Work.Peluse.Tools.eval_abs_le_polySup P (by positivity) (by exact_mod_cast hy2)
  have hlt : (N₀ : ℤ) < |z - P.eval ((y : ℕ) : ℤ)| := by
    have := abs_sub_abs_le_abs_sub z (P.eval ((y : ℕ) : ℤ))
    linarith
  have hnat : N₀ < (z - P.eval ((y : ℕ) : ℤ)).natAbs := by
    have hc : (N₀ : ℤ) < (((z - P.eval ((y : ℕ) : ℤ)).natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hlt
    exact_mod_cast hc
  rw [hs0 _ hnat, zero_mul]

/-! ## The duality identity -/

/-- **The duality identity.**  `N₀ Λ^{N₀,N}_{X,P}(f₀,f₁,f₂) = ∑_z F₂(z) f₂(z)`, where
`F₂ = dualFn N P f₀ f₁`: the `x`-sum in `Λ` is reindexed by `x = z - P(y)` for each `y`. -/
private lemma mul_lambdaZ_eq_tsum_dualFn {N₀ N : ℕ} (hN₀ : 1 ≤ N₀) (_hN : 1 ≤ N) (P : Polynomial ℤ)
    (f₀ f₁ f₂ : ℤ → ℂ) (hs0 : Work.Peluse.SupportIn f₀ N₀)
    (_hs1 : Work.Peluse.SupportIn f₁ N₀) (hs2 : Work.Peluse.SupportIn f₂ N₀) :
    (N₀ : ℂ) * Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂
      = ∑' z : ℤ, Work.Peluse.dualFn N P f₀ f₁ z * f₂ z := by
  have hSx : ∀ x : ℤ, x ∉ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N) → f₀ x = 0 := by
    intro x hx
    have hxlt : Work.Peluse.dSup P N₀ N < x.natAbs := by
      by_contra h
      exact hx (mem_symIcc_iff.mpr (le_of_not_gt h))
    exact hs0 x (lt_of_le_of_lt (le_dSup_left P N₀ N) hxlt)
  have hSc : ∀ z : ℤ, z ∉ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N) →
      Work.Peluse.dualFn N P f₀ f₁ z = 0 :=
    fun z hz => dualFn_eq_zero_of_not_mem P f₀ f₁ hs0 hz
  have hcoef : (N₀ : ℂ) * (((N₀ : ℂ) * (N : ℂ))⁻¹) = ((N : ℂ))⁻¹ := by
    have h0 : (N₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : N₀ ≠ 0)
    field_simp
  have hts : (∑' x : ℤ, f₀ x * ∑ y ∈ Finset.Icc 1 N,
        f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ)))
      = ∑ x ∈ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N), f₀ x * ∑ y ∈ Finset.Icc 1 N,
        f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ)) := by
    rw [tsum_eq_sum (s := Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N))]
    intro x hx
    rw [hSx x hx, zero_mul]
  have hA : (N₀ : ℂ) * Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂
      = (N : ℂ)⁻¹ * ∑ y ∈ Finset.Icc 1 N,
          ∑ x ∈ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N),
            f₀ x * f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ)) := by
    simp only [Work.Peluse.LambdaZ]
    rw [hts, ← mul_assoc, hcoef]
    congr 1
    trans ∑ x ∈ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N), ∑ y ∈ Finset.Icc 1 N,
        f₀ x * (f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ)))
    · apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      ring
  have hB : (∑' z : ℤ, Work.Peluse.dualFn N P f₀ f₁ z * f₂ z)
      = (N : ℂ)⁻¹ * ∑ y ∈ Finset.Icc 1 N,
          ∑ x ∈ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N),
            f₀ x * f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ)) := by
    have hz : (∑' z : ℤ, Work.Peluse.dualFn N P f₀ f₁ z * f₂ z)
        = ∑ z ∈ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N),
            Work.Peluse.dualFn N P f₀ f₁ z * f₂ z := by
      rw [tsum_eq_sum (s := Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N))]
      intro z hz
      rw [hSc z hz, zero_mul]
    rw [hz]
    trans (N : ℂ)⁻¹ * ∑ z ∈ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N),
        ∑ y ∈ Finset.Icc 1 N,
          (f₀ (z - P.eval (y : ℤ)) * f₁ (z + (y : ℤ) - P.eval (y : ℤ))) * f₂ z
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      simp only [Work.Peluse.dualFn]
      rw [mul_assoc, Finset.sum_mul]
    · congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      set p : ℤ := P.eval (y : ℤ) with hp
      have hA' : ∀ z : ℤ, z ∉ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N) →
          (f₀ (z - p) * f₁ (z + (y : ℤ) - p)) * f₂ z = 0 := by
        intro z hz'
        have hzlt : Work.Peluse.dSup P N₀ N < z.natAbs := by
          by_contra h
          exact hz' (mem_symIcc_iff.mpr (le_of_not_gt h))
        rw [hs2 z (lt_of_le_of_lt (le_dSup_left P N₀ N) hzlt), mul_zero]
      have hB' : ∀ z : ℤ, z - p ∉ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N) →
          (f₀ (z - p) * f₁ (z + (y : ℤ) - p)) * f₂ z = 0 := by
        intro z hz'
        have hzlt : Work.Peluse.dSup P N₀ N < (z - p).natAbs := by
          by_contra h
          exact hz' (mem_symIcc_iff.mpr (le_of_not_gt h))
        have h0 : f₀ (z - p) = 0 :=
          hs0 _ (lt_of_le_of_lt (le_dSup_left P N₀ N) hzlt)
        rw [h0, zero_mul, zero_mul]
      rw [← sum_shift_of_support (S := Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N))
        (G := fun z => (f₀ (z - p) * f₁ (z + (y : ℤ) - p)) * f₂ z) (p := p) hA' hB']
      apply Finset.sum_congr rfl
      intro x _
      have h1 : x + p - p = x := by ring
      have h2 : x + p + (y : ℤ) - p = x + (y : ℤ) := by ring
      rw [h1, h2]
  exact hA.trans hB.symm

/-! ## The main theorem -/

theorem dualFn_tsum_norm_ge {N₀ N : ℕ} (hN₀ : 1 ≤ N₀) (hN : 1 ≤ N) (P : Polynomial ℤ) (f₀ f₁ f₂ : ℤ → ℂ) (δ : ℝ)
    (hs0 : Work.Peluse.SupportIn f₀ N₀) (hs1 : Work.Peluse.SupportIn f₁ N₀) (hs2 : Work.Peluse.SupportIn f₂ N₀)
    (hb2 : ∀ x : ℤ, ‖f₂ x‖ ≤ 1)
    (hmain : δ * (N : ℝ) ^ P.natDegree ≤ ‖Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂‖ * (N₀ : ℝ)) :
    δ * (N : ℝ) ^ P.natDegree ≤ ∑' z : ℤ, ‖Work.Peluse.dualFn N P f₀ f₁ z‖ := by
  have hid := mul_lambdaZ_eq_tsum_dualFn hN₀ hN P f₀ f₁ f₂ hs0 hs1 hs2
  have hSd : ∀ z : ℤ, z ∉ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N) →
      Work.Peluse.dualFn N P f₀ f₁ z * f₂ z = 0 := by
    intro z hz
    rw [dualFn_eq_zero_of_not_mem P f₀ f₁ hs0 hz, zero_mul]
  have hSd' : ∀ z : ℤ, z ∉ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N) →
      ‖Work.Peluse.dualFn N P f₀ f₁ z‖ = 0 := by
    intro z hz
    rw [dualFn_eq_zero_of_not_mem P f₀ f₁ hs0 hz, norm_zero]
  calc δ * (N : ℝ) ^ P.natDegree
      ≤ ‖Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂‖ * (N₀ : ℝ) := hmain
    _ = ‖(N₀ : ℂ) * Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂‖ := by
        rw [norm_mul, Complex.norm_natCast]
        ring
    _ = ‖∑' z : ℤ, Work.Peluse.dualFn N P f₀ f₁ z * f₂ z‖ := by rw [hid]
    _ = ‖∑ z ∈ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N),
          Work.Peluse.dualFn N P f₀ f₁ z * f₂ z‖ := by
        rw [tsum_eq_sum (s := Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N)) hSd]
    _ ≤ ∑ z ∈ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N),
          ‖Work.Peluse.dualFn N P f₀ f₁ z * f₂ z‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N),
          ‖Work.Peluse.dualFn N P f₀ f₁ z‖ := by
        apply Finset.sum_le_sum
        intro z _
        calc ‖Work.Peluse.dualFn N P f₀ f₁ z * f₂ z‖
            = ‖Work.Peluse.dualFn N P f₀ f₁ z‖ * ‖f₂ z‖ := norm_mul _ _
          _ ≤ ‖Work.Peluse.dualFn N P f₀ f₁ z‖ * 1 :=
              mul_le_mul_of_nonneg_left (hb2 z) (norm_nonneg _)
          _ = ‖Work.Peluse.dualFn N P f₀ f₁ z‖ := mul_one _
    _ = ∑' z : ℤ, ‖Work.Peluse.dualFn N P f₀ f₁ z‖ := by
        rw [tsum_eq_sum (s := Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N)) hSd']

end

end Work.Peluse.Crux
