import Mathlib

/-!
# `Submission.Helpers`

Bridging and structural lemmas for the statement of
`Submission.cdt_linearIndependent` (Theorems A & C of Calegari–Dimitrov–Tang,
*The linear independence of 1, ζ(2), and L(2, χ₋₃)*, arXiv:2408.15403).

Theorems A and C are deep 2024 Diophantine results (arithmetic holonomy
bounds); none of their substance is present in the pinned Mathlib.  This module
records *verified* infrastructure that connects Mathlib's analytic objects to
the classical ones of the paper and isolates the two deep claims (see the
comments at the bottom of `Submission.lean`).
-/

namespace Submission.Helpers

open Complex
open scoped BigOperators

noncomputable section

/-! ### The character `χ₋₃` modulo 3 -/

/-- The nontrivial Dirichlet character mod `3` (`χ₋₃`), as a complex-valued
function on `ZMod 3` (which is definitionally `Fin 3`). -/
def chi3 : ZMod 3 → ℂ := ![0, 1, -1]

@[simp] lemma chi3_apply_zero : chi3 0 = 0 := rfl
@[simp] lemma chi3_apply_one : chi3 1 = 1 := rfl
@[simp] lemma chi3_apply_two : chi3 2 = -1 := rfl

/-- Pointwise value of a length-3 vector, determined by the index value. -/
lemma vec3_apply {α : Type*} (a b c : α) (x : Fin 3) :
    (![a, b, c] : Fin 3 → α) x = if x.val = 0 then a else if x.val = 1 then b else c := by
  fin_cases x <;> simp

/-- For `n : ℕ`, `chi3 (n : ZMod 3)` equals `1`, `-1`, or `0` according as
`n ≡ 1, 2, 0 (mod 3)`. -/
lemma chi3_apply_nat_mod (n : ℕ) :
    chi3 (n : ZMod 3) =
      if n % 3 = 1 then (1 : ℂ) else if n % 3 = 2 then -1 else 0 := by
  have hmod : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h0 | h1 | h2
  · have hx : (n : ZMod 3) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_iff_mod_eq_zero.mpr h0
    simp [hx, h0]
  · have hx : (n : ZMod 3) = 1 :=
      (ZMod.natCast_eq_natCast_iff' n 1 3).mpr (by simp [h1])
    simp [hx, h1]
  · have hx : (n : ZMod 3) = 2 :=
      (ZMod.natCast_eq_natCast_iff' n 2 3).mpr (by simp [h2])
    have hn1 : n % 3 ≠ 1 := by omega
    simp [hx, hn1, h2]

/-- The sum of the character values over `ZMod 3` vanishes (`χ₋₃` is odd). -/
lemma chi3_sum_zero : (∑ j : ZMod 3, chi3 j) = 0 := by
  change (∑ j : Fin 3, chi3 j) = 0
  simp [chi3, Fin.sum_univ_succ]

/-! ### `L(2, χ₋₃)` as a classical Dirichlet series -/

/-- The L-function value of `χ₋₃` at `2` (the meromorphic continuation used
in Mathlib) coincides with the classical Dirichlet L-series. -/
lemma LFunction_chi3_two_eq_LSeries :
    ZMod.LFunction chi3 2 = LSeries (fun n : ℕ => chi3 (n : ZMod 3)) (2 : ℂ) := by
  exact ZMod.LFunction_eq_LSeries chi3 (s := (2 : ℂ)) (by norm_num)

/-- `L(2, χ₋₃)` as the classical absolutely convergent series
`∑ n, χ₋₃(n) / n²` (complex `cpow` notation). -/
lemma LFunction_chi3_two_eq_tsum :
    ZMod.LFunction chi3 2 = ∑' n : ℕ, chi3 (n : ZMod 3) / ((n : ℂ) ^ (2 : ℂ)) := by
  rw [LFunction_chi3_two_eq_LSeries]
  rw [LSeries_def₀ (f := fun n : ℕ => chi3 (n : ZMod 3)) (s := (2 : ℂ)) (by simp)]

/-- Same series with the character values spelled out via residues mod 3
(exactly the defining display of `L(2, χ₋₃)` in the paper). -/
lemma LFunction_chi3_two_eq_tsum_residues :
    ZMod.LFunction chi3 2 =
      ∑' n : ℕ, (if n % 3 = 1 then (1 : ℂ) else if n % 3 = 2 then -1 else 0) /
        ((n : ℂ) ^ (2 : ℂ)) := by
  rw [LFunction_chi3_two_eq_tsum]
  apply tsum_congr
  intro n
  rw [chi3_apply_nat_mod]

/-! ### Elementary `ℤ`-consequences of the hypothesis of Theorem C -/

/-- If `m ≠ n` and `10⁶ · |m − n| < |n|` then `|n|` is larger than `10⁶`. -/
lemma abs_n_gt_of_ne {m n : ℤ} (hmn : m ≠ n) (h : 10 ^ 6 * |m - n| < |n|) :
    10 ^ 6 < |n| := by
  have hmn' : 1 ≤ |m - n| := by
    have : m - n ≠ 0 := sub_ne_zero.mpr hmn
    exact Int.one_le_abs this
  nlinarith [h, hmn']

/-! ### Generic linear independence criteria (finitary, component form) -/

/-- `![x, y, z]` is linearly independent iff the only vanishing (rational)
combination of `x, y, z` is trivial.  Component form of the standard
finitary criterion; used to phrase Theorems A and C in coefficient form. -/
lemma linearIndependent_cons3_iff {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] (x y z : M) :
    LinearIndependent R ![x, y, z] ↔
      ∀ a b c : R, a • x + b • y + c • z = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [linearIndependent_iff'']
  constructor
  · intro h a b c habc
    have hres := h Finset.univ (![a, b, c] : Fin 3 → R)
      (fun i hi => False.elim (hi (Finset.mem_univ i)))
      (by simpa [Fin.sum_univ_three] using habc)
    have ha : a = 0 := by simpa using hres 0
    have hb : b = 0 := by simpa using hres 1
    have hc : c = 0 := by simpa using hres 2
    exact ⟨ha, hb, hc⟩
  · intro h s g hgs hg0 i
    have hfull0 : (∑ j : Fin 3, g j • (![x, y, z] : Fin 3 → M) j) = 0 := by
      have hrew :
          (∑ j : Fin 3, g j • (![x, y, z] : Fin 3 → M) j) =
            ∑ j ∈ s, g j • (![x, y, z] : Fin 3 → M) j := by
        exact (Finset.sum_subset (s₁ := s) (s₂ := Finset.univ)
          (Finset.subset_univ s) (fun j _hj hjnot => by simp [hgs j hjnot])).symm
      rw [hrew]
      exact hg0
    have hcomp : g 0 • x + g 1 • y + g 2 • z = 0 := by
      simpa [Fin.sum_univ_three] using hfull0
    rcases h (g 0) (g 1) (g 2) hcomp with ⟨h0, h1, h2⟩
    fin_cases i <;> simpa [h0, h1, h2]

/-- The `Fin 4` analogue: `![w, x, y, z]` is independent iff the only null
rational combination is trivial. -/
lemma linearIndependent_cons4_iff {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] (w x y z : M) :
    LinearIndependent R ![w, x, y, z] ↔
      ∀ a b c d : R, a • w + b • x + c • y + d • z = 0 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  rw [linearIndependent_iff'']
  constructor
  · intro h a b c d habcd
    have hres := h Finset.univ (![a, b, c, d] : Fin 4 → R)
      (fun i hi => False.elim (hi (Finset.mem_univ i)))
      (by simpa [Fin.sum_univ_four] using habcd)
    have ha : a = 0 := by simpa using hres 0
    have hb : b = 0 := by simpa using hres 1
    have hc : c = 0 := by simpa using hres 2
    have hd : d = 0 := by simpa using hres 3
    exact ⟨ha, hb, hc, hd⟩
  · intro h s g hgs hg0 i
    have hfull0 : (∑ j : Fin 4, g j • (![w, x, y, z] : Fin 4 → M) j) = 0 := by
      have hrew :
          (∑ j : Fin 4, g j • (![w, x, y, z] : Fin 4 → M) j) =
            ∑ j ∈ s, g j • (![w, x, y, z] : Fin 4 → M) j := by
        exact (Finset.sum_subset (s₁ := s) (s₂ := Finset.univ)
          (Finset.subset_univ s) (fun j _hj hjnot => by simp [hgs j hjnot])).symm
      rw [hrew]
      exact hg0
    have hcomp : g 0 • w + g 1 • x + g 2 • y + g 3 • z = 0 := by
      simpa [Fin.sum_univ_four] using hfull0
    rcases h (g 0) (g 1) (g 2) (g 3) hcomp with ⟨h0, h1, h2, h3⟩
    fin_cases i <;> simpa [h0, h1, h2, h3]



/-! ### The arguments of the logarithms in Theorem C -/

/-- For `m ≠ 0`, the real number `1 + 1/m` never equals `1`. -/
lemma one_add_inv_int_ne_one {m : ℤ} (hm0 : m ≠ 0) : 1 + 1 / (m : ℝ) ≠ 1 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
  have h : 1 / (m : ℝ) ≠ 0 := one_div_ne_zero hmR
  intro heq
  apply h
  linarith

/-- For `m ≠ -1`, the real number `1 + 1/m` never equals `0`. -/
lemma one_add_inv_int_ne_zero {m : ℤ} (hm : m ≠ -1) : 1 + 1 / (m : ℝ) ≠ 0 := by
  by_cases hm0 : m = 0
  · subst m
    norm_num
  · have hm0' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    have hm1 : (m : ℝ) + 1 ≠ 0 := by exact_mod_cast (by omega : m + 1 ≠ 0)
    intro h
    have h' : (1 + 1 / (m : ℝ)) * (m : ℝ) = (m : ℝ) + 1 := by
      calc
        (1 + 1 / (m : ℝ)) * (m : ℝ) = 1 * (m : ℝ) + (1 / (m : ℝ)) * (m : ℝ) := by ring
        _ = (m : ℝ) + 1 := by field_simp [hm0']
    have hmul : (1 + 1 / (m : ℝ)) * (m : ℝ) = 0 := by rw [h]; simp
    exact hm1 (by rwa [h'] at hmul)

/-- For `m ≠ -1, 0`, the real number `1 + 1/m` is strictly positive (it lies
in `(0, 1)` for `m ≤ -2` and in `(1, 2]` for `m ≥ 1`). -/
lemma one_add_inv_int_pos {m : ℤ} (hm0 : m ≠ 0) (hm : m ≠ -1) :
    0 < 1 + 1 / (m : ℝ) := by
  by_cases hpos : 0 < m
  · have hmR : 0 < (m : ℝ) := by exact_mod_cast hpos
    positivity
  · have hmneg : m < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hm0
    have hmle : m ≤ -2 := by omega
    have hmR : (m : ℝ) < 0 := by exact_mod_cast hmneg
    have hmRle : (m : ℝ) ≤ -2 := by exact_mod_cast hmle
    have hm1R : (m : ℝ) + 1 < 0 := by nlinarith
    have hdiv : 0 < ((m : ℝ) + 1) / (m : ℝ) := div_pos_of_neg_of_neg hm1R hmR
    rw [show (1 : ℝ) + 1 / (m : ℝ) = ((m : ℝ) + 1) / (m : ℝ) by
      field_simp [ne_of_lt hmR]]
    exact hdiv

/-- `log(1 + 1/m)` is nonzero for `m ≠ -1, 0`. -/
lemma log_one_add_inv_int_ne_zero {m : ℤ} (hm : m ≠ -1) (hm0 : m ≠ 0) :
    Real.log (1 + 1 / (m : ℝ)) ≠ 0 := by
  have hpos : 0 < 1 + 1 / (m : ℝ) := one_add_inv_int_pos hm0 hm
  have hne : 1 + 1 / (m : ℝ) ≠ 1 := one_add_inv_int_ne_one hm0
  intro hz
  rw [Real.log_eq_zero] at hz
  rcases hz with hz0 | hz1 | hzneg
  · exact one_add_inv_int_ne_zero hm hz0
  · exact hne hz1
  · nlinarith

end

end Submission.Helpers