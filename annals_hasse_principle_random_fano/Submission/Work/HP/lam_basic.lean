import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs

/-!
# Basic properties of the successive minima `lam` (`Work.HP.lam_basic`)

`lam L i` is the `i`-th successive minimum of the integral lattice `L ⊆ ℤ^ι`: the infimum of
the radii `r` for which `L` contains `i` linearly independent vectors of norm `≤ r`.

This file proves the elementary facts collected in `lam_basic`: positivity up to the rank,
monotonicity in the index, finiteness (a dyadic bound), and the two comparison bounds
`lam L 1 ≤ ‖v‖` (one vector) and `lam L 2 ≤ max ‖x‖ ‖y‖` (two vectors).
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP

variable {ι : Type*} [Fintype ι]

/-- A nonzero integer vector has Euclidean norm at least `1`. -/
lemma one_le_eNorm {v : ι → ℤ} (hv : v ≠ 0) : 1 ≤ eNorm v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hiz : v i ≠ 0 := by simpa using hi
  have hge : (1 : ℤ) ≤ |v i| := by have := abs_pos.mpr hiz; omega
  have hge' : (1 : ℝ) ≤ |((v i : ℤ) : ℝ)| := by exact_mod_cast hge
  have hsq : (1 : ℝ) ≤ ((v i : ℝ)) ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg ((v i : ℤ) : ℝ)]
  have h2 : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j : ℝ)) (Finset.mem_univ i)
  have := Real.one_le_sqrt.mpr (le_trans hsq h2)
  simpa [eNorm] using this

/-- The defining set of the `i`-th successive minimum: the radii `r ≥ 0` for which `L` contains
`i` linearly independent vectors of norm at most `r`. -/
def lamSet (L : Submodule ℤ (ι → ℤ)) (i : ℕ) : Set ℝ :=
  {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → ι → ℤ,
    (∀ j, f j ∈ L) ∧ LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ r}

lemma lam_eq_sInf (L : Submodule ℤ (ι → ℤ)) (i : ℕ) : lam L i = sInf (lamSet L i) := rfl

lemma bddBelow_lamSet (L : Submodule ℤ (ι → ℤ)) (i : ℕ) : BddBelow (lamSet L i) :=
  ⟨0, fun _ hr => hr.1⟩

/-- If `i ≤ rk L` then `L` contains `i` linearly independent vectors, so the defining set of
`lam L i` is nonempty. -/
lemma lamSet_nonempty (L : Submodule ℤ (ι → ℤ)) {i : ℕ} (hi : i ≤ rk L) :
    (lamSet L i).Nonempty := by
  classical
  obtain ⟨f, hfL, hfLI⟩ := exists_linIndep_card L hi
  refine ⟨∑ j : Fin i, eNorm (f j), Finset.sum_nonneg (fun j _ => eNorm_nonneg _), f, hfL, hfLI, ?_⟩
  intro j
  exact Finset.single_le_sum (fun k _ => eNorm_nonneg _) (Finset.mem_univ j)

/-- Part 1: for `1 ≤ i ≤ rk L`, the `i`-th successive minimum is positive. -/
lemma lam_pos (L : Submodule ℤ (ι → ℤ)) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ rk L) :
    0 < lam L i := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨f, -, hfLI, hfρ⟩ := lam_witness L hi (ρ := (1 / 2 : ℝ)) (by linarith)
  have h0 : f ⟨0, hi1⟩ ≠ 0 := hfLI.ne_zero ⟨0, hi1⟩
  have h1 : (1 : ℝ) ≤ eNorm (f ⟨0, hi1⟩) := one_le_eNorm h0
  have h2 : eNorm (f ⟨0, hi1⟩) ≤ 1 / 2 := hfρ ⟨0, hi1⟩
  linarith

/-- Part 2: `lam L ·` is monotone in the index, as long as the index is at most the rank. -/
lemma lam_mono (L : Submodule ℤ (ι → ℤ)) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ rk L) :
    lam L i ≤ lam L j := by
  rw [lam_eq_sInf, lam_eq_sInf]
  refine le_csInf (lamSet_nonempty L hj) ?_
  rintro r ⟨hr0, f, hfL, hfLI, hfr⟩
  refine csInf_le (bddBelow_lamSet L i) ?_
  exact ⟨hr0, fun k => f (Fin.castLE hij k), fun k => hfL _,
    hfLI.comp (Fin.castLE hij) (Fin.castLE_injective hij), fun k => hfr _⟩

/-- Part 3: `lam L i` is finite (bounded by a power of `2`) for `i ≤ rk L`. -/
lemma lam_le_two_pow (L : Submodule ℤ (ι → ℤ)) {i : ℕ} (hi : i ≤ rk L) :
    ∃ k : ℕ, lam L i ≤ (2 : ℝ) ^ k := by
  classical
  obtain ⟨f, hfL, hfLI⟩ := exists_linIndep_card L hi
  set r : ℝ := ∑ j : Fin i, eNorm (f j) with hr
  have hmem : r ∈ lamSet L i :=
    ⟨Finset.sum_nonneg (fun j _ => eNorm_nonneg _), f, hfL, hfLI,
      fun j => Finset.single_le_sum (fun k _ => eNorm_nonneg _) (Finset.mem_univ j)⟩
  have hle : lam L i ≤ r := by
    rw [lam_eq_sInf]; exact csInf_le (bddBelow_lamSet L i) hmem
  refine ⟨Nat.ceil r, hle.trans ?_⟩
  have h₁ : r ≤ ((Nat.ceil r : ℕ) : ℝ) := Nat.le_ceil r
  have h₂ : (((Nat.ceil r : ℕ)) : ℝ) ≤ (2 : ℝ) ^ Nat.ceil r := by
    have hnat : Nat.ceil r < 2 ^ Nat.ceil r := Nat.lt_two_pow_self
    calc ((Nat.ceil r : ℕ) : ℝ) ≤ ((2 ^ Nat.ceil r : ℕ) : ℝ) := by exact_mod_cast hnat.le
      _ = (2 : ℝ) ^ Nat.ceil r := by push_cast; ring
  exact h₁.trans h₂

/-- Part 4: the first successive minimum is at most the norm of every nonzero lattice vector. -/
lemma lam_one_le_eNorm (L : Submodule ℤ (ι → ℤ)) {v : ι → ℤ} (hv : v ∈ L) (hv0 : v ≠ 0) :
    lam L 1 ≤ eNorm v := by
  rw [lam_eq_sInf]
  refine csInf_le (bddBelow_lamSet L 1) ?_
  refine ⟨eNorm_nonneg v, fun _ : Fin 1 => v, fun _ => hv, ?_, fun _ => le_rfl⟩
  rw [linearIndependent_unique_iff]
  exact hv0

/-- Part 5: the second successive minimum is at most the larger norm of two independent
lattice vectors. -/
lemma lam_two_le_max (L : Submodule ℤ (ι → ℤ)) {x y : ι → ℤ} (hx : x ∈ L) (hy : y ∈ L)
    (hxy : LinearIndependent ℤ ![x, y]) : lam L 2 ≤ max (eNorm x) (eNorm y) := by
  rw [lam_eq_sInf]
  refine csInf_le (bddBelow_lamSet L 2) ?_
  refine ⟨le_trans (eNorm_nonneg x) (le_max_left _ _), ![x, y], ?_, hxy, ?_⟩
  · intro j
    fin_cases j
    · simpa using hx
    · simpa using hy
  · intro j
    fin_cases j
    · simp
    · simp

theorem lam_basic (ι : Type) [Fintype ι] (L : Submodule ℤ (ι → ℤ)) :
    (∀ i, 1 ≤ i → i ≤ rk L → 0 < lam L i) ∧
    (∀ i j, i ≤ j → j ≤ rk L → lam L i ≤ lam L j) ∧
    (∀ i, i ≤ rk L → ∃ k : ℕ, lam L i ≤ (2 : ℝ) ^ k) ∧
    (∀ v : ι → ℤ, v ∈ L → v ≠ 0 → lam L 1 ≤ eNorm v) ∧
    (∀ x y : ι → ℤ, x ∈ L → y ∈ L → LinearIndependent ℤ ![x, y] →
        lam L 2 ≤ max (eNorm x) (eNorm y)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi1 hi
    exact lam_pos L hi1 hi
  · intro i j hij hj
    exact lam_mono L hij hj
  · intro i hi
    exact lam_le_two_pow L hi
  · intro v hv hv0
    exact lam_one_le_eNorm L hv hv0
  · intro x y hx hy hxy
    exact lam_two_le_max L hx hy hxy

end Work.HP
