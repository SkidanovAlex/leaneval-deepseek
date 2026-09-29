import Mathlib

namespace Work.TMComp.LocCantor

open Set

/-- An auxiliary fact: a set `Z` closed under `± 1` is closed under translation by any
integer. -/
theorem add_int_mem {Z : Set ℝ}
    (hZper : ∀ z ∈ Z, z + 1 ∈ Z ∧ z - 1 ∈ Z) :
    ∀ w ∈ Z, ∀ n : ℤ, w + (n : ℝ) ∈ Z := by
  intro w hw n
  induction n using Int.induction_on with
  | zero => simpa using hw
  | succ i ih =>
      have h := (hZper (w + (i:ℝ)) ih).1
      rw [show ((↑i + 1 : ℤ) : ℝ) = (i:ℝ) + 1 by push_cast; ring]
      simpa [add_assoc] using h
  | pred i ih =>
      have h := (hZper (w + ((-↑i : ℤ):ℝ)) ih).2
      rw [show ((-↑i - 1 : ℤ) : ℝ) = ((-↑i:ℤ):ℝ) - 1 by push_cast; ring]
      simpa [sub_eq_add_neg, add_assoc] using h

/-- If `Z ⊆ ℝ` meets `[0,1]` in a finite set and is invariant under translation by `±1`,
then the half-line `{z + K α : K ≥ 1}` starting at any `z ∈ Z` cannot be entirely contained
in `Z`, whenever `α` is irrational.

Indeed, `Z` is periodic with period `1`, so it is locally finite.  The fractional parts of the
points `z + K α` are distinct (because `α` is irrational) and would all lie in the finite set
`Z ∩ [0,1]`; a finite set cannot contain an infinite set of distinct points. -/
theorem orbit_leaves_zero_set {Z : Set ℝ} {α : ℝ} (hα : Irrational α)
    (hZfin : (Z ∩ Set.Icc 0 1).Finite)
    (hZper : ∀ z ∈ Z, z + 1 ∈ Z ∧ z - 1 ∈ Z) :
    ∀ z ∈ Z, ∃ K : ℕ, 1 ≤ K ∧ z + (K : ℝ) * α ∉ Z := by
  have hint := add_int_mem hZper
  intro z hz
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ K, 1 ≤ K → z + (K : ℝ) * α ∈ Z`.
  -- The map sending `K` to the fractional part of `z + (K+1) α`.
  let u : ℕ → ℝ := fun k => Int.fract (z + ((k:ℝ)+1) * α)
  -- Every value of `u` lies in the finite set `Z ∩ [0,1]`.
  have hu_mem : ∀ k : ℕ, u k ∈ Z ∩ Set.Icc 0 1 := by
    intro k
    have hmem : z + ((k:ℝ)+1) * α ∈ Z := by
      have h1 := hcon (k+1) (Nat.le_add_left 1 k)
      simpa [Nat.cast_add, Nat.cast_one] using h1
    have hZ : u k ∈ Z := by
      show Int.fract (z + ((k:ℝ)+1) * α) ∈ Z
      rw [show Int.fract (z + ((k:ℝ)+1) * α)
          = (z + ((k:ℝ)+1) * α) + ((-⌊z + ((k:ℝ)+1) * α⌋ : ℤ) : ℝ) from by
        rw [Int.fract.eq_1]; push_cast; ring]
      exact hint _ hmem _
    have hI : u k ∈ Set.Icc 0 1 := by
      show 0 ≤ Int.fract (z + ((k:ℝ)+1) * α) ∧ Int.fract (z + ((k:ℝ)+1) * α) ≤ 1
      exact ⟨Int.fract_nonneg _, le_of_lt (Int.fract_lt_one _)⟩
    exact ⟨hZ, hI⟩
  -- `u` is injective because `α` is irrational.
  have hu_inj : Function.Injective u := by
    intro k l hkl
    have hkl' : Int.fract (z + ((k:ℝ)+1) * α) = Int.fract (z + ((l:ℝ)+1) * α) := hkl
    rw [Int.fract_eq_fract] at hkl'
    obtain ⟨m, hm⟩ := hkl'
    have hm2 : (((k:ℤ) - (l:ℤ) : ℤ) : ℝ) * α = (m : ℝ) := by
      have h := hm
      push_cast at h ⊢
      ring_nf at h ⊢
      linarith
    by_contra hne
    have hkd : ((k:ℤ) - (l:ℤ)) ≠ 0 := by
      intro hc
      apply hne
      have : (k:ℤ) = (l:ℤ) := by omega
      exact_mod_cast this
    have hirr : Irrational ((((k:ℤ)-(l:ℤ) : ℤ) : ℝ) * α) := hα.intCast_mul hkd
    have hq : ((((k:ℤ)-(l:ℤ) : ℤ) : ℝ) * α) = ((m : ℚ) : ℝ) := by
      rw [hm2]; push_cast; ring
    exact hirr.ne_rat (m : ℚ) hq
  -- Hence `range u` is an infinite subset of the finite set `Z ∩ [0,1]`: contradiction.
  have hsub : Set.range u ⊆ Z ∩ Set.Icc 0 1 := by
    rintro x ⟨k, rfl⟩
    exact hu_mem k
  have hinf : (Set.range u).Infinite := Set.infinite_range_of_injective hu_inj
  exact hZfin.not_infinite (Set.Infinite.mono hsub hinf)

end Work.TMComp.LocCantor
