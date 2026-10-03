import Mathlib
import Submission.Work.Peluse.Holds.ExpPET.Defs

/-!
# The cube term as a linear configuration (the first half of the `ExpansionPETShort` PET step)

`expCube κ n n' f` is the product `∏_{ω : Fin s → Bool} C^{|ω|} f (· + cubeShift κ n n' ω)`.  For
`κ i = c·a + b i` — the direction sets of `ExpansionPETShort`'s hypothesis — and after translating
the argument by the corner `cubeShift κ n n' 0` of the all-false pattern, the `ω = 0` factor becomes
phase-free and the remaining `2^s - 1` factors are the *shifted slot functions*
`C^{|ω|} f (· + c·a·D_ω + S_ω)`, i.e. exactly the multilinear configuration
`F 0 x · ∏_i F i.succ (x + c_slot i · a)` of Peluse's Lemma 4.10 (`PetLinear.LevelBound`).

This file contains that identity, together with the two corner computations it rests on.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Work.Peluse.Holds.ExpPET

open Work.Peluse

/-- The corner at the all-false pattern is `∑ i, n' i · κ i`. -/
lemma cubeShift_zero {s : ℕ} (κ n n' : Fin s → ℤ) :
    cubeShift κ n n' (0 : Fin s → Bool) = ∑ i : Fin s, n' i * κ i := by
  rw [cubeShift]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- **The corner difference**: subtracting the all-false corner from the `ω`-corner leaves the
`(if ω i then n i - n' i else 0)`-combination of the `κ i`. -/
lemma cubeShift_sub_zero {s : ℕ} (κ n n' : Fin s → ℤ) (ω : Fin s → Bool) :
    cubeShift κ n n' ω - cubeShift κ n n' (0 : Fin s → Bool)
      = ∑ i : Fin s, (if ω i then n i - n' i else 0) * κ i := by
  rw [cubeShift, cubeShift_zero, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by by_cases h : ω i <;> simp [h] <;> ring

/-- The same difference, with `κ i = c·a + b i`, split into the `a`-linear phase and the constant
shift. -/
lemma cubeShift_sub_zero_arith {s : ℕ} {b : Fin s → ℤ} (c a : ℤ) (n n' : Fin s → ℤ)
    (ω : Fin s → Bool) :
    (∑ i : Fin s, (if ω i then n i - n' i else 0) * (c * a + b i))
      = (c * a) * (∑ j : Fin s, if ω j then n j - n' j else 0)
        + (∑ j : Fin s, (if ω j then n j - n' j else 0) * b j) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The cube term of the arithmetic-progression directions as a linear configuration.**

After translating the argument by the all-false corner, the cube term is the phase-free factor
`f x` times the `2^s - 1` shifted slot functions `C^{|ω|} f (· + c·a·D_ω + S_ω)` indexed by the
nonzero patterns `ω`. -/
theorem expCube_eq_multilinear {s : ℕ} {b : Fin s → ℤ} (c : ℤ) (f : ℤ → ℂ) (n n' : Fin s → ℤ) :
    ∀ a x : ℤ,
      expCube (fun i : Fin s => c * a + b i) n n' f (x - ∑ i : Fin s, n' i * (c * a + b i))
        = f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin s → Bool)),
            (star^[weight ω])
              (f (x + (c * a) * (∑ j : Fin s, if ω j then n j - n' j else 0)
                  + (∑ j : Fin s, (if ω j then n j - n' j else 0) * b j))) := by
  intro a x
  have hmain : expCube (fun i : Fin s => c * a + b i) n n' f
        (x - ∑ i : Fin s, n' i * (c * a + b i))
      = ∏ ω : Fin s → Bool, (star^[weight ω])
          (f (x + ∑ j : Fin s, (if ω j then n j - n' j else 0) * (c * a + b j))) := by
    rw [expCube]
    refine Finset.prod_congr rfl fun ω _ => ?_
    have hsum : (∑ i : Fin s, (if ω i then n i else n' i) * (c * a + b i))
          - (∑ i : Fin s, n' i * (c * a + b i))
        = ∑ j : Fin s, (if ω j then n j - n' j else 0) * (c * a + b j) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by by_cases h : ω i <;> simp [h] <;> ring
    have h1 : x - (∑ i : Fin s, n' i * (c * a + b i))
          + cubeShift (fun i : Fin s => c * a + b i) n n' ω
        = x + ∑ j : Fin s, (if ω j then n j - n' j else 0) * (c * a + b j) := by
      rw [show cubeShift (fun i : Fin s => c * a + b i) n n' ω
            = ∑ i : Fin s, (if ω i then n i else n' i) * (c * a + b i) from rfl]
      linarith [hsum]
    rw [h1]
  rw [hmain]
  have huniv : (Finset.univ : Finset (Fin s → Bool))
      = insert (0 : Fin s → Bool) (Finset.univ.erase 0) :=
    (Finset.insert_erase (Finset.mem_univ _)).symm
  conv_lhs => rw [huniv]
  rw [Finset.prod_insert (Finset.notMem_erase (0 : Fin s → Bool) Finset.univ)]
  congr 1
  · -- the all-false pattern: weight `0` and corner `0`
    have hw : weight (0 : Fin s → Bool) = 0 := by
      simp [weight, Pi.zero_apply]
    rw [hw]
    simp [Pi.zero_apply]
  · -- the remaining patterns
    refine Finset.prod_congr rfl fun ω _ => ?_
    apply congrArg (fun z : ℤ => (star^[weight ω]) (f z))
    rw [cubeShift_sub_zero_arith c a n n' ω]
    ring

end Work.Peluse.Holds.ExpPET
