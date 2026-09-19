import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.DirichletCharacter.norm_completedLFunction_vertical

open scoped BigOperators
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-- A block of `N` consecutive integers contains each residue modulo `N` exactly once, so
summing any function over such a block gives the same as summing it over all of `ZMod N`. -/
lemma sum_range_translate {N M : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    (∑ k ∈ Finset.range N, f ((M + k : ℕ) : ZMod N)) = ∑ a : ZMod N, f a := by
  classical
  refine Finset.sum_bij (s := Finset.range N) (t := Finset.univ)
    (fun k _hk => ((M + k : ℕ) : ZMod N)) ?_ ?_ ?_ ?_
  · intro k hk
    simp
  · intro k hk l hl hkl
    have hklt : k < N := Finset.mem_range.mp hk
    have hllt : l < N := Finset.mem_range.mp hl
    have hcancel : (k : ZMod N) = (l : ZMod N) := by
      apply add_left_cancel (a := (M : ZMod N))
      simpa [Nat.cast_add] using hkl
    have hmod : k ≡ l [MOD N] := (ZMod.natCast_eq_natCast_iff k l N).mp hcancel
    have hkmod : k % N = k := Nat.mod_eq_of_lt hklt
    have hlmod : l % N = l := Nat.mod_eq_of_lt hllt
    simpa [Nat.ModEq, hkmod, hlmod] using hmod
  · intro b hb
    refine ⟨(b - (M : ZMod N)).val, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    have hval : (((b - (M : ZMod N)).val : ℕ) : ZMod N) = b - (M : ZMod N) := by
      exact ZMod.natCast_zmod_val (b - (M : ZMod N))
    calc
      ((M + (b - (M : ZMod N)).val : ℕ) : ZMod N)
          = (M : ZMod N) + (((b - (M : ZMod N)).val : ℕ) : ZMod N) := by
            rw [Nat.cast_add]
      _ = (M : ZMod N) + (b - (M : ZMod N)) := by rw [hval]
      _ = b := by abel
  · intro k hk
    rfl

/-- A nontrivial Dirichlet character sums to zero over any complete system of residues
modulo `N`, in particular over the interval `[M, M + N)`. -/
lemma sum_char_shift_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (M : ℕ) :
    (∑ k ∈ Finset.range N, (χ ((M + k : ℕ) : ZMod N) : ℂ)) = 0 := by
  rw [sum_range_translate (f := fun a : ZMod N => (χ a : ℂ))]
  exact (MulChar.sum_eq_zero_of_ne_one hχ : ∑ a : ZMod N, (χ a : ℂ) = 0)

/-- Prefix partial sums of a nontrivial Dirichlet character are periodic with period
`N`: `S (M + N) = S M`. -/
theorem prefix_periodic {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (M : ℕ) :
    (∑ n ∈ Finset.range (M + N), (χ (n : ZMod N) : ℂ)) =
      (∑ n ∈ Finset.range M, (χ (n : ZMod N) : ℂ)) := by
  rw [Finset.sum_range_add (fun n : ℕ => (χ (n : ZMod N) : ℂ)) M N]
  rw [sum_char_shift_zero χ hχ M]
  simp

end Commons.NumberTheory.DirichletCharacter