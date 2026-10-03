import Mathlib
import Submission.Work.FIArea2.sqRoots_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.FIArea2

open Finset

attribute [local instance] Classical.propDecidable

/-- **Counting residues by the class in `ZMod N`.**  For `N ≠ 0`, the number of `y` with
`0 ≤ y < N` and `y ^ 2 % N = c % N` equals the number of `z : ZMod N` with `z ^ 2 = c`.
This is the bijection `z ↦ z.val` between `ZMod N` and `{y // y < N}`, which carries the
condition `z ^ 2 = c` to `z.val ^ 2 % N = c % N`. -/
lemma card_range_filter_sq_mod (N : ℕ) [NeZero N] (c : ℕ) :
    ((Finset.range N).filter (fun y => y ^ 2 % N = c % N)).card
      = Nat.card {z : ZMod N // z ^ 2 = (c : ZMod N)} := by
  classical
  have hcard : ((Finset.univ : Finset (ZMod N)).filter
      (fun z => z ^ 2 = (c : ZMod N))).card
      = ((Finset.range N).filter (fun y => y ^ 2 % N = c % N)).card := by
    refine Finset.card_bij (fun z _ => z.val) ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt z, ?_⟩
      have h : ((z.val ^ 2 : ℕ) : ZMod N) = (c : ZMod N) := by
        push_cast
        rw [ZMod.natCast_zmod_val, hz]
      rw [ZMod.natCast_eq_natCast_iff'] at h
      simpa using h
    · intro z1 hz1 z2 hz2 h
      exact ZMod.val_injective N h
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_range] at hy
      refine ⟨(y : ZMod N), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have h1 : ((y : ℕ) : ZMod N) ^ 2 = ((y ^ 2 : ℕ) : ZMod N) := by push_cast; ring
        rw [h1, ZMod.natCast_eq_natCast_iff']
        exact hy.2
      · exact ZMod.val_cast_of_lt hy.1
  rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **(*FI* (8.12) in residue form) the number of square roots of a unit modulo `p^ν`.**  For an odd prime `p`, `ν ≥ 1` and `c` not divisible by `p`, the number of `y` with `0 ≤ y < p^ν` and `p^ν ∣ y² - c` is `1 + (c/p)`, the Jacobi symbol (i.e. `2` if `c` is a quadratic residue mod `p`, else `0`).  This is the residue-level form of `Work.FIArea2.sqRoots_card` (`z ↦ z.val` is a bijection `ZMod (p^ν) ≃ {y // y < p^ν}` carrying `z² = c` to `y² % p^ν = c % p^ν`), used in the evaluation of the solutions of `aγ₁² ≡ γ₂² (mod p^ν)` with `p ∤ γ₁`. -/
theorem card_sq_roots_nat (p ν : ℕ) (hp : p.Prime) (hodd : Odd p) (hν : 0 < ν) (c : ℕ)
    (hc : ¬ p ∣ c) :
    (((Finset.range (p ^ ν)).filter (fun y => y ^ 2 % p ^ ν = c % p ^ ν)).card : ℤ)
      = 1 + jacobiSym (c : ℤ) p := by
  haveI : NeZero (p ^ ν) := ⟨pow_ne_zero ν hp.ne_zero⟩
  rw [card_range_filter_sq_mod (p ^ ν) c]
  have hcard : Nat.card {z : ZMod (p ^ ν) // z ^ 2 = (c : ZMod (p ^ ν))}
      = Nat.card {z : ZMod (p ^ ν) // z ^ 2 = ((c : ℤ) : ZMod (p ^ ν))} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun z => by simp))
  rw [hcard]
  have hc' : ¬ (p : ℤ) ∣ (c : ℤ) := fun hd => hc (Int.natCast_dvd_natCast.mp hd)
  exact sqRoots_card p ν hp hodd hν (c : ℤ) hc'

end Work.FIArea2
