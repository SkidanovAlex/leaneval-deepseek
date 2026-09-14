import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open scoped BigOperators

namespace Commons.FieldTheory.Finite

/-- Summing a function over the nonzero elements of a finite field equals summing it
over all units (each unit is coerced back into the field). -/
theorem sum_erase_zero_eq_units {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {M : Type*} [AddCommMonoid M] (f : K → M) :
    (∑ c ∈ (Finset.univ : Finset K).erase 0, f c) = ∑ u : Kˣ, f (u : K) := by
  -- Every nonzero element c of the field is a unit `Units.mk0 c hc`, and every unit
  -- has nonzero coercion, so this is a bijection between the two index finsets.
  apply Finset.sum_bij (s := (Finset.univ : Finset K).erase 0) (t := (Finset.univ : Finset Kˣ))
    (fun c hc => Units.mk0 c (by simpa using (Finset.mem_erase.mp hc).1))
  · intro c hc
    simp
  · intro c₁ hc₁ c₂ hc₂ h
    have hv := congrArg (fun u : Kˣ => (u : K)) h
    simpa using hv
  · intro b hb
    refine ⟨(b : K), ?_, ?_⟩
    · rw [Finset.mem_erase]
      exact ⟨Units.ne_zero b, by simp⟩
    · apply Units.ext
      simp
  · intro c hc
    simp

end Commons.FieldTheory.Finite