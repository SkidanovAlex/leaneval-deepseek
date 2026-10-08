import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

theorem indexTwoInduceIrreducible {H : Type*} [Group H] [Finite H] [Fintype H] (H0 : Subgroup H)
    [H0.Normal] (hind : H0.index = 2) (s : H) (hs : s ∉ H0)
    [Invertible (Nat.card H0 : ℂ)] [Invertible (Nat.card H : ℂ)]
    (ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥H0)
    (hν : OddOrder.RepresentationTheory.ClassFunction.conjBy s
            (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ) ≠
          (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ)) :
    OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (OddOrder.RepresentationTheory.ClassFunction.induce H0
        (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ)) := by
  /- Route: Clifford/inertia.  Since `θ = (ν : ClassFunction ↥H₀ ℂ)` is `s`-invariant iff
  `s ∈ I_H(θ)`, the hypothesis `hν` puts `s` outside the inertia group, so `I_H(θ) ≠ ⊤`.
  But `H₀ ≤ I_H(θ)` always, and `[H : H₀] = 2` divides all indices in between, so the only
  possibilities for `I_H(θ)` are `H₀` and `⊤`; hence `I_H(θ) = H₀`.  Frobenius/[Is] 6.34
  (`isIrreducibleCharacter_induce_of_inertia_eq`) then gives irreducibility of `Ind θ`. -/
  refine OddOrder.RepresentationTheory.isIrreducibleCharacter_induce_of_inertia_eq ν ?_
  set I : Subgroup H :=
    OddOrder.RepresentationTheory.ClassFunction.inertia (G := H) (H := H0)
      (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ) with hI
  -- the inertia group contains `H₀` (class functions are invariant under inner conjugation)
  have hle : H0 ≤ I := OddOrder.RepresentationTheory.ClassFunction.subgroup_le_inertia _
  -- `s` is not in the inertia group: it does not stabilise `ν`
  have hsI : s ∉ I := by
    intro hmem
    exact hν (OddOrder.RepresentationTheory.ClassFunction.mem_inertia.mp hmem)
  -- hence the inertia group is a proper subgroup
  have hne_top : I ≠ ⊤ := by
    intro h
    exact hsI (by rw [h]; exact Subgroup.mem_top s)
  -- `[H : I]` divides `[H : H₀] = 2` by monotonicity of the index
  have hdvd : I.index ∣ 2 := by
    have h := Subgroup.index_dvd_of_le hle
    rwa [hind] at h
  -- a proper subgroup has index `≠ 1`, so `[H : I] = 2`
  have hI2 : I.index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h (fun h => hne_top (Subgroup.index_eq_one.mp h))
    · exact h
  -- consequently `[I : H₀] = 1`, i.e. `I ≤ H₀`
  have hrel : H0.relIndex I = 1 := by
    have h := Subgroup.relIndex_mul_index hle
    rw [hind, hI2] at h
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel) hle

end Work.BG
