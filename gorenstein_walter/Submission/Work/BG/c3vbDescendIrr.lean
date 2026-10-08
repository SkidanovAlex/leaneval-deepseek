import Mathlib
import Submission.Work.BG.CharBridge
import Submission.OddOrder.GroupTheory.RepresentationTheory.InflationCharacter

/-!
# Area BG: descending an irreducible character along a normal complement

If `X = B ⋊ K` (i.e. `K ◁ X` is normal with complement `B`: `B ⊔ K = ⊤`, `B ⊓ K = ⊥`) and
`ψ` is an irreducible character of `X` that is trivial on `K`, then `ψ` is the inflation of an
irreducible character `ψ̄` of the quotient `X ⧸ K` (Isaacs (2.22),
`exists_inflate_eq_of_subset_characterKernel`), and `X ⧸ K ≃* B`
(`Subgroup.IsComplement'.QuotientMulEquiv`).  Pulling `ψ̄` back along this isomorphism produces
an irreducible character `β` of `B` with the same degree, `β 1 = ψ 1`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **Descent of an irreducible character to a normal complement.**
Let `K ◁ X` be a normal subgroup with complement `B` (`B ⊔ K = ⊤`, `B ⊓ K = ⊥`).  An
irreducible character `ψ` of `X` that is constant on `K` (equal to its degree there, so that
`K ⊆ ker ψ`) arises by inflation from an irreducible character of `X ⧸ K`; since
`X ⧸ K ≃* B`, it descends to an irreducible character `β` of `B` with the same degree. -/
theorem c3vbDescendIrr {X : Type} [Group X] [Finite X] [Fintype X]
    [Invertible (Nat.card X : ℂ)] (B K : Subgroup X) [K.Normal]
    (hsup : B ⊔ K = ⊤) (hinf : B ⊓ K = ⊥)
    (ψ : OddOrder.RepresentationTheory.ClassFunction X ℂ)
    (hψ : OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ)
    (hker : ∀ k ∈ K, ψ k = ψ 1) :
    ∃ β : OddOrder.RepresentationTheory.ClassFunction ↥B ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter β ∧ β 1 = ψ 1 := by
  classical
  -- `ψ` is trivial on the normal subgroup `K`, i.e. `K` lies in the character kernel of `ψ`.
  have hkerK : (K : Set X) ⊆ OddOrder.Peterfalvi.S03.characterKernel ψ := by
    intro k hk
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def]
    exact hker k hk
  -- Descend `ψ` through the quotient `X ⧸ K` (Isaacs (2.22)).
  obtain ⟨ψbar, hψbar⟩ :=
    exists_inflate_eq_of_subset_characterKernel (N := K) ⟨ψ, hψ⟩ hkerK
  -- `B` and `K` are complementary subgroups, so `X ⧸ K ≃* B`.
  have hcompl : B.IsComplement' K := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf) ?_
    rw [← Subgroup.mul_normal, hsup]
    rfl
  let e : X ⧸ K ≃* ↥B := hcompl.QuotientMulEquiv
  -- The degree of `ψ` is the degree of `ψbar`.
  have h1 : (ψbar : ClassFunction (X ⧸ K) ℂ) 1 = ψ 1 := by
    have h := congrArg
      (fun (χ : IrreducibleCharacter X) => ((χ : ClassFunction X ℂ) 1)) hψbar
    rw [inflate_apply_one] at h
    simpa using h
  -- Pull `ψbar` back along the isomorphism `e.symm : B ≃* X ⧸ K`.
  refine ⟨ClassFunction.compHom (e.symm : ↥B ≃* X ⧸ K).toMonoidHom
    (ψbar : ClassFunction (X ⧸ K) ℂ), ?_, ?_⟩
  · exact IsIrreducibleCharacter.compHom_of_surjective e.symm.surjective ψbar.isIrreducible
  · rw [ClassFunction.compHom_apply, map_one, h1]

end Work.BG
