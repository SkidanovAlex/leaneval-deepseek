import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.EightIdxDefs

namespace Work.CORE4.CtxN9InfAux

/-- **Bender 1981, §4 (8) case 2 (p. 226), the group-theoretic core of `N_U(A) = N_U(P)·Q`.**
`A` is a subgroup of order `p ^ 2` and exponent `p` of a subgroup `Q` (so together with `hAcomm`,
`A ≅ C_p × C_p`), `Z(Q)` (written `Work.CORE4.centerIn Q`) is central of order `p` and lies in `A`,
and `q ∈ Q` satisfies `[q, A] ≤ Z(Q)` (`hcomm`) but does not centralise `A` (`hne`).  Then
conjugation by the powers of `q` moves the `p + 1` subgroups of `A` of order `p` in exactly two
orbits: the central one `Z(Q)` (fixed) and the remaining `p`.  Hence any two subgroups
`L₁, L₂ ≤ A` of order `p`, both different from `Z(Q)`, are conjugate by a power of `q`. -/
theorem ConjPowOrbit {G : Type} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (Q A : Subgroup G) (q : G)
    (hqQ : q ∈ Q)
    (hAQ : A ≤ Q)
    (hAcard : Nat.card ↥A = p ^ 2)
    (hAexp : ∀ x ∈ A, x ^ p = 1)
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hZcard : Nat.card ↥(Work.CORE4.centerIn Q) = p)
    (hZle : Work.CORE4.centerIn Q ≤ A)
    (hcomm : ∀ a ∈ A, q * a * q⁻¹ * a⁻¹ ∈ Work.CORE4.centerIn Q)
    (hne : ∃ a ∈ A, q * a * q⁻¹ * a⁻¹ ≠ 1)
    (L₁ L₂ : Subgroup G) (hL₁A : L₁ ≤ A) (hL₂A : L₂ ≤ A)
    (hL₁card : Nat.card ↥L₁ = p) (hL₂card : Nat.card ↥L₂ = p)
    (hL₁ne : L₁ ≠ Work.CORE4.centerIn Q) (hL₂ne : L₂ ≠ Work.CORE4.centerIn Q) :
    ∃ i : ℕ, Work.GW2.conjSub (q ^ i) L₁ = L₂ := by sorry

end Work.CORE4.CtxN9InfAux
