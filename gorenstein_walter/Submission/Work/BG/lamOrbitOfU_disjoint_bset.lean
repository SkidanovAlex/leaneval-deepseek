import Mathlib
import Submission.Work.BG.lemma36Defs
import Submission.Work.BG.L36SconjNotInOrbit

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **`Λ(a)` is disjoint from `𝒮(χ)`.**  Under the standing hypothesis `hsl : ν^s ∈ Λν` for every
`ν ∈ 𝒮(χ) = bset C f χ`, no member of the `Λ`-orbit `lamOrbitOfU C a` of a `U`-irreducible `a`
that is nontrivial on `K` lies in `𝒮(χ)`.

This is a very short corollary of the *already proved*
`Work.BG.constituent_trivial_of_sconj_mem`
(`Submission/Work/BG/L36SconjNotInOrbit.lean`), which says: if `μ ∈ Irr(H₀)` with
`sconj C μ ∈ lamOrbit C μ`, and `θ ∈ Irr(U)` is a constituent of `μ|_U`, then `θ` is trivial on
`KuSub C K`, i.e. `θ k = θ 1` for `k ∈ KuSub C K`.

Proof: given `ν ∈ lamOrbitOfU C a` we have (by the definition of `lamOrbitOfU`) that `ν` is
irreducible and `⟨ν|_U, a⟩ ≠ 0`; given `ν ∈ bset C f χ` we get `hsl ν hν : sconj C ν ∈ lamOrbit C ν`.
Apply `constituent_trivial_of_sconj_mem` with `μ := ν`, `θ := (a : ClassFunction ↥(Uin C) ℂ)`
(its `hKnorm` is `Knorm` transported along `hDC.U_eq : C.P.U = D.U`; note `hKU` is not needed
since `nontrivialOn` already hands back an element of `↥(Uin C)`): for every `k ∈ KuSub C K`,
`(a : _) k = (a : _) 1`.  But `Work.BG.nontrivialOn C K a` provides
`u : ↥(Uin C)` with `((u : ↥C.P.H0) : G) ∈ K` and `(a : _) u ≠ (a : _) 1`, and
`u ∈ KuSub C K` unfolds (`Subgroup.mem_subgroupOf` twice) to exactly
`((u : ↥C.P.H0) : G) ∈ K`.  Contradiction. -/
theorem lamOrbitOfU_disjoint_bset {G : Type} [Group G] [Finite G] [Fintype G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    (hS3 : Work.GW2.C16.Sec3Hyp D) (K : Subgroup G) (hKU : K ≤ D.U)
    (Knorm : ∀ u ∈ D.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K)
    (h1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (h2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ)
    (χ : ClassFunction G ℂ)
    (hsl : ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ∈ Work.BG.lamOrbit C ν)
    (a : IrreducibleCharacter ↥(Work.GW2.C16.Uin C)) (ha : Work.BG.nontrivialOn C K a) :
    ∀ ν : ClassFunction ↥C.P.H0 ℂ,
      ν ∈ Work.BG.lamOrbitOfU C (a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) →
      ν ∉ Work.GW2.C16.bset C f χ := by
  intro ν hνmem hνbset
  rw [Work.BG.lamOrbitOfU] at hνmem
  obtain ⟨hνirr, hconst⟩ := hνmem
  have hKnorm : ∀ u ∈ C.P.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K := by
    intro u hu
    rw [hDC.U_eq] at hu
    exact Knorm u hu
  obtain ⟨u, huK, hune⟩ := ha
  have hku : u ∈ Work.BG.KuSub C K := by
    rw [Work.BG.KuSub, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact huK
  exact hune (Work.BG.constituent_trivial_of_sconj_mem D C K hDC hKnorm h1 h2 hνirr
    (hsl ν hνbset) a.isIrreducible hconst u hku)

end Work.BG
