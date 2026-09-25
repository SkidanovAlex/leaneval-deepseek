/-
Copyright: the martinet_totally_real_towers team.

# Vanishing of `H¹` with coefficients in the `n`-th powers

`Work.ConCohomology.nPowers (G := G) (B := B) n` is the subgroup `n • B ⊆ B` of `n`-th powers
of a discrete `G`-module `B`.  This module records the elementary consequence of Hilbert 90 that
is used when the power map is *surjective*: if `nPowers n = ⊤` (every element of `B` is an `n`-th
power -- for `B = Lˣ` with `L` separably closed and `n` invertible in `L`) and if every
`1`-cocycle `G → B` is a coboundary (Hilbert 90, `hilbert90_subsingleton_H1`), then also
`H¹(G, nPowers n) = 0`.

The point of the statement is that the coefficients change: a cocycle with values in the subgroup
of `n`-th powers, lifted to `B`, is a coboundary `d⁰β`, and the witnessing `β` automatically lies
in the subgroup because that subgroup is everything.

## The argument

It suffices to prove `B¹(G, ↥nPowers) = ⊤`.  Given a `1`-cocycle `z : G → ↥(nPowers n)`, its
composite `z'` with the inclusion `↥(nPowers n) → B` is again a cocycle (the inclusion is
equivariant and additive), and it is locally constant; by hypothesis `H¹(G,B)` is trivial, so
`z' = d⁰β` for some `β : B`.  Since `nPowers n = ⊤`, that `β` is an `n`-th power, hence defines
an element `⟨β, _⟩ : ↥(nPowers n)`, and the equality `z = d⁰⟨β, _⟩` is checked on the underlying
elements of `B`.
-/

import Mathlib
import Submission.Work.ConCohomology.hilbert90_subsingleton_H1
import Submission.Work.ConCohomology.Kummer

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

/-- **`H¹` with coefficients in the `n`-th powers.**  If `H¹(G,B) = 0` and every element of `B` is
an `n`-th power, then `H¹` with coefficients in the subgroup of `n`-th powers vanishes as well. -/
theorem subsingleton_H1_nPowers {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {B : Type*} [AddCommGroup B] [DistribMulAction G B]
    [IsDiscreteGModule G B] (n : ℕ) (hsub : Subsingleton (H1 G B))
    (h : nPowers (G := G) (B := B) n = ⊤) :
    Subsingleton (H1 G ↥(nPowers (G := G) (B := B) n)) := by
  haveI := hsub
  -- it suffices that every `1`-cocycle with values in `nPowers n` is a coboundary
  have htop : B1' G ↥(nPowers (G := G) (B := B) n) = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro z
    rw [mem_B1', mem_B1]
    -- the cocycle `z`, read in `B`
    let z' : G → B := fun σ => ((z : G → ↥(nPowers (G := G) (B := B) n)) σ : B)
    have hz'coc : IsCocycle1 z' := by
      intro σ τ
      exact congrArg (fun c : ↥(nPowers (G := G) (B := B) n) => (c : B))
        ((mem_Z1 (M := ↥(nPowers (G := G) (B := B) n))).mp z.2 σ τ)
    let Z' : Z1 G B :=
      ⟨⟨z', (z.1.isLocallyConstant).comp
          (fun c : ↥(nPowers (G := G) (B := B) n) => (c : B))⟩, by
        rw [mem_Z1]; exact hz'coc⟩
    -- it is a coboundary, because `H¹(G,B)` is trivial
    have hZ' : (Z' : Cochain1 G B) ∈ B1 G B := by
      have h0 : H1.mk Z' = 0 := Subsingleton.elim _ _
      exact mem_B1'.mp ((H1.mk_eq_zero_iff Z').mp h0)
    obtain ⟨β, hβ⟩ := mem_B1.mp hZ'
    -- and the witnessing `β` lies in `nPowers n`, since that subgroup is everything
    have hβN : β ∈ nPowers (G := G) (B := B) n := by rw [h]; trivial
    refine ⟨⟨β, hβN⟩, ?_⟩
    ext σ
    exact congrFun (congrArg (fun f : Cochain1 G B => (f : G → B)) hβ) σ
  rw [show H1 G ↥(nPowers (G := G) (B := B) n)
      = ((Z1 G ↥(nPowers (G := G) (B := B) n)) ⧸
          (B1' G ↥(nPowers (G := G) (B := B) n))) from rfl, htop]
  exact QuotientAddGroup.subsingleton_quotient_top

/-- **Kummer-theoretic consequence of Hilbert 90.**  When the `n`-th power map on `Lˣ` is
surjective, the first cohomology of `Gal(L/K)` with coefficients in the `n`-th powers (a subgroup
of `Lˣ` that is then all of `Lˣ`) vanishes. -/
lemma H1_nPowers_subsingleton {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (n : ℕ) (h : nPowers (G := Gal(L/K)) (B := Additive Lˣ) n = ⊤) :
    Subsingleton (H1 (Gal(L/K)) ↥(nPowers (G := Gal(L/K)) (B := Additive Lˣ) n)) :=
  subsingleton_H1_nPowers (G := Gal(L/K)) (B := Additive Lˣ) n
    (hilbert90_subsingleton_H1 (K := K) (L := L)) h

end Work.ConCohomology
