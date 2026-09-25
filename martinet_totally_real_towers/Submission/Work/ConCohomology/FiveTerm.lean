/-
Copyright: the martinet_totally_real_towers team.

# The `Q`-action on `H¹(N,M)` and the invariants `H¹(N,M)^Q`

For an extension `1 → N → G → Q → 1` (`GroupExt`) and a discrete `G`-module `M`, the conjugation
action of `G` on `1`-cochains on `N` (`conjCochain`) descends to `H¹(N,M)` (`conjH1Map`), and
since the inner action of `N` is trivial (`conjCochain_inner`) this is a `Q`-action.  Its
invariants are `H1Invariants E hcont hcompN : AddSubgroup (H1 N M)` -- the third term of the five
term sequence.

The exactness statements about the transgression live in
`Work.ConCohomology.ker_H2Res_eq_range_tg`.
-/

import Submission.Work.ConCohomology.Extension
import Submission.Work.ConCohomology.isCocycle1_conjCochain
import Submission.Work.ConCohomology.conjCochain_coboundary
import Submission.Work.ConCohomology.conjCochain_mul
import Submission.Work.ConCohomology.conjCochain_inner

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

/-- The action of `g` on `1`-cochains on `N`, as an additive homomorphism. -/
noncomputable def conjCochainHom {G Q N : Type*} [Group G] [TopologicalSpace G]
    [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N] {M : Type*}
    [AddCommGroup M] [DistribMulAction G M] (E : GroupExt G Q N)
    (hcont : ∀ g : G, Continuous (E.conj g)) (g : G) : Cochain1 N M →+ Cochain1 N M :=
  (LocallyConstant.mapAddMonoidHom
      { toFun := fun m : M => g • m
        map_zero' := smul_zero g
        map_add' := fun m n => smul_add g m n }).comp
    (LocallyConstant.comapAddMonoidHom (⟨E.conj g⁻¹, hcont g⁻¹⟩ : C(N, N)))

@[simp] lemma conjCochainHom_apply {G Q N : Type*} [Group G] [TopologicalSpace G]
    [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N] {M : Type*}
    [AddCommGroup M] [DistribMulAction G M] (E : GroupExt G Q N)
    (hcont : ∀ g : G, Continuous (E.conj g)) (g : G) (φ : Cochain1 N M) :
    conjCochainHom E hcont g φ = conjCochain E hcont g φ := rfl

/-- The conjugation action of `G` on `1`-cocycles on `N`. -/
noncomputable def conjZ1Map {G Q N : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction N M]
    [IsDiscreteGModule N M] (E : GroupExt G Q N) (hcont : ∀ g : G, Continuous (E.conj g))
    (hcompN : ∀ (n : N) (m : M), n • m = E.i n • m) (g : G) : Z1 N M →+ Z1 N M :=
  AddMonoidHom.codRestrict ((conjCochainHom E hcont g).comp (Z1 N M).subtype) (Z1 N M) fun z =>
    mem_Z1.mpr (isCocycle1_conjCochain E hcompN hcont g (mem_Z1.mp z.2))

@[simp] lemma conjZ1Map_coe {G Q N : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction N M]
    [IsDiscreteGModule N M] (E : GroupExt G Q N) (hcont : ∀ g : G, Continuous (E.conj g))
    (hcompN : ∀ (n : N) (m : M), n • m = E.i n • m) (g : G) (z : Z1 N M) :
    ((conjZ1Map E hcont hcompN g z : Z1 N M) : Cochain1 N M) =
      conjCochain E hcont g (z : Cochain1 N M) := rfl

/-- The conjugation action of `G` on `H¹(N,M)`. -/
noncomputable def conjH1Map {G Q N : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    [DistribMulAction N M] [IsDiscreteGModule N M] (E : GroupExt G Q N)
    (hcont : ∀ g : G, Continuous (E.conj g))
    (hcompN : ∀ (n : N) (m : M), n • m = E.i n • m) (g : G) : H1 N M →+ H1 N M :=
  QuotientAddGroup.map (B1' N M) (B1' N M) (conjZ1Map E hcont hcompN g) fun z hz => by
    rw [mem_B1'] at hz
    show (conjZ1Map E hcont hcompN g z : Cochain1 N M) ∈ B1 N M
    obtain ⟨m, hm⟩ := hz
    refine ⟨g • m, ?_⟩
    refine LocallyConstant.coe_inj.mp ?_
    rw [conjZ1Map_coe, ← hm, conjCochain_coboundary E hcompN hcont g m]
    rfl

@[simp] lemma conjH1Map_mk {G Q N : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    [DistribMulAction N M] [IsDiscreteGModule N M] (E : GroupExt G Q N)
    (hcont : ∀ g : G, Continuous (E.conj g))
    (hcompN : ∀ (n : N) (m : M), n • m = E.i n • m) (g : G) (z : Z1 N M) :
    conjH1Map E hcont hcompN g (H1.mk z) = H1.mk (conjZ1Map E hcont hcompN g z) := rfl

/-- The invariants `H¹(N,M)^G` of the conjugation action: the third term of the five term
sequence. -/
def H1Invariants {G Q N : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction N M]
    [IsDiscreteGModule N M] (E : GroupExt G Q N) (hcont : ∀ g : G, Continuous (E.conj g))
    (hcompN : ∀ (n : N) (m : M), n • m = E.i n • m) : AddSubgroup (H1 N M) where
  carrier := {x | ∀ g : G, conjH1Map E hcont hcompN g x = x}
  zero_mem' := by
    intro g
    rw [← H1.mk_zero (G := N) (M := M), conjH1Map_mk, map_zero, H1.mk_zero]
  add_mem' := by
    intro x y hx hy g
    rw [map_add, hx g, hy g]
  neg_mem' := by
    intro x hx g
    rw [map_neg, hx g]

@[simp] lemma mem_H1Invariants {G Q N : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    [DistribMulAction N M] [IsDiscreteGModule N M] (E : GroupExt G Q N)
    (hcont : ∀ g : G, Continuous (E.conj g))
    (hcompN : ∀ (n : N) (m : M), n • m = E.i n • m) {x : H1 N M} :
    x ∈ H1Invariants E hcont hcompN ↔ ∀ g : G, conjH1Map E hcont hcompN g x = x := Iff.rfl

end Work.ConCohomology
