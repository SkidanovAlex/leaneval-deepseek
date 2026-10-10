import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.LTDDefs.H3bridge.extendFun3_mem_coboundaries3
import Submission.Work.SSGRoute.LTDDefs.H3bridge.extendFun3_mem_lcCocycles3
import Submission.Work.SSGRoute.LTDDefs.H3bridge.restrictFun3_mem_B3
import Submission.Work.SSGRoute.LTDDefs.H3loc.restrictFun3_mem_Z3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `H³` model bridge: local `H3loc` versus continuous `H³(↥H, M)`

`LTDDefs/Basic.lean` and `kummerBase_euler_h3loc.lean` define the local cohomology `H3loc` of a
subgroup `H ≤ G_k = Ω ≃ₐ[k] Ω` through functions on the *whole* group `G_k` whose `3`-cocycle and
local-constancy conditions are imposed only on `H`.  Mirroring the degree-`2` bridge
(`LTDDefs/H2locEquivH2.lean`), this file shows that restricting such a cocycle to
`↥H × ↥H × ↥H` and extending a continuous `3`-cocycle of `↥H` by `0` off `H` are inverse
operations modulo coboundaries, so that

`H3loc p k Ω K M H ≃+ Work.SSGRoute.H3 (M := M) ↥H`

for every closed subgroup `H ≤ G_k` and every action of `↥H` on `M` compatible with the action of
`Gal(K/k)` through `res k K`.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.LTDDefs

noncomputable section

namespace H3bridge

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]

/-- The quotient submodule exhibiting `H3loc` as a quotient of the locally constant `3`-cocycles
on `G_k` (the submodule `H3loc` is the quotient by). -/
abbrev cobQ3 (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : Submodule (ZMod p) ↥(lcCocycles3 p k Ω K M H) :=
  Submodule.comap (lcCocycles3 p k Ω K M H).subtype (coboundaries3 p k Ω K M H)

/-- The quotient subgroup exhibiting `H³(↥H, M)` as a quotient of the continuous `3`-cocycles
of `↥H`. -/
abbrev B3Q (G : Type) [Group G] [TopologicalSpace G] (M : Type) [AddCommGroup M]
    [DistribMulAction G M] : AddSubgroup ↥(Work.SSGRoute.Z3 (M := M) G) :=
  (Work.SSGRoute.B3 (M := M) G).comap (Work.SSGRoute.Z3 (M := M) G).subtype

/-- **The restriction map on `3`-cocycles**: restricting a locally constant `3`-cocycle on `H`
(a function on `G_k × G_k × G_k`) to `↥H × ↥H × ↥H` yields a continuous `3`-cocycle of `↥H`. -/
def restrictHom3
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    ↥(lcCocycles3 p k Ω K M H) →+ ↥(Work.SSGRoute.Z3 (M := M) ↥H) where
  toFun c := ⟨Work.SSGRoute.LTDDefs.H3loc.restrictFun3 H c.1,
    Work.SSGRoute.LTDDefs.H3loc.restrictFun3_mem_Z3 p k Ω K M H hcompat c.2⟩
  map_zero' := Subtype.ext (funext fun q => by obtain ⟨g, h, l⟩ := q; rfl)
  map_add' a b := Subtype.ext (funext fun q => by obtain ⟨g, h, l⟩ := q; rfl)

/-- **The extension by `0` map on `3`-cocycles**: extending a continuous `3`-cocycle of `↥H` by
`0` off `H` yields a locally constant `3`-cocycle on `H` (a function on `G_k³`). -/
def extendHom3
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    ↥(Work.SSGRoute.Z3 (M := M) ↥H) →+ ↥(lcCocycles3 p k Ω K M H) where
  toFun c := ⟨Work.SSGRoute.LTDDefs.H3loc.extendFun3 H c.1,
    Work.SSGRoute.LTDDefs.H3bridge.extendFun3_mem_lcCocycles3 p k Ω K M H hH hcompat c.2⟩
  map_zero' := Subtype.ext (by
    show Work.SSGRoute.LTDDefs.H3loc.extendFun3 H
        ((0 : ↥(Work.SSGRoute.Z3 (M := M) ↥H)).1) = 0
    rw [show ((0 : ↥(Work.SSGRoute.Z3 (M := M) ↥H)).1 : ↥H × ↥H × ↥H → M) = 0 from rfl]
    exact Work.SSGRoute.LTDDefs.H3loc.extendFun3_zero H)
  map_add' a b := Subtype.ext (by
    show Work.SSGRoute.LTDDefs.H3loc.extendFun3 H
        ((a + b : ↥(Work.SSGRoute.Z3 (M := M) ↥H)).1)
      = Work.SSGRoute.LTDDefs.H3loc.extendFun3 H a.1
        + Work.SSGRoute.LTDDefs.H3loc.extendFun3 H b.1
    rw [show ((a + b : ↥(Work.SSGRoute.Z3 (M := M) ↥H)).1 : ↥H × ↥H × ↥H → M)
        = a.1 + b.1 from rfl]
    exact Work.SSGRoute.LTDDefs.H3loc.extendFun3_add H)

/-- The extension of the restriction of a locally constant `3`-cocycle differs from it by a
coboundary: the difference vanishes on `H`. -/
theorem extendFun3_restrictFun3_sub_mem (c : ↥(lcCocycles3 p k Ω K M H)) :
    Work.SSGRoute.LTDDefs.H3loc.extendFun3 H
      (Work.SSGRoute.LTDDefs.H3loc.restrictFun3 H c.1) - c.1
      ∈ coboundaries3 p k Ω K M H := by
  refine ⟨0, ?_, ?_⟩
  · exact ⟨⊤, isOpen_univ, fun g _ h _ u _ v _ _ _ => rfl⟩
  · intro g hg h hh l hl
    have hval : Work.SSGRoute.LTDDefs.H3loc.extendFun3 H
        (Work.SSGRoute.LTDDefs.H3loc.restrictFun3 H c.1) g h l = c.1 g h l := by
      rw [Work.SSGRoute.LTDDefs.H3loc.extendFun3_apply H
          (Work.SSGRoute.LTDDefs.H3loc.restrictFun3 H c.1) hg hh hl,
        Work.SSGRoute.LTDDefs.H3loc.restrictFun3_apply]
    show (Work.SSGRoute.LTDDefs.H3loc.extendFun3 H
        (Work.SSGRoute.LTDDefs.H3loc.restrictFun3 H c.1) - c.1) g h l
      = Work.SSGRoute.dCochain2 p k Ω K M 0 g h l
    change Work.SSGRoute.LTDDefs.H3loc.extendFun3 H
        (Work.SSGRoute.LTDDefs.H3loc.restrictFun3 H c.1) g h l - c.1 g h l
      = Work.SSGRoute.dCochain2 p k Ω K M 0 g h l
    rw [hval, Work.SSGRoute.dCochain2_apply]
    simp

/-- The restriction of the extension of a continuous `3`-cocycle of `↥H` is the original cocycle:
the difference is `0`, hence a coboundary. -/
theorem restrictHom3_extendHom3_sub_mem
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (c : ↥(Work.SSGRoute.Z3 (M := M) ↥H)) :
    restrictHom3 p k Ω K M H hcompat (extendHom3 p k Ω K M H hH hcompat c) - c ∈
      B3Q ↥H M := by
  have hzero : restrictHom3 p k Ω K M H hcompat
      (extendHom3 p k Ω K M H hH hcompat c) - c = 0 := by
    refine Subtype.ext ?_
    show Work.SSGRoute.LTDDefs.H3loc.restrictFun3 H
        (Work.SSGRoute.LTDDefs.H3loc.extendFun3 H c.1) - c.1 = 0
    rw [Work.SSGRoute.LTDDefs.H3loc.restrictFun3_extendFun3 H c.1, sub_self]
  rw [hzero]
  exact (B3Q ↥H M).zero_mem

/-- **The restriction map on local `H³`-groups**: restricting a locally constant `3`-cocycle on
`H` (a function on `G_k³`) to `↥H` and passing to cohomology. -/
def bridgeFwd3
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    Work.SSGRoute.H3loc p k Ω K M H →+ Work.SSGRoute.H3 (M := M) ↥H :=
  QuotientAddGroup.map (cobQ3 p k Ω K M H).toAddSubgroup (B3Q ↥H M)
    (restrictHom3 p k Ω K M H hcompat) (by
      intro c hc
      exact Work.SSGRoute.LTDDefs.H3bridge.restrictFun3_mem_B3 p k Ω K M H hcompat c.2
        (Submodule.mem_comap.mp hc))

/-- **The inverse map on local `H³`-groups**: extending a continuous `3`-cocycle of `↥H` by `0`
off `H`, and passing to cohomology. -/
def bridgeBwd3
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    Work.SSGRoute.H3 (M := M) ↥H →+ Work.SSGRoute.H3loc p k Ω K M H :=
  QuotientAddGroup.map (B3Q ↥H M) (cobQ3 p k Ω K M H).toAddSubgroup
    (extendHom3 p k Ω K M H hH hcompat) (by
      intro c hc
      exact Work.SSGRoute.LTDDefs.H3bridge.extendFun3_mem_coboundaries3 p k Ω K M H hH hcompat
        c.2 (AddSubgroup.mem_comap.mp hc))

/-- **The model bridge for `H³`.**  The locally constant cohomology `H3loc` is the same as the
workspace's continuous-cochain model `Work.SSGRoute.H3 ↥H M`. -/
def H3locAddEquivH3
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    Work.SSGRoute.H3loc p k Ω K M H ≃+ Work.SSGRoute.H3 (M := M) ↥H where
  toFun := bridgeFwd3 p k Ω K M H hcompat
  invFun := bridgeBwd3 p k Ω K M H hH hcompat
  left_inv x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (p := cobQ3 p k Ω K M H) x
    show bridgeBwd3 p k Ω K M H hH hcompat
      (bridgeFwd3 p k Ω K M H hcompat (Submodule.Quotient.mk z)) = Submodule.Quotient.mk z
    have h1 : bridgeFwd3 p k Ω K M H hcompat (Submodule.Quotient.mk z)
        = QuotientAddGroup.mk' (B3Q ↥H M) (restrictHom3 p k Ω K M H hcompat z) :=
      QuotientAddGroup.map_mk' _ _ _ _ z
    have h2 : bridgeBwd3 p k Ω K M H hH hcompat
        (QuotientAddGroup.mk' (B3Q ↥H M) (restrictHom3 p k Ω K M H hcompat z))
        = Submodule.Quotient.mk (extendHom3 p k Ω K M H hH hcompat
            (restrictHom3 p k Ω K M H hcompat z)) :=
      QuotientAddGroup.map_mk' _ _ _ _ _
    rw [h1, h2, Submodule.Quotient.eq]
    refine Submodule.mem_comap.mpr ?_
    show Work.SSGRoute.LTDDefs.H3loc.extendFun3 H
        (Work.SSGRoute.LTDDefs.H3loc.restrictFun3 H
          (z : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)) -
      (z : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
        ∈ coboundaries3 p k Ω K M H
    exact extendFun3_restrictFun3_sub_mem p k Ω K M H z
  right_inv y := by
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective (B3Q ↥H M) y
    show bridgeFwd3 p k Ω K M H hcompat
      (bridgeBwd3 p k Ω K M H hH hcompat (QuotientAddGroup.mk' (B3Q ↥H M) c))
      = QuotientAddGroup.mk' (B3Q ↥H M) c
    have h1 : bridgeBwd3 p k Ω K M H hH hcompat (QuotientAddGroup.mk' (B3Q ↥H M) c)
        = Submodule.Quotient.mk (extendHom3 p k Ω K M H hH hcompat c) :=
      QuotientAddGroup.map_mk' _ _ _ _ _
    have h2 : bridgeFwd3 p k Ω K M H hcompat
        (Submodule.Quotient.mk (extendHom3 p k Ω K M H hH hcompat c))
        = QuotientAddGroup.mk' (B3Q ↥H M)
            (restrictHom3 p k Ω K M H hcompat (extendHom3 p k Ω K M H hH hcompat c)) :=
      QuotientAddGroup.map_mk' _ _ _ _ _
    have hd := restrictHom3_extendHom3_sub_mem p k Ω K M H hH hcompat c
    rw [h1, h2, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq]
    have hthis : -(restrictHom3 p k Ω K M H hcompat (extendHom3 p k Ω K M H hH hcompat c))
        + c = -(restrictHom3 p k Ω K M H hcompat (extendHom3 p k Ω K M H hH hcompat c) - c) := by
      abel
    rw [hthis]
    exact (B3Q ↥H M).neg_mem hd
  map_add' x y := (bridgeFwd3 p k Ω K M H hcompat).map_add x y

end H3bridge

theorem H3locEquivH3 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    Nonempty (Work.SSGRoute.H3loc p k Ω K M H ≃+ Work.SSGRoute.H3 (M := M) ↥H) :=
  ⟨H3bridge.H3locAddEquivH3 p k Ω K M H hH hcompat⟩

end

end Work.SSGRoute.LTDDefs
