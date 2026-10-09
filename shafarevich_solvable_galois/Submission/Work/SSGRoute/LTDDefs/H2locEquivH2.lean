import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.LTDDefs.H1loc_iso_H1cont
import Submission.Work.SSGRoute.LTDDefs.H2locAux
import Submission.Work.SSGRoute.LTDDefs.H2loc.restrictFun2_mem_Z2
import Submission.Work.SSGRoute.LTDDefs.H2loc.restrictFun2_mem_B2
import Submission.Work.SSGRoute.LTDDefs.H2loc.extendFun2_mem_lcCocycles2
import Submission.Work.SSGRoute.LTDDefs.H2loc.extendFun2_mem_coboundaries2
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `H²` model bridge: local `H²` of a subgroup versus continuous `H²`

`LTDDefs/Basic.lean` defines the local cohomology `H2loc` of a subgroup `H ≤ G_k = Ω ≃ₐ[k] Ω`
through functions on the *whole* group `G_k` satisfying the `2`-cocycle and local-constancy
conditions only on `H`.  Mirroring `LTDDefs/H1loc_iso_H1cont.lean` (which does the same job in
degree `1`), this file shows that restricting such a cocycle to `H × H` and extending a
continuous `2`-cocycle of `H` by `0` off `H` are inverse operations modulo coboundaries, so that

`H2loc p k Ω K M H ≃+ Work.AbsoluteKummer.H2 ↥H M`

for every closed subgroup `H ≤ G_k` and every action of `↥H` on `M` compatible with the action of
`Gal(K/k)` through `res k K`.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.LTDDefs

open Work.SSGRoute

noncomputable section

/-- Restricting the extension by `0` of a `2`-cochain of a subgroup `H` gives the cochain back. -/
lemma restrictFun2_extendFun2_cancel {Γ : Type*} [Group Γ] {M : Type*} [Zero M]
    (H : Subgroup Γ) (c : ↥H × ↥H → M) : restrictFun2 H (extendFun2 H c) = c := by
  funext q
  obtain ⟨g, h⟩ := q
  rw [restrictFun2_apply, extendFun2_apply H c g.2 h.2]

section Bridge

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]

/-- **The restriction map on `2`-cocycles**: restricting a locally constant `2`-cocycle on `H`
(a function on `G_k × G_k`) to `↥H × ↥H` yields a continuous `2`-cocycle of `↥H`. -/
def restrictHom2
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    ↥(lcCocycles2 p k Ω K M H) →+ ↥(Work.AbsoluteKummer.Z2 ↥H M) where
  toFun c := ⟨restrictFun2 H c.1,
    H2loc.restrictFun2_mem_Z2 p k Ω K M H hcompat c.2⟩
  map_zero' := Subtype.ext (funext fun q => by obtain ⟨g, h⟩ := q; rfl)
  map_add' a b := Subtype.ext (funext fun q => by obtain ⟨g, h⟩ := q; rfl)

/-- **The extension by `0` map on `2`-cocycles**: extending a continuous `2`-cocycle of `↥H` by
`0` off `H` yields a locally constant `2`-cocycle on `H` (a function on `G_k × G_k`). -/
def extendHom2
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    ↥(Work.AbsoluteKummer.Z2 ↥H M) →+ ↥(lcCocycles2 p k Ω K M H) where
  toFun c := ⟨extendFun2 H c.1,
    H2loc.extendFun2_mem_lcCocycles2 p k Ω K M H hH hcompat c.2⟩
  map_zero' := Subtype.ext (by
    show extendFun2 H ((0 : ↥(Work.AbsoluteKummer.Z2 ↥H M)).1) = 0
    rw [show ((0 : ↥(Work.AbsoluteKummer.Z2 ↥H M)).1 : ↥H × ↥H → M) = 0 from rfl]
    exact extendFun2_zero H)
  map_add' a b := Subtype.ext (by
    show extendFun2 H ((a + b : ↥(Work.AbsoluteKummer.Z2 ↥H M)).1) =
      extendFun2 H a.1 + extendFun2 H b.1
    rw [show ((a + b : ↥(Work.AbsoluteKummer.Z2 ↥H M)).1 : ↥H × ↥H → M) = a.1 + b.1 from rfl]
    exact extendFun2_add H)

/-- The extension of the restriction of a locally constant `2`-cocycle differs from it by a
coboundary: the difference vanishes on `H`. -/
theorem extendFun2_restrictFun2_sub_mem (c : ↥(lcCocycles2 p k Ω K M H)) :
    extendFun2 H (restrictFun2 H c.1) - c.1 ∈ coboundaries2 p k Ω K M H := by
  refine ⟨0, ?_, ?_⟩
  · exact ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩
  · intro g hg h hh
    have hval : extendFun2 H (restrictFun2 H c.1) g h = c.1 g h := by
      rw [extendFun2_apply H (restrictFun2 H c.1) hg hh, restrictFun2_apply]
    have hzero : ((0 : (Ω ≃ₐ[k] Ω) → M) h) = 0 := Pi.zero_apply _
    have hzero2 : ((0 : (Ω ≃ₐ[k] Ω) → M) (g * h)) = 0 := Pi.zero_apply _
    have hzero3 : ((0 : (Ω ≃ₐ[k] Ω) → M) g) = 0 := Pi.zero_apply _
    rw [Pi.sub_apply, Pi.sub_apply, hval, hzero, hzero2, hzero3, smul_zero, sub_zero, add_zero]
    exact sub_self _

/-- The restriction of the extension of a continuous `2`-cocycle of `↥H` is the original cocycle:
the difference is `0`, hence a coboundary. -/
theorem restrictHom2_extendHom2_sub_mem
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (c : ↥(Work.AbsoluteKummer.Z2 ↥H M)) :
    restrictHom2 p k Ω K M H hcompat (extendHom2 p k Ω K M H hH hcompat c) - c ∈
      B2Q ↥H M := by
  have hzero : restrictHom2 p k Ω K M H hcompat (extendHom2 p k Ω K M H hH hcompat c) - c
      = 0 := by
    refine Subtype.ext ?_
    show restrictFun2 H (extendFun2 H c.1) - c.1 = (0 : ↥H × ↥H → M)
    rw [restrictFun2_extendFun2_cancel H c.1, sub_self]
  rw [hzero]
  exact (B2Q ↥H M).zero_mem

/-- **The restriction map on local `H²`-groups**: restricting a locally constant `2`-cocycle on
`H` (a function on `G_k × G_k`) to `↥H` and passing to cohomology. -/
def bridgeFwd2
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    H2loc p k Ω K M H →+ Work.AbsoluteKummer.H2 ↥H M :=
  QuotientAddGroup.map (cobQ2 p k Ω K M H).toAddSubgroup (B2Q ↥H M)
    (restrictHom2 p k Ω K M H hcompat) (by
      intro c hc
      exact H2loc.restrictFun2_mem_B2 p k Ω K M H hcompat c.2 (Submodule.mem_comap.mp hc))

/-- **The inverse map on local `H²`-groups**: extending a continuous `2`-cocycle of `↥H` by `0`
off `H`, and passing to cohomology. -/
def bridgeBwd2
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    Work.AbsoluteKummer.H2 ↥H M →+ H2loc p k Ω K M H :=
  QuotientAddGroup.map (B2Q ↥H M) (cobQ2 p k Ω K M H).toAddSubgroup
    (extendHom2 p k Ω K M H hH hcompat) (by
      intro c hc
      exact H2loc.extendFun2_mem_coboundaries2 p k Ω K M H hH hcompat c.2
        (AddSubgroup.mem_comap.mp hc))

/-- **The model bridge for `H²`.**  The locally constant cohomology `H2loc` of `LTDDefs/Basic.lean`
is the same as the workspace's continuous-cochain model `Work.AbsoluteKummer.H2 ↥H M`. -/
def H2locAddEquivH2
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    H2loc p k Ω K M H ≃+ Work.AbsoluteKummer.H2 ↥H M where
  toFun := bridgeFwd2 p k Ω K M H hcompat
  invFun := bridgeBwd2 p k Ω K M H hH hcompat
  left_inv x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (p := cobQ2 p k Ω K M H) x
    show bridgeBwd2 p k Ω K M H hH hcompat
      (bridgeFwd2 p k Ω K M H hcompat (Submodule.Quotient.mk z)) = Submodule.Quotient.mk z
    have h1 : bridgeFwd2 p k Ω K M H hcompat (Submodule.Quotient.mk z)
        = QuotientAddGroup.mk' (B2Q ↥H M) (restrictHom2 p k Ω K M H hcompat z) :=
      QuotientAddGroup.map_mk' _ _ _ _ z
    have h2 : bridgeBwd2 p k Ω K M H hH hcompat
        (QuotientAddGroup.mk' (B2Q ↥H M) (restrictHom2 p k Ω K M H hcompat z))
        = Submodule.Quotient.mk (extendHom2 p k Ω K M H hH hcompat
            (restrictHom2 p k Ω K M H hcompat z)) :=
      QuotientAddGroup.map_mk' _ _ _ _ _
    rw [h1, h2, Submodule.Quotient.eq]
    refine Submodule.mem_comap.mpr ?_
    show extendFun2 H (restrictFun2 H (z : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)) -
      (z : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) ∈ coboundaries2 p k Ω K M H
    exact extendFun2_restrictFun2_sub_mem p k Ω K M H z
  right_inv y := by
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective (B2Q ↥H M) y
    show bridgeFwd2 p k Ω K M H hcompat
      (bridgeBwd2 p k Ω K M H hH hcompat (QuotientAddGroup.mk' (B2Q ↥H M) c))
      = QuotientAddGroup.mk' (B2Q ↥H M) c
    have h1 : bridgeBwd2 p k Ω K M H hH hcompat (QuotientAddGroup.mk' (B2Q ↥H M) c)
        = Submodule.Quotient.mk (extendHom2 p k Ω K M H hH hcompat c) :=
      QuotientAddGroup.map_mk' _ _ _ _ _
    have h2 : bridgeFwd2 p k Ω K M H hcompat
        (Submodule.Quotient.mk (extendHom2 p k Ω K M H hH hcompat c))
        = QuotientAddGroup.mk' (B2Q ↥H M)
            (restrictHom2 p k Ω K M H hcompat (extendHom2 p k Ω K M H hH hcompat c)) :=
      QuotientAddGroup.map_mk' _ _ _ _ _
    have hd := restrictHom2_extendHom2_sub_mem p k Ω K M H hH hcompat c
    rw [h1, h2, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq]
    have hthis : -(restrictHom2 p k Ω K M H hcompat (extendHom2 p k Ω K M H hH hcompat c))
        + c = -(restrictHom2 p k Ω K M H hcompat (extendHom2 p k Ω K M H hH hcompat c) - c) := by
      abel
    rw [hthis]
    exact (B2Q ↥H M).neg_mem hd
  map_add' x y := (bridgeFwd2 p k Ω K M H hcompat).map_add x y

end Bridge

theorem H2locEquivH2 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    Nonempty (H2loc p k Ω K M H ≃+ Work.AbsoluteKummer.H2 ↥H M) :=
  ⟨H2locAddEquivH2 p k Ω K M H hH hcompat⟩

end

end Work.SSGRoute.LTDDefs
