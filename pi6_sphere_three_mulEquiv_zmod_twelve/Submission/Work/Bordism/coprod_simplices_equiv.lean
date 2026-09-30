import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.Pullback

/-!
# Singular simplices of a disjoint union

For topological spaces `X`, `Y` the `k`-th singular simplices of the coproduct `X ⊔ Y`
(disjoint union, with the sum topology) split as the disjoint union of the `k`-simplices of `X`
and those of `Y`:

`Work.Bordism.coprod_simplices_equiv`.

`TopCat.toSSet` is a right adjoint (the singular simplicial set functor is right adjoint to
geometric realization), so it does **not** preserve coproducts out of the box; the reason the
splitting nevertheless holds is that the standard simplex `Δᵏ` is connected, so that a continuous
map `Δᵏ ⟶ X ⊔ Y` has image entirely contained in one of the two summands.

The proof has three ingredients, isolated below.

* `exists_lift_sum` (and its bundled counterpart `sumToCM_surjective`): a continuous map from a
  connected space to a binary sum factors through one of the two inclusions.  This is the standard
  splitting of a preconnected subset of `X ⊕ Y`, Mathlib's `Sum.isConnected_iff`.
* `sumToCM` and its bijectivity: the natural map `C(T,X) ⊕ C(T,Y) ⟶ C(T, X ⊕ Y)` is bijective for
  connected `T`, which gives the levelwise splitting `C(T, X ⊕ Y) ≃ C(T,X) ⊕ C(T,Y)`
  (`sumCMEquiv`), i.e. the connectedness upgrades the product (the universal property of the
  coproduct) to a sum.
* `coprodHomeo`: the binary coproduct in `TopCat` is, concretely, the disjoint union with the sum
  topology; `TopCat.binaryCofan X Y` is a colimit cofan, so it is isomorphic to `X ⨿ Y`.

The `k`-simplices of a singular simplicial set are identified with the continuous maps from the
standard topological simplex by `TopCat.toSSetObjEquivT`, which is how the homeomorphism and the
connectedness input are transported to the statement.
-/

open CategoryTheory Limits Topology

namespace Work.Bordism

universe u

/-! ### Lifting a continuous map from a connected space into a sum -/

/-- A continuous map from a connected topological space to a binary sum `X ⊕ Y` lands entirely in
one of the two summands: it factors through `Sum.inl` or through `Sum.inr`. -/
theorem exists_lift_sum {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X]
    [TopologicalSpace Y] [ConnectedSpace T] {f : T → X ⊕ Y} (hf : Continuous f) :
    (∃ g : T → X, Continuous g ∧ f = Sum.inl ∘ g) ∨
      (∃ g : T → Y, Continuous g ∧ f = Sum.inr ∘ g) := by
  rcases Sum.isConnected_iff.1 (isConnected_range hf) with ⟨s, hs, hst⟩ | ⟨s, hs, hst⟩
  · left
    have hsub : Set.range f ⊆ Set.range (Sum.inl : X → X ⊕ Y) := by
      rw [hst]; exact Set.image_subset_range Sum.inl s
    rcases Set.range_subset_range_iff_exists_comp.1 hsub with ⟨g, hg⟩
    exact ⟨g, (Topology.IsEmbedding.continuous_iff (f := g) Topology.IsEmbedding.inl).mpr
      (hg ▸ hf), hg⟩
  · right
    have hsub : Set.range f ⊆ Set.range (Sum.inr : Y → X ⊕ Y) := by
      rw [hst]; exact Set.image_subset_range Sum.inr s
    rcases Set.range_subset_range_iff_exists_comp.1 hsub with ⟨g, hg⟩
    exact ⟨g, (Topology.IsEmbedding.continuous_iff (f := g) Topology.IsEmbedding.inr).mpr
      (hg ▸ hf), hg⟩

/-! ### The map `C(T,X) ⊕ C(T,Y) ⟶ C(T, X ⊕ Y)` -/

/-- The natural map sending a continuous map into `X` or into `Y` to the composite with the
corresponding inclusion of the sum. -/
noncomputable def sumToCM {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X]
    [TopologicalSpace Y] : C(T, X) ⊕ C(T, Y) → C(T, X ⊕ Y) :=
  Sum.elim (fun g => (⟨Sum.inl, continuous_inl⟩ : C(X, X ⊕ Y)).comp g)
           (fun h => (⟨Sum.inr, continuous_inr⟩ : C(Y, X ⊕ Y)).comp h)

/-- For connected `T`, `sumToCM` is injective: the two summands are disjoint in `C(T, X ⊕ Y)`. -/
theorem sumToCM_injective {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X]
    [TopologicalSpace Y] [ConnectedSpace T] : Function.Injective (@sumToCM T X Y _ _ _) := by
  intro a b hab
  cases a with
  | inl g =>
    cases b with
    | inl g' =>
      congr 1
      ext t
      exact Sum.inl.inj (DFunLike.congr_fun hab t)
    | inr h =>
      exfalso
      have h2 := DFunLike.congr_fun hab (Classical.arbitrary T)
      simp only [sumToCM, Sum.elim_inl, Sum.elim_inr, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk] at h2
      exact Sum.inl_ne_inr h2
  | inr h =>
    cases b with
    | inl g =>
      exfalso
      have h2 := DFunLike.congr_fun hab (Classical.arbitrary T)
      simp only [sumToCM, Sum.elim_inl, Sum.elim_inr, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk] at h2
      exact Sum.inr_ne_inl h2
    | inr h' =>
      congr 1
      ext t
      exact Sum.inr.inj (DFunLike.congr_fun hab t)

/-- For connected `T`, `sumToCM` is surjective: every continuous map into the sum factors through
one of the summands. -/
theorem sumToCM_surjective {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X]
    [TopologicalSpace Y] [ConnectedSpace T] : Function.Surjective (@sumToCM T X Y _ _ _) := by
  intro f
  rcases exists_lift_sum (T := T) (X := X) (Y := Y) f.continuous with
    ⟨g, hg, heq⟩ | ⟨h, hh, heq⟩
  · refine ⟨Sum.inl ⟨g, hg⟩, ?_⟩
    ext t
    simp only [sumToCM, Sum.elim_inl, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    exact (congrFun heq t).symm
  · refine ⟨Sum.inr ⟨h, hh⟩, ?_⟩
    ext t
    simp only [sumToCM, Sum.elim_inr, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    exact (congrFun heq t).symm

/-- For a connected space `T` and topological spaces `X`, `Y`, a continuous map `T → X ⊕ Y`
corresponds to a continuous map into `X` or into `Y`.  (This is the connectedness upgrade of the
universal property of the coproduct, which gives a *product* instead of a sum.) -/
noncomputable def sumCMEquiv {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X]
    [TopologicalSpace Y] [ConnectedSpace T] : C(T, X) ⊕ C(T, Y) ≃ C(T, X ⊕ Y) :=
  Equiv.ofBijective sumToCM ⟨sumToCM_injective, sumToCM_surjective⟩

/-! ### The coproduct of topological spaces as the disjoint union -/

/-- The binary coproduct in `TopCat` is homeomorphic to the disjoint union `X ⊕ Y` with the sum
topology: `TopCat.binaryCofan X Y` is a colimit cofan. -/
noncomputable def coprodHomeo (X Y : TopCat.{u}) :
    (↑(coprod X Y) : Type u) ≃ₜ (X ⊕ Y : Type u) :=
  TopCat.homeoOfIso (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (pair X Y))
    (TopCat.binaryCofanIsColimit X Y))

/-- Precomposition with a homeomorphism induces an equivalence of spaces of continuous maps. -/
noncomputable def homeoCMEquiv {A B S : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace S] (h : A ≃ₜ B) : C(S, A) ≃ C(S, B) where
  toFun f := (⟨⇑h, h.continuous⟩ : C(A, B)).comp f
  invFun g := (⟨⇑h.symm, h.symm.continuous⟩ : C(B, A)).comp g
  left_inv f := by ext s; simp
  right_inv g := by ext s; simp

/-! ### The statement -/

theorem coprod_simplices_equiv (X Y : TopCat) (k : ℕ) :
    Nonempty (((TopCat.toSSet.obj (CategoryTheory.Limits.coprod X Y)).obj
        (Opposite.op (SimplexCategory.mk k))) ≃
      (((TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk k))) ⊕
        ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk k))))) := by
  refine ⟨((TopCat.toSSetObjEquivT (CategoryTheory.Limits.coprod X Y)
      (Opposite.op (SimplexCategory.mk k))).trans
    (((homeoCMEquiv (coprodHomeo X Y)).trans
      (sumCMEquiv.symm)).trans
      (Equiv.sumCongr
        (TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk k))).symm
        (TopCat.toSSetObjEquivT Y (Opposite.op (SimplexCategory.mk k))).symm)))⟩

end Work.Bordism
