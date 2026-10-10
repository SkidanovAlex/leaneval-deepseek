import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.GlobalCFT.GaloisIdeles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The composition law for the canonical local isomorphisms `L_v ≃+* L_{σ v}`

For a finite extension `L / K` of number fields, `Gal(L/K) = (L ≃ₐ[K] L)` acts on the places of
`L`, and for `σ : Gal(L/K)` and a place `v` of `L` there is a canonical isomorphism of local
fields

`NK.GlobalCFT.Place.localRingEquiv σ v : L_v ≃+* L_{σ v}`

(archimedean case: `NK.GlobalCFT.Galois.globalCFT_infiniteCongrEquiv`, nonarchimedean case:
`NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv`).  This file proves that this construction is
compatible with composition of Galois elements: the local isomorphism attached to `σ' * σ` is the
composite of the ones attached to `σ` and `σ'`.

The subtlety is a transport issue.  The places `σ' • (σ • v)` and `(σ' * σ) • v` are equal but not
*definitionally* equal, while the type `L_w` of the local field is a `match` on the place `w`; the
two sides of the identity therefore live a priori in different fibres of the family `w ↦ L_w` and
the statement transports along the equality `h` of places.  The proof is a density argument: after
moving the transport out of the way, both sides are continuous ring homomorphisms out of `L_v`
which agree on the dense image of `L` (see `NK.GlobalCFT.Place.localRingEquiv_algebraMap`), hence
are equal.

## Main results

* `NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp`: the composition law.
* `NK.GlobalCFT.Galois.denseRange_algebraMap_localField`: `L` is dense in `L_v`.
* `NK.GlobalCFT.Galois.continuous_localRingEquiv`: `localRingEquiv σ v` is continuous.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Galois

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### Transport along an equality of places

The local field `L_v` is defined by a `match` on the place `v`, so distinct places give distinct
types and equalities of places have to be transported along.  The following elementary lemmas
record that this transport is compatible with the canonical embeddings of `L` and with
continuity. -/

/-- Transporting an element of a local field along an equality of places commutes with the
canonical embeddings of `L`. -/
lemma localField_cast_algebraMap {a b : Place L} (h : a = b) (x : L) :
    h ▸ (algebraMap L (Place.localField L a) x) = algebraMap L (Place.localField L b) x := by
  cases h; rfl

/-- Transporting a continuous function along an equality of places, in pointwise form. -/
lemma continuous_localField_cast {a b : Place L} (h : a = b) {X : Type*} [TopologicalSpace X]
    {f : X → Place.localField L a} (hf : Continuous f) : Continuous (fun y => h ▸ f y) := by
  cases h; simpa using hf

/-- Moving a transport from one side of an equation to the other. -/
lemma localField_cast_eq_iff {a b : Place L} (h : a = b) (Z : Place.localField L b)
    (Y : Place.localField L a) : (Z = h ▸ Y) ↔ (h.symm ▸ Z = Y) := by
  cases h; rfl

/-! ### Density of `L` in `L_v` and continuity of the local isomorphisms -/

/-- The image of `L` in the local field `L_v` is dense, for every place `v` of `L`. -/
lemma denseRange_algebraMap_localField (v : Place L) :
    DenseRange (algebraMap L (Place.localField L v)) := by
  cases v with
  | inl w =>
      -- Archimedean place: `L` is dense in `WithAbs w`, and `WithAbs w` in its completion.
      have h1 : DenseRange (fun x : L => (WithAbs.toAbs w.1 x : w.1.Completion)) :=
        DenseRange.comp (g := fun y : WithAbs w.1 => (y : w.1.Completion)) (f := WithAbs.toAbs w.1)
          (UniformSpace.Completion.denseRange_coe (α := WithAbs w.1))
          (WithAbs.toAbs_bijective w.1).surjective.denseRange
          (UniformSpace.Completion.continuous_coe (WithAbs w.1))
      have h2 : DenseRange (fun x : L => (NumberField.InfinitePlace.Completion.ofCompletion (v := w)
            ((WithAbs.toAbs w.1 x : WithAbs w.1) : w.1.Completion))) :=
        DenseRange.comp (g := NumberField.InfinitePlace.Completion.ofCompletion (v := w))
          (f := fun x : L => (WithAbs.toAbs w.1 x : WithAbs w.1))
          (by simpa using (NumberField.InfinitePlace.Completion.ofCompletion_surjective w).denseRange)
          h1
          (NumberField.InfinitePlace.Completion.continuous_ofCompletion w)
      have hfun : ⇑(algebraMap L w.Completion) = fun x : L =>
          (NumberField.InfinitePlace.Completion.ofCompletion (v := w)
            ((WithAbs.toAbs w.1 x : WithAbs w.1) : w.1.Completion)) := by
        funext x
        rw [NumberField.InfinitePlace.Completion.algebraMap_apply]
      rwa [hfun]
  | inr q =>
      -- Nonarchimedean place: `algebraMap L (q.adicCompletion L)` is the coercion of `L` into the
      -- `q`-adic completion, which has dense range.
      have hdense : DenseRange (fun y : L => (y : q.adicCompletion L)) := by
        have h := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) L q
        rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion] at h
        simpa using h
      have hfun : (⇑(algebraMap L (q.adicCompletion L)) : L → q.adicCompletion L) =
          fun y : L => (y : q.adicCompletion L) := by
        funext y
        exact globalCFT_algebraMap_eq_coe q y
      rw [hfun]
      exact hdense

/-- The canonical isomorphism of local fields `L_v ≃+* L_{σ v}` is continuous. -/
lemma continuous_localRingEquiv (σ : L ≃ₐ[K] L) (v : Place L) :
    Continuous (Place.localRingEquiv σ v) := by
  cases v with
  | inl w =>
      change Continuous (globalCFT_infiniteCongrEquiv σ w)
      have h1 : Continuous (NumberField.InfinitePlace.Completion.equiv w) := by
        change Continuous (NumberField.InfinitePlace.Completion.toCompletion (v := w))
        exact NumberField.InfinitePlace.Completion.continuous_toCompletion w
      have h3 : Continuous (NumberField.InfinitePlace.Completion.equiv (σ • w)).symm := by
        change Continuous (NumberField.InfinitePlace.Completion.ofCompletion (v := σ • w))
        exact NumberField.InfinitePlace.Completion.continuous_ofCompletion (σ • w)
      have h2 : Continuous (UniformSpace.Completion.mapRingEquiv (globalCFT_withAbsCongrEquiv σ w)
          (globalCFT_isometry_withAbsCongrEquiv σ w).continuous
          (globalCFT_isometry_withAbsCongrEquiv_symm σ w).continuous) := by
        rw [show ⇑(UniformSpace.Completion.mapRingEquiv (globalCFT_withAbsCongrEquiv σ w)
            (globalCFT_isometry_withAbsCongrEquiv σ w).continuous
            (globalCFT_isometry_withAbsCongrEquiv_symm σ w).continuous)
            = UniformSpace.Completion.map (globalCFT_withAbsCongrEquiv σ w) from by
          funext a; rw [UniformSpace.Completion.mapRingEquiv_apply]]
        exact UniformSpace.Completion.continuous_map
      have hfun : ⇑(globalCFT_infiniteCongrEquiv σ w) = fun x =>
          (NumberField.InfinitePlace.Completion.equiv (σ • w)).symm
            (UniformSpace.Completion.mapRingEquiv (globalCFT_withAbsCongrEquiv σ w)
              (globalCFT_isometry_withAbsCongrEquiv σ w).continuous
              (globalCFT_isometry_withAbsCongrEquiv_symm σ w).continuous
              ((NumberField.InfinitePlace.Completion.equiv w) x)) := by
        funext x
        simp [globalCFT_infiniteCongrEquiv, RingEquiv.trans_apply]
      rw [hfun]
      exact h3.comp (h2.comp h1)
  | inr q =>
      change Continuous (globalCFT_adicCongrEquiv σ q)
      exact globalCFT_adicCongrEquiv_continuous σ q

/-! ### The composition law -/

/-- The canonical isomorphism of local fields `L_v ≃+* L_{σ v}` is compatible with composition in
`Gal(L/K)`: the local isomorphism attached to `σ' * σ` is the composite of the local isomorphisms
attached to `σ` and `σ'`.  The equality `h : σ' • (σ • v) = (σ' * σ) • v` of places is used to
identify the two fibres of the family `w ↦ L_w`. -/
theorem globalCFT_localRingEquiv_comp {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ σ' : L ≃ₐ[K] L) (v : NK.GlobalCFT.Place L)
    (h : σ' • (σ • v) = (σ' * σ) • v) (x : NK.GlobalCFT.Place.localField L v) :
    NK.GlobalCFT.Place.localRingEquiv (σ' * σ) v x =
      h ▸ (NK.GlobalCFT.Place.localRingEquiv σ' (σ • v))
        (NK.GlobalCFT.Place.localRingEquiv σ v x) := by
  -- Move the transport to the left hand side.
  refine (localField_cast_eq_iff h _ _).mpr ?_
  -- Both sides are continuous functions `L_v → L_{σ' • (σ • v)}` agreeing on the dense image of
  -- `L` in `L_v`; hence they are equal.
  have hdense : DenseRange (algebraMap L (Place.localField L v)) :=
    denseRange_algebraMap_localField v
  have hcont₁ : Continuous (fun y => h.symm ▸ ((Place.localRingEquiv (σ' * σ) v) y)) :=
    continuous_localField_cast h.symm (continuous_localRingEquiv (σ' * σ) v)
  have hcont₂ : Continuous (fun y => (Place.localRingEquiv σ' (σ • v))
      ((Place.localRingEquiv σ v) y)) :=
    (continuous_localRingEquiv σ' (σ • v)).comp (continuous_localRingEquiv σ v)
  have hfun : (fun y => h.symm ▸ ((Place.localRingEquiv (σ' * σ) v) y))
      = fun y => (Place.localRingEquiv σ' (σ • v)) ((Place.localRingEquiv σ v) y) := by
    refine DenseRange.equalizer hdense hcont₁ hcont₂ ?_
    funext y
    simp only [Function.comp_apply]
    rw [Place.localRingEquiv_algebraMap (σ' * σ) v y,
      localField_cast_algebraMap h.symm ((σ' * σ) y),
      Place.localRingEquiv_algebraMap σ v y,
      Place.localRingEquiv_algebraMap σ' (σ • v) (σ y), AlgEquiv.mul_apply]
  exact congrFun hfun x

end NK.GlobalCFT.Galois
