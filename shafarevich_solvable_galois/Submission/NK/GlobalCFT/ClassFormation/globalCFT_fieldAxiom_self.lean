/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.ClassFormation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The field axiom for the trivial extension `K / K`

The field axiom of a class formation for the idèle class groups is the statement that the norm
subgroup `N_{L/K} C_L` has index `[L : K]` in `C_K` (`NK.GlobalCFT.FieldAxiom`).  For the
trivial extension `L = K` this is a triviality: the norm `N_{K/K}` is the identity on both the
idèles and the idèle classes, so the norm subgroup is everything and its index is `1 = [K : K]`.

This file proves that, unconditionally, by descending to the level of the componentwise norm
formula `NK.GlobalCFT.Idele.normIdeleFun`.  At a place `v` of `K` the fibre of `v` under the
extension `K / K` is the singleton `{v}`, and the local norm `N_{K_v/K_v}` is the identity; hence
the product formula collapses to the identity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.ClassFormation

/-! ### Places of the trivial extension -/

/-- The infinite place `v` of `K` lies over itself, for the trivial extension `K / K`. -/
private lemma liesOver_self_infinite (K : Type) [Field K] [NumberField K] (v : InfinitePlace K) :
    InfinitePlace.LiesOver (K := K) (L := K) v v :=
  (Norm.liesOver_iff_comap_eq v v).mpr (InfinitePlace.comap_id v)

/-- A height-one prime of `𝓞 K` lies over itself, for the trivial extension `K / K`. -/
private lemma liesOver_self_finite (K : Type) [Field K] [NumberField K]
    (Q : HeightOneSpectrum (𝓞 K)) : Q.asIdeal.LiesOver Q.asIdeal :=
  (Norm.liesOver_iff_under_eq Q.asIdeal Q.asIdeal).mpr (by
    rw [Ideal.under_def, Algebra.algebraMap_self, Ideal.comap_id])

/-- The fibre of an infinite place of `K` over itself is the singleton `{v}`, for `K / K`. -/
private lemma fiberInfinite_self (K : Type) [Field K] [NumberField K] (v : InfinitePlace K) :
    Place.fiberInfinite (K := K) (L := K) v = {v} := by
  ext w
  rw [Place.mem_fiberInfinite, Finset.mem_singleton]
  constructor
  · intro h
    have h1 := (Norm.liesOver_iff_comap_eq (K := K) (L := K) w v).mp h
    have h2 : w.comap (algebraMap K K) = w := InfinitePlace.comap_id w
    rw [h2] at h1
    exact h1
  · intro h
    rw [h]
    exact liesOver_self_infinite K v

/-- The fibre of a prime of `𝓞 K` over itself is the singleton `{Q}`, for `K / K`. -/
private lemma primesOverFinite_self (K : Type) [Field K] [NumberField K]
    (Q : HeightOneSpectrum (𝓞 K)) :
    Place.primesOverFinite (K := K) (L := K) Q = {Q} := by
  ext q
  rw [Place.mem_primesOverFinite, Finset.mem_singleton]
  constructor
  · intro h
    have h2 : q.asIdeal.under (𝓞 K) = q.asIdeal := by
      rw [Ideal.under_def, Algebra.algebraMap_self, Ideal.comap_id]
    exact HeightOneSpectrum.ext (h.over.trans h2).symm
  · intro h
    rw [h]
    exact liesOver_self_finite K Q

/-! ### The local norms of the trivial extension -/

/-- The map `K_v → K_v` induced by the identity `K → K` is the identity, at an infinite place. -/
private lemma completionMap_self (K : Type) [Field K] [NumberField K] (w : InfinitePlace K)
    (h : InfinitePlace.LiesOver (K := K) (L := K) w w) :
    @NumberField.LiesOver.completionMap K K _ _ _ w w h = RingHom.id w.Completion := by
  apply RingHom.ext
  intro x
  induction x using NumberField.InfinitePlace.Completion.induction_on with
  | hp => exact isClosed_eq (NumberField.LiesOver.continuous_completionMap) continuous_id
  | ih a =>
      rw [NumberField.LiesOver.completionMap_coe]
      rfl

/-- The local norm `N_{K_v/K_v}` of the trivial extension is the identity, at an infinite place. -/
private lemma localNormInfinite_self (K : Type) [Field K] [NumberField K] (w : InfinitePlace K)
    (h : InfinitePlace.LiesOver (K := K) (L := K) w w) :
    ∀ y : w.Completionˣ, @Place.localNormInfinite K _ K _ _ w w h y = y := by
  intro y
  unfold Place.localNormInfinite
  rw [completionMap_self K w h]
  rw [Algebra.norm_self]
  rfl

/-- The map `K_Q → K_Q` induced by the identity `K → K` is the identity, at a finite place. -/
private lemma adicCompletionMap_self (K : Type) [Field K] [NumberField K]
    (Q : HeightOneSpectrum (𝓞 K)) (h : Q.asIdeal.LiesOver Q.asIdeal) :
    Commons.RingTheory.Henselian.adicCompletionMap Q Q h = RingHom.id (Q.adicCompletion K) := by
  apply RingHom.ext
  intro x
  have hclosed : IsClosed {x : Q.adicCompletion K |
      Commons.RingTheory.Henselian.adicCompletionMap Q Q h x = x} :=
    isClosed_eq (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q Q h) continuous_id
  have hd : DenseRange (algebraMap K (Q.adicCompletion K)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K Q
  refine hd.induction_on x hclosed ?_
  intro a
  exact Commons.RingTheory.Henselian.adicCompletionMap_apply Q Q h a

/-- The local norm `N_{K_Q/K_Q}` of the trivial extension is the identity, at a finite place. -/
private lemma localNormFinite_self (K : Type) [Field K] [NumberField K]
    (Q : HeightOneSpectrum (𝓞 K)) (h : Q.asIdeal.LiesOver Q.asIdeal) :
    ∀ y : (Q.adicCompletion K)ˣ, @Place.localNormFinite K _ _ K _ _ _ Q Q h y = y := by
  intro y
  unfold Place.localNormFinite
  rw [adicCompletionMap_self K Q h]
  rw [Algebra.norm_self]
  rfl

/-! ### The norm of the trivial extension -/

/-- The componentwise norm formula of the trivial extension `K / K` is the identity. -/
private lemma normIdeleFun_self (K : Type) [Field K] [NumberField K] (x : Idele K) (v : Place K) :
    Idele.normIdeleFun (K := K) (L := K) x v = x v := by
  classical
  cases v with
  | inl w =>
      rw [Idele.normIdeleFun_ofInfinite]
      have hw : w ∈ Place.fiberInfinite (K := K) (L := K) w :=
        (Place.mem_fiberInfinite).mpr (liesOver_self_infinite K w)
      refine (Finset.prod_eq_single_of_mem
        (⟨w, hw⟩ : {x // x ∈ Place.fiberInfinite (K := K) (L := K) w})
        (Finset.mem_attach _ _) ?_).trans ?_
      · intro b _ hne
        exact absurd (Subtype.ext (by
          have h1 := (Norm.liesOver_iff_comap_eq (K := K) (L := K) b.1 w).mp
            ((Place.mem_fiberInfinite).mp b.2)
          have h2 : b.1.comap (algebraMap K K) = b.1 := InfinitePlace.comap_id b.1
          rw [h2] at h1
          exact h1)) hne
      · exact localNormInfinite_self K w ((Place.mem_fiberInfinite).mp hw) (x (Place.ofInfinite w))
  | inr Q =>
      rw [Idele.normIdeleFun_ofFinite]
      have hQ : Q ∈ Place.primesOverFinite (K := K) (L := K) Q :=
        (Place.mem_primesOverFinite).mpr (liesOver_self_finite K Q)
      refine (Finset.prod_eq_single_of_mem
        (⟨Q, hQ⟩ : {x // x ∈ Place.primesOverFinite (K := K) (L := K) Q})
        (Finset.mem_attach _ _) ?_).trans ?_
      · intro b _ hne
        exact absurd (Subtype.ext (HeightOneSpectrum.ext (by
          have h1 := ((Place.mem_primesOverFinite).mp b.2).over
          have h2 : b.1.asIdeal.under (𝓞 K) = b.1.asIdeal := by
            rw [Ideal.under_def, Algebra.algebraMap_self, Ideal.comap_id]
          exact (h1.trans h2).symm))) hne
      · exact localNormFinite_self K Q ((Place.mem_primesOverFinite).mp hQ) (x (Place.ofFinite Q))

/-- The idèlic norm of the trivial extension `K / K` is the identity. -/
private lemma normIdeleHom_self (K : Type) [Field K] [NumberField K] (x : Idele K) :
    Idele.normIdeleHom (K := K) (L := K) x = x :=
  Idele.ext fun v => normIdeleFun_self K x v

/-- The norm subgroup `N_{K/K} C_K` of the trivial extension is the whole idèle class group. -/
private lemma normClassSubgroup_self (K : Type) [Field K] [NumberField K] :
    Idele.normClassSubgroup (K := K) (L := K) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro q
  rw [Idele.normClassSubgroup, Subgroup.mem_map]
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K q
  refine ⟨x, ?_, rfl⟩
  rw [Idele.mem_normImage]
  exact ⟨x, fun v => (normIdeleFun_self K x v).symm⟩

/-! ### The field axiom -/

/-- **The field axiom holds for the trivial extension `K / K`**: the norm subgroup `N_{K/K} C_K`
is all of `C_K`, so its index is `1 = [K : K]`. -/
theorem globalCFT_fieldAxiom_self (K : Type) [Field K] [NumberField K] : FieldAxiom K K := by
  have htop := normClassSubgroup_self K
  refine ⟨?_, ?_⟩
  · rw [htop]
    exact Subgroup.finiteIndex_iff.mpr (by rw [Subgroup.index_top]; exact one_ne_zero)
  · rw [htop, Subgroup.index_top, Module.finrank_self]

end NK.GlobalCFT.ClassFormation
