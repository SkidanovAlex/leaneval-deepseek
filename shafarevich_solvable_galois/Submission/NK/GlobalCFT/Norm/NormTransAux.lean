/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transitivity of the idèlic norm: auxiliary lemmas

This file collects the ingredients of the proof that the idèlic norm is transitive in a tower
`M / L / K` of number fields:

* generic `Finset` lemmas converting products over `s.attach` into products with a
  `if h : a ∈ s` decoration, and re-indexing products along a disjoint fibre decomposition;
* the transitivity of `Place.LiesOver` for infinite places and the induced decomposition of the
  fibre of an infinite place of `K` in `M`;
* the transitivity of the local norms `Place.localNormInfinite`, `Place.localNormFinite`.

The main theorem `NK.GlobalCFT.Norm.globalCFT_normIdeleHom_trans` is proved from these.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace Finset

/-- A product over `s.attach` with a function depending on the membership proof equals the
product over `s` of the function decorated by `if h : a ∈ s then · else 1`. -/
theorem prod_attach_dite {ι M : Type*} [CommMonoid M] [DecidableEq ι] (s : Finset ι)
    (g : (a : ι) → a ∈ s → M) :
    ∏ a ∈ s.attach, g a.1 a.2 = ∏ a ∈ s, if h : a ∈ s then g a h else 1 := by
  classical
  rw [← Finset.prod_attach s (fun a => if h : a ∈ s then g a h else 1)]
  exact Finset.prod_congr rfl (fun a _ => by simp only [dif_pos a.2])

/-- A product over a disjoint fibre decomposition: if `T` is the disjoint union of the fibres
`F a` for `a ∈ S`, then a product over `T` equals the product over `S` of the products over the
fibres. -/
theorem prod_biUnion_congr {M : Type*} [CommMonoid M] {α β : Type*} [DecidableEq β]
    {S : Finset α} {T : Finset β} {F : α → Finset β}
    (hunion : S.biUnion F = T) (hdisj : (S : Set α).PairwiseDisjoint F)
    {g : α → β → M} {h : β → M} (hg : ∀ a ∈ S, ∀ b ∈ F a, g a b = h b) :
    (∏ a ∈ S, ∏ b ∈ F a, g a b) = ∏ b ∈ T, h b := by
  rw [← hunion, Finset.prod_biUnion hdisj]
  exact Finset.prod_congr rfl (fun a ha => Finset.prod_congr rfl (fun b hb => hg a ha b hb))

end Finset

namespace NK.GlobalCFT
namespace Norm

/-! ### Extracting the `LiesOver`/`LiesOver` predicates from membership in a fibre -/

/-- Membership in the fibre of an infinite place of `K` in `L` gives `LiesOver`. -/
theorem liesOver_of_mem_fiberInfinite {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {v : InfinitePlace K}
    {w : InfinitePlace L} (hw : w ∈ Place.fiberInfinite (K := K) (L := L) v) : w.LiesOver v :=
  (Place.mem_fiberInfinite).mp hw

/-- Conversely, `LiesOver` gives membership in the fibre. -/
theorem mem_fiberInfinite_of_liesOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {v : InfinitePlace K}
    {w : InfinitePlace L} (hw : w.LiesOver v) : w ∈ Place.fiberInfinite (K := K) (L := L) v :=
  (Place.mem_fiberInfinite).mpr hw

/-- Membership in the fibre of a prime of `𝓞 K` in `𝓞 L` gives `LiesOver`. -/
theorem liesOver_of_mem_primesOverFinite {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {Q : HeightOneSpectrum (𝓞 K)}
    {q : HeightOneSpectrum (𝓞 L)} (hq : q ∈ Place.primesOverFinite (K := K) (L := L) Q) :
    q.asIdeal.LiesOver Q.asIdeal :=
  (Place.mem_primesOverFinite).mp hq

/-- Conversely, `LiesOver` gives membership in the fibre. -/
theorem mem_primesOverFinite_of_liesOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {Q : HeightOneSpectrum (𝓞 K)}
    {q : HeightOneSpectrum (𝓞 L)} (hq : q.asIdeal.LiesOver Q.asIdeal) :
    q ∈ Place.primesOverFinite (K := K) (L := L) Q :=
  (Place.mem_primesOverFinite).mpr hq

/-! ### Infinite places -/


/-- For infinite places, `w` lies over `v` iff the induced place of the base field is `v`. -/
theorem liesOver_iff_comap_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : InfinitePlace L) (v : InfinitePlace K) :
    w.LiesOver v ↔ w.comap (algebraMap K L) = v := by
  constructor
  · intro h; exact InfinitePlace.LiesOver.comap_eq w v
  · intro h
    refine ⟨?_⟩
    rw [← h]
    rfl

/-- Every infinite place lies over its restriction to a subfield. -/
theorem liesOver_comap_self {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : InfinitePlace L) : w.LiesOver (w.comap (algebraMap K L)) := by
  rw [liesOver_iff_comap_eq]

/-- Transitivity of `LiesOver` in a tower, in the form of the restriction of the middle field. -/
theorem liesOver_comap_trans {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (w' : InfinitePlace M) (v : InfinitePlace K) :
    (w'.comap (algebraMap L M)).LiesOver v ↔ w'.LiesOver v := by
  rw [liesOver_iff_comap_eq, liesOver_iff_comap_eq, ← InfinitePlace.comap_comp,
    ← IsScalarTower.algebraMap_eq K L M]

/-- Transitivity of `LiesOver` for infinite places in a tower `M / L / K`. -/
theorem liesOver_trans {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {v : InfinitePlace K} {w : InfinitePlace L} {w' : InfinitePlace M}
    (h1 : w'.LiesOver w) (h2 : w.LiesOver v) : w'.LiesOver v := by
  rw [← liesOver_comap_trans (L := L) w' v]
  haveI := h1
  rw [InfinitePlace.LiesOver.comap_eq w' w]
  exact h2

/-- Two infinite places of `L` over which the same infinite place of `M` lies are equal. -/
theorem liesOver_unique {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {w : InfinitePlace L} {w₂ : InfinitePlace L} {w' : InfinitePlace M}
    (h1 : w'.LiesOver w) (h2 : w'.LiesOver w₂) : w = w₂ := by
  haveI := h1; haveI := h2
  rw [← InfinitePlace.LiesOver.comap_eq w' w, ← InfinitePlace.LiesOver.comap_eq w' w₂]

/-- The fibre of an infinite place of `K` in `M` is the disjoint union of the fibres of the
places of `L` above it. -/
theorem mem_fiberInfinite_tower {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (v : InfinitePlace K) (w' : InfinitePlace M) :
    w' ∈ Place.fiberInfinite (K := K) (L := M) v ↔
      ∃ w : InfinitePlace L, w ∈ Place.fiberInfinite (K := K) (L := L) v ∧
        w' ∈ Place.fiberInfinite (K := L) (L := M) w := by
  simp only [Place.mem_fiberInfinite]
  exact ⟨fun h => ⟨w'.comap (algebraMap L M), (liesOver_comap_trans (L := L) w' v).mpr h,
      liesOver_comap_self w'⟩, fun ⟨w, h1, h2⟩ => liesOver_trans h2 h1⟩

/-- The fibres of the places of `L` above a place `v` of `K` under `fiberInfinite` are pairwise
disjoint. -/
theorem pairwiseDisjoint_fiberInfinite {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (v : InfinitePlace K) :
    (Place.fiberInfinite (K := K) (L := L) v : Set (InfinitePlace L)).PairwiseDisjoint
      (fun w => Place.fiberInfinite (K := L) (L := M) w) := by
  intro w _ w₂ _ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro w' h1 h2
  rw [Place.mem_fiberInfinite] at h1 h2
  exact hne (liesOver_unique (K := K) h1 h2)

/-- The completions at `v ⊂ w ⊂ w'` form a scalar tower. -/
theorem isScalarTower_completion {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {v : InfinitePlace K} {w : InfinitePlace L} {w' : InfinitePlace M} [w.LiesOver v]
    [w'.LiesOver w] [w'.LiesOver v] : IsScalarTower v.Completion w.Completion w'.Completion := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  have hmain : algebraMap w.Completion w'.Completion (algebraMap v.Completion w.Completion x) =
      algebraMap v.Completion w'.Completion x := by
    induction x using NumberField.InfinitePlace.Completion.induction_on with
    | hp =>
      apply isClosed_eq
      · exact ((NumberField.LiesOver.continuous_completionMap (v := w) (w := w')).comp
          (NumberField.LiesOver.continuous_completionMap (v := v) (w := w)))
      · exact NumberField.LiesOver.continuous_completionMap (v := v) (w := w')
    | ih a =>
      simp only [NumberField.InfinitePlace.Completion.algebraMap_coe]
      apply congrArg (fun z : WithAbs w'.1 => (z : w'.Completion))
      apply WithAbs.ofAbs_injective
      simp only [WithAbs.ofAbs_algebraMap, IsScalarTower.algebraMap_apply K L M]
  exact hmain.symm

/-- **Transitivity of the local norm at infinite places**: for a tower of completions
`K_v ⊆ L_w ⊆ M_{w'}`, the norm `N_{M_{w'}/K_v}` is the composite of `N_{L_w/K_v}` and
`N_{M_{w'}/L_w}`. -/
theorem localNormInfinite_trans {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {v : InfinitePlace K} {w : InfinitePlace L} {w' : InfinitePlace M} [w.LiesOver v]
    [w'.LiesOver w] [w'.LiesOver v] (y : w'.Completionˣ) :
    Place.localNormInfinite w v (Place.localNormInfinite w' w y) = Place.localNormInfinite w' v y := by
  haveI : IsScalarTower v.Completion w.Completion w'.Completion := isScalarTower_completion
  haveI : Module.Free v.Completion w.Completion := Module.Free.of_divisionRing _ _
  haveI : Module.Free w.Completion w'.Completion := Module.Free.of_divisionRing _ _
  rw [show Place.localNormInfinite w v = Units.map (Algebra.norm v.Completion) from rfl,
      show Place.localNormInfinite w' w = Units.map (Algebra.norm w.Completion) from rfl,
      show Place.localNormInfinite w' v = Units.map (Algebra.norm v.Completion) from rfl]
  ext
  simp only [Units.coe_map]
  rw [Algebra.norm_norm]

/-! ### Finite places -/

/-- `P` lies over `p` iff `p` is the ideal of `A` under `P`. -/
theorem liesOver_iff_under_eq {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (P : Ideal B) (p : Ideal A) : P.LiesOver p ↔ p = P.under A :=
  ⟨fun h => h.over, fun h => ⟨h⟩⟩

/-- The nonzero primes of `𝓞 M` above a prime of `𝓞 K` are the disjoint union of the primes above
the primes of `𝓞 L` above it. -/
theorem mem_primesOverFinite_tower {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (Q : HeightOneSpectrum (𝓞 K)) (r : HeightOneSpectrum (𝓞 M)) :
    r ∈ Place.primesOverFinite (K := K) (L := M) Q ↔
      ∃ q : HeightOneSpectrum (𝓞 L), q ∈ Place.primesOverFinite (K := K) (L := L) Q ∧
        r ∈ Place.primesOverFinite (K := L) (L := M) q := by
  simp only [Place.mem_primesOverFinite]
  constructor
  · intro h
    have hLie : (r.asIdeal.under (𝓞 L)).LiesOver Q.asIdeal :=
      Ideal.LiesOver.tower_bot r.asIdeal (r.asIdeal.under (𝓞 L)) Q.asIdeal
    refine ⟨⟨r.asIdeal.under (𝓞 L), inferInstance, ?_⟩, hLie, ?_⟩
    · exact Ideal.ne_bot_of_liesOver_of_ne_bot Q.ne_bot _
    · exact Ideal.over_under r.asIdeal
  · rintro ⟨q, h1, h2⟩
    exact ⟨by rw [h1.over, h2.over, Ideal.under_under]⟩

/-- The fibres of the primes of `𝓞 L` above a prime of `𝓞 K` under `primesOverFinite` are
pairwise disjoint. -/
theorem pairwiseDisjoint_primesOverFinite {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (Q : HeightOneSpectrum (𝓞 K)) :
    (Place.primesOverFinite (K := K) (L := L) Q : Set (HeightOneSpectrum (𝓞 L))).PairwiseDisjoint
      (fun q => Place.primesOverFinite (K := L) (L := M) q) := by
  intro q _ q₂ _ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro r h1 h2
  rw [Place.mem_primesOverFinite] at h1 h2
  exact hne (HeightOneSpectrum.ext (h1.over.trans h2.over.symm))

/-- **Transitivity of the local norm at finite places**: for a tower `K_Q ⊆ L_q ⊆ M_{q'}`, the
norm `N_{M_{q'}/K_Q}` is the composite of `N_{L_q/K_Q}` and `N_{M_{q'}/L_q}`. -/
theorem localNormFinite_trans {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L)) (r : HeightOneSpectrum (𝓞 M))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (hr : r.asIdeal.LiesOver q.asIdeal)
    (hQ : r.asIdeal.LiesOver Q.asIdeal) (y : (r.adicCompletion M)ˣ) :
    Place.localNormFinite q Q hq (Place.localNormFinite r q hr y) =
      Place.localNormFinite r Q hQ y := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletion K) (r.adicCompletion M) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q r hQ)
  letI : Algebra (q.adicCompletion L) (r.adicCompletion M) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q r hr)
  haveI : IsScalarTower (Q.adicCompletion K) (q.adicCompletion L) (r.adicCompletion M) := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    simpa [RingHom.comp_apply] using (RingHom.congr_fun
      (Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp Q q r hq hr hQ) x).symm
  haveI : Module.Free (Q.adicCompletion K) (q.adicCompletion L) := Module.Free.of_divisionRing _ _
  haveI : Module.Free (q.adicCompletion L) (r.adicCompletion M) := Module.Free.of_divisionRing _ _
  rw [show Place.localNormFinite q Q hq = Units.map (Algebra.norm (Q.adicCompletion K)) from rfl,
      show Place.localNormFinite r q hr = Units.map (Algebra.norm (q.adicCompletion L)) from rfl,
      show Place.localNormFinite r Q hQ = Units.map (Algebra.norm (Q.adicCompletion K)) from rfl]
  ext
  simp only [Units.coe_map]
  rw [Algebra.norm_norm]

end Norm
end NK.GlobalCFT
