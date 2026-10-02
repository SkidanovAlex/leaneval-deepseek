import Mathlib
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.relCapH
import Submission.Work.Cohomology.cohomologyPairVk
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Cohomology.Crux.relCapPair_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Transport of the transgression/unimodularity between two pairs

This file contains the two purely algebraic steps of the "overlap" form of the crux:

* `Work.Cohomology.Crux.exists_surjective_of_transgression` — if a `ℤ`-bilinear pairing `P` and a
  pairing `Q` are related by a transgression identity `U (P a c) = ± Q (r a) (T c)` (with `r`
  surjective and `T`, `U` isomorphisms) and `Q` is *unimodular*, then `P` is surjective in its
  second variable.  This is the abstract content of
  `Work.Cohomology.Crux.vk_relCapPair_surjective_of_transgression`, isolated from the geometry;

* `Work.Cohomology.Crux.exists_unimodular_of_natural` — **transport of unimodularity along a map of
  pairs**: if `f : (X₁,A₁) → (X₂,A₂)` is a map of pairs whose induced maps on relative homology
  (degree `n+m`) and absolute homology (degree `m`) are appropriately surjective/injective, then the
  naturality of the relative cap product under `f`
  (`Work.Cohomology.Crux.relCapPair_natural`) transports unimodularity of the `(n,m)`-pairing of
  `(X₂,A₂)` to unimodularity of the `(n,m)`-pairing of `(X₁,A₁)`.

The second is what turns the *proved* unimodularity of the overlap pairing of the model pair
`(PairXT,PairAT) = (S³×D⁴,S³×S³)` (`Work.Cohomology.sph3Disc_relCapPair_unimodular`) into
unimodularity of the pairing of the actual overlap `(vkOvl, vkOvlA)` of the two chart images of
`Vk (-2)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology.Crux

noncomputable section

/-! ## The transgression step -/

/-- **From a transgression identity plus unimodularity of the target pairing to surjectivity.**

Let `P : A →ₗ (C →ₗ B)` and `Q : D →ₗ (E →ₗ F)` be `ℤ`-bilinear pairings related by a
transgression identity `U (P a c) = ± Q (r a) (T c)` for all `a, c`, where `r : A →ₗ D` is
surjective and `T : C ≃ₗ E`, `U : B ≃ₗ F` are linear isomorphisms.  If `Q` is *unimodular*
(there is `w ∈ E` whose `Q · w` is surjective), then there is `c ∈ C` for which `P · c` is
surjective. -/
theorem exists_surjective_of_transgression {A B C D E F : Type*}
    [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B] [AddCommGroup C] [Module ℤ C]
    [AddCommGroup D] [Module ℤ D] [AddCommGroup E] [Module ℤ E] [AddCommGroup F] [Module ℤ F]
    (P : A →ₗ[ℤ] (C →ₗ[ℤ] B)) (Q : D →ₗ[ℤ] (E →ₗ[ℤ] F))
    (r : A →ₗ[ℤ] D) (hr : Function.Surjective r) (T : C ≃ₗ[ℤ] E) (U : B ≃ₗ[ℤ] F)
    (h : ∀ a c, U (P a c) = Q (r a) (T c) ∨ U (P a c) = - Q (r a) (T c))
    (hw : ∃ w : E, Function.Surjective (fun d : D => Q d w)) :
    ∃ c : C, Function.Surjective (fun a : A => P a c) := by
  obtain ⟨w, hw⟩ := hw
  refine ⟨T.symm w, ?_⟩
  intro y
  obtain ⟨d, hd⟩ := hw (U y)
  have hd' : Q d w = U y := hd
  obtain ⟨a, ha⟩ := hr d
  have key : U (P a (T.symm w)) = Q d w ∨ U (P a (T.symm w)) = - Q d w := by
    have h' := h a (T.symm w)
    rwa [ha, T.apply_symm_apply] at h'
  rcases key with hk | hk
  · refine ⟨a, ?_⟩
    show P a (T.symm w) = y
    exact U.injective (by rw [hk, hd'])
  · refine ⟨-a, ?_⟩
    show P (-a) (T.symm w) = y
    have hneg : P (-a) (T.symm w) = - P a (T.symm w) := by
      rw [LinearMap.map_neg]; rfl
    have hval : P a (T.symm w) = -y := by
      apply U.injective
      rw [map_neg, hk, hd']
    rw [hneg, hval, neg_neg]

/-! ## The transport of unimodularity along a map of pairs -/

/-- **Transport of unimodularity of the relative cap product along a map of pairs.**

Let `f : X₁ ⟶ X₂` carry `A₁` into `A₂`.  Assume

* `hnat` — the naturality of the relative cap product under `f`:
  `f_*((f^*a) ⌢ c) = a ⌢ (f_* c)` (this is `Work.Cohomology.Crux.relCapPair_natural`);
* `hsurj` — `f_* : H_{n+m}(X₁,A₁) → H_{n+m}(X₂,A₂)` is surjective;
* `hinj` — `f_* : H_m(X₁) → H_m(X₂)` is injective (in the applications these are isomorphisms,
  and the two groups are `ℤ`, so surjectivity/injectivity are what is used);
* `hw` — unimodularity of the `(n,m)`-pairing of `(X₂,A₂)`;

then the `(n,m)`-pairing of `(X₁,A₁)` is unimodular. -/
theorem exists_unimodular_of_natural {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) (n m : ℕ)
    (hnat : ∀ (a : relCohomology ℤ X₂ A₂ n) (c : (relChains X₁ A₁).homology (n + m)),
      (HomologicalComplex.homologyMap (chainMap ℤ X₁ X₂ f) m).hom
          (relCapPair X₁ A₁ n m
            ((HomologicalComplex.homologyMap (relComplexMap ℤ A₁ A₂ f h) n).hom a) c)
        = relCapPair X₂ A₂ n m a
            ((HomologicalComplex.homologyMap
              (relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h))
              (n + m)).hom c))
    (hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h))
      (n + m)).hom)
    (hinj : Function.Injective (HomologicalComplex.homologyMap (chainMap ℤ X₁ X₂ f) m).hom)
    (hw : ∃ w : (relChains X₂ A₂).homology (n + m),
      Function.Surjective (fun u : relCohomology ℤ X₂ A₂ n => relCapPair X₂ A₂ n m u w)) :
    ∃ w' : (relChains X₁ A₁).homology (n + m),
      Function.Surjective (fun u : relCohomology ℤ X₁ A₁ n => relCapPair X₁ A₁ n m u w') := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨w', hw'⟩ := hsurj w
  have hw'' : (HomologicalComplex.homologyMap
      (relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h))
      (n + m)).hom w' = w := hw'
  refine ⟨w', ?_⟩
  intro y
  -- `α` with `α ⌢ w = f_* y`
  obtain ⟨α, hα⟩ := hw ((HomologicalComplex.homologyMap (chainMap ℤ X₁ X₂ f) m).hom y)
  have hα' : relCapPair X₂ A₂ n m α w
      = (HomologicalComplex.homologyMap (chainMap ℤ X₁ X₂ f) m).hom y := hα
  refine ⟨(HomologicalComplex.homologyMap (relComplexMap ℤ A₁ A₂ f h) n).hom α, ?_⟩
  apply hinj
  rw [hnat, hw'', hα']


/-! ## Two elementary facts about maps of pairs given by a compatibility -/

/-- The pair condition of a map of pairs given by a compatibility with `subtypeIncl`. -/
theorem mem_of_comp_eq {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    {g : TopCat.of A₁ ⟶ TopCat.of A₂}
    (w : CategoryTheory.CategoryStruct.comp (Work.Cohomology.subtypeIncl X₁ A₁) f
      = CategoryTheory.CategoryStruct.comp g (Work.Cohomology.subtypeIncl X₂ A₂)) :
    ∀ x ∈ A₁, f x ∈ A₂ := fun x hx => by
  have h2 := congrArg (fun (φ : TopCat.of A₁ ⟶ X₂) => φ (⟨x, hx⟩ : ↥A₁)) w
  have h3' : f x = ((g (⟨x, hx⟩ : ↥A₁) : TopCat.of A₂) : X₂) := h2
  rw [h3']
  exact (g (⟨x, hx⟩ : ↥A₁)).2

/-- The subspace map of a map of pairs with a given compatibility is the canonical `relMapSub`. -/
theorem relMapSub_eq_of_comp_eq {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) {g : TopCat.of A₁ ⟶ TopCat.of A₂}
    (w : CategoryTheory.CategoryStruct.comp (Work.Cohomology.subtypeIncl X₁ A₁) f
      = CategoryTheory.CategoryStruct.comp g (Work.Cohomology.subtypeIncl X₂ A₂)) :
    g = Work.Cohomology.relMapSub A₁ A₂ f h := by
  apply TopCat.hom_ext
  ext x
  exact ((congrArg (fun (φ : TopCat.of A₁ ⟶ X₂) => φ x) w).symm).trans rfl

/-- Two maps of relative chain complexes with the same underlying map are equal. -/
theorem relChainsMapOf_congr_sub {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) {g : TopCat.of A₁ ⟶ TopCat.of A₂}
    (w : CategoryTheory.CategoryStruct.comp (Work.Cohomology.subtypeIncl X₁ A₁) f
      = CategoryTheory.CategoryStruct.comp g (Work.Cohomology.subtypeIncl X₂ A₂))
    (hg : g = Work.Cohomology.relMapSub A₁ A₂ f h) :
    Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ f g w
      = Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ f (Work.Cohomology.relMapSub A₁ A₂ f h)
          (Work.Cohomology.relMapSub_spec A₁ A₂ f h) := by
  subst hg
  rfl

/-! ## The reduction: transgression + overlap unimodularity ⟹ surjectivity for `(Vk, Mk)` -/

/-- **The transgression reduction with the actual overlap.**

If the relative cap product of `(Vk(-2), Mk(-2))` is related to that of the overlap
`(vkOvl, vkOvlA) = (U ∩ V, (U ∩ V) ∩ Mk)` by a Mayer--Vietoris transgression identity
`U (a ⌢ c) = ± (r a) ⌢ (T c)` (with `r` surjective and `T`, `U` isomorphisms), and the overlap
pairing is unimodular, then the Lefschetz-duality map `u ↦ u ⌢ c` of `(Vk(-2), Mk(-2))` is
surjective. -/
theorem vk_relCapPair_surjective_of_transgression_ovl
    (hT : ∃ (r : relCohomology ℤ vkPairX vkPairA 4 →ₗ[ℤ] relCohomology ℤ vkOvl vkOvlA 4)
      (T : (relChains vkPairX vkPairA).homology 8 ≃ₗ[ℤ] (relChains vkOvl vkOvlA).homology 7)
      (U : (singularChains ℤ vkPairX).homology 4 ≃ₗ[ℤ] (singularChains ℤ vkOvl).homology 3),
      Function.Surjective r ∧
      ∀ (a : relCohomology ℤ vkPairX vkPairA 4) (c : (relChains vkPairX vkPairA).homology 8),
        U (relCapPair vkPairX vkPairA 4 4 a c) = relCapPair vkOvl vkOvlA 4 3 (r a) (T c) ∨
        U (relCapPair vkPairX vkPairA 4 4 a c) = - relCapPair vkOvl vkOvlA 4 3 (r a) (T c))
    (hw : ∃ w : (relChains vkOvl vkOvlA).homology 7,
      Function.Surjective (fun u : relCohomology ℤ vkOvl vkOvlA 4 =>
        relCapPair vkOvl vkOvlA 4 3 u w)) :
    ∃ c : (relChains vkPairX vkPairA).homology 8,
      Function.Surjective (fun u : relCohomology ℤ vkPairX vkPairA 4 =>
        relCapPair vkPairX vkPairA 4 4 u c) := by
  obtain ⟨r, T, U, hr, h⟩ := hT
  exact exists_surjective_of_transgression (relCapPair vkPairX vkPairA 4 4)
    (relCapPair vkOvl vkOvlA 4 3) r hr T U h hw

/-- **The weak transgression step.**  As `exists_surjective_of_transgression`, but with `T` only
required to be *surjective* and `U` only *injective* — the form in which the Mayer–Vietoris
transgression is produced by the assembly of the capped-pair frontier
(`Work.Cohomology.vk_transgression_cap_weak`), where `T` and `U` are the connecting maps themselves.
The sharp overlap input is entered through the last hypothesis. -/
theorem exists_surjective_of_transgression_weak {A B C D E F : Type*}
    [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B] [AddCommGroup C] [Module ℤ C]
    [AddCommGroup D] [Module ℤ D] [AddCommGroup E] [Module ℤ E] [AddCommGroup F] [Module ℤ F]
    (P : A →ₗ[ℤ] (C →ₗ[ℤ] B)) (Q : D →ₗ[ℤ] (E →ₗ[ℤ] F))
    (r : A →ₗ[ℤ] D) (hr : Function.Surjective r)
    (T : C →ₗ[ℤ] E) (hT : Function.Surjective T) (U : B →ₗ[ℤ] F) (hU : Function.Injective U)
    (h : ∀ a c, U (P a c) = Q (r a) (T c) ∨ U (P a c) = - Q (r a) (T c))
    (hw : ∃ w : E, Function.Surjective (fun d : D => Q d w)) :
    ∃ c : C, Function.Surjective (fun a : A => P a c) := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨c, hc⟩ := hT w
  refine ⟨c, ?_⟩
  intro y
  obtain ⟨d, hd⟩ := hw (U y)
  have hd' : Q d w = U y := hd
  obtain ⟨a, ha⟩ := hr d
  have key : U (P a c) = Q d w ∨ U (P a c) = - Q d w := by
    have h' := h a c
    rwa [ha, hc] at h'
  rcases key with hk | hk
  · refine ⟨a, ?_⟩
    show P a c = y
    exact hU (by rw [hk, hd'])
  · refine ⟨-a, ?_⟩
    show P (-a) c = y
    have hneg : P (-a) c = - P a c := by
      rw [LinearMap.map_neg]; rfl
    have hval : P a c = -y := by
      apply hU
      rw [map_neg, hk, hd']
    rw [hneg, hval, neg_neg]

/-- The transgression reduction in the weak form, for the pair `(Vk(-2), Mk(-2))`: the weak
transgression identity for the two-chart cover together with unimodularity of the overlap pairing
(entered as the last hypothesis) gives the surjectivity of the Lefschetz-duality map. -/
theorem vk_relCapPair_surjective_of_transgression_weak
    (hT : ∃ (r : relCohomology ℤ vkPairX vkPairA 4 →ₗ[ℤ] relCohomology ℤ vkOvl vkOvlA 4)
      (T : (relChains vkPairX vkPairA).homology 8 →ₗ[ℤ] (relChains vkOvl vkOvlA).homology 7)
      (U : (singularChains ℤ vkPairX).homology 4 →ₗ[ℤ] (singularChains ℤ vkOvl).homology 3),
      Function.Surjective r ∧ Function.Surjective T ∧ Function.Injective U ∧
      ∀ (a : relCohomology ℤ vkPairX vkPairA 4) (c : (relChains vkPairX vkPairA).homology 8),
        U (relCapPair vkPairX vkPairA 4 4 a c) = relCapPair vkOvl vkOvlA 4 3 (r a) (T c) ∨
        U (relCapPair vkPairX vkPairA 4 4 a c) = - relCapPair vkOvl vkOvlA 4 3 (r a) (T c))
    (hw : ∃ w : (relChains vkOvl vkOvlA).homology 7,
      Function.Surjective (fun u : relCohomology ℤ vkOvl vkOvlA 4 =>
        relCapPair vkOvl vkOvlA 4 3 u w)) :
    ∃ c : (relChains vkPairX vkPairA).homology 8,
      Function.Surjective (fun u : relCohomology ℤ vkPairX vkPairA 4 =>
        relCapPair vkPairX vkPairA 4 4 u c) := by
  obtain ⟨r, T, U, hr, hT', hU', h⟩ := hT
  exact exists_surjective_of_transgression_weak (relCapPair vkPairX vkPairA 4 4)
    (relCapPair vkOvl vkOvlA 4 3) r hr T hT' U hU' h hw

/-- The weak transgression reduction with the *model* pair `(PairXT, PairAT) = (S³×D⁴, S³×S³)` as
the target: `Work.Cohomology.vk_transgression_cap_weak` (the weak Mayer–Vietoris transgression
identity for the two-chart cover of `Vk (-2)`, which is the frontier of the transgression route)
together with unimodularity of the model pairing gives the surjectivity of the Lefschetz-duality map
of `(Vk(-2), Mk(-2))`. -/
theorem vk_relCapPair_surjective_of_transgression_weak_model
    (hT : ∃ (r : relCohomology ℤ vkPairX vkPairA 4 →ₗ[ℤ]
          relCohomology ℤ Work.Cohomology.PairXT Work.Cohomology.PairAT 4)
      (T : (relChains vkPairX vkPairA).homology 8 →ₗ[ℤ]
        (relChains Work.Cohomology.PairXT Work.Cohomology.PairAT).homology 7)
      (U : (singularChains ℤ vkPairX).homology 4 →ₗ[ℤ]
        (singularChains ℤ Work.Cohomology.PairXT).homology 3),
      Function.Surjective r ∧ Function.Surjective T ∧ Function.Injective U ∧
      ∀ (a : relCohomology ℤ vkPairX vkPairA 4) (c : (relChains vkPairX vkPairA).homology 8),
        U (relCapPair vkPairX vkPairA 4 4 a c)
            = relCapPair Work.Cohomology.PairXT Work.Cohomology.PairAT 4 3 (r a) (T c) ∨
        U (relCapPair vkPairX vkPairA 4 4 a c)
            = - relCapPair Work.Cohomology.PairXT Work.Cohomology.PairAT 4 3 (r a) (T c))
    (hw : ∃ w : (relChains Work.Cohomology.PairXT Work.Cohomology.PairAT).homology 7,
      Function.Surjective (fun u : relCohomology ℤ Work.Cohomology.PairXT
        Work.Cohomology.PairAT 4 =>
        relCapPair Work.Cohomology.PairXT Work.Cohomology.PairAT 4 3 u w)) :
    ∃ c : (relChains vkPairX vkPairA).homology 8,
      Function.Surjective (fun u : relCohomology ℤ vkPairX vkPairA 4 =>
        relCapPair vkPairX vkPairA 4 4 u c) := by
  obtain ⟨r, T, U, hr, hT', hU', h⟩ := hT
  exact exists_surjective_of_transgression_weak (relCapPair vkPairX vkPairA 4 4)
    (relCapPair Work.Cohomology.PairXT Work.Cohomology.PairAT 4 3) r hr T hT' U hU' h hw

end

end Work.Cohomology.Crux
