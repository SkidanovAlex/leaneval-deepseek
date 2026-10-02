import Mathlib
import Submission.Work.Milnor.CappedManifold
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Cohomology.pairIsoOfTrivial
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.capped_relCupSquare_generates

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cup square of the Thom class of the capped manifold generates `H⁸`

Let `X = D(ξ) ∪_F D⁸` be the closed `8`-manifold of `Submission/Work/Milnor/CappedManifold.lean`
and `A = ιY '' ℝ⁸ ⊆ X` the cap (`D = cappedDatum F hF`).  The cap is contractible, so the long
exact sequence of the pair `(X, A)` shows that

* `relIncl : H⁴(X,A) ⟶ H⁴(X)` and `relIncl : H⁸(X,A) ⟶ H⁸(X)` are isomorphisms
  (`pairIsoOfTrivial`), and
* `relIncl` is a ring homomorphism for the two cup products (`relIncl_relCupH`).

Hence the *relative* statement `Work.Cohomology.capped_relCupSquare_generates` — the existence of a
generator `u ∈ H⁴(X,A) ≅ ℤ` whose relative square `u ⌣ u` generates `H⁸(X,A) ≅ ℤ` — transfers
verbatim to the absolute cohomology of `X`: the image `x = relIncl u` generates `H⁴(X)` and
`x ⌣ x = relIncl (u ⌣ u)` generates `H⁸(X)`.

The relative statement is the crux of the whole chapter — Poincaré–Lefschetz duality for the disc
bundle `ξ = Vk (-2)`, i.e. the self-intersection of the zero section being the Euler number `±1` —
and this file is the reduction of the absolute target to it.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-! ## Elementary linear algebra over `ℤ` -/

/-- A `ℤ`-module is spanned by a single element iff every element is an integer multiple of it.

The statement involves the two `ℤ`-scalar multiplications available on an abelian group (the one
coming from the `ℤ`-module structure and the canonical one induced by `zsmul`); `int_smul_eq_zsmul`
identifies them. -/
lemma span_singleton_eq_top_iff {M : Type*} [AddCommGroup M] [Module ℤ M] (x : M) :
    Submodule.span ℤ {x} = ⊤ ↔ ∀ z : M, ∃ a : ℤ, z = a • x := by
  have bridge : ∀ (a : ℤ), (LinearMap.toSpanSingleton ℤ M x) a = (a • x : M) := by
    intro a
    rw [LinearMap.toSpanSingleton_apply]
    exact int_smul_eq_zsmul (inferInstance : Module ℤ M) a x
  constructor
  · intro h z
    have hmem : z ∈ Submodule.span ℤ {x} := by rw [h]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have ha' : (LinearMap.toSpanSingleton ℤ M x) a = z := by
      rw [LinearMap.toSpanSingleton_apply]; exact ha
    exact ⟨a, by rw [← ha', bridge]⟩
  · intro h
    rw [Submodule.eq_top_iff']
    intro z
    obtain ⟨a, ha⟩ := h z
    rw [ha, ← bridge a]
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton x))

/-- A surjective `ℤ`-linear map sends a generator to a generator. -/
lemma exists_smul_of_surjective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {x : M}
    (h : ∀ z : M, ∃ a : ℤ, z = a • x) : ∀ z : N, ∃ a : ℤ, z = a • (f x) := by
  intro z
  obtain ⟨w, rfl⟩ := hf z
  obtain ⟨a, ha⟩ := h w
  exact ⟨a, by rw [ha, map_zsmul]⟩

/-! ## The cap of the capping datum is contractible -/

/-- The cap `A = ιY '' ℝ⁸` of the capping datum is the image of the open embedding `ιY` of the
contractible space `ℝ⁸`, so its positive-degree singular cohomology vanishes. -/
lemma subsingleton_cap (D : Work.Milnor.CapData) (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton ↥(singularCohomology ℤ n (TopCat.of ↥(Set.range D.ιY))) := by
  haveI : ContractibleSpace ↥(Set.range D.ιY) :=
    (D.isOpenEmbedding_ιY.isEmbedding.toHomeomorph.symm).contractibleSpace
  have h := contractible ℤ (TopCat.of ↥(Set.range D.ιY)) (n - 1)
  rw [Nat.sub_add_cancel hn] at h
  exact ModuleCat.isZero_iff_subsingleton.mp h

/-! ## The transport from the relative statement to the absolute one -/

/-- **The relative cup square of a generator generates the absolute `H⁸`, provided the cohomology
of `A` vanishes in degrees `3`, `4`, `7`, `8`.**  Under these hypotheses (which hold when `A` is
contractible) the relative inclusion `relIncl` is a ring isomorphism in degrees `4` and `8`, so the
existence of a relative generator whose relative square generates transfers to `X` itself. -/
lemma cupSquare_generates_of_rel (X : TopCat) (A : Set X)
    (h3 : Subsingleton ↥(singularCohomology ℤ 3 (TopCat.of ↥A)))
    (h4 : Subsingleton ↥(singularCohomology ℤ 4 (TopCat.of ↥A)))
    (h7 : Subsingleton ↥(singularCohomology ℤ 7 (TopCat.of ↥A)))
    (h8 : Subsingleton ↥(singularCohomology ℤ 8 (TopCat.of ↥A)))
    (u : relCohomology ℤ X A 4)
    (hu : Submodule.span ℤ {u} = ⊤)
    (huu : Submodule.span ℤ {relCupH' ℤ X A 4 4 u u} = ⊤) :
    ∃ x : singularCohomology ℤ 4 X,
      (∀ z : singularCohomology ℤ 4 X, ∃ a : ℤ, z = a • x) ∧
      (∀ y : singularCohomology ℤ 8 X,
        ∃ a : ℤ, y = a • cupH' ℤ (TopCat.toSSet.obj X) 4 4 x x) := by
  haveI hiso4 : IsIso (HomologicalComplex.homologyMap (relIncl ℤ X A) 4) :=
    pairIsoOfTrivial ℤ X A 3 h3 h4
  haveI hiso8 : IsIso (HomologicalComplex.homologyMap (relIncl ℤ X A) 8) :=
    pairIsoOfTrivial ℤ X A 7 h7 h8
  have hsurj4 : Function.Surjective (HomologicalComplex.homologyMap (relIncl ℤ X A) 4).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hsurj8 : Function.Surjective (HomologicalComplex.homologyMap (relIncl ℤ X A) 8).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hu' : ∀ z : relCohomology ℤ X A 4, ∃ a : ℤ, z = a • u :=
    (span_singleton_eq_top_iff u).mp hu
  have huu' : ∀ z : relCohomology ℤ X A 8, ∃ a : ℤ, z = a • relCupH' ℤ X A 4 4 u u :=
    (span_singleton_eq_top_iff _).mp huu
  refine ⟨(HomologicalComplex.homologyMap (relIncl ℤ X A) 4).hom u, ?_, ?_⟩
  · exact exists_smul_of_surjective _ hsurj4 hu'
  · have hsq := relIncl_relCupH ℤ X A 4 4 u u
    have h := exists_smul_of_surjective (HomologicalComplex.homologyMap (relIncl ℤ X A) 8).hom
      hsurj8 huu'
    rw [hsq] at h
    exact h

/-! ## The main theorem -/

theorem capped_cupSquare_generates (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) :
    ∃ x : Work.Cohomology.singularCohomology ℤ 4
        (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))),
      (∀ z : Work.Cohomology.singularCohomology ℤ 4
          (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))),
        ∃ a : ℤ, z = a • x) ∧
      (∀ y : Work.Cohomology.singularCohomology ℤ 8
          (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))),
        ∃ a : ℤ, y = a • Work.Cohomology.cupH' ℤ
          (TopCat.toSSet.obj (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))))
          4 4 x x) := by
  obtain ⟨u, hu, huu⟩ := capped_relCupSquare_generates F hF
  exact cupSquare_generates_of_rel
    (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
    (Set.range (Work.Milnor.cappedDatum F hF).ιY)
    (subsingleton_cap (Work.Milnor.cappedDatum F hF) 3 (by norm_num))
    (subsingleton_cap (Work.Milnor.cappedDatum F hF) 4 (by norm_num))
    (subsingleton_cap (Work.Milnor.cappedDatum F hF) 7 (by norm_num))
    (subsingleton_cap (Work.Milnor.cappedDatum F hF) 8 (by norm_num))
    u hu huu

end

end Work.Cohomology
