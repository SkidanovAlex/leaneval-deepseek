import Mathlib
import Submission.Work.Cohomology.dualZ

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Exactness of the `ℤ`-dual of a degreewise split short exact sequence

Let `S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)` be a short exact sequence of chain
complexes of `ℤ`-modules whose first map `S.f` is *degreewise* a split monomorphism
(`Work.Cohomology.IsDegreewiseSplit S`): for every degree `n` there is a `ℤ`-linear retraction
`r n` of `S.f.f n`.

The main result `Work.Cohomology.dualZSplitExact` says that then the `ℤ`-dual of `S` with values
in an arbitrary commutative ring `R`,

`0 ⟶ dualZ R S.X₃ ⟶ dualZ R S.X₂ ⟶ dualZ R S.X₁ ⟶ 0`

(`Work.Cohomology.dualZShort R S`) is again short exact.

The mathematical content is degreewise: if `0 → A --f--> B --g--> C → 0` is a short exact
sequence of `ℤ`-modules and `f` admits a retraction `r` (`r ∘ f = id`), then

`0 → Hom_ℤ(C,R) --g*--> Hom_ℤ(B,R) --f*--> Hom_ℤ(A,R) → 0`

is exact in `ModuleCat R`: `g*` is injective because `g` is surjective, `f*` is surjective
because `f` is a split mono (a preimage of `ψ` is `ψ ∘ r`), and exactness in the middle is left
exactness of `Hom` (`LinearMap.exact_lcomp_of_exact_of_surjective`).  Degreewise short exactness
of a short complex of cochain complexes is equivalent to short exactness of the complex
(`HomologicalComplex.shortExact_of_degreewise_shortExact`), which finishes the proof.

The `set_option` below is the same one used in `Submission/Work/Cohomology/dualZ.lean`: it makes
defeq checking disregard the transparency of the module instances stored in `ModuleCat` objects.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

/-- **Degreewise short exactness of the `ℤ`-dual.**  For a short exact sequence `S` of chain
complexes of `ℤ`-modules whose first map is degreewise a split monomorphism, the `n`-th
degreewise piece of `dualZShort R S` is a short exact sequence of `R`-modules. -/
theorem dualZShort_degreewise_shortExact (R : Type) [CommRing R]
    {S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)} (hS : S.ShortExact)
    (hs : IsDegreewiseSplit S) (n : ℕ) :
    ((dualZShort R S).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).ShortExact := by
  -- degreewise data provided by the short exactness of `S`
  have hSn : (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  have hex : Function.Exact ((S.f.f n) : S.X₁.X n → S.X₂.X n) ((S.g.f n) : S.X₂.X n → S.X₃.X n) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n))).mp hSn.exact
  have hsurj : Function.Surjective ((S.g.f n) : S.X₂.X n → S.X₃.X n) :=
    (ModuleCat.epi_iff_surjective _).mp hSn.epi_g
  -- the degreewise retraction of `S.f`
  obtain ⟨r, hr⟩ := hs n
  have hr' : (ModuleCat.Hom.hom r).comp (ModuleCat.Hom.hom (S.f.f n)) = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom hr
    rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  -- identify the two maps of the degreewise dual complex with the transposes of `g` and `f`
  have hf : ((dualZShort R S).map
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).f
      = ModuleCat.ofHom (LinearMap.lcomp R R ((S.g.f n).hom)) := by
    rw [show ((dualZShort R S).map
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).f
        = dualZMapComp R S.X₂ S.X₃ S.g n from rfl]
    apply ModuleCat.hom_ext
    ext φ
    rw [dualZMapComp_apply']
    rfl
  have hg : ((dualZShort R S).map
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).g
      = ModuleCat.ofHom (LinearMap.lcomp R R ((S.f.f n).hom)) := by
    rw [show ((dualZShort R S).map
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).g
        = dualZMapComp R S.X₁ S.X₂ S.f n from rfl]
    apply ModuleCat.hom_ext
    ext φ
    rw [dualZMapComp_apply']
    rfl
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · -- exactness in the middle: left exactness of `Hom`
    rw [hf, hg]
    exact LinearMap.exact_lcomp_of_exact_of_surjective R hex hsurj
  · -- injectivity of the transpose of `g`
    rw [hf]
    exact LinearMap.lcomp_injective_of_surjective _ hsurj
  · -- surjectivity of the transpose of `f`, using the retraction of `f`
    rw [hg]
    intro ψ
    refine ⟨ψ.comp (ModuleCat.Hom.hom r), ?_⟩
    change (LinearMap.lcomp R R ((S.f.f n).hom))
      (ψ.comp (ModuleCat.Hom.hom r)) = ψ
    ext x
    rw [LinearMap.lcomp_apply, LinearMap.comp_apply]
    have hx : (ModuleCat.Hom.hom r) ((ModuleCat.Hom.hom (S.f.f n)) x) = x := by
      rw [← LinearMap.comp_apply, hr', LinearMap.id_apply]
    rw [hx]

end

end Work.Cohomology

namespace Work.Cohomology

noncomputable section

open CategoryTheory AlgebraicTopology

/-- **The `ℤ`-dual of a degreewise split short exact sequence is short exact.**

If `S` is a short exact sequence of chain complexes of `ℤ`-modules and `S.f` is degreewise a
split monomorphism, then its `ℤ`-dual `dualZShort R S` with values in any commutative ring `R`
is short exact. -/
theorem dualZSplitExact (R : Type) [CommRing R]
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)} (hS : S.ShortExact)
    (hs : Work.Cohomology.IsDegreewiseSplit S) :
    (Work.Cohomology.dualZShort R S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact dualZShort_degreewise_shortExact R hS hs n

end

end Work.Cohomology
