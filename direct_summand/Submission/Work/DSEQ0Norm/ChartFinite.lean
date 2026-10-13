/-
Finiteness and vanishing of the cohomology of the (unnormalised) Čech complex `cechZ A X f U`
of a finite affine cover `U` of a projective scheme `X` over a Noetherian ring `A`, together with
the independence of the cover.

The mathematical content is Serre's finiteness theorem for the cohomology of the structure sheaf
of a projective scheme.  It is obtained here from the sibling areas:
* `Work.DSCOH.cechComplexFunctor_homology_iso` (the normalisation comparison, Stacks 01FG),
* `Work.DSCOH.cechZ_homology_iso_chartCech` and `Work.DSCOH.chartCech_finite_vanishing` (coherence
  of the chart Čech complex of the graded module attached to the closed immersion), and
* `DSMap.area_F1_cech_proved` (the Čech complex computes `RΓ(X, 𝒪_X)`), which gives the
  independence of the cover.
-/
import Mathlib
import Submission.Work.DSCOH.cechComplexFunctor_homology_iso
import Submission.Work.DSCOH.cechZ_homology_iso_chartCech
import Submission.Work.DSCOH.chartCech_finite_vanishing
import Submission.Work.DSEQ0.chartCover_facts
import Submission.Work.DSEQ0.cechZ_chartCover_homology_finite
import Submission.Work.DSF1.Main
import Submission.Work.DSMap.Map

namespace Work.DSEQ0Norm

open CategoryTheory AlgebraicGeometry Limits

universe a

/-! ## Independence of the finite affine cover -/

/-- The homology of the Čech complex `cechZ A X f U` of the structure sheaf is independent of the
finite affine cover `U`: both complexes compute `RΓ(X, 𝒪_X)` (`DSMap.area_F1_cech_proved`). -/
theorem cechZ_homology_iso_of_covers {A : Type a} [CommRing A] {X : Scheme.{a}}
    (f : X ⟶ Spec (.of A)) [IsSeparated f] [QuasiCompact f]
    {ι κ : Type a} [Finite ι] [Finite κ] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) (V : κ → X.Opens) (hV : ∀ j, IsAffineOpen (V j))
    (hcov' : ⨆ j, V j = ⊤) :
    ∀ i : ℤ, Nonempty ((DSMap.cechZ A X f U).homology i ≅ (DSMap.cechZ A X f V).homology i) := by
  letI : HasDerivedCategory (ModuleCat.{a} A) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (SheafOfModules X.ringCatSheaf) := HasDerivedCategory.standard _
  haveI hEn : EnoughInjectives (SheafOfModules X.ringCatSheaf) :=
    inferInstanceAs (EnoughInjectives (Scheme.Modules X))
  intro i
  obtain ⟨cc, e, -, -⟩ := DSMap.area_F1_cech_proved A X f U hU hcov
  obtain ⟨cc', e', -, -⟩ := DSMap.area_F1_cech_proved A X f V hV hcov'
  refine ⟨?_⟩
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{a} A) i).app (DSMap.cechZ A X f U)).symm
    ≪≫ ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).mapIso e' ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{a} A) i).app (DSMap.cechZ A X f V))

/-! ## The chart cover -/

/-- Finiteness and vanishing of the homology of the Čech complex of the structure sheaf with
respect to the standard chart cover of a closed subscheme of projective space. -/
theorem chartCover_homology_finite {A : Type a} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{a}} (f : X ⟶ Spec (.of A)) (N : ℕ) (i : X ⟶ DSMap.PSpace A N)
    (hi : IsClosedImmersion i) (hif : i ≫ DSMap.PSpace.toSpec A N = f) :
    ∃ M : ℤ, ∀ q : ℤ,
      Module.Finite A ((DSMap.cechZ A X f (DSMap.Mix2.chartCover i)).homology q) ∧
      (M < q → CategoryTheory.Limits.IsZero
        ((DSMap.cechZ A X f (DSMap.Mix2.chartCover i)).homology q)) := by
  haveI := hi
  -- the normalisation comparison `(1c)` (Stacks 01FG)
  have h1c : ∀ q : ℕ, Nonempty ((DSMap.cech A X f (DSMap.Mix2.chartCover i)).homology q ≅
      (Work.DSCOH.altCech (DSMap.cechPresheaf A X f) (DSMap.Mix2.chartCover i)).homology q) :=
    fun q => Work.DSCOH.cechComplexFunctor_homology_iso A X (ULift.{a} (Fin (N + 1)))
      (DSMap.cechPresheaf A X f) (DSMap.Mix2.chartCover i) q
  -- the geometric bridge: the chart Čech complex of the graded module attached to `i`
  have hbr : ∀ q : ℕ, Nonempty ((DSMap.cechZ A X f (DSMap.Mix2.chartCover i)).homology (q : ℤ) ≅
      (Work.DSCOH.chartCech (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i)).homology q) :=
    Work.DSCOH.cechZ_homology_iso_chartCech (A := A) N i hi f hif h1c
  -- Serre finiteness and vanishing for the chart Čech complex
  haveI : DirectSum.Decomposition (Work.DSEQP.Mg i) := Work.DSEQP.MgDecomposition i
  obtain ⟨hfin, hvan⟩ := Work.DSCOH.chartCech_finite_vanishing (A := A) (n := N + 1)
    (M := Work.DSEQP.Mmod i) (Work.DSEQP.Mg i)
  refine ⟨(N : ℤ) + 1, fun q => ⟨?_, ?_⟩⟩
  · rcases lt_or_ge q 0 with hq | hq
    · rw [show DSMap.cechZ A X f (DSMap.Mix2.chartCover i)
          = (DSMap.cech A X f (DSMap.Mix2.chartCover i)).extend
            ComplexShape.embeddingUpNat from rfl]
      exact Work.DSCOH.moduleFinite_of_isZero
        (CochainComplex.isZero_of_isGE _ 0 q hq)
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      obtain ⟨e⟩ := hbr n
      exact Work.DSEQ0.moduleFinite_of_iso e.symm (hfin n)
  · intro hq
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ q)
    obtain ⟨e⟩ := hbr n
    exact Work.DSEQ0.isZero_of_iso e.symm (hvan n (by exact_mod_cast hq))

/-! ## Arbitrary finite affine covers -/

/-- **Finiteness and vanishing of the Čech cohomology of a projective morphism**, for an
arbitrary finite affine cover: this is the input consumed by the bounded finite free model
(`Work.DSEQ0.exists_boundedModelU_final`). -/
theorem cechZ_homology_finite_v2 {A : Type a} [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f] (hp : DSMap.IsProjOver A f)
    {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (hcov : ⨆ t, U t = ⊤) :
    ∃ N : ℤ, ∀ q : ℤ, Module.Finite A ((DSMap.cechZ A X f U).homology q) ∧
      (N < q → CategoryTheory.Limits.IsZero ((DSMap.cechZ A X f U).homology q)) := by
  obtain ⟨N, i, hi, hif⟩ := hp
  haveI := hi
  obtain ⟨M, hM⟩ := chartCover_homology_finite (A := A) f N i hi hif
  -- the chart cover is a finite affine cover
  obtain ⟨hchart_aff, hchart_cov⟩ := Work.DSEQ0.chartCover_facts (A := A) N i
  -- `f` is separated (a closed immersion composed with the separated projection) and
  -- quasi-compact (it is proper)
  haveI hsep : IsSeparated f := by rw [← hif]; infer_instance
  haveI hqc : QuasiCompact f := by
    have h := (inferInstance : IsProper f)
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.2
  -- the homology is independent of the cover
  have hiso := cechZ_homology_iso_of_covers (A := A) f U hU hcov
    (DSMap.Mix2.chartCover i) hchart_aff hchart_cov
  refine ⟨M, fun q => ⟨?_, ?_⟩⟩
  · obtain ⟨e⟩ := hiso q
    haveI : Module.Finite A
        ((DSMap.cechZ A X f (DSMap.Mix2.chartCover i)).homology q) := (hM q).1
    exact Module.Finite.equiv e.symm.toLinearEquiv
  · intro hq
    obtain ⟨e⟩ := hiso q
    exact CategoryTheory.Limits.IsZero.of_iso ((hM q).2 hq) e

end Work.DSEQ0Norm
