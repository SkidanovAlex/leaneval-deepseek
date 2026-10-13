import Mathlib
import Submission.Work.DSCOH.AltCechComplex
import Submission.Work.DSCOH.altCech_iso_chartCech_of_termwise
import Submission.Work.DSCOH.altCech_reindex_ulift
import Submission.Work.DSEQP.gf_bridge
import Submission.Work.DSMap.Map

namespace Work.DSCOH

open CategoryTheory

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- The chart cover of `X ⊆ ℙᴺ_A`, indexed by `Fin (N+1)`: `U' k = i⁻¹ D₊(x_k)`. -/
private noncomputable abbrev chartCoverFin {A : Type*} [CommRing A] {X : AlgebraicGeometry.Scheme} {N : ℕ}
    (i : X ⟶ DSMap.PSpace A N) : Fin (N + 1) → X.Opens :=
  fun k => DSMap.Mix2.chartCover i ⟨k⟩

/-- The intersection `⋂_{k∈S} U'_k` of the `Fin (N+1)`-indexed chart cover is the chart `U_S`
of the closed immersion: both are the preimage of `D₊(∏_{k∈S} x_k)`. -/
private lemma inf_chartCoverFin_eq_Ucmp {A : Type*} [CommRing A] {X : AlgebraicGeometry.Scheme}
    {N : ℕ} (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) :
    Work.DSEQP.Ucmp i S = S.inf (chartCoverFin i) := by
  rw [Finset.inf_eq_iInf, Work.DSEQP.Ucmp_eq_iInf]
  simp only [chartCoverFin, DSMap.Mix2.chartCover]

theorem cechZ_homology_iso_chartCech (A : Type*) [CommRing A] {X : AlgebraicGeometry.Scheme}
    (N : ℕ) (i : X ⟶ DSMap.PSpace A N) (hi : AlgebraicGeometry.IsClosedImmersion i)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (hif : CategoryTheory.CategoryStruct.comp i (DSMap.PSpace.toSpec A N) = f)
    (h1c : ∀ q : ℕ, Nonempty ((DSMap.cech A X f (DSMap.Mix2.chartCover i)).homology q ≅
      (Work.DSCOH.altCech (DSMap.cechPresheaf A X f) (DSMap.Mix2.chartCover i)).homology q)) :
    ∀ q : ℕ, Nonempty ((DSMap.cechZ A X f (DSMap.Mix2.chartCover i)).homology (q : ℤ) ≅
      (Work.DSCOH.chartCech (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i)).homology q) := by
  classical
  -- The geometric bridge `(1b)`: the chart Čech terms are the sections of `𝒪_X` over the charts,
  -- compatibly with the restriction maps.
  haveI : DirectSum.Decomposition (Work.DSEQP.Mg i) := Work.DSEQP.MgDecomposition i
  obtain ⟨eTerm, hnat⟩ := Work.DSEQP.chartCechTerm_iso (A := A) (N := N) (X := X) i hi f hif
  -- The `Fin (N+1)`-indexed form of the cover.
  let U' : Fin (N + 1) → X.Opens := chartCoverFin i
  have hU : ∀ S : Finset (Fin (N + 1)), Work.DSEQP.Ucmp i S = S.inf U' := fun S => by
    rw [Finset.inf_eq_iInf, Work.DSEQP.Ucmp_eq_iInf]
    simp only [U', DSMap.Mix2.chartCover]
  -- The termwise comparison in the shape consumed by `altCech_iso_chartCech_of_termwise`.
  let e : ∀ S : Finset (Fin (N + 1)), S.Nonempty →
      ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i) S) ≃ₗ[A]
      ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (S.inf U'))) :=
    fun S hS => (eTerm S hS).trans (LinearEquiv.cast
      (M := fun W => ↥((DSMap.cechPresheaf A X f).obj (Opposite.op W))) (hU S))
  have he : ∀ (S T : Finset (Fin (N + 1))) (hST : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
      (x : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i) S)),
      (e T hT) ⟨Work.DSCOH.resAt (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i) hST x.1,
          Work.DSCOH.resAt_degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
            (ℳ := Work.DSEQP.Mg i) hST x.1 x.2⟩
        = (DSMap.cechPresheaf A X f).map (CategoryTheory.homOfLE
            (Finset.le_inf fun b hb => Finset.inf_le (hST hb))).op (e S hS x) := by
    intro S T hST hS hT x
    rw [show (e T hT) = (eTerm T hT).trans (LinearEquiv.cast
          (M := fun W => ↥((DSMap.cechPresheaf A X f).obj (Opposite.op W))) (hU T)) from rfl,
      show (e S hS) = (eTerm S hS).trans (LinearEquiv.cast
          (M := fun W => ↥((DSMap.cechPresheaf A X f).obj (Opposite.op W))) (hU S)) from rfl]
    simp only [LinearEquiv.trans_apply, LinearEquiv.cast_apply]
    rw [hnat S T hST hS hT x]
    rw [← Work.DSCOH.Pcast_eq_cast (DSMap.cechPresheaf A X f) (hU T),
      ← Work.DSCOH.Pcast_eq_cast (DSMap.cechPresheaf A X f) (hU S)]
    simp only [Work.DSCOH.Pcast]
    rw [Work.DSCOH.Pmap_comp_apply, Work.DSCOH.Pmap_comp_apply]
  -- The two matching isomorphisms: the reindexing `ULift (Fin (N+1)) ≃o Fin (N+1)` and the
  -- termwise chart comparison.
  obtain ⟨isoReindex⟩ :=
    Work.DSCOH.altCech_reindex_ulift (DSMap.cechPresheaf A X f) (DSMap.Mix2.chartCover i)
  obtain ⟨isoTermwise⟩ :=
    Work.DSCOH.altCech_iso_chartCech_of_termwise (DSMap.cechPresheaf A X f) U' e he
  intro q
  -- `H^q` of the `ℤ`-extension of `cech` is `H^q` of `cech`.
  have iso1 : (DSMap.cechZ A X f (DSMap.Mix2.chartCover i)).homology (q : ℤ) ≅
      (DSMap.cech A X f (DSMap.Mix2.chartCover i)).homology q :=
    HomologicalComplex.extendHomologyIso (DSMap.cech A X f (DSMap.Mix2.chartCover i))
      ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f q)
  have iso2 : (DSMap.cech A X f (DSMap.Mix2.chartCover i)).homology q ≅
      (Work.DSCOH.altCech (DSMap.cechPresheaf A X f) (DSMap.Mix2.chartCover i)).homology q :=
    Classical.choice (h1c q)
  have iso3 : (Work.DSCOH.altCech (DSMap.cechPresheaf A X f)
        (DSMap.Mix2.chartCover i)).homology q ≅
      (Work.DSCOH.altCech (DSMap.cechPresheaf A X f) U').homology q :=
    (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℕ) q).mapIso isoReindex
  have iso4 : (Work.DSCOH.altCech (DSMap.cechPresheaf A X f) U').homology q ≅
      (Work.DSCOH.chartCech (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i)).homology q :=
    (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℕ) q).mapIso isoTermwise
  exact ⟨iso1.trans (iso2.trans (iso3.trans iso4))⟩

end Work.DSCOH
