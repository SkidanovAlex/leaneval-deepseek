/-
# The two `F1`/`COH` wire points of the EQP assembly

`DSMap.area_EQP_proved` (`Submission/Work/DSEQP/Main.lean`) uses

* a finite free model of `RΓ(X, 𝒪_X)` (`Work.DSEQP.mx0U_from_F1COH`), and
* the bridge from a chain-level splitting of that model to `DSplit`
  (`Work.DSEQP.mx0bU_from_F1`).

Both are composites of a *clean* sibling deliverable with *one* invocation of a frozen area:

| composite | clean part (proved, axiom-clean) | fused content | frozen input |
|---|---|---|---|
| `mx0U_from_F1COH` | `Work.DSMX0U.area_MX0U_of_coherence` | pseudo-coherence of `Č(U;𝒪)` | `DSMap.area_COH` (only) |
| `mx0bU_from_F1` | `DSMap.Mix2.area_MX0bU_of_F1` | `RΓ(X,𝒪) ≅ Q(Č(U))` compatibly with the units | none — wired to `DSMap.area_F1_cech_proved` |

(`DSMap.area_F1_cech` is **proved**: `DSMap.area_F1_cech_proved` in `Submission/Work/DSF1/Main.lean`,
axiom-clean; both `F1` invocations below cite it.  The only remaining frozen input is
`DSMap.area_COH`, at the single line marked `WIRE POINT 1a`.)

This file contains *local* copies of the two transfers
(`cechZ_homology_finite_from_F1COH`, `f1Data_from_F1`) so that the assembly depends on the frozen
areas at exactly **three marked lines** in this file.  Replacing those three lines by the proved
COH (`DSMap.area_COH_proved`, `Submission/Work/DSCOH/Main.lean`) makes
`DSMap.area_EQP_proved` fully axiom-clean
(`#print axioms = [propext, Classical.choice, Quot.sound]`) with no other change anywhere.

The two composites themselves are *statements only of the frozen nodes*
`DSMap.Mix2.area_MX0U` / `DSMap.Mix2.area_MX0bU`, so the assembly is unaffected by the swap.
-/
import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSMX0U.Main
import Submission.Work.DSMX0bU.Main
import Submission.Work.DSF1.Main
import Submission.Work.DSCHART.Main

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSEQP

universe a b c

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-! ## WIRE POINT 1: the coherence input (`F1` + `COH`) -/

/-- **The coherence input of `MX0U`.**  For a projective `X` over a Noetherian ring `A` and every
finite affine cover, the cohomology of the Čech complex is finitely generated and vanishes in all
sufficiently high degrees.

This is the conjunction of the frozen areas `F1` (the Čech complex computes `RΓ(X, 𝒪_X)`,
`DSMap.area_F1_cech`) and `COH` (`DSMap.area_COH`), transferred from the derived category to the
explicit Čech complex along `Hⁱ(Q(Č)) ≅ Hⁱ(Č)` — the same transfer as
`Work.DSMX0U.cechZ_homology_finite`, reproduced here so that the two frozen inputs are named in
this file. -/
theorem cechZ_homology_finite_from_F1COH {A : Type a} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{a}} (f : X ⟶ Spec (.of A)) [IsProper f] (hp : DSMap.IsProjOver A f)
    {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) :
    ∃ N : ℤ, ∀ i : ℤ, Module.Finite A ((DSMap.cechZ A X f U).homology i) ∧
      (N < i → CategoryTheory.Limits.IsZero ((DSMap.cechZ A X f U).homology i)) := by
  letI : HasDerivedCategory (ModuleCat.{a} A) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (SheafOfModules X.ringCatSheaf) := HasDerivedCategory.standard _
  haveI hEn : EnoughInjectives (SheafOfModules X.ringCatSheaf) :=
    inferInstanceAs (EnoughInjectives (Scheme.Modules X))
  haveI hQC : QuasiCompact f := by
    have h := (inferInstance : IsProper f)
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.2
  -- >>> WIRE POINT 1a (area `COH`, subproject `DSCOH`): finiteness and boundedness of `Hⁱ(RΓ)`
  obtain ⟨N, hN⟩ := DSMap.area_COH A X f hp
  -- `F1` (proved: `DSMap.area_F1_cech_proved`, subproject `DSF1`): `RΓ(X, 𝒪_X)` is the Čech
  -- complex of `U`
  obtain ⟨cc, e, -, -⟩ := DSMap.area_F1_cech_proved A X f U hU hcov
  refine ⟨N, fun i => ⟨?_, ?_⟩⟩
  · have iso := (DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{a} A) i).app (DSMap.cechZ A X f U)
    haveI := (hN i).1
    exact Module.Finite.equiv iso.toLinearEquiv
  · intro hi
    have iso := (DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{a} A) i).app (DSMap.cechZ A X f U)
    exact IsZero.of_iso ((hN i).2 hi) iso.symm

/-! ## WIRE POINT 2: the `F1` predicate for a cover -/

/-- **The output of area `F1` for a cover**, uniformly over the derived-category instances (the
same statement as `Work.DSMX0bU.F1Data_exists`). -/
theorem f1Data_from_F1 (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [IsProper f] {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) :
    ∀ (_ : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (_ : HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf))
      (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)),
      Work.DSMX0bU.CechModelData A X f U := by
  intro hb hc hEn
  letI := hb
  letI := hc
  letI := hEn
  haveI hQC : QuasiCompact f := by
    have h := (inferInstance : IsProper f)
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.2
  -- `F1` (proved: `DSMap.area_F1_cech_proved`, subproject `DSF1`)
  exact DSMap.area_F1_cech_proved A X f U hU hcov

/-! ## The two composites used by the assembly -/

/-- **MX0U with its frozen inputs localised.**  Same statement as the frozen
`DSMap.Mix2.area_MX0U` (and as `Work.DSMX0U.area_MX0U_proved`). -/
theorem mx0U_from_F1COH (A : Type a) [CommRing A] [IsNoetherianRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) [IsProper f] (hp : DSMap.IsProjOver A f) {ι : Type a} [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) :
    ∃ (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0),
      DSMap.Mix2.IsFinFreeModelU A X f U P ε :=
  Work.DSMX0U.area_MX0U_of_coherence A X f hp U hU hcov
    (cechZ_homology_finite_from_F1COH (A := A) (X := X) f hp U hU hcov)

/-- **MX0U for the chart cover of a closed immersion, from the *Čech-level* coherence.**  This is
the form in which the assembly uses `MX0U` (the cover produced by `area_GOOD` is the chart cover of
a closed immersion `i : X ⊆ ℙᴺ_A`), with the coherence input supplied by
`Work.DSEQP.cechZ_homology_finite_chartCover` / `Work.DSEQP.cechZ_homology_chartCover_proved`
(the bridge `(1b)+(1c)`, no `F1`, no `area_COH`) instead of
`Work.DSCOH.cechZ_homology_finite_from_F1COH`. -/
theorem mx0U_of_chartCover (A : Type a) [CommRing A] [IsNoetherianRing A] {X : Scheme.{a}}
    (N : ℕ) (i : X ⟶ DSMap.PSpace A N) (hi : IsClosedImmersion i) (f : X ⟶ Spec (.of A))
    [IsProper f] (hif : i ≫ DSMap.PSpace.toSpec A N = f)
    (hcoh : ∃ N' : ℤ, ∀ j : ℤ,
      Module.Finite A ((DSMap.cechZ A X f (DSMap.Mix2.chartCover i)).homology j) ∧
      (N' < j → CategoryTheory.Limits.IsZero
        ((DSMap.cechZ A X f (DSMap.Mix2.chartCover i)).homology j))) :
    ∃ (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0),
      DSMap.Mix2.IsFinFreeModelU A X f (DSMap.Mix2.chartCover i) P ε :=
  Work.DSMX0U.area_MX0U_of_coherence A X f ⟨N, i, hi, hif⟩ (DSMap.Mix2.chartCover i)
    (DSMap.Mix2.chartCover_affine_proved i hi) (DSMap.Mix2.chartCover_iSup_proved i)
    hcoh

/-- **MX0bU with its frozen input localised.**  Same statement as the frozen
`DSMap.Mix2.area_MX0bU` (and as `DSMap.Mix2.area_MX0bU_proved`). -/
theorem mx0bU_from_F1 (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [IsProper f] {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) (hP : DSMap.Mix2.IsFinFreeModelU A X f U P ε)
    (h : DSMap.Mix.ModSplit P ε (RingHom.id A) ⊥ 1) : DSMap.DSplit.{a, b, c} A X f :=
  DSMap.Mix2.area_MX0bU_of_F1 A X f U hU hcov P ε hP h
    (f1Data_from_F1 A X f U hU hcov)

end Work.DSEQP
