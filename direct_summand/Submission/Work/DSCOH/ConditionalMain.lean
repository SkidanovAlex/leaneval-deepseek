/-
Area DSCOH — the last mile of `DSMap.area_COH`, conditional on the two sibling areas.

`Work.DSCOH.area_COH_of_F1_and_bridge` has *exactly* the conclusion of the frozen
`DSMap.area_COH`.  Its (explicit) hypotheses are the two data that this area cannot supply:

* `e : ι(RΓ(X, 𝒪_X)) ≅ Q(cechZ A X f U)`, i.e. the Čech model of `RΓ` for a finite affine cover
  `U` of `X` — the output of the frozen area `F1` (`DSMap.area_F1_cech`, delivered by the area
  `DSF1`);
* `hK : ∀ q, H^q(cechZ A X f U) ≅ (chartCech ℳ).homology q` for a finitely generated graded
  `A[X₀,…,X_{n-1}]`-module `M` with internal decomposition `ℳ` — the geometric bridge
  (chartwise identification of the sections of `𝒪_X` with the degree-zero parts of the chart
  localizations, `(1b)`, delivered by area `DSEQP`; plus the normalization quasi-isomorphism
  between Mathlib's unnormalized Čech complex and the alternating one, `(1c)`, proved in this
  area and composed with the `ℤ`-extension isomorphism
  `HomologicalComplex.extendHomologyIso (cech A X f U) ComplexShape.embeddingUpNat`).

Given those, the frozen statement follows by `Work.DSCOH.area_COH_of_comparison` (the area's own
assembly) applied to `Work.DSCOH.comparison_of_cech_model` (which turns `e` and `hK` into the
comparison hypothesis) — no further input is needed, since the coherence of the chart Čech
complex of `ℳ` is the area's theorem `Work.DSCOH.chartCech_finite_vanishing`.
-/
import Submission.Work.DSCOH.comparison_of_cech_model
import Submission.Work.DSCOH.chartCech_finite_vanishing
import Submission.Work.DSCHART.Main

open CategoryTheory AlgebraicGeometry Limits

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.DSCOH

universe a b c

/-- **`DSMap.area_COH`, from F1 and the geometric bridge.** -/
theorem area_COH_of_F1_and_bridge (A : Type a) [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{b} (ModuleCat.{a} A)] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    {n : ℕ} {M : Type a} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] {ℳ : ℕ → Submodule A M} [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (homSub A n) ℳ] [Module.Finite (Poly A n) M]
    {ι : Type a} (U : ι → X.Opens)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
      DerivedCategory.Q.obj (DSMap.cechZ A X f U))
    (hK : ∀ q : ℕ, Nonempty ((DSMap.cechZ A X f U).homology (q : ℤ) ≅
      (chartCech (A := A) (n := n) (M := M) ℳ).homology q)) :
    ∃ N : ℤ, ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).obj
        (DerivedCategory.Plus.ι.obj (DSMap.RG A X f))) ∧
      (N < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).obj
        (DerivedCategory.Plus.ι.obj (DSMap.RG A X f)))) :=
  area_COH_of_comparison A X f (comparison_of_cech_model A X f e
    (chartCech (A := A) (n := n) (M := M) ℳ) hK)

end Work.DSCOH

/-! ## The chart cover of a projective `X` -/

namespace Work.DSCOH

universe a b c

/-- The chart cover `U_k = X ∩ D₊(x_k)` of a closed subscheme `X ⊆ ℙᴺ_A` is a finite affine
cover: the two halves are DSCHART's deliverables `DSMap.Mix2.chartCover_affine_proved` and
`DSMap.Mix2.chartCover_iSup_proved`. -/
theorem chartCover_affine_and_covers {A : Type a} [CommRing A] {X : Scheme.{a}} {N : ℕ}
    (i : X ⟶ DSMap.PSpace A N) (hi : IsClosedImmersion i) :
    (∀ k, IsAffineOpen (DSMap.Mix2.chartCover i k)) ∧
      (⨆ k, DSMap.Mix2.chartCover i k = ⊤) :=
  ⟨DSMap.Mix2.chartCover_affine_proved i hi, DSMap.Mix2.chartCover_iSup_proved i⟩

/-- **`DSMap.area_COH`, from F1 and the geometric bridge, for the chart cover of a given closed
immersion `i : X ⊆ ℙᴺ_A`.**  This is the form in which `Submission/Work/DSCOH/Main.lean` will
consume the two sibling deliverables: `DSMap.area_F1_cech` (area F1) applied to the chart cover
of `i` gives the isomorphism `e`, and the geometric bridge `(1b)`+`(1c)` (areas DSEQP and DSCOH)
gives `hK`. -/
theorem area_COH_of_F1_and_bridge_proj (A : Type a) [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{b} (ModuleCat.{a} A)] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    {N : ℕ} (i : X ⟶ DSMap.PSpace A N) (hi : IsClosedImmersion i)
    (hif : i ≫ DSMap.PSpace.toSpec A N = f)
    {n : ℕ} {M : Type a} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] {ℳ : ℕ → Submodule A M} [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (homSub A n) ℳ] [Module.Finite (Poly A n) M]
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
      DerivedCategory.Q.obj (DSMap.cechZ A X f (DSMap.Mix2.chartCover i)))
    (hK : ∀ q : ℕ, Nonempty
      ((DSMap.cechZ A X f (DSMap.Mix2.chartCover i)).homology (q : ℤ) ≅
        (chartCech (A := A) (n := n) (M := M) ℳ).homology q)) :
    ∃ N' : ℤ, ∀ j : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) j).obj
        (DerivedCategory.Plus.ι.obj (DSMap.RG A X f))) ∧
      (N' < j → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) j).obj
        (DerivedCategory.Plus.ι.obj (DSMap.RG A X f)))) :=
  area_COH_of_F1_and_bridge A X f (DSMap.Mix2.chartCover i) e hK

end Work.DSCOH
