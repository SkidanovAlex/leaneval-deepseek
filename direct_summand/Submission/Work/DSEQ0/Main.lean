import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map
import Submission.Work.DSEQ0.Basic
import Submission.Work.DSEQ0.Model
import Submission.Work.DSEQ0.SuperTrace
import Submission.Work.DSEQ0.CechModel
import Submission.Work.DSEQ0.chainMap_retraction_of_functional
import Submission.Work.DSEQ0.chainMap_retraction_of_differential
import Submission.Work.DSEQ0.area_EQ0_proved

/-!
# DSEQ0 (area EQ0): equal characteristic zero — the reduced main interface

This is the final module of the area `EQ0`.  It records

* the exact data that the trace argument has to supply (`Work.DSEQ0.PerfectModel`), and
* the reduction of the frozen area statement `DSMap.area_EQ0` to that data
  (`Work.DSEQ0.area_EQ0_of_perfectModel`), together with the derived-category assembly
  (`Work.DSEQ0.isSplitMono_of_perfectModel`).

## Status of the frozen statement `DSMap.area_EQ0`

`DSMap.area_EQ0` is *not* proved in this module, and deliberately so: its proof needs four
inputs, three of which do not exist in this workspace or in Mathlib.

1. **The Čech model** `DSMap.area_F1_cech` (area `DSF1`).  Needed to know that
   `RΓ(X,𝒪)` is computed by the alternating Čech complex of a finite affine cover.
2. **Coherence** `DSMap.area_COH` (area `DSCOH`).  Needed to know that `RΓ(X,𝒪)` has
   finitely generated cohomology, bounded above.
3. **Finite projective dimension over a regular local ring.**  Needed to replace a bounded
   complex with finitely generated cohomology by a *bounded* complex of finite free modules
   (Serre's theorem `gl.dim A = dim A` for `A` regular local; the Auslander–Buchsbaum
   machinery).  This is *not* in Mathlib at the frozen pin and is not the statement of any area
   of the proof map.
4. **The trace on the perfect model.**  A strictly unital, strictly associative product on the
   finite free model (the Alexander–Whitney product of the Čech complex, transported along a
   quasi-isomorphism), which produces the functional `φ₀ = superTrace ∘ μ(−,−)` with
   `φ₀(c 1) = χ`, where `χ = [K(X):K]` is the generic degree.  The *linear algebra* of this
   step is in `Submission/Work/DSEQ0/SuperTrace.lean` and its two delegated lemmas; what is
   missing is the strictification of the product.

Everything else is done:

* `Work.DSEQ0.isSplitMono_of_chainModel`: model + retraction in the derived category.
* `Work.DSEQ0.isSplitMono_of_cechModel`: the same, with the Čech model glued in.
* `Work.DSEQ0.isSplitMono_of_perfectModel` / `Work.DSEQ0.area_EQ0_of_perfectModel`: the
  reduction of the frozen `DSMap.area_EQ0` to the data of `Work.DSEQ0.PerfectModel`.

The arithmetic input is also done: `Work.DSEQ0.isUnit_natCast_of_charZero_residueField` shows
that `χ` is invertible, since `ResidueField A` has characteristic zero.
-/

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSEQ0

universe u v w w₁ w₂ w₃

variable (A : Type u) [CommRing A]

/-- **The perfect model with trace retraction.**  Relative to a fixed family of opens `U` and the
Čech coaugmentation `cc` (both provided by `DSMap.area_F1_cech`), this is the data produced by
the trace argument of area `EQ0`:

* a complex `P` of finite free `A`-modules, concentrated in degrees `≥ 0` (this is what makes a
  chain map `P ⟶ A[0]` the same thing as a functional `P⁰ ⟶ A`);
* a quasi-isomorphism `q : P ⟶ Č(U;𝒪)`;
* a lift `c : A[0] ⟶ P` of the coaugmentation `cc`; and
* a chain map `φ : P ⟶ A[0]` retracting `c`, i.e. `c ≫ φ = 𝟙`.

The last two items are what the supertrace provides: `φ` is `(χ⁻¹ : A) • superTrace ∘ μ(−,−)`
in degree zero (see `Submission/Work/DSEQ0/SuperTrace.lean`), and `χ = [K(X):K]` is a unit by
`Work.DSEQ0.isUnit_natCast_of_charZero_residueField`. -/
def PerfectModel [HasDerivedCategory (ModuleCat.{u} A)] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A))
    {J : Type u} (U : J → X.Opens) (cc : singleZ A ⟶ DSMap.cechZ A X f U) : Prop :=
  ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (q : P ⟶ DSMap.cechZ A X f U)
    (c : singleZ A ⟶ P) (φ : P ⟶ singleZ A),
    QuasiIso q ∧
      DerivedCategory.Q.map cc = DerivedCategory.Q.map c ≫ DerivedCategory.Q.map q ∧
      c ≫ φ = 𝟙 (singleZ A)

/-- The Čech model together with a perfect model with trace retraction gives the splitting of
the challenge unit. -/
theorem isSplitMono_of_perfectModel [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    {J : Type u} (U : J → X.Opens)
    (cc : singleZ A ⟶ DSMap.cechZ A X f U)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
      DerivedCategory.Q.obj (DSMap.cechZ A X f U))
    (he : DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
      (singleIsoCompQ A).hom ≫ DerivedCategory.Q.map cc)
    (h : PerfectModel A X f U cc) : IsSplitMono (DSMap.rgUnit A X f) := by
  obtain ⟨P, q, c, φ, hq, hc, hφ⟩ := h
  exact isSplitMono_of_cechModel A X f U cc e he P q hq c hc φ hφ

/-- **Area `EQ0`, reduced to the perfect model.**  For a regular local ring `A`, complete with
algebraically closed residue field of characteristic zero, and `X` integral, proper, surjective,
generically finite and projective over `Spec A`, the challenge unit splits as soon as the Čech
model of `DSMap.area_F1_cech` carries a perfect model with trace retraction
(`Work.DSEQ0.PerfectModel`).

This is the reduction of the frozen statement `DSMap.area_EQ0` to the missing input 3/4
documented at the top of this file. -/
theorem area_EQ0_of_perfectModel.{a, b, c} (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsAlgClosed (IsLocalRing.ResidueField A)]
    [CharZero (IsLocalRing.ResidueField A)] (X : Scheme.{a}) [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f)
    (hg : DSMap.IsGenFinite A f) (hp : DSMap.IsProjOver A f)
    (h : ∀ (_ : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (_ : HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf))
      (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)),
      ∃ (J : Type a) (_ : Finite J) (U : J → X.Opens) (_ : ∀ i, IsAffineOpen (U i))
        (_ : ⨆ i, U i = ⊤) (cc : singleZ A ⟶ DSMap.cechZ A X f U)
        (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
          DerivedCategory.Q.obj (DSMap.cechZ A X f U)),
        (DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
          (singleIsoCompQ A).hom ≫ DerivedCategory.Q.map cc) ∧
          PerfectModel A X f U cc) :
    DSMap.DSplit.{a, b, c} A X f := by
  intro h₁ h₂ h₃
  obtain ⟨J, hJ, U, hU, hcov, cc, e, he, hpm⟩ := h h₁ h₂ h₃
  exact isSplitMono_of_perfectModel A X f U cc e he hpm

/-! ## The linear algebra of the trace

The construction of the functional from a strictly unital product, in the shape in which the
trace argument uses it.  `M i` is the degree `i` part of the perfect model, `μ` is the product,
`u` is the class of `1` under the coaugmentation, and `hu` says `μ u = 𝟙`. -/

/-- If a strictly unital product on a family of finite free modules is given, with unit `u`,
then `x ↦ superTrace (μ x)` is a functional taking the value `eulerChar` at `u`. -/
theorem exists_functional_of_unitalProduct {A : Type u} [CommRing A] {N : ℕ}
    (M : Fin (N + 1) → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module.Finite A (M i)] [∀ i, Module.Free A (M i)]
    (μ : M 0 →ₗ[A] (∀ i, M i →ₗ[A] M i)) (u : M 0) (hu : μ u = 1) :
    ∃ φ₀ : M 0 →ₗ[A] A, φ₀ u = eulerChar A M :=
  ⟨superTraceLin A M ∘ₗ μ, by
    rw [LinearMap.comp_apply, hu]
    exact superTrace_one A M⟩

/-! ## Reduction to a single functional

The chain-level retraction `φ` is only needed on the model `P`; by
`Work.DSEQ0.chainMap_retraction_of_functional` it is produced by a functional `φ₀ : P⁰ ⟶ A`
whose value on the coaugmentation class is a nonzero natural number of `A`.  Consequently the
*entire* remaining content of area `EQ0` is the existence of the model `P` together with such a
functional — which is what the trace on the perfect model provides. -/

/-- A bounded model of the Čech complex with a lift of the coaugmentation and a functional whose
value on the coaugmentation class is a nonzero natural number yields the perfect model. -/
theorem perfectModel_of_functional [HasDerivedCategory (ModuleCat.{u} A)] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [IsLocalRing A] [CharZero (IsLocalRing.ResidueField A)]
    {J : Type u} (U : J → X.Opens) (cc : singleZ A ⟶ DSMap.cechZ A X f U)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (q : P ⟶ DSMap.cechZ A X f U) (hq : QuasiIso q) (c : singleZ A ⟶ P)
    (hc : DerivedCategory.Q.map cc = DerivedCategory.Q.map c ≫ DerivedCategory.Q.map q)
    (φ₀ : P.X 0 ⟶ ModuleCat.of A A) (χ : ℕ) (hχ : χ ≠ 0)
    (hφ₀ : φ₀ (c.f 0 (1 : A)) = (χ : A)) (hker : P.d (-1) 0 ≫ φ₀ = 0) :
    PerfectModel A X f U cc := by
  obtain ⟨φ, hφ⟩ := chainMap_retraction_of_differential (A := A) P c φ₀ χ hχ hφ₀ hker
  exact ⟨P, q, c, φ, hq, hc, hφ⟩

/-- **Area `EQ0`, reduced to a single functional.**  Same as `area_EQ0_of_perfectModel`, except
that the model is described by a functional `φ₀ : P⁰ ⟶ A` with `φ₀(c 1) = χ` for some nonzero
natural number `χ` — the shape in which the trace on the perfect model produces it. -/
theorem area_EQ0_of_functional.{a, b, c} (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsAlgClosed (IsLocalRing.ResidueField A)]
    [CharZero (IsLocalRing.ResidueField A)] (X : Scheme.{a}) [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f)
    (hg : DSMap.IsGenFinite A f) (hp : DSMap.IsProjOver A f)
    (h : ∀ (_ : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (_ : HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf))
      (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)),
      ∃ (J : Type a) (_ : Finite J) (U : J → X.Opens) (_ : ∀ i, IsAffineOpen (U i))
        (_ : ⨆ i, U i = ⊤) (cc : singleZ A ⟶ DSMap.cechZ A X f U)
        (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
          DerivedCategory.Q.obj (DSMap.cechZ A X f U)),
        (DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
          (singleIsoCompQ A).hom ≫ DerivedCategory.Q.map cc) ∧
        ∃ (P : CochainComplex (ModuleCat.{a} A) ℤ)
          (q : P ⟶ DSMap.cechZ A X f U) (_ : QuasiIso q) (c : singleZ A ⟶ P)
          (_ : DerivedCategory.Q.map cc =
            DerivedCategory.Q.map c ≫ DerivedCategory.Q.map q)
          (φ₀ : P.X 0 ⟶ ModuleCat.of A A) (χ : ℕ) (_ : χ ≠ 0),
          φ₀ (c.f 0 (1 : A)) = (χ : A) ∧ P.d (-1) 0 ≫ φ₀ = 0) :
    DSMap.DSplit.{a, b, c} A X f := by
  intro h₁ h₂ h₃
  obtain ⟨J, hJ, U, hU, hcov, cc, e, he, P, q, hq, c, hc, φ₀, χ, hχ, hφ₀, hker⟩ := h h₁ h₂ h₃
  exact isSplitMono_of_perfectModel A X f U cc e he
    (perfectModel_of_functional A X f U cc P q hq c hc φ₀ χ hχ hφ₀ hker)

end Work.DSEQ0

/-! ## The deliverable: `DSMap.area_EQ0_proved`

The theorem of this area, under the requested name and in the requested file, with the frozen type
of `DSMap.area_EQ0` (`Submission/Work/DSMap/Map.lean`).  The proof is
`Work.DSEQ0.area_EQ0_proved` in `Submission/Work/DSEQ0/area_EQ0_proved.lean`; this is the
`DSMap`-namespace re-export the lead's assembly imports.
-/

namespace DSMap

theorem area_EQ0_proved.{a, b, c} (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsAlgClosed (IsLocalRing.ResidueField A)]
    [CharZero (IsLocalRing.ResidueField A)] (X : Scheme.{a}) [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f)
    (hg : DSMap.IsGenFinite A f) (hp : DSMap.IsProjOver A f) :
    DSMap.DSplit.{a, b, c} A X f :=
  Work.DSEQ0.area_EQ0_proved A X f hs hg hp

end DSMap
