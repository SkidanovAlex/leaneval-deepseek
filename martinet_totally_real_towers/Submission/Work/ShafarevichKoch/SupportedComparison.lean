import Mathlib
import Submission.Work.ShafarevichKoch.SupportedTower

/-!
# `Work.ShafarevichKoch.SupportedComparison` -- the extension `1 → H_S → G_S → G_∅ → 1`

With `kSupported F p S` the maximal pro-`p` extension of `F` unramified outside `S`
(`SupportedTower.lean`), and `F_∅ = k_∅ = kSupported F p ∅ ⊆ k_S`, this module constructs the
**objects of the comparison** of the counting (Hochschild--Serre) form of the Shafarevich--Koch
argument:

* `kEmptyInS F p S` -- the image of `k_∅` inside `k_S`, as an `IntermediateField F ↥(k_S)`;
* `kEmptyEquiv F p S` -- the comparison `↥(kEmptyInS F p S) ≃ₐ[F] ↥(k_∅)` (the identity on
  elements of the algebraic closure);
* `isGalois_kEmptyInS F p S` -- it is Galois over `F` (transported from `k_∅`);
* `restrictToEmpty F p S` -- the restriction `Gal(k_S/F) →* Gal(k_∅/F)`, as the composite of
  `AlgEquiv.restrictNormalHom` with `kEmptyEquiv`;
* `restrictToEmpty_surjective F p S` -- it is surjective (`AlgEquiv.restrictNormalHom_surjective`);
* `HSupported F p S` -- the kernel `H_S = Gal(k_S/k_∅)`, a normal subgroup of `G_S`;
* `quotientHSupportedEquiv F p S` -- `G_S ⧸ H_S ≃* G_∅`.

These are steps 1 and 3 of `README.md` §15.2 (Target 2).  Everything here is *pure field theory*:
no class field theory and no arithmetic is used.  The Krull topology of
`Mathlib.FieldTheory.KrullTopology` is available on `Gal(k_S/F)` as soon as `k_S/F` is algebraic,
so these groups can be fed to `Submission.Work.ConCohomology`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- The image of `k_∅` inside `k_S`, as an intermediate field of `↥(kSupported F p S)`. -/
def kEmptyInS (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (S : Finset ℕ) :
    IntermediateField F ↥(kSupported F p S) :=
  (kSupported F p (∅ : Finset ℕ)).comap (IntermediateField.val (kSupported F p S))

/-- **The comparison `↥(k_∅ in k_S) ≃ₐ[F] ↥k_∅`**: the identity on elements of the algebraic
closure. -/
def kEmptyEquiv (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (S : Finset ℕ) :
    ↥(kEmptyInS F p S) ≃ₐ[F] ↥(kSupported F p (∅ : Finset ℕ)) :=
  let f : ↥(kEmptyInS F p S) →ₐ[F] ↥(kSupported F p (∅ : Finset ℕ)) :=
    { toFun := fun x => ⟨(x.1 : AlgebraicClosure F), by
        have h := (Subalgebra.mem_comap (S := (kSupported F p (∅ : Finset ℕ)).toSubalgebra)
          (f := IntermediateField.val (kSupported F p S)) x.1).mp x.2
        simpa using h⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl
      commutes' := fun a => Subtype.ext rfl }
  AlgEquiv.ofBijective f
    ⟨fun a b hab => by
      have h : (a.1 : AlgebraicClosure F) = (b.1 : AlgebraicClosure F) := by
        simpa [f] using congrArg
          (fun y : ↥(kSupported F p (∅ : Finset ℕ)) => (y : AlgebraicClosure F)) hab
      exact Subtype.ext (Subtype.ext h),
     fun y => ⟨⟨⟨(y.1 : AlgebraicClosure F),
        kSupported_empty_le (F := F) (p := p) S y.2⟩, y.2⟩, Subtype.ext rfl⟩⟩

/-- `k_∅`, viewed inside `k_S`, is Galois over `F`. -/
theorem isGalois_kEmptyInS (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) : IsGalois F ↥(kEmptyInS F p S) := by
  haveI : IsGalois F ↥(kSupported F p (∅ : Finset ℕ)) :=
    isGalois_kSupported (F := F) (p := p) (S := (∅ : Finset ℕ))
  exact IsGalois.of_algEquiv (kEmptyEquiv F p S).symm

instance normal_kEmptyInS (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) : Normal F ↥(kEmptyInS F p S) :=
  (isGalois_kEmptyInS F p S).to_normal

instance normal_kSupported (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) : Normal F ↥(kSupported F p S) :=
  (isGalois_kSupported (F := F) (p := p) (S := S)).to_normal

/-- The restriction `Gal(k_S/F) →* Gal(k_∅/F)`. -/
noncomputable def restrictToEmpty (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) :
    (↥(kSupported F p S) ≃ₐ[F] ↥(kSupported F p S)) →*
      (↥(kSupported F p (∅ : Finset ℕ)) ≃ₐ[F] ↥(kSupported F p (∅ : Finset ℕ))) :=
  (AlgEquiv.autCongr (kEmptyEquiv F p S)).toMonoidHom.comp
    (AlgEquiv.restrictNormalHom (K₁ := ↥(kSupported F p S)) ↥(kEmptyInS F p S))

/-- The restriction is surjective: both fields are Galois over `F` and `k_∅ ⊆ k_S`. -/
theorem restrictToEmpty_surjective (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) : Function.Surjective (restrictToEmpty F p S) := by
  have h : Function.Surjective
      (AlgEquiv.restrictNormalHom (K₁ := ↥(kSupported F p S)) ↥(kEmptyInS F p S) :
        (↥(kSupported F p S) ≃ₐ[F] ↥(kSupported F p S)) →*
          (↥(kEmptyInS F p S) ≃ₐ[F] ↥(kEmptyInS F p S))) :=
    AlgEquiv.restrictNormalHom_surjective (F := F) (E := ↥(kSupported F p S))
  exact (AlgEquiv.autCongr (kEmptyEquiv F p S)).surjective.comp h

/-- **`H_S = Gal(k_S/k_∅)`**, as a normal subgroup of `G_S = Gal(k_S/F)`. -/
noncomputable def HSupported (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) : Subgroup (↥(kSupported F p S) ≃ₐ[F] ↥(kSupported F p S)) :=
  (restrictToEmpty F p S).ker

instance normal_HSupported (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) : (HSupported F p S).Normal :=
  MonoidHom.normal_ker _

/-- **`G_S ⧸ H_S ≃* G_∅`**: the quotient of the maximal `S`-ramified pro-`p` Galois group by the
Galois group of `k_S/k_∅` is the maximal everywhere-unramified pro-`p` Galois group. -/
noncomputable def quotientHSupportedEquiv (F : Type) [Field F] [NumberField F] (p : ℕ)
    [Fact p.Prime] (S : Finset ℕ) :
    (↥(kSupported F p S) ≃ₐ[F] ↥(kSupported F p S)) ⧸ HSupported F p S ≃*
      (↥(kSupported F p (∅ : Finset ℕ)) ≃ₐ[F] ↥(kSupported F p (∅ : Finset ℕ))) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (restrictToEmpty_surjective F p S)

end Work.ShafarevichKoch
