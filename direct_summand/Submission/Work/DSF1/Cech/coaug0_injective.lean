import Mathlib
import Submission.Work.DSF1.Cech.CechDefs
import Submission.Work.DSF1.Cech.basicOpen_localization_facts
import Submission.Work.DSF1.Cech.CoaugCycle

/-!
# Injectivity of the degree-zero coaugmentation `R ⟶ Č⁰`

Let `R` be a commutative ring, `f : ι → R` a family of elements generating the unit
ideal, `X = Spec R`, `U i = D (f i)` and `Č` the Čech complex of the structure sheaf of
`X` (as a presheaf of `R`-modules) along `U` (`Work.DSF1.Cech.cechSpec`).  The degree
zero coaugmentation `coaug0 f : R ⟶ Č⁰` sends `q : R` to the family of its images in the
section rings `Γ(U x)` over the degree zero simplices.

In degree zero the simplices are indexed by `Fin 1 → ι`, and for `x : Fin 1 → ι` the
corresponding open is `Eobj U 0 x = ∏ᶜ (U ∘ x)`, the product of the single open
`U (x 0)`.  Thus the component of `coaug0 f q` at `x` is the image of `q` under the
structure map `R → Γ(∏ᶜ (U ∘ x))`.

Taking `x₀ : Fin 1 → ι` the constant index with value `i`, the open `Eobj U 0 x₀` is
`D (f i)` (this is `Eobj_zero_const` below), so the hypothesis `coaug0 f q = 0` gives
that the image of `q` in `Γ(D (f i))` is zero for every `i`.  Since `Γ(D (f i))` is the
localization `R[1/f i]` (`StructureSheaf.IsLocalization.to_basicOpen`), this means that
`f i ^ k * q = 0` for some `k`.  The `f i` generating the unit ideal then force `q = 0`
by the standard "powers of a generating family" argument
(`Submodule.mem_of_span_eq_top_of_smul_pow_mem`), applied to the zero submodule of `R`.

This is the exactness of the augmented Čech complex in degree `-1`, i.e. the statement
that `R` is the degree zero cohomology of the affine Čech complex.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

variable {R : Type u} [CommRing R] {ι : Type u}

/-- **The degree zero open attached to a constant index.**  For `x : Fin 1 → ι` the
constant index with value `i`, the open `Eobj U 0 x` — the product over the single
element of `Fin 1` of `D (f i)` — is `D (f i)`.

The two inequalities are the projection `∏ᶜ F ⟶ F 0` and the map
`F 0 ⟶ ∏ᶜ F` given by the universal property of the product (all components of the
latter are the identity). -/
lemma Eobj_zero_const (f : ι → R) (i : ι) :
    Eobj (basicOpens f) 0 (fun _ : Fin 1 => i) = PrimeSpectrum.basicOpen (f i) := by
  refine le_antisymm ?_ ?_
  · exact (Pi.π (fun _ : Fin 1 => PrimeSpectrum.basicOpen (f i)) 0).le
  · exact (Pi.lift (fun _ : Fin 1 => 𝟙 (PrimeSpectrum.basicOpen (f i)))).le

/-- **The component of the coaugmentation at a constant index.**  If `(coaug0 f) q = 0`
then the image of `q` in the section ring of `Eobj U 0 x₀`, where `x₀ : Fin 1 → ι` is the
constant index with value `i`, is zero.

Indeed the `x₀`-th component of the coaugmentation is the composite
`unitTop ≫ (specPresheaf R).map (homOfLE le_top).op` (the component formula for
`Pi.lift`), and `unitTop` is the structure map `R → Γ(Spec R, ⊤)` corresponding to the
identity of `Spec R`, i.e. `(ΓSpecIso).inv`. -/
lemma algebraMap_secRing_Eobj_eq_zero (f : ι → R) (i : ι) (q : R)
    (hq : (coaug0 f).hom q = 0) :
    algebraMap R ↑(secRing R (Eobj (basicOpens f) 0 (fun _ : Fin 1 => i))) q = 0 := by
  have h1 : ((Pi.π (fun y : Fin 1 → ι => (specPresheaf R).obj (op (Eobj (basicOpens f) 0 y)))
      (fun _ : Fin 1 => i)).hom ((coaug0 f).hom q)) = 0 := by
    rw [hq]
    exact map_zero _
  have hcomp := Pi.lift_comp_π (β := Fin 1 → ι)
      (f := fun y : Fin 1 → ι => (specPresheaf R).obj (op (Eobj (basicOpens f) 0 y)))
      (p := fun y => unitTop R ≫ (specPresheaf R).map (homOfLE le_top).op) (fun _ : Fin 1 => i)
  have h2 : ((unitTop R ≫ (specPresheaf R).map (homOfLE (le_top :
      Eobj (basicOpens f) 0 (fun _ : Fin 1 => i) ≤ ⊤)).op)).hom q = 0 := by
    rw [← hcomp]
    exact h1
  rw [← resSection_le_top_GammaSpecIso_inv R
    (Eobj (basicOpens f) 0 (fun _ : Fin 1 => i)) q]
  exact h2

/-- **The component of the coaugmentation at a constant index, in the basic open form.**
The previous lemma, with `Eobj U 0 x₀` identified with `D (f i)`. -/
lemma algebraMap_secRing_basicOpen_eq_zero_of_coaug0 (f : ι → R) (i : ι) (q : R)
    (hq : (coaug0 f).hom q = 0) :
    algebraMap R ↑(secRing R (PrimeSpectrum.basicOpen (f i))) q = 0 := by
  rw [← Eobj_zero_const f i]
  exact algebraMap_secRing_Eobj_eq_zero f i q hq

/-- **Kernel of the structure map on a basic open.**  The section ring `Γ(D g)` is the
localization `R[1/g]`, so an element of `R` whose image in `Γ(D g)` vanishes is killed by
a power of `g`. -/
lemma exists_pow_mul_eq_zero_of_algebraMap_eq_zero (g q : R)
    (h : algebraMap R ↑(secRing R (PrimeSpectrum.basicOpen g)) q = 0) :
    ∃ k : ℕ, g ^ k * q = 0 := by
  haveI := StructureSheaf.IsLocalization.to_basicOpen (R := R) g
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g)
    ↑(secRing R (PrimeSpectrum.basicOpen g)) q).mp h
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff m.1 g).mp m.2
  exact ⟨k, by rw [hk]; exact hm⟩

theorem coaug0_injective {R : Type u} [CommRing R] {ι : Type u} [Fintype ι] (f : ι → R) (h : Ideal.span (Set.range f) = ⊤) : ∀ q : R, (Work.DSF1.Cech.coaug0 f).hom q = 0 → q = 0 := by
  intro q hq
  -- Every `f i` kills a power of `q`.
  have key : ∀ i : ι, ∃ k : ℕ, f i ^ k * q = 0 := fun i =>
    exists_pow_mul_eq_zero_of_algebraMap_eq_zero (f i) q
      (algebraMap_secRing_basicOpen_eq_zero_of_coaug0 f i q hq)
  -- Since the `f i` generate the unit ideal, `q` lies in every submodule, in particular `⊥`.
  have hmem : q ∈ (⊥ : Submodule R R) :=
    Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule R R) (Set.range f) h q (by
      rintro ⟨r, hr⟩
      obtain ⟨i, rfl⟩ := Set.mem_range.mp hr
      obtain ⟨k, hk⟩ := key i
      exact ⟨k, by simpa using hk⟩)
  simpa using hmem

end Work.DSF1.Cech
