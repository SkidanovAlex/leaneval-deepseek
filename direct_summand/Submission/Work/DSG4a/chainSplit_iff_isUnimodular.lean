import Mathlib
import Submission.Work.DSG4a.Criterion

/-!
# DSG4a: `ChainSplit` is equivalent to unimodularity of the model element

This file proves the bridge recorded in `Submission/Work/DSG4a/Criterion.lean`:

`ChainSplit P cc ↔ Module.IsUnimodular A (modelElem P cc)`

for a cochain complex `P` of `A`-modules and a coaugmentation `cc : A[0] ⟶ P`.

Both sides are statements about the module `M := P.X 0` and the submodule
`p := range (d⁻¹ : P.X (-1) → P.X 0)`:

* `ChainSplit P cc` says that there is `s : M →ₗ[A] A` with `s ∘ d⁻¹ = 0` and
  `s (coaugElem P cc) = 1`, i.e. `s` kills `p` and takes the value `1` at the element `e`;
* `IsUnimodular A (modelElem P cc)` says that there is `f : M ⧸ p →ₗ[A] A` with
  `f [e] = 1`.

The two are interchangeable because a functional on `M ⧸ p` is the same thing as a
functional on `M` killing `p` (`Submodule.liftQ` in one direction, composition with the
quotient map `p.mkQ` in the other), and because `p ≤ ker s ↔ s ∘ d⁻¹ = 0`
(`LinearMap.range_le_ker_iff`).  The first of these two facts is the general lemma
`quotient_dual_one_iff` below; it is stated for an arbitrary module and submodule and is
the whole content of the equivalence, the rest being bookkeeping.
-/

namespace Work.DSG4a

open CategoryTheory

universe u

/-- **Functionals on a quotient**: a linear functional on `M ⧸ p` taking the value `1` at
the class of `e` is the same thing as a linear functional on `M` which vanishes on `p` and
takes the value `1` at `e`.

This is the standard adjunction between `Submodule.liftQ` and `Submodule.mkQ`. -/
theorem quotient_dual_one_iff {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M]
    [Module A M] (p : Submodule A M) (e : M) :
    (∃ f : M ⧸ p →ₗ[A] A, f (Submodule.mkQ p e) = 1) ↔
      ∃ s : M →ₗ[A] A, p ≤ LinearMap.ker s ∧ s e = 1 := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f.comp (Submodule.mkQ p), ?_, ?_⟩
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply]
      show f (Submodule.Quotient.mk x) = 0
      rw [(Submodule.Quotient.mk_eq_zero p).mpr hx, map_zero]
    · simpa [Submodule.mkQ_apply] using hf
  · rintro ⟨s, hs, hse⟩
    refine ⟨p.liftQ s hs, ?_⟩
    simpa [Submodule.mkQ_apply] using hse

theorem chainSplit_iff_isUnimodular {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj (ModuleCat.of A A) ⟶ P) :
    Work.DSG4a.Criterion.ChainSplit P cc ↔
      Module.IsUnimodular A (Work.DSG4a.Criterion.modelElem P cc) := by
  simp only [Criterion.ChainSplit, Criterion.modelElem, Module.isUnimodular_iff]
  rw [quotient_dual_one_iff (LinearMap.range (P.d (-1) 0).hom) (Criterion.coaugElem P cc)]
  constructor
  · rintro ⟨s, hs, hse⟩
    exact ⟨s, LinearMap.range_le_ker_iff.mpr hs, hse⟩
  · rintro ⟨s, hs, hse⟩
    exact ⟨s, LinearMap.range_le_ker_iff.mp hs, hse⟩

end Work.DSG4a
