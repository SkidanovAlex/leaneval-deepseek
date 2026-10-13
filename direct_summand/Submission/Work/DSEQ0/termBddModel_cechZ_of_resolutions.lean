import Mathlib
import Submission.Work.DSEQ0.exists_bounded_free_model
import Submission.Work.DSEQ0.Coaug

universe a

namespace Work.DSEQ0

open CategoryTheory Limits

/-- **Termwise bounded finite free models of the Čech complex from resolutions of its
cohomology.**

Let `C = Ĉ(U; 𝒪_X)` be the Čech cochain complex of a family of opens `U` on a scheme `X` over
`A` (concentrated in degrees `≥ 0`), whose cohomology vanishes above `N`, and suppose that for
every `i` we are given a bounded complex `G i` of finite free `A`-modules together with a
quasi-isomorphism `G i ⟶ single i (Hⁱ(C))`.  Then `C` admits a quasi-isomorphism `q : P ⟶ C`
with `P` a complex of finite free `A`-modules that is bounded in both directions.

Proof: `C` is cohomologically supported in degrees `≤ N` (`C.IsLE N`), so `C.ιTruncLE m` is a
quasi-isomorphism for `m = max N 0` (its source is supported in `[0, m]` and both complexes
have the same cohomology); applying `Work.DSEQ0.exists_bounded_free_model` to `C.truncLE m` with
the transported resolutions `G i` produces the model. -/
theorem termBddModel_cechZ_of_resolutions (A : Type a) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{a}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    {ι : Type a} (U : ι → X.Opens) (N : ℤ)
    (hhi : ∀ i : ℤ, N < i →
      CategoryTheory.Limits.IsZero ((DSMap.cechZ A X f U).homology i))
    (G : ℤ → CochainComplex (ModuleCat.{a} A) ℤ)
    (hGfin : ∀ i j, Module.Finite A ((G i).X j))
    (hGfree : ∀ i j, Module.Free A ((G i).X j))
    (hGbdd : ∀ i, ∃ a b : ℤ, ∀ j, j < a ∨ b < j →
      CategoryTheory.Limits.IsZero ((G i).X j))
    (hGres : ∀ i : ℤ, ∃ g : G i ⟶
      (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) i).obj
        ((DSMap.cechZ A X f U).homology i), QuasiIso g) :
    ∃ (P : CochainComplex (ModuleCat.{a} A) ℤ),
      (∀ i, Module.Finite A (P.X i)) ∧ (∀ i, Module.Free A (P.X i)) ∧
      (∃ a b : ℤ, ∀ i, i < a ∨ b < i → CategoryTheory.Limits.IsZero (P.X i)) ∧
      ∃ q : P ⟶ DSMap.cechZ A X f U, QuasiIso q := by
  letI : HasDerivedCategory (ModuleCat.{a} A) := HasDerivedCategory.standard (ModuleCat.{a} A)
  set C : CochainComplex (ModuleCat.{a} A) ℤ := DSMap.cechZ A X f U with hC
  -- The cohomology of `C` vanishes above `N`.
  have hCex : ∀ i : ℤ, N < i → C.ExactAt i := fun i hi =>
    (HomologicalComplex.exactAt_iff_isZero_homology C i).mpr (hhi i hi)
  haveI hCleN : C.IsLE N := (CochainComplex.isLE_iff C N).mpr hCex
  -- The truncation degree `m = max N 0` (as a natural number).
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = max N 0 :=
    ⟨(max N 0).toNat, Int.toNat_of_nonneg (le_max_right N 0)⟩
  have hNm : N ≤ (m : ℤ) := by rw [hm]; exact le_max_left N 0
  haveI hClem : C.IsLE (m : ℤ) := CochainComplex.isLE_of_le C N (m : ℤ) hNm
  haveI hQI : QuasiIso (C.ιTruncLE (m : ℤ)) :=
    (CochainComplex.quasiIso_ιTruncLE_iff (K := C) (n := (m : ℤ))).mpr inferInstance
  -- The truncation is concentrated in degrees `[0, m]`.
  have hC' : ∀ i : ℤ, i < 0 ∨ (m : ℤ) < i → IsZero ((C.truncLE (m : ℤ)).X i) := by
    intro i hi
    rcases hi with hi | hi
    · have hilt : i < (m : ℤ) := by omega
      exact IsZero.of_iso (isZero_cechZ_X_of_neg A X f U hi)
        (CochainComplex.truncLEXIso (K := C) (n := (m : ℤ)) (i := i) hilt)
    · exact CochainComplex.isZero_of_isStrictlyLE (C.truncLE (m : ℤ)) (m : ℤ) i hi
  -- The resolutions of the cohomology of the truncation, transported along `ιTruncLE`.
  have hGres' : ∀ i : ℤ, ∃ g : G i ⟶
      (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) i).obj
        ((C.truncLE (m : ℤ)).homology i), QuasiIso g := by
    intro i
    obtain ⟨g, hg⟩ := hGres i
    haveI : QuasiIso g := hg
    haveI : IsIso (HomologicalComplex.homologyMap (C.ιTruncLE (m : ℤ)) i) :=
      (quasiIsoAt_iff_isIso_homologyMap (C.ιTruncLE (m : ℤ)) i).mp inferInstance
    exact ⟨g ≫ ((HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) i).mapIso
      (asIso (HomologicalComplex.homologyMap (C.ιTruncLE (m : ℤ)) i)).symm).hom,
      inferInstance⟩
  obtain ⟨P, hPfin, hPfree, hPbdd, q', hq'⟩ :=
    exists_bounded_free_model (A := A) m (C.truncLE (m : ℤ)) hC' G hGfin hGfree hGbdd hGres'
  haveI : QuasiIso q' := hq'
  exact ⟨P, hPfin, hPfree, hPbdd, q' ≫ C.ιTruncLE (m : ℤ), inferInstance⟩

end Work.DSEQ0
