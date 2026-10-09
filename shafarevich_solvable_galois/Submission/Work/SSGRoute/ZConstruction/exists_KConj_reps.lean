import Mathlib
import Submission.Work.SSGRoute.ZConstruction.AuxInterface
import Submission.Work.SSGRoute.ZConstruction.exists_finset_KConj_cover
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute
open scoped Pointwise

set_option linter.unusedVariables false

/-- **One representative per level-`K` class of a finite place set.**  For a finite set `S` of finite
places there is a finite set `T` of pairwise level-`K`-non-conjugate finite places which consists of
places `G_k`-conjugate into `S` (so `T ⊆ cs(S)`), and which meets every level-`K` class of `cs(S)`:
`∃ A' ∈ T, Work.SSGRoute.KConj K A' B` for every place `B` of `Ω` that is `G_k`-conjugate to an
element of `S`.

This is the place set on which the p. 18 diagram chase runs: the relaxed dual Selmer conditions are
formulated at the level-`K` classes of `S`, so one needs a system of representatives of those classes
*inside* `cs(S)` (the statement of `Work.SSGRoute.ZConstruction.exists_finset_KConj_cover` provides a
cover but does not assert that its elements lie in `cs(S')`, and for the orthogonality gate the
representatives must be conjugate into `S`).  Pure place/Galois bookkeeping.

Hints: build `W := ⋃_{A ∈ S} {lift φ • A : φ ∈ (K ≃ₐ[k] K)}` with `lift φ := φ.liftNormal Ω`
(as in `exists_finset_KConj_cover`), then take one `Quotient.out` per class of the level-`K` setoid
`Work.SSGRoute.ZConstruction.kConjSetoid K` over `W`; the `lift φ • A` construction is needed for the
cover clause (the classes of `S` alone do not cover the classes of its `G_k`-orbit), and each
`lift φ • A` is `G_k`-conjugate to `A ∈ S`, so it lies in `cs(S)`.  `S` is *not* assumed pairwise
`G_k`-non-conjugate here, so reduce to one element per `G_k` class first (or build `W` directly).
`IsConjPlace k A B` with `A` finite gives `B` finite, so the cover clause needs no finiteness
hypothesis. -/
theorem exists_KConj_reps {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) :
    ∃ T : Finset (ValuationSubring Ω),
      (∀ A ∈ T, SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.KConj K A B → A = B) ∧
      (∀ A ∈ T, ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A) ∧
      (∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∃ A' ∈ T, Work.SSGRoute.KConj K A' B) := by
  classical
  -- A chosen lift of an element of `Gal(K/k)` to `G_k`.
  let lift : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω) := fun φ => φ.liftNormal Ω
  have lift_spec : ∀ φ : K ≃ₐ[k] K, AlgEquiv.restrictNormalHom (↥K) (lift φ) = φ := by
    intro φ
    rw [show AlgEquiv.restrictNormalHom (↥K) (lift φ) = (lift φ).restrictNormal (↥K) from rfl]
    exact AlgEquiv.restrict_liftNormal Ω φ
  -- The `G_k`-orbit of `S`, presented as a finite set of places through the chosen lifts.
  set W : Finset (ValuationSubring Ω) :=
    S.biUnion (fun A => (Finset.univ : Finset (K ≃ₐ[k] K)).image (fun φ => lift φ • A))
      with hW
  have hWfin : ∀ w ∈ W, SSGRoute.IsFinPlace k w := by
    intro w hw
    rw [hW, Finset.mem_biUnion] at hw
    obtain ⟨A, hAS, hwA⟩ := hw
    rw [Finset.mem_image] at hwA
    obtain ⟨φ, -, rfl⟩ := hwA
    exact (isFinPlace_smul_iff A (lift φ)).mpr (hSfin A hAS)
  -- One representative per level-`K` class met by `W`.
  set T : Finset (ValuationSubring Ω) :=
    (W.image (fun w => Quotient.mk (kConjSetoid K) w)).image (fun q => Quotient.out q) with hT
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · -- finiteness of the places of `T`
    intro A hA
    rw [hT, Finset.mem_image] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    rw [Finset.mem_image] at hq
    obtain ⟨w, hwW, hwq⟩ := hq
    have hout : Work.SSGRoute.KConj K (Quotient.out q) w := by
      rw [← hwq]
      exact Quotient.exact (Quotient.out_eq (Quotient.mk (kConjSetoid K) w))
    exact isFinPlace_of_isConjPlace (hWfin w hwW)
      (SSGRoute.isConjPlace_symm (kConj_isConjPlace hout))
  · -- pairwise level-`K`-non-conjugacy
    intro A hA B hB hAB
    rw [hT, Finset.mem_image] at hA hB
    obtain ⟨qA, -, rfl⟩ := hA
    obtain ⟨qB, -, rfl⟩ := hB
    have hqq : Quotient.mk (kConjSetoid K) (Quotient.out qA) =
        Quotient.mk (kConjSetoid K) (Quotient.out qB) := Quotient.sound hAB
    rw [Quotient.out_eq qA, Quotient.out_eq qB] at hqq
    rw [hqq]
  · -- `T` consists of places `G_k`-conjugate into `S`
    intro A hA
    rw [hT, Finset.mem_image] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    rw [Finset.mem_image] at hq
    obtain ⟨w, hwW, hwq⟩ := hq
    rw [hW, Finset.mem_biUnion] at hwW
    obtain ⟨A0, hA0S, hwA0⟩ := hwW
    rw [Finset.mem_image] at hwA0
    obtain ⟨φ, -, hφ⟩ := hwA0
    refine ⟨A0, hA0S, ?_⟩
    have hout : Work.SSGRoute.KConj K (Quotient.out q) w := by
      rw [← hwq]
      exact Quotient.exact (Quotient.out_eq (Quotient.mk (kConjSetoid K) w))
    exact SSGRoute.isConjPlace_trans ⟨lift φ, hφ⟩
      (SSGRoute.isConjPlace_symm (kConj_isConjPlace hout))
  · -- the cover clause
    intro B hconjB
    obtain ⟨A0, hA0S, hA0B⟩ := hconjB
    obtain ⟨σ, hσ⟩ := hA0B
    set φ : K ≃ₐ[k] K := AlgEquiv.restrictNormalHom (↥K) σ with hφdef
    have hker : (AlgEquiv.restrictNormalHom (↥K)) (σ * (lift φ)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hφdef, lift_spec φ, mul_inv_cancel]
    have hmem : σ * (lift φ)⁻¹ ∈ K.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker K]
      exact MonoidHom.mem_ker.mpr hker
    have hKconj : Work.SSGRoute.KConj K (lift φ • A0) B := by
      refine ⟨σ * (lift φ)⁻¹, hmem, ?_⟩
      rw [← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
      exact hσ
    have hwW : lift φ • A0 ∈ W := by
      rw [hW, Finset.mem_biUnion]
      exact ⟨A0, hA0S, Finset.mem_image.mpr ⟨φ, Finset.mem_univ φ, rfl⟩⟩
    refine ⟨Quotient.out (Quotient.mk (kConjSetoid K) (lift φ • A0)), ?_, ?_⟩
    · rw [hT, Finset.mem_image]
      exact ⟨Quotient.mk (kConjSetoid K) (lift φ • A0),
        Finset.mem_image.mpr ⟨lift φ • A0, hwW, rfl⟩, rfl⟩
    · exact kConj_trans
        (Quotient.exact (Quotient.out_eq (Quotient.mk (kConjSetoid K) (lift φ • A0))))
        hKconj

end Work.SSGRoute.ZConstruction
