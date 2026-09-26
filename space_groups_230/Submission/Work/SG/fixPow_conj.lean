import Mathlib
import Submission.Work.SG.arithDefs

namespace Work.SG

open scoped BigOperators Matrix

/-- Fixed-point-count power sums of the action on `(ℤ/m)³` are invariant under conjugation by a
unimodular integer matrix.

Definitions (in `Submission.Work.SG.arithRep_conj_eq`, namespace `Work.SG`):
`redmod m A = A.map (Int.castRingHom (ZMod m))`,
`actm m A v = (redmod m A).mulVec v`,
`nfix m P v = (P.filter fun A => actm m A v = v).card`,
`fixPow m P k = ∑ v : Fin 3 → ZMod m, ((nfix m P v : ℤ)) ^ k` (`m` has a `[NeZero m]` instance
argument because `Fintype (ZMod m)` needs it).

Suggested route: `redmod` is multiplicative (`Matrix.map_mul`), so with `hU : IsUnit U.det`,
`redmod m U` is invertible with inverse `redmod m U⁻¹` (from `Matrix.nonsing_inv_mul`). Hence
`ψ v := (redmod m U).mulVec v` is an equivalence of `Fin 3 → ZMod m` (`Matrix.mulVec_mulVec`,
`Matrix.one_mulVec`). It intertwines the actions:
`actm m (U * A * U⁻¹) (ψ v) = ψ (actm m A v)` (expand `redmod m (U * A * U⁻¹)` and use
`redmod m U⁻¹ * redmod m U = 1`). Together with `P' = P.image (fun A => U * A * U⁻¹)`
(from `Finset.ext` applied to `h`), `Finset.filter_image`,
`Finset.card_image_of_injective` and the injectivity of `ψ`, this gives
`nfix m P' (ψ v) = nfix m P v` for all `v`. Reindexing the sum along the equivalence `ψ`
(`Equiv.sum_comp`) gives the claim. -/
theorem fixPow_conj {P P' : Finset IMat} {U : IMat} (hU : IsUnit U.det)
    (h : ∀ A, A ∈ P' ↔ ∃ B ∈ P, A = U * B * U⁻¹) (m : ℕ) [NeZero m] (k : ℕ) :
    fixPow m P' k = fixPow m P k := by
  -- `redmod` is multiplicative and preserves `1`.
  have hredmul : ∀ A B : IMat, redmod m (A * B) = redmod m A * redmod m B :=
    fun A B => Matrix.map_mul
  have hredone : redmod m (1 : IMat) = 1 :=
    Matrix.map_one (Int.castRingHom (ZMod m)) (map_zero _) (map_one _)
  set M : Matrix (Fin 3) (Fin 3) (ZMod m) := redmod m U with hM
  set N : Matrix (Fin 3) (Fin 3) (ZMod m) := redmod m U⁻¹ with hN
  have hNM : N * M = 1 := by
    rw [hN, hM, ← hredmul U⁻¹ U, Matrix.nonsing_inv_mul U hU, hredone]
  have hMN : M * N = 1 := by
    rw [hM, hN, ← hredmul U U⁻¹, Matrix.mul_nonsing_inv U hU, hredone]
  have hNMv : ∀ v : Fin 3 → ZMod m, N *ᵥ (M *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
  -- the change of coordinates induced by `U`
  let ψ : (Fin 3 → ZMod m) ≃ (Fin 3 → ZMod m) :=
    { toFun := fun v => M *ᵥ v
      invFun := fun v => N *ᵥ v
      left_inv := fun v => hNMv v
      right_inv := fun v => by
        show M *ᵥ (N *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec] }
  have hψ : ∀ v : Fin 3 → ZMod m, ψ v = M *ᵥ v := fun v => rfl
  -- `ψ` intertwines the conjugated action with the original one
  have hinter : ∀ (A : IMat) (v : Fin 3 → ZMod m),
      actm m (U * A * U⁻¹) (ψ v) = ψ (actm m A v) := by
    intro A v
    have hred : redmod m (U * A * U⁻¹) = M * redmod m A * N := by
      rw [hredmul (U * A) U⁻¹, hredmul U A, hM, hN]
    simp only [hψ, actm]
    rw [hred]
    calc (M * redmod m A * N) *ᵥ (M *ᵥ v)
        = (M * redmod m A) *ᵥ (N *ᵥ (M *ᵥ v)) :=
          (Matrix.mulVec_mulVec (M *ᵥ v) (M * redmod m A) N).symm
      _ = (M * redmod m A) *ᵥ v := by rw [hNMv v]
      _ = M *ᵥ (redmod m A *ᵥ v) :=
          (Matrix.mulVec_mulVec v M (redmod m A)).symm
  -- conjugation by `U` is injective on integer matrices
  have hφinj : Function.Injective (fun A : IMat => U * A * U⁻¹) := by
    intro A B hAB
    have key : ∀ X : IMat, U⁻¹ * (U * X * U⁻¹) * U = X := by
      intro X
      rw [← Matrix.mul_assoc U⁻¹ (U * X) U⁻¹,
        Matrix.nonsing_inv_mul_cancel_right U (U⁻¹ * (U * X)) hU,
        Matrix.nonsing_inv_mul_cancel_left U X hU]
    exact (key A).symm.trans ((congrArg (fun X => U⁻¹ * X * U) hAB).trans (key B))
  -- `P'` is the image of `P` under conjugation
  have hP' : P' = P.image (fun A : IMat => U * A * U⁻¹) := by
    ext A
    rw [Finset.mem_image]
    exact ⟨fun hA => by
        obtain ⟨B, hB, hBA⟩ := (h A).mp hA
        exact ⟨B, hB, hBA.symm⟩,
      fun hA => by
        obtain ⟨B, hB, hBA⟩ := hA
        exact (h A).mpr ⟨B, hB, hBA.symm⟩⟩
  -- the two fixed-point counts agree
  have hnfix : ∀ v : Fin 3 → ZMod m, nfix m P' (ψ v) = nfix m P v := by
    intro v
    have hfilt : (P.filter (fun B => actm m (U * B * U⁻¹) (ψ v) = ψ v))
        = (P.filter fun B => actm m B v = v) := by
      apply Finset.filter_congr
      intro B _
      rw [hinter B v]
      exact Function.Injective.eq_iff ψ.injective
    unfold nfix
    rw [hP', Finset.filter_image, Finset.card_image_of_injective _ hφinj, hfilt]
  show (∑ v : Fin 3 → ZMod m, ((nfix m P' v : ℤ)) ^ k)
      = ∑ v : Fin 3 → ZMod m, ((nfix m P v : ℤ)) ^ k
  calc (∑ v : Fin 3 → ZMod m, ((nfix m P' v : ℤ)) ^ k)
      = ∑ v : Fin 3 → ZMod m, ((nfix m P' (ψ v) : ℤ)) ^ k :=
        (Equiv.sum_comp ψ (fun v => ((nfix m P' v : ℤ)) ^ k)).symm
    _ = ∑ v : Fin 3 → ZMod m, ((nfix m P v : ℤ)) ^ k := by
        refine Finset.sum_congr rfl ?_
        intro v _
        rw [hnfix v]

end Work.SG
