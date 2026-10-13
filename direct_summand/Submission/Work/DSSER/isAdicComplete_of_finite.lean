import Mathlib
import Submission.Work.DSSER.Basic

universe u

namespace Work.DSSER

/-- A finite module over an `I`-adically complete Noetherian ring (`I ≤ jacobson`) is `I`-adically
complete (Stacks 05GG/05GH); apparently missing from Mathlib.
Route: `IsHausdorff.of_le_jacobson` for the Hausdorff half; for precompleteness use
`AdicCompletion.of_bijective_iff`, `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`
(`Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean`), `AdicCompletion.of_bijective` for `R`, and
`AdicCompletion.ofTensorProduct_tmul` to identify the composite with `of I M`. -/
theorem isAdicComplete_of_finite {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) [IsAdicComplete I R] : IsAdicComplete I M := by
  -- Hausdorff half: `I ≤ jacobson ⊥` forces `⋂ IⁿM = 0` (Stacks 05GH).
  have hH : IsHausdorff I M := IsHausdorff.of_le_jacobson I M hI
  have hsurj : Function.Surjective ⇑(AdicCompletion.of I M) := by
    -- `R` is `I`-adically complete, so `of I R : R → AdicCompletion I R` is bijective, hence so is
    -- the base change `of I R ⊗ id : R ⊗[R] M → AdicCompletion I R ⊗[R] M`.
    have h1 : AdicCompletion.of I R (1 : R) = 1 := by
      ext n
      simp
    have hmap : Function.Bijective ⇑(TensorProduct.map (AdicCompletion.of I R)
        (LinearMap.id : M →ₗ[R] M)) :=
      TensorProduct.map_bijective (AdicCompletion.of_bijective I R) Function.bijective_id
    -- Over a Noetherian ring, the completion of a finite module is its completion tensored up.
    have hcomp : Function.Bijective ⇑(AdicCompletion.ofTensorProduct I M) :=
      AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M
    -- The two maps agree on `M ≃ R ⊗[R] M`.
    have hkey : ⇑(AdicCompletion.of I M) = fun x : M =>
        AdicCompletion.ofTensorProduct I M
          (TensorProduct.map (AdicCompletion.of I R) (LinearMap.id : M →ₗ[R] M)
            ((TensorProduct.lid R M).symm x)) := by
      funext x
      rw [TensorProduct.lid_symm_apply, TensorProduct.map_tmul, h1,
        AdicCompletion.ofTensorProduct_tmul, one_smul, LinearMap.id_apply]
    rw [hkey]
    exact hcomp.surjective.comp (hmap.surjective.comp (TensorProduct.lid R M).symm.surjective)
  exact { toIsHausdorff := hH, toIsPrecomplete := AdicCompletion.of_surjective_iff.mp hsurj }

end Work.DSSER
