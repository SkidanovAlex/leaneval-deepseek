import Mathlib
import Submission.NK.ReconstructField.Input

namespace NK.ReconstructField

/-- Helper: the chosen lift of the identity base-field isomorphism fixes the embedded base field. -/
theorem liftBase_refl_fix {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (x : K) :
    liftBase K K K' K' (RingEquiv.refl K) (algebraMap K K' x) = algebraMap K K' x := by
  simpa using liftBase_apply_base K K K' K' (RingEquiv.refl K) x

/-- Helper: the inverse of the chosen lift of the identity base-field isomorphism fixes the
embedded base field. -/
theorem liftBase_refl_symm_fix {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (x : K) :
    (liftBase K K K' K' (RingEquiv.refl K)).symm (algebraMap K K' x) = algebraMap K K' x :=
  (liftBase K K K' K' (RingEquiv.refl K)).symm_apply_eq.mpr (liftBase_refl_fix x).symm

/-- **Helper**: with `h : Gal(K'/K)` induced by the inverse of the chosen lift of the identity
base-field isomorphism, the corresponding twist of the identity lift is the identity isomorphism
of `K'`. -/
theorem liftTwist_refl_liftBase_symm {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] :
    ∃ h : Gal(K'/K), liftTwist K K K' K' (RingEquiv.refl K) h = RingEquiv.refl K' := by
  refine ⟨AlgEquiv.ofRingEquiv
    (f := (liftBase K K K' K' (RingEquiv.refl K)).symm) (fun x => liftBase_refl_symm_fix x), ?_⟩
  ext x
  rw [liftTwist_apply, AlgEquiv.ofRingEquiv_apply]
  exact RingEquiv.apply_symm_apply (liftBase K K K' K' (RingEquiv.refl K)) x

/-- **Non-vacuity of the reconstruction input in the trivial case.**

Let `K₁ = K₂ = K` (literally the same field), `K'` a separable closure of `K`, `ϕ = id` on
`Gal(K'/K)`, and `a : LocalCorrespondence (MulEquiv.refl Gal(K'/K))` a local correspondence whose
place map is the identity (`ha`).  Then the reconstruction input holds: take `τ := RingEquiv.refl`,
and `h := (liftBase K K K' K' RingEquiv.refl)⁻¹`, for which
`liftTwist K K K' K' RingEquiv.refl h` is the identity isomorphism and the place correspondence is
realized trivially.  This shows that the interface of
`NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius` is satisfiable for a genuinely
inhabited `LocalCorrespondence` (it is not vacuous). -/
theorem reconstructionInput_refl
    {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (a : NK.Reconstruct.LocalCorrespondence (MulEquiv.refl Gal(K'/K)))
    (ha : ∀ A : NK.Reconstruct.FinitePlaceOf K K', a.placeMap A = A)
    (he : IsHomeomorph (MulEquiv.refl Gal(K'/K))) :
    NK.ReconstructField.ReconstructionInput (K₁ := K) (K₂ := K) (K₁' := K') (K₂' := K')
      he a := by
  obtain ⟨h, hlt⟩ := liftTwist_refl_liftBase_symm (K := K) (K' := K')
  refine ⟨RingEquiv.refl K, h, ?_⟩
  intro A
  rw [hlt, ha A]
  ext x
  simp

end NK.ReconstructField
