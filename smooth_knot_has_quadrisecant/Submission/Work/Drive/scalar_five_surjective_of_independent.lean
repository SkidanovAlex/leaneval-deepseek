import Mathlib

/-!
# Independent functionals give a surjective evaluation map (`Fin 5` version)

`Fin 5`-instance of `Work.Drive.scalar_surjective_of_independent`
(`Submission/Work/Drive/scalar_surjective_of_independent.lean`): if the five linear functionals
`d ↦ ∑ j, ℓ i j * d j` on `ℝ⁹` are linearly independent, then the evaluation map
`d ↦ (∑ j, ℓ i j * d j)_i` from `ℝ⁹` to `ℝ⁵` is surjective (finite-dimensional duality,
`LinearMap.dualMap_injective_iff`).
-/

namespace Work.Drive

noncomputable section

/-- The dual pairing of a linear functional on `Fin 5 → ℝ` with a vector, expanded in the standard
basis. -/
theorem dual_pi_apply5 (ψ : (Fin 5 → ℝ) →ₗ[ℝ] ℝ) (y : Fin 5 → ℝ) :
    ψ y = ∑ i : Fin 5, y i * ψ (Pi.single i (1 : ℝ)) := by
  have hy : y = ∑ i : Fin 5, y i • (Pi.single i (1 : ℝ) : Fin 5 → ℝ) := by
    conv_lhs => rw [← (Pi.basisFun ℝ (Fin 5)).sum_repr y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.basisFun_repr, Pi.basisFun_apply]
  conv_lhs => rw [hy]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]

/-- **Independence of the five functionals implies surjectivity of the evaluation map.** -/
theorem scalar_five_surjective_of_independent {ℓ : Fin 5 → Fin 9 → ℝ}
    (hind : ∀ c : Fin 5 → ℝ, (∀ j : Fin 9, ∑ i : Fin 5, c i * ℓ i j = 0) → c = 0) :
    ∀ A : Fin 5 → ℝ, ∃ d : Fin 9 → ℝ, ∀ i : Fin 5, ∑ j : Fin 9, ℓ i j * d j = A i := by
  let T : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) :=
    { toFun := fun d i => ∑ j : Fin 9, ℓ i j * d j
      map_add' := by
        intro d e
        funext i
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a d
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by simp only [RingHom.id_apply]; ring }
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.dualMap_injective_iff (f := T)]
    intro Φ Ψ hΦΨ
    have hcomp : ∀ d : Fin 9 → ℝ, Φ (T d) = Ψ (T d) := by
      intro d
      have h := congrArg (fun f : (Fin 9 → ℝ) →ₗ[ℝ] ℝ => f d) hΦΨ
      simpa only [LinearMap.dualMap_apply] using h
    set Λ : (Fin 5 → ℝ) →ₗ[ℝ] ℝ := Φ - Ψ with hΛ
    have hΛT : ∀ d : Fin 9 → ℝ, Λ (T d) = 0 := by
      intro d
      rw [hΛ]
      simp only [LinearMap.sub_apply]
      rw [hcomp d, sub_self]
    have hΛsingle : ∀ i : Fin 5, Λ (Pi.single i (1 : ℝ)) = 0 := by
      intro i
      refine congrFun (hind (fun i => Λ (Pi.single i (1 : ℝ))) ?_) i
      intro j
      have h0 : Λ (T (Pi.single j (1 : ℝ) : Fin 9 → ℝ)) = 0 := hΛT _
      rw [dual_pi_apply5 Λ (T (Pi.single j (1 : ℝ) : Fin 9 → ℝ))] at h0
      have hcoord : ∀ i : Fin 5, (T (Pi.single j (1 : ℝ) : Fin 9 → ℝ)) i = ℓ i j := by
        intro i
        show (∑ j' : Fin 9, ℓ i j' * (Pi.single j (1 : ℝ) : Fin 9 → ℝ) j') = ℓ i j
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
        · intro hj; exact absurd (Finset.mem_univ j) hj
      calc ∑ i : Fin 5, Λ (Pi.single i (1 : ℝ)) * ℓ i j
          = ∑ i : Fin 5, (T (Pi.single j (1 : ℝ) : Fin 9 → ℝ)) i * Λ (Pi.single i (1 : ℝ)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hcoord i]; ring
        _ = 0 := h0
    refine LinearMap.ext fun y => ?_
    have hΛy : Λ y = 0 := by
      rw [dual_pi_apply5 Λ y]
      exact Finset.sum_eq_zero fun i _ => by rw [hΛsingle i, mul_zero]
    rw [hΛ] at hΛy
    simpa only [LinearMap.sub_apply, sub_eq_zero] using hΛy
  intro A
  obtain ⟨d, hd⟩ := hsurj A
  exact ⟨d, fun i => congrFun hd i⟩

end

end Work.Drive
