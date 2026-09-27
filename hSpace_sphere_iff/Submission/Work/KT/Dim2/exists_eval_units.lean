import Mathlib

namespace Work.KT.Dim2

/-- Pointwise evaluation of a matrix of continuous functions (identified with the matrix whose
entries are the evaluations of the entries) is continuous when the matrix ring carries the product
topology. -/
private lemma continuous_eval_mapMatrix {X : Type} [TopologicalSpace X] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Continuous (fun x : X =>
      RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom M) := by
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  have := (M i j).continuous
  convert this using 1
  funext a
  exact ContinuousMap.evalAlgHom_apply ℂ ℂ a (M i j)

theorem exists_eval_units {X : Type} [TopologicalSpace X] (n : ℕ)
    (u : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) :
    ∃ u' v' : C(X, Matrix (Fin n) (Fin n) ℂ),
      (∀ x, u' x = RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
        (u : Matrix (Fin n) (Fin n) C(X, ℂ))) ∧
      (∀ x, v' x = RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
        (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))) ∧
      (∀ x, u' x * v' x = 1 ∧ v' x * u' x = 1) := by
  refine ⟨⟨fun x => RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
        (u : Matrix (Fin n) (Fin n) C(X, ℂ)), continuous_eval_mapMatrix n _⟩,
    ⟨fun x => RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
        (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ)), continuous_eval_mapMatrix n _⟩,
    fun x => rfl, fun x => rfl, fun x => ⟨?_, ?_⟩⟩
  · show (RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
        (u : Matrix (Fin n) (Fin n) C(X, ℂ))) *
      (RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
        (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))) = 1
    rw [← map_mul, Units.mul_inv, map_one]
  · show (RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
        (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))) *
      (RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
        (u : Matrix (Fin n) (Fin n) C(X, ℂ))) = 1
    rw [← map_mul, Units.inv_mul, map_one]

end Work.KT.Dim2
