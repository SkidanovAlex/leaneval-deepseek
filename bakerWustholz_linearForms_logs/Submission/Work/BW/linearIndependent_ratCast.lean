import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Base change from `ℚ` to `ℝ` preserves linear independence for families of
rational-valued functions on a finite product `m × ι`. -/
theorem linearIndependent_ratCast {ι_fam : Type*} {m ι : Type*} [Fintype m] [Fintype ι]
    {v : ι_fam → (m → ι → ℚ)} :
    LinearIndependent ℝ (fun i => fun (j : m) (l : ι) => ((v i j l : ℚ) : ℝ)) ↔
      LinearIndependent ℚ v := by
  classical
  -- Curry the two function levels `m → ι → ℚ` and `m → ι → ℝ`.
  let eQ : (m × ι → ℚ) ≃ₗ[ℚ] (m → ι → ℚ) :=
    { Equiv.curry m ι ℚ with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let eR : (m × ι → ℝ) ≃ₗ[ℝ] (m → ι → ℝ) :=
    { Equiv.curry m ι ℝ with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let w : ι_fam → (m × ι → ℚ) := fun i p => v i p.1 p.2
  have keyQ : LinearIndependent ℚ v ↔ LinearIndependent ℚ w := by
    have h : v = (eQ : (m × ι → ℚ) → (m → ι → ℚ)) ∘ w := rfl
    rw [h]
    exact LinearMap.linearIndependent_iff (eQ : (m × ι → ℚ) →ₗ[ℚ] (m → ι → ℚ)) eQ.ker
  have keyR : LinearIndependent ℝ (fun i => fun (j : m) (l : ι) => ((v i j l : ℚ) : ℝ)) ↔
      LinearIndependent ℝ (fun i => fun (p : m × ι) => ((w i p : ℚ) : ℝ)) := by
    have h : (fun i => fun (j : m) (l : ι) => ((v i j l : ℚ) : ℝ)) =
        (eR : (m × ι → ℝ) → (m → ι → ℝ)) ∘
          (fun i => fun (p : m × ι) => ((w i p : ℚ) : ℝ)) := rfl
    rw [h]
    exact LinearMap.linearIndependent_iff (eR : (m × ι → ℝ) →ₗ[ℝ] (m → ι → ℝ)) eR.ker
  have keyB : LinearIndependent ℝ (fun i => fun (p : m × ι) => ((w i p : ℚ) : ℝ)) ↔
      LinearIndependent ℚ w :=
    linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ) (v := w)
  exact keyR.trans (keyB.trans keyQ.symm)

end Work.BW
