import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The coefficientwise cast `(Fin n → ℚ) → (Fin n → ℂ)` as a `ℚ`-linear map. -/
noncomputable def castH (n : ℕ) : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℂ) :=
  LinearMap.pi (fun j : Fin n => (Algebra.linearMap ℚ ℂ).comp (LinearMap.proj j))

/-- If two families of rational vectors span the same `ℚ`-subspace, then the corresponding
families of complex vectors (entrywise cast) span the same `ℂ`-subspace. -/
lemma span_cast_rat_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}
    (u : ι → Fin n → ℚ) (v : κ → Fin n → ℚ)
    (h : Submodule.span ℚ (Set.range u) = Submodule.span ℚ (Set.range v)) :
    Submodule.span ℂ (Set.range (fun m : ι => fun j : Fin n => ((u m j : ℚ) : ℂ)))
      = Submodule.span ℂ (Set.range (fun m : κ => fun j : Fin n => ((v m j : ℚ) : ℂ))) := by
  have hU : Set.range (fun m : ι => fun j : Fin n => ((u m j : ℚ) : ℂ)) = castH n '' Set.range u :=
    Set.range_comp (castH n) u
  have hV : Set.range (fun m : κ => fun j : Fin n => ((v m j : ℚ) : ℂ)) = castH n '' Set.range v :=
    Set.range_comp (castH n) v
  rw [hU, hV,
    ← Submodule.span_span_of_tower ℚ ℂ (castH n '' Set.range u),
    ← Submodule.span_span_of_tower ℚ ℂ (castH n '' Set.range v),
    ← Submodule.map_span (castH n) (Set.range u),
    ← Submodule.map_span (castH n) (Set.range v)]
  rw [h]

end Work.BW
