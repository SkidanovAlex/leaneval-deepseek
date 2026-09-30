import Mathlib
import Submission.Work.BW.DefsMP

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Casting `extM σ M' j` to `ℚ` is the same as extending the `ℚ`-vector `M' j` by zero. -/
lemma extM_cast_rat {r N ρ : ℕ} (σ : Fin N → Fin r)
    (M' : Fin ρ → Fin N → ℤ) (j : Fin ρ) :
    (fun i : Fin r => ((extM σ M' j i : ℤ) : ℚ)) =
      Function.extend σ (fun k : Fin N => ((M' j k : ℤ) : ℚ)) 0 := by
  funext i
  change ((Function.extend σ (M' j) 0 i : ℤ) : ℚ) =
      Function.extend σ (fun k : Fin N => ((M' j k : ℤ) : ℚ)) 0 i
  rw [Function.apply_extend (f := σ) (g := M' j) (fun z : ℤ => (z : ℚ)) (0 : Fin r → ℤ) i]
  rfl

/-- `Function.extend σ · 0` preserves the membership in the span of the extended rows. -/
theorem mem_span_extM {r N ρ : ℕ} (σ : Fin N → Fin r) (hσ : Function.Injective σ)
    (M' : Fin ρ → Fin N → ℤ) (B : Fin r → ℤ)
    (hBZ : ∀ i : Fin r, i ∉ Set.range σ → B i = 0)
    (hB' : (fun i : Fin N => (B (σ i) : ℚ)) ∈
      Submodule.span ℚ (Set.range fun (j : Fin ρ) (i : Fin N) => (M' j i : ℚ))) :
    (fun i : Fin r => (B i : ℚ)) ∈
      Submodule.span ℚ (Set.range fun (j : Fin ρ) (i : Fin r) => (extM σ M' j i : ℚ)) := by
  classical
  -- The ℚ-linear "extension by zero along `σ`" map `Fin N → ℚ →ₗ[ℚ] Fin r → ℚ`.
  set L : (Fin N → ℚ) →ₗ[ℚ] (Fin r → ℚ) := Function.ExtendByZero.linearMap ℚ σ with hL
  set S : Set (Fin r → ℚ) :=
    Set.range fun (j : Fin ρ) (i : Fin r) => (extM σ M' j i : ℚ) with hS
  -- The rows of `M'` are mapped to the rows of `extM σ M'`.
  have hmap : ∀ x ∈ Set.range (fun (j : Fin ρ) (i : Fin N) => (M' j i : ℚ)),
      L x ∈ Submodule.span ℚ S := by
    rintro x ⟨j, rfl⟩
    refine Submodule.subset_span ⟨j, ?_⟩
    show (fun i : Fin r => (extM σ M' j i : ℚ)) = L (fun i : Fin N => (M' j i : ℚ))
    rw [hL]
    ext i
    rw [Function.ExtendByZero.linearMap_apply]
    exact congr_fun (extM_cast_rat σ M' j) i
  -- Therefore the image of the span of the rows of `M'` lies in the span of the rows of `extM`.
  have hle : Submodule.span ℚ (Set.range fun (j : Fin ρ) (i : Fin N) => (M' j i : ℚ))
      ≤ Submodule.comap L (Submodule.span ℚ S) := Submodule.span_le.mpr hmap
  -- `L` fixes `B` because `B` vanishes off `range σ`.
  have hLx : L (fun i : Fin N => (B (σ i) : ℚ)) = (fun i : Fin r => (B i : ℚ)) := by
    funext i
    rw [hL, Function.ExtendByZero.linearMap_apply]
    by_cases hi : i ∈ Set.range σ
    · obtain ⟨a, rfl⟩ := hi
      rw [Function.Injective.extend_apply hσ]
    · rw [Function.extend_apply' _ _ _ (by simpa [Set.mem_range] using hi), hBZ i hi]
      simp
  rw [← hLx]
  exact hle hB'

end Work.BW
