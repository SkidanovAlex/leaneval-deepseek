import Mathlib
import Submission.Work.HP.Sig2.GamTwoDefs

namespace Work.HP.Sig2

/-- The real span of the lattice `Λ ⊆ ℤ^ι` is the real span of the realifications of the vectors of
any `ℤ`-basis `b` of `Λ`. -/
theorem span_intCast_eq_span_range {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ) :
    Submodule.span ℝ (intCastPi '' (Λ : Set (ι → ℤ)))
      = Submodule.span ℝ (Set.range fun i : κ => intCastPi (((b i : Λ) : ι → ℤ))) := by
  classical
  -- `Λ` is the `ℤ`-span of the underlying vectors of the basis.
  have hK : Λ = Submodule.span ℤ (Set.range fun j : κ => ((b j : Λ) : ι → ℤ)) := by
    conv_lhs => rw [← Submodule.range_subtype Λ, ← Submodule.map_top]
    rw [← b.span_eq, Submodule.map_span, ← Set.range_comp]
    rfl
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro y ⟨k, hk, rfl⟩
    let S : Submodule ℝ (ι → ℝ) :=
      Submodule.span ℝ (Set.range fun j : κ => intCastPi (((b j : Λ) : ι → ℤ)))
    let T : Submodule ℤ (ι → ℤ) :=
      { carrier := {x | intCastPi x ∈ S}
        zero_mem' := by show intCastPi (0 : ι → ℤ) ∈ S; simp
        add_mem' := by
          intro x y hx hy
          show intCastPi (x + y) ∈ S
          rw [map_add]; exact add_mem hx hy
        smul_mem' := by
          intro c x hx
          show intCastPi (c • x) ∈ S
          rw [map_smul, ← Int.cast_smul_eq_zsmul ℝ c (intCastPi x)]
          exact Submodule.smul_mem _ _ hx }
    have hle : Λ ≤ T := by
      rw [hK]
      refine Submodule.span_le.mpr ?_
      rintro y ⟨j, rfl⟩
      show intCastPi ((b j : Λ) : ι → ℤ) ∈ S
      exact Submodule.subset_span (Set.mem_range_self j)
    have h2 := hle hk
    change intCastPi k ∈ S at h2
    exact h2
  · rw [Submodule.span_le]
    rintro y ⟨j, rfl⟩
    exact Submodule.subset_span ⟨(b j : Λ), (b j).2, rfl⟩

end Work.HP.Sig2
