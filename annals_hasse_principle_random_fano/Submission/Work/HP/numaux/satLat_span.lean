import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.castL_mem_spread_iff

/-!
# The saturation is the rational span of the lattice

For an integral lattice `Λ ⊆ ℤ^ι`, the saturation `satLat Λ` consists exactly of the integer
vectors whose image in `ℚ^ι` lies in the `ℚ`-span of the rational points of `Λ`:

`x ∈ satLat Λ ↔ castL x ∈ span_ℚ {castL y | y ∈ Λ}`.

Indeed `span_ℚ {castL y | y ∈ Λ}` is the rational spread `spread Λ` of `rk_orthLatDefs`, and
`castL_mem_spread_iff` identifies the integer points of `spread Λ` with `satLat Λ`.
-/

namespace Work.HP.numaux

/-- The `ℚ`-span of the rational points of `Λ` is the rational spread of `Λ`. -/
lemma span_range_castL_eq_spread {ι : Type} [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ (ι → ℤ)) :
    Submodule.span ℚ (Set.range (fun y : Λ => fun i => (((y : ι → ℤ) i : ℤ) : ℚ)))
      = spread Λ := by
  rw [spread_eq_span_image]
  congr 1
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(y : ι → ℤ), y.2, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

theorem satLat_span {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (ι → ℤ)) (x : ι → ℤ) :
    x ∈ satLat Λ ↔ (fun i => (x i : ℚ)) ∈
      Submodule.span ℚ (Set.range (fun y : Λ => fun i => (((y : ι → ℤ) i : ℤ) : ℚ))) := by
  rw [span_range_castL_eq_spread Λ]
  exact (castL_mem_spread_iff Λ x).symm

end Work.HP.numaux
