import Mathlib

namespace Work.Repel.R3Level0v2

/-- Arithmetic of the level-0 target disc at radius `R ≥ r/4 + 200/(g η)`, with the
`δ`-cap `δ ≤ g r / 256` of `R3Pre`.

Scaling `r/4 + 200/(g η) ≤ R` by `g > 0` gives `g r/4 + 200/η ≤ g R`, i.e. (since
`200/η = 50·(4/η)`) the two linear inputs

* `g r / 4 + 50·(4/η) ≤ g R`  (the disc of radius `R` swallows the level-0 disc),
* `g r > 0`, `4/η > 0`;

against the cap `δ ≤ g r / 256` all four conclusions are then plain linear arithmetic in
the monomials `g r`, `g R`, `δ`, `4/η`. -/
theorem level0_arith {g r η R δ : ℝ} (hg : 0 < g) (hr : 0 < r) (hη : 0 < η)
    (hδcap : δ ≤ g * r / 256)
    (hRbig : r / 4 + 200 / (g * η) ≤ R) :
    0 < (1 / 50 : ℝ) * g * R - δ ∧
      4 / η ≤ (1 / 50 : ℝ) * g * R - δ ∧
      δ ≤ R * g / 8 ∧
      128 * δ < (2 * R) * g := by
  have hgr : 0 < g * r := mul_pos hg hr
  have h4term : (0 : ℝ) < 4 / η := div_pos (by norm_num) hη
  -- the elementary cancellation `g · (200/(g η)) = 200/η`
  have hkey2 : g * (200 / (g * η)) = 200 / η := by
    field_simp
  have hmul : g * (r / 4 + 200 / (g * η)) ≤ g * R :=
    mul_le_mul_of_nonneg_left hRbig (le_of_lt hg)
  have hmid : g * (r / 4) + 200 / η ≤ g * R := by
    have h := hmul
    rw [mul_add] at h
    rwa [hkey2] at h
  -- put the scaled hypothesis in the shape used by the linear arithmetic
  have hbound : g * r / 4 + 50 * (4 / η) ≤ g * R := by
    have h := hmid
    have hratio : (200 : ℝ) / η = 50 * (4 / η) := by ring
    rw [hratio] at h
    have he : g * (r / 4) = g * r / 4 := by ring
    rwa [he] at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end Work.Repel.R3Level0v2
