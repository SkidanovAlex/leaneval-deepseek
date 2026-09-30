import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the section-map construction (`Work.BW.Minkowski2.section_maps`)

For `i : Fin d`, the linear map `Work.BW.Minkowski2.suf i : (Fin d → ℝ) → (Fin d → ℝ)` keeps the
coordinates `m ≥ i` and kills the coordinates `m < i`.  A point `x` is a "section" of a set `K`
above `s` when `suf i x = s`.
-/

namespace Work.BW.Minkowski2

variable {d : ℕ}

/-- The coordinate projection keeping the coordinates `m ≥ i` (and zeroing the others). -/
def suf (i : Fin d) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun x := fun m => if i ≤ m then x m else 0
  map_add' x y := by
    ext m
    by_cases h : i ≤ m <;> simp [h]
  map_smul' c x := by
    ext m
    by_cases h : i ≤ m <;> simp [h]

@[simp] theorem suf_apply_of_le {i m : Fin d} (x : Fin d → ℝ) (h : i ≤ m) : suf i x m = x m := by
  simp [suf, h]

@[simp] theorem suf_apply_of_not_le {i m : Fin d} (x : Fin d → ℝ) (h : ¬ i ≤ m) :
    suf i x m = 0 := by
  simp [suf, h]

theorem suf_idem (i : Fin d) (x : Fin d → ℝ) : suf i (suf i x) = suf i x := by
  ext m
  by_cases h : i ≤ m <;> simp [h]

theorem mem_range_suf {i : Fin d} {s : Fin d → ℝ} (h : s ∈ Set.range (suf i)) : suf i s = s := by
  obtain ⟨x, rfl⟩ := h
  exact suf_idem i x

theorem suf_continuous (i : Fin d) : Continuous (suf i) :=
  LinearMap.continuous_of_finiteDimensional _

theorem suf_measurable (i : Fin d) : Measurable (suf i) := (suf_continuous i).measurable

theorem suf_eq_zero_iff {i : Fin d} {v : Fin d → ℝ} : suf i v = 0 ↔ ∀ m, i ≤ m → v m = 0 := by
  constructor
  · intro h m hm
    have := congrFun h m
    simpa [hm] using this
  · intro h
    ext m
    by_cases hm : i ≤ m
    · simpa [hm] using h m hm
    · simp [hm]

theorem suf_eq_iff {i : Fin d} {x y : Fin d → ℝ} : suf i x = suf i y ↔ ∀ m, i ≤ m → x m = y m := by
  constructor
  · intro h m hm
    have := congrFun h m
    simpa [hm] using this
  · intro h
    ext m
    by_cases hm : i ≤ m
    · simpa [hm] using h m hm
    · simp [hm]

end Work.BW.Minkowski2
