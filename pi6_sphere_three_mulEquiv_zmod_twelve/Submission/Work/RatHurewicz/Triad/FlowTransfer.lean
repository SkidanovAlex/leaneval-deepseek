import Mathlib
import Submission.Work.RatHurewicz.Triad.GridDefs
import Submission.Work.RatHurewicz.Triad.SpreadDefs

/-!
# The flow stays in the cells, and the half-conditions transfer

`Triad/NOTES_triadCompression.md`, session 12.  Three lemmas used to maintain the invariants of the
grid induction:

* `clamp_eq_hi_of_lt`, `clamp_eq_lo_of_gt` — the two "extremal" cases of the coordinate clamp;
* `Triad.segMap_clamp_mem_cellSet` (LEMMA G) — the segment from a point of the collar of `c` to its
  clamp onto `c` stays in every cell containing the point;
* `Triad.smallIn_segMap_clamp` / `Triad.largeIn_segMap_clamp` — the cell-local half-conditions
  transfer backwards along that segment.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

open Work.ThomBordism.TwoSet

noncomputable section

/-- If the clamped coordinate is strictly smaller than the original one, it is the upper endpoint. -/
theorem clamp_eq_hi_of_lt {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N) {x : IC j} {i : Fin j}
    (h : ((clampCell c hN x i : unitInterval) : ℝ) < (x i : ℝ)) :
    ((clampCell c hN x i : unitInterval) : ℝ) = (c.hi i : ℝ) / N := by
  rw [clampCell_val, clampR] at h ⊢
  have hl : ((c.lo i : ℝ)) / N ≤ ((c.hi i : ℝ)) / N := by
    rw [div_le_div_iff_of_pos_right (by exact_mod_cast hN)]
    exact_mod_cast c.hle i
  set l := ((c.lo i : ℝ)) / N with hldef
  set u := ((c.hi i : ℝ)) / N with hudef
  set t := (x i : ℝ) with htdef
  have h1 : min u t < t := lt_of_le_of_lt (le_max_right l (min u t)) h
  have h2 : u < t := by
    rcases min_choice u t with hh | hh
    · rw [hh] at h1; exact h1
    · rw [hh] at h1; exact absurd h1 (lt_irrefl t)
  rw [min_eq_left (le_of_lt h2), max_eq_right hl]

/-- If the clamped coordinate is strictly larger than the original one, it is the lower
endpoint. -/
theorem clamp_eq_lo_of_gt {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N) {x : IC j} {i : Fin j}
    (h : (x i : ℝ) < ((clampCell c hN x i : unitInterval) : ℝ)) :
    ((clampCell c hN x i : unitInterval) : ℝ) = (c.lo i : ℝ) / N := by
  rw [clampCell_val, clampR] at h ⊢
  set l := ((c.lo i : ℝ)) / N with hldef
  set u := ((c.hi i : ℝ)) / N with hudef
  set t := (x i : ℝ) with htdef
  have h1 : t < max l (min u t) := h
  have h2 : l > t := by
    rcases max_choice l (min u t) with hh | hh
    · rw [hh] at h1; exact h1
    · rw [hh] at h1
      exact absurd h1 (not_lt_of_ge (min_le_right u t))
  have h3 : min u t ≤ l := le_trans (min_le_right u t) (le_of_lt h2)
  rw [max_eq_left h3]

/-- **LEMMA G.**  The segment from a point `x` of the `ε`-collar of the cell `c` to the clamp of
`x` onto `c` stays inside every cell containing `x`. -/
theorem segMap_clamp_mem_cellSet {j N : ℕ} (hN : 1 ≤ N) {c c' : CellIdx j N} {ε : ℝ}
    (hεN : (N : ℝ) * ε ≤ 1 / 2) {x : IC j}
    (hx : ∀ i, (c.lo i : ℝ) / N - ε ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (c.hi i : ℝ) / N + ε)
    (hx' : x ∈ cellSet c') (τ : unitInterval) :
    segMap x (clampCell c hN x) τ ∈ cellSet c' := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hε1 : (N : ℝ) * ε < 1 := by linarith
  have hy : clampCell c hN x ∈ cellSet c' := by
    intro i
    have hxi := hx' i
    have hlo : ((c'.lo i : ℕ) : ℝ) ≤ (N : ℝ) * (x i : ℝ) := by
      have := hxi.1
      rw [div_le_iff₀ hNpos] at this
      linarith [this]
    have hhi : (N : ℝ) * (x i : ℝ) ≤ ((c'.hi i : ℕ) : ℝ) := by
      have := hxi.2
      rw [le_div_iff₀ hNpos] at this
      linarith [this]
    rcases lt_trichotomy ((clampCell c hN x i : unitInterval) : ℝ) (x i : ℝ) with hlt | heq | hgt
    · have hyi := clamp_eq_hi_of_lt hN c hlt
      rw [hyi]
      have hxe : (c.hi i : ℝ) / N < (x i : ℝ) := hyi ▸ hlt
      have hxe' : (c.hi i : ℝ) < (N : ℝ) * (x i : ℝ) := by
        rw [div_lt_iff₀ hNpos] at hxe
        linarith
      have hNxlt : (N : ℝ) * (x i : ℝ) < (c.hi i : ℝ) + 1 := by
        have h2 : (N : ℝ) * (x i : ℝ) ≤ (N : ℝ) * ((c.hi i : ℝ) / N + ε) :=
          mul_le_mul_of_nonneg_left (hx i).2 (le_of_lt hNpos)
        have h3 : (N : ℝ) * ((c.hi i : ℝ) / N + ε) = (c.hi i : ℝ) + (N : ℝ) * ε := by
          field_simp
        linarith [hε1]
      refine ⟨?_, ?_⟩
      · have hreal : ((c'.lo i : ℕ) : ℝ) < (((c.hi i) + 1 : ℕ) : ℝ) := by
          push_cast
          linarith
        have hnat : c'.lo i ≤ c.hi i := by
          have h2 : c'.lo i < c.hi i + 1 := by exact_mod_cast hreal
          omega
        exact div_le_div_of_nonneg_right (by exact_mod_cast hnat) (le_of_lt hNpos)
      · have hreal : ((c.hi i : ℕ) : ℝ) ≤ ((c'.hi i : ℕ) : ℝ) := by linarith
        exact div_le_div_of_nonneg_right (by exact_mod_cast hreal) (le_of_lt hNpos)
    · rw [heq]; exact hxi
    · have hyi := clamp_eq_lo_of_gt hN c hgt
      rw [hyi]
      have hxe : (x i : ℝ) < (c.lo i : ℝ) / N := hyi ▸ hgt
      have hxe' : (N : ℝ) * (x i : ℝ) < (c.lo i : ℝ) := by
        rw [lt_div_iff₀ hNpos] at hxe
        linarith
      have hNxgt : (c.lo i : ℝ) - 1 < (N : ℝ) * (x i : ℝ) := by
        have h2 : (N : ℝ) * ((c.lo i : ℝ) / N - ε) ≤ (N : ℝ) * (x i : ℝ) :=
          mul_le_mul_of_nonneg_left (hx i).1 (le_of_lt hNpos)
        have h3 : (N : ℝ) * ((c.lo i : ℝ) / N - ε) = (c.lo i : ℝ) - (N : ℝ) * ε := by
          field_simp
        linarith [hε1]
      refine ⟨?_, ?_⟩
      · have hreal : ((c'.lo i : ℕ) : ℝ) < ((c.lo i : ℕ) : ℝ) := by linarith
        have hnat : c'.lo i ≤ c.lo i := by
          have h2 : c'.lo i < c.lo i := by exact_mod_cast hreal
          omega
        exact div_le_div_of_nonneg_right (by exact_mod_cast hnat) (le_of_lt hNpos)
      · have hreal : ((c.lo i : ℕ) : ℝ) ≤ ((c'.hi i : ℕ) : ℝ) := by
          rcases Nat.eq_zero_or_pos (c.lo i) with h0 | hpos
          · rw [h0]; push_cast; positivity
          · have hcast : ((c.lo i - 1 : ℕ) : ℝ) = (c.lo i : ℝ) - 1 := by
              rw [Nat.cast_sub hpos]; norm_num
            have h2 : ((c.lo i - 1 : ℕ) : ℝ) < ((c'.hi i : ℕ) : ℝ) := by
              rw [hcast]; linarith
            have hnat : c.lo i - 1 < c'.hi i := by exact_mod_cast h2
            have : c.lo i ≤ c'.hi i := by omega
            exact_mod_cast this
        exact div_le_div_of_nonneg_right (by exact_mod_cast hreal) (le_of_lt hNpos)
  exact segMap_mem_cellSet hx' hy τ

/-- **The `SmallIn` condition transfers backwards along the flow segment.** -/
theorem smallIn_segMap_clamp {j N : ℕ} (hN : 1 ≤ N) {c c' : CellIdx j N} {ε : ℝ}
    (hεN : (N : ℝ) * ε < 1 / 2) {x : IC j}
    (hx : ∀ i, (c.lo i : ℝ) / N - ε ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (c.hi i : ℝ) / N + ε)
    (τ : unitInterval) (i : Fin j)
    (h : SmallIn N c' (segMap x (clampCell c hN x) τ) i) : SmallIn N c' x i := by
  obtain ⟨hle, hhalf⟩ := h
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set y : IC j := clampCell c hN x with hydef
  have htcoord : ((segMap x y τ : IC j) i : ℝ) =
      (1 - (τ : ℝ)) * (x i : ℝ) + (τ : ℝ) * (y i : ℝ) := by
    simp [segMap]
  refine ⟨hle, ?_⟩
  rcases lt_trichotomy (x i : ℝ) (y i : ℝ) with hlt | heq | hgt
  · have h1 : (x i : ℝ) ≤ ((segMap x y τ : IC j) i : ℝ) := by
      rw [htcoord]
      nlinarith [τ.2.1, τ.2.2, le_of_lt hlt]
    have := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    linarith
  · have h1 : ((segMap x y τ : IC j) i : ℝ) = (x i : ℝ) := by
      rw [htcoord, heq]; ring
    rwa [h1] at hhalf
  · have hyi : (y i : ℝ) = (c.hi i : ℝ) / N := clamp_eq_hi_of_lt hN c hgt
    have h1 : (y i : ℝ) ≤ ((segMap x y τ : IC j) i : ℝ) := by
      rw [htcoord]
      nlinarith [τ.2.1, τ.2.2, le_of_lt hgt]
    have h2 : (c.hi i : ℝ) ≤ (N : ℝ) * ((segMap x y τ : IC j) i : ℝ) := by
      have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
      rw [hyi] at h3
      have h4 : (N : ℝ) * ((c.hi i : ℝ) / N) = (c.hi i : ℝ) := by field_simp
      linarith
    have hnat : c.hi i ≤ c'.lo i := by
      by_contra hcon
      push_neg at hcon
      have h5 : ((c'.lo i : ℕ) : ℝ) + 1 ≤ (c.hi i : ℝ) := by exact_mod_cast hcon
      linarith
    have hcast : ((c.hi i : ℕ) : ℝ) ≤ ((c'.lo i : ℕ) : ℝ) := by exact_mod_cast hnat
    have h4 : (N : ℝ) * (x i : ℝ) ≤ (c.hi i : ℝ) + (N : ℝ) * ε := by
      have h5 : (N : ℝ) * (x i : ℝ) ≤ (N : ℝ) * ((c.hi i : ℝ) / N + ε) :=
        mul_le_mul_of_nonneg_left (hx i).2 (le_of_lt hNpos)
      have h6 : (N : ℝ) * ((c.hi i : ℝ) / N + ε) = (c.hi i : ℝ) + (N : ℝ) * ε := by
        field_simp
      linarith
    linarith

/-- **The `LargeIn` condition transfers backwards along the flow segment.** -/
theorem largeIn_segMap_clamp {j N : ℕ} (hN : 1 ≤ N) {c c' : CellIdx j N} {ε : ℝ}
    (hεN : (N : ℝ) * ε < 1 / 2) {x : IC j}
    (hx : ∀ i, (c.lo i : ℝ) / N - ε ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (c.hi i : ℝ) / N + ε)
    (τ : unitInterval) (i : Fin j)
    (h : LargeIn N c' (segMap x (clampCell c hN x) τ) i) : LargeIn N c' x i := by
  obtain ⟨hle, hhalf⟩ := h
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set y : IC j := clampCell c hN x with hydef
  have htcoord : ((segMap x y τ : IC j) i : ℝ) =
      (1 - (τ : ℝ)) * (x i : ℝ) + (τ : ℝ) * (y i : ℝ) := by
    simp [segMap]
  refine ⟨hle, ?_⟩
  rcases lt_trichotomy (x i : ℝ) (y i : ℝ) with hlt | heq | hgt
  · have hyi : (y i : ℝ) = (c.lo i : ℝ) / N := clamp_eq_lo_of_gt hN c hlt
    have h1 : ((segMap x y τ : IC j) i : ℝ) ≤ (y i : ℝ) := by
      rw [htcoord]
      nlinarith [τ.2.1, τ.2.2, le_of_lt hlt]
    have h2 : (N : ℝ) * ((segMap x y τ : IC j) i : ℝ) ≤ (c.lo i : ℝ) := by
      have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
      rw [hyi] at h3
      have h4 : (N : ℝ) * ((c.lo i : ℝ) / N) = (c.lo i : ℝ) := by field_simp
      linarith
    have hnat : c'.lo i + 1 ≤ c.lo i := by
      by_contra hcon
      push_neg at hcon
      have h5 : c.lo i ≤ c'.lo i := by omega
      have h6 : ((c.lo i : ℕ) : ℝ) ≤ ((c'.lo i : ℕ) : ℝ) := by exact_mod_cast h5
      linarith
    have hcast : ((c'.lo i : ℕ) : ℝ) + 1 ≤ (c.lo i : ℝ) := by
      have h5 : ((c'.lo i + 1 : ℕ) : ℝ) ≤ ((c.lo i : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at h5
      linarith
    have h4 : (c.lo i : ℝ) - (N : ℝ) * ε ≤ (N : ℝ) * (x i : ℝ) := by
      have h5 := mul_le_mul_of_nonneg_left (hx i).1 (le_of_lt hNpos)
      have h6 : (N : ℝ) * ((c.lo i : ℝ) / N - ε) = (c.lo i : ℝ) - (N : ℝ) * ε := by
        field_simp
      linarith
    linarith
  · have h1 : ((segMap x y τ : IC j) i : ℝ) = (x i : ℝ) := by
      rw [htcoord, heq]; ring
    rwa [h1] at hhalf
  · have h1 : ((segMap x y τ : IC j) i : ℝ) ≤ (x i : ℝ) := by
      rw [htcoord]
      nlinarith [τ.2.1, τ.2.2, le_of_lt hgt]
    have := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    linarith

end

end Work.RatHurewicz.Triad
