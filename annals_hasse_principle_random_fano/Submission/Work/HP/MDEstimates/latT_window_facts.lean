import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.kwin_spec
import Submission.Work.HP.ceil_logb_bounds
import Submission.Work.HP.lam_basic

/-!
# Dyadic window facts for a rank-`3` lattice `L ⊆ ℤ^5`

Given Minkowski's bound in the form
`∏_{j<rk L} λ_{j+1}(L) ≤ Kmk · detL L` for every lattice `L`, and a rank-`3` lattice `L` whose
covolume satisfies `detL L ≤ Δ + 1`, the three successive minima `λ₁ ≤ λ₂ ≤ λ₃` of `L` (with
`1 ≤ λ₁`) satisfy:

* the dyadic exponents are ordered: `⌈log₂ λ₁⌉ ≤ ⌈log₂ λ₂⌉`;
* `2 ^ (⌈log₂ λ₁⌉ + 2 ⌈log₂ λ₂⌉) ≤ 8 Kmk (Δ+1)`, from `λ₁ λ₂² ≤ λ₁ λ₂ λ₃ ≤ Kmk (Δ+1)`
  together with the tight ceiling bound `2 ^ ⌈log₂ x⌉ ≤ 2 x` (`Work.HP.ceil_logb_bounds`);
* `λ₃ ≤ 4 Kmk (Δ+1) / (2 ^ ⌈log₂ λ₁⌉ · 2 ^ ⌈log₂ λ₂⌉)`, from
  `λ₃ ≤ Kmk (Δ+1)/(λ₁λ₂)` and `2 ^ ⌈log₂ λ₁⌉ · 2 ^ ⌈log₂ λ₂⌉ ≤ 4 λ₁ λ₂`.
-/

namespace Work.HP.MDEstimates

theorem latT_window_facts (Kmk : ℝ) (hKmk : 1 ≤ Kmk)
    (hmink : ∀ L : Submodule ℤ (Fin 5 → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmk * detL L)
    (L : Submodule ℤ (Fin 5 → ℤ)) (hrk : rk L = 3) (Δ : ℝ) (hΔ : 1 ≤ Δ)
    (hdet : detL L ≤ Δ + 1) :
    ⌈Real.logb 2 (lam L 1)⌉₊ ≤ ⌈Real.logb 2 (lam L 2)⌉₊ ∧
    (2:ℝ) ^ (⌈Real.logb 2 (lam L 1)⌉₊ + 2 * ⌈Real.logb 2 (lam L 2)⌉₊) ≤ 8 * Kmk * (Δ + 1) ∧
    lam L 3 ≤ 4 * Kmk * (Δ + 1) / ((2:ℝ) ^ ⌈Real.logb 2 (lam L 1)⌉₊ * (2:ℝ) ^ ⌈Real.logb 2 (lam L 2)⌉₊) := by
  have hrk1 : 1 ≤ rk L := by omega
  have hrk2 : 2 ≤ rk L := by omega
  have hpos1 : 1 ≤ lam L 1 := Work.HP.one_le_lam L le_rfl hrk1
  have hpos2 : 1 ≤ lam L 2 := Work.HP.one_le_lam L (by norm_num) hrk2
  have h12 : lam L 1 ≤ lam L 2 := Work.HP.lam_mono L (by norm_num) hrk2
  have h23 : lam L 2 ≤ lam L 3 := Work.HP.lam_mono L (by norm_num) (by omega)
  have hb1 := Work.HP.ceil_logb_bounds hpos1
  have hb2 := Work.HP.ceil_logb_bounds hpos2
  -- Minkowski's bound for `L`, expanded over `range 3 = {0,1,2}`.
  have hprod3 : (∏ j ∈ Finset.range (rk L), lam L (j + 1)) = lam L 1 * lam L 2 * lam L 3 := by
    rw [hrk, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    norm_num
  have hprod : lam L 1 * lam L 2 * lam L 3 ≤ Kmk * detL L := by
    rw [← hprod3]; exact hmink L
  have hKmk0 : 0 ≤ Kmk := le_trans (by norm_num) hKmk
  have hMK : lam L 1 * lam L 2 * lam L 3 ≤ Kmk * (Δ + 1) := by
    calc lam L 1 * lam L 2 * lam L 3 ≤ Kmk * detL L := hprod
      _ ≤ Kmk * (Δ + 1) := mul_le_mul_of_nonneg_left hdet hKmk0
  have hMK2 : lam L 1 * lam L 2 ^ 2 ≤ Kmk * (Δ + 1) := by
    have hnn : 0 ≤ lam L 1 * lam L 2 := by positivity
    calc lam L 1 * lam L 2 ^ 2 = lam L 1 * lam L 2 * lam L 2 := by ring
      _ ≤ lam L 1 * lam L 2 * lam L 3 := mul_le_mul_of_nonneg_left h23 hnn
      _ ≤ Kmk * (Δ + 1) := hMK
  refine ⟨?_, ?_, ?_⟩
  · -- the dyadic exponents are ordered
    apply Nat.ceil_mono
    exact (Real.logb_le_logb (by norm_num) (lt_of_lt_of_le one_pos hpos1)
      (lt_of_lt_of_le one_pos hpos2)).mpr h12
  · -- `2 ^ (n₁ + 2 n₂) ≤ 8 Kmk (Δ+1)`
    set n1 := ⌈Real.logb 2 (lam L 1)⌉₊ with hn1
    set n2 := ⌈Real.logb 2 (lam L 2)⌉₊ with hn2
    have hp1 : (2:ℝ) ^ n1 ≤ 2 * lam L 1 := hb1.2
    have hp2 : (2:ℝ) ^ n2 ≤ 2 * lam L 2 := hb2.2
    have hp2sq : ((2:ℝ) ^ n2) ^ 2 ≤ (2 * lam L 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hp2 2
    have hsplit : (2:ℝ) ^ (n1 + 2 * n2) = (2:ℝ) ^ n1 * ((2:ℝ) ^ n2) ^ 2 := by
      rw [pow_add, Nat.mul_comm 2 n2, pow_mul]
    rw [hsplit]
    calc (2:ℝ) ^ n1 * ((2:ℝ) ^ n2) ^ 2 ≤ (2 * lam L 1) * (2 * lam L 2) ^ 2 :=
          mul_le_mul hp1 hp2sq (by positivity) (by positivity)
      _ = 8 * (lam L 1 * lam L 2 ^ 2) := by ring
      _ ≤ 8 * (Kmk * (Δ + 1)) := by
            apply mul_le_mul_of_nonneg_left hMK2 (by norm_num)
      _ = 8 * Kmk * (Δ + 1) := by ring
  · -- `λ₃ ≤ 4 Kmk (Δ+1) / (2 ^ n₁ · 2 ^ n₂)`
    set n1 := ⌈Real.logb 2 (lam L 1)⌉₊ with hn1
    set n2 := ⌈Real.logb 2 (lam L 2)⌉₊ with hn2
    have hp1 : (2:ℝ) ^ n1 ≤ 2 * lam L 1 := hb1.2
    have hp2 : (2:ℝ) ^ n2 ≤ 2 * lam L 2 := hb2.2
    have hppos : 0 < lam L 1 * lam L 2 := by positivity
    have h3le : lam L 3 ≤ Kmk * (Δ + 1) / (lam L 1 * lam L 2) := by
      rw [le_div_iff₀ hppos]
      calc lam L 3 * (lam L 1 * lam L 2) = lam L 1 * lam L 2 * lam L 3 := by ring
        _ ≤ Kmk * (Δ + 1) := hMK
    have hden : (2:ℝ) ^ n1 * (2:ℝ) ^ n2 ≤ 4 * (lam L 1 * lam L 2) := by
      calc (2:ℝ) ^ n1 * (2:ℝ) ^ n2 ≤ (2 * lam L 1) * (2 * lam L 2) :=
            mul_le_mul hp1 hp2 (by positivity) (by positivity)
        _ = 4 * (lam L 1 * lam L 2) := by ring
    have hdenpos : 0 < (2:ℝ) ^ n1 * (2:ℝ) ^ n2 := by positivity
    have hinv : 1 / (lam L 1 * lam L 2) ≤ 4 / ((2:ℝ) ^ n1 * (2:ℝ) ^ n2) := by
      rw [div_le_div_iff₀ hppos hdenpos]
      simpa using hden
    calc lam L 3 ≤ Kmk * (Δ + 1) / (lam L 1 * lam L 2) := h3le
      _ = Kmk * (Δ + 1) * (1 / (lam L 1 * lam L 2)) := by rw [div_eq_mul_one_div]
      _ ≤ Kmk * (Δ + 1) * (4 / ((2:ℝ) ^ n1 * (2:ℝ) ^ n2)) := by
            apply mul_le_mul_of_nonneg_left hinv; positivity
      _ = 4 * Kmk * (Δ + 1) / ((2:ℝ) ^ n1 * (2:ℝ) ^ n2) := by ring

end Work.HP.MDEstimates
