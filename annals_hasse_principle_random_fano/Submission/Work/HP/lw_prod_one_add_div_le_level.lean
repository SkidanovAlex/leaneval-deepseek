import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP

/-- Level-product estimate.

For a nondecreasing positive weight sequence `w 1, …, w m` and `r > 0`,
```
∏_{i<m} (1 + r / w (i+1))  ≤  2^m · r^S / ∏_{i<S} w (i+1),
```
where `S = #{i < m : w (i+1) ≤ r}`.  Since `w` is nondecreasing, the index set
`{i < m : w (i+1) ≤ r}` is an initial segment of `range m`, namely `range S`,
and each factor with `w (i+1) ≤ r` is bounded by `2·r/w (i+1)` while each factor
with `w (i+1) > r` is bounded by `2`. -/
theorem lw_prod_one_add_div_le_level {w : ℕ → ℝ} {m : ℕ} {r : ℝ}
    (hpos : ∀ i, 1 ≤ i → i ≤ m → 0 < w i)
    (hmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m → w i ≤ w j) (hr : 0 < r) :
    ∏ i ∈ Finset.range m, (1 + r / w (i + 1)) ≤
      2 ^ m * r ^ (((Finset.range m).filter (fun i => w (i + 1) ≤ r)).card) /
        ∏ i ∈ Finset.range (((Finset.range m).filter (fun i => w (i + 1) ≤ r)).card), w (i + 1) := by
  set T := (Finset.range m).filter (fun i => w (i + 1) ≤ r) with hTdef
  set S := T.card with hSdef
  -- membership in `T`, and `T ⊆ range m`
  have hmem : ∀ i, i ∈ T ↔ i < m ∧ w (i + 1) ≤ r := by
    intro i; rw [hTdef, Finset.mem_filter, Finset.mem_range]
  have hTm : T ⊆ Finset.range m := by rw [hTdef]; exact Finset.filter_subset _ _
  have hSm : S ≤ m := by
    rw [hSdef]
    calc T.card ≤ (Finset.range m).card := Finset.card_le_card hTm
      _ = m := Finset.card_range m
  -- `T` is downward closed
  have hdown : ∀ i j, j ∈ T → i ≤ j → i ∈ T := by
    intro i j hj hij
    rw [hmem] at hj ⊢
    obtain ⟨hjm, hjw⟩ := hj
    refine ⟨by omega, ?_⟩
    exact le_trans (hmono (i+1) (j+1) (by omega) (by omega) (by omega)) hjw
  -- `range S ⊆ T`
  have hsub : Finset.range S ⊆ T := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_contra hni
    have him : i < m := lt_of_lt_of_le hi hSm
    have hri : r < w (i + 1) := by
      have : ¬ (w (i+1) ≤ r) := fun h => hni ((hmem i).mpr ⟨him, h⟩)
      exact not_le.mp this
    have hTin : T ⊆ Finset.range i := by
      intro k hk
      rw [Finset.mem_range]
      by_contra hki
      rw [not_lt] at hki
      have hkm : k < m := ((hmem k).mp hk).1
      have hwk : w (i+1) ≤ w (k+1) := hmono (i+1) (k+1) (by omega) (by omega) (by omega)
      have hkr : w (k+1) ≤ r := ((hmem k).mp hk).2
      linarith
    have : S ≤ i := by
      rw [hSdef]
      calc T.card ≤ (Finset.range i).card := Finset.card_le_card hTin
        _ = i := Finset.card_range i
    omega
  -- `T ⊆ range S`
  have hsup : T ⊆ Finset.range S := by
    intro j hj
    rw [Finset.mem_range]
    have : (Finset.range (j+1)).card ≤ T.card := by
      apply Finset.card_le_card
      intro i hi
      rw [Finset.mem_range] at hi
      exact hdown i j hj (by omega)
    rw [Finset.card_range, ← hSdef] at this
    omega
  have hTeq : T = Finset.range S := Finset.Subset.antisymm hsup hsub
  -- pointwise bound against the auxiliary function `g`
  set g : ℕ → ℝ := fun i => if i ∈ T then 2 * (r / w (i + 1)) else 2 with hgdef
  have hfg : ∀ i ∈ Finset.range m, (1 + r / w (i + 1)) ≤ g i := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hT : i ∈ T
    · rw [hgdef]; simp only [hT, ite_true]
      have hw : 0 < w (i+1) := hpos (i+1) (by omega) (by omega)
      have hle : w (i+1) ≤ r := ((hmem i).mp hT).2
      have hx : 1 ≤ r / w (i+1) := (one_le_div hw).mpr hle
      linarith
    · rw [hgdef]; simp only [hT, ite_false]
      have hw : 0 < w (i+1) := hpos (i+1) (by omega) (by omega)
      have hgt : r < w (i+1) := by
        have : ¬ (w (i+1) ≤ r) := fun h => hT ((hmem i).mpr ⟨hi, h⟩)
        exact not_le.mp this
      have hx : r / w (i+1) < 1 := (div_lt_one hw).mpr hgt
      linarith
  have hfnonneg : ∀ i ∈ Finset.range m, 0 ≤ (1 + r / w (i+1)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hw : 0 < w (i+1) := hpos (i+1) (by omega) (by omega)
    have : 0 < r / w (i+1) := div_pos hr hw
    linarith
  have hstep1 : ∏ i ∈ Finset.range m, (1 + r / w (i+1)) ≤ ∏ i ∈ Finset.range m, g i :=
    Finset.prod_le_prod₀ hfnonneg hfg
  -- evaluate the product of `g`
  have hprod : ∏ i ∈ Finset.range m, g i = 2^m * r^S / ∏ i ∈ Finset.range S, w (i+1) := by
    have hg : ∀ i, g i = 2 * (if i ∈ T then r / w (i+1) else 1) := by
      intro i
      rw [hgdef]
      by_cases h : i ∈ T <;> simp [h]
    calc ∏ i ∈ Finset.range m, g i
        = ∏ i ∈ Finset.range m, 2 * (if i ∈ T then r / w (i+1) else 1) := by
            apply Finset.prod_congr rfl; intro i _; exact hg i
      _ = (∏ i ∈ Finset.range m, (2:ℝ))
            * ∏ i ∈ Finset.range m, (if i ∈ T then r / w (i+1) else 1) := by
            rw [Finset.prod_mul_distrib]
      _ = 2^m * ∏ i ∈ Finset.range m ∩ T, r / w (i+1) := by
            rw [Finset.prod_const, Finset.card_range, Finset.prod_ite_mem]
      _ = 2^m * ∏ i ∈ T, r / w (i+1) := by
            rw [Finset.inter_eq_right.mpr hTm]
      _ = 2^m * (r^S / ∏ i ∈ T, w (i+1)) := by
            rw [Finset.prod_div_distrib, Finset.prod_const, ← hSdef]
      _ = 2^m * (r^S / ∏ i ∈ Finset.range S, w (i+1)) := by
            rw [hTeq]
      _ = 2^m * r^S / ∏ i ∈ Finset.range S, w (i+1) := by
            rw [mul_div_assoc]
  calc ∏ i ∈ Finset.range m, (1 + r / w (i+1)) ≤ ∏ i ∈ Finset.range m, g i := hstep1
    _ = 2^m * r^S / ∏ i ∈ Finset.range S, w (i+1) := hprod

end Work.HP
