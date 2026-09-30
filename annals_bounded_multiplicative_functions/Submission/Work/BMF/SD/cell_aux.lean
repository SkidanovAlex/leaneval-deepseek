import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Generic combinatorial lemmas for the scaling-down step

* `card_big_fibers`: pigeonhole over the fibres of a map `α → ℕ`.
* `card_le_of_separated`: a `d`-separated finite set of reals meets any interval of length
  `2r` in at most `2r/d + 1` points.
-/

open Classical

namespace Work.BMF.SD

/-- Pigeonhole over the fibres of a map `g : α → ℕ`. If all the fibres of the restricted domain
`S` have at most `M` elements, the indices used lie in `J`, and `#J ≤ m`, then the number of
fibres with at least `t` elements is at least `(|S| - m t)/M`. -/
theorem card_big_fibers {α : Type*} (S : Finset α) (g : α → ℕ) (J : Finset ℕ) (t M m : ℝ)
    (ht : 0 ≤ t)
    (hJ : ∀ s ∈ S, g s ∈ J)
    (hM : ∀ j ∈ J, ((S.filter (fun s => g s = j)).card : ℝ) ≤ M)
    (hm : (J.card : ℝ) ≤ m) :
    (S.card : ℝ) - m * t ≤
      ((J.filter (fun j => t ≤ ((S.filter (fun s => g s = j)).card : ℝ))).card : ℝ) * M := by
  set B : Finset ℕ := J.filter (fun j => t ≤ ((S.filter (fun s => g s = j)).card : ℝ)) with hB
  have hpartition : S.card = ∑ j ∈ J, (S.filter (fun s => g s = j)).card :=
    Finset.card_eq_sum_card_fiberwise (f := g) (s := S) (t := J) hJ
  have hsum : (S.card : ℝ) = ∑ j ∈ J, ((S.filter (fun s => g s = j)).card : ℝ) := by
    rw [hpartition]
    push_cast
    ring
  have hBJ : B ⊆ J := by rw [hB]; exact Finset.filter_subset _ _
  have hsplit : ∑ j ∈ J, ((S.filter (fun s => g s = j)).card : ℝ)
      = ∑ j ∈ B, ((S.filter (fun s => g s = j)).card : ℝ)
        + ∑ j ∈ J \ B, ((S.filter (fun s => g s = j)).card : ℝ) := by
    have hunion : B ∪ (J \ B) = J := Finset.union_sdiff_of_subset hBJ
    conv_lhs => rw [← hunion]
    rw [Finset.sum_union Finset.disjoint_sdiff]
  have hbig : ∑ j ∈ B, ((S.filter (fun s => g s = j)).card : ℝ) ≤ (B.card : ℝ) * M := by
    calc ∑ j ∈ B, ((S.filter (fun s => g s = j)).card : ℝ)
        ≤ ∑ _j ∈ B, M := Finset.sum_le_sum (fun j hj => hM j ((Finset.mem_filter.mp hj).1))
      _ = (B.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsmall : ∑ j ∈ J \ B, ((S.filter (fun s => g s = j)).card : ℝ) ≤ m * t := by
    have h1 : ∑ j ∈ J \ B, ((S.filter (fun s => g s = j)).card : ℝ) ≤ ∑ _j ∈ (J \ B), t := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjJ : j ∈ J := (Finset.mem_sdiff.mp hj).1
      have hjnB : j ∉ B := (Finset.mem_sdiff.mp hj).2
      have hlt : ¬ (t ≤ ((S.filter (fun s => g s = j)).card : ℝ)) := fun h =>
        hjnB (by rw [hB]; exact Finset.mem_filter.mpr ⟨hjJ, h⟩)
      linarith
    have h2 : ∑ _j ∈ (J \ B), t = ((J \ B).card : ℝ) * t := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : ((J \ B).card : ℝ) ≤ m := by
      have h4 : ((J \ B).card : ℝ) ≤ (J.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : J \ B ⊆ J)
      linarith
    rw [h2] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_right h3 ht)
  calc (S.card : ℝ) - m * t
      = (∑ j ∈ J, ((S.filter (fun s => g s = j)).card : ℝ)) - m * t := by rw [hsum]
    _ = (∑ j ∈ B, ((S.filter (fun s => g s = j)).card : ℝ))
        + (∑ j ∈ J \ B, ((S.filter (fun s => g s = j)).card : ℝ)) - m * t := by rw [hsplit]
    _ ≤ (B.card : ℝ) * M := by linarith

/-- A finite set `S` of pairwise `d`-separated real numbers contained in `[α,β]` has at most
`(β-α)/d + 1` elements. -/
theorem card_le_of_separated' {S : Finset ℝ} {d α β : ℝ} (hd : 0 < d) (hαβ : α ≤ β)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|)
    (hsub : ∀ x ∈ S, α ≤ x ∧ x ≤ β) :
    (S.card : ℝ) ≤ (β - α) / d + 1 := by
  classical
  set φ : ℝ → ℕ := fun x => ⌊(x - α) / d⌋₊ with hφ
  have hpos : ∀ x ∈ S, 0 ≤ (x - α) / d := fun x hx =>
    div_nonneg (by linarith [(hsub x hx).1]) hd.le
  have hmono : ∀ x ∈ S, ∀ y ∈ S, x < y → φ x < φ y := by
    intro x hx y hy hxy
    change ⌊(x - α) / d⌋₊ < ⌊(y - α) / d⌋₊
    have hxy' : d ≤ y - x := by
      have h := hsep x hx y hy (ne_of_lt hxy)
      rwa [abs_sub_comm, abs_of_nonneg (by linarith)] at h
    have h1 : (x - α) / d + 1 ≤ (y - α) / d := by
      have hsub' : (y - α) / d - (x - α) / d = (y - x) / d := by
        rw [← sub_div]; ring_nf
      have h2 : 1 ≤ (y - x) / d := by rw [le_div_iff₀ hd]; linarith
      linarith
    have h3 : ⌊(x - α) / d⌋₊ + 1 ≤ ⌊(y - α) / d⌋₊ := by
      rw [← Nat.floor_add_one (hpos x hx)]
      exact Nat.floor_mono h1
    omega
  have hinj : ∀ x ∈ S, ∀ y ∈ S, φ x = φ y → x = y := by
    intro x hx y hy h
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact absurd h (ne_of_lt (hmono x hx y hy hlt))
    · exact heq
    · exact absurd h.symm (ne_of_lt (hmono y hy x hx hgt))
  have hcard : (S.image φ).card = S.card := Finset.card_image_of_injOn hinj
  have hrange : S.image φ ⊆ Finset.range (⌊(β - α) / d⌋₊ + 1) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Finset.mem_range]
    have h1 : (x - α) / d ≤ (β - α) / d :=
      div_le_div_of_nonneg_right (by linarith [(hsub x hx).2]) hd.le
    have h2 : φ x ≤ ⌊(β - α) / d⌋₊ := by
      rw [hφ]
      exact Nat.floor_mono h1
    exact Nat.lt_succ_of_le h2
  have hbound : ((S.image φ).card : ℝ) ≤ (β - α) / d + 1 := by
    calc ((S.image φ).card : ℝ) ≤ ((Finset.range (⌊(β - α) / d⌋₊ + 1)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hrange
      _ = (⌊(β - α) / d⌋₊ : ℝ) + 1 := by
          rw [Finset.card_range]; push_cast; ring
      _ ≤ (β - α) / d + 1 := by linarith [Nat.floor_le (by positivity : (0:ℝ) ≤ (β - α) / d)]
  rw [hcard] at hbound
  exact hbound

/-- A finite set `S` of pairwise `d`-separated real numbers meets any interval of length `2r` in
at most `2r/d + 1` points. -/
theorem card_le_of_separated {S : Finset ℝ} {d c r : ℝ} (hd : 0 < d) (hr : 0 ≤ r)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|) :
    ((S.filter (fun x => |x - c| ≤ r)).card : ℝ) ≤ 2 * r / d + 1 := by
  classical
  set T : Finset ℝ := S.filter (fun x => |x - c| ≤ r) with hT
  have hsub : ∀ x ∈ T, c - r ≤ x ∧ x ≤ c + r := by
    intro x hx
    rw [hT] at hx
    have h := (Finset.mem_filter.mp hx).2
    rw [abs_le] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hsepT : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → d ≤ |x - y| := by
    intro x hx y hy hne
    rw [hT] at hx hy
    exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne
  have hkey := card_le_of_separated' (S := T) (d := d) (α := c - r) (β := c + r) hd
    (by linarith) hsepT hsub
  have hgoal : (T.card : ℝ) ≤ 2 * r / d + 1 := by
    have : (c + r - (c - r)) / d = 2 * r / d := by ring_nf
    linarith [hkey, this.le, this.ge]
  rw [hT] at hgoal
  exact hgoal

/-- Location of a point inside its cell: with `j = ⌊(z-u)/w⌋₊` and `u ≤ z`, we have
`u + j w ≤ z ≤ u + (j+1) w`. -/
lemma cell_bounds {u w z : ℝ} (hw : 0 < w) (hz : u ≤ z) :
    u + (⌊(z - u) / w⌋₊ : ℝ) * w ≤ z ∧ z ≤ u + ((⌊(z - u) / w⌋₊ : ℝ) + 1) * w := by
  have h0 : 0 ≤ (z - u) / w := div_nonneg (by linarith) hw.le
  have hfl : (⌊(z - u) / w⌋₊ : ℝ) ≤ (z - u) / w := Nat.floor_le h0
  have hlt : (z - u) / w < (⌊(z - u) / w⌋₊ : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((z - u) / w)
    push_cast
    exact h
  rw [le_div_iff₀ hw] at hfl
  rw [div_lt_iff₀ hw] at hlt
  constructor <;> linarith

/-- Two points of the same cell are within `w`. -/
lemma cell_dist {u w z z' : ℝ} (hw : 0 < w) (hz : u ≤ z) (hz' : u ≤ z')
    (hgg : ⌊(z - u) / w⌋₊ = ⌊(z' - u) / w⌋₊) : |z - z'| ≤ w := by
  obtain ⟨h1, h2⟩ := cell_bounds hw hz
  obtain ⟨h1', h2'⟩ := cell_bounds hw hz'
  rw [hgg] at h1 h2
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Two distinct naturals with the same residue mod `168` differ by at least `168`. -/
lemma mod168_dist {j j' r : ℕ} (h1 : j % 168 = r) (h2 : j' % 168 = r) :
    j ≠ j' → 168 ≤ |(j : ℝ) - (j' : ℝ)| := by
  intro hne
  have hmod : j % 168 = j' % 168 := by rw [h1, h2]
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h : j' - j = 168 * (j' / 168 - j / 168) := by omega
    have hpos : 0 < j' / 168 - j / 168 := by
      rcases Nat.eq_zero_or_pos (j' / 168 - j / 168) with h0 | h0
      · rw [h0, mul_zero] at h; omega
      · exact h0
    have hge : 168 ≤ j' - j := by
      rw [h]
      have : 1 ≤ j' / 168 - j / 168 := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
      nlinarith
    have hcast : ((j' - j : ℕ) : ℝ) = (j' : ℝ) - (j : ℝ) := Nat.cast_sub hlt.le
    rw [abs_sub_comm, abs_of_nonneg (by rw [← hcast]; positivity)]
    rw [← hcast]
    exact_mod_cast hge
  · have h : j - j' = 168 * (j / 168 - j' / 168) := by omega
    have hpos : 0 < j / 168 - j' / 168 := by
      rcases Nat.eq_zero_or_pos (j / 168 - j' / 168) with h0 | h0
      · rw [h0, mul_zero] at h; omega
      · exact h0
    have hge : 168 ≤ j - j' := by
      rw [h]
      have : 1 ≤ j / 168 - j' / 168 := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
      nlinarith
    have hcast : ((j - j' : ℕ) : ℝ) = (j : ℝ) - (j' : ℝ) := Nat.cast_sub hlt.le
    rw [abs_of_nonneg (by rw [← hcast]; positivity)]
    rw [← hcast]
    exact_mod_cast hge

/-- Points of cells whose indices are in the same class mod `168` and distinct are at distance at
least `167 w`. -/
lemma cell_sep {u w z z' : ℝ} (hw : 0 < w) (hz : u ≤ z) (hz' : u ≤ z')
    (hmod : ⌊(z - u) / w⌋₊ % 168 = ⌊(z' - u) / w⌋₊ % 168)
    (hne : ⌊(z - u) / w⌋₊ ≠ ⌊(z' - u) / w⌋₊) :
    167 * w ≤ |z - z'| := by
  obtain ⟨h1, h2⟩ := cell_bounds hw hz
  obtain ⟨h1', h2'⟩ := cell_bounds hw hz'
  set j := ⌊(z - u) / w⌋₊ with hj
  set j' := ⌊(z' - u) / w⌋₊ with hj'
  have hne' : j ≠ j' := by rw [hj, hj']; exact hne
  have hkey : 168 ≤ |(j : ℝ) - (j' : ℝ)| := mod168_dist (r := j' % 168) hmod rfl hne'
  rcases le_or_gt (j : ℝ) (j' : ℝ) with h | h
  · have hlt : j < j' := lt_of_le_of_ne (by exact_mod_cast h) hne'
    have hjj : (j : ℝ) + 1 ≤ (j' : ℝ) := by exact_mod_cast hlt
    have h2'' : (j' : ℝ) - (j : ℝ) ≥ 168 := by
      have hk := hkey
      rw [abs_sub_comm] at hk
      rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ (j' : ℝ) - (j : ℝ))] at hk
    have h3 : 167 * w ≤ ((j' : ℝ) - ((j : ℝ) + 1)) * w := by
      have h4 : (167 : ℝ) ≤ (j' : ℝ) - ((j : ℝ) + 1) := by linarith
      nlinarith [hw]
    rw [abs_of_nonpos (by linarith : z - z' ≤ 0)]
    nlinarith [h1', h2, h3]
  · have hlt : j' < j := lt_of_lt_of_le (by exact_mod_cast h) (by simp)
    have hjj : (j' : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
    have h2'' : (j : ℝ) - (j' : ℝ) ≥ 168 := by
      have hk := hkey
      rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ (j : ℝ) - (j' : ℝ))] at hk
    have h3 : 167 * w ≤ ((j : ℝ) - ((j' : ℝ) + 1)) * w := by
      have h4 : (167 : ℝ) ≤ (j : ℝ) - ((j' : ℝ) + 1) := by linarith
      nlinarith [hw]
    rw [abs_of_nonneg (by linarith : 0 ≤ z - z')]
    nlinarith [h1, h2', h3]

end Work.BMF.SD