import Mathlib

namespace Commons.Measure.AddCircle

open MeasureTheory Set
open scoped ENNReal Pointwise

/-- The quotient map `ℝ → ℝ/ℤ` as an additive monoid homomorphism. -/
private noncomputable def circleCoeHom : ℝ →+ UnitAddCircle :=
  AddMonoidHom.mk' (fun x : ℝ => (x : UnitAddCircle)) (fun a b => AddCircle.coe_add 1 a b)

/-- The image of a sum of sets under the quotient map is the sum of the images. -/
private lemma image_add_coe (s t : Set ℝ) :
    (fun x : ℝ => (x : UnitAddCircle)) '' s + (fun x : ℝ => (x : UnitAddCircle)) '' t
      = (fun x : ℝ => (x : UnitAddCircle)) '' (s + t) :=
  (image_add circleCoeHom).symm

/-- Translating a half-open interval by a real constant. -/
private lemma Ico_translate (a b c : ℝ) :
    (fun x : ℝ => x + c) '' Set.Ico a b = Set.Ico (a + c) (b + c) := by
  ext x
  simp only [Set.mem_image, Set.mem_Ico]
  constructor
  · rintro ⟨y, ⟨hya, hyb⟩, rfl⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x - c, ⟨by linarith, by linarith⟩, by ring⟩

/-- The Minkowski sum of two nonempty half-open intervals is the half-open interval with the
summed endpoints. -/
private lemma Ico_add_Ico (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    Set.Ico a b + Set.Ico c d = Set.Ico (a + c) (b + d) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
    exact ⟨add_le_add hya hzc, add_lt_add_of_le_of_lt hyb.le hzd⟩
  · intro x hx
    rw [Set.mem_Ico] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Set.mem_add]
    by_cases h : x - c < b
    · exact ⟨x - c, ⟨by linarith, h⟩, c, ⟨le_refl c, hcd⟩, by ring⟩
    · have hbc : b ≤ x - c := not_lt.mp h
      have hMb : max a (x - d) < b := max_lt hab (by linarith)
      have hy1 : max a (x - d) < (max a (x - d) + b) / 2 := by linarith
      have hy2 : (max a (x - d) + b) / 2 < b := by linarith
      have hy3 : x - d < (max a (x - d) + b) / 2 := by
        have := le_max_right a (x - d); linarith
      refine ⟨(max a (x - d) + b) / 2, ⟨?_, hy2⟩,
              x - (max a (x - d) + b) / 2, ⟨?_, ?_⟩, by ring⟩
      · exact le_of_lt (lt_of_le_of_lt (le_max_left _ _) hy1)
      · linarith
      · linarith

/-- Adding a natural number does not change a point of `ℝ/ℤ`. -/
private lemma coe_add_natCast (x : ℝ) (c : ℕ) :
    ((x + (c : ℝ) : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  have hc : ((c : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨(c : ℤ), by simp⟩
  rw [AddCircle.coe_add, hc, add_zero]

/-- The image under `ℝ → ℝ/ℤ` of the half-open interval `[t/n, (t+1)/n)` depends only on the
residue class of the natural number `t` modulo `n`. -/
private lemma image_Ico_div_eq_cell (n : ℕ) [NeZero n] (t : ℕ) :
    (fun x : ℝ => (x : UnitAddCircle)) '' Set.Ico ((t : ℝ) / n) (((t : ℝ) + 1) / n)
      = (fun x : ℝ => (x : UnitAddCircle)) ''
          Set.Ico ((((t : ZMod n)).val : ℝ) / n) (((((t : ZMod n)).val : ℝ) + 1) / n) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hdiv : t / n * n + (t : ZMod n).val = t := by
    rw [ZMod.val_natCast, mul_comm (t / n) n]
    exact Nat.div_add_mod t n
  have hdivR : (t : ℝ) = ((t / n : ℕ) : ℝ) * n + (((t : ZMod n).val : ℕ) : ℝ) := by
    conv_lhs => rw [← hdiv]
    push_cast
    ring
  have h1 : (t : ℝ) / n = (((t : ZMod n).val : ℝ)) / n + ((t / n : ℕ) : ℝ) := by
    rw [hdivR]; field_simp; ring
  have h2 : ((t : ℝ) + 1) / n = ((((t : ZMod n).val : ℝ)) + 1) / n + ((t / n : ℕ) : ℝ) := by
    rw [hdivR]; field_simp; ring
  have hIco : Set.Ico ((t : ℝ) / n) (((t : ℝ) + 1) / n)
      = (fun x : ℝ => x + ((t / n : ℕ) : ℝ)) ''
          Set.Ico (((t : ZMod n).val : ℝ) / n) ((((t : ZMod n).val : ℝ) + 1) / n) := by
    rw [h1, h2, ← Ico_translate]
  rw [hIco, ← Set.image_comp]
  apply Set.image_congr
  intro x _
  exact coe_add_natCast x (t / n)

/-- In the additive circle `ℝ/ℤ`, adding the `k`-th and `l`-th elementary half-open cells of the
`n`-fold grid gives the union of the `(k+l)`-th and `(k+l+1)`-th cells. -/
theorem cell_add_cell (n : ℕ) [NeZero n] (k l : ZMod n) :
    ((fun x : ℝ => (x : UnitAddCircle)) '' Set.Ico ((k.val : ℝ)/n) (((k.val:ℝ)+1)/n))
    + ((fun x : ℝ => (x : UnitAddCircle)) '' Set.Ico ((l.val : ℝ)/n) (((l.val:ℝ)+1)/n))
    = ((fun x : ℝ => (x : UnitAddCircle)) '' Set.Ico (((k+l).val : ℝ)/n) ((((k+l).val:ℝ)+1)/n))
      ∪ ((fun x : ℝ => (x : UnitAddCircle)) '' Set.Ico (((k+l+1).val : ℝ)/n) ((((k+l+1).val:ℝ)+1)/n)) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  set s : ℕ := k.val + l.val with hs
  have hs_cast : ((s : ℕ) : ZMod n) = k + l := by
    rw [hs]; push_cast
    rw [ZMod.natCast_zmod_val k, ZMod.natCast_zmod_val l]
  have hs_cast1 : (((s + 1) : ℕ) : ZMod n) = k + l + 1 := by
    rw [Nat.cast_add, Nat.cast_one, hs_cast]
  rw [image_add_coe]
  have hkstep : ((k.val : ℝ) / n) < (((k.val : ℝ) + 1) / n) := by
    rw [div_lt_div_iff_of_pos_right hnpos]; linarith
  have hlstep : ((l.val : ℝ) / n) < (((l.val : ℝ) + 1) / n) := by
    rw [div_lt_div_iff_of_pos_right hnpos]; linarith
  have hsum : Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n)
      + Set.Ico ((l.val : ℝ) / n) (((l.val : ℝ) + 1) / n)
      = Set.Ico ((s : ℝ) / n) (((s : ℝ) + 2) / n) := by
    rw [Ico_add_Ico _ _ _ _ hkstep hlstep]
    have e1 : (k.val : ℝ) / n + (l.val : ℝ) / n = (s : ℝ) / n := by
      rw [hs]; push_cast; field_simp
    have e2 : ((k.val : ℝ) + 1) / n + ((l.val : ℝ) + 1) / n = ((s : ℝ) + 2) / n := by
      rw [hs]; push_cast; field_simp; ring
    rw [e1, e2]
  rw [hsum]
  have hsplit : Set.Ico ((s : ℝ) / n) (((s : ℝ) + 2) / n)
      = Set.Ico ((s : ℝ) / n) (((s : ℝ) + 1) / n)
        ∪ Set.Ico (((s : ℝ) + 1) / n) (((s : ℝ) + 2) / n) := by
    refine (Set.Ico_union_Ico_eq_Ico ?_ ?_).symm
    · rw [div_le_div_iff_of_pos_right hnpos]; linarith
    · rw [div_le_div_iff_of_pos_right hnpos]; linarith
  rw [hsplit, Set.image_union]
  have hcell1 : (fun x : ℝ => (x : UnitAddCircle)) '' Set.Ico ((s : ℝ) / n) (((s : ℝ) + 1) / n)
      = (fun x : ℝ => (x : UnitAddCircle)) ''
          Set.Ico (((k + l).val : ℝ) / n) ((((k + l).val : ℝ) + 1) / n) := by
    rw [image_Ico_div_eq_cell n s, hs_cast]
  have hcell2 : (fun x : ℝ => (x : UnitAddCircle)) '' Set.Ico (((s : ℝ) + 1) / n) (((s : ℝ) + 2) / n)
      = (fun x : ℝ => (x : UnitAddCircle)) ''
          Set.Ico (((k + l + 1).val : ℝ) / n) ((((k + l + 1).val : ℝ) + 1) / n) := by
    have e1 : ((s : ℝ) + 1) / n = (((s + 1 : ℕ) : ℝ)) / n := by push_cast; ring
    have e2 : ((s : ℝ) + 2) / n = ((((s + 1 : ℕ) : ℝ)) + 1) / n := by push_cast; ring
    rw [e1, e2, image_Ico_div_eq_cell n (s + 1), hs_cast1]
  rw [hcell1, hcell2]

end Commons.Measure.AddCircle
