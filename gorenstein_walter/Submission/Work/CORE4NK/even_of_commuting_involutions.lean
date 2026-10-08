import Mathlib

namespace Work.CORE4NK

open DihedralGroup

/-- Two distinct commuting involutions in a dihedral group force the index `m` to be even:
in `DihedralGroup m` an involution is either a reflection `sr i` or the "half rotation"
`r (m/2)`, and two such commute only if `2 * (difference) = 0` with a nonzero difference. -/
theorem even_of_commuting_involutions {m : ℕ} {x y : DihedralGroup m}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hcomm : x * y = y * x) (hxy : x ≠ y) : Even m := by
  -- `DihedralGroup m` has elements `r i` (rotations) and `sr i` (reflections), with
  -- `r i * r j = r (i+j)`, `sr i * sr j = r (j-i)`, and `sr i` always an involution.
  -- We argue by contradiction: for odd `m` the doubling map on `ZMod m` is injective,
  -- so every involution is `1`, and two reflections commute only if they are equal.
  rw [← Nat.not_odd_iff_even]
  intro hodd
  cases x with
  | r i =>
    -- `r i` is an involution: `r (i + i) = 1`, hence `i + i = 0`, hence `i = 0` for odd `m`.
    exfalso
    have hii : i + i = 0 := by
      rw [← DihedralGroup.r.injEq, ← r_mul_r, hx2, r_zero]
    have hi0 : i = 0 := (ZMod.add_self_eq_zero_iff_eq_zero hodd).mp hii
    exact hx1 (by rw [hi0, r_zero])
  | sr i =>
    cases y with
    | r j =>
      -- Symmetric case: `r j` cannot be a nontrivial involution for odd `m`.
      exfalso
      have hjj : j + j = 0 := by
        rw [← DihedralGroup.r.injEq, ← r_mul_r, hy2, r_zero]
      have hj0 : j = 0 := (ZMod.add_self_eq_zero_iff_eq_zero hodd).mp hjj
      exact hy1 (by rw [hj0, r_zero])
    | sr j =>
      -- Two reflections: commutation forces `2 * (j - i) = 0`, hence `j = i` for odd `m`,
      -- contradicting that the two reflections are distinct.
      exfalso
      have hsub : j - i = i - j := by
        rw [sr_mul_sr, sr_mul_sr] at hcomm
        exact DihedralGroup.r.inj hcomm
      have h2 : (j - i) + (j - i) = 0 := by
        nth_rewrite 2 [hsub]
        rw [← neg_sub, neg_add_cancel]
      have hji : j - i = 0 := (ZMod.add_self_eq_zero_iff_eq_zero hodd).mp h2
      have hij : i = j := (sub_eq_zero.mp hji).symm
      exact hxy (by rw [hij])

end Work.CORE4NK
