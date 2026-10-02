import Mathlib
import Submission.Work.SeedCertNum.Box
import Submission.Work.SeedCertNum.Dyadic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

/-! ## Elementary real lemmas about the four corner products

The product of two real intervals `[a,b]` and `[c,d]` is contained in the hull of the four corner
products `a*c, a*d, b*c, b*d`; unlike addition this needs a case distinction on the signs, since
`y ↦ x*y` is monotone only on one side of `0`.  The two lemmas below are the real-number content
of the soundness of `Work.SeedCert.IV.mul`. -/

/-- The two groupings of a `max` of four terms agree (AC-normal form for `max`). -/
private lemma max4_swap (p q r s : ℝ) :
    max (max p q) (max r s) = max (max p r) (max q s) := by ac_rfl

/-- The two groupings of a `min` of four terms agree (AC-normal form for `min`). -/
private lemma min4_swap (p q r s : ℝ) :
    min (min p q) (min r s) = min (min p r) (min q s) := by ac_rfl

/-- Upper bound of a product of two intervals: if `a ≤ x ≤ b` and `c ≤ y ≤ d` then `x*y` is at
most the largest of the four corner products (in the grouping used by `IV.cornerMax`). -/
private lemma mul_le_cornerMax {a b c d x y : ℝ} (ha : a ≤ x) (hx : x ≤ b) (hc : c ≤ y)
    (hy : y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  -- `x*y ≤ max (x*c) (x*d)`: the map `y ↦ x*y` is monotone on `[c,d]` when `x ≥ 0` and
  -- antitone when `x ≤ 0`.
  have h1 : x * y ≤ max (x * c) (x * d) := by
    rcases le_total 0 x with h | h
    · exact le_trans (mul_le_mul_of_nonneg_left hy h) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left hc h) (le_max_left _ _)
  -- `x*c ≤ max (a*c) (b*c)`, and likewise with `d` for `c`, by the sign of the second factor.
  have h2 : x * c ≤ max (a * c) (b * c) := by
    rcases le_total 0 c with h | h
    · exact le_trans (mul_le_mul_of_nonneg_right hx h) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_right ha h) (le_max_left _ _)
  have h3 : x * d ≤ max (a * d) (b * d) := by
    rcases le_total 0 d with h | h
    · exact le_trans (mul_le_mul_of_nonneg_right hx h) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_right ha h) (le_max_left _ _)
  exact le_trans
    (le_trans h1 (max_le (le_trans h2 (le_max_left _ _)) (le_trans h3 (le_max_right _ _))))
    (le_of_eq (max4_swap (a * c) (b * c) (a * d) (b * d)))

/-- Lower bound of a product of two intervals: if `a ≤ x ≤ b` and `c ≤ y ≤ d` then `x*y` is at
least the smallest of the four corner products (in the grouping used by `IV.cornerMin`). -/
private lemma cornerMin_le_mul {a b c d x y : ℝ} (ha : a ≤ x) (hx : x ≤ b) (hc : c ≤ y)
    (hy : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  -- `min (x*c) (x*d) ≤ x*y`, by monotonicity/antitonicity of `y ↦ x*y` on `[c,d]`.
  have h1 : min (x * c) (x * d) ≤ x * y := by
    rcases le_total 0 x with h | h
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hc h)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hy h)
  -- `min (a*c) (b*c) ≤ x*c`, and likewise with `d` for `c`, by the sign of the second factor.
  have h2 : min (a * c) (b * c) ≤ x * c := by
    rcases le_total 0 c with h | h
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right ha h)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right hx h)
  have h3 : min (a * d) (b * d) ≤ x * d := by
    rcases le_total 0 d with h | h
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right ha h)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right hx h)
  have h4 : min (min (a * c) (b * c)) (min (a * d) (b * d)) ≤ min (x * c) (x * d) :=
    le_min (le_trans (min_le_left _ _) h2) (le_trans (min_le_right _ _) h3)
  have h5 : min (min (a * c) (b * c)) (min (a * d) (b * d)) ≤ x * y := le_trans h4 h1
  rw [min4_swap (a * c) (b * c) (a * d) (b * d)] at h5
  exact h5

/-- **Soundness of the interval product** `Work.SeedCert.IV.mul`, which is the hull
`[Work.SeedCert.IV.cornerMin I J, Work.SeedCert.IV.cornerMax I J]` of the four corner products
`I.lo*J.lo`, `I.lo*J.hi`, `I.hi*J.lo`, `I.hi*J.hi` (each a `Work.SeedCert.Dya` product, so the
statement is about `Dya.toReal` after `Dya.toReal_mul`, and `cornerMin`/`cornerMax` are `Dya.min`/
`Dya.max`, i.e. `min`/`max` of the reals by `Dya.toReal_min`/`Dya.toReal_max`).

If `x ∈ I.toSet` and `y ∈ J.toSet` then `x * y ∈ (I.mul J).toSet`.  Equivalently: with
`a = I.lo.toReal ≤ x ≤ I.hi.toReal = b` and `c = J.lo.toReal ≤ y ≤ J.hi.toReal = d`,
`min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d))`.

A short proof: `x*y ≤ max (x*c) (x*d)` by monotonicity of `y ↦ x*y` on `[c,d]` (split on the sign
of `x`), then `x*c ≤ max (a*c) (b*c)` and `x*d ≤ max (a*d) (b*d)` similarly; the lower bound is
the same argument with the roles of `min`/`max` exchanged.  `Mathlib`'s `Set.Icc_mul_Icc_subset'`
does not apply (it needs monotone multiplication). -/
theorem IV_mem_mul {I J : Work.SeedCert.IV} {x y : ℝ} (hx : x ∈ I.toSet) (hy : y ∈ J.toSet) :
    x * y ∈ (I.mul J).toSet := by
  rw [Work.SeedCert.IV.mem_toSet] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  rw [Work.SeedCert.IV.mem_toSet]
  refine ⟨?_, ?_⟩
  · have h := cornerMin_le_mul (a := I.lo.toReal) (b := I.hi.toReal) (c := J.lo.toReal)
      (d := J.hi.toReal) hx1 hx2 hy1 hy2
    simpa only [Work.SeedCert.IV.mul, Work.SeedCert.IV.cornerMin, Work.SeedCert.Dya.toReal_min,
      Work.SeedCert.Dya.toReal_mul] using h
  · have h := mul_le_cornerMax (a := I.lo.toReal) (b := I.hi.toReal) (c := J.lo.toReal)
      (d := J.hi.toReal) hx1 hx2 hy1 hy2
    simpa only [Work.SeedCert.IV.mul, Work.SeedCert.IV.cornerMax, Work.SeedCert.Dya.toReal_max,
      Work.SeedCert.Dya.toReal_mul] using h

end Work.SeedCertNum
