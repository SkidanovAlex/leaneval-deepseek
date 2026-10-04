import Mathlib
import Submission.Work.Diff.Alg.PA.Defs
import Submission.Work.Diff.Alg.PA.R4_bianchi
import Submission.Work.Diff.Alg.PA.R4_polarize

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The quartic form `secK R · ·` of an algebraic curvature tensor

`secK R p q = R4 R p q p q` is the sectional curvature of the (not necessarily orthonormal) pair
`(p,q)`.  For an algebraic curvature tensor `R` (`IsAlgCurv R`) this quartic form is
* multilinear and homogeneous of degree two in each argument (`secK_add_smul_second`,
  `secK_add_smul_first`, `secK_smul_smul`),
* insensitive to adding a multiple of `p` to the second argument (`secK_sub_smul_second`),

and it *determines* `R`: the combination
`polU R X Y W Z = secK R (X+W) (Y+Z) - secK R (X+W) (Y-Z) - secK R (X-W) (Y+Z) + secK R (X-W) (Y-Z)`
and its sibling `polV` (with the roles of `Y` and `W` exchanged) give
`24 * R4 R X Y W Z = 2 * polU + polV` (`R4_eq_polarize`).  This is the standard polarization
identity expressing a curvature tensor through its sectional curvatures; no orthonormality of
`X, Y, W, Z` is used.

These are the elementary multilinear-algebra lemmas used by `Work.Diff.L.secK_pair_bound` and
`Work.Diff.L.curv4_component_bound`.
-/

namespace Work.Diff.L

open Submission.Diff.Alg Finset
open Work.Diff.Alg.PA

variable {n : ℕ}

/-! ## Elementary algebra of `dot` -/

theorem dot_comm (p q : Fin n → ℝ) : dot p q = dot q p := by
  simp only [dot]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem dot_add_add (p p' q q' : Fin n → ℝ) :
    dot (p + p') (q + q') = dot p q + dot p q' + dot p' q + dot p' q' := by
  simp only [dot, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem dot_sub_sub (p p' q q' : Fin n → ℝ) :
    dot (p - p') (q - q') = dot p q - dot p q' - dot p' q + dot p' q' := by
  simp only [dot, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

theorem dot_smul_smul (a b : ℝ) (p q : Fin n → ℝ) :
    dot (a • p) (b • q) = a * b * dot p q := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_self_nonneg (p : Fin n → ℝ) : 0 ≤ dot p p := by
  simp only [dot]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem dot_self_eq_zero {p : Fin n → ℝ} (h : dot p p = 0) : p = 0 := by
  funext i
  have h1 : p i * p i ≤ dot p p :=
    Finset.single_le_sum (f := fun j => p j * p j) (fun j _ => mul_self_nonneg (p j))
      (Finset.mem_univ i)
  rw [h] at h1
  exact mul_self_eq_zero.mp (le_antisymm h1 (mul_self_nonneg _))

theorem dot_self_pos {p : Fin n → ℝ} (hp : p ≠ 0) : 0 < dot p p :=
  lt_of_le_of_ne (dot_self_nonneg p) fun h => hp (dot_self_eq_zero h.symm)

theorem dot_stdB_add_self_le (i k : Fin n) :
    dot (stdB n i + stdB n k) (stdB n i + stdB n k) ≤ 4 := by
  rw [dot_add_add, dot_stdB_stdB, dot_stdB_stdB, dot_stdB_stdB, dot_stdB_stdB]
  split_ifs <;> norm_num

theorem dot_stdB_sub_self_le (i k : Fin n) :
    dot (stdB n i - stdB n k) (stdB n i - stdB n k) ≤ 4 := by
  rw [dot_sub_sub, dot_stdB_stdB, dot_stdB_stdB, dot_stdB_stdB, dot_stdB_stdB]
  split_ifs <;> norm_num

/-! ## Component form at the standard basis -/

/-- `R4` at four standard basis vectors is the corresponding component of `R`. -/
theorem R4_stdB (R : Curv4 n) (i j k l : Fin n) :
    R4 R (stdB n i) (stdB n j) (stdB n k) (stdB n l) = R i j k l := by
  simp only [R4, stdB]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single k]
      · rw [Finset.sum_eq_single l]
        · simp
        · intro m _ hm; simp [Pi.single_eq_of_ne hm]
        · intro h; exact absurd (Finset.mem_univ l) h
      · intro m _ hm; simp [Pi.single_eq_of_ne hm]
      · intro h; exact absurd (Finset.mem_univ k) h
    · intro m _ hm; simp [Pi.single_eq_of_ne hm]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro m _ hm; simp [Pi.single_eq_of_ne hm]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ## Multilinearity of the quartic form `secK R · ·` -/

theorem secK_add_smul_second (R : Curv4 n) (hR : IsAlgCurv R) (p q q' : Fin n → ℝ) (c : ℝ) :
    secK R p (q + c • q') = secK R p q + 2 * c * R4 R p q p q' + c ^ 2 * secK R p q' := by
  have h := R4_pair_symm R hR p q p q'
  simp only [secK, R4_add₂, R4_add₄, R4_smul₂, R4_smul₄]
  rw [h]; ring

theorem secK_add_smul_first (R : Curv4 n) (hR : IsAlgCurv R) (p p' q : Fin n → ℝ) (c : ℝ) :
    secK R (p + c • p') q = secK R p q + 2 * c * R4 R p q p' q + c ^ 2 * secK R p' q := by
  have h := R4_pair_symm R hR p q p' q
  simp only [secK, R4_add₁, R4_add₃, R4_smul₁, R4_smul₃]
  rw [h]; ring

theorem secK_add_second (R : Curv4 n) (hR : IsAlgCurv R) (p q q' : Fin n → ℝ) :
    secK R p (q + q') = secK R p q + 2 * R4 R p q p q' + secK R p q' := by
  simpa using secK_add_smul_second R hR p q q' 1

theorem secK_add_first (R : Curv4 n) (hR : IsAlgCurv R) (p p' q : Fin n → ℝ) :
    secK R (p + p') q = secK R p q + 2 * R4 R p q p' q + secK R p' q := by
  simpa using secK_add_smul_first R hR p p' q 1

theorem secK_sub_second (R : Curv4 n) (hR : IsAlgCurv R) (p q q' : Fin n → ℝ) :
    secK R p (q - q') = secK R p q - 2 * R4 R p q p q' + secK R p q' := by
  have h := secK_add_smul_second R hR p q q' (-1)
  simpa [sub_eq_add_neg, neg_one_smul] using h

theorem secK_sub_first (R : Curv4 n) (hR : IsAlgCurv R) (p p' q : Fin n → ℝ) :
    secK R (p - p') q = secK R p q - 2 * R4 R p q p' q + secK R p' q := by
  have h := secK_add_smul_first R hR p p' q (-1)
  simpa [sub_eq_add_neg, neg_one_smul] using h

theorem secK_smul_smul (R : Curv4 n) (a b : ℝ) (p q : Fin n → ℝ) :
    secK R (a • p) (b • q) = a ^ 2 * b ^ 2 * secK R p q := by
  simp only [secK, R4_smul₁, R4_smul₂, R4_smul₃, R4_smul₄]
  ring

theorem secK_comm (R : Curv4 n) (hR : IsAlgCurv R) (p q : Fin n → ℝ) :
    secK R q p = secK R p q := by
  have h1 := R4_antisym₁₂ R hR p q q p
  have h2 := R4_antisym₃₄ R hR p q p q
  simp only [secK]
  rw [h1, h2]; ring

/-- `secK R p ·` is unchanged by removing the component of the second argument along the first. -/
theorem secK_sub_smul_second (R : Curv4 n) (hR : IsAlgCurv R) (p q : Fin n → ℝ) (c : ℝ) :
    secK R p (q - c • p) = secK R p q := by
  have h1 : R4 R p q p (c • p) = 0 := by
    rw [R4_smul₄, R4_self₂ R hR p q p, mul_zero]
  have h2 : secK R p (c • p) = 0 := by
    simp only [secK, R4_smul₂, R4_smul₄, R4_self₁ R hR p p p, mul_zero]
  rw [secK_sub_second R hR p q (c • p), h1, h2]
  ring


/-! ## Negation in each slot -/

theorem R4_neg₂ (R : Curv4 n) (a b c d : Fin n → ℝ) : R4 R a (-b) c d = - R4 R a b c d := by
  simpa using R4_smul₂ R (-1) a b c d

theorem R4_neg₃ (R : Curv4 n) (a b c d : Fin n → ℝ) : R4 R a b (-c) d = - R4 R a b c d := by
  simpa using R4_smul₃ R (-1) a b c d

theorem R4_neg₄ (R : Curv4 n) (a b c d : Fin n → ℝ) : R4 R a b c (-d) = - R4 R a b c d := by
  simpa using R4_smul₄ R (-1) a b c d

/-! ## Second-order expansions in one slot (used by the polarization identities) -/

theorem R4_add_add_third_first (R : Curv4 n) (X W Y Z : Fin n → ℝ) :
    R4 R (X + W) Y (X + W) Z
      = R4 R X Y X Z + R4 R X Y W Z + R4 R W Y X Z + R4 R W Y W Z := by
  simp only [R4_add₁, R4_add₃]; ring

theorem R4_sub_sub_third_first (R : Curv4 n) (X W Y Z : Fin n → ℝ) :
    R4 R (X - W) Y (X - W) Z
      = R4 R X Y X Z - R4 R X Y W Z - R4 R W Y X Z + R4 R W Y W Z := by
  rw [show X - W = X + (-W) from sub_eq_add_neg X W]
  rw [R4_add_add_third_first]
  simp only [R4_neg₁, R4_neg₂, R4_neg₃, R4_neg₄]
  ring

theorem R4_add_add_second_fourth (R : Curv4 n) (X W Y Z : Fin n → ℝ) :
    R4 R X (W + Z) Y (W + Z)
      = R4 R X W Y W + R4 R X W Y Z + R4 R X Z Y W + R4 R X Z Y Z := by
  simp only [R4_add₂, R4_add₄]; ring

theorem R4_sub_sub_second_fourth (R : Curv4 n) (X W Y Z : Fin n → ℝ) :
    R4 R X (W - Z) Y (W - Z)
      = R4 R X W Y W - R4 R X W Y Z - R4 R X Z Y W + R4 R X Z Y Z := by
  rw [show W - Z = W + (-Z) from sub_eq_add_neg W Z]
  rw [R4_add_add_second_fourth]
  simp only [R4_neg₂, R4_neg₄]
  ring

/-! ## The polarization identities -/

/-- The four-term `secK`-combination whose polarization gives `R4 R X Y W Z`. -/
noncomputable def polU (R : Curv4 n) (X Y W Z : Fin n → ℝ) : ℝ :=
  secK R (X + W) (Y + Z) - secK R (X + W) (Y - Z) - secK R (X - W) (Y + Z)
    + secK R (X - W) (Y - Z)

/-- The sibling combination with `Y` and `W` exchanged. -/
noncomputable def polV (R : Curv4 n) (X Y W Z : Fin n → ℝ) : ℝ :=
  secK R (X + Y) (W + Z) - secK R (X + Y) (W - Z) - secK R (X - Y) (W + Z)
    + secK R (X - Y) (W - Z)

theorem polU_eq (R : Curv4 n) (hR : IsAlgCurv R) (X Y W Z : Fin n → ℝ) :
    polU R X Y W Z = 8 * (R4 R X Y W Z + R4 R X Z W Y) := by
  have h1 : secK R (X + W) (Y + Z)
      = secK R (X + W) Y + 2 * R4 R (X + W) Y (X + W) Z + secK R (X + W) Z :=
    secK_add_second R hR (X + W) Y Z
  have h2 : secK R (X + W) (Y - Z)
      = secK R (X + W) Y - 2 * R4 R (X + W) Y (X + W) Z + secK R (X + W) Z :=
    secK_sub_second R hR (X + W) Y Z
  have h3 : secK R (X - W) (Y + Z)
      = secK R (X - W) Y + 2 * R4 R (X - W) Y (X - W) Z + secK R (X - W) Z :=
    secK_add_second R hR (X - W) Y Z
  have h4 : secK R (X - W) (Y - Z)
      = secK R (X - W) Y - 2 * R4 R (X - W) Y (X - W) Z + secK R (X - W) Z :=
    secK_sub_second R hR (X - W) Y Z
  have hP : R4 R (X + W) Y (X + W) Z - R4 R (X - W) Y (X - W) Z
      = 2 * R4 R X Y W Z + 2 * R4 R W Y X Z := by
    rw [R4_add_add_third_first, R4_sub_sub_third_first]; ring
  have hsym : R4 R W Y X Z = R4 R X Z W Y := R4_pair_symm R hR X Z W Y
  simp only [polU, h1, h2, h3, h4]
  linarith

theorem polV_eq (R : Curv4 n) (hR : IsAlgCurv R) (X Y W Z : Fin n → ℝ) :
    polV R X Y W Z = 8 * (R4 R X Y W Z - 2 * R4 R X Z W Y) := by
  have h1 : secK R (X + Y) (W + Z)
      = secK R X (W + Z) + 2 * R4 R X (W + Z) Y (W + Z) + secK R Y (W + Z) :=
    secK_add_first R hR X Y (W + Z)
  have h2 : secK R (X + Y) (W - Z)
      = secK R X (W - Z) + 2 * R4 R X (W - Z) Y (W - Z) + secK R Y (W - Z) :=
    secK_add_first R hR X Y (W - Z)
  have h3 : secK R (X - Y) (W + Z)
      = secK R X (W + Z) - 2 * R4 R X (W + Z) Y (W + Z) + secK R Y (W + Z) :=
    secK_sub_first R hR X Y (W + Z)
  have h4 : secK R (X - Y) (W - Z)
      = secK R X (W - Z) - 2 * R4 R X (W - Z) Y (W - Z) + secK R Y (W - Z) :=
    secK_sub_first R hR X Y (W - Z)
  have hP : R4 R X (W + Z) Y (W + Z) - R4 R X (W - Z) Y (W - Z)
      = 2 * R4 R X W Y Z + 2 * R4 R X Z Y W := by
    rw [R4_add_add_second_fourth, R4_sub_sub_second_fourth]; ring
  have hh : R4 R X W Y Z = R4 R X Y W Z - R4 R X Z W Y := by
    have hb := R4_bianchi n R hR X W Y Z
    have hsym : R4 R W Y X Z = R4 R X Z W Y := R4_pair_symm R hR X Z W Y
    have hanti : R4 R Y X W Z = - R4 R X Y W Z := R4_antisym₁₂ R hR X Y W Z
    linarith
  have h34 : R4 R X Z Y W = - R4 R X Z W Y := R4_antisym₃₄ R hR X Z W Y
  simp only [polV, h1, h2, h3, h4]
  linarith

/-- The polarization identity: an algebraic curvature tensor is determined by its quartic form. -/
theorem R4_eq_polarize (R : Curv4 n) (hR : IsAlgCurv R) (X Y W Z : Fin n → ℝ) :
    R4 R X Y W Z = (2 * polU R X Y W Z + polV R X Y W Z) / 24 := by
  have h1 := polU_eq R hR X Y W Z
  have h2 := polV_eq R hR X Y W Z
  linarith

end Work.Diff.L
