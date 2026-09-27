import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.margulisPairDefs
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.abs_mat_le_tpart_actO
import Submission.Work.Mostow.BaryBase

/-!
# Shared vocabulary for `margulisCusp`

The Margulis/Zassenhaus argument of `Work.Mostow.margulisCusp` runs with the *sheet preserving*
lift of `PO(n,1)` into matrices: every `g : PO n 1` has a representative `LambdaMat g`
(`Submission.Work.Mostow.StabLift`) with non-negative time-time entry, and `LambdaMat` is a group
homomorphism `PO n 1 →* matrices` (`LambdaMat_mul`, `LambdaMat_inv`, `LambdaMat_one`).

`ToO g` re-packages `LambdaMat g` as an element of `O(n,1)` (it satisfies the two defining
relations), so that the entrywise near-identity predicates `Near1`/`NearId` of
`Submission.Work.Mostow.margulisPair` — and the commutator estimates proved there — apply to it.

The lemmas below translate between the hyperbolic displacement of `g • 0` and the entrywise
deviation of `ToO g` from the identity:

* `Near1_ToO_of_hdist` : `hdist 0 (g • 0) ≤ R` forces `Near1 (ToO g) (cosh R + 1)`;
* `hdist_le_of_Near1_ToO` : `Near1 (ToO g) q` forces `hdist 0 (g • 0) ≤ arcosh (1 + q)`.

`ci A B` is the iterated commutator sequence `c₀ = B`, `c_{j+1} = A c_j A⁻¹ c_j⁻¹`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-! ## The sheet preserving lift -/

/-- The sheet-preserving lift of `g : PO n 1`, as an element of `O(n,1)`. -/
def ToO (g : PO n 1) : O1 n :=
  O1.ofMatrix (LambdaMat g) ⟨LambdaMat_isJOrth g, LambdaMat_isJOrth_row g⟩

@[simp] lemma mat_ToO (g : PO n 1) : mat (ToO g) = LambdaMat g :=
  mat_O1_ofMatrix _ _

/-- The underlying matrix determines an element of `O(n,1)`. -/
lemma O1.mat_injective {A B : O1 n} (h : mat A = mat B) : A = B := by
  apply Subtype.ext
  have h2 := congrArg (fun M => (MatrixSum.ofMatrix M : MatrixSum (Fin n) (Fin 1) ℝ)) h
  simpa only [mat, RingEquiv.apply_symm_apply] using h2

/-- `Near1` only depends on the underlying matrix. -/
lemma Near1.of_mat_eq {A B : O1 n} (h : mat A = mat B) {q : ℝ} :
    Near1 A q ↔ Near1 B q := by
  simp only [Near1, h]

lemma Near1.mat_eq {A B : O1 n} (h : mat A = mat B) {q : ℝ} (hA : Near1 A q) : Near1 B q :=
  (Near1.of_mat_eq h).mp hA

lemma ToO_mul (hA : POActionProp n) (g h : PO n 1) : ToO (g * h) = ToO g * ToO h := by
  apply O1.mat_injective
  rw [mat_ToO, mat_mul_coe, mat_ToO, mat_ToO, LambdaMat_mul hA]

lemma ToO_one (hA : POActionProp n) : ToO (1 : PO n 1) = 1 := by
  apply O1.mat_injective
  rw [mat_ToO, LambdaMat_one hA, mat_one_coe]

lemma ToO_mul_inv (hA : POActionProp n) (g : PO n 1) : ToO g * ToO g⁻¹ = 1 := by
  apply O1.mat_injective
  rw [mat_mul_coe, mat_ToO, mat_ToO, LambdaMat_inv hA g, mat_one_coe]

lemma ToO_inv (hA : POActionProp n) (g : PO n 1) : ToO g⁻¹ = (ToO g)⁻¹ :=
  (inv_eq_of_mul_eq_one_right (ToO_mul_inv hA g)).symm

/-! ## Near identity versus displacement -/

lemma abs_tsign (A : O1 n) : |tsign A| = 1 := by
  rw [tsign]; split <;> norm_num

/-- Every entry of `ToO g` is bounded by `tpart (g • 0) = cosh (hdist 0 (g • 0))`. -/
lemma abs_ToO_le_tpart (g : PO n 1) (i j : Fin n ⊕ Fin 1) :
    |mat (ToO g) i j| ≤ tpart (g • (0 : E n)) := by
  rw [mat_ToO, LambdaMat, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_tsign, one_mul]
  have h := abs_mat_le_tpart_actO (rep g) i j
  rwa [show actO (rep g) (0 : E n) = g • (0 : E n) from rfl] at h

/-- An element of `PO n 1` displacing the origin by at most `R` has an entrywise
`(cosh R + 1)`-bound on its sheet-preserving lift. -/
lemma Near1_ToO_of_hdist {R : ℝ} (hR : 0 ≤ R) {g : PO n 1}
    (hg : hdist (0 : E n) (g • (0 : E n)) ≤ R) : Near1 (ToO g) (Real.cosh R + 1) := by
  intro i j
  have h1 := abs_ToO_le_tpart g i j
  have h2 : tpart (g • (0 : E n)) = Real.cosh (hdist 0 (g • (0 : E n))) :=
    (cosh_hdist_zero (g • (0 : E n))).symm
  rw [h2] at h1
  have h3 : Real.cosh (hdist 0 (g • (0 : E n))) ≤ Real.cosh R :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg (hdist_nonneg 0 _), abs_of_nonneg hR]; exact hg)
  have h4 : |dE n i j| ≤ 1 := abs_dE_le i j
  have hsub : |mat (ToO g) i j - dE n i j| ≤ |mat (ToO g) i j| + |dE n i j| := by
    calc |mat (ToO g) i j - dE n i j| = |mat (ToO g) i j + (-(dE n i j))| := by ring_nf
      _ ≤ |mat (ToO g) i j| + |-(dE n i j)| := abs_add_le _ _
      _ = |mat (ToO g) i j| + |dE n i j| := by rw [abs_neg]
  calc |mat (ToO g) i j - dE n i j| ≤ |mat (ToO g) i j| + |dE n i j| := hsub
    _ ≤ Real.cosh R + 1 := by linarith

/-- `tsign A` times the time-time entry of `A` is its absolute value. -/
lemma tsign_mul_time_entry (A : O1 n) :
    tsign A * mat A (Sum.inr 0) (Sum.inr 0) = |mat A (Sum.inr 0) (Sum.inr 0)| := by
  by_cases h : 0 < mat A (Sum.inr 0) (Sum.inr 0)
  · rw [tsign, if_pos h, one_mul, abs_of_pos h]
  · rw [tsign, if_neg h, neg_one_mul, abs_of_nonpos (le_of_not_gt h)]

/-- The time-time entry of the sheet preserving lift is `tpart (g • 0)`. -/
lemma ToO_time_entry (hA : POActionProp n) (g : PO n 1) :
    mat (ToO g) (Sum.inr 0) (Sum.inr 0) = tpart (g • (0 : E n)) := by
  have h := congrFun (hlift_LambdaMat hA g (0 : E n)) (Sum.inr 0)
  rw [hlift_zero, Matrix.mulVec_single_one] at h
  rw [mat_ToO]
  exact h.symm

/-- An entrywise bound `q` on the sheet-preserving lift bounds the displacement of the origin. -/
lemma hdist_le_of_Near1_ToO (hA : POActionProp n) {q : ℝ} (hq : 0 ≤ q) {g : PO n 1}
    (h : Near1 (ToO g) q) :
    hdist (0 : E n) (g • (0 : E n)) ≤ Real.arcosh (1 + q) := by
  have hcosh : Real.cosh (hdist (0 : E n) (g • (0 : E n)))
      = mat (ToO g) (Sum.inr 0) (Sum.inr 0) := by
    rw [cosh_hdist_zero, ← ToO_time_entry hA]
  have h3 : mat (ToO g) (Sum.inr 0) (Sum.inr 0) ≤ 1 + q := by
    have hh := h (Sum.inr 0) (Sum.inr 0)
    rw [show dE n (Sum.inr 0) (Sum.inr 0) = 1 from dE_self _] at hh
    have := (abs_le.mp hh).2
    linarith
  have hpos : 0 < mat (ToO g) (Sum.inr 0) (Sum.inr 0) := by
    rw [ToO_time_entry hA]; exact tpart_pos _
  calc hdist (0 : E n) (g • (0 : E n))
      = Real.arcosh (Real.cosh (hdist (0 : E n) (g • (0 : E n)))) :=
        (Real.arcosh_cosh (hdist_nonneg 0 _)).symm
    _ = Real.arcosh (mat (ToO g) (Sum.inr 0) (Sum.inr 0)) := by rw [hcosh]
    _ ≤ Real.arcosh (1 + q) :=
        (Real.arcosh_le_arcosh hpos (by linarith)).mpr h3

/-! ## The iterated commutator sequence -/

/-- `ci A B` is the iterated commutator of `B` with `A`: `c₀ = B`, `c_{j+1} = A c_j A⁻¹ c_j⁻¹`. -/
def ci {G : Type*} [Group G] (A B : G) : ℕ → G
  | 0 => B
  | (j + 1) => A * ci A B j * A⁻¹ * (ci A B j)⁻¹

@[simp] lemma ci_zero {G : Type*} [Group G] (A B : G) : ci A B 0 = B := rfl

@[simp] lemma ci_succ {G : Type*} [Group G] (A B : G) (j : ℕ) :
    ci A B (j + 1) = A * ci A B j * A⁻¹ * (ci A B j)⁻¹ := rfl

end

end Work.Mostow

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-! ## The two-radius commutator estimate

A self-contained copy of the estimate that the shrinking argument of `margulisCusp` needs: if
`A` has defect `a` and `B` has defect `b` (entrywise, relative to the identity) then the
commutator `A B A⁻¹ B⁻¹` has defect at most `2 (n+1)³ a b (1+a)(1+b)`. -/

/-- Entrywise bound for `AB - BA` in terms of the defects of `A` and `B`. -/
lemma abs_sub_comm_mul_le_two {A B : O1 n} {a b : ℝ} (hA : Near1 A a) (hB : Near1 B b)
    (i j : Fin n ⊕ Fin 1) :
    |(mat A * mat B - mat B * mat A) i j| ≤ 2 * (msz n * a * b) := by
  have ha : 0 ≤ a := hA.nonneg
  have hb : 0 ≤ b := hB.nonneg
  have key : (mat A * mat B - mat B * mat A) i j =
      (∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)) -
        (∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)) := by
    have p1 := sub_mul_sub_apply (n := n) (A := mat A) (B := mat B) i j
    have p2 := sub_mul_sub_apply (n := n) (A := mat B) (B := mat A) i j
    rw [show (mat A * mat B - mat B * mat A) i j
        = (mat A * mat B) i j - (mat B * mat A) i j from rfl, p1, p2]
    abel
  have b1 : |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)| ≤ msz n * (a * b) := by
    calc |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)|
        ≤ ∑ k, |(mat A i k - dE n i k) * (mat B k j - dE n k j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k, a * b := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          have s1 : |mat A i k - dE n i k| * |mat B k j - dE n k j|
              ≤ a * |mat B k j - dE n k j| :=
            mul_le_mul_of_nonneg_right (hA i k) (abs_nonneg _)
          have s2 : a * |mat B k j - dE n k j| ≤ a * b :=
            mul_le_mul_of_nonneg_left (hB k j) ha
          linarith [s1, s2]
      _ = msz n * (a * b) := sum_const_sum n _
  have b2 : |∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)| ≤ msz n * (a * b) := by
    calc |∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)|
        ≤ ∑ k, |(mat B i k - dE n i k) * (mat A k j - dE n k j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k, a * b := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          have s1 : |mat B i k - dE n i k| * |mat A k j - dE n k j|
              ≤ b * |mat A k j - dE n k j| :=
            mul_le_mul_of_nonneg_right (hB i k) (abs_nonneg _)
          have s2 : b * |mat A k j - dE n k j| ≤ b * a :=
            mul_le_mul_of_nonneg_left (hA k j) hb
          linarith [s1, s2]
      _ = msz n * (a * b) := sum_const_sum n _
  have htri : |(∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)) -
      (∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j))|
      ≤ |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)|
        + |∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)| := by
    calc |(∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)) -
            (∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j))|
        = |(∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)) +
            (-(∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)))| := by ring_nf
      _ ≤ |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)|
            + |-(∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j))| := abs_add_le _ _
      _ = |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)|
            + |∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)| := by rw [abs_neg]
  rw [key]
  linarith [htri, b1, b2]

/-- Entrywise bound for the product of the inverses. -/
lemma abs_inv_mul_entry_le_two {A B : O1 n} {a b : ℝ} (hA : Near1 A a) (hB : Near1 B b)
    (k j : Fin n ⊕ Fin 1) :
    |((mat A)⁻¹ * (mat B)⁻¹) k j| ≤ msz n * (1 + a) * (1 + b) := by
  have ha : 0 ≤ a := hA.nonneg
  have hb : 0 ≤ b := hB.nonneg
  calc |((mat A)⁻¹ * (mat B)⁻¹) k j| ≤ ∑ l, |(mat A)⁻¹ k l * (mat B)⁻¹ l j| := by
        rw [Matrix.mul_apply]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l, (1 + a) * (1 + b) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_inv_matrix_entry_le' hA ha k l) (abs_inv_matrix_entry_le' hB hb l j)
          (abs_nonneg _) (by linarith)
    _ = msz n * ((1 + a) * (1 + b)) := sum_const_sum n _
    _ = msz n * (1 + a) * (1 + b) := by ring

/-- **The two-radius commutator estimate.** -/
lemma near1_commutator_two {A B : O1 n} {a b : ℝ} (hA : Near1 A a) (hB : Near1 B b) :
    Near1 (A * B * A⁻¹ * B⁻¹) (2 * (msz n) ^ 3 * a * b * (1 + a) * (1 + b)) := by
  have hAA : mat A * (mat A)⁻¹ = 1 := by
    have h : mat A * mat A⁻¹ = 1 := by rw [← mat_mul_coe, mul_inv_cancel, mat_one_coe]
    rwa [mat_inv_coe] at h
  have hBB : mat B * (mat B)⁻¹ = 1 := by
    have h : mat B * mat B⁻¹ = 1 := by rw [← mat_mul_coe, mul_inv_cancel, mat_one_coe]
    rwa [mat_inv_coe] at h
  have hBA : (mat B * mat A) * ((mat A)⁻¹ * (mat B)⁻¹) = 1 := by
    rw [mul_assoc, ← mul_assoc (mat A), hAA, one_mul, hBB]
  have hmat : mat (A * B * A⁻¹ * B⁻¹) - 1 = (mat A * mat B - mat B * mat A) *
      ((mat A)⁻¹ * (mat B)⁻¹) := by
    have hL : mat (A * B * A⁻¹ * B⁻¹) = (mat A * mat B) * ((mat A)⁻¹ * (mat B)⁻¹) := by
      rw [mat_mul_coe, mat_mul_coe, mat_mul_coe, mat_inv_coe, mat_inv_coe, mul_assoc]
    rw [hL]
    have hexp : (mat A * mat B) * ((mat A)⁻¹ * (mat B)⁻¹) - 1
        = (mat A * mat B) * ((mat A)⁻¹ * (mat B)⁻¹)
          - (mat B * mat A) * ((mat A)⁻¹ * (mat B)⁻¹) := by rw [hBA]
    rw [hexp, ← sub_mul]
  intro i j
  have hkey : mat (A * B * A⁻¹ * B⁻¹) i j - dE n i j =
      ((mat A * mat B - mat B * mat A) * ((mat A)⁻¹ * (mat B)⁻¹)) i j := by
    have hD : (mat (A * B * A⁻¹ * B⁻¹) - 1) i j
        = mat (A * B * A⁻¹ * B⁻¹) i j - dE n i j :=
      sub_one_entry (A * B * A⁻¹ * B⁻¹) i j
    have hentry : (mat (A * B * A⁻¹ * B⁻¹) - 1) i j
        = ((mat A * mat B - mat B * mat A) * ((mat A)⁻¹ * (mat B)⁻¹)) i j := by
      rw [hmat]
    rw [← hD, hentry]
  rw [hkey, Matrix.mul_apply]
  calc |∑ k, (mat A * mat B - mat B * mat A) i k * ((mat A)⁻¹ * (mat B)⁻¹) k j|
      ≤ ∑ k, |(mat A * mat B - mat B * mat A) i k| * |((mat A)⁻¹ * (mat B)⁻¹) k j| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
        exact Finset.sum_congr rfl fun k _ => abs_mul _ _
    _ ≤ ∑ _k, (2 * (msz n * a * b)) * (msz n * (1 + a) * (1 + b)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hnn : (0:ℝ) ≤ 2 * (msz n * a * b) := by
          have := msz_nonneg n; have := hA.nonneg; have := hB.nonneg
          positivity
        exact mul_le_mul (abs_sub_comm_mul_le_two hA hB i k) (abs_inv_mul_entry_le_two hA hB k j)
          (abs_nonneg _) hnn
    _ = msz n * ((2 * (msz n * a * b)) * (msz n * (1 + a) * (1 + b))) := sum_const_sum n _
    _ = 2 * (msz n) ^ 3 * a * b * (1 + a) * (1 + b) := by ring

/-- **The shrinking iteration**: iterating commutators with an `η`-small element contracts the
defect by a factor `1/2` at each step, as long as the initial defect is bounded by `C`. -/
lemma near1_ci_shrink_O1 {A B : O1 n} {η b C : ℝ} (hA : Near1 A η) (hη : 0 ≤ η)
    (hB : Near1 B b) (hb : 0 ≤ b) (hbC : b ≤ C) (hC : 0 ≤ C)
    (hsmall : 2 * (msz n) ^ 3 * η * (1 + η) * (1 + C) ≤ 1 / 2) (j : ℕ) :
    Near1 (ci A B j) ((1 / 2 : ℝ) ^ j * b) := by
  induction j with
  | zero => simpa using hB
  | succ j ih =>
      have hd0 : 0 ≤ (1 / 2 : ℝ) ^ j * b := by positivity
      have hdC : (1 / 2 : ℝ) ^ j * b ≤ C := by
        have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have h2 : (1 / 2 : ℝ) ^ j * b ≤ 1 * b := mul_le_mul_of_nonneg_right h1 hb
        linarith [hbC]
      have h1d : 1 + (1 / 2 : ℝ) ^ j * b ≤ 1 + C := by linarith
      have hstep : Near1 (A * ci A B j * A⁻¹ * (ci A B j)⁻¹)
          (2 * (msz n) ^ 3 * η * ((1 / 2 : ℝ) ^ j * b) * (1 + η)
            * (1 + (1 / 2 : ℝ) ^ j * b)) := near1_commutator_two hA ih
      have h2 : (0:ℝ) ≤ 2 * (msz n) ^ 3 * η * ((1 / 2 : ℝ) ^ j * b) * (1 + η) := by
        have hm := msz_nonneg n
        have h1b : (0:ℝ) ≤ (1 / 2 : ℝ) ^ j * b := hd0
        positivity
      intro i k
      refine le_trans (hstep i k) ?_
      calc 2 * (msz n) ^ 3 * η * ((1 / 2 : ℝ) ^ j * b) * (1 + η) * (1 + (1 / 2 : ℝ) ^ j * b)
          ≤ 2 * (msz n) ^ 3 * η * ((1 / 2 : ℝ) ^ j * b) * (1 + η) * (1 + C) :=
            mul_le_mul_of_nonneg_left h1d h2
        _ = (2 * (msz n) ^ 3 * η * (1 + η) * (1 + C)) * ((1 / 2 : ℝ) ^ j * b) := by ring
        _ ≤ (1 / 2) * ((1 / 2 : ℝ) ^ j * b) :=
            mul_le_mul_of_nonneg_right hsmall hd0
        _ = (1 / 2 : ℝ) ^ (j + 1) * b := by ring

/-- The sheet-preserving lift of an iterated commutator is the iterated commutator of the
lifts. -/
lemma ToO_ci (hA : POActionProp n) (A B : PO n 1) (j : ℕ) :
    ToO (ci A B j) = ci (ToO A) (ToO B) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [ci_succ, ToO_mul hA, ToO_inv hA, ih]

/-- **Defect contraction for the iterated commutator of `PO(n,1)`-elements.** -/
theorem toO_ci_shrink' (n : ℕ) (hA : POActionProp n) {A B : PO n 1} {η b C : ℝ}
    (hAη : Near1 (ToO A) η) (hη0 : 0 ≤ η)
    (hB : Near1 (ToO B) b) (hb0 : 0 ≤ b) (hbC : b ≤ C)
    (hC0 : 0 ≤ C) (hsmall : 2 * (msz n) ^ 3 * η * (1 + η) * (1 + C) ≤ 1 / 2) :
    ∀ j : ℕ, Near1 (ToO (ci A B j)) ((1 / 2 : ℝ) ^ j * b) := by
  intro j
  have h1 := near1_ci_shrink_O1 hAη hη0 hB hb0 hbC hC0 hsmall j
  rw [ToO_ci hA] at *
  exact h1

end

end Work.Mostow
