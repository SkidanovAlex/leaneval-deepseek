import Mathlib
import Submission.Mostow.Interfaces

/-!
# Shared hyperboloid tools for the Mostow-rigidity development

Linear algebra on `ℝ^{Fin n ⊕ Fin 1}` together with the chart
`hlift : E n → ℝ^{Fin n ⊕ Fin 1}` of the hyperboloid `⟨x,x⟩ = -1`, `x₀ > 0`.

* `mink x y = Σ xᵢyᵢ − x₀y₀` is the Minkowski form;
* `hlift u = (u, √(1+‖u‖²))` is the chart (`⟨hlift u, hlift v⟩ = ⟪u,v⟫ - tpart u tpart v`);
* `cc u v = tpart u * tpart v − ⟪u,v⟫ = −⟨hlift u, hlift v⟩` is the cosh-kernel of the
  hyperbolic distance (`hdist u v = arcosh (cc u v)`);
* `gram u` is the matrix of the hyperbolic metric in the chart (`gH u v = v ⬝ᵥ gram u *ᵥ v`);
* `bmat v` is the boost matrix sending `e₀` to `hlift v`.
-/

open LeanEval.Geometry.MostowRigidity MeasureTheory

namespace Submission.Mostow

noncomputable section

namespace Hyper

variable {n : ℕ}

/-- The Minkowski bilinear form `⟨x,y⟩ = Σ xᵢyᵢ − x₀y₀`. -/
def mink (x y : Fin n ⊕ Fin 1 → ℝ) : ℝ :=
  x ⬝ᵥ (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)).mulVec y

/-- The time vector `e₀`. -/
def etime (n : ℕ) : Fin n ⊕ Fin 1 → ℝ := Pi.single (Sum.inr 0) 1

/-- The spatial part of a vector of `ℝ^{Fin n ⊕ Fin 1}`. -/
def spat (x : Fin n ⊕ Fin 1 → ℝ) : E n := WithLp.toLp 2 fun i => x (Sum.inl i)

/-- The cosh-kernel `tpart u * tpart v − ⟪u,v⟫ = −⟨hlift u, hlift v⟩`. -/
def cc (u v : E n) : ℝ := tpart u * tpart v - inner ℝ u v

/-- The matrix of the hyperbolic metric in the chart: `gH u v = v ⬝ᵥ (gram u *ᵥ v)`. -/
def gram (u : E n) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (1 / (1 + ‖u‖ ^ 2)) • (Matrix.of fun i j => u i * u j)

/-- The boost matrix of `v`: `bmat v ∈ O(1)` and `bmat v *ᵥ e₀ = hlift v`. -/
def bmat (v : E n) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks
    (1 + (1 / (1 + tpart v)) •
      (Matrix.replicateCol (Fin 1) (fun i => v i) * Matrix.replicateRow (Fin 1) (fun i => v i)))
    (Matrix.replicateCol (Fin 1) (fun i => v i))
    (Matrix.replicateRow (Fin 1) (fun i => v i))
    (tpart v • (1 : Matrix (Fin 1) (Fin 1) ℝ))

lemma tpart_pos (u : E n) : 0 < tpart u := by
  rw [tpart]; exact Real.sqrt_pos.2 (by positivity)

lemma one_le_tpart (u : E n) : 1 ≤ tpart u := by
  rw [tpart, Real.one_le_sqrt]
  linarith [sq_nonneg ‖u‖]

lemma tpart_ne_zero (u : E n) : tpart u ≠ 0 := ne_of_gt (tpart_pos u)

lemma sq_tpart (u : E n) : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := by
  rw [tpart, Real.sq_sqrt (by positivity)]

lemma pmOneMat_mulVec (y : Fin n ⊕ Fin 1 → ℝ) :
    (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)).mulVec y =
      Sum.elim (fun i => y (Sum.inl i)) (fun _ => - y (Sum.inr 0)) := by
  funext z
  rcases z with i | j
  · rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    simp [pmOneMat, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.one_apply,
      Matrix.zero_apply]
  · fin_cases j
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    simp [pmOneMat, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply,
      Matrix.zero_apply]

lemma mink_apply (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink x y = (∑ i, x (Sum.inl i) * y (Sum.inl i)) - x (Sum.inr 0) * y (Sum.inr 0) := by
  rw [mink, pmOneMat_mulVec, dotProduct, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Fin.sum_univ_one]
  ring

lemma mink_smul (r s : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink (r • x) (s • y) = r * s * mink x y := by
  rw [mink_apply, mink_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ i, r * x (Sum.inl i) * (s * y (Sum.inl i))) =
      r * s * ∑ i, x (Sum.inl i) * y (Sum.inl i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  ring

lemma inner_eq_sum (u v : E n) : inner ℝ u v = ∑ i : Fin n, u i * v i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma norm_sq_eq_sum (w : E n) : ‖w‖ ^ 2 = ∑ i : Fin n, w i * w i := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]

lemma hlift_zero : hlift (0 : E n) = etime n := by
  funext z
  rcases z with i | j
  · simp [hlift, etime]
  · fin_cases j
    simp [hlift, etime, tpart]

lemma spat_hlift (u : E n) : spat (hlift u) = u := by
  simp only [spat, hlift, Sum.elim_inl]

lemma hlift_injective : Function.Injective (hlift : E n → Fin n ⊕ Fin 1 → ℝ) := by
  intro u v h
  have h2 := congrArg spat h
  rwa [spat_hlift, spat_hlift] at h2

/-- `mink` of two chart points. -/
lemma mink_hlift (u v : E n) :
    mink (hlift u) (hlift v) = inner ℝ u v - tpart u * tpart v := by
  rw [mink_apply, inner_eq_sum]
  simp [hlift]

lemma mink_hlift_self (u : E n) : mink (hlift u) (hlift u) = -1 := by
  rw [mink_hlift, real_inner_self_eq_norm_sq]
  nlinarith [sq_tpart u]

lemma hdist_eq_cc (u v : E n) : hdist u v = Real.arcosh (cc u v) := rfl

lemma cc_comm (u v : E n) : cc u v = cc v u := by
  simp only [cc, real_inner_comm]
  ring

lemma cc_zero (u : E n) : cc u 0 = tpart u := by
  simp [cc, tpart]

lemma cc_equiv (u v : E n) : cc u v = -mink (hlift u) (hlift v) := by
  simp only [cc, mink_hlift]
  ring

lemma mink_eq_neg_cc (u v : E n) : mink (hlift u) (hlift v) = -cc u v := by
  rw [cc_equiv]; ring

/-- A point of the upper sheet is determined by its spatial part. -/
lemma hlift_spat_of_mink (y : Fin n ⊕ Fin 1 → ℝ) (hy : mink y y = -1)
    (hpos : 0 < y (Sum.inr 0)) : hlift (spat y) = y := by
  have hsum : (∑ i, y (Sum.inl i) * y (Sum.inl i)) = y (Sum.inr 0) * y (Sum.inr 0) - 1 := by
    rw [mink_apply] at hy
    linarith
  have hnorm : ‖spat y‖ ^ 2 = ∑ i, y (Sum.inl i) * y (Sum.inl i) := by
    rw [norm_sq_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rfl
  have hsqrt : y (Sum.inr 0) = tpart (spat y) := by
    have hsq : y (Sum.inr 0) ^ 2 = 1 + ‖spat y‖ ^ 2 := by rw [hnorm, hsum]; ring
    rw [tpart, ← hsq, Real.sqrt_sq (le_of_lt hpos)]
  funext z
  rcases z with i | j
  · simp [hlift, spat]
  · fin_cases j
    simp [hlift, hsqrt]

lemma transpose_pmOneMat :
    (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)).transpose = pmOneMat := by
  rw [pmOneMat, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.transpose_zero, Matrix.transpose_neg, Matrix.transpose_one]

lemma conjTranspose_eq_transpose (A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :
    A.conjTranspose = A.transpose := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]

/-- The underlying matrix of an element of `O(1)` is `J`-orthogonal. -/
lemma mat_conj (A : O1 n) :
    (mat A).transpose * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * (mat A) = pmOneMat := by
  have hA : (star (A : MatrixSum (Fin n) (Fin 1) ℝ)) * (A : MatrixSum (Fin n) (Fin 1) ℝ) = 1 :=
    (Unitary.mem_iff.mp A.2).1
  have h1 : (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * (mat A).conjTranspose *
      (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * (mat A) = 1 := hA
  rw [show (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * (mat A).conjTranspose *
      (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * (mat A) =
      (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * ((mat A).transpose *
        ((pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * (mat A))) from by
    rw [conjTranspose_eq_transpose, ← mul_assoc, ← mul_assoc]] at h1
  have h2 := congrArg (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ =>
    (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * M) h1
  simp only [mul_one] at h2
  rw [← mul_assoc, pmOneMat_mul_pmOneMat, one_mul] at h2
  simpa only [mul_assoc] using h2

/-- The second unitarity condition, in matrix form. -/
lemma mat_conj' (A : O1 n) :
    (mat A) * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * (mat A).transpose = pmOneMat := by
  have hA : (A : MatrixSum (Fin n) (Fin 1) ℝ) * (star (A : MatrixSum (Fin n) (Fin 1) ℝ)) = 1 :=
    (Unitary.mem_iff.mp A.2).2
  have h1 : (mat A) * ((pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * (mat A).conjTranspose *
      (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ))) = 1 := hA
  have h1' : (mat A) * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * (mat A).transpose *
      (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) = 1 := by
    rw [← h1, conjTranspose_eq_transpose]
    noncomm_ring
  calc (mat A) * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * (mat A).transpose
      = ((mat A) * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * (mat A).transpose *
          (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ))) *
          (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) := by
        simp [mul_assoc, pmOneMat_mul_pmOneMat]
    _ = 1 * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) := by rw [h1']
    _ = (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) := one_mul _

/-- The Minkowski form is preserved by any `J`-orthogonal matrix. -/
lemma mink_mulVec (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (hM : M.transpose * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * M = pmOneMat)
    (x y : Fin n ⊕ Fin 1 → ℝ) : mink (M.mulVec x) (M.mulVec y) = mink x y := by
  rw [mink, mink]
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_mulVec]
  rw [← mul_assoc, hM]
  rw [show Matrix.vecMul x (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) =
      (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)).mulVec x from by
    rw [← Matrix.vecMul_transpose, transpose_pmOneMat]]
  rw [dotProduct_comm]
  simpa [transpose_pmOneMat] using Matrix.dotProduct_transpose_mulVec
    (A := (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ))) (x := y) (y := x)

lemma mink_etime : mink (etime n) (etime n) = -1 := by
  rw [← hlift_zero, mink_hlift_self]

lemma mat00_ne_zero (A : O1 n) : (mat A) (Sum.inr 0) (Sum.inr 0) ≠ 0 := by
  have h := mink_mulVec (mat A) (mat_conj A) (etime n) (etime n)
  rw [mink_etime, mink_apply, etime, Matrix.mulVec_single_one] at h
  simp only [← sq, Matrix.col_apply] at h
  have h1 : (mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 =
      1 + ∑ i, (mat A) (Sum.inl i) (Sum.inr 0) ^ 2 := by linarith
  intro hc
  rw [hc] at h1
  have h2 : (0 : ℝ) ≤ ∑ i, (mat A) (Sum.inl i) (Sum.inr 0) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

lemma row_sq (A : O1 n) :
    (∑ i, (mat A) (Sum.inr 0) (Sum.inl i) ^ 2) =
      (mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 - 1 := by
  have hM : (mat A).transpose.transpose * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) *
      (mat A).transpose = pmOneMat := by
    rw [Matrix.transpose_transpose]
    exact mat_conj' A
  have h := mink_mulVec ((mat A).transpose) hM (etime n) (etime n)
  rw [mink_etime, mink_apply, etime, Matrix.mulVec_transpose, Matrix.single_vecMul] at h
  simp only [Pi.smul_apply, one_smul, Matrix.row_apply, ← sq] at h
  linarith

lemma time_mulVec_hlift (A : O1 n) (u : E n) :
    ((mat A).mulVec (hlift u)) (Sum.inr 0) =
      (mat A) (Sum.inr 0) (Sum.inr 0) * tpart u +
        inner ℝ (WithLp.toLp 2 (fun i => (mat A) (Sum.inr 0) (Sum.inl i))) u := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, inner_eq_sum]
  simp only [hlift, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one]
  ring

lemma tsign_eq_one_or (A : O1 n) : tsign A = 1 ∨ tsign A = -1 := by
  rw [tsign]; split <;> simp

lemma tsign_mul_self (A : O1 n) : tsign A * tsign A = 1 := by
  rcases tsign_eq_one_or A with h | h <;> rw [h] <;> norm_num

lemma tsign_abs (A : O1 n) : tsign A * (mat A) (Sum.inr 0) (Sum.inr 0) =
    |(mat A) (Sum.inr 0) (Sum.inr 0)| := by
  have hne := mat00_ne_zero A
  rw [tsign]
  split_ifs with h
  · rw [one_mul, abs_of_pos h]
  · rw [neg_mul, one_mul, abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hne)]

lemma row_norm_sq (A : O1 n) :
    ‖(WithLp.toLp 2 fun i => (mat A) (Sum.inr 0) (Sum.inl i) : E n)‖ ^ 2 =
      (mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 - 1 := by
  rw [norm_sq_eq_sum]
  simp only [WithLp.ofLp_toLp, ← sq]
  exact row_sq A

lemma sqrt_row_lt (A : O1 n) (u : E n) :
    Real.sqrt ((mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 - 1) * ‖u‖ <
      |(mat A) (Sum.inr 0) (Sum.inr 0)| * tpart u := by
  have hw := row_norm_sq A
  have hc1 : 1 ≤ (mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 := by
    have h : (0 : ℝ) ≤
        ‖(WithLp.toLp 2 fun i => (mat A) (Sum.inr 0) (Sum.inl i) : E n)‖ ^ 2 := sq_nonneg _
    linarith
  have ha : 0 ≤ Real.sqrt ((mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 - 1) * ‖u‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hb : 0 ≤ |(mat A) (Sum.inr 0) (Sum.inr 0)| * tpart u :=
    mul_nonneg (abs_nonneg _) (le_of_lt (tpart_pos u))
  have hsq : (Real.sqrt ((mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 - 1) * ‖u‖) ^ 2 <
      (|(mat A) (Sum.inr 0) (Sum.inr 0)| * tpart u) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), sq_abs, tpart,
      Real.sq_sqrt (by positivity)]
    nlinarith [hw, sq_nonneg ‖u‖]
  have := sq_lt_sq.mp hsq
  rwa [abs_of_nonneg ha, abs_of_nonneg hb] at this

lemma abs_inner_row_le (A : O1 n) (u : E n) :
    |inner ℝ (WithLp.toLp 2 fun i => (mat A) (Sum.inr 0) (Sum.inl i)) u| ≤
      Real.sqrt ((mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 - 1) * ‖u‖ := by
  have hcs := abs_real_inner_le_norm
    (WithLp.toLp 2 fun i => (mat A) (Sum.inr 0) (Sum.inl i) : E n) u
  have h1 : ‖(WithLp.toLp 2 fun i => (mat A) (Sum.inr 0) (Sum.inl i) : E n)‖ =
      Real.sqrt ((mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 - 1) := by
    rw [← Real.sqrt_sq (norm_nonneg _), row_norm_sq]
  rwa [h1] at hcs

/-- The time coordinate of `tsign A • A x` is positive for upper-sheet `x`. -/
lemma tsign_mul_time_mulVec_pos (A : O1 n) (u : E n) :
    0 < tsign A * ((mat A).mulVec (hlift u)) (Sum.inr 0) := by
  have hlt := sqrt_row_lt A u
  have hwt := abs_inner_row_le A u
  have htime := time_mulVec_hlift A u
  have hcne := mat00_ne_zero A
  rw [tsign]
  by_cases hcpos : 0 < (mat A) (Sum.inr 0) (Sum.inr 0)
  · rw [if_pos hcpos, one_mul]
    have h' := hlt; rw [abs_of_pos hcpos] at h'
    have h2 : inner ℝ (WithLp.toLp 2 fun i => (mat A) (Sum.inr 0) (Sum.inl i)) u ≥
        -|inner ℝ (WithLp.toLp 2 fun i => (mat A) (Sum.inr 0) (Sum.inl i)) u| := neg_abs_le _
    linarith
  · rw [if_neg hcpos, neg_mul]
    have hcneg : (mat A) (Sum.inr 0) (Sum.inr 0) < 0 :=
      lt_of_le_of_ne (not_lt.mp hcpos) hcne
    have h' := hlt; rw [abs_of_neg hcneg] at h'
    have h2 : inner ℝ (WithLp.toLp 2 fun i => (mat A) (Sum.inr 0) (Sum.inl i)) u ≤
        |inner ℝ (WithLp.toLp 2 fun i => (mat A) (Sum.inr 0) (Sum.inl i)) u| := le_abs_self _
    linarith

/-- The sheet lemma: `actO` is (up to the sign choice) the linear action of the matrix. -/
lemma hlift_actO (A : O1 n) (u : E n) :
    hlift (actO A u) = tsign A • (mat A).mulVec (hlift u) := by
  set z : Fin n ⊕ Fin 1 → ℝ := (mat A).mulVec (hlift u) with hz
  have hsign := tsign_mul_time_mulVec_pos A u
  have hpos : 0 < (tsign A • z) (Sum.inr 0) := by
    simp only [Pi.smul_apply, smul_eq_mul]; exact hsign
  have hmink : mink (tsign A • z) (tsign A • z) = -1 := by
    rw [mink_smul, mink_mulVec (mat A) (mat_conj A), mink_hlift_self, tsign_mul_self]
    ring
  have h := hlift_spat_of_mink (tsign A • z) hmink hpos
  have hsp : spat (tsign A • z) = actO A u := by
    simp only [spat, actO, hz, Pi.smul_apply, smul_eq_mul]
  rw [← hsp]
  exact h

/-- The cosh-kernel is invariant under the linear action of `O(1)`. -/
lemma cc_actO (A : O1 n) (u v : E n) : cc (actO A u) (actO A v) = cc u v := by
  rw [cc_equiv, cc_equiv, hlift_actO, hlift_actO, mink_smul, mink_mulVec (mat A) (mat_conj A),
    tsign_mul_self]
  ring

lemma of_mul_eq_replicate (a b : Fin n → ℝ) :
    (Matrix.of fun i j => a i * b j : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.replicateCol (Fin 1) a * Matrix.replicateRow (Fin 1) b := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_unique]
  simp [Matrix.of_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]

lemma of_mulVec (u v : E n) :
    (Matrix.of (fun i j => u i * u j) : Matrix (Fin n) (Fin n) ℝ).mulVec (fun i => v i) =
      fun i => u i * inner ℝ u v := by
  funext i
  simp only [Matrix.mulVec, Matrix.of_apply]
  rw [inner_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma gram_mulVec (u v : E n) :
    (gram u).mulVec (fun i => v i) = fun i => v i - (1 / (1 + ‖u‖ ^ 2)) * (u i * inner ℝ u v) := by
  rw [gram, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, of_mulVec]
  funext i
  simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

lemma gH_eq_gram (u v : E n) : gH u v = (fun i => v i) ⬝ᵥ (gram u).mulVec (fun i => v i) := by
  rw [gram_mulVec, dotProduct, gH]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← norm_sq_eq_sum]
  have h : (∑ i, v i * ((1 / (1 + ‖u‖ ^ 2)) * (u i * inner ℝ u v))) =
      (1 / (1 + ‖u‖ ^ 2)) * (inner ℝ u v) ^ 2 := by
    rw [show (∑ i, v i * ((1 / (1 + ‖u‖ ^ 2)) * (u i * inner ℝ u v))) =
        ∑ i, (1 / (1 + ‖u‖ ^ 2)) * (v i * (u i * inner ℝ u v)) from
      Finset.sum_congr rfl fun i _ => by ring]
    rw [← Finset.mul_sum]
    rw [show (∑ i, v i * (u i * inner ℝ u v)) = inner ℝ u v * inner ℝ v u from by
      rw [inner_eq_sum, inner_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring]
    rw [real_inner_comm u v]
    ring
  rw [h]
  field_simp

lemma det_gram (u : E n) : (gram u).det = (tpart u ^ 2)⁻¹ := by
  have h1 : gram u = 1 + Matrix.replicateCol (Fin 1) (fun i => u i) *
      Matrix.replicateRow (Fin 1) (fun j => -(1 / (1 + ‖u‖ ^ 2)) * u j) := by
    rw [gram, ← of_mul_eq_replicate]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, smul_eq_mul]
    ring
  have key : (1 + Matrix.replicateCol (Fin 1) (fun i => u i) *
      Matrix.replicateRow (Fin 1) (fun j => -(1 / (1 + ‖u‖ ^ 2)) * u j)).det =
      1 + (fun j => -(1 / (1 + ‖u‖ ^ 2)) * u j) ⬝ᵥ (fun i => u i) :=
    Matrix.det_one_add_replicateCol_mul_replicateRow _ _
  rw [h1, key, dotProduct]
  have h2 : (∑ i, (-(1 / (1 + ‖u‖ ^ 2)) * u i) * u i) =
      -(1 / (1 + ‖u‖ ^ 2)) * ‖u‖ ^ 2 := by
    rw [show (∑ i, (-(1 / (1 + ‖u‖ ^ 2)) * u i) * u i) =
        ∑ i, (-(1 / (1 + ‖u‖ ^ 2))) * (u i * u i) from
      Finset.sum_congr rfl fun i _ => by ring]
    rw [← Finset.mul_sum, ← norm_sq_eq_sum]
  rw [h2]
  have h3 : 1 + -(1 / (1 + ‖u‖ ^ 2)) * ‖u‖ ^ 2 = (1 + ‖u‖ ^ 2)⁻¹ := by
    rw [show (1 + ‖u‖ ^ 2)⁻¹ = 1 / (1 + ‖u‖ ^ 2) from by rw [one_div]]
    rw [show 1 + -(1 / (1 + ‖u‖ ^ 2)) * ‖u‖ ^ 2 = 1 - ‖u‖ ^ 2 / (1 + ‖u‖ ^ 2) from by ring]
    field_simp
    ring
  rw [h3, ← sq_tpart]

end Hyper

end

end Submission.Mostow
