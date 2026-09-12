import Mathlib
import Submission.RationalSqrt

/-!
# Kronecker's criterion: eventually vanishing Hankel determinants ⟹ rational

This module proves the *algebraic half* of the rationality step used in the
analytic engine of the proof of Dimitrov's theorem (Pólya–Kronecker route).

Let `a : ℕ → ℤ` be the integer sequence produced by
`Submission.PowRev.powRev_sqrt_integral` (so `a 0 = 1` and the convolution
square of `a` is the coefficient sequence of `G := R₂ * R₄`), and let
`f(X) = ∑ aₖ X⁻ᵏ` be the associated Laurent series (in the X-plane) or,
equivalently, `F(w) = ∑ aₖ wᵏ`.

Classical Kronecker criterion (the direction needed):  if the (unshifted)
Hankel determinants

    A_k := det (a_{i+j})_{0 ≤ i,j < k}

vanish for all sufficiently large `k`, then `a` satisfies a linear
recurrence with constant coefficients, and hence the power series of `a` is
rational — in the terminology of `Submission.RationalSqrt.SeriesRational`.

In the engine, Pólya's inequality gives `limsup |A_k|^{1/k²} ≤ t(K) < 1`;
since `A_k ∈ ℤ`, this forces `A_k = 0` for all large `k`, and then this
module turns that into `SeriesRational a`, feeding the already verified
chain (`RationalSqrt.square_of_rational_conv_square` and friends).

## Proof roadmap

1. **Recurrence lemma** (`seriesRational_of_recurrence`).  If there is a
   monic linear recurrence with integer coefficients
   `a (n + m) = ∑_{i < m} c i • a (n + i)` for all `n`, then
   `SeriesRational a` holds.  Indeed, put
   `q(X) := X^m − ∑_{i<m} (c i) • X^i` and `p(X) := (q • (∑ aₖ Xᵏ))`; the
   recurrence makes the coefficient of `X^{n+m}` in the product vanish for
   every `n`, so `q • (∑ aₖ Xᵏ)` is a polynomial: it suffices to define
   `p` by its (finitely many) coefficients, i.e.
   `p := ∑ k ∈ range m , ((q • F).coeff k) • X^k` (one checks that
   `(q • F).coeff k = 0` for `k ≥ m`... careful: `F := PowerSeries` with
   coefficients `a`, and `(q • F).coeff k = ∑_{i ≤ min(k, m)} q.coeff i • a (k−i)`;
   for `k ≥ m` write `k = n + m` and use the recurrence — the identity to
   prove is `(q • F).coeff (n + m) = a (n+m) − ∑_i (c i) • a (n+i) = 0`).
   Then convert the power-series identity to the coefficientwise form of
   `SeriesRational` (`Finset.sum_range`-reindexing, as in RationalSqrt).

2. **Hankel rank lemma.**  Over `ℚ`, regard the infinite Hankel matrix
   `H = (a (i+j))_{i,j}`.  Let `K` be such that all principal minors of
   size `> K` vanish.  Then, for Hankel matrices, the rank of `H` is at
   most `K` — more concretely:  with `Dₙ := det (a (i+j))_{i,j<n}`, pick
   `N` minimal with `D_{N+1} = 0` (possible; `D₁ = a 0 = 1`).  The columns
   `c_j := (a j, a (j+1), …)` satisfy a linear recurrence of order `N+1`
   with constant coefficients obtained from a nonzero vector
   `q : Fin (N+1) → ℚ` in the kernel of the `(N+1)×(N+1)` Hankel matrix
   `(a (i+j))_{i,j ≤ N}` (existence: `D_{N+1} = 0`), normalized so that
   `q (N) ≠ 0` if possible.  The vanishing of the larger determinants
   `D_{N+2}, D_{N+3}, …` is used to propagate the identity
   `∑_j q j • a (i + j) = 0` from the first rows to all rows `i`.
   [If the simple propagation is hard, an alternative classical route is:
   prove that `Σₙ aₙ Xⁿ` equals a rational function by exhibiting the
   denominator `Q(X) := ∑_j q j X^j` and showing the product `Q • F` has
   finite support using the eventual vanishing of the determinants — e.g.
   via the Frobenius/Sylvester identity for Hankel determinants, or via
   the following explicit argument:  for each `r ≥ N`, `D_r = 0` means the
   `r`-th column of the `r × r` Hankel matrix is a linear combination of
   the first `r−1` columns *with coefficients that do not depend on the row
   index* only once a fixed recurrence is found; establish the recurrence
   by induction on `n` using that `D_{n+2} = 0` forces the row `n+1`
   relation to agree with the row-`n`-derived one.]

3. **Conversion to integer recurrence.**  A recurrence over `ℚ` is cleared
   of denominators to give the integer-coefficient recurrence required by
   step 1 (or directly build integer `q ∈ ℤ[X]` and `p ∈ ℤ[X]`).

The two public theorems are `seriesRational_of_recurrence` (step 1) and
`seriesRational_of_hankel_eventually_zero` (steps 2+3).

You may add any number of helper definitions/lemmas in this file.  Do NOT
change the two public statements.  No sorries may remain in the file when
you report success.
-/

noncomputable section
open Polynomial
open scoped Polynomial
open Matrix
open scoped BigOperators

namespace Submission.Kronecker

open Submission.RationalSqrt

/-- The `k × k` Hankel determinant `det (a (i+j))_{i,j < k}` over `ℤ`. -/
def hankelDet (a : ℕ → ℤ) (k : ℕ) : ℤ :=
  (Matrix.det (Matrix.of fun i j : Fin k => a (i.val + j.val)))

/-- Hankel matrix over `ℤ`. -/
def hankelMat (a : ℕ → ℤ) (k : ℕ) : Matrix (Fin k) (Fin k) ℤ := fun i j => a (i.val + j.val)

/-! ## ℚ-linear algebra: Hankel rank / recurrence lemmas -/

@[simp] lemma finCastAdd_val {m n : ℕ} (i : Fin m) : Fin.castAdd n i = ⟨i.val, by omega⟩ := by
  apply Fin.ext
  simp [Fin.val_castAdd]

@[simp] lemma finNatAdd_val {m n : ℕ} (i : Fin m) : Fin.natAdd n i = ⟨n + i.val, by omega⟩ := by
  apply Fin.ext
  simp [Fin.val_natAdd]

/-- Canonical split `Fin (R+L+1) ≃ Fin R ⊕ Fin (L+1)` (first `R` vs the rest). -/
def finSumSplit (R L : ℕ) : Fin R ⊕ Fin (L + 1) ≃ Fin (R + L + 1) :=
  finSumFinEquiv (m := R) (n := L + 1)

/-- Hankel matrix over `ℚ`. -/
def hankelMatQ (a : ℕ → ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := fun i j => a (i.val + j.val)

/-- Hankel determinant over `ℚ`. -/
def hankelDetQ (a : ℕ → ℚ) (n : ℕ) : ℚ := (hankelMatQ a n).det

/-- Determinants commute with the integer-to-rational embedding. -/
lemma hankelDetQ_int_cast (a : ℕ → ℤ) (k : ℕ) :
    hankelDetQ (fun n => (a n : ℚ)) k = (hankelDet a k : ℚ) := by
  have hmat : hankelMatQ (fun n => (a n : ℚ)) k =
      (Int.castRingHom ℚ).mapMatrix (hankelMat a k) := by
    ext i j
    simp [hankelMatQ, hankelMat]
  calc
    hankelDetQ (fun n => (a n : ℚ)) k = (hankelMatQ (fun n => (a n : ℚ)) k).det := rfl
    _ = ((Int.castRingHom ℚ).mapMatrix (hankelMat a k)).det := by rw [hmat]
    _ = (Int.castRingHom ℚ) ((hankelMat a k).det) := (RingHom.map_det (Int.castRingHom ℚ) (hankelMat a k)).symm
    _ = (hankelDet a k : ℚ) := by
      rw [show (hankelMat a k).det = hankelDet a k by
        unfold hankelDet hankelMat
        rfl]
      rfl

/-- The `w`-defect sequence: `w m = a(R+m) − Σ_j lam j * a(m+j)`. -/
def wdef (a : ℕ → ℚ) (R : ℕ) (lam : Fin R → ℚ) (m : ℕ) : ℚ :=
  a (R + m) - ∑ j : Fin R, lam j * a (m + j.val)

/-- Row-reduced Hankel matrix: rows `s < R` stay `(a(s+c))_c`; rows `s ≥ R` become
`row_s − Σ_j lam j * row_{s−R+j}`. -/
def hankelReduced (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ) :
    Matrix (Fin (R+L+1)) (Fin (R+L+1)) ℚ :=
  fun s c => if s.val < R then a (s.val + c.val)
    else a (s.val + c.val) - ∑ j : Fin R, lam j * a (s.val - R + j.val + c.val)

lemma hReduced_top (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ) (s c : Fin (R+L+1))
    (hs : s.val < R) : hankelReduced a R L lam s c = a (s.val + c.val) := by
  simp [hankelReduced, hs]

lemma hReduced_low (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ) (s c : Fin (R+L+1))
    (hs : R ≤ s.val) :
    hankelReduced a R L lam s c =
      a (s.val + c.val) - ∑ j : Fin R, lam j * a (s.val - R + j.val + c.val) := by
  have hnot : ¬ s.val < R := by omega
  simp [hankelReduced, hnot]

/-- Shift matrix: `S_j` sends row `s` to row `s−R+j` (when `R ≤ s`), else to zero. -/
def rowShift (R N : ℕ) (j : Fin R) : Matrix (Fin N) (Fin N) ℚ :=
  fun s s' => if R ≤ s.val ∧ s'.val = s.val - R + j.val then 1 else 0

/-- Row-operation matrix `1 − Σ_j lam j • S_j` (unit lower triangular). -/
def hankelRowOp (R L : ℕ) (lam : Fin R → ℚ) : Matrix (Fin (R+L+1)) (Fin (R+L+1)) ℚ :=
  1 - ∑ j : Fin R, (lam j • rowShift R (R+L+1) j)

lemma rowShift_mul_apply_ge (a : ℕ → ℚ) (R L : ℕ) (j : Fin R) (s c : Fin (R+L+1))
    (hs : R ≤ s.val) :
    (rowShift R (R+L+1) j * hankelMatQ a (R+L+1)) s c = a (s.val - R + j.val + c.val) := by
  let t : Fin (R+L+1) := ⟨s.val - R + j.val, by omega⟩
  have hts : t.val = s.val - R + j.val := rfl
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single t]
  · simp [rowShift, hankelMatQ, hs, hts]
  · intro b hb hbt
    have hbval : b.val ≠ s.val - R + j.val := by
      intro hv
      apply hbt
      ext
      rw [hts]
      exact hv
    have hf : ¬ (R ≤ s.val ∧ b.val = s.val - R + j.val) := by
      intro hc
      exact hbval hc.2
    simp [rowShift, hankelMatQ, hf]
  · intro hmemf
    exfalso
    exact hmemf (Finset.mem_univ t)

lemma rowShift_mul_apply_lt (a : ℕ → ℚ) (R L : ℕ) (j : Fin R) (s c : Fin (R+L+1))
    (hs : s.val < R) :
    (rowShift R (R+L+1) j * hankelMatQ a (R+L+1)) s c = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro s' hs'
  have hf : ¬ (R ≤ s.val ∧ s'.val = s.val - R + j.val) := by
    intro hc
    exact (not_le_of_gt hs) hc.1
  simp [rowShift, hankelMatQ, hf]

lemma rowOp_eq (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ) :
    (hankelRowOp R L lam * hankelMatQ a (R+L+1)) =
      hankelMatQ a (R+L+1) - ∑ j : Fin R, lam j • (rowShift R (R+L+1) j * hankelMatQ a (R+L+1)) := by
  unfold hankelRowOp
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sum_mul]
  congr 1
  simp

lemma rowOp_mul_apply (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ) (s c : Fin (R+L+1)) :
    (hankelRowOp R L lam * hankelMatQ a (R+L+1)) s c =
      a (s.val + c.val) - (∑ j : Fin R, lam j * (rowShift R (R+L+1) j * hankelMatQ a (R+L+1)) s c) := by
  rw [rowOp_eq]
  simp only [Matrix.sub_apply]
  rw [Matrix.sum_apply]
  simp [smul_eq_mul, hankelMatQ]

lemma hReduced_eq_mul (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ) :
    hankelReduced a R L lam = hankelRowOp R L lam * hankelMatQ a (R+L+1) := by
  ext s c
  rw [rowOp_mul_apply]
  by_cases hs : s.val < R
  · rw [hReduced_top a R L lam s c hs]
    have hsum : (∑ j : Fin R, lam j * (rowShift R (R+L+1) j * hankelMatQ a (R+L+1)) s c) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [rowShift_mul_apply_lt a R L j s c hs]
      simp
    rw [hsum]
    simp
  · have hsge : R ≤ s.val := by omega
    rw [hReduced_low a R L lam s c hsge]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [rowShift_mul_apply_ge a R L j s c hsge]

/-- Block matrix `A = a(r+c)` (top-left). -/
def hankelA (a : ℕ → ℚ) (R : ℕ) : Matrix (Fin R) (Fin R) ℚ := hankelMatQ a R

/-- Block matrix `C = a(r+R+i)` (top-right). -/
def hankelC (a : ℕ → ℚ) (R L : ℕ) : Matrix (Fin R) (Fin (L+1)) ℚ :=
  fun r i => a (r.val + (R + i.val))

/-- Block matrix `D = w(R+r+i)` (bottom-right). -/
def hankelD (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ) : Matrix (Fin (L+1)) (Fin (L+1)) ℚ :=
  fun r i => wdef a R lam (R + r.val + i.val)

/-- Reindexed entry facts. -/
lemma reindex_apply_inl_inl {R L : ℕ} (M : Matrix (Fin (R+L+1)) (Fin (R+L+1)) ℚ) (r c : Fin R) :
    ((Matrix.reindex (finSumSplit R L).symm (finSumSplit R L).symm) M) (Sum.inl r) (Sum.inl c)
      = M ⟨r.val, by omega⟩ ⟨c.val, by omega⟩ := by
  simp [Matrix.reindex_apply, finSumSplit, finSumFinEquiv_apply_left]

lemma reindex_apply_inl_inr {R L : ℕ} (M : Matrix (Fin (R+L+1)) (Fin (R+L+1)) ℚ) (r : Fin R) (i : Fin (L+1)) :
    ((Matrix.reindex (finSumSplit R L).symm (finSumSplit R L).symm) M) (Sum.inl r) (Sum.inr i)
      = M ⟨r.val, by omega⟩ ⟨R + i.val, by omega⟩ := by
  simp [Matrix.reindex_apply, finSumSplit, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

lemma reindex_apply_inr_inl {R L : ℕ} (M : Matrix (Fin (R+L+1)) (Fin (R+L+1)) ℚ) (i : Fin (L+1)) (r : Fin R) :
    ((Matrix.reindex (finSumSplit R L).symm (finSumSplit R L).symm) M) (Sum.inr i) (Sum.inl r)
      = M ⟨R + i.val, by omega⟩ ⟨r.val, by omega⟩ := by
  simp [Matrix.reindex_apply, finSumSplit, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

lemma reindex_apply_inr_inr {R L : ℕ} (M : Matrix (Fin (R+L+1)) (Fin (R+L+1)) ℚ) (i j : Fin (L+1)) :
    ((Matrix.reindex (finSumSplit R L).symm (finSumSplit R L).symm) M) (Sum.inr i) (Sum.inr j)
      = M ⟨R + i.val, by omega⟩ ⟨R + j.val, by omega⟩ := by
  simp [Matrix.reindex_apply, finSumSplit, finSumFinEquiv_apply_right]

/-- Reduced entries: top-left. -/
lemma hRed_entry_11 (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ) (r c : Fin R) :
    hankelReduced a R L lam ⟨r.val, by omega⟩ ⟨c.val, by omega⟩ = a (r.val + c.val) := by
  rw [hReduced_top a R L lam ⟨r.val, by omega⟩ ⟨c.val, by omega⟩ (by simpa using r.isLt)]

/-- Reduced entries: top-right. -/
lemma hRed_entry_12 (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ) (r : Fin R) (i : Fin (L+1)) :
    hankelReduced a R L lam ⟨r.val, by omega⟩ ⟨R + i.val, by omega⟩ = a (r.val + (R + i.val)) := by
  rw [hReduced_top a R L lam ⟨r.val, by omega⟩ ⟨R + i.val, by omega⟩ (by simpa using r.isLt)]

/-- Reduced entries: bottom-left is zero (uses the vanishing defect hypothesis). -/
lemma hRed_entry_21 (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ)
    (hw : ∀ m : ℕ, m < R + L → wdef a R lam m = 0) (r' : Fin (L+1)) (c : Fin R) :
    hankelReduced a R L lam ⟨R + r'.val, by omega⟩ ⟨c.val, by omega⟩ = 0 := by
  have hr' : r'.val < L + 1 := r'.isLt
  have hc' : c.val < R := c.isLt
  rw [hReduced_low a R L lam ⟨R + r'.val, by omega⟩ ⟨c.val, by omega⟩ (by simp)]
  simp
  have hw' : wdef a R lam (r'.val + c.val) = 0 := hw (r'.val + c.val) (by omega)
  rw [wdef] at hw'
  have hsumeq : (∑ j : Fin R, lam j * a (r'.val + j.val + c.val)) =
      (∑ j : Fin R, lam j * a (r'.val + c.val + j.val)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [show r'.val + j.val + c.val = r'.val + c.val + j.val by omega]
  have hR : R + (r'.val + c.val) = R + r'.val + c.val := by omega
  rw [hR] at hw'
  have hw'' : a (R + r'.val + c.val) = ∑ j : Fin R, lam j * a (r'.val + c.val + j.val) := by
    linarith
  rw [hw'']
  rw [hsumeq]
  simp

lemma hRed_entry_22 (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ) (r' i : Fin (L+1)) :
    hankelReduced a R L lam ⟨R + r'.val, by omega⟩ ⟨R + i.val, by omega⟩ =
      wdef a R lam (R + r'.val + i.val) := by
  rw [hReduced_low a R L lam ⟨R + r'.val, by omega⟩ ⟨R + i.val, by omega⟩ (by simp)]
  simp
  rw [wdef]
  rw [show R + r'.val + (R + i.val) = R + (R + r'.val + i.val) by omega]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [show r'.val + j.val + (R + i.val) = R + r'.val + i.val + j.val by omega]

lemma hReduced_fromBlocks (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ)
    (hw : ∀ m : ℕ, m < R + L → wdef a R lam m = 0) :
    Matrix.reindex (finSumSplit R L).symm (finSumSplit R L).symm (hankelReduced a R L lam) =
      Matrix.fromBlocks (hankelA a R) (hankelC a R L)
        (0 : Matrix (Fin (L+1)) (Fin R) ℚ) (hankelD a R L lam) := by
  ext x y
  cases x with
  | inl r =>
    cases y with
    | inl c =>
      rw [reindex_apply_inl_inl]
      rw [hRed_entry_11 a R L lam r c]
      rfl
    | inr i =>
      rw [reindex_apply_inl_inr]
      rw [hRed_entry_12 a R L lam r i]
      rfl
  | inr r' =>
    cases y with
    | inl c =>
      rw [reindex_apply_inr_inl]
      rw [hRed_entry_21 a R L lam hw r' c]
      rfl
    | inr i =>
      rw [reindex_apply_inr_inr]
      rw [hRed_entry_22 a R L lam r' i]
      rfl

/-- Entries of `hankelRowOp` strictly above the diagonal vanish. -/
lemma rowOp_apply_above (R L : ℕ) (lam : Fin R → ℚ) (s t : Fin (R+L+1))
    (hst : s.val < t.val) : (hankelRowOp R L lam) s t = 0 := by
  have hst' : s ≠ t := by
    intro h
    have : s.val = t.val := congrArg Fin.val h
    omega
  have hSj : ∀ j : Fin R, rowShift R (R+L+1) j s t = 0 := by
    intro j
    unfold rowShift
    by_cases hs : R ≤ s.val
    · have hlt : s.val - R + j.val < t.val := by omega
      have hne : t.val ≠ s.val - R + j.val := by omega
      simp [hs, hne]
    · simp [hs]
  unfold hankelRowOp
  simp only [Matrix.sub_apply, Matrix.one_apply]
  rw [Matrix.sum_apply]
  simp [smul_eq_mul]
  simp [hst', hSj]

/-- Diagonal entries of `hankelRowOp` are `1`. -/
lemma rowOp_apply_diag (R L : ℕ) (lam : Fin R → ℚ) (s : Fin (R+L+1)) :
    (hankelRowOp R L lam) s s = 1 := by
  have hSj : ∀ j : Fin R, rowShift R (R+L+1) j s s = 0 := by
    intro j
    unfold rowShift
    by_cases hs : R ≤ s.val
    · have hne : s.val ≠ s.val - R + j.val := by omega
      simp [hs, hne]
    · simp [hs]
  unfold hankelRowOp
  simp only [Matrix.sub_apply, Matrix.one_apply]
  rw [Matrix.sum_apply]
  simp [smul_eq_mul]
  simp [hSj]

/-- The row-operation matrix is unit lower triangular, so it has determinant `1`. -/
lemma rowOp_det_one (R L : ℕ) (lam : Fin R → ℚ) : (hankelRowOp R L lam).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [rowOp_apply_diag]
  · intro s t hst
    exact rowOp_apply_above R L lam s t (by exact hst)

/-- Block determinant: `det M = det A · det D` (when the defect vanishes below `R+L`). -/
lemma hReduced_det (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ)
    (hw : ∀ m : ℕ, m < R + L → wdef a R lam m = 0) :
    (hankelReduced a R L lam).det = (hankelA a R).det * (hankelD a R L lam).det := by
  have hFB := hReduced_fromBlocks a R L lam hw
  calc
    (hankelReduced a R L lam).det
        = (Matrix.reindex (finSumSplit R L).symm (finSumSplit R L).symm (hankelReduced a R L lam)).det := by
          exact (Matrix.det_reindex_self (finSumSplit R L).symm (hankelReduced a R L lam)).symm
    _ = (Matrix.fromBlocks (hankelA a R) (hankelC a R L)
          (0 : Matrix (Fin (L+1)) (Fin R) ℚ) (hankelD a R L lam)).det := by rw [hFB]
    _ = (hankelA a R).det * (hankelD a R L lam).det := by
          exact Matrix.det_fromBlocks_zero₂₁ (hankelA a R) (hankelC a R L) (hankelD a R L lam)

/-- Row reduction does not change the determinant. -/
lemma hReduced_det_hankel (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ) :
    (hankelReduced a R L lam).det = (hankelMatQ a (R+L+1)).det := by
  rw [hReduced_eq_mul, Matrix.det_mul, rowOp_det_one]
  simp

/-- The determinant of the leading `R` block. -/
lemma hankelA_det (a : ℕ → ℚ) (R : ℕ) : (hankelA a R).det = hankelDetQ a R := rfl

/-- Row reversal on `Fin (L+1)` (maps `i` to `L − i`). -/
def finRev (L : ℕ) : Equiv.Perm (Fin (L+1)) where
  toFun i := ⟨L - i.val, by omega⟩
  invFun i := ⟨L - i.val, by omega⟩
  left_inv i := by
    ext
    simp
    have hi : i.val < L + 1 := i.isLt
    omega
  right_inv i := by
    ext
    simp
    have hi : i.val < L + 1 := i.isLt
    omega

/-- Anti-triangular Hankel matrix (zero top-left corner) has determinant `± w(R+L)^(L+1)`;
more precisely its row-reversal `F` (with `F r i = w(R + (L−r) + i)`) is upper triangular
with constant diagonal `w (R+L)`. -/
lemma antiTri_det (R L : ℕ) (w : ℕ → ℚ) (hz : ∀ m : ℕ, m < R + L → w m = 0) :
    let F : Matrix (Fin (L+1)) (Fin (L+1)) ℚ := fun r i => w (R + (L - r.val) + i.val)
    F.det = w (R + L) ^ (L + 1) := by
  intro F
  have hFtri : F.IsUpperTriangular := by
    intro i j hij
    have hc : j.val < i.val := hij
    simp [F]
    apply hz
    omega
  rw [Matrix.det_of_isUpperTriangular hFtri]
  calc
    (∏ r : Fin (L+1), F r r) = ∏ r : Fin (L+1), w (R + L) := by
      apply Finset.prod_congr rfl
      intro r hr
      simp [F]
      congr 1
      have hr' : r.val < L + 1 := r.isLt
      omega
    _ = w (R + L) ^ (L + 1) := by simp

/-- If `D` has entries `w(R+r+i)` (with `w` vanishing below `R+L`) and `det D = 0`,
then `w (R+L) = 0`. -/
lemma antiTri_zero (R L : ℕ) (w : ℕ → ℚ) (hz : ∀ m : ℕ, m < R + L → w m = 0)
    (D : Matrix (Fin (L+1)) (Fin (L+1)) ℚ) (hD : ∀ r i, D r i = w (R + r.val + i.val))
    (hdet : D.det = 0) : w (R + L) = 0 := by
  let F : Matrix (Fin (L+1)) (Fin (L+1)) ℚ := fun r i => w (R + (L - r.val) + i.val)
  have hF : F.det = w (R + L) ^ (L + 1) := by
    exact antiTri_det (R := R) (L := L) (w := w) hz
  have hsub : F = D.submatrix (finRev L) id := by
    ext r i
    rw [Matrix.submatrix_apply, hD]
    simp [F, finRev]
  have hperm : (D.submatrix (finRev L) id).det =
      ((Equiv.Perm.sign (finRev L) : ℤ) : ℚ) * D.det := by
    exact Matrix.det_permute (finRev L) D
  have hFdet0 : F.det = 0 := by
    rw [hsub, hperm, hdet]
    norm_num
  have hpow : w (R + L) ^ (L + 1) = 0 := by
    rw [← hF]
    exact hFdet0
  exact (pow_eq_zero_iff (a := w (R + L)) (n := L + 1) (by omega)).mp hpow


/-- **Propagation step.** If the defect `w m` vanishes for all `m < R+L` and
`det` of the `(R+L+1)`-Hankel matrix is zero while the `R`-Hankel matrix is nonsingular,
then the defect also vanishes at `m = R+L`. -/
lemma hankel_step (a : ℕ → ℚ) (R L : ℕ) (lam : Fin R → ℚ)
    (hB : hankelDetQ a R ≠ 0) (hD : hankelDetQ a (R + L + 1) = 0)
    (hw : ∀ m : ℕ, m < R + L → wdef a R lam m = 0) :
    wdef a R lam (R + L) = 0 := by
  let D : Matrix (Fin (L+1)) (Fin (L+1)) ℚ := hankelD a R L lam
  have hred_det_block : (hankelReduced a R L lam).det = (hankelA a R).det * D.det := by
    simpa [D] using hReduced_det a R L lam hw
  have hred_det_h : (hankelReduced a R L lam).det = hankelDetQ a (R + L + 1) := by
    simpa [hankelDetQ] using hReduced_det_hankel a R L lam
  have hprod : (hankelA a R).det * D.det = 0 := by
    rw [← hred_det_block, hred_det_h, hD]
  have hD0 : D.det = 0 := by
    exact (mul_eq_zero.mp hprod).resolve_left (by simpa [hankelA_det] using hB)
  exact antiTri_zero (R := R) (L := L) (w := wdef a R lam) hw D (by intro r i; rfl) hD0

/-- **Kronecker's rank lemma over `ℚ`.** If the `R`-Hankel determinant is nonzero and all
larger Hankel determinants vanish, the sequence satisfies a monic linear recurrence
of order `R` with rational coefficients. -/
theorem rationalRec (a : ℕ → ℚ) (R : ℕ) (hRpos : 0 < R)
    (hB : hankelDetQ a R ≠ 0) (hD : ∀ n : ℕ, R < n → hankelDetQ a n = 0) :
    ∃ lam : Fin R → ℚ, ∀ m : ℕ, a (R + m) = ∑ j : Fin R, lam j * a (m + j.val) := by
  let A : Matrix (Fin R) (Fin R) ℚ := hankelMatQ a R
  let tail : Fin R → ℚ := fun i => a (R + i.val)
  have hAunit : IsUnit A.det := by
    dsimp [A]
    rw [show (hankelMatQ a R).det = hankelDetQ a R by rfl]
    exact isUnit_iff_ne_zero.mpr hB
  let lam : Fin R → ℚ := (A⁻¹).mulVec tail
  have hAinv : A.mulVec lam = tail := by
    dsimp [lam]
    calc
      A.mulVec ((A⁻¹).mulVec tail) = (A * A⁻¹).mulVec tail := by
        rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin R) (Fin R) ℚ).mulVec tail := by
        rw [Matrix.mul_nonsing_inv A hAunit]
      _ = tail := by simp
  have hwbase : ∀ m : ℕ, m < R → wdef a R lam m = 0 := by
    intro m hm
    let r : Fin R := ⟨m, hm⟩
    have hprod : (A.mulVec lam) r = ∑ c : Fin R, lam c * a (m + c.val) := by
      dsimp [A]
      rw [Matrix.mulVec]
      apply Finset.sum_congr rfl
      intro c hc
      rw [mul_comm]
      rfl
    have hAt : (A.mulVec lam) r = a (R + m) := by
      rw [hAinv]
    have heq : a (R + m) = ∑ c : Fin R, lam c * a (m + c.val) := by
      rw [← hprod]
      exact hAt.symm
    dsimp [wdef]
    rw [heq]
    simp
  have hmain : ∀ L : ℕ, ∀ m : ℕ, m < R + L → wdef a R lam m = 0 := by
    intro L
    induction L with
    | zero =>
        intro m hm
        exact hwbase m (by omega)
    | succ L ih =>
        intro m hm
        by_cases hmL : m < R + L
        · exact ih m hmL
        · have hm' : m = R + L := by omega
          subst m
          exact hankel_step a R L lam hB (hD (R + L + 1) (by omega)) (fun m' hm' => ih m' hm')
  refine ⟨lam, ?_⟩
  intro m
  have hwm : wdef a R lam m = 0 := by
    by_cases hm : m < R
    · exact hwbase m hm
    · have hmain' := hmain (m - R + 1) m
      exact hmain' (by omega)
  dsimp [wdef] at hwm
  linarith

/-! ## ℤ-side: forward integer recurrence ⇒ `SeriesRational` -/

lemma polySum_coeff {ι : Type*} [Fintype ι] {R : Type*} [Semiring R] (f : ι → R[X]) (n : ℕ) :
    (∑ i, f i).coeff n = ∑ i, (f i).coeff n := by
  change (Polynomial.lcoeff R n) (∑ i, f i) = ∑ i, (f i).coeff n
  exact map_sum (Polynomial.lcoeff R n) f Finset.univ

/-- Reversed coefficient polynomial: `coeff t = qc (m − t)` for `t ≤ m`. -/
def qpoly (m : ℕ) (qc : Fin (m+1) → ℤ) : ℤ[X] :=
  ∑ j : Fin (m+1), C (qc j) * X ^ (m - j.val)

lemma qpoly_coeff_le (m : ℕ) (qc : Fin (m+1) → ℤ) (t : ℕ) (ht : t ≤ m) :
    (qpoly m qc).coeff t = qc ⟨m - t, by omega⟩ := by
  unfold qpoly
  rw [polySum_coeff]
  have hsum : (∑ j : Fin (m+1), (C (qc j) * X ^ (m - j.val)).coeff t)
      = (∑ j : Fin (m+1), qc j * (if t = m - j.val then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [hsum]
  let j0 : Fin (m+1) := ⟨m - t, by omega⟩
  rw [Finset.sum_eq_single j0]
  · have hm : m - j0.val = t := by
      dsimp [j0]
      omega
    simp [hm]
    apply congrArg qc
    ext
    dsimp [j0]
  · intro b hb hbne
    have hval : b.val ≠ m - t := by
      intro hv
      apply hbne
      ext
      exact hv
    have hif : t ≠ m - b.val := by
      intro hmm
      apply hval
      omega
    simp [hif]
  · intro hnot
    exfalso
    exact hnot (Finset.mem_univ j0)

lemma qpoly_coeff_gt (m : ℕ) (qc : Fin (m+1) → ℤ) (t : ℕ) (ht : m < t) :
    (qpoly m qc).coeff t = 0 := by
  unfold qpoly
  rw [polySum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hif : t ≠ m - j.val := by omega
  simp [hif]

lemma qpoly_ne_zero (m : ℕ) (qc : Fin (m+1) → ℤ) (hq : qc ≠ 0) : qpoly m qc ≠ 0 := by
  intro h0
  apply hq
  funext j
  have hc : (qpoly m qc).coeff (m - j.val) = 0 := by simp [h0]
  have hcl := qpoly_coeff_le m qc (m - j.val) (by omega)
  have hc' : qc ⟨m - (m - j.val), by omega⟩ = 0 := by
    rw [← hcl]
    exact hc
  have hj : ⟨m - (m - j.val), by omega⟩ = j := by
    ext
    simp
    have hj' : j.val < m + 1 := j.isLt
    omega
  rw [hj] at hc'
  exact hc'

lemma drop_ge (m n : ℕ) (f : ℕ → ℤ) (hf : ∀ i, m < i → f i = 0) :
    (∑ i ∈ Finset.range (m + n + 1), f i) = (∑ i ∈ Finset.range (m + 1), f i) := by
  symm
  apply Finset.sum_subset
  · intro i hi
    have hi' : i < m + 1 := Finset.mem_range.mp hi
    exact Finset.mem_range.mpr (by omega)
  · intro i hi hi2
    have hi2' : ¬ i < m + 1 := by
      intro h
      apply hi2
      exact Finset.mem_range.mpr h
    exact hf i (by omega)

def conv (a : ℕ → ℤ) (q : ℤ[X]) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1), q.coeff i * a (k - i)

def finMirror (m : ℕ) : Fin (m+1) ≃ Fin (m+1) where
  toFun i := ⟨m - i.val, by omega⟩
  invFun i := ⟨m - i.val, by omega⟩
  left_inv i := by
    ext; simp; have hi : i.val < m + 1 := i.isLt; omega
  right_inv i := by
    ext; simp; have hi : i.val < m + 1 := i.isLt; omega

lemma finMirror_val (m : ℕ) (i : Fin (m+1)) : (finMirror m i).val = m - i.val := by
  simp [finMirror]

lemma conv_eq_hrec (a : ℕ → ℤ) (m n : ℕ) (qc : Fin (m+1) → ℤ) :
    conv a (qpoly m qc) (m + n)
      = ∑ i : Fin (m+1), qc i * a (n + i.val) := by
  calc
    conv a (qpoly m qc) (m + n)
        = ∑ i ∈ Finset.range (m + 1), (qpoly m qc).coeff i * a (m + n - i) := by
          unfold conv
          exact drop_ge m n (fun i => (qpoly m qc).coeff i * a (m + n - i))
            (by intro i hi; rw [qpoly_coeff_gt m qc i hi]; simp)
    _ = ∑ i : Fin (m+1), (qpoly m qc).coeff i.val * a (m + n - i.val) := by
          exact (Fin.sum_univ_eq_sum_range
            (fun i => (qpoly m qc).coeff i * a (m + n - i)) (m+1)).symm
    _ = ∑ i : Fin (m+1), qc ⟨m - i.val, by omega⟩ * a (m + n - i.val) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [qpoly_coeff_le m qc i.val (by have h := i.isLt; omega)]
    _ = ∑ i : Fin (m+1), qc (finMirror m i) * a (n + (finMirror m i).val) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hmv : (finMirror m i).val = m - i.val := finMirror_val m i
          have hq : qc ⟨m - i.val, by omega⟩ = qc (finMirror m i) := by
            apply congrArg qc
            ext
            simp [finMirror]
          have ha : a (m + n - i.val) = a (n + (finMirror m i).val) := by
            rw [hmv]
            congr 1
            have hi' : i.val < m + 1 := i.isLt
            omega
          rw [hq, ha]
    _ = ∑ i : Fin (m+1), qc i * a (n + i.val) := by
          exact Equiv.sum_comp (finMirror m) (fun j => qc j * a (n + j.val))

lemma pCoeff_lt (c : ℕ → ℤ) (m t : ℕ) (ht : t < m) :
    (∑ k ∈ Finset.range m, (c k) • (X : ℤ[X]) ^ k).coeff t = c t := by
  have hdist : (∑ k ∈ Finset.range m, (c k) • (X : ℤ[X]) ^ k).coeff t
      = ∑ k ∈ Finset.range m, ((c k) • (X : ℤ[X]) ^ k).coeff t := by
    change (Polynomial.lcoeff ℤ t) (∑ k ∈ Finset.range m, (c k) • (X : ℤ[X]) ^ k)
        = ∑ k ∈ Finset.range m, ((c k) • (X : ℤ[X]) ^ k).coeff t
    exact map_sum (Polynomial.lcoeff ℤ t) (fun k => (c k) • (X : ℤ[X]) ^ k) (Finset.range m)
  rw [hdist]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b hb hbne
    have hbt : t ≠ b := by
      intro h
      exact hbne h.symm
    simp [hbt]
  · intro hnot
    exfalso
    exact hnot (Finset.mem_range.mpr ht)

lemma pCoeff_ge (c : ℕ → ℤ) (m t : ℕ) (ht : m ≤ t) :
    (∑ k ∈ Finset.range m, (c k) • (X : ℤ[X]) ^ k).coeff t = 0 := by
  have hdist : (∑ k ∈ Finset.range m, (c k) • (X : ℤ[X]) ^ k).coeff t
      = ∑ k ∈ Finset.range m, ((c k) • (X : ℤ[X]) ^ k).coeff t := by
    change (Polynomial.lcoeff ℤ t) (∑ k ∈ Finset.range m, (c k) • (X : ℤ[X]) ^ k)
        = ∑ k ∈ Finset.range m, ((c k) • (X : ℤ[X]) ^ k).coeff t
    exact map_sum (Polynomial.lcoeff ℤ t) (fun k => (c k) • (X : ℤ[X]) ^ k) (Finset.range m)
  rw [hdist]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' : k < m := Finset.mem_range.mp hk
  have hkt : t ≠ k := by omega
  simp [hkt]

/-- An integer forward linear recurrence (with arbitrary integer coefficients, not all
zero) makes the generating power series rational. -/
lemma SeriesRational_of_forward_fin (a : ℕ → ℤ) (m : ℕ) (qc : Fin (m+1) → ℤ)
    (hq : qc ≠ 0) (hrec : ∀ n : ℕ, (∑ j : Fin (m+1), qc j * a (n + j.val)) = 0) :
    SeriesRational a := by
  let q : ℤ[X] := qpoly m qc
  have hqne : q ≠ 0 := by
    dsimp [q]
    exact qpoly_ne_zero m qc hq
  have hconv_ge : ∀ k : ℕ, m ≤ k → conv a q k = 0 := by
    intro k hk
    let n : ℕ := k - m
    have hk' : k = m + n := by omega
    rw [hk']
    dsimp [q]
    rw [conv_eq_hrec a m n qc]
    exact hrec n
  let p : ℤ[X] := ∑ k ∈ Finset.range m, (conv a q k) • (X : ℤ[X]) ^ k
  have hconv_p : ∀ k : ℕ, conv a q k = p.coeff k := by
    intro k
    by_cases hk : k < m
    · dsimp [p]
      rw [pCoeff_lt (fun t => conv a q t) m k hk]
    · have hge : m ≤ k := by omega
      have hc0 : conv a q k = 0 := hconv_ge k hge
      dsimp [p]
      rw [pCoeff_ge (fun t => conv a q t) m k hge]
      exact hc0
  refine ⟨p, q, hqne, ?_⟩
  intro k
  change conv a q k = p.coeff k
  exact hconv_p k

/-! ## Integer clearing of the rational recurrence -/

lemma rat_eq_num_div_den (q : ℚ) : q = (q.num : ℚ) / (q.den : ℚ) := by
  have h : q * (q.den : ℚ) = (q.num : ℚ) := by simp
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  field_simp [hd]
  exact h

lemma clear_coeff (q : ℚ) (N : ℕ) (hdvd : q.den ∣ N) :
    (((q.num * (N / q.den : ℕ) : ℤ) : ℚ)) = (N : ℚ) * q := by
  rcases hdvd with ⟨c, hc⟩
  have hdiv : N / q.den = c := by
    rw [hc]
    exact Nat.mul_div_right c (Rat.den_pos q)
  rw [hdiv]
  rw [hc]
  norm_num
  have h2 : (q.den : ℚ) * q = (q.num : ℚ) := by simp
  rw [show (q.den : ℚ) * (c : ℚ) * q = (c : ℚ) * ((q.den : ℚ) * q) by ring]
  rw [h2]
  ring

/-- Clear denominators: a rational recurrence with integer sequence values yields an
integer forward recurrence (nonzero coefficient array). -/
lemma int_recurrence_of_rat (a : ℕ → ℤ) (R : ℕ) (lam : Fin R → ℚ)
    (hrec : ∀ m : ℕ, (a (R + m) : ℚ) = ∑ j : Fin R, lam j * (a (m + j.val) : ℚ)) :
    ∃ qc : Fin (R+1) → ℤ, qc ≠ 0 ∧
      ∀ m : ℕ, (∑ j : Fin (R+1), qc j * a (m + j.val)) = 0 := by
  let N : ℕ := ∏ j : Fin R, (lam j).den
  let γ : Fin R → ℤ := fun j => (lam j).num * ((N / (lam j).den : ℕ) : ℤ)
  have hNpos : 0 < N := by
    dsimp [N]
    exact Finset.prod_pos (fun j hj => Rat.den_pos (lam j))
  have hdvd : ∀ j : Fin R, (lam j).den ∣ N := by
    intro j
    dsimp [N]
    exact Finset.dvd_prod_of_mem (fun j : Fin R => (lam j).den) (Finset.mem_univ j)
  have hclear : ∀ j : Fin R, (γ j : ℚ) = (N : ℚ) * lam j := by
    intro j
    dsimp [γ]
    exact clear_coeff (lam j) N (hdvd j)
  have hN : ∀ m : ℕ, (N : ℚ) * (a (R + m) : ℚ) =
      ∑ j : Fin R, (γ j : ℚ) * (a (m + j.val) : ℚ) := by
    intro m
    calc
      (N : ℚ) * (a (R + m) : ℚ) = (N : ℚ) * (∑ j : Fin R, lam j * (a (m + j.val) : ℚ)) := by
        rw [hrec m]
      _ = ∑ j : Fin R, (N : ℚ) * (lam j * (a (m + j.val) : ℚ)) := by
        simp [Finset.mul_sum]
      _ = ∑ j : Fin R, ((N : ℚ) * lam j) * (a (m + j.val) : ℚ) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ j : Fin R, (γ j : ℚ) * (a (m + j.val) : ℚ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hclear j]
  let qc : Fin (R+1) → ℤ :=
    fun j => if h : j.val < R then -γ ⟨j.val, h⟩ else (N : ℤ)
  have hqclast : qc (Fin.last R) = (N : ℤ) := by
    dsimp [qc]
    simp [Fin.val_last]
  have hqcast : ∀ j : Fin R, qc (j.castSucc) = -γ j := by
    intro j
    dsimp [qc]
    have hj : j.castSucc.val < R := by
      simp
    simp [hj]
  have hqc_ne : qc ≠ 0 := by
    intro h0
    have : (qc (Fin.last R) : ℚ) ≠ 0 := by
      rw [hqclast]
      norm_num
      exact_mod_cast hNpos.ne'
    exact this (by rw [h0]; simp)
  -- integer version of hN
  have hNZ : ∀ m : ℕ, (N : ℤ) * a (R + m) = ∑ j : Fin R, γ j * a (m + j.val) := by
    intro m
    apply (Int.cast_injective (α := ℚ))
    norm_num
    exact hN m
  refine ⟨qc, hqc_ne, ?_⟩
  intro m
  rw [Fin.sum_univ_castSucc]
  have hsum : (∑ j : Fin R, qc j.castSucc * a (m + j.castSucc.val))
      = - ∑ j : Fin R, γ j * a (m + j.val) := by
    calc
      (∑ j : Fin R, qc j.castSucc * a (m + j.castSucc.val))
          = ∑ j : Fin R, - (γ j * a (m + j.val)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hqcast j]
            rw [show (m + j.castSucc.val) = m + j.val by
              rw [Fin.val_castSucc]]
            ring
      _ = - ∑ j : Fin R, γ j * a (m + j.val) := by
            rw [← Finset.sum_neg_distrib]
  have hlast : qc (Fin.last R) * a (m + (Fin.last R).val) = (N : ℤ) * a (R + m) := by
    rw [hqclast]
    rw [show (Fin.last R).val = R by rfl]
    rw [show m + R = R + m by omega]
  rw [hsum, hlast]
  rw [hNZ m]
  ring

/-- A sequence satisfying a monic constant-coefficient recurrence is rational. -/
theorem seriesRational_of_recurrence (a : ℕ → ℤ) (m : ℕ) (hm : 0 < m)
    (c : Fin m → ℤ)
    (hrec : ∀ n : ℕ, a (n + m) = ∑ i : Fin m, c i * a (n + i.val)) :
    SeriesRational a := by
  let qc : Fin (m+1) → ℤ := fun j => if h : j.val < m then -c ⟨j.val, h⟩ else 1
  have hq : qc ≠ 0 := by
    intro h0
    have hq1 : qc (Fin.last m) = 1 := by
      dsimp [qc]
      simp [Fin.val_last]
    have h01 : (1 : ℤ) = 0 := by
      rw [← hq1, h0]
      simp
    norm_num at h01
  have hrec' : ∀ n : ℕ, (∑ j : Fin (m+1), qc j * a (n + j.val)) = 0 := by
    intro n
    rw [Fin.sum_univ_castSucc]
    have h1 : (∑ j : Fin m, qc j.castSucc * a (n + j.castSucc.val)) = -∑ j : Fin m, c j * a (n + j.val) := by
      calc
        (∑ j : Fin m, qc j.castSucc * a (n + j.castSucc.val))
            = ∑ j : Fin m, - (c j * a (n + j.val)) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hqj : qc (j.castSucc) = -c j := by
                dsimp [qc]
                have hjv : j.castSucc.val < m := by
                  rw [Fin.val_castSucc]
                  exact j.isLt
                simp [hjv]
              rw [hqj]
              rw [show (n + j.castSucc.val) = n + j.val by
                rw [Fin.val_castSucc]]
              ring
        _ = -∑ j : Fin m, c j * a (n + j.val) := by
              rw [← Finset.sum_neg_distrib]
    have h2 : qc (Fin.last m) * a (n + (Fin.last m).val) = a (n + m) := by
      have hqm : qc (Fin.last m) = 1 := by
        dsimp [qc]
        simp [Fin.val_last]
      rw [hqm]
      rw [show (Fin.last m).val = m by rfl]
      simp
    rw [h1, h2]
    rw [hrec n]
    ring
  exact SeriesRational_of_forward_fin a m qc hq hrec'

/-- **Kronecker's criterion** (the direction used in the engine): if all
sufficiently large Hankel determinants of `a` vanish (`a 0 = 1`), then the
power series of `a` is rational. -/
theorem seriesRational_of_hankel_eventually_zero (a : ℕ → ℤ) (ha0 : a 0 = 1)
    (h : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → hankelDet a k = 0) :
    SeriesRational a := by
  let aQ : ℕ → ℚ := fun n => (a n : ℚ)
  rcases h with ⟨K, hK⟩
  have hKQ : ∀ k : ℕ, K ≤ k → hankelDetQ aQ k = 0 := by
    intro k hk
    rw [hankelDetQ_int_cast a k]
    rw [hK k hk]
    rfl
  have hK2 : 2 ≤ K := by
    by_contra hnot
    have hK1 : K ≤ 1 := by omega
    have hD1 : hankelDetQ aQ 1 = 0 := hKQ 1 hK1
    have hD1' : hankelDetQ aQ 1 = 1 := by
      simp [hankelDetQ, hankelMatQ, aQ, ha0]
    have : (0 : ℚ) = 1 := by rw [← hD1, hD1']
    norm_num at this
  let P : ℕ → Prop := fun n => hankelDetQ aQ n ≠ 0
  let R : ℕ := Nat.findGreatest P (K - 1)
  have hP1 : P 1 := by
    dsimp [P]
    rw [show hankelDetQ aQ 1 = 1 by simp [hankelDetQ, hankelMatQ, aQ, ha0]]
    norm_num
  have h1le : 1 ≤ K - 1 := by omega
  have hPR : P R := by
    dsimp [R]
    exact Nat.findGreatest_spec h1le hP1
  have hRle : R ≤ K - 1 := by
    have hc := (Nat.findGreatest_eq_iff (P := P) (k := K - 1) (m := R)).mp rfl
    exact hc.1
  have hRmax : ∀ n : ℕ, R < n → n ≤ K - 1 → ¬ P n := by
    have hc := (Nat.findGreatest_eq_iff (P := P) (k := K - 1) (m := R)).mp rfl
    exact hc.2.2
  have hRpos : 0 < R := by
    by_contra h
    have hR0 : R = 0 := by omega
    have hnP : ¬ P 1 := hRmax 1 (by rw [hR0]; omega) h1le
    exact hnP hP1
  have hDQ : ∀ n : ℕ, R < n → hankelDetQ aQ n = 0 := by
    intro n hn
    by_cases hnK : K ≤ n
    · exact hKQ n hnK
    · have hnle : n ≤ K - 1 := by omega
      have hnp : ¬ P n := hRmax n hn hnle
      by_contra hneq
      exact hnp hneq
  rcases rationalRec aQ R hRpos hPR hDQ with ⟨lam, hlam⟩
  rcases int_recurrence_of_rat a R lam (by
    intro m
    simpa [aQ] using hlam m) with ⟨qc, hqc0, hqc⟩
  exact SeriesRational_of_forward_fin a R qc hqc0 hqc

end Submission.Kronecker

end
