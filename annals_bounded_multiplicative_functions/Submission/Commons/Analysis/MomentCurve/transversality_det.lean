import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Submission.Commons.Algebra.Nat.descFactorial_mul_add_pow
import Submission.Commons.LinearAlgebra.Matrix.det_eq_det_submatrix_inr_of_cols_eq_stdBasis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

/-!
# Transversality of the moment curve

This file proves the determinant lower bound for the mixed wedge of derivatives of the
moment curve `Γ(t) = (t, t², …, tᵏ)`, needed for Vinogradov's mean value theorem
(Guo–Li–Yung–Zorin-Kranich, *A short proof of ℓ² decoupling for the moment curve*,
arXiv:1912.09798, Lemma 3.5).
-/

namespace Commons.Analysis.MomentCurve

/-- The `a`-th derivative of the moment curve `t ↦ (t, t², …, tᵏ)` at `θ`, as a vector:
its `j`-th coordinate is the falling factorial `(j+1)^↓a` times `θ^(j+1-a)`. -/
noncomputable def gam (k : ℕ) (θ : ℝ) (a : ℕ) : Fin k → ℝ :=
  fun j => ((j.val + 1).descFactorial a : ℝ) * θ ^ (j.val + 1 - a)

@[simp] lemma gam_apply (k : ℕ) (θ : ℝ) (a : ℕ) (j : Fin k) :
    gam k θ a j = ((j.val + 1).descFactorial a : ℝ) * θ ^ (j.val + 1 - a) := rfl

/-- The `a`-th derivative vector vanishes once `a > k`. -/
lemma gam_eq_zero (k : ℕ) {a : ℕ} (ha : k < a) (θ : ℝ) : gam k θ a = 0 := by
  funext j
  have hj : j.val + 1 ≤ k := by have := j.isLt; omega
  have h0 : (j.val + 1).descFactorial a = 0 :=
    Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
  simp [gam_apply, h0]

/-- Taylor expansion of the moment-curve derivative vectors around `x`:
`Γ^{(a)}(x+h) = ∑_{e=0}^{k} h^e/e! · Γ^{(a+e)}(x)`. -/
lemma gam_add (k : ℕ) (x h : ℝ) (a : ℕ) :
    gam k (x + h) a
      = ∑ e ∈ Finset.range (k + 1), (h ^ e / (e.factorial : ℝ)) • gam k x (a + e) := by
  funext j
  rw [Finset.sum_apply]
  simp only [gam_apply, Pi.smul_apply, smul_eq_mul]
  rw [Commons.Algebra.Nat.descFactorial_mul_add_pow (j.val + 1) a x h]
  have hj : j.val + 1 ≤ k := by have := j.isLt; omega
  trans ∑ e ∈ Finset.range (j.val + 1 - a + 1),
      h ^ e / (e.factorial : ℝ) * (((j.val + 1).descFactorial (a + e) : ℝ) * x ^ (j.val + 1 - (a + e)))
  · refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mem_range] at he
    have h1 : j.val + 1 - (a + e) = j.val + 1 - a - e := by omega
    rw [h1]; ring
  · refine Finset.sum_subset (Finset.range_mono ?_) ?_
    · omega
    · intro e he hes
      rw [Finset.mem_range] at he hes
      have h0 : ((j.val + 1).descFactorial (a + e) : ℝ) = 0 := by
        rw [Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt]
        omega
      rw [h0]; ring


/-- The basis matrix `[Γ^{(1)}(x), …, Γ^{(k)}(x)]` of the ambient space. -/
noncomputable def Bmat (k : ℕ) (x : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of (fun (j c : Fin k) => gam k x (c.val + 1) j)

/-- Coefficient matrix expressing the columns of `Mmat k l x y` in the basis `Bmat k x`:
the `(c,i)` entry is the coefficient of `Γ^{(c+1)}(x)`.  For `i ≥ l` it is obtained from the
Taylor expansion of `Γ^{(i-l+1)}(y)` around `x`. -/
noncomputable def Qmat (k l : ℕ) (h : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of (fun (c i : Fin k) =>
    if i.val < l then (if c.val = i.val then (1 : ℝ) else 0)
    else ∑ e ∈ Finset.range (k + 1),
      (if c.val + 1 = (i.val - l + 1) + e then h ^ e / (e.factorial : ℝ) else 0))

/-- The matrix whose columns are `Γ^{(1)}(x), …, Γ^{(l)}(x), Γ^{(1)}(y), …, Γ^{(k-l)}(y)`. -/
noncomputable def Mmat (k l : ℕ) (x y : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of (fun (j i : Fin k) =>
    if i.val < l then gam k x (i.val + 1) j else gam k y (i.val - l + 1) j)

/-- The only nonzero term of the sum `∑_c [c+1 = m] Γ^{(c+1)}(x)`. -/
lemma sum_ite_gam (k : ℕ) (x : ℝ) (j : Fin k) {m : ℕ} (hm : 1 ≤ m) :
    (∑ c : Fin k, if c.val + 1 = m then gam k x (c.val + 1) j else 0) = gam k x m j := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if a + 1 = m then gam k x (a + 1) j else 0) k]
  rcases lt_or_ge (m - 1) k with hlt | hge
  · rw [Finset.sum_eq_single (m - 1)]
    · rw [if_pos (by omega), Nat.sub_add_cancel hm]
    · intro b _ hb
      by_cases h : b + 1 = m
      · omega
      · simp [h]
    · intro h; exact absurd (Finset.mem_range.mpr hlt) h
  · have hmk : k < m := by omega
    rw [Finset.sum_eq_zero]
    · exact (congrFun (gam_eq_zero k hmk x) j).symm
    · intro b hb
      rw [Finset.mem_range] at hb
      by_cases h : b + 1 = m
      · omega
      · simp [h]

/-- The determinant of the basis matrix `[Γ^{(1)}(x), …, Γ^{(k)}(x)]` is `∏ i!`. -/
lemma det_Bmat (k : ℕ) (x : ℝ) :
    (Bmat k x).det = ∏ i : Fin k, (((i.val + 1).factorial : ℕ) : ℝ) := by
  rw [Matrix.det_of_isLowerTriangular _ ?_]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Bmat, Matrix.of_apply, gam_apply, Nat.sub_self, pow_zero, mul_one,
      Nat.descFactorial_self]
  · intro i j hij
    have hij' : i.val < j.val := hij
    show Bmat k x i j = 0
    rw [Bmat, Matrix.of_apply, gam_apply]
    have h0 : (i.val + 1).descFactorial (j.val + 1) = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [h0, Nat.cast_zero, zero_mul]

/-- The key matrix identity: `M = B · Q`, i.e. the Taylor expansion of the second block of
columns of `Mmat` in the basis `Bmat`. -/
lemma Mmat_eq_mul (k l : ℕ) (x y : ℝ) :
    Mmat k l x y = Bmat k x * Qmat k l (y - x) := by
  ext j i
  rw [Mmat, Matrix.of_apply, Matrix.mul_apply]
  by_cases hi : i.val < l
  · rw [if_pos hi, Finset.sum_eq_single i]
    · simp [Bmat, Qmat, hi]
    · intro b _ hb
      have hb' : b.val ≠ i.val := fun hh => hb (Fin.ext hh)
      simp [Bmat, Qmat, hi, hb']
    · intro hnot; exact absurd (Finset.mem_univ i) hnot
  · rw [if_neg hi]
    have hd1 : 1 ≤ i.val - l + 1 := by omega
    have hgam := congrFun (gam_add k x (y - x) (i.val - l + 1)) j
    rw [show x + (y - x) = y by ring, Finset.sum_apply] at hgam
    simp only [Pi.smul_apply, smul_eq_mul] at hgam
    rw [hgam]
    have hT : (∑ c : Fin k, Bmat k x j c * Qmat k l (y - x) c i)
        = ∑ e ∈ Finset.range (k + 1),
            ((y - x) ^ e / (e.factorial : ℝ)) * gam k x ((i.val - l + 1) + e) j := by
      simp only [Bmat, Matrix.of_apply]
      rw [show (∑ c : Fin k, gam k x (c.val + 1) j * Qmat k l (y - x) c i)
          = ∑ c : Fin k, ∑ e ∈ Finset.range (k + 1),
              (if c.val + 1 = (i.val - l + 1) + e
                then gam k x (c.val + 1) j * ((y - x) ^ e / (e.factorial : ℝ)) else 0) from by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Qmat, Matrix.of_apply, if_neg hi, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        by_cases hP : c.val + 1 = (i.val - l + 1) + e <;> simp [hP]]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      trans (∑ c : Fin k,
          (if c.val + 1 = (i.val - l + 1) + e then gam k x (c.val + 1) j else 0))
          * ((y - x) ^ e / (e.factorial : ℝ))
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases hP : c.val + 1 = (i.val - l + 1) + e <;> simp [hP]
      · rw [sum_ite_gam k x j (m := (i.val - l + 1) + e) (by omega)]
        ring
    rw [hT]


/-- The reindexing of `Fin k` as `Fin l ⊕ Fin (k-l)` given `l ≤ k`. -/
noncomputable def splitEquiv (k l : ℕ) (hl : l ≤ k) : Fin l ⊕ Fin (k - l) ≃ Fin k where
  toFun x := match x with
    | Sum.inl i => ⟨i.val, by omega⟩
    | Sum.inr j => ⟨l + j.val, by omega⟩
  invFun n := if h : n.val < l then Sum.inl ⟨n.val, h⟩
    else Sum.inr ⟨n.val - l, by have := n.isLt; omega⟩
  left_inv := by
    rintro (i | j)
    · dsimp only
      rw [dif_pos i.isLt]
    · dsimp only
      rw [dif_neg (show ¬ l + j.val < l by omega)]
      rw [Sum.inr.injEq]
      exact Fin.ext (by simp)
  right_inv := by
    intro n
    dsimp only
    by_cases h : n.val < l
    · rw [dif_pos h]
    · rw [dif_neg h]
      dsimp only
      congr 1
      omega

@[simp] lemma splitEquiv_inl (k l : ℕ) (hl : l ≤ k) (i : Fin l) :
    (splitEquiv k l hl) (Sum.inl i) = ⟨i.val, by omega⟩ := rfl

@[simp] lemma splitEquiv_inr (k l : ℕ) (hl : l ≤ k) (j : Fin (k - l)) :
    (splitEquiv k l hl) (Sum.inr j) = ⟨l + j.val, by omega⟩ := rfl

/-- For `i` with `l ≤ i.val` the entries of `Qmat` have the simple Taylor form. -/
lemma Qmat_apply (k l : ℕ) (u : ℝ) (c i : Fin k) (hi : l ≤ i.val) :
    Qmat k l u c i
      = (if i.val - l + 1 ≤ c.val + 1 then
          u ^ (c.val + 1 - (i.val - l + 1))
            / (((c.val + 1 - (i.val - l + 1))).factorial : ℝ) else 0) := by
  have hni : ¬ i.val < l := by omega
  rw [Qmat, Matrix.of_apply, if_neg hni]
  by_cases hd : i.val - l + 1 ≤ c.val + 1
  · rw [if_pos hd]
    have he : c.val + 1 - (i.val - l + 1) ∈ Finset.range (k + 1) := by
      rw [Finset.mem_range]; omega
    rw [Finset.sum_eq_single (c.val + 1 - (i.val - l + 1)) _ (fun hnot => absurd he hnot)]
    · rw [if_pos (by omega)]
    · intro b _ hb
      by_cases hbc : c.val + 1 = i.val - l + 1 + b
      · omega
      · simp [hbc]
  · rw [if_neg hd, Finset.sum_eq_zero]
    intro b _ 
    by_cases hbc : c.val + 1 = i.val - l + 1 + b
    · omega
    · simp [hbc]

/-- The bottom-right `(k-l) × (k-l)` block of `Qmat`: a Toeplitz matrix in the powers of `u`. -/
noncomputable def Cmat (k l : ℕ) (u : ℝ) : Matrix (Fin (k - l)) (Fin (k - l)) ℝ :=
  Matrix.of (fun i j => if j.val ≤ l + i.val then
    u ^ (l + i.val - j.val) / (((l + i.val - j.val)).factorial : ℝ) else 0)

/-- The constant part of `Cmat`: reciprocal factorials. -/
noncomputable def Rmat (k l : ℕ) : Matrix (Fin (k - l)) (Fin (k - l)) ℝ :=
  Matrix.of (fun i j => if j.val ≤ l + i.val then
    1 / (((l + i.val - j.val)).factorial : ℝ) else 0)

/-- The determinant of `Qmat` is (up to sign) the determinant of its bottom-right block. -/
lemma abs_det_Qmat (k l : ℕ) (hl : l ≤ k) (u : ℝ) :
    |(Qmat k l u).det| = |(Cmat k l u).det| := by
  set A := (Qmat k l u).submatrix (splitEquiv k l hl) (splitEquiv k l hl) with hA
  have hdetA : A.det = (Qmat k l u).det := Matrix.det_submatrix_equiv_self _ _
  have hblock : A.det = (A.submatrix Sum.inr Sum.inr).det := by
    refine Commons.LinearAlgebra.Matrix.det_eq_det_submatrix_inr_of_cols_eq_stdBasis A ?_
    intro i c
    rcases c with c | c
    · simp only [hA, Matrix.submatrix_apply]
      simp only [splitEquiv_inl, Qmat, Matrix.of_apply, if_pos i.isLt]
      by_cases hci : c.val = i.val
      · have hce : c = i := Fin.ext hci
        subst hce; simp
      · have hne : ¬ (c = i) := fun hh => hci (by rw [hh])
        have hne' : ¬ ((Sum.inl c : Fin l ⊕ Fin (k - l)) = Sum.inl i) := by
          rw [Sum.inl.injEq]; exact hne
        simp [hci, hne']
    · simp only [hA, Matrix.submatrix_apply]
      simp only [splitEquiv_inr, splitEquiv_inl, Qmat, Matrix.of_apply, if_pos i.isLt]
      have hne : ¬ ((l + c.val : ℕ) = i.val) := by omega
      have hne' : ¬ ((Sum.inr c : Fin l ⊕ Fin (k - l)) = Sum.inl i) := by simp
      simp [hne, hne']
  have hC : (A.submatrix Sum.inr Sum.inr) = Cmat k l u := by
    ext i j
    have h1 : (A.submatrix Sum.inr Sum.inr) i j
        = Qmat k l u (Fin.mk (l + i.val) (by omega)) (Fin.mk (l + j.val) (by omega)) := by
      simp [hA, Matrix.submatrix_apply]
    rw [h1, Qmat_apply k l u _ _ (by simp), Cmat, Matrix.of_apply]
    simp only [Fin.val_mk]
    by_cases hji : j.val ≤ l + i.val
    · rw [if_pos hji, if_pos (by omega)]
      have e2 : l + j.val - l + 1 = j.val + 1 := by omega
      have e1 : (l + i.val) + 1 - (j.val + 1) = l + i.val - j.val := by omega
      rw [e2, e1]
    · rw [if_neg hji, if_neg (by omega)]
  rw [← hdetA, hblock, hC]


/-- Scaling identity for `Cmat`: multiplying the `j`-th column by `u^j` turns the
`h`-powers `u^(l+i-j)` into the single factor `u^(l+i)` of row `i`. -/
lemma Cmat_mul_diagonal (k l : ℕ) (u : ℝ) :
    Cmat k l u * Matrix.diagonal (fun j : Fin (k - l) => u ^ j.val)
      = Matrix.diagonal (fun i : Fin (k - l) => u ^ (l + i.val)) * Rmat k l := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Cmat, Rmat, Matrix.of_apply]
  by_cases hji : j.val ≤ l + i.val
  · rw [if_pos hji, if_pos hji, div_mul_eq_mul_div, ← pow_add,
      show l + i.val - j.val + j.val = l + i.val by omega, mul_one_div]
  · rw [if_neg hji, if_neg hji, zero_mul, mul_zero]

/-- The determinant of `Cmat` is `|u|^(l(k-l))` times the determinant of the constant
matrix `Rmat`. -/
lemma abs_det_Cmat (k l : ℕ) (hl : 1 ≤ l) (u : ℝ) :
    |(Cmat k l u).det| = |u| ^ (l * (k - l)) * |(Rmat k l).det| := by
  rcases eq_or_ne u 0 with rfl | hu
  · rcases Nat.eq_zero_or_pos (k - l) with hm | hm
    · haveI : IsEmpty (Fin (k - l)) := by rw [hm]; exact Fin.isEmpty
      rw [Matrix.det_isEmpty, Matrix.det_isEmpty, abs_one, hm, mul_zero, abs_zero, pow_zero,
        one_mul]
    · have hzero : (Cmat k l 0).det = 0 := by
        refine Matrix.det_eq_zero_of_column_eq_zero ⟨0, hm⟩ fun i => ?_
        rw [Cmat, Matrix.of_apply, if_pos (Nat.zero_le _), Nat.sub_zero]
        rw [zero_pow (by omega : l + i.val ≠ 0)]
        simp
      have hp : l * (k - l) ≠ 0 :=
        (Nat.mul_pos (by omega) hm).ne'
      rw [hzero, abs_zero, zero_pow hp, zero_mul]
  · have h := congrArg Matrix.det (Cmat_mul_diagonal k l u)
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_mul, Matrix.det_diagonal] at h
    rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum] at h
    have hsum : (∑ i : Fin (k - l), (l + i.val))
        = l * (k - l) + ∑ j : Fin (k - l), j.val := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul]
      ring
    rw [hsum, pow_add] at h
    have hne : u ^ (∑ j : Fin (k - l), j.val) ≠ 0 := pow_ne_zero _ hu
    have key : (Cmat k l u).det = u ^ (l * (k - l)) * (Rmat k l).det := by
      refine mul_right_cancel₀ hne ?_
      rw [h]; ring
    rw [key, abs_mul, abs_pow]

/-- The constant matrix `Rmat` is nonsingular. -/
lemma det_Rmat_ne_zero (k l : ℕ) : (Rmat k l).det ≠ 0 := by
  have hdiag : Matrix.diagonal (fun i : Fin (k - l) => (((l + i.val).factorial : ℕ) : ℝ))
        * Rmat k l
      = Matrix.of (fun i j : Fin (k - l) => ((l + i.val).descFactorial j.val : ℝ)) := by
    ext i j
    rw [Matrix.diagonal_mul, Rmat, Matrix.of_apply, Matrix.of_apply]
    by_cases hji : j.val ≤ l + i.val
    · rw [if_pos hji, mul_one_div]
      have h1 : ((l + i.val).descFactorial j.val : ℝ)
            * (((l + i.val - j.val).factorial : ℕ) : ℝ)
          = (((l + i.val).factorial : ℕ) : ℝ) := by
        rw [mul_comm]
        exact_mod_cast Nat.factorial_mul_descFactorial hji
      have h2 : (((l + i.val - j.val).factorial : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      rw [div_eq_iff h2]
      exact h1.symm
    · rw [if_neg hji, mul_zero]
      have h0 : (l + i.val).descFactorial j.val = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [h0, Nat.cast_zero]
  have hP : (Matrix.of (fun i j : Fin (k - l) => ((l + i.val).descFactorial j.val : ℝ))).det
      ≠ 0 := by
    have hconv : Matrix.of (fun i j : Fin (k - l) => ((l + i.val).descFactorial j.val : ℝ))
        = Matrix.of (fun i j : Fin (k - l) =>
            (descPochhammer ℝ j.val).eval ((l + i.val : ℕ) : ℝ)) := by
      ext i j
      rw [Matrix.of_apply, Matrix.of_apply]
      exact (descPochhammer_eval_eq_descFactorial ℝ (l + i.val) j.val).symm
    rw [hconv, ← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (v := fun i : Fin (k - l) => ((l + i.val : ℕ) : ℝ))
      (p := fun j : Fin (k - l) => descPochhammer ℝ j.val)
      (fun i => descPochhammer_natDegree ℝ i.val)
      (fun i => monic_descPochhammer ℝ i.val)]
    rw [Matrix.det_vandermonde, Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [Finset.mem_Ioi] at hj
    refine sub_ne_zero.mpr ?_
    intro hcon
    have : l + j.val = l + i.val := by exact_mod_cast hcon
    omega
  intro hzero
  have hh := congrArg Matrix.det hdiag
  rw [Matrix.det_mul, Matrix.det_diagonal, hzero, mul_zero] at hh
  exact hP hh.symm


/-- **Transversality of the moment curve** (Guo–Li–Yung–Zorin-Kranich,
arXiv:1912.09798, Lemma 3.5): the `(l, k-l)` mixed wedge of derivatives of the
moment curve `Γ(t) = (t, t², …, tᵏ)` is bounded below by a constant times
`|ξ₁-ξ₂|^{l(k-l)}`.  Concretely, for `1 ≤ l ≤ k` and `ξ₁, ξ₂ ∈ [0,1]`,
`|det M| ≥ c · |ξ₁ - ξ₂|^{l(k-l)}` with `c > 0` depending only on `k` and `l`,
where `M : Matrix (Fin k) (Fin k) ℝ` has columns
`γ^{(1)}(ξ₁), …, γ^{(l)}(ξ₁), γ^{(1)}(ξ₂), …, γ^{(k-l)}(ξ₂)`, the `j`-th
coordinate of `γ^{(i)}(t)` being the falling factorial `(j+1)^↓i · t^{j+1-i}`
(so `M j i` is that expression evaluated at `t = ξ₁` for `i.val < l` and at
`t = ξ₂` for `i.val ≥ l`, with `i` replaced by `i.val - l + 1` in the second
case).  In fact the determinant equals
`(± ∏_{i=1}^k i!) · c_{k,l} · (ξ₂-ξ₁)^{l(k-l)}`; only the lower bound is
needed. -/
theorem transversality_det (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ₁ ξ₂ : ℝ, 0 ≤ ξ₁ → ξ₁ ≤ 1 → 0 ≤ ξ₂ → ξ₂ ≤ 1 →
      c * |ξ₁ - ξ₂| ^ (l * (k - l))
        ≤ |(Matrix.of (fun (j i : Fin k) =>
            if i.val < l
              then ((j.val + 1).descFactorial (i.val + 1) : ℝ)
                * ξ₁ ^ (j.val + 1 - (i.val + 1))
              else ((j.val + 1).descFactorial (i.val - l + 1) : ℝ)
                * ξ₂ ^ (j.val + 1 - (i.val - l + 1)))).det| := by
  set c : ℝ := (∏ i : Fin k, (((i.val + 1).factorial : ℕ) : ℝ)) * |(Rmat k l).det| with hc
  refine ⟨c, ?_, ?_⟩
  · have h1 : (0 : ℝ) < ∏ i : Fin k, (((i.val + 1).factorial : ℕ) : ℝ) :=
      Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos (i.val + 1)
    have h2 : (0 : ℝ) < |(Rmat k l).det| := abs_pos.mpr (det_Rmat_ne_zero k l)
    rw [hc]; positivity
  · intro ξ₁ ξ₂ h1 h2 h3 h4
    show c * |ξ₁ - ξ₂| ^ (l * (k - l)) ≤ |(Mmat k l ξ₁ ξ₂).det|
    have hB : |(Bmat k ξ₁).det| = ∏ i : Fin k, (((i.val + 1).factorial : ℕ) : ℝ) := by
      rw [det_Bmat k ξ₁, abs_of_pos]
      exact Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos (i.val + 1)
    have hM : |(Mmat k l ξ₁ ξ₂).det| = c * |ξ₁ - ξ₂| ^ (l * (k - l)) := by
      rw [Mmat_eq_mul k l ξ₁ ξ₂, Matrix.det_mul, abs_mul, hB,
        abs_det_Qmat k l hlk (ξ₂ - ξ₁), abs_det_Cmat k l hl (ξ₂ - ξ₁),
        abs_sub_comm ξ₂ ξ₁, hc]
      ring
    rw [hM]

end Commons.Analysis.MomentCurve