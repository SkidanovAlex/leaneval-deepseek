import Mathlib
import Submission.Work.BMF.br_path

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset Matrix

/-!
# The bicycle count: Sidorenko's inequality for two even cycles joined by an edge

Route (following Matomäki–Radziwiłł–Tao, §4):

* `T = 1ᵀA^{2j+1}1` is the total weight of walks of length `2j+1`; by the Cauchy–Schwarz
  inequality applied to the configurations "middle edge with a half-walk hanging at each end",
  `T² ≤ (n²S)·L`, where `L = ∑ A_{ij}(A^{2j})_{ii}(A^{2j})_{jj}` is the bicycle count and
  `S = 1ᵀA1`.
* By the Mulholland–Smith / Blakley–Roy inequality (Sidorenko's property for paths),
  `T ≥ S^{2j+1}/n^{2j}`.
* Hence `L ≥ S^{2j+1}/n^{2j+2}`.
-/

/-- Powers of a symmetric matrix are symmetric, in `apply` form. -/
lemma pow_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hsym : A.transpose = A) (j : ℕ)
    (i k : Fin n) : (A ^ j) k i = (A ^ j) i k := by
  have h : (A ^ j).transpose = A ^ j := by rw [Matrix.transpose_pow, hsym]
  have h2 := congrFun (congrFun h i) k
  simpa [Matrix.transpose_apply] using h2

/-- Diagonal entries of an even power of a symmetric matrix are sums of squares. -/
lemma diag_pow_two_mul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hsym : A.transpose = A)
    (j : ℕ) (i : Fin n) : (A ^ (2 * j)) i i = ∑ k, ((A ^ j) i k) ^ 2 := by
  have hpow : A ^ (2 * j) = A ^ j * A ^ j := by
    rw [show (2 : ℕ) * j = j + j by omega, pow_add]
  rw [hpow, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pow_symm hsym j i k]
  ring

/-- Fold a nested four-fold sum into a sum over the product index `((i,j'),(k,l))`. -/
lemma sum4_prod {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j', ∑ k, ∑ l, F i j' k l)
      = ∑ Q : (Fin n × Fin n) × (Fin n × Fin n), F Q.1.1 Q.1.2 Q.2.1 Q.2.2 := by
  have h1 : (∑ i, ∑ j', ∑ k, ∑ l, F i j' k l)
      = ∑ p : Fin n × Fin n, (∑ k, ∑ l, F p.1 p.2 k l) :=
    (Fintype.sum_prod_type
      (f := fun p : Fin n × Fin n => ∑ k, ∑ l, F p.1 p.2 k l)).symm
  rw [h1]
  have h2 : (∑ p : Fin n × Fin n, (∑ k, ∑ l, F p.1 p.2 k l))
      = ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, F p.1 p.2 q.1 q.2 := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact (Fintype.sum_prod_type (f := fun q : Fin n × Fin n => F p.1 p.2 q.1 q.2)).symm
  rw [h2]
  exact (Fintype.sum_prod_type
    (f := fun Q : (Fin n × Fin n) × (Fin n × Fin n) => F Q.1.1 Q.1.2 Q.2.1 Q.2.2)).symm

/-- Swap the two `Fin n × Fin n` components of a product-index sum. -/
lemma sum_prod_swap {n : ℕ} (G : (Fin n × Fin n) × (Fin n × Fin n) → ℝ) :
    (∑ Q : (Fin n × Fin n) × (Fin n × Fin n), G (Q.2, Q.1)) = ∑ Q, G Q :=
  Equiv.sum_comp (Equiv.prodComm (Fin n × Fin n) (Fin n × Fin n)) G

/-- `1ᵀA^{2j+1}1`, written as a sum over "middle edge with a half-walk hanging at each end". -/
lemma walk_odd_prod {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hsym : A.transpose = A) (j : ℕ) :
    (∑ a, ∑ b, (A ^ (2 * j + 1)) a b) =
      ∑ Q : (Fin n × Fin n) × (Fin n × Fin n),
        A Q.1.1 Q.1.2 * (A ^ j) Q.1.1 Q.2.1 * (A ^ j) Q.1.2 Q.2.2 := by
  have h1 : (∑ a, ∑ b, (A ^ (2 * j + 1)) a b)
      = ∑ a, ∑ b, ∑ i, ∑ j', (A ^ j) a i * A i j' * (A ^ j) j' b := by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    have hpow : A ^ (2 * j + 1) = A ^ j * (A * A ^ j) := by
      rw [show 2 * j + 1 = j + (1 + j) by omega, pow_add, pow_add, pow_one]
    rw [hpow, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j' _ => by ring)
  rw [h1]
  set K : (Fin n × Fin n) × (Fin n × Fin n) → ℝ :=
    fun Q => A Q.1.1 Q.1.2 * (A ^ j) Q.1.1 Q.2.1 * (A ^ j) Q.1.2 Q.2.2 with hK
  have h2 : (∑ a, ∑ b, ∑ i, ∑ j', (A ^ j) a i * A i j' * (A ^ j) j' b)
      = ∑ Q : (Fin n × Fin n) × (Fin n × Fin n),
          (A ^ j) Q.1.1 Q.2.1 * A Q.2.1 Q.2.2 * (A ^ j) Q.2.2 Q.1.2 :=
    sum4_prod (F := fun a b i j' => (A ^ j) a i * A i j' * (A ^ j) j' b)
  rw [h2]
  have h3 : (∑ Q : (Fin n × Fin n) × (Fin n × Fin n),
        (A ^ j) Q.1.1 Q.2.1 * A Q.2.1 Q.2.2 * (A ^ j) Q.2.2 Q.1.2)
      = ∑ Q : (Fin n × Fin n) × (Fin n × Fin n), K (Q.2, Q.1) := by
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    simp only [hK]
    rw [pow_symm hsym j Q.1.1 Q.2.1]
    ring
  rw [h3]
  exact sum_prod_swap K

/-- The bicycle count, written over "middle edge with a half-walk hanging at each end". -/
lemma bicycle_prod {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hsym : A.transpose = A) (j : ℕ) :
    (∑ i, ∑ j', A i j' * ((A ^ (2 * j)) i i) * ((A ^ (2 * j)) j' j'))
      = ∑ Q : (Fin n × Fin n) × (Fin n × Fin n),
          A Q.1.1 Q.1.2 * ((A ^ j) Q.1.1 Q.2.1) ^ 2 * ((A ^ j) Q.1.2 Q.2.2) ^ 2 := by
  have h1 : (∑ i, ∑ j', A i j' * ((A ^ (2 * j)) i i) * ((A ^ (2 * j)) j' j'))
      = ∑ i, ∑ j', A i j' * (∑ a, ((A ^ j) i a) ^ 2) * (∑ b, ((A ^ j) j' b) ^ 2) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j' _ => ?_))
    rw [diag_pow_two_mul hsym j i, diag_pow_two_mul hsym j j']
  rw [h1]
  have h2 : (∑ i, ∑ j', A i j' * (∑ a, ((A ^ j) i a) ^ 2) * (∑ b, ((A ^ j) j' b) ^ 2))
      = ∑ i, ∑ j', ∑ a, ∑ b, A i j' * ((A ^ j) i a) ^ 2 * ((A ^ j) j' b) ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j' _ => ?_))
    rw [Finset.mul_sum]
    have hper : ∀ b : Fin n, (A i j' * (∑ a, ((A ^ j) i a) ^ 2)) * ((A ^ j) j' b) ^ 2
        = ∑ a, A i j' * ((A ^ j) i a) ^ 2 * ((A ^ j) j' b) ^ 2 := by
      intro b
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun b _ => hper b), Finset.sum_comm]
  rw [h2]
  exact sum4_prod (F := fun i j' a b => A i j' * ((A ^ j) i a) ^ 2 * ((A ^ j) j' b) ^ 2)

/-- The number of "shapes" (middle edge plus the two free outer vertices). -/
lemma shapes_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} :
    (∑ Q : (Fin n × Fin n) × (Fin n × Fin n), A Q.1.1 Q.1.2)
      = (n : ℝ) ^ 2 * ∑ i, ∑ j, A i j := by
  have h1 : (∑ Q : (Fin n × Fin n) × (Fin n × Fin n), A Q.1.1 Q.1.2)
      = ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, A p.1 p.2 :=
    Fintype.sum_prod_type
      (f := fun Q : (Fin n × Fin n) × (Fin n × Fin n) => A Q.1.1 Q.1.2)
  rw [h1]
  have h2 : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, A p.1 p.2)
      = ∑ p : Fin n × Fin n, (n : ℝ) ^ 2 * A p.1 p.2 := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [h2]
  have h3 : (∑ p : Fin n × Fin n, A p.1 p.2) = ∑ i, ∑ j, A i j :=
    Fintype.sum_prod_type (f := fun p : Fin n × Fin n => A p.1 p.2)
  rw [← Finset.mul_sum, h3]

/-- Cauchy–Schwarz step: `(1ᵀA^{2j+1}1)² ≤ (n²·1ᵀA1) · (bicycle count)`. -/
lemma bike_cs {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hsym : A.transpose = A)
    (hnn : ∀ i j, 0 ≤ A i j) (j : ℕ) :
    (∑ a, ∑ b, (A ^ (2 * j + 1)) a b) ^ 2 ≤
      (∑ i, ∑ j', A i j' * ((A ^ (2 * j)) i i) * ((A ^ (2 * j)) j' j')) *
        ((n : ℝ) ^ 2 * ∑ i, ∑ j', A i j') := by
  rw [walk_odd_prod hsym j, bicycle_prod hsym j, ← shapes_eq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n)))
    (fun Q => Real.sqrt (A Q.1.1 Q.1.2) * (A ^ j) Q.1.1 Q.2.1 * (A ^ j) Q.1.2 Q.2.2)
    (fun Q => Real.sqrt (A Q.1.1 Q.1.2))
  have h1 : (∑ Q : (Fin n × Fin n) × (Fin n × Fin n),
        Real.sqrt (A Q.1.1 Q.1.2) * (A ^ j) Q.1.1 Q.2.1 * (A ^ j) Q.1.2 Q.2.2
          * Real.sqrt (A Q.1.1 Q.1.2))
      = ∑ Q : (Fin n × Fin n) × (Fin n × Fin n),
          A Q.1.1 Q.1.2 * (A ^ j) Q.1.1 Q.2.1 * (A ^ j) Q.1.2 Q.2.2 := by
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    have h0 : 0 ≤ A Q.1.1 Q.1.2 := hnn _ _
    have hs : Real.sqrt (A Q.1.1 Q.1.2) * Real.sqrt (A Q.1.1 Q.1.2) = A Q.1.1 Q.1.2 := by
      rw [← sq, Real.sq_sqrt h0]
    calc Real.sqrt (A Q.1.1 Q.1.2) * (A ^ j) Q.1.1 Q.2.1 * (A ^ j) Q.1.2 Q.2.2
            * Real.sqrt (A Q.1.1 Q.1.2)
        = (Real.sqrt (A Q.1.1 Q.1.2) * Real.sqrt (A Q.1.1 Q.1.2))
            * (A ^ j) Q.1.1 Q.2.1 * (A ^ j) Q.1.2 Q.2.2 := by ring
      _ = A Q.1.1 Q.1.2 * (A ^ j) Q.1.1 Q.2.1 * (A ^ j) Q.1.2 Q.2.2 := by rw [hs]
  have h2 : (∑ Q : (Fin n × Fin n) × (Fin n × Fin n),
        (Real.sqrt (A Q.1.1 Q.1.2) * (A ^ j) Q.1.1 Q.2.1 * (A ^ j) Q.1.2 Q.2.2) ^ 2)
      = ∑ Q : (Fin n × Fin n) × (Fin n × Fin n),
          A Q.1.1 Q.1.2 * ((A ^ j) Q.1.1 Q.2.1) ^ 2 * ((A ^ j) Q.1.2 Q.2.2) ^ 2 := by
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    have h0 : 0 ≤ A Q.1.1 Q.1.2 := hnn _ _
    rw [mul_pow, mul_pow, Real.sq_sqrt h0]
  have h3 : (∑ Q : (Fin n × Fin n) × (Fin n × Fin n), (Real.sqrt (A Q.1.1 Q.1.2)) ^ 2)
      = ∑ Q : (Fin n × Fin n) × (Fin n × Fin n), A Q.1.1 Q.1.2 := by
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [Real.sq_sqrt (hnn _ _)]
  rw [h1, h2, h3] at hcs
  exact hcs

/-- Nonnegative matrices have nonnegative powers (entrywise). -/
lemma matrix_pow_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hnn : ∀ i j, 0 ≤ A i j) :
    ∀ m i j, 0 ≤ (A ^ m) i j := by
  intro m
  induction m with
  | zero =>
    intro i j
    rw [pow_zero]
    by_cases h : i = j
    · rw [h, Matrix.one_apply_eq]; norm_num
    · rw [Matrix.one_apply_ne h]
  | succ m ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun t _ => mul_nonneg (ih i t) (hnn t j))

/-- **Bicycle count** (the Blakley–Roy inequality for symmetric nonnegative matrices, in the
form used in MRT §4).  For a symmetric matrix `A` with nonnegative entries and `ℓ` even, the
sum over ordered adjacent pairs of the products of the two diagonal entries of `A ^ ℓ` is at
least `(∑ A)^{2ℓ+1} / n^{2ℓ+2}`. -/
theorem bike_count {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hsym : A.transpose = A) (hnn : ∀ i j, 0 ≤ A i j) {ℓ : ℕ} (hℓ : Even ℓ) :
    (∑ i, ∑ j, A i j * (A ^ ℓ) i i * (A ^ ℓ) j j) ≥
      ((∑ i, ∑ j, A i j)) ^ (2 * ℓ + 1) / (n : ℝ) ^ (2 * ℓ + 2) := by
  obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hℓ
  have hexp1 : 2 * (2 * k) + 1 = 4 * k + 1 := by ring
  have hexp2 : 2 * (2 * k) + 2 = 4 * k + 2 := by ring
  rw [hexp1, hexp2]
  set S : ℝ := ∑ i, ∑ j, A i j with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j))
  rcases lt_or_eq_of_le hSnn with hSpos | hS0
  · -- main case: the total weight `S` is positive
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    -- Cauchy–Schwarz step
    have hcs := bike_cs hsym hnn k
    have hcs' : (∑ a, ∑ b, (A ^ (2 * k + 1)) a b) ^ 2 ≤
        (∑ i, ∑ j, A i j * (A ^ (2 * k)) i i * (A ^ (2 * k)) j j) * ((n : ℝ) ^ 2 * S) := by
      simpa only [← hSdef] using hcs
    -- Blakley–Roy / Mulholland–Smith for the odd length `2k+1`
    have hbr := br_path hn hsym hnn (2 * k + 1)
    have hbr' : (∑ i, ∑ j, A i j) ^ (2 * k + 1) / (n : ℝ) ^ (2 * k) ≤
        ∑ a, ∑ b, (A ^ (2 * k + 1)) a b := by
      rw [show 2 * k + 1 - 1 = 2 * k by omega] at hbr
      exact hbr
    have hc : 0 ≤ (∑ i, ∑ j, A i j) ^ (2 * k + 1) / (n : ℝ) ^ (2 * k) :=
      div_nonneg (pow_nonneg hSnn _) (pow_nonneg (le_of_lt hnpos) _)
    have hTnn : 0 ≤ ∑ a, ∑ b, (A ^ (2 * k + 1)) a b :=
      Finset.sum_nonneg (fun a _ => Finset.sum_nonneg
        (fun b _ => matrix_pow_nonneg hnn (2 * k + 1) a b))
    have hsq : ((∑ i, ∑ j, A i j) ^ (2 * k + 1) / (n : ℝ) ^ (2 * k)) ^ 2 ≤
        (∑ a, ∑ b, (A ^ (2 * k + 1)) a b) ^ 2 := by
      nlinarith [hc, hbr', hTnn]
    have hstep : ((∑ i, ∑ j, A i j) ^ (2 * k + 1) / (n : ℝ) ^ (2 * k)) ^ 2 ≤
        (∑ i, ∑ j, A i j * (A ^ (2 * k)) i i * (A ^ (2 * k)) j j) * ((n : ℝ) ^ 2 * S) :=
      le_trans hsq hcs'
    -- simplify the square of the lower bound
    have hc2 : ((∑ i, ∑ j, A i j) ^ (2 * k + 1) / (n : ℝ) ^ (2 * k)) ^ 2
        = (∑ i, ∑ j, A i j) ^ (4 * k + 2) / (n : ℝ) ^ (4 * k) := by
      rw [div_pow, ← pow_mul, ← pow_mul,
        show (2 * k + 1) * 2 = 4 * k + 2 by ring, show (2 * k) * 2 = 4 * k by ring]
    have hmain : (∑ i, ∑ j, A i j) ^ (4 * k + 2) ≤
        (∑ i, ∑ j, A i j * (A ^ (2 * k)) i i * (A ^ (2 * k)) j j)
          * ((n : ℝ) ^ 2 * S) * (n : ℝ) ^ (4 * k) := by
      rw [hc2] at hstep
      rw [div_le_iff₀ (show (0 : ℝ) < (n : ℝ) ^ (4 * k) by positivity)] at hstep
      simpa [hSdef] using hstep
    -- divide by `S > 0`
    have hgoal : (∑ i, ∑ j, A i j) ^ (4 * k + 1) ≤
        (∑ i, ∑ j, A i j * (A ^ (2 * k)) i i * (A ^ (2 * k)) j j) * (n : ℝ) ^ (4 * k + 2) := by
      have h1 : (∑ i, ∑ j, A i j) ^ (4 * k + 2)
          = (∑ i, ∑ j, A i j) ^ (4 * k + 1) * (∑ i, ∑ j, A i j) := by
        rw [show 4 * k + 2 = 4 * k + 1 + 1 by ring, pow_succ]
      have h2 : (∑ i, ∑ j, A i j * (A ^ (2 * k)) i i * (A ^ (2 * k)) j j)
            * ((n : ℝ) ^ 2 * S) * (n : ℝ) ^ (4 * k)
          = ((∑ i, ∑ j, A i j * (A ^ (2 * k)) i i * (A ^ (2 * k)) j j) * (n : ℝ) ^ (4 * k + 2))
            * S := by
        rw [show 4 * k + 2 = 2 + 4 * k by omega, pow_add]
        ring
      rw [h1, h2] at hmain
      exact le_of_mul_le_mul_right hmain hSpos
    -- conclude
    have hpos : (0 : ℝ) < (n : ℝ) ^ (4 * k + 2) := by positivity
    have hmul : (∑ i, ∑ j, A i j) ^ (4 * k + 1) / (n : ℝ) ^ (4 * k + 2) * (n : ℝ) ^ (4 * k + 2)
        = (∑ i, ∑ j, A i j) ^ (4 * k + 1) := by
      field_simp
    rw [ge_iff_le]
    apply le_of_mul_le_mul_right _ hpos
    rw [hmul]
    exact hgoal
  · -- degenerate case: all entries vanish
    have hzero : ∑ i, ∑ j, A i j = 0 := by
      rw [← hSdef]; exact hS0.symm
    have hrow : ∀ i, (∑ j, A i j) = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ) (f := fun i => ∑ j, A i j)
        (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j))).mp hzero i (Finset.mem_univ i)
    have hA0 : A = 0 := by
      ext i j
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ) (f := fun j => A i j)
        (fun j _ => hnn i j)).mp (hrow i) j (Finset.mem_univ j)
    rw [hA0, ← hS0]
    rw [zero_pow (show 4 * k + 1 ≠ 0 by omega), zero_div]
    simp

end Work.BMF
