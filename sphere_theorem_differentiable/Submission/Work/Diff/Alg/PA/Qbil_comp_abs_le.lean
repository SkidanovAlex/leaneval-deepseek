import Mathlib
import Submission.Work.Diff.Alg.PA.CS_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Componentwise bound for the polarised reaction term `Qbil`

`Qbil n A B` is the symmetric bilinear form polarising Hamilton's reaction term `Q`:
`Q (A + B) = Q A + Q B + 2 • Qbil n A B`.  The target is the componentwise estimate

  `|Qbil n A B i j k l| ≤ 5 n² √(|A|²) √(|B|²)`,

where `|A|² = frobSq A` is the sum of the squares of the components of `A`.

`Qbil` is a polarised quadratic form, so its components are `1/2` times the sum of the six
bilinear pairings

  `∑_{p,q} ( Aᵢⱼₚq Bₖₗₚq + Bᵢⱼₚq Aₖₗₚq + 2 Aᵢₚₖq Bⱼₚₗq + 2 Bᵢₚₖq Aⱼₚₗq
            - 2 Aᵢₚₗq Bⱼₚₖq - 2 Bᵢₚₗq Aⱼₚₖq )`

(`Qbil_apply_eq`).  Every one of the six double sums is a Euclidean scalar product indexed by
`(p,q)`, hence is bounded by `√(frobSq A) √(frobSq B)` by Cauchy–Schwarz
(`sum2_abs_mul_le_frobSq_12`, `sum2_abs_mul_le_frobSq_13`): the moving index patterns have
sums of squares that are sub-sums of the full four-fold sum of squares (`sum_12_le`,
`sum_13_le`, `sum_first_le_frobSq`).  The triangle inequality then gives `10 √|A|² √|B|²`
before the factor `1/2`, i.e. the factor `5` of the statement.  The extra factor `(n : ℝ) ^ 2`
is not needed: it is at least `1` since a `Fin n` index is given.
-/

open Finset Submission.Diff.Alg

namespace Work.Diff.Alg.PA

variable {n : ℕ}

/-! ## Elementary absolute-value toolkit -/

/-- Triangle inequality for six terms:
`|a + b + c + d - e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f|`. -/
lemma abs_six_le (a b c d e f : ℝ) :
    |a + b + c + d - e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 : |a + b| ≤ |a| + |b| := abs_add_le a b
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h4 : |a + b + c + d - e| ≤ |a + b + c + d| + |e| := by
    calc |a + b + c + d - e| = |(a + b + c + d) + (-e)| := rfl
      _ ≤ |a + b + c + d| + |-e| := abs_add_le _ _
      _ = |a + b + c + d| + |e| := by rw [abs_neg]
  have h5 : |a + b + c + d - e - f| ≤ |a + b + c + d - e| + |f| := by
    calc |a + b + c + d - e - f| = |(a + b + c + d - e) + (-f)| := rfl
      _ ≤ |a + b + c + d - e| + |-f| := abs_add_le _ _
      _ = |a + b + c + d - e| + |f| := by rw [abs_neg]
  linarith

/-! ## Cauchy–Schwarz for products of absolute values -/

/-- Cauchy–Schwarz for the sum of the products `|X i| |Y i|`: since all summands are nonnegative
this is the absolute-value form of `|∑ Xᵢ Yᵢ| ≤ √(∑Xᵢ²) √(∑Yᵢ²)`. -/
lemma sum_abs_mul_le_sqrt {ι : Type*} [Fintype ι] (X Y : ι → ℝ) :
    (∑ i, |X i| * |Y i|) ≤ Real.sqrt (∑ i, X i ^ 2) * Real.sqrt (∑ i, Y i ^ 2) := by
  have hsq : (∑ i, |X i| * |Y i|) ^ 2 ≤ (∑ i, X i ^ 2) * (∑ i, Y i ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun i => |X i|) (fun i => |Y i|)
    simpa only [sq_abs] using h
  have h0 : 0 ≤ ∑ i, |X i| * |Y i| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc (∑ i, |X i| * |Y i|) ≤ Real.sqrt ((∑ i, X i ^ 2) * (∑ i, Y i ^ 2)) := by
        rw [← Real.sqrt_sq h0]
        exact Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ i, X i ^ 2) * Real.sqrt (∑ i, Y i ^ 2) :=
        Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _) _

/-- The double-index version of `sum_abs_mul_le_sqrt`. -/
lemma sum2_abs_mul_le_sqrt (X Y : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, |X p q| * |Y p q|) ≤
      Real.sqrt (∑ p, ∑ q, X p q ^ 2) * Real.sqrt (∑ p, ∑ q, Y p q ^ 2) := by
  have e1 : (∑ p, ∑ q, |X p q| * |Y p q|)
      = ∑ pq : Fin n × Fin n, |X pq.1 pq.2| * |Y pq.1 pq.2| := by
    simp only [Fintype.sum_prod_type]
  have e2 : (∑ p, ∑ q, X p q ^ 2) = ∑ pq : Fin n × Fin n, X pq.1 pq.2 ^ 2 := by
    simp only [Fintype.sum_prod_type]
  have e3 : (∑ p, ∑ q, Y p q ^ 2) = ∑ pq : Fin n × Fin n, Y pq.1 pq.2 ^ 2 := by
    simp only [Fintype.sum_prod_type]
  rw [e1, e2, e3]
  exact sum_abs_mul_le_sqrt _ _

/-! ## Sub-sums of the four-fold sum of squares -/

/-- The sum of the squares over the last three indices, the first one fixed, is at most the full
Frobenius square. -/
lemma sum_first_le_frobSq (X : Curv4 n) (a : Fin n) :
    (∑ j, ∑ k, ∑ l, X a j k l ^ 2) ≤ frobSq X := by
  simp only [frobSq]
  exact Finset.single_le_sum (f := fun a' => ∑ j, ∑ k, ∑ l, X a' j k l ^ 2)
    (fun a' _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ a)

/-- The sum of the squares over the last two indices (with the first two fixed) is at most the
sum over the last three indices. -/
lemma sum_12_le (X : Curv4 n) (i j : Fin n) :
    (∑ p, ∑ q, X i j p q ^ 2) ≤ ∑ _j', ∑ _k, ∑ _l, X i _j' _k _l ^ 2 :=
  Finset.single_le_sum (f := fun j' => ∑ k, ∑ l, X i j' k l ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)

/-- The sum of the squares over the slots `2` and `4` (with the slots `1` and `3` fixed) is at most
the sum over the last three indices. -/
lemma sum_13_le (X : Curv4 n) (i k : Fin n) :
    (∑ p, ∑ q, X i p k q ^ 2) ≤ ∑ _j, ∑ _k', ∑ _l, X i _j _k' _l ^ 2 := by
  refine Finset.sum_le_sum (fun p _ => ?_)
  exact Finset.single_le_sum (f := fun k' => ∑ l, X i p k' l ^ 2)
    (fun k' _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ k)

/-! ## Cauchy–Schwarz bounds for the two index patterns occurring in `Q` -/

/-- Cauchy–Schwarz for the scalar product of the `(a,b)`-row of `X` with the `(c,d)`-row of `Y`. -/
lemma sum2_abs_mul_le_frobSq_12 (X Y : Curv4 n) (a b c d : Fin n) :
    (∑ p, ∑ q, |X a b p q| * |Y c d p q|) ≤
      Real.sqrt (frobSq X) * Real.sqrt (frobSq Y) := by
  have h := sum2_abs_mul_le_sqrt (fun p q => X a b p q) (fun p q => Y c d p q)
  have e1 : (∑ p, ∑ q, X a b p q ^ 2) ≤ frobSq X :=
    (sum_12_le X a b).trans (sum_first_le_frobSq X a)
  have e2 : (∑ p, ∑ q, Y c d p q ^ 2) ≤ frobSq Y :=
    (sum_12_le Y c d).trans (sum_first_le_frobSq Y c)
  exact h.trans (mul_le_mul (Real.sqrt_le_sqrt e1) (Real.sqrt_le_sqrt e2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Cauchy–Schwarz for the scalar product of the `(a,·,b,·)`-pattern of `X` with the
`(c,·,d,·)`-pattern of `Y`. -/
lemma sum2_abs_mul_le_frobSq_13 (X Y : Curv4 n) (a b c d : Fin n) :
    (∑ p, ∑ q, |X a p b q| * |Y c p d q|) ≤
      Real.sqrt (frobSq X) * Real.sqrt (frobSq Y) := by
  have h := sum2_abs_mul_le_sqrt (fun p q => X a p b q) (fun p q => Y c p d q)
  have e1 : (∑ p, ∑ q, X a p b q ^ 2) ≤ frobSq X :=
    (sum_13_le X a b).trans (sum_first_le_frobSq X a)
  have e2 : (∑ p, ∑ q, Y c p d q ^ 2) ≤ frobSq Y :=
    (sum_13_le Y c d).trans (sum_first_le_frobSq Y c)
  exact h.trans (mul_le_mul (Real.sqrt_le_sqrt e1) (Real.sqrt_le_sqrt e2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-! ## The polarisation identity and the pointwise estimate -/

/-- The components of the polarised reaction term: `Qbil` is `1/2` times the sum of the six
bilinear pairings coming from the expansion of `Q (A + B)`. -/
lemma Qbil_apply_eq (n : ℕ) (A B : Curv4 n) (i j k l : Fin n) :
    Qbil n A B i j k l =
      (1 / 2) * ∑ p, ∑ q, (A i j p q * B k l p q + B i j p q * A k l p q
        + 2 * A i p k q * B j p l q + 2 * B i p k q * A j p l q
        - 2 * A i p l q * B j p k q - 2 * B i p l q * A j p k q) := by
  have hss : ∀ f g h : Fin n → ℝ, (∑ x, f x) - (∑ x, g x) - (∑ x, h x)
      = ∑ x, (f x - g x - h x) := by
    intro f g h
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Qbil, Q, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [hss]
  apply Finset.sum_congr rfl; intro p _
  rw [hss]
  apply Finset.sum_congr rfl; intro q _
  ring

/-- Pointwise estimate for one summand of the expansion of `Qbil`: the six-term triangle
inequality, followed by `|x * y| = |x| |y|`. -/
lemma abs_Qsummand_le (A B : Curv4 n) (i j k l : Fin n) (p q : Fin n) :
    |A i j p q * B k l p q + B i j p q * A k l p q
      + 2 * A i p k q * B j p l q + 2 * B i p k q * A j p l q
      - 2 * A i p l q * B j p k q - 2 * B i p l q * A j p k q| ≤
    |A i j p q| * |B k l p q| + |B i j p q| * |A k l p q|
      + 2 * (|A i p k q| * |B j p l q|) + 2 * (|B i p k q| * |A j p l q|)
      + 2 * (|A i p l q| * |B j p k q|) + 2 * (|B i p l q| * |A j p k q|) := by
  have h := abs_six_le (A i j p q * B k l p q) (B i j p q * A k l p q)
    (2 * A i p k q * B j p l q) (2 * B i p k q * A j p l q)
    (2 * A i p l q * B j p k q) (2 * B i p l q * A j p k q)
  simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] at h
  simpa only [mul_assoc] using h

/-- Splitting a double sum of a six-term summand into the six double sums (the two constant
factors `2` being pulled out). -/
lemma sum_sum_six (x1 x2 x3 x4 x5 x6 : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, (x1 p q + x2 p q + 2 * x3 p q + 2 * x4 p q
        + 2 * x5 p q + 2 * x6 p q))
      = ((((∑ p, ∑ q, x1 p q) + (∑ p, ∑ q, x2 p q)) + 2 * (∑ p, ∑ q, x3 p q))
          + 2 * (∑ p, ∑ q, x4 p q) + 2 * (∑ p, ∑ q, x5 p q)) + 2 * (∑ p, ∑ q, x6 p q) := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The bound for the six-term double sum of the expansion of `Qbil`. -/
lemma abs_Qbil_sum_le (A B : Curv4 n) (i j k l : Fin n) :
    |∑ p, ∑ q, (A i j p q * B k l p q + B i j p q * A k l p q
        + 2 * A i p k q * B j p l q + 2 * B i p k q * A j p l q
        - 2 * A i p l q * B j p k q - 2 * B i p l q * A j p k q)| ≤
      10 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) := by
  -- the six Cauchy–Schwarz bounds
  have h1 : (∑ p, ∑ q, |A i j p q| * |B k l p q|) ≤
      Real.sqrt (frobSq A) * Real.sqrt (frobSq B) := sum2_abs_mul_le_frobSq_12 A B i j k l
  have h2 : (∑ p, ∑ q, |B i j p q| * |A k l p q|) ≤
      Real.sqrt (frobSq A) * Real.sqrt (frobSq B) :=
    (sum2_abs_mul_le_frobSq_12 B A i j k l).trans (le_of_eq (mul_comm _ _))
  have h3 : 2 * (∑ p, ∑ q, |A i p k q| * |B j p l q|) ≤
      2 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) :=
    mul_le_mul_of_nonneg_left (sum2_abs_mul_le_frobSq_13 A B i k j l) (by norm_num)
  have h4 : 2 * (∑ p, ∑ q, |B i p k q| * |A j p l q|) ≤
      2 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) :=
    mul_le_mul_of_nonneg_left ((sum2_abs_mul_le_frobSq_13 B A i k j l).trans
      (le_of_eq (mul_comm _ _))) (by norm_num)
  have h5 : 2 * (∑ p, ∑ q, |A i p l q| * |B j p k q|) ≤
      2 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) :=
    mul_le_mul_of_nonneg_left (sum2_abs_mul_le_frobSq_13 A B i l j k) (by norm_num)
  have h6 : 2 * (∑ p, ∑ q, |B i p l q| * |A j p k q|) ≤
      2 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) :=
    mul_le_mul_of_nonneg_left ((sum2_abs_mul_le_frobSq_13 B A i l j k).trans
      (le_of_eq (mul_comm _ _))) (by norm_num)
  have htri : |∑ p, ∑ q, (A i j p q * B k l p q + B i j p q * A k l p q
        + 2 * A i p k q * B j p l q + 2 * B i p k q * A j p l q
        - 2 * A i p l q * B j p k q - 2 * B i p l q * A j p k q)| ≤
      ∑ p, ∑ q, |A i j p q * B k l p q + B i j p q * A k l p q
        + 2 * A i p k q * B j p l q + 2 * B i p k q * A j p l q
        - 2 * A i p l q * B j p k q - 2 * B i p l q * A j p k q| := by
    calc |∑ p, ∑ q, (A i j p q * B k l p q + B i j p q * A k l p q
          + 2 * A i p k q * B j p l q + 2 * B i p k q * A j p l q
          - 2 * A i p l q * B j p k q - 2 * B i p l q * A j p k q)|
        ≤ ∑ p, |∑ q, (A i j p q * B k l p q + B i j p q * A k l p q
          + 2 * A i p k q * B j p l q + 2 * B i p k q * A j p l q
          - 2 * A i p l q * B j p k q - 2 * B i p l q * A j p k q)| :=
          Finset.abs_sum_le_sum_abs _ Finset.univ
      _ ≤ ∑ p, ∑ q, |A i j p q * B k l p q + B i j p q * A k l p q
          + 2 * A i p k q * B j p l q + 2 * B i p k q * A j p l q
          - 2 * A i p l q * B j p k q - 2 * B i p l q * A j p k q| :=
          Finset.sum_le_sum fun p _ =>
            Finset.abs_sum_le_sum_abs _ Finset.univ
  have hsplit := sum_sum_six (fun p q => |A i j p q| * |B k l p q|)
    (fun p q => |B i j p q| * |A k l p q|)
    (fun p q => |A i p k q| * |B j p l q|)
    (fun p q => |B i p k q| * |A j p l q|)
    (fun p q => |A i p l q| * |B j p k q|)
    (fun p q => |B i p l q| * |A j p k q|)
  have hpt : (∑ p, ∑ q, |A i j p q * B k l p q + B i j p q * A k l p q
        + 2 * A i p k q * B j p l q + 2 * B i p k q * A j p l q
        - 2 * A i p l q * B j p k q - 2 * B i p l q * A j p k q|) ≤
      ∑ p, ∑ q, (|A i j p q| * |B k l p q| + |B i j p q| * |A k l p q|
        + 2 * (|A i p k q| * |B j p l q|) + 2 * (|B i p k q| * |A j p l q|)
        + 2 * (|A i p l q| * |B j p k q|) + 2 * (|B i p l q| * |A j p k q|)) :=
    Finset.sum_le_sum fun p _ =>
      Finset.sum_le_sum fun q _ => abs_Qsummand_le A B i j k l p q
  calc |∑ p, ∑ q, (A i j p q * B k l p q + B i j p q * A k l p q
        + 2 * A i p k q * B j p l q + 2 * B i p k q * A j p l q
        - 2 * A i p l q * B j p k q - 2 * B i p l q * A j p k q)|
      ≤ ∑ p, ∑ q, |A i j p q * B k l p q + B i j p q * A k l p q
        + 2 * A i p k q * B j p l q + 2 * B i p k q * A j p l q
        - 2 * A i p l q * B j p k q - 2 * B i p l q * A j p k q| := htri
    _ ≤ ∑ p, ∑ q, (|A i j p q| * |B k l p q| + |B i j p q| * |A k l p q|
        + 2 * (|A i p k q| * |B j p l q|) + 2 * (|B i p k q| * |A j p l q|)
        + 2 * (|A i p l q| * |B j p k q|) + 2 * (|B i p l q| * |A j p k q|)) := hpt
    _ = ((((∑ p, ∑ q, |A i j p q| * |B k l p q|) + (∑ p, ∑ q, |B i j p q| * |A k l p q|))
          + 2 * (∑ p, ∑ q, |A i p k q| * |B j p l q|))
          + 2 * (∑ p, ∑ q, |B i p k q| * |A j p l q|)
          + 2 * (∑ p, ∑ q, |A i p l q| * |B j p k q|))
          + 2 * (∑ p, ∑ q, |B i p l q| * |A j p k q|) := hsplit
    _ ≤ 10 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) := by
        linarith [h1, h2, h3, h4, h5, h6]

/-! ## The componentwise bound -/

theorem Qbil_comp_abs_le (n : ℕ) (A B : _root_.Submission.Diff.Alg.Curv4 n) (i j k l : Fin n) :
    |_root_.Work.Diff.Alg.PA.Qbil n A B i j k l| ≤
      5 * (n : ℝ) ^ 2 * (Real.sqrt (_root_.Submission.Diff.Alg.frobSq A) *
        Real.sqrt (_root_.Submission.Diff.Alg.frobSq B)) := by
  have hsA : 0 ≤ Real.sqrt (frobSq A) := Real.sqrt_nonneg _
  have hsB : 0 ≤ Real.sqrt (frobSq B) := Real.sqrt_nonneg _
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    have h : 1 ≤ n := by
      have := i.isLt
      omega
    exact_mod_cast h
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have h10 := abs_Qbil_sum_le A B i j k l
  rw [Qbil_apply_eq n A B i j k l, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  calc (1 / 2) * |∑ p, ∑ q, (A i j p q * B k l p q + B i j p q * A k l p q
        + 2 * A i p k q * B j p l q + 2 * B i p k q * A j p l q
        - 2 * A i p l q * B j p k q - 2 * B i p l q * A j p k q)|
      ≤ (1 / 2) * (10 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B))) := by linarith
    _ = 5 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) := by ring
    _ ≤ 5 * (n : ℝ) ^ 2 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hsA hsB)

end Work.Diff.Alg.PA
