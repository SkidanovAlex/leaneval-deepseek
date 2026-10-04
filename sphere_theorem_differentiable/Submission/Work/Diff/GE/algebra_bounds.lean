import Mathlib
import Submission.Work.Diff.GE.Api

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-! ## Elementary summation lemmas -/

/-- A single nonnegative summand is at most the whole sum. -/
private lemma le_sum_univ {ι : Type*} [Fintype ι] {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (a : ι) :
    f a ≤ ∑ i, f i := by
  simpa using Finset.single_le_sum (s := Finset.univ) (fun i _ => hf i) (Finset.mem_univ a)

/-- `frobSq` is a sum of squares, hence nonnegative. -/
private lemma frobSq_nonneg {n : ℕ} (R : Curv4 n) : 0 ≤ frobSq R := by
  simp only [frobSq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _

/-- Cauchy–Schwarz for an `ℓ¹`-norm against the `ℓ²`-norm on a finite type. -/
private lemma sq_sum_abs_le_card_mul_sum_sq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, |f i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, f i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |f i|)
  simpa [sq_abs] using h

/-- The `(0,4)`-array `R : Curv4 n` read as a function of the flat index
`(i,j,k,l) : Fin n × Fin n × Fin n × Fin n`. -/
private abbrev flat4 {n : ℕ} (R : Curv4 n) : (Fin n × Fin n × Fin n × Fin n) → ℝ :=
  fun x => R x.1 x.2.1 x.2.2.1 x.2.2.2

/-- `frobSq` is the sum of squares over the flat index. -/
private lemma frobSq_eq_sum_flat4 {n : ℕ} (R : Curv4 n) :
    frobSq R = ∑ x : Fin n × Fin n × Fin n × Fin n, (flat4 R x) ^ 2 := by
  simp only [frobSq, flat4, Fintype.sum_prod_type]

/-- A "diagonal" slice `(k,i,k,j)` of the four-index square sum is bounded by the full sum. -/
private lemma sum_diag_le_frobSq {n : ℕ} (R : Curv4 n) (i j : Fin n) :
    ∑ k, R k i k j ^ 2 ≤ frobSq R := by
  rw [frobSq_eq_sum_flat4]
  have key : (∑ x ∈ Finset.image (fun k : Fin n => (k, (i, (k, j))))
        (Finset.univ : Finset (Fin n)), (flat4 R x) ^ 2) = ∑ k, R k i k j ^ 2 := by
    rw [Finset.sum_image (by intro a _ b _ hab; exact congrArg Prod.fst hab)]
  rw [← key]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
  intro x _ _
  exact sq_nonneg _

/-- The `(0,5)`-array `S` read as a function of the flat index `(m,i,j,k,l)`. -/
private abbrev flat5 {n : ℕ} (S : Fin n → Curv4 n) :
    (Fin n × Fin n × Fin n × Fin n × Fin n) → ℝ :=
  fun x => S x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- **Elementary bounds for curvature arrays.**  For a `(0,4)`-curvature array `R` (as used in
`Curv4 n`) and a `(0,5)`-array `S` (the components of `∇Rm`), the individual components, the Ricci
components `∑_k R k i k j` and the `ℓ¹`-norm of the components of `S` are all controlled by the
Frobenius norms `frobSq R = ∑ Rᵢⱼₖₗ²` and `∑_m frobSq (S m) = ∑ S_{mijkl}²`. -/
theorem algebra_bounds {n : ℕ} (R : Curv4 n) (S : Fin n → Curv4 n) :
    (∀ i j, (∑ k, R k i k j) ^ 2 ≤ (n : ℝ) * frobSq R) ∧
    (∀ i j k l, (R i j k l) ^ 2 ≤ frobSq R) ∧
    (∀ m i j k l, (S m i j k l) ^ 2 ≤ ∑ m, frobSq (S m)) ∧
    ((∑ m, ∑ i, ∑ j, ∑ k, ∑ l, |S m i j k l|) ^ 2
      ≤ (n : ℝ) ^ 5 * (∑ m, frobSq (S m))) := by
  -- (1) each Ricci component: Cauchy–Schwarz over `k`, then a diagonal slice of `frobSq`.
  have h1 : ∀ i j : Fin n, (∑ k, R k i k j) ^ 2 ≤ (n : ℝ) * frobSq R := by
    intro i j
    have hcs : (∑ k, R k i k j) ^ 2 ≤ (n : ℝ) * ∑ k, (R k i k j) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k : Fin n => R k i k j)
      simpa [Fintype.card_fin] using this
    exact hcs.trans
      (mul_le_mul_of_nonneg_left (sum_diag_le_frobSq R i j) (Nat.cast_nonneg n))
  -- (2) each component of `R`: a single term of the square sum.
  have h2 : ∀ i j k l : Fin n, (R i j k l) ^ 2 ≤ frobSq R := by
    intro i j k l
    calc (R i j k l) ^ 2 ≤ ∑ l', R i j k l' ^ 2 := le_sum_univ (fun l' => sq_nonneg _) l
      _ ≤ ∑ k', ∑ l', R i j k' l' ^ 2 :=
        le_sum_univ (fun k' => Finset.sum_nonneg (fun l' _ => sq_nonneg _)) k
      _ ≤ ∑ j', ∑ k', ∑ l', R i j' k' l' ^ 2 :=
        le_sum_univ (fun j' => Finset.sum_nonneg (fun k' _ =>
          Finset.sum_nonneg (fun l' _ => sq_nonneg _))) j
      _ ≤ ∑ i', ∑ j', ∑ k', ∑ l', R i' j' k' l' ^ 2 :=
        le_sum_univ (fun i' => Finset.sum_nonneg (fun j' _ => Finset.sum_nonneg (fun k' _ =>
          Finset.sum_nonneg (fun l' _ => sq_nonneg _)))) i
      _ = frobSq R := rfl
  -- (3) each component of `S`: a single term of the full `(0,5)` square sum.
  have h3 : ∀ m i j k l : Fin n, (S m i j k l) ^ 2 ≤ ∑ m, frobSq (S m) := by
    intro m i j k l
    calc (S m i j k l) ^ 2 ≤ ∑ l', (S m i j k l') ^ 2 := le_sum_univ (fun l' => sq_nonneg _) l
      _ ≤ ∑ k', ∑ l', (S m i j k' l') ^ 2 :=
        le_sum_univ (fun k' => Finset.sum_nonneg (fun l' _ => sq_nonneg _)) k
      _ ≤ ∑ j', ∑ k', ∑ l', (S m i j' k' l') ^ 2 :=
        le_sum_univ (fun j' => Finset.sum_nonneg (fun k' _ =>
          Finset.sum_nonneg (fun l' _ => sq_nonneg _))) j
      _ ≤ ∑ i', ∑ j', ∑ k', ∑ l', (S m i' j' k' l') ^ 2 :=
        le_sum_univ (fun i' => Finset.sum_nonneg (fun j' _ => Finset.sum_nonneg (fun k' _ =>
          Finset.sum_nonneg (fun l' _ => sq_nonneg _)))) i
      _ = frobSq (S m) := rfl
      _ ≤ ∑ m', frobSq (S m') := le_sum_univ (fun m' => frobSq_nonneg (S m')) m
  refine ⟨h1, h2, h3, ?_⟩
  -- (4) the `ℓ¹`-norm of `S` against its `ℓ²`-norm: Cauchy–Schwarz on the flat index `(m,i,j,k,l)`.
  have hsum : (∑ x : Fin n × Fin n × Fin n × Fin n × Fin n, |flat5 S x|)
      = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, |S m i j k l| := by
    simp only [flat5, Fintype.sum_prod_type]
  have hsq : (∑ x : Fin n × Fin n × Fin n × Fin n × Fin n, flat5 S x ^ 2)
      = ∑ m, frobSq (S m) := by
    simp only [flat5, frobSq, Fintype.sum_prod_type]
  have hcard : ((Fintype.card (Fin n × Fin n × Fin n × Fin n × Fin n) : ℕ) : ℝ) = (n : ℝ) ^ 5 := by
    simp [Fintype.card_prod, Fintype.card_fin]
    ring
  calc (∑ m, ∑ i, ∑ j, ∑ k, ∑ l, |S m i j k l|) ^ 2
      = (∑ x : Fin n × Fin n × Fin n × Fin n × Fin n, |flat5 S x|) ^ 2 := by rw [hsum]
    _ ≤ (Fintype.card (Fin n × Fin n × Fin n × Fin n × Fin n) : ℝ)
          * ∑ x, flat5 S x ^ 2 := sq_sum_abs_le_card_mul_sum_sq (fun x => flat5 S x)
    _ = (n : ℝ) ^ 5 * (∑ m, frobSq (S m)) := by rw [hcard, hsq]

end Work.Diff.GE
