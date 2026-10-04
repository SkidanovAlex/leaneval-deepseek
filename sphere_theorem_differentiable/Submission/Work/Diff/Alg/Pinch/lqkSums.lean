import Mathlib
import Submission.Work.Diff.Alg.Pinch.lqkDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Contraction identities for `knProd A (id2 n)` in an orthonormal frame

Auxiliary index computations for the Böhm–Wilking identity
`Work.Diff.Alg.Pinch.linv_Q_ell_knProd`.  Everything here is stated for a symmetric
`2`-tensor `A` (`A i j = A j i`), in the conventions of `Submission.Diff.Alg`:
`R i j k l = ⟪R(eᵢ,eⱼ)eₗ, eₖ⟫`, `knProd A id2` is the Kulkarni–Nomizu product of `A` with the
Kronecker delta (no factor `1/2`), `sqT A = A * A` is the matrix square, `trT A` the trace and
`frobT A` the squared Frobenius norm.

The two main results are the two half-contractions of `Z = knProd A (id2 n)` with itself,

* `lqk_sum1`: `∑_{pq} Zᵢⱼₚq Zₖₗₚq`, and
* `lqk_sum2`: `∑_{pq} Zᵢₚₖq Zⱼₚₗq`,

which together give Hamilton's quadratic term `Q` on `knProd A (id2 n)`.

Everything is proved by expanding the four-term definition of `knProd` and collapsing the
resulting `16` double sums with the elementary Kronecker-delta contractions
`lqk_sum_mul_id2`, `lqk_sum_id2_mul`, `lqk_sum_diag` and the "shape" lemmas
`lqk_sum_cc`, `lqk_sum_dd`, `lqk_sum_ee`, `lqk_sum_ff` (and their variants `...2` where a
Kronecker delta carries its indices in the other order), which capture the possible positions of
the contracted indices in the four factors.
-/

namespace Work.Diff.Alg.Pinch

variable {n : ℕ}

lemma lqk_id2_eq_zero {a q : Fin n} (h : ¬ (a = q)) : id2 n a q = 0 := by
  simp only [id2]; rw [ite_eq_right h]

lemma lqk_id2_eq_one {a q : Fin n} (h : a = q) : id2 n a q = 1 := by
  simp only [id2]; rw [ite_eq_left h]

lemma lqk_sum_mul_id2 (f : Fin n → ℝ) (a : Fin n) : (∑ q, f q * id2 n a q) = f a := by
  rw [Finset.sum_eq_single a]
  · rw [lqk_id2_eq_one rfl, mul_one]
  · intro q _ hq; rw [lqk_id2_eq_zero (fun h => hq h.symm), mul_zero]
  · intro ha; exact absurd (Finset.mem_univ a) ha

lemma lqk_sum_mul_id2' (f : Fin n → ℝ) (a : Fin n) : (∑ q, f q * id2 n q a) = f a := by
  rw [show (∑ q, f q * id2 n q a) = ∑ q, f q * id2 n a q from by
    apply Finset.sum_congr rfl; intro q _; rw [id2_symm q a]]
  exact lqk_sum_mul_id2 f a

lemma lqk_sum_id2_mul (f : Fin n → ℝ) (a : Fin n) : (∑ q, id2 n a q * f q) = f a := by
  rw [Finset.sum_eq_single a]
  · rw [lqk_id2_eq_one rfl, one_mul]
  · intro q _ hq; rw [lqk_id2_eq_zero (fun h => hq h.symm), zero_mul]
  · intro ha; exact absurd (Finset.mem_univ a) ha

lemma lqk_sum_id2_mul' (f : Fin n → ℝ) (a : Fin n) : (∑ q, id2 n q a * f q) = f a := by
  rw [show (∑ q, id2 n q a * f q) = ∑ q, id2 n a q * f q from by
    apply Finset.sum_congr rfl; intro q _; rw [id2_symm q a]]
  exact lqk_sum_id2_mul f a

lemma lqk_sum_diag (f : Fin n → Fin n → ℝ) (p : Fin n) : (∑ q, f p q * id2 n p q) = f p p := by
  rw [Finset.sum_eq_single p]
  · rw [lqk_id2_eq_one rfl, mul_one]
  · intro q _ hq; rw [lqk_id2_eq_zero (fun h => hq h.symm), mul_zero]
  · intro hp; exact absurd (Finset.mem_univ p) hp

lemma lqk_sum_diag' (f : Fin n → Fin n → ℝ) (p : Fin n) : (∑ q, id2 n p q * f p q) = f p p := by
  rw [Finset.sum_eq_single p]
  · rw [lqk_id2_eq_one rfl, one_mul]
  · intro q _ hq; rw [lqk_id2_eq_zero (fun h => hq h.symm), zero_mul]
  · intro hp; exact absurd (Finset.mem_univ p) hp



lemma lqk_sum_delta_diag : (∑ p : Fin n, id2 n p p) = (n : ℝ) := by
  rw [show (∑ p : Fin n, id2 n p p) = ∑ _p : Fin n, (1 : ℝ) from by
    apply Finset.sum_congr rfl; intro p _; exact lqk_id2_eq_one rfl]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma lqk_sum_cc (X Y : Fin n → ℝ) (a b : Fin n) :
    (∑ p, ∑ q, (X p * id2 n a q) * (Y p * id2 n b q)) = id2 n a b * ∑ p, X p * Y p := by
  have h1 : ∀ p : Fin n, (∑ q, (X p * id2 n a q) * (Y p * id2 n b q))
      = (X p * Y p) * (∑ q, id2 n a q * id2 n b q) := by
    intro p
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  simp only [h1, sum_id2_row]
  rw [← Finset.sum_mul]
  ring

lemma lqk_sum_dd (X Y : Fin n → ℝ) (a b : Fin n) :
    (∑ p, ∑ q, (X p * id2 n a q) * (Y q * id2 n b p)) = X b * Y a := by
  have h1 : ∀ p : Fin n, (∑ q, (X p * id2 n a q) * (Y q * id2 n b p))
      = (X p * id2 n b p) * (∑ q, Y q * id2 n a q) := by
    intro p
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  simp only [h1, lqk_sum_mul_id2]
  rw [← Finset.sum_mul, lqk_sum_mul_id2]

lemma lqk_sum_ee (X Y : Fin n → ℝ) (a b : Fin n) :
    (∑ p, ∑ q, (X q * id2 n a p) * (Y p * id2 n b q)) = X b * Y a := by
  rw [show (∑ p, ∑ q, (X q * id2 n a p) * (Y p * id2 n b q))
      = ∑ p, ∑ q, (Y p * id2 n b q) * (X q * id2 n a p) from by
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _; ring]
  rw [lqk_sum_dd Y X b a, mul_comm]

lemma lqk_sum_ff (X Y : Fin n → ℝ) (a b : Fin n) :
    (∑ p, ∑ q, (X q * id2 n a p) * (Y q * id2 n b p)) = id2 n a b * ∑ q, X q * Y q := by
  rw [Finset.sum_comm]
  exact lqk_sum_cc X Y a b


lemma lqk_sum_dd2 (X Y : Fin n → ℝ) (a b : Fin n) :
    (∑ p, ∑ q, (X p * id2 n a q) * (Y q * id2 n p b)) = X b * Y a := by
  have h : ∀ p : Fin n, (∑ q, (X p * id2 n a q) * (Y q * id2 n p b))
      = X p * id2 n p b * Y a := by
    intro p
    rw [show (∑ q, (X p * id2 n a q) * (Y q * id2 n p b))
        = X p * id2 n p b * (∑ q, Y q * id2 n a q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [lqk_sum_mul_id2]
  simp only [h]
  rw [← Finset.sum_mul, lqk_sum_mul_id2']

lemma lqk_sum_ee2 (X Y : Fin n → ℝ) (a b : Fin n) :
    (∑ p, ∑ q, (X q * id2 n p a) * (Y p * id2 n b q)) = X b * Y a := by
  have h : ∀ p : Fin n, (∑ q, (X q * id2 n p a) * (Y p * id2 n b q))
      = Y p * id2 n p a * X b := by
    intro p
    rw [show (∑ q, (X q * id2 n p a) * (Y p * id2 n b q))
        = Y p * id2 n p a * (∑ q, X q * id2 n b q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [lqk_sum_mul_id2]
  simp only [h]
  rw [← Finset.sum_mul, lqk_sum_mul_id2']
  ring

lemma lqk_sum_ff2 (X Y : Fin n → ℝ) (a b : Fin n) :
    (∑ p, ∑ q, (X q * id2 n p a) * (Y q * id2 n p b)) = id2 n a b * ∑ q, X q * Y q := by
  have h : ∀ p : Fin n, (∑ q, (X q * id2 n p a) * (Y q * id2 n p b))
      = id2 n p a * id2 n p b * (∑ q, X q * Y q) := by
    intro p
    rw [show (∑ q, (X q * id2 n p a) * (Y q * id2 n p b))
        = id2 n p a * id2 n p b * (∑ q, X q * Y q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
  simp only [h]
  rw [show (∑ p, id2 n p a * id2 n p b * (∑ q, X q * Y q))
      = (∑ p, id2 n p a * id2 n p b) * (∑ q, X q * Y q) from by
    rw [Finset.sum_mul]]
  rw [sum_id2_col a b]

lemma lqk_sum_c1 (c d : ℝ) :
    (∑ p, ∑ q, (c * id2 n p q) * (d * id2 n p q)) = (n : ℝ) * c * d := by
  have h : ∀ p : Fin n, (∑ q, (c * id2 n p q) * (d * id2 n p q)) = c * d := by
    intro p
    rw [show (∑ q, (c * id2 n p q) * (d * id2 n p q))
        = c * d * (∑ q, id2 n p q * id2 n p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [sum_id2_row (i := p) (j := p), lqk_id2_eq_one rfl, mul_one]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma lqk_sum_c2 (c : ℝ) (Y : Fin n → ℝ) (b : Fin n) :
    (∑ p, ∑ q, (c * id2 n p q) * (Y q * id2 n p b)) = c * Y b := by
  have h : ∀ p : Fin n, (∑ q, (c * id2 n p q) * (Y q * id2 n p b))
      = c * Y p * id2 n p b := by
    intro p
    rw [show (∑ q, (c * id2 n p q) * (Y q * id2 n p b))
        = c * id2 n p b * (∑ q, Y q * id2 n p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [lqk_sum_mul_id2]; ring
  simp only [h]
  rw [show (∑ p, c * Y p * id2 n p b) = c * (∑ p, Y p * id2 n p b) from by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring]
  rw [lqk_sum_mul_id2']

lemma lqk_sum_c3 (c : ℝ) (Y : Fin n → ℝ) (b : Fin n) :
    (∑ p, ∑ q, (c * id2 n p q) * (Y p * id2 n b q)) = c * Y b := by
  have h : ∀ p : Fin n, (∑ q, (c * id2 n p q) * (Y p * id2 n b q))
      = c * Y p * id2 n p b := by
    intro p
    rw [show (∑ q, (c * id2 n p q) * (Y p * id2 n b q))
        = c * Y p * (∑ q, id2 n p q * id2 n b q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [sum_id2_row p b]
  simp only [h]
  rw [show (∑ p, c * Y p * id2 n p b) = c * (∑ p, Y p * id2 n p b) from by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring]
  rw [lqk_sum_mul_id2']

lemma lqk_sum_c4 (c : ℝ) {A : Fin n → Fin n → ℝ} (i k : Fin n) :
    (∑ p, ∑ q, (c * id2 n p q) * (A p q * id2 n i k)) = c * id2 n i k * trT A := by
  have h : ∀ p : Fin n, (∑ q, (c * id2 n p q) * (A p q * id2 n i k))
      = c * id2 n i k * A p p := by
    intro p
    rw [show (∑ q, (c * id2 n p q) * (A p q * id2 n i k))
        = c * id2 n i k * (∑ q, A p q * id2 n p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [lqk_sum_diag]
  simp only [h]
  rw [← Finset.mul_sum]
  rw [trT_apply]

lemma lqk_sum_c5 (c : ℝ) (Y : Fin n → ℝ) (a : Fin n) :
    (∑ p, ∑ q, (Y q * id2 n p a) * (c * id2 n p q)) = c * Y a := by
  have h : ∀ p : Fin n, (∑ q, (Y q * id2 n p a) * (c * id2 n p q))
      = c * id2 n p a * Y p := by
    intro p
    rw [show (∑ q, (Y q * id2 n p a) * (c * id2 n p q))
        = c * id2 n p a * (∑ q, Y q * id2 n p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [lqk_sum_mul_id2]
  simp only [h]
  rw [show (∑ p, c * id2 n p a * Y p) = c * (∑ p, Y p * id2 n p a) from by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring]
  rw [lqk_sum_mul_id2']

lemma lqk_sum_c6 (c : ℝ) (Y : Fin n → ℝ) (b : Fin n) :
    (∑ p, ∑ q, (Y p * id2 n b q) * (c * id2 n p q)) = c * Y b := by
  have h : ∀ p : Fin n, (∑ q, (Y p * id2 n b q) * (c * id2 n p q))
      = c * Y p * id2 n p b := by
    intro p
    rw [show (∑ q, (Y p * id2 n b q) * (c * id2 n p q))
        = c * Y p * (∑ q, id2 n b q * id2 n p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [sum_id2_row b p, id2_symm b p]
  simp only [h]
  rw [show (∑ p, c * Y p * id2 n p b) = c * (∑ p, Y p * id2 n p b) from by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring]
  rw [lqk_sum_mul_id2']

lemma lqk_sum_c7 (c : ℝ) {A : Fin n → Fin n → ℝ} (i k : Fin n) :
    (∑ p, ∑ q, (A p q * id2 n i k) * (c * id2 n p q)) = c * id2 n i k * trT A := by
  have h : ∀ p : Fin n, (∑ q, (A p q * id2 n i k) * (c * id2 n p q))
      = c * id2 n i k * A p p := by
    intro p
    rw [show (∑ q, (A p q * id2 n i k) * (c * id2 n p q))
        = c * id2 n i k * (∑ q, A p q * id2 n p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [lqk_sum_diag]
  simp only [h]
  rw [← Finset.mul_sum]
  rw [trT_apply]

lemma lqk_sum_g1 {A : Fin n → Fin n → ℝ} (Y : Fin n → ℝ) (a i k : Fin n) :
    (∑ p, ∑ q, (Y q * id2 n p a) * (A p q * id2 n i k))
      = id2 n i k * ∑ q, Y q * A a q := by
  have h : ∀ p : Fin n, (∑ q, (Y q * id2 n p a) * (A p q * id2 n i k))
      = id2 n p a * id2 n i k * (∑ q, Y q * A p q) := by
    intro p
    rw [show (∑ q, (Y q * id2 n p a) * (A p q * id2 n i k))
        = id2 n p a * id2 n i k * (∑ q, Y q * A p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
  simp only [h]
  rw [show (∑ p, id2 n p a * id2 n i k * (∑ q, Y q * A p q))
      = id2 n i k * (∑ p, id2 n p a * (∑ q, Y q * A p q)) from by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring]
  rw [lqk_sum_id2_mul']

lemma lqk_sum_g2 {A : Fin n → Fin n → ℝ} (Y : Fin n → ℝ) (b i k : Fin n) :
    (∑ p, ∑ q, (A p q * id2 n i k) * (Y q * id2 n p b))
      = id2 n i k * ∑ q, Y q * A b q := by
  have h : ∀ p : Fin n, (∑ q, (A p q * id2 n i k) * (Y q * id2 n p b))
      = id2 n i k * id2 n p b * (∑ q, A p q * Y q) := by
    intro p
    rw [show (∑ q, (A p q * id2 n i k) * (Y q * id2 n p b))
        = id2 n i k * id2 n p b * (∑ q, A p q * Y q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
  simp only [h]
  rw [show (∑ p, id2 n i k * id2 n p b * (∑ q, A p q * Y q))
      = id2 n i k * (∑ p, (∑ q, A p q * Y q) * id2 n p b) from by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring]
  rw [lqk_sum_mul_id2']
  congr 1
  apply Finset.sum_congr rfl; intro q _; ring

lemma lqk_sum_g3 {A : Fin n → Fin n → ℝ} (Y : Fin n → ℝ) (b i k : Fin n) :
    (∑ p, ∑ q, (Y p * id2 n b q) * (A p q * id2 n i k))
      = id2 n i k * ∑ p, Y p * A p b := by
  have h : ∀ p : Fin n, (∑ q, (Y p * id2 n b q) * (A p q * id2 n i k))
      = id2 n i k * Y p * A p b := by
    intro p
    rw [show (∑ q, (Y p * id2 n b q) * (A p q * id2 n i k))
        = id2 n i k * Y p * (∑ q, id2 n b q * A p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [lqk_sum_id2_mul]
  simp only [h]
  rw [show (∑ p, id2 n i k * Y p * A p b) = id2 n i k * (∑ p, Y p * A p b) from by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring]

lemma lqk_sum_g4 {A : Fin n → Fin n → ℝ} (Y : Fin n → ℝ) (b i k : Fin n) :
    (∑ p, ∑ q, (A p q * id2 n i k) * (Y p * id2 n b q))
      = id2 n i k * ∑ p, Y p * A p b := by
  have h : ∀ p : Fin n, (∑ q, (A p q * id2 n i k) * (Y p * id2 n b q))
      = id2 n i k * Y p * A p b := by
    intro p
    rw [show (∑ q, (A p q * id2 n i k) * (Y p * id2 n b q))
        = id2 n i k * Y p * (∑ q, A p q * id2 n b q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [lqk_sum_mul_id2]
  simp only [h]
  rw [show (∑ p, id2 n i k * Y p * A p b) = id2 n i k * (∑ p, Y p * A p b) from by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring]

lemma lqk_sum_g5 {A : Fin n → Fin n → ℝ} (i k j l : Fin n) :
    (∑ p, ∑ q, (A p q * id2 n i k) * (A p q * id2 n j l))
      = id2 n i k * id2 n j l * frobT A := by
  have h : ∀ p q : Fin n,
      (A p q * id2 n i k) * (A p q * id2 n j l) = (id2 n i k * id2 n j l) * (A p q * A p q) := by
    intro p q; ring
  simp only [h]
  rw [frobT_apply]
  rw [show (∑ p, ∑ q, (id2 n i k * id2 n j l) * (A p q * A p q))
      = (id2 n i k * id2 n j l) * (∑ p, ∑ q, A p q * A p q) from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]]

lemma lqk_sum_AA_eq_sqT {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) (i k : Fin n) :
    (∑ p, A i p * A k p) = sqT A i k := by
  rw [sqT_apply]
  apply Finset.sum_congr rfl; intro p _
  rw [hA p k]

lemma lqk_sum_AA'_eq_sqT {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) (i k : Fin n) :
    (∑ p, A p i * A p k) = sqT A i k := by
  rw [sqT_apply]
  apply Finset.sum_congr rfl; intro p _
  rw [hA p i]

lemma lqk_sqT_symm {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) (i k : Fin n) :
    sqT A i k = sqT A k i := by
  rw [sqT_apply, sqT_apply]
  apply Finset.sum_congr rfl; intro p _
  rw [hA i p, hA p k, mul_comm]

theorem lqk_sum1 (n : ℕ) {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) (i j k l : Fin n) :
    (∑ p, ∑ q, knProd A (id2 n) i j p q
        * knProd A (id2 n) k l p q)
      = 2 * (id2 n j l * sqT A i k
             - id2 n i l * sqT A j k
             + id2 n i k * sqT A j l
             - id2 n j k * sqT A i l)
        + 4 * (A i k * A j l - A i l * A j k) := by
  simp only [knProd]
  simp only [mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [lqk_sum_cc, lqk_sum_dd, lqk_sum_ee, lqk_sum_ff]
  rw [lqk_sum_AA_eq_sqT hA i k, lqk_sum_AA_eq_sqT hA j k, lqk_sum_AA_eq_sqT hA i l,
    lqk_sum_AA_eq_sqT hA j l, hA k j, hA k i, hA l i, hA l j]
  ring

theorem lqk_sum2 (n : ℕ) {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) (i j k l : Fin n) :
    (∑ p, ∑ q, knProd A (id2 n) i p k q
        * knProd A (id2 n) j p l q)
      = ((n : ℝ) - 4) * (A i k * A j l)
        + trT A * (id2 n j l * A i k
            + id2 n i k * A j l)
        + (id2 n k l * sqT A i j
            + id2 n i j * sqT A k l)
        + 2 * (A i j * A k l)
        - 2 * (id2 n j l * sqT A i k
            + id2 n i k * sqT A j l)
        + id2 n i k * id2 n j l
            * frobT A := by
  simp only [knProd]
  simp only [mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [lqk_sum_cc, lqk_sum_dd, lqk_sum_ee, lqk_sum_ff, lqk_sum_dd2, lqk_sum_ee2, lqk_sum_ff2,
    lqk_sum_c1, lqk_sum_c2, lqk_sum_c3, lqk_sum_c4, lqk_sum_c5, lqk_sum_c6, lqk_sum_c7,
    lqk_sum_g1, lqk_sum_g2, lqk_sum_g3, lqk_sum_g4, lqk_sum_g5]
  rw [lqk_sum_AA_eq_sqT hA i j, lqk_sum_AA_eq_sqT hA j l, lqk_sum_AA_eq_sqT hA i k,
    lqk_sum_AA'_eq_sqT hA k l, lqk_sum_AA'_eq_sqT hA l j, lqk_sum_AA'_eq_sqT hA k i]
  rw [lqk_sqT_symm hA l j, lqk_sqT_symm hA k i]
  rw [hA l k, hA j i]
  ring


end Work.Diff.Alg.Pinch
