import Mathlib
import Submission.Work.Diff.PP.deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.PP

open Submission.Diff.Alg
open Finset

/-!
# `Q (Iso n) = 2 (n - 1) • Iso n`

Componentwise computation of Hamilton's reaction term on the curvature tensor of the unit round
sphere.  Writing `D n a b = δ_{ab}` (the Kronecker delta), `Iso n` has components
`D n i k * D n j l - D n i l * D n j k`, and `Q` expands into three trace-type sums whose values
are computed from the single basic identity `∑ p, D n a p * D n p b = D n a b`.
-/

/-- The Kronecker delta on `Fin n`, as a real matrix. -/
private noncomputable def D (n : ℕ) : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0

private lemma Iso_eq_D (n : ℕ) (i j k l : Fin n) :
    Iso n i j k l = D n i k * D n j l - D n i l * D n j k := rfl

private lemma D_symm {n : ℕ} (i j : Fin n) : D n i j = D n j i := by
  by_cases h : i = j
  · subst h; rfl
  · simp [D, h, Ne.symm h]

private lemma D_idem {n : ℕ} (i j : Fin n) : D n i j * D n i j = D n i j := by
  by_cases h : i = j <;> simp [D, h]

/-- The fundamental contraction `∑ p, δ_{a p} δ_{p b} = δ_{a b}`. -/
private lemma sum_D_mul_D_row {n : ℕ} (i j : Fin n) : ∑ p, D n i p * D n p j = D n i j := by
  rw [Finset.sum_eq_single i]
  · simp [D]
  · intro b _ hb
    have h : i ≠ b := fun h => hb h.symm
    simp [D, h]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Row contraction: `∑ p, δ_{i p} δ_{k p} = δ_{i k}`. -/
private lemma sum_D_row {n : ℕ} (i k : Fin n) : ∑ p, D n i p * D n k p = D n i k := by
  rw [← sum_D_mul_D_row (n := n) i k]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [D_symm p k]

/-- Column contraction: `∑ p, δ_{p i} δ_{p k} = δ_{i k}`. -/
private lemma sum_D_col {n : ℕ} (i k : Fin n) : ∑ p, D n p i * D n p k = D n i k := by
  have h := sum_D_mul_D_row (n := n) k i
  rw [D_symm k i] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [D_symm p i, D_symm p k]
  ring

/-- The trace of the delta: `∑ p ∑ q, δ_{p q} = n`. -/
private lemma sum_D_trace {n : ℕ} : ∑ p, ∑ q, D n p q = (n : ℝ) := by
  have hinner : ∀ p : Fin n, (∑ q, D n p q) = 1 := by
    intro p
    rw [Finset.sum_eq_single p]
    · simp [D]
    · intro b _ hb; have h : p ≠ b := fun h => hb h.symm; simp [D, h]
    · intro h; exact absurd (Finset.mem_univ p) h
  simp only [hinner]
  simp

private lemma sum_D_sq {n : ℕ} : ∑ p, ∑ q, D n p q * D n p q = (n : ℝ) := by
  rw [← sum_D_trace (n := n)]
  exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => D_idem p q))

/-- A double sum of a product of a `p`-factor and a `q`-factor factors. -/
private lemma factor2 {n : ℕ} (f g : Fin n → ℝ) :
    ∑ p, ∑ q, f p * g q = (∑ p, f p) * (∑ q, g q) := by
  rw [Finset.sum_mul_sum]

/-- A constant pulls out of a double sum. -/
private lemma pullconst2 {n : ℕ} (c : ℝ) (F : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, c * F p q) = c * (∑ p, ∑ q, F p q) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]

/-- Mixed contraction: `∑ p ∑ q, δ_{p q} δ_{p a} δ_{b q} = δ_{b a}`. -/
private lemma triple {n : ℕ} (a b : Fin n) :
    ∑ p, ∑ q, D n p q * D n p a * D n b q = D n b a := by
  rw [Finset.sum_comm]
  have hinner : ∀ q : Fin n, (∑ p, D n p q * D n p a * D n b q) = D n q a * D n b q := by
    intro q
    rw [← Finset.sum_mul, sum_D_col]
  simp only [hinner]
  rw [D_symm b a, ← sum_D_mul_D_row (n := n) a b]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [D_symm q a, D_symm b q]

/-- Distribution of a double sum of a four-term combination. -/
private lemma sum4 {n : ℕ} (A B C E : Fin n → Fin n → ℝ) :
    ∑ p, ∑ q, (A p q - B p q - C p q + E p q)
      = (∑ p, ∑ q, A p q) - (∑ p, ∑ q, B p q) - (∑ p, ∑ q, C p q)
        + (∑ p, ∑ q, E p q) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Distribution of a double sum of `A + 2 B - 2 C`. -/
private lemma sum_lin {n : ℕ} (A B C : Fin n → Fin n → ℝ) :
    ∑ p, ∑ q, (A p q + 2 * B p q - 2 * C p q)
      = (∑ p, ∑ q, A p q) + 2 * (∑ p, ∑ q, B p q) - 2 * (∑ p, ∑ q, C p q) := by
  have h1 : ∀ p, (∑ q, (A p q + 2 * B p q - 2 * C p q))
      = (∑ q, A p q) + 2 * (∑ q, B p q) - 2 * (∑ q, C p q) := by
    intro p
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The `∑_{p,q} Iso i j p q · Iso k l p q` part of `Q`: it equals `2 Iso i j k l`. -/
private lemma S1 {n : ℕ} (i j k l : Fin n) :
    ∑ p, ∑ q, (D n i p * D n j q - D n i q * D n j p) * (D n k p * D n l q - D n k q * D n l p)
      = 2 * (D n i k * D n j l) - 2 * (D n i l * D n j k) := by
  have hpt : ∀ p q : Fin n,
      (D n i p * D n j q - D n i q * D n j p) * (D n k p * D n l q - D n k q * D n l p)
      = (D n i p * D n k p) * (D n j q * D n l q) - (D n j p * D n k p) * (D n i q * D n l q)
        - (D n i p * D n l p) * (D n j q * D n k q) + (D n j p * D n l p) * (D n i q * D n k q) := by
    intro p q; ring
  rw [show (∑ p, ∑ q,
        (D n i p * D n j q - D n i q * D n j p) * (D n k p * D n l q - D n k q * D n l p))
        = (∑ p, ∑ q,
            ((D n i p * D n k p) * (D n j q * D n l q) - (D n j p * D n k p) * (D n i q * D n l q)
              - (D n i p * D n l p) * (D n j q * D n k q) + (D n j p * D n l p) * (D n i q * D n k q)))
      from Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
  rw [sum4, factor2, factor2, factor2, factor2]
  simp only [sum_D_row]
  ring

/-- The `∑_{p,q} Iso i p k q · Iso j p l q` part of `Q`. -/
private lemma S2 {n : ℕ} (i j k l : Fin n) :
    ∑ p, ∑ q, (D n i k * D n p q - D n i q * D n p k) * (D n j l * D n p q - D n j q * D n p l)
      = ((n : ℝ) - 2) * (D n i k * D n j l) + D n i j * D n k l := by
  have hpt : ∀ p q : Fin n,
      (D n i k * D n p q - D n i q * D n p k) * (D n j l * D n p q - D n j q * D n p l)
      = (D n i k * D n j l) * (D n p q * D n p q) - D n i k * (D n p q * D n p l * D n j q)
        - D n j l * (D n p q * D n p k * D n i q) + (D n p k * D n p l) * (D n i q * D n j q) := by
    intro p q; ring
  rw [show (∑ p, ∑ q,
        (D n i k * D n p q - D n i q * D n p k) * (D n j l * D n p q - D n j q * D n p l))
        = (∑ p, ∑ q,
            ((D n i k * D n j l) * (D n p q * D n p q) - D n i k * (D n p q * D n p l * D n j q)
              - D n j l * (D n p q * D n p k * D n i q) + (D n p k * D n p l) * (D n i q * D n j q)))
      from Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
  rw [sum4]
  simp only [pullconst2, factor2]
  rw [sum_D_sq, triple l j, triple k i, sum_D_col k l, sum_D_row i j]
  ring

/-- The `∑_{p,q} Iso i p l q · Iso j p k q` part of `Q` (obtained from `S2` by `k ↔ l`). -/
private lemma S3 {n : ℕ} (i j k l : Fin n) :
    ∑ p, ∑ q, (D n i l * D n p q - D n i q * D n p l) * (D n j k * D n p q - D n j q * D n p k)
      = ((n : ℝ) - 2) * (D n i l * D n j k) + D n i j * D n k l := by
  have h := S2 (n := n) i j l k
  rw [D_symm l k] at h
  exact h

/-- **Sign sanity check (s1).** Hamilton's reaction term on the curvature of the unit round sphere
(`Iso n i j k l = δᵢₖδⱼₗ − δᵢₗδⱼₖ`) is `2 (n − 1) • Iso n`: the two "cross" contributions each give
`(n−2)(δᵢₖδⱼₗ − δᵢₗδⱼₖ)` and `∑_{p,q} Iso i j p q * Iso k l p q = 2 Iso i j k l`, which certifies
the normalisation of `Q` (hence the sign and factor in the curvature ODE). -/
theorem Q_Iso (n : ℕ) : Q (Iso n) = (2 * ((n : ℝ) - 1)) • Iso n := by
  funext i j k l
  simp only [Q, Pi.smul_apply, smul_eq_mul, Iso_eq_D]
  simp only [mul_assoc]
  rw [sum_lin]
  rw [S1 i j k l, S2 i j k l, S3 i j k l]
  ring

end Work.Diff.PP
