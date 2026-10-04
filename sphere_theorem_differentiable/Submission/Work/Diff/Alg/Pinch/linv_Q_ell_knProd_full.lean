import Mathlib
import Submission.Work.Diff.Alg.Pinch.BWDefs
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.BQDefs
import Submission.Work.Diff.Alg.Pinch.ric_Q
import Submission.Work.Diff.Alg.Pinch.scalAlg_Q
import Submission.Work.Diff.Alg.Pinch.ell_isAlgCurv
import Submission.Work.Diff.Alg.Pinch.Q_knProd_aux
import Submission.Work.Diff.Alg.Pinch.ric_knProd_id2
import Submission.Work.Diff.Alg.Pinch.scalAlg_knProd
import Submission.Work.Diff.Alg.Pinch.Q_knProd_apply
import Submission.Work.Diff.Alg.Pinch.lqkDefs
import Submission.Work.Diff.Alg.Pinch.ricQ_knProd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Böhm–Wilking identity in the Ricci-type family `A ∧ id`

Böhm–Wilking, *Manifolds with positive curvature operators are space forms* (arXiv math/0606187),
Theorem 2, in the case of a curvature tensor of "Ricci type", `R = A ∧ id`:

`linv a b (Q (ell a b (A ∧ id))) = Q (A ∧ id) + bwCorr a b (A ∧ id)`  for a symmetric `2`-tensor `A`.

This is the key computational input of the reduction `bwDef_of_children`: adding a Weyl tensor does
not change the difference `bwDef`, so the general identity follows from this one.

## Structure of the proof

Everything is pushed onto the `2`-tensor level.

* `ell a b (A ∧ id) = Ã ∧ id` with `Ã = (1 + (n-2)b)·A + ((2a(n-1) - b(n-2))/n · tr A)·id`
  (`ell_knProd_id2`): indeed `ric0 (A ∧ id) = (n-2)·(A - (tr A/n) id)` and
  `scal (A ∧ id) = 2(n-1) tr A`, and `knProd` is linear in its first slot.
* Hamilton's reaction term on a Ricci-type tensor is (Böhm–Wilking Lemma 2.2, here
  `Q_knProd_apply`)
  `Q (C ∧ id) = -2 · (C Cᵀ) ∧ id + (n-2) · C ∧ C + 2 (tr C) · C ∧ id + |C|² · (id ∧ id)`;
  contracting gives `ric (Q (C ∧ id)) = 4(n-2)tr C · C - 4(n-2) · C Cᵀ + 2((tr C)² + (n-2)|C|²)·id`
  and `scal (Q (C ∧ id)) = 2((3n-4)(tr C)² + (n-2)²|C|²)` (`ricQ_knProd`).
* Substituting into the definition of `linv` yields the explicit form `lqef_linv_Q_knProd`.
* `bwCorr a b (A ∧ id)` is expanded into the same four basis tensors (`lqef_bwCorr_knProd`), and
  the two sides are compared componentwise.

The final comparison is a polynomial identity in the entries of `A`, `A Aᵀ`, `id`, `tr A` and
`|A|²`, after clearing the three denominators `1 + (n-2)b`, `1 + 2(n-1)a` and `n`.
-/

set_option maxRecDepth 100000

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Bilinearity of the Kulkarni–Nomizu product in its second slot -/

lemma lqef_knProd_smul_right (c : ℝ) (P Q : Fin n → Fin n → ℝ) :
    knProd P (c • Q) = c • knProd P Q := by
  funext i j k l
  simp only [knProd, Pi.smul_apply, smul_eq_mul]
  ring

/-- The Kulkarni–Nomizu product is symmetric in its two arguments for any `2`-tensor:
`id2 n ∧ A = A ∧ id2 n`. -/
lemma lqef_knProd_id_comm (A : Fin n → Fin n → ℝ) :
    knProd (id2 n) A = knProd A (id2 n) := by
  funext i j k l
  simp only [knProd]
  ring

/-- `knProd` is linear in its first slot when the second slot is `id2 n`. -/
lemma lqef_knProd_lin1 (p q : ℝ) (P Q : Fin n → Fin n → ℝ) :
    knProd (p • P + q • Q) (id2 n) = p • knProd P (id2 n) + q • knProd Q (id2 n) := by
  rw [knProd_add_left_linv, knProd_smul_left_linv, knProd_smul_left_linv]

/-- The three-term version of `lqef_knProd_lin1`. -/
lemma lqef_knProd_lin3 (p q r : ℝ) (P Q R : Fin n → Fin n → ℝ) :
    knProd (p • P + q • Q + r • R) (id2 n)
      = p • knProd P (id2 n) + q • knProd Q (id2 n) + r • knProd R (id2 n) := by
  rw [knProd_add_left_linv, lqef_knProd_lin1, knProd_smul_left_linv]

/-! ## The `2`-tensor invariants of an affine combination `p·P + q·id` -/

lemma lqef_trM_add (P Q : Fin n → Fin n → ℝ) : trM (P + Q) = trM P + trM Q := by
  simp only [trM, Pi.add_apply, Finset.sum_add_distrib]

lemma lqef_trM_smul (c : ℝ) (P : Fin n → Fin n → ℝ) : trM (c • P) = c * trM P := by
  simp only [trM, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma lqef_trM_affine (p q : ℝ) (P : Fin n → Fin n → ℝ) :
    trM (p • P + q • id2 n) = p * trM P + q * (n : ℝ) := by
  rw [lqef_trM_add, lqef_trM_smul, lqef_trM_smul, trM_id2]

lemma lqef_s2m_affine {P : Fin n → Fin n → ℝ} (hP : ∀ i j, P i j = P j i) (p q : ℝ) :
    s2m (p • P + q • id2 n) = (p ^ 2) • s2m P + (2 * p * q) • P + (q ^ 2) • id2 n := by
  funext i j
  have hL : s2m (p • P + q • id2 n) i j
      = ∑ k, (p * P i k + q * id2 n i k) * (p * P j k + q * id2 n j k) := by
    simp only [s2m, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hL]
  have hterm : ∀ k : Fin n,
      (p * P i k + q * id2 n i k) * (p * P j k + q * id2 n j k)
        = p ^ 2 * (P i k * P j k) + (p * q) * (P i k * id2 n j k)
          + (p * q) * (id2 n i k * P j k) + q ^ 2 * (id2 n i k * id2 n j k) := by
    intro k; ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  simp only [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [sum_id2_id2, sum_id2_mul (fun k => P j k) i]
  rw [show (∑ k, P i k * id2 n j k) = P i j from by
    rw [show (∑ k, P i k * id2 n j k) = ∑ k, P i k * id2 n k j from
      Finset.sum_congr rfl (fun k _ => by rw [id2_symm j k])]
    exact sum_mul_id2 (fun k => P i k) j]
  rw [hP j i]
  simp only [s2m, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma lqef_frb_affine (p q : ℝ) (P : Fin n → Fin n → ℝ) :
    frb (p • P + q • id2 n) = p ^ 2 * frb P + 2 * p * q * trM P + (n : ℝ) * q ^ 2 := by
  have hterm : ∀ i j : Fin n, (p * P i j + q * id2 n i j) * (p * P i j + q * id2 n i j)
      = p ^ 2 * (P i j * P i j) + (2 * p * q) * (P i j * id2 n i j)
        + q ^ 2 * (id2 n i j * id2 n i j) := by
    intro i j; ring
  have h1 : (∑ i, ∑ j, p ^ 2 * (P i j * P i j))
      = p ^ 2 * (∑ i, ∑ j, P i j * P i j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  have hinner : ∀ i : Fin n,
      (∑ j, (2 * p * q) * (P i j * id2 n i j)) = (2 * p * q) * P i i := by
    intro i
    rw [← Finset.mul_sum]
    congr 1
    rw [show (∑ j, P i j * id2 n i j) = ∑ j, P i j * id2 n j i from
      Finset.sum_congr rfl (fun j _ => by rw [id2_symm i j])]
    exact sum_mul_id2 (fun j => P i j) i
  have h2 : (∑ i, ∑ j, (2 * p * q) * (P i j * id2 n i j)) = 2 * p * q * trM P := by
    rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    rw [← Finset.mul_sum, trM]
  have h3 : (∑ i, ∑ j, q ^ 2 * (id2 n i j * id2 n i j))
      = q ^ 2 * (∑ i, ∑ j, id2 n i j * id2 n i j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  simp only [frb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))]
  simp only [Finset.sum_add_distrib]
  rw [h1, h2, h3, sum_id2_sq]
  ring

/-! ## `ell` on the Ricci-type family -/

/-- `ell a b (A ∧ id) = Ã ∧ id` with `Ã = (1 + (n-2)b)·A + ((2a(n-1) - b(n-2))/n · tr A)·id`. -/
lemma lqef_ell_knProd (n : ℕ) (a b : ℝ) (hn : (n : ℝ) ≠ 0) (A : Fin n → Fin n → ℝ) :
    ell a b (knProd A (id2 n))
      = knProd ((1 + ((n : ℝ) - 2) * b) • A
          + (((2 * a * ((n : ℝ) - 1) - b * ((n : ℝ) - 2)) / (n : ℝ)) * trM A) • id2 n)
          (id2 n) := by
  have hric0 : ric0 (knProd A (id2 n))
      = ((n : ℝ) - 2) • A + (-(((n : ℝ) - 2) * (trM A / (n : ℝ)))) • id2 n := by
    funext i j
    rw [ric0_knProd hn i j]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hscal : scalAlg (knProd A (id2 n)) = (2 * (n : ℝ) - 2) * trM A := scalAlg_knProd_id A
  rw [ell, hric0, hscal, lqef_knProd_lin1, lqef_knProd_lin1]
  funext i j k l
  simp only [knProd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## `linv a b (Q (X ∧ id))` for symmetric `X` -/

/-- The explicit form of `linv a b (Q (X ∧ id))` for a symmetric `2`-tensor `X`. -/
theorem lqef_linv_Q_knProd (n : ℕ) (a b : ℝ) {X : Fin n → Fin n → ℝ}
    (hX : ∀ i j, X i j = X j i) :
    linv a b (Q (knProd X (id2 n)))
      = ((n : ℝ) - 2) • knProd X X
        + (2 * trM X - (b / (1 + ((n : ℝ) - 2) * b)) * (4 * ((n : ℝ) - 2) * trM X))
            • knProd X (id2 n)
        + (-2 + (b / (1 + ((n : ℝ) - 2) * b)) * (4 * ((n : ℝ) - 2))) • knProd (s2m X) (id2 n)
        + (frb X
            - (b / (1 + ((n : ℝ) - 2) * b))
                * (2 * ((trM X) ^ 2 + ((n : ℝ) - 2) * frb X)
                    - (2 * ((3 * (n : ℝ) - 4) * (trM X) ^ 2 + ((n : ℝ) - 2) ^ 2 * frb X))
                        / (n : ℝ))
            - ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a))
                * (2 * ((3 * (n : ℝ) - 4) * (trM X) ^ 2 + ((n : ℝ) - 2) ^ 2 * frb X)))
          • knProd (id2 n) (id2 n) := by
  have hQ : Q (knProd X (id2 n))
      = (-2 : ℝ) • knProd (s2m X) (id2 n) + ((n : ℝ) - 2) • knProd X X
        + (2 * trM X) • knProd X (id2 n) + (frb X) • knProd (id2 n) (id2 n) :=
    Q_knProd_apply n hX
  have hric0 : ric0 (Q (knProd X (id2 n)))
      = (4 * ((n : ℝ) - 2) * trM X) • X + (-(4 * ((n : ℝ) - 2))) • s2m X
        + (2 * ((trM X) ^ 2 + ((n : ℝ) - 2) * frb X)
            - (2 * ((3 * (n : ℝ) - 4) * (trM X) ^ 2 + ((n : ℝ) - 2) ^ 2 * frb X))
                / (n : ℝ)) • id2 n := by
    funext i j
    rw [ric0, ric_Q_knProd_apply n hX i j, scalAlg_Q_knProd_apply n hX]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [linv, hric0, scalAlg_Q_knProd_apply n hX, hQ]
  rw [lqef_knProd_lin3]
  funext i j k l
  simp only [knProd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## `bwCorr` on the Ricci-type family -/

/-- The expansion of the Böhm–Wilking correction tensor of `A ∧ id` in the four basis tensors
`A ∧ A`, `A ∧ id`, `(A Aᵀ) ∧ id`, `id ∧ id`. -/
lemma lqef_bwCorr_knProd (n : ℕ) (a b : ℝ) (hn : (n : ℝ) ≠ 0) {A : Fin n → Fin n → ℝ}
    (hA : ∀ i j, A i j = A j i) :
    bwCorr a b (knProd A (id2 n))
      = (((n : ℝ) - 2) * b ^ 2 - 2 * (a - b)) •
          knProd (((n : ℝ) - 2) • A + (-(((n : ℝ) - 2) * (trM A / (n : ℝ)))) • id2 n)
                 (((n : ℝ) - 2) • A + (-(((n : ℝ) - 2) * (trM A / (n : ℝ)))) • id2 n)
        + (2 * a) • knProd (((n : ℝ) - 2) • A + (trM A) • id2 n)
                            (((n : ℝ) - 2) • A + (trM A) • id2 n)
        + (2 * b ^ 2) • knProd ((((n : ℝ) - 2) ^ 2) • s2m A
              + (-(2 * ((n : ℝ) - 2) ^ 2 * (trM A / (n : ℝ)))) • A
              + (((n : ℝ) - 2) ^ 2 * (trM A / (n : ℝ)) ^ 2) • id2 n) (id2 n)
        + ((((n : ℝ) * b ^ 2 * (1 - 2 * b) - 2 * (a - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
              / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a)))
            * (((n : ℝ) - 2) ^ 2 * (frb A - (trM A) ^ 2 / (n : ℝ)))) • knProd (id2 n) (id2 n) := by
  have h1 : ric0 (knProd A (id2 n))
      = ((n : ℝ) - 2) • A + (-(((n : ℝ) - 2) * (trM A / (n : ℝ)))) • id2 n := by
    funext i j
    rw [ric0_knProd hn i j]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : ric (knProd A (id2 n)) = ((n : ℝ) - 2) • A + (trM A) • id2 n := by
    funext i j
    rw [ric_knProd_id A i j]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h3 : ric0sq (knProd A (id2 n))
      = (((n : ℝ) - 2) ^ 2) • s2m A + (-(2 * ((n : ℝ) - 2) ^ 2 * (trM A / (n : ℝ)))) • A
        + (((n : ℝ) - 2) ^ 2 * (trM A / (n : ℝ)) ^ 2) • id2 n := by
    funext i j
    rw [ric0sq_knProd hA hn i j]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h4 : ric0Frob2 (knProd A (id2 n))
      = ((n : ℝ) - 2) ^ 2 * (frb A - (trM A) ^ 2 / (n : ℝ)) := ric0Frob2_knProd hn
  rw [bwCorr, h1, h2, h3, h4]

/-! ## The main theorem -/

/-- **The Böhm–Wilking identity in the Ricci-type family** (Böhm–Wilking Theorem 2 for
`R = A ∧ id`): for a symmetric `2`-tensor `A`,

`linv a b (Q (ell a b (A ∧ id))) = Q (A ∧ id) + bwCorr a b (A ∧ id)`.

This is the input `hrt` of `bwDef_of_children`. -/
theorem linv_Q_ell_knProd_full (n : ℕ) (a b : ℝ)
    (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0) (hb : 1 + ((n : ℝ) - 2) * b ≠ 0)
    {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) :
    Work.Diff.Alg.Pinch.linv a b (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a b (Work.Diff.Alg.Pinch.knProd A (Work.Diff.Alg.Pinch.id2 n))))
      = Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.knProd A (Work.Diff.Alg.Pinch.id2 n))
        + Work.Diff.Alg.Pinch.bwCorr a b (Work.Diff.Alg.Pinch.knProd A (Work.Diff.Alg.Pinch.id2 n)) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    funext i j k l
    exact Fin.elim0 i
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
  set X : Fin n → Fin n → ℝ :=
    (1 + ((n : ℝ) - 2) * b) • A
      + (((2 * a * ((n : ℝ) - 1) - b * ((n : ℝ) - 2)) / (n : ℝ)) * trM A) • id2 n with hXdef
  have hXs : ∀ i j, X i j = X j i := by
    intro i j
    rw [hXdef]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hA i j, id2_symm i j]
  have hell : ell a b (knProd A (id2 n)) = knProd X (id2 n) := by
    rw [hXdef]
    exact lqef_ell_knProd n a b hn A
  rw [hell, lqef_linv_Q_knProd n a b hXs]
  -- substitute `X` and its invariants, and expand `knProd` over the affine combinations
  rw [hXdef, lqef_s2m_affine hA, lqef_trM_affine, lqef_frb_affine]
  simp only [knProd_add_left_linv, knProd_smul_left_linv, knProd_add_right,
    lqef_knProd_smul_right, lqef_knProd_id_comm]
  -- the right-hand side
  rw [Q_knProd_apply n hA, lqef_bwCorr_knProd n a b hn hA]
  simp only [knProd_add_left_linv, knProd_smul_left_linv, knProd_add_right,
    lqef_knProd_smul_right, lqef_knProd_id_comm]
  simp only [smul_add, smul_sub, add_smul, sub_smul, smul_smul, one_smul]
  -- compare the coefficients of the four monomials `A ∧ A`, `A ∧ id`, `(A Aᵀ) ∧ id`, `id ∧ id`
  funext i j k l
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  -- the non-vanishing of the three denominators, in the normal forms `field_simp` produces
  have ha1 : 1 + 2 * a * ((n : ℝ) - 1) ≠ 0 := by
    have h : (1 + 2 * a * ((n : ℝ) - 1)) = 1 + 2 * ((n : ℝ) - 1) * a := by ring
    rw [h]; exact ha
  have ha2 : 1 + (n : ℝ) * a * 2 - a * 2 ≠ 0 := by
    have h : (1 + (n : ℝ) * a * 2 - a * 2) = 1 + 2 * ((n : ℝ) - 1) * a := by ring
    rw [h]; exact ha
  have hb1 : 1 + b * ((n : ℝ) - 2) ≠ 0 := by
    have h : (1 + b * ((n : ℝ) - 2)) = 1 + ((n : ℝ) - 2) * b := by ring
    rw [h]; exact hb
  have hb2 : 1 + (n : ℝ) * b - b * 2 ≠ 0 := by
    have h : (1 + (n : ℝ) * b - b * 2) = 1 + ((n : ℝ) - 2) * b := by ring
    rw [h]; exact hb
  have hb3 : 1 + (n : ℝ) * b - 2 * b ≠ 0 := by
    have h : (1 + (n : ℝ) * b - 2 * b) = 1 + ((n : ℝ) - 2) * b := by ring
    rw [h]; exact hb
  have hna : (n : ℝ) * (1 + (n : ℝ) * a * 2 - a * 2) ≠ 0 := mul_ne_zero hn ha2
  have hba : (1 + (n : ℝ) * b - b * 2) * (1 + (n : ℝ) * a * 2 - a * 2) ≠ 0 := mul_ne_zero hb2 ha2
  have hba1 : (1 + b * ((n : ℝ) - 2)) * (1 + 2 * a * ((n : ℝ) - 1)) ≠ 0 := mul_ne_zero hb1 ha1
  field_simp
  ring

end Work.Diff.Alg.Pinch
