import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Strict
import Submission.Work.Diff.Alg.Pinch.ell_inv
import Submission.Work.Diff.Alg.Pinch.ell_isAlgCurv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The explicit inverse `linv a b` of the Böhm–Wilking transform `ell a b`

`ell a b R = R + b • (Ric₀ R ∧ id) + (a/n · scal R) • (id ∧ id)` is the Böhm–Wilking linear
transformation used to build the cones `Ccone a b p = ell a b '' Dpic p`.  It is invertible
whenever `1 + 2(n-1)a ≠ 0` and `1 + (n-2)b ≠ 0`, the inverse being

`linv a b Y = Y - (b/(1+(n-2)b)) • (Ric₀ Y ∧ id) - ((a/n)/(1+2(n-1)a) · scal Y) • (id ∧ id)`.

This is exactly the explicit right inverse from `Work.Diff.Alg.Pinch.ell_inv`; here we package it
as a *definition* and record the two inverse identities, together with the linearity that lets one
push `linv` through the one-step map `R ↦ R + s • Q R` of Hamilton's ODE.

The reason `linv` matters for the target statement

`R ∈ Ccone a b p → R + s • Q R ∈ CconeS a b p`

(for small `s`): `CconeS a b p = ell a b '' DpicS p`, so the goal is to exhibit `S' ∈ DpicS p` with
`ell a b S' = R + s • Q R`.  Writing `R = ell a b S` with `S ∈ Dpic p`, the candidate is
`S' = S + s • linv a b (Q (ell a b S))`: the statement is thereby pushed into the `Dpic`-picture,
which decouples the Böhm–Wilking transform from the ODE.

## Contents

* `linv`, `ric0sq`, `ric0Frob2`;
* linearity of `ric0`, `scalAlg`, `knProd`, `linv`;
* `ell_linv : ell a b (linv a b Y) = Y` for `Y` an algebraic curvature tensor;
* `linv_ell : linv a b (ell a b S) = S`, together with
  `ric0 (ell a b R) = (1 + (n-2)b) • ric0 R` and `scal (ell a b R) = (1 + 2(n-1)a) · scal R`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The explicit inverse of the Böhm–Wilking transformation `ell a b`
(see `Work.Diff.Alg.Pinch.ell_inv`):

`linv a b Y = Y - (b/(1+(n-2)b)) • (Ric₀ Y ∧ id) - ((a/n)/(1+2(n-1)a) · scal Y) • (id ∧ id)`. -/
noncomputable def linv (a b : ℝ) (Y : Curv4 n) : Curv4 n :=
  Y - (b / (1 + ((n : ℝ) - 2) * b)) • knProd (ric0 Y) (id2 n)
    - ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y) • knProd (id2 n) (id2 n)

/-- The square of the traceless Ricci tensor, `ric0sq R i j = ∑ k, ric0 R i k * ric0 R k j`. -/
noncomputable def ric0sq (Y : Curv4 n) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k, ric0 Y i k * ric0 Y k j

/-- The squared Frobenius norm of the traceless Ricci tensor. -/
noncomputable def ric0Frob2 (Y : Curv4 n) : ℝ := ∑ i, ∑ j, ric0 Y i j * ric0 Y i j

/-! ## Linearity of the ingredients -/

section Linearity

lemma ric_add_linv (A B : Curv4 n) (i j : Fin n) : ric (A + B) i j = ric A i j + ric B i j := by
  simp only [ric, Pi.add_apply, Finset.sum_add_distrib]

lemma ric_sub (A B : Curv4 n) (i j : Fin n) : ric (A - B) i j = ric A i j - ric B i j :=
  ellinv_ric_sub A B i j

lemma ric_smul_linv (c : ℝ) (A : Curv4 n) (i j : Fin n) : ric (c • A) i j = c * ric A i j :=
  ellinv_ric_smul c A i j

lemma scalAlg_add_linv (A B : Curv4 n) : scalAlg (A + B) = scalAlg A + scalAlg B := by
  simp only [scalAlg, Pi.add_apply, Finset.sum_add_distrib]

lemma scalAlg_sub (A B : Curv4 n) : scalAlg (A - B) = scalAlg A - scalAlg B :=
  ellinv_scalAlg_sub A B

lemma scalAlg_smul_linv (c : ℝ) (A : Curv4 n) : scalAlg (c • A) = c * scalAlg A :=
  ellinv_scalAlg_smul c A

lemma ric0_add_apply (A B : Curv4 n) (i j : Fin n) : ric0 (A + B) i j = ric0 A i j + ric0 B i j := by
  simp only [ric0, ric_add_linv, scalAlg_add_linv]
  ring

lemma ric0_sub (A B : Curv4 n) (i j : Fin n) : ric0 (A - B) i j = ric0 A i j - ric0 B i j := by
  simp only [ric0, ric_sub, scalAlg_sub]
  ring

lemma ric0_smul_linv (c : ℝ) (A : Curv4 n) (i j : Fin n) : ric0 (c • A) i j = c * ric0 A i j := by
  simp only [ric0, ric_smul_linv, scalAlg_smul_linv]
  ring

lemma ric0_add' (A B : Curv4 n) : ric0 (A + B) = ric0 A + ric0 B := by
  funext i j; simp only [ric0, Pi.add_apply, ric_add_linv, scalAlg_add_linv]; ring

lemma ric0_sub' (A B : Curv4 n) : ric0 (A - B) = ric0 A - ric0 B := by
  funext i j; simp only [ric0, Pi.sub_apply, ric_sub, scalAlg_sub]; ring

lemma ric0_smul' (c : ℝ) (A : Curv4 n) : ric0 (c • A) = c • ric0 A := by
  funext i j; simp only [ric0, Pi.smul_apply, ric_smul_linv, scalAlg_smul_linv, smul_eq_mul]; ring

lemma knProd_add_left_linv (A B C : Fin n → Fin n → ℝ) :
    knProd (A + B) C = knProd A C + knProd B C := by
  funext i j k l
  simp only [knProd, Pi.add_apply]
  ring

lemma knProd_sub_left (A B C : Fin n → Fin n → ℝ) :
    knProd (A - B) C = knProd A C - knProd B C := by
  funext i j k l
  simp only [knProd, Pi.sub_apply]
  ring

lemma knProd_smul_left_linv (c : ℝ) (A C : Fin n → Fin n → ℝ) :
    knProd (c • A) C = c • knProd A C :=
  ellinv_knProd_smul_left c A C

lemma knProd_add_right (A B C : Fin n → Fin n → ℝ) :
    knProd A (B + C) = knProd A B + knProd A C := by
  funext i j k l
  simp only [knProd, Pi.add_apply]
  ring

lemma knProd_sub_right (A B C : Fin n → Fin n → ℝ) :
    knProd A (B - C) = knProd A B - knProd A C := by
  funext i j k l
  simp only [knProd, Pi.sub_apply]
  ring

/-- `linv a b` is additive. -/
lemma linv_add (a b : ℝ) (Y Z : Curv4 n) : linv a b (Y + Z) = linv a b Y + linv a b Z := by
  rw [linv, linv, linv, ric0_add', scalAlg_add_linv, knProd_add_left_linv]
  rw [smul_add, mul_add, add_smul]
  abel

/-- `linv a b` is negatively additive. -/
lemma linv_sub (a b : ℝ) (Y Z : Curv4 n) : linv a b (Y - Z) = linv a b Y - linv a b Z := by
  rw [linv, linv, linv, ric0_sub', scalAlg_sub, knProd_sub_left]
  rw [smul_sub, mul_sub, sub_smul]
  abel

/-- `linv a b` is homogeneous. -/
lemma linv_smul (a b : ℝ) (c : ℝ) (Y : Curv4 n) : linv a b (c • Y) = c • linv a b Y := by
  rw [linv, linv, ric0_smul', scalAlg_smul_linv, knProd_smul_left_linv, smul_sub, smul_sub, smul_smul,
    smul_smul]
  have e1 : (b / (1 + ((n : ℝ) - 2) * b)) * c = c * (b / (1 + ((n : ℝ) - 2) * b)) := by ring
  have e2 : (a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * (c * scalAlg Y)
      = c * ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y) := by ring
  rw [e1, e2, smul_smul]

end Linearity

/-! ## The inverse identities -/

/-- `linv a b` is a right inverse of `ell a b` on algebraic curvature tensors. -/
theorem ell_linv (n : ℕ) {a b : ℝ} (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) {Y : Curv4 n} (hY : IsAlgCurv Y) :
    ell a b (linv a b Y) = Y :=
  ell_inv n ha hb hY

/-- The scalar curvature scales by `1 + 2(n-1)a` under `ell a b`. -/
theorem scalAlg_ell_of_ne (n : ℕ) (a b : ℝ) (hn : ((n : ℝ)) ≠ 0) {R : Curv4 n}
    (hR : IsAlgCurv R) :
    scalAlg (ell a b R) = (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg R := by
  rw [ell, scalAlg_add_linv, scalAlg_add_linv, scalAlg_smul_linv, scalAlg_smul_linv, ellinv_scalAlg_knProd_ric0 hR,
    ellinv_scalAlg_knProd_id2_id2 n]
  field_simp
  ring

/-- The scalar identity behind `ric0_ell_linv`. -/
lemma ric0_ell_arith {n : ℕ} (hn : ((n : ℝ)) ≠ 0) (a b r s d : ℝ) :
    r + b * (((n : ℝ) - 2) * (r - s / (n : ℝ) * d)) + (a / (n : ℝ) * s) * ((2 * (n : ℝ) - 2) * d)
      - ((1 + 2 * ((n : ℝ) - 1) * a) * s / (n : ℝ)) * d
    = (1 + ((n : ℝ) - 2) * b) * (r - s / (n : ℝ) * d) := by
  field_simp
  ring

/-- `Ric₀` scales by `1 + (n-2)b` under `ell a b`. -/
theorem ric0_ell_linv (n : ℕ) (a b : ℝ) (hn : ((n : ℝ)) ≠ 0) {R : Curv4 n} (hR : IsAlgCurv R)
    (i j : Fin n) :
    ric0 (ell a b R) i j = (1 + ((n : ℝ) - 2) * b) * ric0 R i j := by
  · have hric : ric (ell a b R) i j
        = ric R i j + b * (((n : ℝ) - 2) * ric0 R i j)
          + (a / (n : ℝ) * scalAlg R) * ((2 * (n : ℝ) - 2) * id2 n i j) := by
      rw [ell, ric_add_linv, ric_add_linv, ric_smul_linv, ric_smul_linv, ellinv_ric_knProd_ric0 hR,
        ellinv_ric_knProd_id2_id2]
    have hscal : scalAlg (ell a b R) = (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg R :=
      scalAlg_ell_of_ne n a b hn hR
    simp only [ric0] at *
    rw [hric, hscal]
    exact ric0_ell_arith hn a b (ric R i j) (scalAlg R) (id2 n i j)

/-- `linv a b` is a left inverse of `ell a b` on algebraic curvature tensors. -/
theorem linv_ell (n : ℕ) {a b : ℝ} (hn : ((n : ℝ)) ≠ 0)
    (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) {S : Curv4 n} (hS : IsAlgCurv S) :
    linv a b (ell a b S) = S := by
  have hric : ric0 (ell a b S) = (1 + ((n : ℝ) - 2) * b) • ric0 S := by
    funext p q
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ric0_ell_linv n a b hn hS p q
  have hscal : scalAlg (ell a b S) = (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg S :=
    scalAlg_ell_of_ne n a b hn hS
  have hbk : (b / (1 + ((n : ℝ) - 2) * b)) * (1 + ((n : ℝ) - 2) * b) = b :=
    div_mul_cancel₀ b hb
  have hak2 : (a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * ((1 + 2 * ((n : ℝ) - 1) * a)
      * scalAlg S) = a / (n : ℝ) * scalAlg S := by
    rw [← mul_assoc, div_mul_cancel₀ _ ha]
  rw [linv, hric, hscal, knProd_smul_left_linv]
  rw [smul_smul, hbk, hak2]
  rw [ell]
  abel

/-- The `a`-parameter of the Böhm–Wilking family with `0 < b ≤ 1/2` (Brendle–Schoen Prop. 13). -/
noncomputable def ccA (n : ℕ) (b : ℝ) : ℝ :=
  (2 * b + ((n : ℝ) - 2) * b ^ 2) / (2 * (1 + ((n : ℝ) - 2) * b ^ 2))

/-- The `p`-parameter of the Böhm–Wilking family with `0 < b ≤ 1/2` (Brendle–Schoen Prop. 13). -/
noncomputable def ccP (n : ℕ) (b : ℝ) : ℝ := 1 - 1 / (1 + ((n : ℝ) - 2) * b ^ 2)

lemma ccA_pos {n : ℕ} (hn : 1 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    0 < ccA n b := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : (0 : ℝ) < 2 + ((n : ℝ) - 2) * b := by nlinarith
  have h3 : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b ^ 2 := by nlinarith [sq_nonneg b]
  rw [ccA]
  apply div_pos
  · nlinarith
  · linarith

lemma ccA_denom_ne {n : ℕ} (hn : 1 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    1 + 2 * ((n : ℝ) - 1) * ccA n b ≠ 0 := by
  have ha := ccA_pos hn hb hb'
  rcases Nat.lt_or_ge n 2 with h | h
  · -- n = 1
    have : (n : ℝ) = 1 := by
      have : n = 1 := by omega
      exact_mod_cast this
    rw [this]; norm_num
  · have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    nlinarith

lemma ccP_denom_pos {n : ℕ} (hn : 1 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    0 < 1 + ((n : ℝ) - 2) * b ^ 2 := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [sq_nonneg b, sq_nonneg (b - 1 / 2), sq_nonneg (b + 1 / 2)]

/-- `ccP n b` is nonnegative in the range `n ≥ 2`. -/
lemma ccP_nn {n : ℕ} (hn2 : 2 ≤ n) {b : ℝ} : 0 ≤ ccP n b := by
  rw [ccP]
  have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hge : 1 ≤ 1 + ((n : ℝ) - 2) * b ^ 2 := by nlinarith [sq_nonneg b]
  have hpos : 0 < 1 + ((n : ℝ) - 2) * b ^ 2 := by linarith
  have h1 : 1 / (1 + ((n : ℝ) - 2) * b ^ 2) ≤ 1 := (div_le_one hpos).mpr hge
  linarith

lemma ccP_lt_one {n : ℕ} (hn : 1 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    ccP n b < 1 := by
  rw [ccP]
  have h := ccP_denom_pos hn hb hb'
  have : 0 < 1 / (1 + ((n : ℝ) - 2) * b ^ 2) := by positivity
  linarith

/-- The Böhm–Wilking `b`-denominator is nonzero in the range used here. -/
lemma ccB_denom_ne {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    1 + ((n : ℝ) - 2) * b ≠ 0 := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

/-- A difference of algebraic curvature tensors is algebraic. -/
lemma isAlgCurv_sub {R S : Curv4 n} (hR : IsAlgCurv R) (hS : IsAlgCurv S) :
    IsAlgCurv (R - S) := by
  have h : R - S = R + (-1 : ℝ) • S := by
    funext i j k l
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  exact isAlgCurv_add hR (isAlgCurv_smul (-1) hS)

end Work.Diff.Alg.Pinch
