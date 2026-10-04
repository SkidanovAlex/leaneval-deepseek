import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Strict
import Submission.Work.Diff.Alg.Pinch.EFun_a_defs
import Submission.Work.Diff.Alg.Pinch.BQDefs
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic
import Submission.Work.Diff.Alg.Pinch.inPIC2_Q_pointwise
import Submission.Work.Diff.Alg.Pinch.linv_Q_ell
import Submission.Work.Diff.Alg.Pinch.EFun_knProd_psd
import Submission.Work.Diff.Alg.Pinch.ric0Frob2_le
import Submission.Work.Diff.Alg.Pinch.scalAlg_pos_of_inPIC2_ricpinch
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `a > 1/2` branch: strict positivity at degenerate directions

Target: `Work.Diff.Alg.Pinch.ChatT_strict_pic_a`, the pointwise strictness statement of Brendle–Schoen
Proposition 14 (after Böhm–Wilking Lemma 3.5), in the `b = 1/2` branch of the pinching family.

With `s = 2a-1`, `p = 1 - 4/((n-2) + 8a) = 1 - 4/(n+2+4s)`, `λ̄ = scal S / n`, `R₀ = Ric₀ S = ric0 S`
and
`X = linv a (1/2) (Q (ell a (1/2) S))`,

the Böhm–Wilking identity (`Work.Diff.Alg.Pinch.BW_identity`, Theorem 2 of Böhm–Wilking) writes
`X = Q S + D_{a,1/2}(S)` with

`D_{a,1/2}(S) = ((n+2)/4)·(A ∧ A) + (2 s λ̄)·(B ∧ id) + (1/2)·(Ric₀² ∧ id) + γ·(id ∧ id)`,

where `A = Ric₀ S + 4λ̄/(n+2)·id`, `B = Ric₀ S + 4λ̄/(n+2+4s)·id = Ric S - p λ̄ · id` and

`γ = λ̄²·((n-2)/(n+2) + s(n-6+4s)/(n+2+4s)) - s·|Ric₀|²/(4(n + (n-1)s))`.

The Ricci pinching makes `A`, `B` and `Ric₀²` positive semidefinite (`B` is exactly the pinching,
`A` the weaker pinching `Ric ≥ ((n-2)/(n+2)) λ̄`), so the Kulkarni–Nomizu products `A ∧ A`,
`B ∧ id`, `Ric₀² ∧ id` are nonnegative on the cone of decomposable complex `2`-forms; the
`γ`-coefficient of `id ∧ id = 2 • Iso n` is strictly positive by the Böhm–Wilking estimate
`|Ric₀|² ≤ n(n-1)(1-p)²λ̄²` (valid because `Ric ≥ p λ̄ id`) together with an elementary inequality.
Since `Q S` also has nonnegative complex sectional curvature (`inPIC2_Q_pointwise`), `X` is
strictly positive in every direction with `EFun (Iso n) x y z w ≠ 0`.

This file contains the algebraic decomposition of `bwCorr a (1/2) S` into `DtensorA n a S`
(the `bwCorr_half_eq` lemma) and its four scalar coefficient identities; the positivity of the
four summands and the final assembly follow.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## The difference tensor of the `b = 1/2` branch -/

/-- The Böhm–Wilking difference tensor `D_{a,1/2}(S)` of the `b = 1/2` branch, written in the
frame-free form of Böhm–Wilking's Corollary 2.3 (proof of their Lemma 3.5):
`((n+2)/4)·(A ∧ A) + (2 s λ̄)·(B ∧ id) + (1/2)·(Ric₀² ∧ id) + γ·(id ∧ id)`. -/
noncomputable def DtensorA (n : ℕ) (a : ℝ) (S : Curv4 n) : Curv4 n :=
  (((n : ℝ) + 2) / 4) • knProd (bwA n S) (bwA n S)
    + (2 * bwS a * bwLam n S) • knProd (bwB n a S) (id2 n)
    + (1 / 2 : ℝ) • knProd (ric0sq S) (id2 n)
    + bwGamma n a S • knProd (id2 n) (id2 n)

/-! ## Elementary Kulkarni–Nomizu algebra -/

/-- Kulkarni–Nomizu products are symmetric in their two arguments. -/
lemma knProd_comm (A B : Fin n → Fin n → ℝ) : knProd A B = knProd B A := by
  funext i j k l
  simp only [knProd]
  ring

/-- Bilinearity of `knProd` in its second argument. -/
lemma knProd_smul_right' (c : ℝ) (A B : Fin n → Fin n → ℝ) :
    knProd A (c • B) = c • knProd A B := by
  funext i j k l
  simp only [knProd, Pi.smul_apply, smul_eq_mul]
  ring

/-- `knProd` of `X + c • id` with itself. -/
lemma knProd_add_smul_self (X : Fin n → Fin n → ℝ) (c : ℝ) :
    knProd (X + c • id2 n) (X + c • id2 n)
      = knProd X X + (2 * c) • knProd X (id2 n) + (c * c) • knProd (id2 n) (id2 n) := by
  rw [knProd_add_left_linv, knProd_add_right, knProd_add_right, knProd_smul_left_linv,
    knProd_smul_left_linv, knProd_smul_right', knProd_smul_right', knProd_comm (id2 n) X]
  module

/-- `knProd` of `X + c • id` with `id`. -/
lemma knProd_add_smul_id (X : Fin n → Fin n → ℝ) (c : ℝ) :
    knProd (X + c • id2 n) (id2 n) = knProd X (id2 n) + c • knProd (id2 n) (id2 n) := by
  rw [knProd_add_left_linv, knProd_smul_left_linv]

/-- `bwA n S` as an explicit two-tensor. -/
lemma bwA_eq (n : ℕ) (S : Curv4 n) :
    bwA n S = ric0 S + (4 * bwLam n S / ((n : ℝ) + 2)) • id2 n := rfl

/-- `bwB n a S` as an explicit two-tensor. -/
lemma bwB_eq (n : ℕ) (a : ℝ) (S : Curv4 n) :
    bwB n a S = ric0 S + (4 * bwLam n S / ((n : ℝ) + 2 + 4 * bwS a)) • id2 n := rfl

/-- The Ricci tensor in terms of the traceless Ricci tensor and the mean curvature. -/
lemma ric_eq_ric0_add (n : ℕ) (S : Curv4 n) : ric S = ric0 S + bwLam n S • id2 n := by
  funext i j
  simp only [ric0, bwLam, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## The two expansions -/

/-- Expansion of `bwCorr a (1/2) S` in the four basis tensors `Ric₀ ∧ Ric₀`, `Ric₀ ∧ id`,
`Ric₀² ∧ id`, `id ∧ id`. -/
lemma bwCorr_half_expand (n : ℕ) (a : ℝ) (S : Curv4 n) :
    bwCorr a (1 / 2) S
      = (((n : ℝ) - 2) * (1 / 2 : ℝ) ^ 2 - 2 * (a - 1 / 2) + 2 * a)
          • knProd (ric0 S) (ric0 S)
        + (2 * a * (2 * bwLam n S)) • knProd (ric0 S) (id2 n)
        + (2 * (1 / 2 : ℝ) ^ 2) • knProd (ric0sq S) (id2 n)
        + (2 * a * (bwLam n S * bwLam n S)
            + ((((n : ℝ) * (1 / 2 : ℝ) ^ 2 * (1 - 2 * (1 / 2))
                - 2 * (a - 1 / 2) * (1 - 2 * (1 / 2) + (n : ℝ) * (1 / 2) ^ 2))
              / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) * ric0Frob2 S))
          • knProd (id2 n) (id2 n) := by
  rw [bwCorr, ric_eq_ric0_add, knProd_add_smul_self]
  module

/-- Expansion of `DtensorA n a S` in the same four basis tensors. -/
lemma DtensorA_expand (n : ℕ) (a : ℝ) (S : Curv4 n) :
    DtensorA n a S
      = (((n : ℝ) + 2) / 4) • knProd (ric0 S) (ric0 S)
        + (2 * (4 * bwLam n S / ((n : ℝ) + 2)) * ((n : ℝ) + 2) / 4 + 2 * bwS a * bwLam n S)
            • knProd (ric0 S) (id2 n)
        + (1 / 2 : ℝ) • knProd (ric0sq S) (id2 n)
        + ((((n : ℝ) + 2) / 4)
              * ((4 * bwLam n S / ((n : ℝ) + 2)) * (4 * bwLam n S / ((n : ℝ) + 2)))
            + 2 * bwS a * bwLam n S * (4 * bwLam n S / ((n : ℝ) + 2 + 4 * bwS a))
            + bwGamma n a S) • knProd (id2 n) (id2 n) := by
  rw [DtensorA, bwA_eq, bwB_eq, knProd_add_smul_self, knProd_add_smul_id]
  module

/-! ## The four scalar coefficient identities -/

/-- The `Ric₀ ∧ Ric₀` coefficient: `(n-2)/4 - 2(a-1/2) + 2a = (n+2)/4`. -/
lemma bwCoef1 (n : ℕ) (a : ℝ) :
    ((n : ℝ) - 2) * (1 / 2 : ℝ) ^ 2 - 2 * (a - 1 / 2) + 2 * a = ((n : ℝ) + 2) / 4 := by
  ring

/-- The `Ric₀ ∧ id` coefficient. -/
lemma bwCoef2 (n : ℕ) (a : ℝ) {lam : ℝ} (h : (n : ℝ) + 2 ≠ 0) :
    2 * (4 * lam / ((n : ℝ) + 2)) * ((n : ℝ) + 2) / 4 + 2 * bwS a * lam = 2 * a * (2 * lam) := by
  rw [bwS]
  field_simp
  ring

/-- The `Ric₀² ∧ id` coefficient. -/
lemma bwCoef3 : (2 : ℝ) * (1 / 2 : ℝ) ^ 2 = 1 / 2 := by norm_num

/-- The two `Ric₀`-induced simplifications in the `id ∧ id` coefficient. -/
lemma bwCoef4a (n : ℕ) {lam : ℝ} (h : (n : ℝ) + 2 ≠ 0) :
    (((n : ℝ) + 2) / 4) * ((4 * lam / ((n : ℝ) + 2)) * (4 * lam / ((n : ℝ) + 2)))
      = 4 * (lam * lam) / ((n : ℝ) + 2) := by
  field_simp

lemma bwCoef4b (n : ℕ) (a : ℝ) {lam : ℝ} :
    2 * (2 * a - 1) * lam * (4 * lam / ((n : ℝ) + 2 + 4 * (2 * a - 1)))
      = 8 * (2 * a - 1) * (lam * lam) / ((n : ℝ) + 2 + 4 * (2 * a - 1)) := by
  ring

/-- `bwGamma` in explicit form. -/
lemma bwGamma_eq (n : ℕ) (a : ℝ) (S : Curv4 n) :
    bwGamma n a S = bwLam n S ^ 2 * (((n : ℝ) - 2) / ((n : ℝ) + 2)
        + bwS a * (((n : ℝ) - 6 + 4 * bwS a) / ((n : ℝ) + 2 + 4 * bwS a)))
      - bwS a * ric0Frob2 S / (4 * ((n : ℝ) + ((n : ℝ) - 1) * bwS a)) := rfl

/-- The `bwCorr` coefficient of `|Ric₀|²` equals `-s/(4(n+(n-1)s))`. -/
lemma bwCoef4c (n : ℕ) (a : ℝ) {frob : ℝ}
    (h1 : (n : ℝ) ≠ 0) (h2 : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0)
    (h3 : (n : ℝ) + ((n : ℝ) - 1) * (2 * a - 1) ≠ 0) :
    ((n : ℝ) * (1 / 2 : ℝ) ^ 2 * (1 - 2 * (1 / 2))
        - 2 * (a - 1 / 2) * (1 - 2 * (1 / 2) + (n : ℝ) * (1 / 2) ^ 2))
      / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a)) * frob
      = -(2 * a - 1) * frob / (4 * ((n : ℝ) + ((n : ℝ) - 1) * (2 * a - 1))) := by
  field_simp
  ring

/-- The Böhm–Wilking estimate (Böhm–Wilking, proof of Lemma 3.5): the `id ∧ id` coefficient is
positive. -/
lemma bwCoef4d (n : ℕ) (a : ℝ) {lam frob : ℝ} (h1 : (n : ℝ) + 2 ≠ 0)
    (h2 : (n : ℝ) + 2 + 4 * (2 * a - 1) ≠ 0)
    (h3 : (n : ℝ) + ((n : ℝ) - 1) * (2 * a - 1) ≠ 0) :
    4 * (lam * lam) / ((n : ℝ) + 2)
      + 8 * (2 * a - 1) * (lam * lam) / ((n : ℝ) + 2 + 4 * (2 * a - 1))
      + (lam * lam * (((n : ℝ) - 2) / ((n : ℝ) + 2)
            + (2 * a - 1) * (((n : ℝ) - 6 + 4 * (2 * a - 1)) / ((n : ℝ) + 2 + 4 * (2 * a - 1))))
          - (2 * a - 1) * frob / (4 * ((n : ℝ) + ((n : ℝ) - 1) * (2 * a - 1))))
      = 2 * a * (lam * lam)
        - (2 * a - 1) * frob / (4 * ((n : ℝ) + ((n : ℝ) - 1) * (2 * a - 1))) := by
  field_simp
  ring

/-- The `id ∧ id` coefficient: the four previous identities combined. -/
lemma bwCoef4 (n : ℕ) (a : ℝ) (lam frob : ℝ) (h1 : (n : ℝ) + 2 ≠ 0)
    (h2 : (n : ℝ) ≠ 0) (h3 : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0)
    (h4 : (n : ℝ) + ((n : ℝ) - 1) * (2 * a - 1) ≠ 0)
    (h5 : (n : ℝ) + 2 + 4 * (2 * a - 1) ≠ 0) :
    2 * a * (lam * lam)
      + ((((n : ℝ) * (1 / 2 : ℝ) ^ 2 * (1 - 2 * (1 / 2))
            - 2 * (a - 1 / 2) * (1 - 2 * (1 / 2) + (n : ℝ) * (1 / 2) ^ 2))
          / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) * frob)
      = (((n : ℝ) + 2) / 4) * ((4 * lam / ((n : ℝ) + 2)) * (4 * lam / ((n : ℝ) + 2)))
        + 2 * bwS a * lam * (4 * lam / ((n : ℝ) + 2 + 4 * bwS a))
        + (lam * lam * (((n : ℝ) - 2) / ((n : ℝ) + 2)
              + bwS a * (((n : ℝ) - 6 + 4 * bwS a) / ((n : ℝ) + 2 + 4 * bwS a)))
            - bwS a * frob / (4 * ((n : ℝ) + ((n : ℝ) - 1) * bwS a))) := by
  rw [bwS]
  rw [bwCoef4a n (lam := lam) h1]
  rw [bwCoef4b n a (lam := lam)]
  rw [bwCoef4c n a (frob := frob) h2 h3 h4]
  rw [bwCoef4d n a (lam := lam) (frob := frob) h1 h5 h4]
  ring

/-! ## The Böhm–Wilking identity in the `b = 1/2` branch -/

/-- **The difference tensor is `bwCorr`.**  Purely algebraic rewriting of the Böhm–Wilking
identity `linv a (1/2) (Q (ell a (1/2) S)) = Q S + bwCorr a (1/2) S` into the frame-free form
`DtensorA n a S`. -/
lemma bwCorr_half_eq (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 1 / 2 < a) (S : Curv4 n) :
    bwCorr a (1 / 2) S = DtensorA n a S := by
  have h0 : (n : ℝ) ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0 := by
    have : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * a := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    exact ne_of_gt this
  have h4 : (n : ℝ) + ((n : ℝ) - 1) * (2 * a - 1) ≠ 0 := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have h5 : (n : ℝ) + 2 + 4 * (2 * a - 1) ≠ 0 := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  rw [bwCorr_half_expand n a S, DtensorA_expand n a S, bwGamma_eq]
  rw [show bwLam n S ^ 2 = bwLam n S * bwLam n S from by ring]
  rw [bwCoef1 n a]
  rw [bwCoef2 n a h2]
  rw [bwCoef3]
  rw [bwCoef4 n a (bwLam n S) (ric0Frob2 S) h2 h0 h3 h4 h5]

/-! ## Scalar arithmetic for the positivity of `γ`

The Böhm–Wilking estimate of Lemma 3.5 reduces to the elementary polynomial inequality below. -/


lemma arithP (n : ℕ) (hn : 3 ≤ n) {s : ℝ} (hs : 0 < s) :
    0 < (((n : ℝ) ^ 2 - 4) + s * ((n : ℝ) ^ 2 - 20) + 4 * s ^ 2 * ((n : ℝ) + 2))
          * ((n : ℝ) + 2 + 4 * s) - 4 * s * ((n : ℝ) - 1) * ((n : ℝ) + 2) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  by_cases h5 : n < 5
  · have hn34 : n = 3 ∨ n = 4 := by omega
    rcases hn34 with rfl | rfl
    · norm_num
      nlinarith [sq_nonneg (s - 1 / 2), sq_nonneg (272 * s - 95)]
    · norm_num
      nlinarith [sq_nonneg (512 * s - 96)]
  · have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_not_lt h5
    have hP : (((n : ℝ) ^ 2 - 4) + s * ((n : ℝ) ^ 2 - 20) + 4 * s ^ 2 * ((n : ℝ) + 2))
          * ((n : ℝ) + 2 + 4 * s) - 4 * s * ((n : ℝ) - 1) * ((n : ℝ) + 2)
        = ((n : ℝ) ^ 2 - 4) * ((n : ℝ) + 2)
          + s * ((n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 - 24 * (n : ℝ) - 48)
          + 8 * ((n : ℝ) + 4) * ((n : ℝ) - 2) * s ^ 2 + 16 * ((n : ℝ) + 2) * s ^ 3 := by
      ring
    have hcoef : 0 ≤ (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 - 24 * (n : ℝ) - 48 := by
      have h : (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 - 24 * (n : ℝ) - 48
          = ((n : ℝ) - 5) * ((n : ℝ) ^ 2 + 7 * (n : ℝ) + 11) + 7 := by ring
      rw [h]
      nlinarith [hn5, sq_nonneg ((n : ℝ) + 7 / 2)]
    rw [hP]
    have h1 : 0 < ((n : ℝ) ^ 2 - 4) * ((n : ℝ) + 2) := by nlinarith
    have h3 : 0 ≤ 8 * ((n : ℝ) + 4) * ((n : ℝ) - 2) * s ^ 2 := by
      have h : (0 : ℝ) < (n : ℝ) - 2 := by linarith
      positivity
    have h4 : 0 < 16 * ((n : ℝ) + 2) * s ^ 3 := by positivity
    nlinarith [h1, hcoef, h3, h4]

lemma arithC (n : ℕ) (hn : 3 ≤ n) {s : ℝ} (hs : 0 < s) :
    4 * s * ((n : ℝ) - 1) / ((n : ℝ) + 2 + 4 * s) ^ 2
      < ((n : ℝ) - 2) / ((n : ℝ) + 2) + s * (((n : ℝ) - 6 + 4 * s) / ((n : ℝ) + 2 + 4 * s)) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have h2 : (0 : ℝ) < (n : ℝ) + 2 + 4 * s := by linarith
  have hC : ((n : ℝ) - 2) / ((n : ℝ) + 2) + s * (((n : ℝ) - 6 + 4 * s) / ((n : ℝ) + 2 + 4 * s))
      = (((n : ℝ) ^ 2 - 4) + s * ((n : ℝ) ^ 2 - 20) + 4 * s ^ 2 * ((n : ℝ) + 2))
        / (((n : ℝ) + 2) * ((n : ℝ) + 2 + 4 * s)) := by
    field_simp
    ring
  rw [hC, div_lt_div_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 2 + 4 * s) ^ 2)
    (by positivity : (0 : ℝ) < ((n : ℝ) + 2) * ((n : ℝ) + 2 + 4 * s))]
  have hP := arithP n hn hs
  nlinarith [hP, h2]

/-! ## The positivity of the difference tensor -/

/-- `ric0Frob2` is a sum of squares. -/
lemma ric0Frob2_nonneg (Y : Curv4 n) : 0 ≤ ric0Frob2 Y := by
  simp only [ric0Frob2]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- In dimension `2` every algebraic curvature tensor is a multiple of the round sphere. -/
lemma isAlgCurv_two {S : Curv4 2} (hS : IsAlgCurv S) : S = (S 0 1 0 1) • Iso 2 := by
  have h12 : ∀ a b c d : Fin 2, S b a c d = - S a b c d := fun a b c d => hS.1 a b c d
  have h34 : ∀ a b c d : Fin 2, S a b d c = - S a b c d := by
    intro a b c d
    have h1 := hS.2.1 a b d c
    have h2 := hS.1 d c a b
    have h3 := hS.2.1 a b c d
    linarith
  funext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [Pi.smul_apply, smul_eq_mul, Iso] <;>
    norm_num <;>
    linarith [h12 (0 : Fin 2) 0 0 0, h12 0 0 0 1, h12 0 0 1 0, h12 0 0 1 1, h12 0 1 0 0,
      h12 0 1 0 1, h12 0 1 1 0, h12 0 1 1 1, h12 1 0 0 0, h12 1 0 0 1, h12 1 0 1 0,
      h12 1 0 1 1, h12 1 1 0 0, h12 1 1 0 1, h12 1 1 1 0, h12 1 1 1 1,
      h34 (0 : Fin 2) 0 0 0, h34 0 0 0 1, h34 0 0 1 0, h34 0 0 1 1, h34 0 1 0 0,
      h34 0 1 0 1, h34 0 1 1 0, h34 0 1 1 1, h34 1 0 0 0, h34 1 0 0 1, h34 1 0 1 0,
      h34 1 0 1 1, h34 1 1 0 0, h34 1 1 0 1, h34 1 1 1 0, h34 1 1 1 1]

/-- In dimensions `≤ 1` the round sphere tensor vanishes, so `EFun (Iso n)` is identically zero. -/
lemma iso_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) : Iso n = (0 : Curv4 n) := by
  rcases Nat.lt_or_ge n 2 with h | h
  swap
  · omega
  interval_cases n
  · funext i; exact i.elim0
  · funext i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp [Iso]

/-- **Vacuity of the hypotheses in dimensions `≤ 2`**: if `S ≠ 0` is an algebraic curvature tensor
in dimension at most `2`, then `EFun S x y z w = 0` forces `EFun (Iso n) x y z w = 0`. -/
lemma efIso_zero_of_ef_zero_lt_three (n : ℕ) (hn : n < 3) {S : Curv4 n}
    (hS : IsAlgCurv S) (hS0 : S ≠ 0) :
    ∀ x y z w : Fin n → ℝ,
      Work.Diff.Alg.Q2P.EFun S x y z w = 0 → Work.Diff.Alg.Q2P.EFun (Iso n) x y z w = 0 := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · -- `n ≤ 1`: `Iso n = 0`, so `EFun (Iso n)` vanishes
    intro x y z w _
    have hzero : Iso n = (0 : Curv4 n) := iso_eq_zero_of_lt_two h2
    rw [hzero]
    simp only [Work.Diff.Alg.Q2P.EFun, Submission.Diff.Alg.R4, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero]
    ring
  · -- `n = 2`
    have hn2 : n = 2 := by omega
    subst hn2
    have hstruct : S = (S 0 1 0 1) • Iso 2 := isAlgCurv_two hS
    have hc : (S 0 1 0 1) ≠ 0 := by
      intro h
      apply hS0
      rw [hstruct, h, zero_smul]
    intro x y z w hzero
    have h1 : Work.Diff.Alg.Q2P.EFun S x y z w
        = (S 0 1 0 1) * Work.Diff.Alg.Q2P.EFun (Iso 2) x y z w := by
      conv_lhs => rw [hstruct]
      exact Cone.EF_smul (S 0 1 0 1) (Iso 2) x y z w
    rw [h1] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hc

/-- **Positivity of the Böhm–Wilking coefficient `γ`** (Böhm–Wilking, proof of Lemma 3.5), given
the Frobenius bound `|Ric₀|² ≤ n(n-1)(1-p)²λ̄²` for `Ric ≥ p λ̄ · id`. -/
lemma bwGamma_pos (n : ℕ) (hn : 3 ≤ n) {a : ℝ} (ha : 1 / 2 < a) {S : Curv4 n}
    (hFrob : ric0Frob2 S
      ≤ (n : ℝ) * ((n : ℝ) - 1) * (4 / ((n : ℝ) - 2 + 8 * a)) ^ 2 * (bwLam n S) ^ 2)
    (hlam : 0 < bwLam n S) : 0 < bwGamma n a S := by
  rw [bwGamma_eq]
  have hs : 0 < bwS a := by rw [bwS]; linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set D : ℝ := (n : ℝ) + 2 + 4 * bwS a with hDdef
  set E : ℝ := (n : ℝ) + ((n : ℝ) - 1) * bwS a with hEdef
  have hDeq : D = (n : ℝ) + 2 + 4 * bwS a := hDdef
  have hEeq : E = (n : ℝ) + ((n : ℝ) - 1) * bwS a := hEdef
  have hEpos : 0 < E := by
    rw [hEeq]; nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (le_of_lt hs)]
  have hnE : (n : ℝ) ≤ E := by
    rw [hEeq]; nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (le_of_lt hs)]
  have hden : (n : ℝ) - 2 + 8 * a = D := by rw [hDeq, bwS]; ring
  have hDpos : 0 < D := by rw [← hden]; linarith
  have hD2 : (0 : ℝ) < D ^ 2 := by positivity
  have hC : 4 * bwS a * ((n : ℝ) - 1) / D ^ 2
      < ((n : ℝ) - 2) / ((n : ℝ) + 2) + bwS a * (((n : ℝ) - 6 + 4 * bwS a) / D) := by
    rw [show D = (n : ℝ) + 2 + 4 * bwS a from hDeq]
    exact arithC n hn hs
  have hFrobc : ric0Frob2 S * D ^ 2 ≤ 16 * (n : ℝ) * ((n : ℝ) - 1) * (bwLam n S) ^ 2 := by
    have h := hFrob
    rw [hden] at h
    have h1 : (n : ℝ) * ((n : ℝ) - 1) * (4 / D) ^ 2 * (bwLam n S) ^ 2
        = 16 * (n : ℝ) * ((n : ℝ) - 1) * (bwLam n S) ^ 2 / D ^ 2 := by
      rw [div_pow]; ring
    rw [h1] at h
    rw [le_div_iff₀ hD2] at h
    exact h
  have hkey : bwS a * ric0Frob2 S * D ^ 2
      ≤ 16 * bwS a * ((n : ℝ) - 1) * (bwLam n S) ^ 2 * E := by
    have h1 : bwS a * ric0Frob2 S * D ^ 2
        ≤ bwS a * (16 * (n : ℝ) * ((n : ℝ) - 1) * (bwLam n S) ^ 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hFrobc (le_of_lt hs)
    have h2 : bwS a * (16 * (n : ℝ) * ((n : ℝ) - 1) * (bwLam n S) ^ 2)
        ≤ 16 * bwS a * ((n : ℝ) - 1) * (bwLam n S) ^ 2 * E := by
      have hmono := mul_le_mul_of_nonneg_left hnE
        (by positivity : (0 : ℝ) ≤ 16 * bwS a * ((n : ℝ) - 1) * (bwLam n S) ^ 2)
      linarith [hmono]
    linarith [h1, h2]
  have hb : bwS a * ric0Frob2 S / (4 * E)
      ≤ (bwLam n S) ^ 2 * (4 * bwS a * ((n : ℝ) - 1) / D ^ 2) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * E)]
    have hrw : (bwLam n S) ^ 2 * (4 * bwS a * ((n : ℝ) - 1) / D ^ 2) * (4 * E)
        = 16 * bwS a * ((n : ℝ) - 1) * (bwLam n S) ^ 2 * E / D ^ 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [hrw, le_div_iff₀ hD2]
    exact hkey
  have h2 : (bwLam n S) ^ 2 * (4 * bwS a * ((n : ℝ) - 1) / D ^ 2)
      < (bwLam n S) ^ 2 * (((n : ℝ) - 2) / ((n : ℝ) + 2)
          + bwS a * (((n : ℝ) - 6 + 4 * bwS a) / D)) :=
    mul_lt_mul_of_pos_left hC (by positivity)
  linarith [hb, h2]

/-! ## Positive semidefiniteness of the two-tensors appearing in `DtensorA` -/

/-- The double sum of the Kronecker delta against `v ⊗ v`. -/
lemma sum_id2_quad (n : ℕ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, id2 n i j * v i * v j) = ∑ i, v i * v i := by
  apply Finset.sum_congr rfl; intro i _
  rw [show (∑ j, id2 n i j * v i * v j) = ∑ j, id2 n i j * (v i * v j) from
    Finset.sum_congr rfl fun j _ => by ring]
  exact ellinv_sum_id2_mul (fun j => v i * v j) i

/-- `ric0 S` as a quadratic form. -/
lemma ric0_quad_eq (n : ℕ) (S : Curv4 n) (v : Fin n → ℝ) :
    (∑ i, ∑ j, ric0 S i j * v i * v j)
      = (∑ i, ∑ j, ric S i j * v i * v j) - bwLam n S * (∑ i, v i * v i) := by
  have hL : (∑ i, ∑ j, ric0 S i j * v i * v j)
      = ∑ i, ∑ j, (ric S i j - bwLam n S * id2 n i j) * v i * v j := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp only [ric0, bwLam]
  rw [hL]
  have hpt : ∀ i j : Fin n, (ric S i j - bwLam n S * id2 n i j) * v i * v j
      = ric S i j * v i * v j - bwLam n S * (id2 n i j * v i * v j) := fun i j => by ring
  simp only [hpt, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.mul_sum]
  congr 1
  rw [show (∑ j, id2 n i j * v i * v j) = ∑ j, id2 n i j * (v i * v j) from
    Finset.sum_congr rfl fun j _ => by ring]
  exact ellinv_sum_id2_mul (fun j => v i * v j) i

/-- `bwA n S = Ric₀ S + (4λ̄/(n+2))·id` is positive semidefinite under `Ric ≥ p λ̄ · id` with
`p ≥ (n-2)/(n+2)`. -/
lemma bwA_qform_nonneg (n : ℕ) (hn : 3 ≤ n) {a : ℝ} (_ha : 1 / 2 < a) {S : Curv4 n}
    (hric : RicPinch (1 - 4 / ((n : ℝ) - 2 + 8 * a)) S) (hlam : 0 ≤ bwLam n S) :
    ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, bwA n S i j * v i * v j := by
  intro v
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : (0 : ℝ) < (n : ℝ) - 2 + 8 * a := by linarith
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hpp : ((n : ℝ) - 2) / ((n : ℝ) + 2) ≤ 1 - 4 / ((n : ℝ) - 2 + 8 * a) := by
    rw [le_sub_iff_add_le, div_add_div _ _ (ne_of_gt h2) (ne_of_gt h1), div_le_one (by positivity)]
    nlinarith
  have hric' : (1 - 4 / ((n : ℝ) - 2 + 8 * a)) * bwLam n S * (∑ i, v i * v i)
      ≤ ∑ i, ∑ j, ric S i j * v i * v j := by
    have h := hric v
    simp only [bwLam]
    have e : (1 - 4 / ((n : ℝ) - 2 + 8 * a)) * (scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
        = (1 - 4 / ((n : ℝ) - 2 + 8 * a)) * scalAlg S / (n : ℝ) * (∑ i, v i * v i) := by ring
    rw [e]
    exact h
  have hA : ∑ i, ∑ j, bwA n S i j * v i * v j
      = (∑ i, ∑ j, ric0 S i j * v i * v j) + (4 * bwLam n S / ((n : ℝ) + 2)) * (∑ i, v i * v i) := by
    rw [bwA_eq]
    have hpt : ∀ i j : Fin n,
        (ric0 S i j + (4 * bwLam n S / ((n : ℝ) + 2)) * id2 n i j) * v i * v j
          = ric0 S i j * v i * v j
            + (4 * bwLam n S / ((n : ℝ) + 2)) * (id2 n i j * v i * v j) := fun i j => by ring
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hpt, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.mul_sum]
    congr 1
    rw [show (∑ j, id2 n i j * v i * v j) = ∑ j, id2 n i j * (v i * v j) from
      Finset.sum_congr rfl fun j _ => by ring]
    exact ellinv_sum_id2_mul (fun j => v i * v j) i
  have harith : 4 * bwLam n S / ((n : ℝ) + 2) * (∑ i, v i * v i)
      = (1 - ((n : ℝ) - 2) / ((n : ℝ) + 2)) * bwLam n S * (∑ i, v i * v i) := by
    have h : (0 : ℝ) < (n : ℝ) + 2 := by linarith
    field_simp
    ring
  rw [hA, ric0_quad_eq, harith]
  have hsq : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h3 : ((n : ℝ) - 2) / ((n : ℝ) + 2) * (bwLam n S * (∑ i, v i * v i))
      ≤ (1 - 4 / ((n : ℝ) - 2 + 8 * a)) * (bwLam n S * (∑ i, v i * v i)) :=
    mul_le_mul_of_nonneg_right hpp (mul_nonneg hlam hsq)
  nlinarith [hric', h3]

/-- `bwB n a S = Ric₀ S + (4λ̄/(n+2+4s))·id = Ric S - p λ̄ · id` is positive semidefinite: it is
exactly the Ricci pinching hypothesis. -/
lemma bwB_qform_nonneg (n : ℕ) (hn : 3 ≤ n) {a : ℝ} (ha : 1 / 2 < a) {S : Curv4 n}
    (hric : RicPinch (1 - 4 / ((n : ℝ) - 2 + 8 * a)) S) :
    ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, bwB n a S i j * v i * v j := by
  intro v
  have hs : 0 < bwS a := by rw [bwS]; linarith
  have hric' : (1 - 4 / ((n : ℝ) - 2 + 8 * a)) * bwLam n S * (∑ i, v i * v i)
      ≤ ∑ i, ∑ j, ric S i j * v i * v j := by
    have h := hric v
    simp only [bwLam]
    have e : (1 - 4 / ((n : ℝ) - 2 + 8 * a)) * (scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
        = (1 - 4 / ((n : ℝ) - 2 + 8 * a)) * scalAlg S / (n : ℝ) * (∑ i, v i * v i) := by ring
    rw [e]
    exact h
  have hB : ∑ i, ∑ j, bwB n a S i j * v i * v j
      = (∑ i, ∑ j, ric0 S i j * v i * v j)
        + (4 * bwLam n S / ((n : ℝ) + 2 + 4 * bwS a)) * (∑ i, v i * v i) := by
    rw [bwB_eq]
    have hpt : ∀ i j : Fin n,
        (ric0 S i j + (4 * bwLam n S / ((n : ℝ) + 2 + 4 * bwS a)) * id2 n i j) * v i * v j
          = ric0 S i j * v i * v j
            + (4 * bwLam n S / ((n : ℝ) + 2 + 4 * bwS a)) * (id2 n i j * v i * v j) :=
      fun i j => by ring
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hpt, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.mul_sum]
    congr 1
    rw [show (∑ j, id2 n i j * v i * v j) = ∑ j, id2 n i j * (v i * v j) from
      Finset.sum_congr rfl fun j _ => by ring]
    exact ellinv_sum_id2_mul (fun j => v i * v j) i
  have hB2 : ∑ i, ∑ j, bwB n a S i j * v i * v j
      = (∑ i, ∑ j, ric S i j * v i * v j)
        - (1 - 4 / ((n : ℝ) - 2 + 8 * a)) * bwLam n S * (∑ i, v i * v i) := by
    rw [hB, ric0_quad_eq]
    have hden' : (n : ℝ) + 2 + 4 * bwS a = (n : ℝ) - 2 + 8 * a := by rw [bwS]; ring
    rw [hden']
    field_simp
    ring
  rw [hB2]
  linarith [hric']

/-! ## `Ric₀²` is positive semidefinite -/

lemma ric0sq_symm (n : ℕ) {S : Curv4 n} (hS : IsAlgCurv S) (i j : Fin n) :
    ric0sq S i j = ric0sq S j i := by
  simp only [ric0sq]
  apply Finset.sum_congr rfl; intro k _
  rw [ric0_symm hS i k, ric0_symm hS k j, ric0_symm hS j k, ric0_symm hS k i]
  ring

/-- Reindexing a triple sum: `∑ᵢⱼₖ = ∑ₖᵢⱼ`. -/
lemma sum3_rotate (n : ℕ) (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
  have e1 : (∑ i, ∑ j, ∑ k, f i j k) = ∑ i, ∑ k, ∑ j, f i j k := by
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
  rw [e1, Finset.sum_comm]

/-- Product of two sums as a double sum. -/
lemma sum_mul_sum' {n : ℕ} (f g : Fin n → ℝ) :
    (∑ i, f i) * (∑ j, g j) = ∑ i, ∑ j, f i * g j := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]

lemma ric0sq_qform_eq (n : ℕ) {S : Curv4 n} (hS : IsAlgCurv S) (v : Fin n → ℝ) :
    (∑ i, ∑ j, ric0sq S i j * v i * v j)
      = ∑ k, (∑ i, ric0 S k i * v i) * (∑ i, ric0 S k i * v i) := by
  have key2 : (∑ i, ∑ j, ric0sq S i j * v i * v j)
      = ∑ i, ∑ j, ∑ k, ric0 S k i * ric0 S k j * v i * v j := by
    simp only [ric0sq]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _
    rw [ric0_symm hS i k]
  have h1 : ∀ k : Fin n, (∑ i, ric0 S k i * v i) * (∑ i, ric0 S k i * v i)
      = ∑ i, ∑ j, ric0 S k i * ric0 S k j * v i * v j := by
    intro k
    rw [sum_mul_sum']
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [key2, sum3_rotate n]
  exact Finset.sum_congr rfl (fun k _ => (h1 k).symm)

lemma ric0sq_qform_nonneg (n : ℕ) {S : Curv4 n} (hS : IsAlgCurv S) (v : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, ric0sq S i j * v i * v j := by
  rw [ric0sq_qform_eq n hS v]
  exact Finset.sum_nonneg fun k _ => mul_self_nonneg _

/-! ## Symmetry of the two-tensors -/

lemma id2_symm_a (n : ℕ) : ∀ i j : Fin n, id2 n i j = id2 n j i := by
  intro i j
  simp only [id2]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

lemma bwA_symm (n : ℕ) {S : Curv4 n} (hS : IsAlgCurv S) :
    ∀ i j, bwA n S i j = bwA n S j i := by
  intro i j
  rw [bwA_eq]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ric0_symm hS i j, id2_symm_a]

lemma bwB_symm (n : ℕ) (a : ℝ) {S : Curv4 n} (hS : IsAlgCurv S) :
    ∀ i j, bwB n a S i j = bwB n a S j i := by
  intro i j
  rw [bwB_eq]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ric0_symm hS i j, id2_symm_a]

/-- Linearity of `Q2P.EFun` in the tensor argument. -/
lemma Q2P_EFun_add (R S : Curv4 n) (x y z w : Fin n → ℝ) :
    Q2P.EFun (R + S) x y z w = Q2P.EFun R x y z w + Q2P.EFun S x y z w :=
  Cone.EF_add R S x y z w

lemma Q2P_EFun_smul (t : ℝ) (R : Curv4 n) (x y z w : Fin n → ℝ) :
    Q2P.EFun (t • R) x y z w = t * Q2P.EFun R x y z w :=
  Cone.EF_smul t R x y z w

/-- `∑ᵢ vᵢ² ≥ 0`. -/
lemma sum_id2_nonneg (n : ℕ) (v : Fin n → ℝ) : 0 ≤ ∑ i, v i * v i :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- `knProd (id2 n) (id2 n) = 2 • Iso n`. -/
lemma knProd_id2_id2_a (n : ℕ) : knProd (id2 n) (id2 n) = (2 : ℝ) • Iso n := by
  funext i j k l
  simp only [knProd, id2, Iso, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-! ## Strict positivity of the difference tensor -/

/-- **The Böhm–Wilking eigenvalue computation in the `PIC2` form**: the difference tensor
`DtensorA n a S` is strictly positive at every nondegenerate direction. -/
lemma DtensorA_EFun_pos (n : ℕ) (hn : 3 ≤ n) {a : ℝ} (ha : 1 / 2 < a) {S : Curv4 n}
    (hS : IsAlgCurv S) (hS0 : S ≠ 0) (hP : InPIC2 S)
    (hric : RicPinch (1 - 4 / ((n : ℝ) - 2 + 8 * a)) S)
    (hFrob : ric0Frob2 S
      ≤ (n : ℝ) * ((n : ℝ) - 1) * (4 / ((n : ℝ) - 2 + 8 * a)) ^ 2 * (bwLam n S) ^ 2)
    (hKN : ∀ (M N : Fin n → Fin n → ℝ), (∀ i j, M i j = M j i) → (∀ i j, N i j = N j i) →
      (∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, M i j * v i * v j) →
      (∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, N i j * v i * v j) →
      ∀ x y z w : Fin n → ℝ, 0 ≤ Q2P.EFun (knProd M N) x y z w)
    (hlam : 0 < bwLam n S) :
    ∀ x y z w : Fin n → ℝ, Q2P.EFun (Iso n) x y z w ≠ 0 →
      0 < Q2P.EFun (DtensorA n a S) x y z w := by
  have hgamma : 0 < bwGamma n a S := bwGamma_pos n hn ha hFrob hlam
  have hs : 0 < bwS a := by rw [bwS]; linarith
  have hid2sym : ∀ i j : Fin n, id2 n i j = id2 n j i := id2_symm_a n
  have hA := bwA_qform_nonneg n hn ha hric (le_of_lt hlam)
  have hAsym := bwA_symm n hS
  have hB := bwB_qform_nonneg n hn ha hric
  have hBsym := bwB_symm n a hS
  have hRsym := ric0sq_symm n hS
  have hR := ric0sq_qform_nonneg n hS
  have hT1 : ∀ x y z w : Fin n → ℝ, 0 ≤ Q2P.EFun (knProd (bwA n S) (bwA n S)) x y z w :=
    hKN _ _ hAsym hAsym hA hA
  have hT2 : ∀ x y z w : Fin n → ℝ,
      0 ≤ Q2P.EFun (knProd (bwB n a S) (id2 n)) x y z w :=
    hKN _ _ hBsym hid2sym hB (fun v => by simpa only [sum_id2_quad] using sum_id2_nonneg n v)
  have hT3 : ∀ x y z w : Fin n → ℝ,
      0 ≤ Q2P.EFun (knProd (ric0sq S) (id2 n)) x y z w :=
    hKN _ _ hRsym hid2sym hR (fun v => by simpa only [sum_id2_quad] using sum_id2_nonneg n v)
  intro x y z w hIso
  have hIso_pos : 0 < Q2P.EFun (Iso n) x y z w :=
    lt_of_le_of_ne (Cone.inPIC2_iso n x y z w) (Ne.symm hIso)
  have hT4 : 0 < Q2P.EFun (knProd (id2 n) (id2 n)) x y z w := by
    rw [knProd_id2_id2_a, Q2P_EFun_smul]
    linarith
  rw [DtensorA]
  rw [Q2P_EFun_add, Q2P_EFun_add, Q2P_EFun_add, Q2P_EFun_smul, Q2P_EFun_smul, Q2P_EFun_smul,
    Q2P_EFun_smul]
  have h1 := hT1 x y z w
  have h2 := hT2 x y z w
  have h3 := hT3 x y z w
  have hc2 : 0 ≤ 2 * bwS a * bwLam n S := by positivity
  have hc1 : 0 ≤ ((n : ℝ) + 2) / 4 := by positivity
  nlinarith [h1, h2, h3, hT4, hgamma, hc1, hc2]

/-! ## The target statement -/

theorem ChatT_strict_pic_a (n : ℕ) (hn : 2 ≤ n) {a : ℝ} (ha : 1 / 2 < a)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S) (hS0 : S ≠ 0)
    (hP : Submission.Diff.Alg.InPIC2 S)
    (hric : Work.Diff.Alg.Pinch.RicPinch (1 - 4 / ((n : ℝ) - 2 + 8 * a)) S) :
    ∀ x y z w : Fin n → ℝ,
      Work.Diff.Alg.Q2P.EFun S x y z w = 0 →
      Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w ≠ 0 →
      0 < Work.Diff.Alg.Q2P.EFun
        (Work.Diff.Alg.Pinch.linv a (1 / 2)
          (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a (1 / 2) S))) x y z w := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · -- `n ≤ 2`: the two hypotheses on `x y z w` are contradictory
    intro x y z w hdeg hIso
    exact absurd (efIso_zero_of_ef_zero_lt_three n hlt hS hS0 x y z w hdeg) hIso
  · intro x y z w hdeg hIso
    have hn1 : 1 ≤ n := by omega
    -- the mean curvature `λ̄ = scal S / n` is positive
    have hlam : 0 < bwLam n S := by
      have h := scalAlg_pos_of_inPIC2_ricpinch n hn ha hS hS0 hP hric
      simpa only [bwLam] using h
    -- the Frobenius bound on `Ric₀`
    have hFrob : ric0Frob2 S
        ≤ (n : ℝ) * ((n : ℝ) - 1) * (4 / ((n : ℝ) - 2 + 8 * a)) ^ 2 * (bwLam n S) ^ 2 := by
      have hp : 1 - 4 / ((n : ℝ) - 2 + 8 * a) ≤ 1 := by
        have hpos : (0 : ℝ) < 4 / ((n : ℝ) - 2 + 8 * a) := by
          apply div_pos (by norm_num)
          have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith
        linarith
      have h := ric0Frob2_le n (p := 1 - 4 / ((n : ℝ) - 2 + 8 * a)) hp hS hric
        (by simpa only [bwLam] using hlam)
      have h1 : (1 - (1 - 4 / ((n : ℝ) - 2 + 8 * a))) ^ 2 = (4 / ((n : ℝ) - 2 + 8 * a)) ^ 2 := by
        ring
      rw [← h1]
      simpa only [bwLam] using h
    -- the Böhm–Wilking identity
    have hX : linv a (1 / 2) (Q (ell a (1 / 2) S)) = Q S + DtensorA n a S := by
      have ha1 : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0 := by
        have : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * a := by
          have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          nlinarith
        exact ne_of_gt this
      have hb1 : 1 + ((n : ℝ) - 2) * (1 / 2) ≠ 0 := by
        have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        intro hc
        nlinarith
      have h0 := bwDef_of_children
        (fun m {A} hA {W} hW hricW => by
          show KeyForm m A W
          funext i j k l
          exact BQ_knProd_W m hA hW hricW i j k l)
        (fun m a' b' ha' hb' {A} hA => linv_Q_ell_knProd m a' b' ha' hb' hA)
        n a (1 / 2) ha1 hb1 hS
      have hbw : linv a (1 / 2) (Q (ell a (1 / 2) S)) = Q S + bwCorr a (1 / 2) S := by
        simpa only [bwDef, sub_eq_zero] using h0
      rw [hbw, bwCorr_half_eq n hn1 ha S]
    rw [hX, Q2P_EFun_add]
    have h1 : 0 ≤ Q2P.EFun (Q S) x y z w := inPIC2_Q_pointwise n S hS hP x y z w hdeg
    have h2 : 0 < Q2P.EFun (DtensorA n a S) x y z w :=
      DtensorA_EFun_pos n hge ha hS hS0 hP hric hFrob
        (fun M N hMsym hNsym hM hN => EFun_knProd_psd n hMsym hNsym hM hN) hlam x y z w hIso
    linarith

end Work.Diff.Alg.Pinch
