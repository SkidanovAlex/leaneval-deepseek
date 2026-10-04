import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.BQDefs
import Submission.Work.Diff.Alg.Pinch.linv_Q_ell
import Submission.Work.Diff.Alg.Pinch.BQ_knProd_W
import Submission.Work.Diff.Alg.Pinch.EFun_knProd_psd
import Submission.Work.Diff.Alg.Pinch.linv_Q_ell_knProd_full
import Submission.Work.Diff.Alg.Pinch.bwCorr_decomp
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic
import Submission.Work.Diff.Alg.Pinch.inPIC2_Q_pointwise
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Strict positivity of the pulled-back reaction term at degenerate directions

The target `Work.Diff.Alg.Pinch.ChatT_strict_pic_b` (equivalently
`Work.Diff.Alg.Pinch.EFun_X_strict_at_degenerate`) is the pointwise strictness statement behind the
transversal invariance of the Böhm–Wilking cones `Ĉ(b)`, `0 < b ≤ 1/2` (Brendle–Schoen Prop. 13,
Böhm–Wilking Lemma 3.4).  With `a = ccA n b`, `p = ccP n b` and
`X = linv a b (Q (ell a b S))`, the Böhm–Wilking identity (Theorem 2) writes

`X = Q S + bwCorr a b S`,

and the two summands are handled separately:

* `0 ≤ EFun (Q S) x y z w` on a degenerate direction `EFun S x y z w = 0`
  (`Work.Diff.Alg.Pinch.inPIC2_Q_pointwise`, Brendle–Schoen §2);
* `bwCorr a b S` is positive definite on nondegenerate directions.  The proof here is *basis free*
  and uses only the Böhm–Wilking decomposition of the difference tensor

  `bwCorr a b S = (2a/(1-p)) • (B ∧ B) + 2b² • (Ric₀² ∧ id) + (2ap·(scal/n)² + c₄·|Ric₀|²) • (id ∧ id)`

  with `B = Ric − p·(scal/n)·id` a positive semidefinite matrix (this is exactly `RicPinch p`).
  Since `A ∧ B` for positive semidefinite `A, B` has nonnegative complex sectional curvature
  (`Work.Diff.Alg.Pinch.EFun_knProd_psd`), and `(id ∧ id)` contributes `2 • EFun (Iso n)`, one gets

  `4·a·p·(scal/n)² · EFun (Iso n) x y z w ≤ EFun (bwCorr a b S) x y z w`,

  and the left hand side is strictly positive for `n ≥ 3` since `scalAlg S > 0` (`InPIC2 S` and
  `S ≠ 0` force it, `Work.Diff.Alg.Pinch.inPIC2_comp_bound`) and `EFun (Iso n) x y z w > 0` on a
  nondegenerate direction.  The case `n = 2` is vacuous: then `S = c • Iso 2` and a degenerate,
  nondegenerate direction forces `c = 0`, i.e. `S = 0`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary contractions of `id2` -/

/-- The diagonal contraction `∑ᵢⱼ id2 i j * (v i * v j) = ∑ᵢ v i * v i`. -/
lemma chatb_sum_id2_mul' (v : Fin n → ℝ) :
    (∑ i, ∑ j, id2 n i j * (v i * v j)) = ∑ i, v i * v i := by
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_eq_single i]
  · simp [id2]
  · intro j _ hj
    have hji : ¬ (i = j) := fun h => hj h.symm
    simp [id2, hji]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ## Linearity of `EFun` in the tensor variable -/

/-- `EFun` is additive in the curvature tensor. -/
lemma chatb_EFun_add (Y Z : Curv4 n) (x y z w : Fin n → ℝ) :
    Q2P.EFun (Y + Z) x y z w = Q2P.EFun Y x y z w + Q2P.EFun Z x y z w :=
  Cone.EF_add Y Z x y z w

/-- `EFun` is homogeneous in the curvature tensor. -/
lemma chatb_EFun_smul (c : ℝ) (Y : Curv4 n) (x y z w : Fin n → ℝ) :
    Q2P.EFun (c • Y) x y z w = c * Q2P.EFun Y x y z w :=
  Cone.EF_smul c Y x y z w

/-- `knProd (id2 n) (id2 n) = 2 • Iso n` contributes `2 · EFun (Iso n)`. -/
lemma chatb_EFun_knProd_id2_id2 (x y z w : Fin n → ℝ) :
    Q2P.EFun (knProd (id2 n) (id2 n)) x y z w = 2 * Q2P.EFun (Iso n) x y z w := by
  rw [knProd_id2_id2, chatb_EFun_smul]

/-- The round sphere lies in the cone, so its quartic form is nonnegative. -/
lemma chatb_EFun_Iso_nonneg (x y z w : Fin n → ℝ) : 0 ≤ Q2P.EFun (Iso n) x y z w :=
  Cone.inPIC2_iso n x y z w

/-! ## Nonnegativity of the `knProd`-pieces -/

/-- `Ric₀ ∘ Ric₀` is positive semidefinite for an algebraic curvature tensor (it is the square of
the symmetric matrix `ric0 S`). -/
lemma chatb_ric0sq_psd {S : Curv4 n} (hS : IsAlgCurv S) (v : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, ric0sq S i j * v i * v j := by
  have hsymm : ∀ i j, ric0 S i j = ric0 S j i := fun i j => ric0_symm hS i j
  have key : (∑ i, ∑ j, ric0sq S i j * v i * v j)
      = ∑ k, (∑ i, ric0 S i k * v i) * (∑ j, ric0 S j k * v j) := by
    simp only [ric0sq]
    have e1 : ∀ i j : Fin n, (∑ k, ric0 S i k * ric0 S k j) * v i * v j
        = ∑ k, (ric0 S i k * ric0 S k j) * v i * v j := by
      intro i j; rw [Finset.sum_mul, Finset.sum_mul]
    simp only [e1]
    calc ∑ i, ∑ j, ∑ k, (ric0 S i k * ric0 S k j) * v i * v j
        = ∑ i, ∑ k, ∑ j, (ric0 S i k * ric0 S k j) * v i * v j := by
          apply Finset.sum_congr rfl; intro i _
          exact Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, (ric0 S i k * ric0 S k j) * v i * v j := Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, (ric0 S i k * v i) * (ric0 S j k * v j) := by
          apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [hsymm k j]; ring
      _ = ∑ k, (∑ i, ric0 S i k * v i) * (∑ j, ric0 S j k * v j) := by
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.sum_mul_sum]
  rw [key]
  exact Finset.sum_nonneg (fun k _ => mul_self_nonneg _)

/-- `Ric − c·id` is positive semidefinite as soon as the quadratic form of `Ric` dominates
`c · ‖v‖²` (which is exactly what `RicPinch` says for `c = p · scal/n`). -/
lemma chatb_ric_sub_smul_id2_psd {S : Curv4 n} {c : ℝ}
    (hric : ∀ v : Fin n → ℝ, c * (∑ i, v i * v i) ≤ ∑ i, ∑ j, ric S i j * v i * v j)
    (v : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, (ric S i j - c * id2 n i j) * v i * v j := by
  have hsplit : (∑ i, ∑ j, (ric S i j - c * id2 n i j) * v i * v j)
      = (∑ i, ∑ j, ric S i j * v i * v j)
        - c * (∑ i, ∑ j, id2 n i j * (v i * v j)) := by
    have h1 : ∀ i j : Fin n,
        (ric S i j - c * id2 n i j) * v i * v j
          = ric S i j * v i * v j - c * id2 n i j * (v i * v j) := by
      intro i j; ring
    simp only [h1, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hsplit, chatb_sum_id2_mul']
  linarith [hric v]

/-! ## Nonnegativity of the coefficient of `id ∧ id` -/

/-- The last coefficient of `bwCorr (ccA n b) b S` is nonnegative: it equals
`2b²(1-2b)(1+(n-2)b) / (n (1+(n-2)b²) (1+2(n-1)ccA n b))`. -/
lemma chatb_c4_nonneg (n : ℕ) (hn : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    0 ≤ ((n : ℝ) * b ^ 2 * (1 - 2 * b) - 2 * (ccA n b - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
          / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * ccA n b)) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hD : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b ^ 2 := by nlinarith [sq_nonneg b]
  have hA : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * ccA n b := by
    have := ccA_pos hn1 hb hb'
    nlinarith
  have h2a : 2 * ccA n b * (1 + ((n : ℝ) - 2) * b ^ 2)
      = 2 * b + ((n : ℝ) - 2) * b ^ 2 := by
    have hDnz : (1 : ℝ) + ((n : ℝ) - 2) * b ^ 2 ≠ 0 := ne_of_gt hD
    have h1 : ccA n b * (1 + ((n : ℝ) - 2) * b ^ 2)
        = (2 * b + ((n : ℝ) - 2) * b ^ 2) / 2 := by
      rw [ccA, div_mul_eq_mul_div, mul_div_mul_right _ _ hDnz]
    calc 2 * ccA n b * (1 + ((n : ℝ) - 2) * b ^ 2)
        = 2 * (ccA n b * (1 + ((n : ℝ) - 2) * b ^ 2)) := by ring
      _ = 2 * ((2 * b + ((n : ℝ) - 2) * b ^ 2) / 2) := by rw [h1]
      _ = 2 * b + ((n : ℝ) - 2) * b ^ 2 := by ring_nf
  have hnum_mul :
      ((n : ℝ) * b ^ 2 * (1 - 2 * b) - 2 * (ccA n b - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
          * (1 + ((n : ℝ) - 2) * b ^ 2)
        = 2 * b ^ 2 * (1 - 2 * b) * (1 + ((n : ℝ) - 2) * b) := by
    have hexp : ((n : ℝ) * b ^ 2 * (1 - 2 * b)
          - 2 * (ccA n b - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
          * (1 + ((n : ℝ) - 2) * b ^ 2)
        = (n : ℝ) * b ^ 2 * (1 - 2 * b) * (1 + ((n : ℝ) - 2) * b ^ 2)
          - (2 * ccA n b * (1 + ((n : ℝ) - 2) * b ^ 2)) * (1 - 2 * b + (n : ℝ) * b ^ 2)
          + (2 * b * (1 + ((n : ℝ) - 2) * b ^ 2)) * (1 - 2 * b + (n : ℝ) * b ^ 2) := by
      ring
    rw [hexp, h2a]
    ring
  have hnum : (n : ℝ) * b ^ 2 * (1 - 2 * b)
        - 2 * (ccA n b - b) * (1 - 2 * b + (n : ℝ) * b ^ 2)
      = 2 * b ^ 2 * (1 - 2 * b) * (1 + ((n : ℝ) - 2) * b) / (1 + ((n : ℝ) - 2) * b ^ 2) := by
    rw [eq_div_iff (ne_of_gt hD)]
    exact hnum_mul
  rw [hnum, div_div]
  apply div_nonneg
  · have h2 : (0 : ℝ) ≤ 1 - 2 * b := by linarith
    have h4 : (0 : ℝ) ≤ 1 + ((n : ℝ) - 2) * b := by
      have : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
      nlinarith [hb.le]
    have h3 : (0 : ℝ) ≤ 2 * b ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg h3 h2) h4
  · exact le_of_lt (mul_pos hD (mul_pos hnR hA))

/-! ## Positivity of the difference tensor -/

/-- The Böhm–Wilking identity (Böhm–Wilking, Theorem 2): the pulled-back reaction term is the
reaction term plus the correction tensor. -/
theorem chatb_bwDef_zero (m : ℕ) (a b : ℝ)
    (ha : 1 + 2 * ((m : ℝ) - 1) * a ≠ 0) (hb : 1 + ((m : ℝ) - 2) * b ≠ 0)
    {R : Curv4 m} (hR : IsAlgCurv R) :
    linv a b (Q (ell a b R)) = Q R + bwCorr a b R := by
  have h := bwDef_of_children
    (fun m A hA W hW hric => funext (fun i => funext (fun j => funext (fun k => funext (fun l =>
      BQ_knProd_W m hA hW hric i j k l)))))
    (fun m a b ha hb A hA => linv_Q_ell_knProd_full m a b ha hb hA)
    m a b ha hb hR
  simp only [bwDef] at h
  exact sub_eq_zero.mp h

/-- **Lower bound for the difference tensor.**  For `S` an algebraic curvature tensor satisfying
the Ricci pinching `Ric ≥ p·scal/n` (with `p = ccP n b`), the quartic form of the Böhm–Wilking
difference tensor dominates `4·a·p·(scal/n)²·EFun (Iso n)`. -/
theorem chatb_bwCorr_bound (n : ℕ) (hn : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2)
    {S : Curv4 n} (hS : IsAlgCurv S) (hric : RicPinch (ccP n b) S)
    (x y z w : Fin n → ℝ) :
    4 * ccA n b * ccP n b * (scalAlg S / (n : ℝ)) ^ 2 * Q2P.EFun (Iso n) x y z w
      ≤ Q2P.EFun (bwCorr (ccA n b) b S) x y z w := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hIso : 0 ≤ Q2P.EFun (Iso n) x y z w := chatb_EFun_Iso_nonneg x y z w
  have hBsym : ∀ i j : Fin n, (ric S i j - (ccP n b * (scalAlg S / (n : ℝ))) * id2 n i j)
      = (ric S j i - (ccP n b * (scalAlg S / (n : ℝ))) * id2 n j i) := by
    intro i j
    rw [ric_symm hS i j]
    by_cases h : i = j
    · subst h; rfl
    · simp [id2, h, Ne.symm h]
  have hBpsd : ∀ v : Fin n → ℝ,
      0 ≤ ∑ i, ∑ j, (ric S i j - (ccP n b * (scalAlg S / (n : ℝ))) * id2 n i j) * v i * v j := by
    intro v
    apply chatb_ric_sub_smul_id2_psd
    intro u
    have h := hric u
    rw [show (ccP n b * (scalAlg S / (n : ℝ))) * (∑ i, u i * u i)
        = (ccP n b * scalAlg S / (n : ℝ)) * (∑ i, u i * u i) from by ring]
    exact h
  have hC0sym : ∀ i j : Fin n, ric0sq S i j = ric0sq S j i := by
    intro i j
    simp only [ric0sq]
    apply Finset.sum_congr rfl; intro k _
    rw [ric0_symm hS i k, ric0_symm hS k j]
    ring
  have hC0psd : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, ric0sq S i j * v i * v j := chatb_ric0sq_psd hS
  have hid2sym : ∀ i j : Fin n, id2 n i j = id2 n j i := by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp [id2, h, Ne.symm h]
  have hid2psd : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, id2 n i j * v i * v j := by
    intro v
    rw [show (∑ i, ∑ j, id2 n i j * v i * v j) = ∑ i, v i * v i from by
      rw [← chatb_sum_id2_mul']
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have h1 : 0 ≤ Q2P.EFun (knProd (fun i j => ric S i j - (ccP n b * (scalAlg S / (n : ℝ))) * id2 n i j)
      (fun i j => ric S i j - (ccP n b * (scalAlg S / (n : ℝ))) * id2 n i j)) x y z w :=
    EFun_knProd_psd n hBsym hBsym hBpsd hBpsd x y z w
  have h2 : 0 ≤ Q2P.EFun (knProd (ric0sq S) (id2 n)) x y z w :=
    EFun_knProd_psd n hC0sym hid2sym hC0psd hid2psd x y z w
  have h3 : Q2P.EFun (knProd (id2 n) (id2 n)) x y z w = 2 * Q2P.EFun (Iso n) x y z w :=
    chatb_EFun_knProd_id2_id2 x y z w
  have hc1 : 0 ≤ 2 * ccA n b / (1 - ccP n b) := by
    have ha := ccA_pos hn1 hb hb'
    have h1mp : 0 < 1 - ccP n b := by
      have hD : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b ^ 2 := by nlinarith [sq_nonneg b]
      have heq : 1 - ccP n b = 1 / (1 + ((n : ℝ) - 2) * b ^ 2) := by
        rw [ccP]
        have hsub : (1 : ℝ) - (1 - 1 / (1 + ((n : ℝ) - 2) * b ^ 2))
            = 1 / (1 + ((n : ℝ) - 2) * b ^ 2) := by ring
        rw [hsub]
      rw [heq]; positivity
    positivity
  have hc2 : 0 ≤ 2 * b ^ 2 := by positivity
  have hc3 : 2 * ccA n b * ccP n b * (scalAlg S / (n : ℝ)) ^ 2
      ≤ 2 * ccA n b * ccP n b * (scalAlg S / (n : ℝ)) ^ 2
        + (((n : ℝ) * b ^ 2 * (1 - 2 * b) - 2 * (ccA n b - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
            / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * ccA n b))) * ric0Frob2 S := by
    have hc4 := chatb_c4_nonneg n hn hb hb'
    have hfrob : 0 ≤ ric0Frob2 S := by
      simp only [ric0Frob2]
      exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_self_nonneg _))
    nlinarith [mul_nonneg hc4 hfrob]
  have hval : Q2P.EFun (bwCorr (ccA n b) b S) x y z w
      = (2 * ccA n b / (1 - ccP n b))
          * Q2P.EFun (knProd (fun i j => ric S i j - (ccP n b * (scalAlg S / (n : ℝ))) * id2 n i j)
              (fun i j => ric S i j - (ccP n b * (scalAlg S / (n : ℝ))) * id2 n i j)) x y z w
        + 2 * b ^ 2 * Q2P.EFun (knProd (ric0sq S) (id2 n)) x y z w
        + (2 * ccA n b * ccP n b * (scalAlg S / (n : ℝ)) ^ 2
            + (((n : ℝ) * b ^ 2 * (1 - 2 * b) - 2 * (ccA n b - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
                / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * ccA n b))) * ric0Frob2 S)
          * Q2P.EFun (knProd (id2 n) (id2 n)) x y z w := by
    rw [bwCorr_decomp n hn hb hb' S]
    rw [chatb_EFun_add, chatb_EFun_add, chatb_EFun_smul, chatb_EFun_smul, chatb_EFun_smul]
  have hA1 : 0 ≤ (2 * ccA n b / (1 - ccP n b))
      * Q2P.EFun (knProd (fun i j => ric S i j - (ccP n b * (scalAlg S / (n : ℝ))) * id2 n i j)
          (fun i j => ric S i j - (ccP n b * (scalAlg S / (n : ℝ))) * id2 n i j)) x y z w :=
    mul_nonneg hc1 h1
  have hA2 : 0 ≤ 2 * b ^ 2 * Q2P.EFun (knProd (ric0sq S) (id2 n)) x y z w := mul_nonneg hc2 h2
  have hA3 : 4 * ccA n b * ccP n b * (scalAlg S / (n : ℝ)) ^ 2 * Q2P.EFun (Iso n) x y z w
      ≤ (2 * ccA n b * ccP n b * (scalAlg S / (n : ℝ)) ^ 2
          + (((n : ℝ) * b ^ 2 * (1 - 2 * b) - 2 * (ccA n b - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
              / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * ccA n b))) * ric0Frob2 S)
        * (2 * Q2P.EFun (Iso n) x y z w) := by
    nlinarith [hc3, hIso]
  rw [hval, h3]
  linarith [hA1, hA2, hA3]


/-! ## The target -/

theorem ChatT_strict_pic_b (n : ℕ) (hn : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S) (hS0 : S ≠ 0)
    (hP : Submission.Diff.Alg.InPIC2 S) (hric : Work.Diff.Alg.Pinch.RicPinch (ccP n b) S) :
    ∀ x y z w : Fin n → ℝ,
      Work.Diff.Alg.Q2P.EFun S x y z w = 0 →
      Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w ≠ 0 →
      0 < Work.Diff.Alg.Q2P.EFun
        (Work.Diff.Alg.Pinch.linv (ccA n b) b
          (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell (ccA n b) b S))) x y z w := by
  intro x y z w hdeg hIso
  by_cases hn3 : 3 ≤ n
  · have hn1 : 1 ≤ n := by omega
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hBW : linv (ccA n b) b (Q (ell (ccA n b) b S)) = Q S + bwCorr (ccA n b) b S :=
      chatb_bwDef_zero n (ccA n b) b (ccA_denom_ne hn1 hb hb') (ccB_denom_ne hn0 hb hb') hS
    rw [hBW, chatb_EFun_add]
    have hQ : 0 ≤ Q2P.EFun (Q S) x y z w := inPIC2_Q_pointwise n S hS hP x y z w hdeg
    have hD := chatb_bwCorr_bound n hn hb hb' hS hric x y z w
    have hIso_pos : 0 < Q2P.EFun (Iso n) x y z w :=
      lt_of_le_of_ne (chatb_EFun_Iso_nonneg x y z w) (Ne.symm hIso)
    have hscal : 0 < scalAlg S := by
      rcases lt_or_eq_of_le ((inPIC2_metric_basic n).2.2 S hP) with h | h
      · exact h
      · exact absurd ((inPIC2_comp_bound n).2 S hP h.symm) hS0
    have ha : 0 < ccA n b := ccA_pos hn1 hb hb'
    have hp : 0 < ccP n b := by
      have hDpos : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b ^ 2 := by nlinarith [sq_nonneg b]
      have hnum : (0 : ℝ) < ((n : ℝ) - 2) * b ^ 2 := by
        have hn3R : (2 : ℝ) < (n : ℝ) := by exact_mod_cast hn3
        have : (0 : ℝ) < (n : ℝ) - 2 := by linarith
        positivity
      have heq : ccP n b = (((n : ℝ) - 2) * b ^ 2) / (1 + ((n : ℝ) - 2) * b ^ 2) := by
        have hDne : (1 : ℝ) + ((n : ℝ) - 2) * b ^ 2 ≠ 0 := ne_of_gt hDpos
        have h1 : (1 : ℝ) - 1 / (1 + ((n : ℝ) - 2) * b ^ 2)
            = ((n : ℝ) - 2) * b ^ 2 / (1 + ((n : ℝ) - 2) * b ^ 2) := by
          calc (1 : ℝ) - 1 / (1 + ((n : ℝ) - 2) * b ^ 2)
              = (1 + ((n : ℝ) - 2) * b ^ 2) / (1 + ((n : ℝ) - 2) * b ^ 2)
                  - 1 / (1 + ((n : ℝ) - 2) * b ^ 2) := by rw [div_self hDne]
            _ = ((1 + ((n : ℝ) - 2) * b ^ 2) - 1) / (1 + ((n : ℝ) - 2) * b ^ 2) := by
                  rw [div_sub_div_same]
            _ = ((n : ℝ) - 2) * b ^ 2 / (1 + ((n : ℝ) - 2) * b ^ 2) := by
                  congr 1; ring
        rw [ccP]
        exact h1
      rw [heq]
      exact div_pos hnum hDpos
    have hlbar : 0 < scalAlg S / (n : ℝ) := div_pos hscal hnR
    have hpos : 0 < 4 * ccA n b * ccP n b * (scalAlg S / (n : ℝ)) ^ 2
        * Q2P.EFun (Iso n) x y z w := by
      have h4 : (0 : ℝ) < 4 := by norm_num
      have hs : 0 < (scalAlg S / (n : ℝ)) ^ 2 := by positivity
      exact mul_pos (mul_pos (mul_pos (mul_pos h4 ha) hp) hs) hIso_pos
    linarith
  · obtain rfl : n = 2 := by omega
    have hSiso : S = (S 0 1 0 1) • Iso 2 := IsAlgCurv_fin_two hS
    have hzero : S 0 1 0 1 * Q2P.EFun (Iso 2) x y z w = 0 := by
      have h := hdeg
      rw [hSiso, chatb_EFun_smul] at h
      exact h
    have hc0 : S 0 1 0 1 = 0 := (mul_eq_zero.mp hzero).resolve_right hIso
    exact absurd (by rw [hSiso, hc0, zero_smul]) hS0

end Work.Diff.Alg.Pinch
