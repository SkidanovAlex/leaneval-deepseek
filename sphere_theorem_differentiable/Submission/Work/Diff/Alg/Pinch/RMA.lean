import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.BQDefs
import Submission.Work.Diff.Alg.Pinch.linv_Q_ell
import Submission.Work.Diff.Alg.Pinch.scalAlg_linv
import Submission.Work.Diff.Alg.Pinch.ric_knProd_id2
import Submission.Work.Diff.Alg.Pinch.scalAlg_knProd
import Submission.Work.Diff.Alg.Pinch.ric_Q
import Submission.Work.Diff.Alg.Pinch.scalAlg_Q
import Submission.Work.Diff.Alg.Pinch.ell_isAlgCurv
import Submission.Work.Diff.Alg.Pinch.Q_isAlgCurv
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.Pinch.eq_zero_of_secK_eq_zero
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Clash-free copy of the branch `1 / 2 < a` quantitative Ricci margin

Verbatim copy of the bodies of `ChatT_ric_a_defs.lean`, `qfm_ric_Q.lean`, `tr_NzK_eq.lean`,
`qfm_bwCorr_half.lean`, `scalAlg_linv_Q_ell_half.lean`, `ChatT_strict_ric_a.lean` and
`ric_margin_a.lean`, concatenated into a single module, in which every declaration that also
occurs in the ambient imported environment has been given a `_rma` suffix, and the imports of
the concatenated modules are dropped (their contents are inlined).  No other change.
-/

namespace Work.Diff.Alg.Pinch


/-!
# Self-contained auxiliary lemmas for `Work.Diff.Alg.Pinch.ChatT_strict_ric_a`

This module deliberately avoids the (concurrently edited) modules `RicFormDefs` / `RicFormAux`:
everything used by the strict Ricci-form statement is set up here.

Vocabulary:
* `qfm M v = ∑ᵢⱼ Mᵢⱼ vᵢ vⱼ` — the quadratic form of a `(0,2)`-tensor;
* `NzK R v p q = ∑ᵢⱼ R i p j q vᵢ vⱼ` — the curvature matrix of `R` in the direction `v`;
* `sqM M i j = ∑ₖ M i k M k j` — the matrix square.
-/


open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-- The quadratic form of a `(0,2)`-tensor. -/
noncomputable def qfm (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : ℝ := ∑ i, ∑ j, M i j * v i * v j

/-- The matrix square. -/
noncomputable def sqM (M : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k, M i k * M k j

/-- The curvature matrix of `R` in the direction `v`. -/
noncomputable def NzK (R : Curv4 n) (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun p q => ∑ i, ∑ j, R i p j q * v i * v j

/-- The Ricci matrix. -/
noncomputable def ricM (T : Curv4 n) : Matrix (Fin n) (Fin n) ℝ := fun i j => ric T i j

/-! ## Elementary rewriting -/

lemma qfm_add (M N : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    qfm (M + N) v = qfm M v + qfm N v := by
  simp only [qfm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma qfm_sub (M N : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    qfm (M - N) v = qfm M v - qfm N v := by
  simp only [qfm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma qfm_smul (c : ℝ) (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    qfm (c • M) v = c * qfm M v := by
  simp only [qfm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

lemma qfm_neg (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : qfm (-M) v = - qfm M v := by
  have h : (-M) = (-1 : ℝ) • M := by funext i j; simp
  rw [h, qfm_smul]; ring

lemma qfm_id2 (v : Fin n → ℝ) : qfm (id2 n) v = ∑ i, v i * v i := by
  simp only [qfm, id2]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [if_neg (Ne.symm hj)]; ring
  · intro h; exact absurd (Finset.mem_univ i) h

lemma qfm_const_smul_id2 (c : ℝ) (v : Fin n → ℝ) :
    qfm (c • id2 n) v = c * (∑ i, v i * v i) := by
  rw [qfm_smul, qfm_id2]

/-- `qfm M v = v ⬝ᵥ (M *ᵥ v)`. -/
lemma qfm_eq_dotProduct (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    qfm (fun i j => M i j) v = v ⬝ᵥ (M *ᵥ v) := by
  simp only [qfm, dotProduct, mulVec]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

/-- The quadratic form of `M - c • 1`. -/
lemma qfm_sub_smul_one (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (v : Fin n → ℝ) :
    qfm (fun i j => (M - c • 1) i j) v = qfm (fun i j => M i j) v - c * (∑ i, v i * v i) := by
  have h : (fun i j : Fin n => (M - c • 1) i j) = (fun i j => M i j) - c • (id2 n) := by
    funext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, id2]
  rw [h, qfm_sub, qfm_const_smul_id2]

/-! ## The Ricci tensor of a Kulkarni–Nomizu product -/

/-- `ric (A ∧ B) i j = (tr A) B i j + (tr B) A i j - (A B) i j - (B A) i j`. -/
theorem ric_knProd_gen (n : ℕ) (A B : Fin n → Fin n → ℝ) (i j : Fin n) :
    ric (knProd A B) i j
      = (∑ k, A k k) * B i j + (∑ k, B k k) * A i j
        - (∑ k, A i k * B k j) - (∑ k, B i k * A k j) := by
  have hpt : ∀ k : Fin n,
      knProd A B k i k j = A k k * B i j + (-(A k j * B i k)) + (-(A i k * B k j))
        + A i j * B k k := by
    intro k; simp only [knProd]; ring
  simp only [ric, hpt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => mul_comm (A i j) (B k k))]
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => mul_comm (A k j) (B i k))]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- The trace of the traceless Ricci tensor vanishes (no algebraicity needed). -/
lemma ric0_diag_sum (Y : Curv4 n) : (∑ i, ric0 Y i i) = 0 := by
  have hsum : (∑ i, ric0 Y i i)
      = (∑ i, ric Y i i) - (scalAlg Y / (n : ℝ)) * (∑ i : Fin n, id2 n i i) := by
    simp only [ric0, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
  have hid : (∑ i : Fin n, id2 n i i) = (n : ℝ) := by simp [id2]
  have hsc : (∑ i, ric Y i i) = scalAlg Y := by
    simp only [ric, scalAlg]
    rw [Finset.sum_comm]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
    rw [hsum, hid, hsc]
    field_simp
    ring

/-! ## Symmetry of `Ric₀²` and its trace -/

lemma ric0sq_symm_rma {S : Curv4 n} (hS : IsAlgCurv S) (i j : Fin n) :
    ric0sq S i j = ric0sq S j i := by
  simp only [ric0sq]
  apply Finset.sum_congr rfl; intro k _
  rw [ric0_symm hS i k, ric0_symm hS k j]
  ring

lemma sum_ric0sq_diag_eq {S : Curv4 n} (hS : IsAlgCurv S) :
    (∑ i, ric0sq S i i) = ric0Frob2 S := by
  simp only [ric0sq, ric0Frob2]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _
  rw [ric0_symm hS k i]

/-! ## Positive semidefinite pairings -/

/-- The Frobenius pairing of two positive semidefinite matrices is nonnegative. -/
lemma psd_pairing_rma {A N : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hN : N.PosSemidef) :
    0 ≤ ∑ i, ∑ j, A i j * N i j := by
  have h := (hA.hadamard hN).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  rw [star_trivial] at h
  simpa [dotProduct, mulVec, Matrix.hadamard, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_assoc]
    using h

/-- `Ric - (p · scal / n) · 1` is positive semidefinite under `RicPinch p S`. -/
lemma ricM_sub_posSemidef {S : Curv4 n} (hS : IsAlgCurv S) {p : ℝ} (hric : RicPinch p S) :
    (ricM S - (p * scalAlg S / (n : ℝ)) • 1).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    simp only [star_trivial, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      ricM]
    rw [ric_symm hS j i]
    by_cases h : i = j
    · subst h; ring
    · rw [if_neg h, if_neg (fun hh : j = i => h hh.symm)]
  · intro x
    rw [star_trivial]
    have hx : x ⬝ᵥ ((ricM S - (p * scalAlg S / (n : ℝ)) • 1) *ᵥ x)
        = qfm (fun i j => (ricM S - (p * scalAlg S / (n : ℝ)) • 1) i j) x :=
      (qfm_eq_dotProduct _ x).symm
    rw [hx, qfm_sub_smul_one]
    simp only [ricM, qfm]
    have := hric x
    linarith

/-- Tightness of the Ricci pinching at `v` makes `v` an eigenvector of `Ric` with eigenvalue
`p · scal S / n`. -/
theorem ric_mulVec_of_tight {S : Curv4 n} (hS : IsAlgCurv S) {p : ℝ} (hric : RicPinch p S)
    {v : Fin n → ℝ}
    (htight : (p * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
      = ∑ i, ∑ j, ric S i j * v i * v j) :
    ∀ i, (∑ j, ric S i j * v j) = (p * scalAlg S / (n : ℝ)) * v i := by
  set c : ℝ := p * scalAlg S / (n : ℝ) with hc
  have hA : (ricM S - c • 1).PosSemidef := by
    rw [hc]; exact ricM_sub_posSemidef hS hric
  have hzero : v ⬝ᵥ ((ricM S - c • 1) *ᵥ v) = 0 := by
    have hx : v ⬝ᵥ ((ricM S - c • 1) *ᵥ v)
        = qfm (fun i j => (ricM S - c • 1) i j) v := (qfm_eq_dotProduct _ v).symm
    rw [hx, qfm_sub_smul_one]
    simp only [ricM]
    rw [hc] at htight
    have ht2 : qfm (fun i j => ric S i j) v
        = ∑ i, ∑ j, ric S i j * v i * v j := rfl
    rw [ht2]
    linarith
  have hmv : (ricM S - c • 1) *ᵥ v = 0 := (hA.dotProduct_mulVec_zero_iff).mp hzero
  intro i
  have hi : ((ricM S - c • 1) *ᵥ v) i = 0 := by rw [hmv]; rfl
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ricM,
    Matrix.mulVec, dotProduct] at hi
  have hsplit : (∑ j, (ric S i j - c * (if i = j then (1 : ℝ) else 0)) * v j)
      = (∑ j, ric S i j * v j) - c * v i := by
    rw [show (∑ j, (ric S i j - c * (if i = j then (1 : ℝ) else 0)) * v j)
        = (∑ j, ric S i j * v j) - ∑ j, c * (if i = j then (1 : ℝ) else 0) * v j from by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; rw [if_neg (fun h : i = j => hj h.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hsplit] at hi
  linarith

/-! ## The curvature matrix in a direction -/

lemma NzK_apply (R : Curv4 n) (v : Fin n → ℝ) (p q : Fin n) :
    NzK R v p q = ∑ i, ∑ j, R i p j q * v i * v j := rfl

/-- Block exchange `∑_{p q i j} = ∑_{i j p q}` for a fourfold sum. -/
lemma sum4_swap_block_rma {m : ℕ} (g : Fin m → Fin m → Fin m → Fin m → ℝ) :
    (∑ p, ∑ q, ∑ i, ∑ j, g p q i j) = ∑ i, ∑ j, ∑ p, ∑ q, g p q i j := by
  calc (∑ p, ∑ q, ∑ i, ∑ j, g p q i j)
      = ∑ p, ∑ i, ∑ q, ∑ j, g p q i j := by
        apply Finset.sum_congr rfl; intro p _; rw [Finset.sum_comm]
    _ = ∑ i, ∑ p, ∑ q, ∑ j, g p q i j := by rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ p, ∑ q, g p q i j := by
        apply Finset.sum_congr rfl; intro i _
        calc (∑ p, ∑ q, ∑ j, g p q i j) = ∑ p, ∑ j, ∑ q, g p q i j := by
              apply Finset.sum_congr rfl; intro p _; rw [Finset.sum_comm]
          _ = ∑ j, ∑ p, ∑ q, g p q i j := by rw [Finset.sum_comm]

/-- `R4 R v z v z = ∑_{p q} NzK R v p q z_p z_q`. -/
theorem R4_eq_NzK (R : Curv4 n) (v z : Fin n → ℝ) :
    R4 R v z v z = ∑ p, ∑ q, NzK R v p q * z p * z q := by
  have h1 : R4 R v z v z = ∑ i, ∑ k, (∑ p, ∑ q, R i p k q * z p * z q) * v i * v k := by
    simp only [R4]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring
  rw [h1]
  have h2 : (∑ p, ∑ q, (∑ i, ∑ j, R i p j q * v i * v j) * z p * z q)
      = ∑ i, ∑ k, (∑ p, ∑ q, R i p k q * z p * z q) * v i * v k := by
    have e1 : (∑ p, ∑ q, (∑ i, ∑ j, R i p j q * v i * v j) * z p * z q)
        = ∑ p, ∑ q, ∑ i, ∑ j, R i p j q * v i * v j * z p * z q := by
      apply Finset.sum_congr rfl; intro p _
      apply Finset.sum_congr rfl; intro q _
      simp only [Finset.sum_mul]
    rw [e1, sum4_swap_block_rma (fun p q i j => R i p j q * v i * v j * z p * z q)]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring
  simp only [NzK]
  exact h2.symm

/-- `NzK R v` is symmetric for an algebraic curvature tensor. -/
lemma NzK_symm {R : Curv4 n} (hR : IsAlgCurv R) (v : Fin n → ℝ) (p q : Fin n) :
    NzK R v p q = NzK R v q p := by
  simp only [NzK]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [hR.2.1 i p j q]
  ring

/-- `InPIC2` makes the curvature matrix `NzK R v` positive semidefinite. -/
lemma NzK_posSemidef {R : Curv4 n} (hR : IsAlgCurv R) (hP : InPIC2 R) (v : Fin n → ℝ) :
    (NzK R v).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    simp only [star_trivial]
    exact NzK_symm hR v j i
  · intro z
    rw [star_trivial]
    have hz : z ⬝ᵥ (NzK R v *ᵥ z) = qfm (fun p q => NzK R v p q) z :=
      (qfm_eq_dotProduct _ z).symm
    rw [hz, qfm, ← R4_eq_NzK R v z]
    exact inPIC2_R4_nonneg R hP v z






open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- A quadruple sum is invariant under the block permutation `(i,j,p,q) ↦ (p,q,i,j)`. -/
private lemma sum4_reindex (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ p, ∑ q, f i j p q) = ∑ p, ∑ q, ∑ i, ∑ j, f i j p q := by
  calc ∑ i, ∑ j, ∑ p, ∑ q, f i j p q
      = ∑ i, ∑ p, ∑ j, ∑ q, f i j p q := by
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.sum_comm]
    _ = ∑ p, ∑ i, ∑ j, ∑ q, f i j p q := by rw [Finset.sum_comm]
    _ = ∑ p, ∑ i, ∑ q, ∑ j, f i j p q := by
          apply Finset.sum_congr rfl; intro p _
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.sum_comm]
    _ = ∑ p, ∑ q, ∑ i, ∑ j, f i j p q := by
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.sum_comm]

/-- Pushing a scalar factor through a double sum on the right. -/
private lemma sum2_mul (f : Fin n → Fin n → ℝ) (c : ℝ) :
    (∑ p, ∑ q, f p q) * c = ∑ p, ∑ q, f p q * c := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_mul]

/-- Pulling a scalar factor out of a double sum on the left. -/
private lemma mul_sum2 (c : ℝ) (f : Fin n → Fin n → ℝ) :
    c * (∑ i, ∑ j, f i j) = ∑ i, ∑ j, c * f i j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]

theorem qfm_ric_Q (n : ℕ) {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) (v : Fin n → ℝ) :
    Work.Diff.Alg.Pinch.qfm (Work.Diff.Alg.Pinch.ric (Submission.Diff.Alg.Q R)) v
      = 2 * ∑ p, ∑ q, Work.Diff.Alg.Pinch.ric R p q * Work.Diff.Alg.Pinch.NzK R v p q := by
  have hric : ∀ i j : Fin n,
      ric (Q R) i j = 2 * ∑ p, ∑ q, ric R p q * R i p j q := ric_Q n hR
  have hstep1 : (∑ i, ∑ j, ric (Q R) i j * v i * v j)
      = 2 * ∑ i, ∑ j, (∑ p, ∑ q, ric R p q * R i p j q) * v i * v j := by
    rw [show (∑ i, ∑ j, ric (Q R) i j * v i * v j)
        = ∑ i, ∑ j, (2 * ∑ p, ∑ q, ric R p q * R i p j q) * v i * v j from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hric i j]))]
    rw [show (∑ i, ∑ j, (2 * ∑ p, ∑ q, ric R p q * R i p j q) * v i * v j)
        = ∑ i, ∑ j, 2 * ((∑ p, ∑ q, ric R p q * R i p j q) * v i * v j) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
  have hstep2 : (∑ i, ∑ j, (∑ p, ∑ q, ric R p q * R i p j q) * v i * v j)
      = ∑ i, ∑ j, ∑ p, ∑ q, (ric R p q * R i p j q) * v i * v j := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [sum2_mul (fun p q => ric R p q * R i p j q) (v i)]
    rw [sum2_mul (fun p q => (ric R p q * R i p j q) * v i) (v j)]
  have hstep3 : (∑ i, ∑ j, ∑ p, ∑ q, (ric R p q * R i p j q) * v i * v j)
      = ∑ p, ∑ q, ∑ i, ∑ j, (ric R p q * R i p j q) * v i * v j :=
    sum4_reindex (fun i j p q => (ric R p q * R i p j q) * v i * v j)
  have hstep4 : (∑ p, ∑ q, ∑ i, ∑ j, (ric R p q * R i p j q) * v i * v j)
      = ∑ p, ∑ q, ∑ i, ∑ j, ric R p q * (R i p j q * v i * v j) := by
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have hstep5 : (∑ p, ∑ q, ∑ i, ∑ j, ric R p q * (R i p j q * v i * v j))
      = ∑ p, ∑ q, ric R p q * (∑ i, ∑ j, R i p j q * v i * v j) := by
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [mul_sum2 (ric R p q) (fun i j => R i p j q * v i * v j)]
  have key : (∑ i, ∑ j, ric (Q R) i j * v i * v j)
      = 2 * ∑ p, ∑ q, ric R p q * (∑ i, ∑ j, R i p j q * v i * v j) := by
    rw [hstep1, hstep2, hstep3, hstep4, hstep5]
  simp only [qfm, NzK]
  rw [key]





open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- Rotating a triple sum: `∑ p ∑ i ∑ j f p i j = ∑ i ∑ j ∑ p f p i j`. -/
lemma sum3_swap_out {m : ℕ} (f : Fin m → Fin m → Fin m → ℝ) :
    (∑ p, ∑ i, ∑ j, f p i j) = ∑ i, ∑ j, ∑ p, f p i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]

/-- `R` is antisymmetric in its second pair (a consequence of the first-pair
antisymmetry and the pair-exchange symmetry). -/
lemma algCurv_snd_pair_antisymm {R : Curv4 n} (hR : IsAlgCurv R) (a b c d : Fin n) :
    R a b c d = - R a b d c := by
  rw [← hR.2.1 a b c d, hR.1 d c a b, hR.2.1 a b d c]

/-- Swapping the first two indices and the last two indices of `R`: `R i p j p = R p i p j`. -/
lemma algCurv_pair_four {R : Curv4 n} (hR : IsAlgCurv R) (i j p : Fin n) :
    R i p j p = R p i p j := by
  rw [← hR.2.1 p i p j, algCurv_snd_pair_antisymm hR p j p i, ← hR.2.1 p j i p,
    algCurv_snd_pair_antisymm hR i p p j]
  ring

theorem tr_NzK_eq (n : ℕ) {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) (v : Fin n → ℝ) :
    (∑ p, Work.Diff.Alg.Pinch.NzK R v p p)
      = ∑ i, ∑ j, Work.Diff.Alg.Pinch.ric R i j * v i * v j := by
  have key : ∀ i j p : Fin n, R i p j p = R p i p j := fun i j p => algCurv_pair_four hR i j p
  simp only [NzK, ric, Finset.sum_mul]
  rw [sum3_swap_out (fun p i j => R i p j p * v i * v j)]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro p _
  rw [key i j p]




/-!
# `qfm (ric (bwCorr a (1/2) S)) v` at a Ricci eigenvector

`Work.Diff.Alg.Pinch.qfm_bwCorr_half`: if `v` is an eigenvector of the Ricci tensor `ric S` with
eigenvalue `p · scal S / n`, then the quadratic form of the Ricci tensor of the Böhm–Wilking
correction `bwCorr a (1/2) S` (the `b = 1/2` branch of the family) is `|v|²` times an explicit
expression in `p`, `a`, `scalAlg S` and `ric0Frob2 S`.

The computation is the contraction of the four Kulkarni–Nomizu summands of `bwCorr`:

* `Ric₀ ∧ Ric₀`: `ric` gives `2 (tr Ric₀) · Ric₀ - 2 Ric₀²`, and `tr Ric₀ = 0`;
* `Ric ∧ Ric`: `ric` gives `2 (tr Ric) · Ric - 2 Ric²`, and `tr Ric = scalAlg`;
* `Ric₀² ∧ id`: `ric` gives `(tr Ric₀²) · id + (n-2) Ric₀²`, and `tr Ric₀² = |Ric₀|²`;
* `id ∧ id`: `ric` gives `(2n-2) · id`.

The eigenvector hypothesis gives `Ric₀ v = (p-1) λ v` and `Ric₀² v = ((p-1) λ)² v`
(with `λ = scalAlg S / n`), which is what turns the four quadratic forms into multiples of `|v|²`.
-/


open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary contraction lemmas -/

/-- The Kronecker delta contracts a vector to itself. -/
private lemma sum_id2_mul_vec (v : Fin n → ℝ) (i : Fin n) :
    (∑ j, id2 n i j * v j) = v i := by
  rw [Finset.sum_eq_single i]
  · simp [id2]
  · intro j _ hj
    have hij : ¬ (i = j) := fun h => hj h.symm
    simp only [id2, hij, ite_false, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- If `M v = c v` then the quadratic form of `M` in the direction `v` is `c |v|²`. -/
private lemma qfm_of_mulVec {M : Fin n → Fin n → ℝ} {v : Fin n → ℝ} {c : ℝ}
    (h : ∀ i, (∑ j, M i j * v j) = c * v i) :
    qfm M v = c * (∑ i, v i * v i) := by
  simp only [qfm]
  calc ∑ i, ∑ j, M i j * v i * v j
      = ∑ i, (∑ j, M i j * v j) * v i := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _; ring
    _ = ∑ i, (c * v i) * v i := by
        apply Finset.sum_congr rfl; intro i _; rw [h i]
    _ = c * ∑ i, v i * v i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring

/-- If `M v = c v` then `M² v = c² v`. -/
private lemma sum_sq_mulVec {M : Fin n → Fin n → ℝ} {v : Fin n → ℝ} {c : ℝ}
    (h : ∀ i, (∑ j, M i j * v j) = c * v i) :
    ∀ i, (∑ j, (∑ k, M i k * M k j) * v j) = (c * c) * v i := by
  intro i
  calc ∑ j, (∑ k, M i k * M k j) * v j
      = ∑ k, ∑ j, (M i k * M k j) * v j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_mul]
    _ = ∑ k, M i k * (∑ j, M k j * v j) := by
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
    _ = ∑ k, M i k * (c * v k) := by
        apply Finset.sum_congr rfl; intro k _; rw [h k]
    _ = c * (∑ k, M i k * v k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring
    _ = c * (c * v i) := by rw [h i]
    _ = (c * c) * v i := by ring

/-- The traceless Ricci square of a `Ric₀`-eigenvector. -/
private lemma ric0sq_mulVec {S : Curv4 n} {v : Fin n → ℝ} {c : ℝ}
    (h : ∀ i, (∑ j, ric0 S i j * v j) = c * v i) :
    ∀ i, (∑ j, ric0sq S i j * v j) = (c * c) * v i := by
  intro i
  exact sum_sq_mulVec h i

/-! ## The four Kulkarni–Nomizu contractions -/

/-- `qfm (ric (Ric₀ ∧ Ric₀)) v = -2 · qfm (Ric₀²) v` (the trace of `Ric₀` vanishes). -/
private lemma qfm_ric_knProd_ric0_self {S : Curv4 n} (v : Fin n → ℝ) :
    qfm (ric (knProd (ric0 S) (ric0 S))) v = -2 * qfm (ric0sq S) v := by
  have hfun : ric (knProd (ric0 S) (ric0 S))
      = (2 * (∑ k, ric0 S k k)) • ric0 S - (2 : ℝ) • ric0sq S := by
    funext i j
    rw [ric_knProd_gen]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ric0sq]
    ring
  rw [hfun]
  simp only [qfm_sub, qfm_smul, ric0_diag_sum]
  ring

/-- `qfm (ric (Ric ∧ Ric)) v = 2 · scalAlg S · qfm (Ric) v - 2 · qfm (Ric²) v`. -/
private lemma qfm_ric_knProd_ric_self {S : Curv4 n} (hS : IsAlgCurv S) (v : Fin n → ℝ) :
    qfm (ric (knProd (ric S) (ric S))) v
      = 2 * scalAlg S * qfm (ric S) v
        - 2 * qfm (fun i j => ∑ k, ric S i k * ric S k j) v := by
  have hfun : ric (knProd (ric S) (ric S))
      = (2 * (∑ k, ric S k k)) • ric S
        - (2 : ℝ) • (fun i j => ∑ k, ric S i k * ric S k j) := by
    funext i j
    rw [ric_knProd_gen]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  simp only [qfm_sub, qfm_smul]
  rw [show (∑ k, ric S k k) = scalAlg S from (scalAlg_eq_sum_ric hS).symm]

/-- `qfm (ric (Ric₀² ∧ id)) v = |Ric₀|² · |v|² + (n-2) · qfm (Ric₀²) v`. -/
private lemma qfm_ric_knProd_ric0sq_id {S : Curv4 n} (hS : IsAlgCurv S) (v : Fin n → ℝ) :
    qfm (ric (knProd (ric0sq S) (id2 n))) v
      = ric0Frob2 S * (∑ i, v i * v i) + ((n : ℝ) - 2) * qfm (ric0sq S) v := by
  have hfun : ric (knProd (ric0sq S) (id2 n))
      = (∑ k, ric0sq S k k) • id2 n + ((n : ℝ) - 2) • ric0sq S := by
    funext i j
    rw [ric_knProd_id2]
    simp only [id2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun, qfm_add, qfm_smul, qfm_smul, qfm_id2, sum_ric0sq_diag_eq hS]

/-- `qfm (ric (id ∧ id)) v = (2n-2) · |v|²`. -/
private lemma qfm_ric_knProd_id_id (v : Fin n → ℝ) :
    qfm (ric (knProd (id2 n) (id2 n))) v = (2 * (n : ℝ) - 2) * (∑ i, v i * v i) := by
  have hsum : (∑ k, id2 n k k) = (n : ℝ) := by
    have hk : ∀ k : Fin n, id2 n k k = (1 : ℝ) := by intro k; simp [id2]
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hfun : ric (knProd (id2 n) (id2 n)) = (2 * (n : ℝ) - 2) • id2 n := by
    funext i j
    rw [ric_knProd_id2, hsum]
    simp only [id2, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, qfm_const_smul_id2]

/-! ## The `id ∧ id` coefficient of `bwCorr a (1/2)` -/

/-- The `id ∧ id` coefficient of `bwCorr a (1/2) S` rewrites to the form appearing in the target:
`-(a - 1/2)/(2(1 + 2(n-1)a))`. -/
private lemma coefD4_half (n : ℕ) (hn : 0 < n) (a frob : ℝ) :
    ((((n : ℝ) * (1/2 : ℝ) ^ 2 * (1 - 2 * (1/2 : ℝ))
          - 2 * (a - 1/2) * (1 - 2 * (1/2 : ℝ) + (n : ℝ) * (1/2 : ℝ) ^ 2))
        / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) * frob)
      = (-((a - 1/2) / (2 * (1 + 2 * ((n : ℝ) - 1) * a)))) * frob := by
  have hnR : ((n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  rcases eq_or_ne (1 + 2 * ((n : ℝ) - 1) * a) 0 with h | h
  · rw [h]; simp
  · have h2 : (2 : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a) ≠ 0 :=
      mul_ne_zero (by norm_num) h
    have h3 : (n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a) ≠ 0 := mul_ne_zero hnR h
    field_simp
    ring

/-! ## The main computation -/

private lemma qfm_bwCorr_half_aux (n : ℕ) (hn : 0 < n) (a p : ℝ) {S : Curv4 n}
    (hS : Submission.Diff.Alg.IsAlgCurv S) {v : Fin n → ℝ}
    (hev : ∀ i, (∑ j, ric S i j * v j)
        = (p * scalAlg S / (n : ℝ)) * v i) :
    qfm (ric (bwCorr a (1/2) S)) v
      = (∑ i, v i * v i) *
        ( -2 * (((n : ℝ) - 2)/4 - 2*a + 1) * (1 - p)^2 * (scalAlg S/(n:ℝ))^2
          + 4*a*( (n:ℝ) * (scalAlg S/(n:ℝ)) * (p * (scalAlg S/(n:ℝ)))
                  - (p * (scalAlg S/(n:ℝ)))^2 )
          + (1/2)*( ric0Frob2 S
                    + ((n:ℝ)-2)*(1-p)^2*(scalAlg S/(n:ℝ))^2 )
          + (-((a - 1/2)/(2*(1 + 2*((n:ℝ)-1)*a)))) * (2*(n:ℝ)-2) * ric0Frob2 S ) := by
  have hnR : ((n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  set L : ℝ := scalAlg S / (n : ℝ) with hL
  set P : ℝ := p * L with hP
  set V : ℝ := ∑ i, v i * v i with hV
  have hscal : (n : ℝ) * L = scalAlg S := by
    rw [hL]; exact mul_div_cancel₀ _ hnR
  have hmueq : ∀ i, (∑ j, ric S i j * v j) = P * v i := by
    intro i
    rw [hev i, hP]
    congr 1
    rw [hL]
    ring
  have hric0eq : ∀ i, (∑ j, ric0 S i j * v j) = ((p - 1) * L) * v i := by
    intro i
    have h1 : (∑ j, ric0 S i j * v j)
        = (∑ j, ric S i j * v j) - (scalAlg S / (n : ℝ)) * (∑ j, id2 n i j * v j) := by
      rw [show (∑ j, ric0 S i j * v j)
          = ∑ j, (ric S i j * v j - (scalAlg S / (n : ℝ)) * (id2 n i j * v j)) from by
        apply Finset.sum_congr rfl; intro j _
        simp only [ric0]
        ring]
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [Finset.mul_sum]
    rw [h1, sum_id2_mul_vec v i, hmueq i, hP, hL]
    ring
  have hric0sqeq : ∀ i, (∑ j, ric0sq S i j * v j) = (((p - 1) * L) * ((p - 1) * L)) * v i :=
    ric0sq_mulVec hric0eq
  have hricSqeq : ∀ i, (∑ j, (∑ k, ric S i k * ric S k j) * v j) = (P * P) * v i :=
    sum_sq_mulVec hmueq
  have hq0 : qfm (ric0sq S) v = (((p - 1) * L) * ((p - 1) * L)) * V := by
    rw [qfm_of_mulVec hric0sqeq, ← hV]
  have hqSq : qfm (fun i j => ∑ k, ric S i k * ric S k j) v = (P * P) * V := by
    rw [qfm_of_mulVec hricSqeq, ← hV]
  have hqR : qfm (ric S) v = P * V := by
    rw [qfm_of_mulVec hmueq, ← hV]
  have hK1 : qfm (ric (knProd (ric0 S) (ric0 S))) v
      = -2 * ((((p - 1) * L) * ((p - 1) * L)) * V) := by
    rw [qfm_ric_knProd_ric0_self v, hq0]
  have hK2 : qfm (ric (knProd (ric S) (ric S))) v
      = 2 * scalAlg S * (P * V) - 2 * ((P * P) * V) := by
    rw [qfm_ric_knProd_ric_self hS v, hqR, hqSq]
  have hK3 : qfm (ric (knProd (ric0sq S) (id2 n))) v
      = ric0Frob2 S * V + ((n : ℝ) - 2) * ((((p - 1) * L) * ((p - 1) * L)) * V) := by
    rw [qfm_ric_knProd_ric0sq_id hS v, ← hV, hq0]
  have hK4 : qfm (ric (knProd (id2 n) (id2 n))) v = (2 * (n : ℝ) - 2) * V := by
    rw [qfm_ric_knProd_id_id v, ← hV]
  have hbw : bwCorr a (1/2) S
      = (((n:ℝ) - 2) * (1/2:ℝ)^2 - 2 * (a - 1/2)) • knProd (ric0 S) (ric0 S)
        + (2*a) • knProd (ric S) (ric S)
        + (2*(1/2:ℝ)^2) • knProd (ric0sq S) (id2 n)
        + (((((n:ℝ)*(1/2:ℝ)^2*(1 - 2*(1/2:ℝ))
                - 2*(a - 1/2)*(1 - 2*(1/2:ℝ) + (n:ℝ)*(1/2:ℝ)^2))
              / ((n:ℝ) * (1 + 2*((n:ℝ)-1)*a))) * ric0Frob2 S)
            • knProd (id2 n) (id2 n)) := rfl
  have hricdist : ric ((((n:ℝ) - 2) * (1/2:ℝ)^2 - 2 * (a - 1/2)) • knProd (ric0 S) (ric0 S)
        + (2*a) • knProd (ric S) (ric S)
        + (2*(1/2:ℝ)^2) • knProd (ric0sq S) (id2 n)
        + (((((n:ℝ)*(1/2:ℝ)^2*(1 - 2*(1/2:ℝ))
                - 2*(a - 1/2)*(1 - 2*(1/2:ℝ) + (n:ℝ)*(1/2:ℝ)^2))
              / ((n:ℝ) * (1 + 2*((n:ℝ)-1)*a))) * ric0Frob2 S)
            • knProd (id2 n) (id2 n)))
      = (((n:ℝ) - 2) * (1/2:ℝ)^2 - 2 * (a - 1/2)) • ric (knProd (ric0 S) (ric0 S))
        + (2*a) • ric (knProd (ric S) (ric S))
        + (2*(1/2:ℝ)^2) • ric (knProd (ric0sq S) (id2 n))
        + (((((n:ℝ)*(1/2:ℝ)^2*(1 - 2*(1/2:ℝ))
                - 2*(a - 1/2)*(1 - 2*(1/2:ℝ) + (n:ℝ)*(1/2:ℝ)^2))
              / ((n:ℝ) * (1 + 2*((n:ℝ)-1)*a))) * ric0Frob2 S)
            • ric (knProd (id2 n) (id2 n))) := by
    funext i j
    simp only [ric_add_linv, ric_smul_linv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hbw, hricdist]
  simp only [qfm_add, qfm_smul]
  rw [hK1, hK2, hK3, hK4, ← hscal, coefD4_half n hn a (ric0Frob2 S)]
  ring

theorem qfm_bwCorr_half (n : ℕ) (a p : ℝ) {S : Submission.Diff.Alg.Curv4 n}
    (hS : Submission.Diff.Alg.IsAlgCurv S) {v : Fin n → ℝ}
    (hev : ∀ i, (∑ j, Work.Diff.Alg.Pinch.ric S i j * v j)
        = (p * Submission.Diff.Alg.scalAlg S / (n : ℝ)) * v i) :
    Work.Diff.Alg.Pinch.qfm (Work.Diff.Alg.Pinch.ric (Work.Diff.Alg.Pinch.bwCorr a (1/2) S)) v
      = (∑ i, v i * v i) *
        ( -2 * (((n : ℝ) - 2)/4 - 2*a + 1) * (1 - p)^2 * (Submission.Diff.Alg.scalAlg S/(n:ℝ))^2
          + 4*a*( (n:ℝ) * (Submission.Diff.Alg.scalAlg S/(n:ℝ)) * (p * (Submission.Diff.Alg.scalAlg S/(n:ℝ)))
                  - (p * (Submission.Diff.Alg.scalAlg S/(n:ℝ)))^2 )
          + (1/2)*( Work.Diff.Alg.Pinch.ric0Frob2 S
                    + ((n:ℝ)-2)*(1-p)^2*(Submission.Diff.Alg.scalAlg S/(n:ℝ))^2 )
          + (-((a - 1/2)/(2*(1 + 2*((n:ℝ)-1)*a)))) * (2*(n:ℝ)-2) * Work.Diff.Alg.Pinch.ric0Frob2 S ) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp only [qfm]
    simp
  · exact qfm_bwCorr_half_aux n hpos a p hS hev




/-!
# The scalar curvature of `linv a (1/2) (Q (ell a (1/2) S))`

Böhm–Wilking / Brendle–Schoen, the `b = 1/2` branch of the pinching-set family.  The main theorem
of this file computes, for an algebraic curvature tensor `S`, the scalar curvature of the image of
`Q (ell a (1/2) S)` under the explicit inverse `linv a (1/2)` of the Böhm–Wilking transform:

`scal (linv a (1/2) (Q (ell a (1/2) S)))`
`  = 2 * (n * (scal S / n)^2 * (1 + 2(n-1)a)^2 + (n^2/4) * |Ric_0 S|^2) / (1 + 2(n-1)a)`.

The computation splits into two independent pieces.

* `scalAlg_linv_half`: for `b = 1/2` and `D = 1 + 2(n-1)a` the scalar curvature of the inverse is
  `scal (linv a (1/2) Y) = scal Y / D`.  Indeed `linv a b Y = Y - c•(Ric_0 Y ∧ id) - c'•(id ∧ id)`
  with `scal (Ric_0 Y ∧ id) = 0` and `scal (id ∧ id) = (2n-2)·n`, and for `b = 1/2` the correction
  terms only rescale the scalar curvature by `(1 + 2(n-1)a)^{-1}` (this is `scalAlg_linv`).

* `ric_sq_sum_ell_half`: `scal (Q Y) = 2 |Ric Y|^2` (`scalAlg_Q`), and for `Y = ell a (1/2) S`
  the Ricci tensor is (`ric_ell_aux_rma`, `b = 1/2`)
  `Ric Y = (n/2)·Ric_0 S + (scal S · D / n)·id`,
  so, using the tracelessness `∑_i (Ric_0 S)_ii = 0` and `∑_{ij} δ_ij δ_ij = n`,
  `∑_{ij} (Ric Y)_ij^2 = (n^2/4)|Ric_0 S|^2 + n·(scal S / n)^2·D^2`.

The two are combined in the target `scalAlg_linv_Q_ell_half`.

(To keep this module independent of the concurrent work on the full Böhm–Wilking identity
`linv_Q_ell`, the three small index lemmas `anti34_aux`, `scalAlg_eq_sum_ric_aux_rma`,
`sum_id2_mul_aux_rma`, `sum_ric0_self_aux` and `ric_ell_aux_rma` are proved here from `Linv`.)
-/


open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Small index lemmas (self-contained) -/

/-- Antisymmetry in the last pair of indices. -/
lemma anti34_aux {W : Curv4 n} (hW : IsAlgCurv W) (i j k l : Fin n) : W i j l k = - W i j k l := by
  rw [← hW.2.1 i j l k, hW.1 k l i j, hW.2.1 i j k l]

/-- `scalAlg` is the trace of `ric`. -/
lemma scalAlg_eq_sum_ric_aux_rma {W : Curv4 n} (hW : IsAlgCurv W) : scalAlg W = ∑ i, ric W i i := by
  obtain ⟨hanti, hpair, hbian⟩ := hW
  simp only [scalAlg, ric]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  have h1 : W j i j i = - W i j j i := hanti i j j i
  have h2 : W i j j i = - W i j i j := anti34_aux ⟨hanti, hpair, hbian⟩ i j i j
  rw [h1, h2]; ring

/-- Contraction of a `(0,2)`-tensor against the identity. -/
lemma sum_id2_mul_aux_rma (f : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, id2 n p q * f p q) = ∑ p, f p p := by
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_eq_single p]
  · simp [id2]
  · intro q _ hq
    rw [id2, if_neg (fun h => hq h.symm), zero_mul]
  · intro hp; exact absurd (Finset.mem_univ p) hp

/-- The traceless Ricci tensor has vanishing trace. -/
lemma sum_ric0_self_aux (n : ℕ) (hn : (n : ℝ) ≠ 0) {R : Curv4 n} (hR : IsAlgCurv R) :
    (∑ k, ric0 R k k) = 0 := by
  have h1 : (∑ k : Fin n, ric0 R k k)
      = (∑ k : Fin n, (ric R k k - (scalAlg R / (n : ℝ)) * id2 n k k)) := by
    apply Finset.sum_congr rfl; intro k _; rw [ric0]
  rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [scalAlg_eq_sum_ric_aux_rma hR]
  have h2 : (∑ k : Fin n, id2 n k k) = (n : ℝ) := by simp [id2]
  rw [h2, div_mul_cancel₀ _ hn]
  ring

/-- The Ricci tensor of `ell a b R`. -/
lemma ric_ell_aux_rma (n : ℕ) (a b : ℝ) (hn : (n : ℝ) ≠ 0) {R : Curv4 n} (hR : IsAlgCurv R)
    (i j : Fin n) :
    ric (ell a b R) i j = (1 + ((n : ℝ) - 2) * b) * ric0 R i j
      + (scalAlg R * (1 + 2 * ((n : ℝ) - 1) * a) / (n : ℝ)) * id2 n i j := by
  have h1 := ric0_ell_linv n a b hn hR i j
  have h2 := scalAlg_ell_of_ne n a b hn hR
  have h3 : ric (ell a b R) i j
      = ric0 (ell a b R) i j + (scalAlg (ell a b R) / (n : ℝ)) * id2 n i j := by
    rw [ric0]; ring
  rw [h3, h1, h2]; ring

/-! ## The two pieces -/

/-- The scalar curvature of the Böhm–Wilking inverse `linv a (1/2)`:
`scal (linv a (1/2) Y) = scal Y / (1 + 2(n-1)a)` for an algebraic curvature tensor `Y`. -/
theorem scalAlg_linv_half (n : ℕ) (hn : 2 ≤ n) {a : ℝ} (ha : 1/2 < a)
    {Y : Submission.Diff.Alg.Curv4 n} (hY : Submission.Diff.Alg.IsAlgCurv Y) :
    Submission.Diff.Alg.scalAlg (Work.Diff.Alg.Pinch.linv a (1/2) Y)
      = Submission.Diff.Alg.scalAlg Y / (1 + 2*((n:ℝ)-1)*a) := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hb : 1 + ((n:ℝ) - 2) * (1/2) ≠ 0 := by
    have h2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hD : 1 + 2*((n:ℝ)-1)*a ≠ 0 := by
    have h2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [Work.Diff.Alg.Pinch.scalAlg_linv n hb hD hY]
  set D := 1 + 2*((n:ℝ)-1)*a with hDdef
  have hDnz : D ≠ 0 := by rw [hDdef]; exact hD
  field_simp [hDnz, hn0]
  rw [hDdef]
  ring

/-- The squared Frobenius norm of the Ricci tensor of `ell a (1/2) S`, for an algebraic curvature
tensor `S`, in terms of `scalAlg S` and `|Ric_0 S|^2`. -/
theorem ric_sq_sum_ell_half (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S) :
    (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric (Work.Diff.Alg.Pinch.ell a (1/2) S) i j
        * Work.Diff.Alg.Pinch.ric (Work.Diff.Alg.Pinch.ell a (1/2) S) i j)
      = (n:ℝ)^2/4 * Work.Diff.Alg.Pinch.ric0Frob2 S
        + (n:ℝ) * (Submission.Diff.Alg.scalAlg S/(n:ℝ))^2 * (1 + 2*((n:ℝ)-1)*a)^2 := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hb0 : (1 + ((n:ℝ)-2)*(1/2)) = (n:ℝ)/2 := by ring
  have hric : ∀ i j, Work.Diff.Alg.Pinch.ric (Work.Diff.Alg.Pinch.ell a (1/2) S) i j
      = (n:ℝ)/2 * Work.Diff.Alg.Pinch.ric0 S i j
        + (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))
            * Work.Diff.Alg.Pinch.id2 n i j := by
    intro i j
    rw [ric_ell_aux_rma n a (1/2) hn0 hS i j, hb0]
  rw [show (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric (Work.Diff.Alg.Pinch.ell a (1/2) S) i j
        * Work.Diff.Alg.Pinch.ric (Work.Diff.Alg.Pinch.ell a (1/2) S) i j)
      = ∑ i, ∑ j, ((n:ℝ)/2 * Work.Diff.Alg.Pinch.ric0 S i j
            + (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))
                * Work.Diff.Alg.Pinch.id2 n i j)
          * ((n:ℝ)/2 * Work.Diff.Alg.Pinch.ric0 S i j
            + (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))
                * Work.Diff.Alg.Pinch.id2 n i j) from by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hric i j]]
  rw [show (∑ i, ∑ j, ((n:ℝ)/2 * Work.Diff.Alg.Pinch.ric0 S i j
            + (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))
                * Work.Diff.Alg.Pinch.id2 n i j)
          * ((n:ℝ)/2 * Work.Diff.Alg.Pinch.ric0 S i j
            + (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))
                * Work.Diff.Alg.Pinch.id2 n i j))
      = ∑ i, ∑ j, (((n:ℝ)/2)^2 * (Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.ric0 S i j)
          + 2 * ((n:ℝ)/2) * (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))
              * (Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.id2 n i j)
          + (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))^2
              * (Work.Diff.Alg.Pinch.id2 n i j * Work.Diff.Alg.Pinch.id2 n i j)) from by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring]
  have hA : (∑ i, ∑ j, ((n:ℝ)/2)^2
        * (Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.ric0 S i j))
      = ((n:ℝ)/2)^2 * Work.Diff.Alg.Pinch.ric0Frob2 S := by
    rw [Work.Diff.Alg.Pinch.ric0Frob2, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
  have hB : (∑ i, ∑ j, 2 * ((n:ℝ)/2) * (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))
        * (Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.id2 n i j))
      = 2 * ((n:ℝ)/2) * (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))
        * (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.id2 n i j) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
  have hC : (∑ i, ∑ j, (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))^2
        * (Work.Diff.Alg.Pinch.id2 n i j * Work.Diff.Alg.Pinch.id2 n i j))
      = (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))^2
        * (∑ i, ∑ j, Work.Diff.Alg.Pinch.id2 n i j * Work.Diff.Alg.Pinch.id2 n i j) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
  have hrd : (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.id2 n i j) = 0 := by
    rw [show (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.id2 n i j)
        = ∑ i, ∑ j, Work.Diff.Alg.Pinch.id2 n i j * Work.Diff.Alg.Pinch.ric0 S i j from by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring]
    rw [sum_id2_mul_aux_rma]
    exact sum_ric0_self_aux n hn0 hS
  have hdd : (∑ i, ∑ j, Work.Diff.Alg.Pinch.id2 n i j * Work.Diff.Alg.Pinch.id2 n i j) = (n:ℝ) := by
    rw [sum_id2_mul_aux_rma]
    simp [Work.Diff.Alg.Pinch.id2]
  have hsplit : (∑ i, ∑ j, (((n:ℝ)/2)^2
          * (Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.ric0 S i j)
          + 2 * ((n:ℝ)/2) * (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))
              * (Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.id2 n i j)
          + (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))^2
              * (Work.Diff.Alg.Pinch.id2 n i j * Work.Diff.Alg.Pinch.id2 n i j)))
      = (∑ i, ∑ j, ((n:ℝ)/2)^2
            * (Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.ric0 S i j))
        + (∑ i, ∑ j, 2 * ((n:ℝ)/2)
              * (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))
              * (Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.id2 n i j))
        + (∑ i, ∑ j, (Submission.Diff.Alg.scalAlg S * (1+2*((n:ℝ)-1)*a) / (n:ℝ))^2
              * (Work.Diff.Alg.Pinch.id2 n i j * Work.Diff.Alg.Pinch.id2 n i j)) := by
    simp only [Finset.sum_add_distrib]
  rw [hsplit, hA, hB, hC, hrd, hdd]
  field_simp
  ring

/-! ## The target -/

/-- The scalar curvature of `linv a (1/2) (Q (ell a (1/2) S))`: the `b = 1/2` case of the
Böhm–Wilking scalar identity, in the form used by the pinching-set construction. -/
theorem scalAlg_linv_Q_ell_half (n : ℕ) (hn : 2 ≤ n) {a : ℝ} (ha : 1/2 < a)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S) :
    Submission.Diff.Alg.scalAlg
        (Work.Diff.Alg.Pinch.linv a (1/2)
          (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a (1/2) S)))
      = 2 * ((n:ℝ) * (Submission.Diff.Alg.scalAlg S / (n:ℝ))^2 * (1 + 2*((n:ℝ)-1)*a)^2
              + ((n:ℝ)^2/4) * Work.Diff.Alg.Pinch.ric0Frob2 S)
          / (1 + 2*((n:ℝ)-1)*a) := by
  have hSel : Submission.Diff.Alg.IsAlgCurv (Work.Diff.Alg.Pinch.ell a (1/2) S) :=
    Work.Diff.Alg.Pinch.ell_isAlgCurv n a (1/2) hS
  have hY : Submission.Diff.Alg.IsAlgCurv
      (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a (1/2) S)) :=
    Work.Diff.Alg.Pinch.Q_isAlgCurv n hSel
  rw [scalAlg_linv_half n hn ha hY, Work.Diff.Alg.Pinch.scalAlg_Q n hSel,
    ric_sq_sum_ell_half n hn a hS]
  ring





open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-- `InPIC2` and `S ≠ 0` force positive scalar curvature. -/
theorem scalAlg_pos_of_ne_zero {S : Curv4 n} (hS : IsAlgCurv S) (hP : InPIC2 S) (hne : S ≠ 0) :
    0 < scalAlg S := by
  have h1 : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hP
  have h2 : scalAlg S ≠ 0 := fun h0 => hne ((inPIC2_comp_bound n).2 S hP h0)
  exact lt_of_le_of_ne h1 (Ne.symm h2)

/-- A nonzero vector has positive Euclidean square-norm. -/
theorem sum_sq_pos {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < ∑ i, v i * v i := by
  obtain ⟨j0, hj0⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    exact hv (funext fun j => not_not.mp (not_exists.mp h j))
  have hle : v j0 * v j0 ≤ ∑ i, v i * v i :=
    Finset.single_le_sum (fun i _ => mul_self_nonneg (v i)) (Finset.mem_univ j0)
  have hpos : 0 < v j0 * v j0 := mul_self_pos.mpr hj0
  linarith

/-- The `Q S` half of the strict Ricci-form inequality: the quadratic form of `ric (Q S)` at a
tight direction is at least `2 (p · scal S / n)² ‖v‖²`. -/
theorem qfm_ric_QS_lower (n : ℕ) {p : ℝ} {S : Curv4 n} (hS : IsAlgCurv S)
    (hP : InPIC2 S) (hric : RicPinch p S) {v : Fin n → ℝ}
    (hev : ∀ i, (∑ j, ric S i j * v j) = (p * scalAlg S / (n : ℝ)) * v i) :
    2 * (p * scalAlg S / (n : ℝ)) ^ 2 * (∑ i, v i * v i) ≤ qfm (ric (Q S)) v := by
  rw [qfm_ric_Q n hS v]
  set c : ℝ := p * scalAlg S / (n : ℝ) with hc
  have hA : (ricM S - c • 1).PosSemidef := by rw [hc]; exact ricM_sub_posSemidef hS hric
  have hN : (NzK S v).PosSemidef := NzK_posSemidef hS hP v
  have hpair : 0 ≤ ∑ i, ∑ j, (ricM S - c • 1) i j * NzK S v i j := psd_pairing_rma hA hN
  have htr : (∑ j, NzK S v j j) = c * (∑ i, v i * v i) := by
    rw [tr_NzK_eq n hS v]
    have h1 : (∑ i, ∑ j, ric S i j * v i * v j) = ∑ i, v i * (∑ j, ric S i j * v j) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [h1]
    have h2 : (∑ i, v i * (∑ j, ric S i j * v j)) = ∑ i, v i * (c * v i) := by
      apply Finset.sum_congr rfl; intro i _; rw [hev i]
    rw [h2, show (∑ i, v i * (c * v i)) = ∑ i, c * (v i * v i) from
      Finset.sum_congr rfl (fun i _ => by ring), ← Finset.mul_sum]
  have hsplit : (∑ i, ∑ j, (ricM S - c • 1) i j * NzK S v i j)
      = (∑ i, ∑ j, ricM S i j * NzK S v i j) - c * (∑ j, NzK S v j j) := by
    have hpt : ∀ i j : Fin n, (ricM S - c • 1) i j * NzK S v i j
        = ricM S i j * NzK S v i j - c * (id2 n i j * NzK S v i j) := by
      intro i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, id2]
      ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
    simp only [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_eq_single i]
    · unfold id2; rw [if_pos rfl]; ring
    · intro j _ hj
      have hne : i ≠ j := fun h => hj h.symm
      unfold id2; rw [if_neg hne]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  have hmain : c * (∑ j, NzK S v j j) ≤ ∑ i, ∑ j, ric S i j * NzK S v i j := by
    have h2 : (∑ i, ∑ j, (ricM S - c • 1) i j * NzK S v i j)
        = (∑ i, ∑ j, ric S i j * NzK S v i j) - c * (∑ j, NzK S v j j) := by
      rw [hsplit]; simp only [ricM]
    linarith
  rw [htr] at hmain
  nlinarith [hmain]

theorem ChatT_strict_ric_a (n : ℕ) (hn : 2 ≤ n) {a : ℝ} (ha : 1 / 2 < a)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S) (hS0 : S ≠ 0)
    (hP : Submission.Diff.Alg.InPIC2 S)
    (hric : Work.Diff.Alg.Pinch.RicPinch (1 - 4 / ((n : ℝ) - 2 + 8 * a)) S) :
    ∀ v : Fin n → ℝ, v ≠ 0 →
      ((1 - 4 / ((n : ℝ) - 2 + 8 * a)) * Submission.Diff.Alg.scalAlg S / (n : ℝ))
          * (∑ i, v i * v i)
        = ∑ i, ∑ j, Work.Diff.Alg.Pinch.ric S i j * v i * v j →
      0 < (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric
              (Work.Diff.Alg.Pinch.linv a (1 / 2)
                (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a (1 / 2) S))) i j * v i * v j)
        - ((1 - 4 / ((n : ℝ) - 2 + 8 * a)) * Submission.Diff.Alg.scalAlg
              (Work.Diff.Alg.Pinch.linv a (1 / 2)
                (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a (1 / 2) S)))
              / (n : ℝ)) * (∑ i, v i * v i) := by
  intro v hv htight
  set p : ℝ := 1 - 4 / ((n : ℝ) - 2 + 8 * a) with hp
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hApos : 0 < 1 + 2 * ((n : ℝ) - 1) * a := by nlinarith
  have hAne : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0 := ne_of_gt hApos
  have hple : p < 1 := by
    rw [hp]
    have h4 : 0 < 4 / ((n : ℝ) - 2 + 8 * a) := by
      apply div_pos (by norm_num); nlinarith
    linarith
  have h1mp : 0 < 1 - p := by linarith
  have h2a1 : 0 < 2 * a - 1 := by linarith
  have hSsq : 0 < ∑ i, v i * v i := sum_sq_pos hv
  have hscalpos : 0 < scalAlg S := scalAlg_pos_of_ne_zero hS hP hS0
  have hev : ∀ i, (∑ j, ric S i j * v j) = (p * scalAlg S / (n : ℝ)) * v i :=
    ric_mulVec_of_tight hS hric htight
  have hX : linv a (1 / 2) (Q (ell a (1 / 2) S)) = Q S + bwCorr a (1 / 2) S := by
    have hb : 1 + ((n : ℝ) - 2) * (1 / 2) ≠ 0 := by
      intro h; nlinarith [hn2R]
    have h := linv_Q_ell n a (1 / 2) hAne hb hS
    rw [h, bwCorr]
    abel
  have hqfm : qfm (ric (linv a (1 / 2) (Q (ell a (1 / 2) S)))) v
      = qfm (ric (Q S)) v + qfm (ric (bwCorr a (1 / 2) S)) v := by
    rw [hX]
    rw [show ric (Q S + bwCorr a (1 / 2) S) = ric (Q S) + ric (bwCorr a (1 / 2) S) from
      funext fun i => funext fun j => ric_add_linv _ _ i j, qfm_add]
  have hQS := qfm_ric_QS_lower n hS hP hric hev
  have hB := qfm_bwCorr_half n a p hS hev
  have hScl := scalAlg_linv_Q_ell_half n hn ha hS
  -- package
  set lb : ℝ := scalAlg S / (n : ℝ) with hlb
  set f2 : ℝ := ric0Frob2 S with hf2
  set A2 : ℝ := 1 + 2 * ((n : ℝ) - 1) * a with hA2
  set Sv : ℝ := ∑ i, v i * v i with hSv
  have hlb_pos : 0 < lb := by rw [hlb]; exact div_pos hscalpos hnpos
  have hA2pos : 0 < A2 := by rw [hA2]; exact hApos
  have hf2nn : 0 ≤ f2 := by
    rw [hf2, ric0Frob2]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hSv_pos : 0 < Sv := by rw [hSv]; exact hSsq
  have hc : p * scalAlg S / (n : ℝ) = p * lb := by rw [hlb]; ring
  have hQS' : 2 * (p * lb) ^ 2 * Sv ≤ qfm (ric (Q S)) v := by
    have h := hQS
    rw [hc] at h
    exact h
  have hkey : (p * (2 * ((n:ℝ) * lb^2 * A2^2 + ((n:ℝ)^2/4) * f2) / A2) / (n:ℝ))
      = 2 * p * lb^2 * A2 + (p * (n:ℝ) / 2) * f2 / A2 := by
    field_simp
    ring
  have hgoal1 : (∑ i, ∑ j, ric (linv a (1 / 2) (Q (ell a (1 / 2) S))) i j * v i * v j)
      = qfm (ric (linv a (1 / 2) (Q (ell a (1 / 2) S)))) v := by simp only [qfm]
  rw [hgoal1, hqfm, hScl, hkey, hB]
  have hident : 2*(p*lb)^2 + (
      -2 * (((n : ℝ) - 2)/4 - 2*a + 1) * (1 - p)^2 * lb^2
      + 4*a*( (n:ℝ) * lb * (p * lb) - (p * lb)^2 )
      + (1/2)*( f2 + ((n:ℝ)-2)*(1-p)^2*lb^2 )
      + (-((a - 1/2)/(2*A2))) * (2*(n:ℝ)-2) * f2)
      - (2 * p * lb^2 * A2 + (p * (n:ℝ) / 2) * f2 / A2)
      = 2*(2*a-1)*(1-p)*lb^2 + (n:ℝ)*(1-p)/(2*A2)*f2 := by
    field_simp
    ring
  have hpp : 0 < 2*(2*a-1)*(1-p)*lb^2 + (n:ℝ)*(1-p)/(2*A2)*f2 := by
    have h1 : 0 < 2*(2*a-1)*(1-p)*lb^2 := by
      have ha1 : 0 < 2*(2*a-1) := by linarith
      exact mul_pos (mul_pos ha1 h1mp) (pow_pos hlb_pos 2)
    have h2 : 0 ≤ (n:ℝ)*(1-p)/(2*A2)*f2 := by
      have hnum : 0 ≤ (n:ℝ)*(1-p) := mul_nonneg (le_of_lt hnpos) (le_of_lt h1mp)
      have hden : 0 < 2*A2 := by linarith
      exact mul_nonneg (div_nonneg hnum (le_of_lt hden)) hf2nn
    linarith
  have hfin : 0 < 2 * (p * lb)^2 * Sv + Sv * (
      -2 * (((n : ℝ) - 2)/4 - 2*a + 1) * (1 - p)^2 * lb^2
      + 4*a*( (n:ℝ) * lb * (p * lb) - (p * lb)^2 )
      + (1/2)*( f2 + ((n:ℝ)-2)*(1-p)^2*lb^2 )
      + (-((a - 1/2)/(2*A2))) * (2*(n:ℝ)-2) * f2)
      - (2 * p * lb^2 * A2 + (p * (n:ℝ) / 2) * f2 / A2) * Sv := by
    rw [show 2 * (p * lb)^2 * Sv + Sv * (
        -2 * (((n : ℝ) - 2)/4 - 2*a + 1) * (1 - p)^2 * lb^2
        + 4*a*( (n:ℝ) * lb * (p * lb) - (p * lb)^2 )
        + (1/2)*( f2 + ((n:ℝ)-2)*(1-p)^2*lb^2 )
        + (-((a - 1/2)/(2*A2))) * (2*(n:ℝ)-2) * f2)
        - (2 * p * lb^2 * A2 + (p * (n:ℝ) / 2) * f2 / A2) * Sv
        = (2*(p*lb)^2 + (
        -2 * (((n : ℝ) - 2)/4 - 2*a + 1) * (1 - p)^2 * lb^2
        + 4*a*( (n:ℝ) * lb * (p * lb) - (p * lb)^2 )
        + (1/2)*( f2 + ((n:ℝ)-2)*(1-p)^2*lb^2 )
        + (-((a - 1/2)/(2*A2))) * (2*(n:ℝ)-2) * f2)
        - (2 * p * lb^2 * A2 + (p * (n:ℝ) / 2) * f2 / A2)) * Sv from by ring]
    rw [hident]
    exact mul_pos hpp hSv_pos
  linarith [hQS', hfin]




/-!
# The quantitative margin `Work.Diff.Alg.Pinch.ric_margin_a_rma`

This is the `b = 1/2`, `a > 1/2` branch of the Böhm–Wilking strictness estimate, in the
*quantitative* form needed by the shifted-pinching argument
(`Work.Diff.Alg.Pinch.ChatShiftStrictDefs`, `Work.Diff.Alg.Pinch.chat_shift_strict`).

Let `S ≠ 0` be an algebraic curvature tensor with `InPIC2 S` and
`Ric ≥ p·scal/n` where `p = 1 - 4/((n-2) + 8a)`, and let `v ≠ 0` be a *tight* direction, i.e.
`ric S v v = (p·scal S/n) |v|²`.  Put `X = linv a (1/2) (Q (ell a (1/2) S))`.  Then the Ricci form
of `X` improves on the pinching by an explicit positive amount:

`ric X v v - (p·scal X/n)|v|² ≥ 2 (1-p) (scal S/n)² ((2a-1) + n (1-p)²/(4(1+2(n-1)a)))|v|²`.

## Proof

* `linv_Q_ell` splits `X = Q S + bwCorr a (1/2) S`, and `ric` is additive, so
  `Ric_X(v,v) = qfm (ric (Q S)) v + qfm (ric (bwCorr a (1/2) S)) v`.
* `qfm_ric_QS_lower` (positive semidefiniteness of `Ric - pσ·id` and of the curvature matrix)
  gives `qfm (ric (Q S)) v ≥ 2 (p·σ)² |v|²` at the tight direction, and `qfm_bwCorr_half`
  evaluates the second term exactly.
* `scalAlg_linv_Q_ell_half` evaluates the scalar curvature of `X`.
* The resulting identity for the margin has coefficient
  `2 (2a-1)(1-p) σ² + n(1-p)/(2A)·|Ric₀ S|²`, where `σ = scal S/n` and `A = 1 + 2(n-1)a`.
  Replacing `|Ric₀ S|²` by its smallest possible value is the only remaining step: tightness makes
  `Ric₀ S · v = (p-1)σ v`, so row-wise Cauchy–Schwarz gives `|Ric₀ S|² ≥ (1-p)² σ²`
  (`ric0Frob2_ge_tight`).  Since the target coefficient is
  `2 (2a-1)(1-p) σ² + n(1-p)³ σ²/(2A)`, this is exactly what is required.
-/


open Finset Submission.Diff.Alg

set_option maxHeartbeats 2000000

variable {n : ℕ}

/-- `∑ⱼ δᵢⱼ vⱼ = vᵢ`. -/
private lemma id2_mulVec' (v : Fin n → ℝ) (i : Fin n) :
    (∑ j, id2 n i j * v j) = v i := by
  rw [Finset.sum_eq_single i]
  · simp [id2]
  · intro j _ hj
    have hij : ¬ (i = j) := fun h => hj h.symm
    simp only [id2, hij, ite_false, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **The traceless Ricci tensor of a tight direction is not small.**  If `Ric ≥ p·scal/n` and the
direction `v ≠ 0` saturates this bound, then `|Ric₀ S|² ≥ (1-p)² (scal S/n)²`.

Tightness makes `v` an eigenvector of `Ric₀` with eigenvalue `(p-1)·scal S/n`
(`ric_mulVec_of_tight`), and the row-wise Cauchy–Schwarz inequality
`(∑ⱼ Aᵢⱼvⱼ)² ≤ (∑ⱼ Aᵢⱼ²)(∑ⱼ vⱼ²)` then bounds `|Ric₀ S|²` below. -/
theorem ric0Frob2_ge_tight {p : ℝ} {S : Curv4 n} (hS : IsAlgCurv S) (hric : RicPinch p S)
    {v : Fin n → ℝ} (hv : v ≠ 0)
    (htight : (p * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
        = ∑ i, ∑ j, ric S i j * v i * v j) :
    (1 - p) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2 ≤ ric0Frob2 S := by
  have hq : 0 < ∑ i, v i * v i := sum_sq_pos hv
  have hev : ∀ i, (∑ j, ric S i j * v j) = (p * scalAlg S / (n : ℝ)) * v i :=
    ric_mulVec_of_tight hS hric htight
  -- `Ric₀ S · v = (p - 1)·(scal S/n)·v`
  have hric0 : ∀ i, (∑ j, ric0 S i j * v j) = ((p - 1) * (scalAlg S / (n : ℝ))) * v i := by
    intro i
    have h1 : (∑ j, ric0 S i j * v j)
        = (∑ j, ric S i j * v j) - (scalAlg S / (n : ℝ)) * (∑ j, id2 n i j * v j) := by
      rw [show (∑ j, ric0 S i j * v j)
          = ∑ j, (ric S i j * v j - (scalAlg S / (n : ℝ)) * (id2 n i j * v j)) from by
        apply Finset.sum_congr rfl; intro j _
        simp only [ric0]; ring]
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [Finset.mul_sum]
    rw [h1, id2_mulVec' v i, hev i]
    ring
  -- row-wise Cauchy–Schwarz
  have hcs : ∀ i, (∑ j, ric0 S i j * v j) ^ 2
      ≤ (∑ j, ric0 S i j ^ 2) * (∑ j, v j * v j) := by
    intro i
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ric0 S i j) v
    simpa only [pow_two] using h
  have hsum : (((p - 1) * (scalAlg S / (n : ℝ))) ^ 2) * (∑ i, v i * v i)
      ≤ (∑ i, ∑ j, ric0 S i j ^ 2) * (∑ i, v i * v i) := by
    calc (((p - 1) * (scalAlg S / (n : ℝ))) ^ 2) * (∑ i, v i * v i)
        = ∑ i, (∑ j, ric0 S i j * v j) ^ 2 := by
          rw [show (∑ i, (∑ j, ric0 S i j * v j) ^ 2)
              = ∑ i, (((p - 1) * (scalAlg S / (n : ℝ))) * v i) ^ 2 from by
            apply Finset.sum_congr rfl; intro i _; rw [hric0 i]]
          rw [show (∑ i, (((p - 1) * (scalAlg S / (n : ℝ))) * v i) ^ 2)
              = (((p - 1) * (scalAlg S / (n : ℝ))) ^ 2) * (∑ i, v i * v i) from by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro i _; ring]
      _ ≤ ∑ i, (∑ j, ric0 S i j ^ 2) * (∑ j, v j * v j) :=
          Finset.sum_le_sum (fun i _ => hcs i)
      _ = (∑ i, ∑ j, ric0 S i j ^ 2) * (∑ i, v i * v i) := by rw [Finset.sum_mul]
  have hfrob : ric0Frob2 S = ∑ i, ∑ j, ric0 S i j ^ 2 := by
    rw [ric0Frob2]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have hpp : ((p - 1) * (scalAlg S / (n : ℝ))) ^ 2
      = (1 - p) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2 := by ring
  rw [hpp] at hsum
  rw [hfrob]
  exact le_of_mul_le_mul_right hsum hq

theorem ric_margin_a_rma (n : ℕ) (hn2 : 2 ≤ n) {a : ℝ} (ha : 1 / 2 < a)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S) (hS0 : S ≠ 0)
    (hP : Submission.Diff.Alg.InPIC2 S)
    (hric : Work.Diff.Alg.Pinch.RicPinch (1 - 4 / ((n : ℝ) - 2 + 8 * a)) S)
    {v : Fin n → ℝ} (hv : v ≠ 0)
    (htight : ((1 - 4 / ((n : ℝ) - 2 + 8 * a)) * Submission.Diff.Alg.scalAlg S / ↑n)
        * (∑ i, v i * v i) = ∑ i, ∑ j, Work.Diff.Alg.Pinch.ric S i j * v i * v j) :
    2 * (4 / ((n : ℝ) - 2 + 8 * a)) * (Submission.Diff.Alg.scalAlg S / ↑n) ^ 2
        * ((2 * a - 1)
            + (n : ℝ) * (4 / ((n : ℝ) - 2 + 8 * a)) ^ 2
                / (4 * (1 + 2 * ((n : ℝ) - 1) * a)))
        * (∑ i, v i * v i)
      ≤ (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric
              (Work.Diff.Alg.Pinch.linv a (1 / 2)
                (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a (1 / 2) S))) i j * v i * v j)
        - ((1 - 4 / ((n : ℝ) - 2 + 8 * a)) * Submission.Diff.Alg.scalAlg
              (Work.Diff.Alg.Pinch.linv a (1 / 2)
                (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a (1 / 2) S))) / ↑n)
          * (∑ i, v i * v i) := by
  set p : ℝ := 1 - 4 / ((n : ℝ) - 2 + 8 * a) with hp
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hDpos : (0 : ℝ) < (n : ℝ) - 2 + 8 * a := by nlinarith
  have hApos : 0 < 1 + 2 * ((n : ℝ) - 1) * a := by nlinarith
  have hAne : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0 := ne_of_gt hApos
  have h1mp : 0 < 1 - p := by
    rw [hp]
    have h4 : 0 < 4 / ((n : ℝ) - 2 + 8 * a) := div_pos (by norm_num) hDpos
    linarith
  have hscalpos : 0 < scalAlg S := scalAlg_pos_of_ne_zero hS hP hS0
  have hric' : RicPinch p S := hric
  have htight' : (p * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
      = ∑ i, ∑ j, ric S i j * v i * v j := htight
  have hSsq : 0 < ∑ i, v i * v i := sum_sq_pos hv
  have hev : ∀ i, (∑ j, ric S i j * v j) = (p * scalAlg S / (n : ℝ)) * v i :=
    ric_mulVec_of_tight hS hric' htight'
  -- the Böhm–Wilking splitting of the one-step image
  have hX : linv a (1 / 2) (Q (ell a (1 / 2) S)) = Q S + bwCorr a (1 / 2) S := by
    have hb : 1 + ((n : ℝ) - 2) * (1 / 2) ≠ 0 := by nlinarith
    have h := linv_Q_ell n a (1 / 2) hAne hb hS
    rw [h, bwCorr]
    abel
  have hqfm : qfm (ric (linv a (1 / 2) (Q (ell a (1 / 2) S)))) v
      = qfm (ric (Q S)) v + qfm (ric (bwCorr a (1 / 2) S)) v := by
    rw [hX]
    rw [show ric (Q S + bwCorr a (1 / 2) S) = ric (Q S) + ric (bwCorr a (1 / 2) S) from
      funext fun i => funext fun j => ric_add_linv _ _ i j, qfm_add]
  have hQS := qfm_ric_QS_lower n hS hP hric' hev
  have hB := qfm_bwCorr_half n a p hS hev
  have hScl := scalAlg_linv_Q_ell_half n hn2 ha hS
  -- abbreviations
  set lb : ℝ := scalAlg S / (n : ℝ) with hlb
  set f2 : ℝ := ric0Frob2 S with hf2
  set A2 : ℝ := 1 + 2 * ((n : ℝ) - 1) * a with hA2
  set Sv : ℝ := ∑ i, v i * v i with hSv
  set BIG : ℝ :=
      -2 * (((n : ℝ) - 2)/4 - 2*a + 1) * (1 - p)^2 * lb^2
      + 4*a*( (n:ℝ) * lb * (p * lb) - (p * lb)^2 )
      + (1/2)*( f2 + ((n:ℝ)-2)*(1-p)^2*lb^2 )
      + (-((a - 1/2)/(2*A2))) * (2*(n:ℝ)-2) * f2 with hBIG
  have hlb_pos : 0 < lb := by rw [hlb]; exact div_pos hscalpos hnpos
  have hA2pos : 0 < A2 := by rw [hA2]; exact hApos
  have hSv_pos : 0 < Sv := by rw [hSv]; exact hSsq
  have hc : p * scalAlg S / (n : ℝ) = p * lb := by rw [hlb]; ring
  have hQS' : 2 * (p * lb) ^ 2 * Sv ≤ qfm (ric (Q S)) v := by
    have h := hQS
    rw [hc] at h
    exact h
  have hkey : (p * (2 * ((n:ℝ) * lb^2 * A2^2 + ((n:ℝ)^2/4) * f2) / A2) / (n:ℝ))
      = 2 * p * lb^2 * A2 + (p * (n:ℝ) / 2) * f2 / A2 := by
    field_simp
    ring
  have hscalX : p * scalAlg (linv a (1 / 2) (Q (ell a (1 / 2) S))) / (n:ℝ)
      = 2 * p * lb^2 * A2 + (p * (n:ℝ) / 2) * f2 / A2 := by
    rw [hScl]; exact hkey
  have hBSv : qfm (ric (bwCorr a (1 / 2) S)) v = Sv * BIG := by
    rw [hB, hBIG]
  have hident : 2 * (p * lb) ^ 2 + BIG
        - (2 * p * lb^2 * A2 + (p * (n:ℝ) / 2) * f2 / A2)
      = 2 * (2*a - 1) * (1 - p) * lb^2 + (n:ℝ) * (1 - p) / (2 * A2) * f2 := by
    rw [hBIG]
    field_simp
    ring
  -- ### the margin of the one-step map
  have hmargin : (2 * (2*a - 1) * (1 - p) * lb^2 + (n:ℝ) * (1 - p) / (2 * A2) * f2) * Sv
      ≤ qfm (ric (linv a (1 / 2) (Q (ell a (1 / 2) S)))) v
        - (p * scalAlg (linv a (1 / 2) (Q (ell a (1 / 2) S))) / (n:ℝ)) * Sv := by
    calc (2 * (2*a - 1) * (1 - p) * lb^2 + (n:ℝ) * (1 - p) / (2 * A2) * f2) * Sv
        = (2 * (p * lb) ^ 2 + BIG
            - (2 * p * lb^2 * A2 + (p * (n:ℝ) / 2) * f2 / A2)) * Sv := by
          rw [hident]
      _ ≤ qfm (ric (Q S)) v + Sv * BIG
            - (2 * p * lb^2 * A2 + (p * (n:ℝ) / 2) * f2 / A2) * Sv := by
          have h := hQS'
          have h2 : (2 * (p * lb) ^ 2 + BIG
              - (2 * p * lb^2 * A2 + (p * (n:ℝ) / 2) * f2 / A2)) * Sv
              = 2 * (p * lb) ^ 2 * Sv + (Sv * BIG
                  - (2 * p * lb^2 * A2 + (p * (n:ℝ) / 2) * f2 / A2) * Sv) := by ring
          rw [h2]
          linarith [h]
      _ = qfm (ric (linv a (1 / 2) (Q (ell a (1 / 2) S)))) v
            - (p * scalAlg (linv a (1 / 2) (Q (ell a (1 / 2) S))) / (n:ℝ)) * Sv := by
          rw [hqfm, hBSv, hscalX]
  -- ### the Cauchy–Schwarz improvement of the traceless-Ricci term
  have hcs : (1 - p) ^ 2 * lb^2 ≤ f2 := by
    have h := ric0Frob2_ge_tight hS hric' hv htight'
    simpa only [hlb, hf2] using h
  have hfac : (0:ℝ) ≤ (n:ℝ) * (1 - p) / (2 * A2) := by
    apply div_nonneg
    · exact mul_nonneg (le_of_lt hnpos) (le_of_lt h1mp)
    · linarith
  have hmul := mul_le_mul_of_nonneg_left hcs hfac
  have hcoef : 2 * (1 - p) * lb^2 * ((n:ℝ) * (1 - p)^2 / (4 * A2))
      ≤ (n:ℝ) * (1 - p) / (2 * A2) * f2 := by
    have heq : 2 * (1 - p) * lb^2 * ((n:ℝ) * (1 - p)^2 / (4 * A2))
        = (n:ℝ) * (1 - p) / (2 * A2) * ((1 - p)^2 * lb^2) := by
      field_simp
      ring
    rw [heq]
    exact hmul
  have hcoef2 : 2 * (1 - p) * lb^2 * ((2*a - 1) + (n:ℝ) * (1 - p)^2 / (4 * A2))
      ≤ 2 * (2*a - 1) * (1 - p) * lb^2 + (n:ℝ) * (1 - p) / (2 * A2) * f2 := by
    have h1 : 2 * (1 - p) * lb^2 * ((2*a - 1) + (n:ℝ) * (1 - p)^2 / (4 * A2))
        = 2 * (2*a - 1) * (1 - p) * lb^2
          + 2 * (1 - p) * lb^2 * ((n:ℝ) * (1 - p)^2 / (4 * A2)) := by
      ring
    rw [h1]
    linarith [hcoef]
  have h4D : 4 / ((n : ℝ) - 2 + 8 * a) = 1 - p := by rw [hp]; ring
  have hfinal : 2 * (4 / ((n : ℝ) - 2 + 8 * a)) * lb^2
        * ((2*a - 1) + (n:ℝ) * (4 / ((n : ℝ) - 2 + 8 * a))^2 / (4 * A2)) * Sv
      ≤ qfm (ric (linv a (1 / 2) (Q (ell a (1 / 2) S)))) v
        - (p * scalAlg (linv a (1 / 2) (Q (ell a (1 / 2) S))) / (n:ℝ)) * Sv := by
    rw [h4D]
    exact le_trans (mul_le_mul_of_nonneg_right hcoef2 (le_of_lt hSv_pos)) hmargin
  exact hfinal



end Work.Diff.Alg.Pinch
