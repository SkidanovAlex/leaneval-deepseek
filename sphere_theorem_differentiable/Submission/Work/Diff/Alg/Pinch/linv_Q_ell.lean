import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.BQDefs
import Submission.Work.Diff.Alg.Pinch.ric_Q
import Submission.Work.Diff.Alg.Pinch.BQ_iso
import Submission.Work.Diff.Alg.Pinch.scalAlg_Q
import Submission.Work.Diff.Alg.Pinch.BQ_knProd_W
import Submission.Work.Diff.Alg.Pinch.linv_Q_ell_knProd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Böhm–Wilking identity `linv a b (Q (ell a b R)) = Q R + D_{a,b}(R)`

Böhm–Wilking, *Manifolds with positive curvature operators are space forms*, Theorem 2.
-/

set_option maxHeartbeats 4000000

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## The `(0,2)`-companions of the polarization -/

lemma ric_BQ (n : ℕ) {R S : Curv4 n} (hR : IsAlgCurv R) (hS : IsAlgCurv S) (i j : Fin n) :
    ric (BQ R S) i j
      = ∑ p, ∑ q, (ric R p q * S i p j q + ric S p q * R i p j q) := by
  have hRS : IsAlgCurv (R + S) := isAlgCurv_add hR hS
  have hlin : ric (Q (R + S)) i j = ric (Q R) i j + ric (Q S) i j + 2 * ric (BQ R S) i j := by
    rw [Q_add_polarize]
    simp only [ric_add_linv, Pi.add_apply]
    ring
  rw [ric_Q n hRS i j, ric_Q n hR i j, ric_Q n hS i j] at hlin
  have hsum : (∑ p, ∑ q, ric (R + S) p q * (R + S) i p j q)
      = (∑ p, ∑ q, ric R p q * R i p j q)
        + (∑ p, ∑ q, (ric R p q * S i p j q + ric S p q * R i p j q))
        + (∑ p, ∑ q, ric S p q * S i p j q) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro p _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro q _
    simp only [ric_add_linv, Pi.add_apply]
    ring
  rw [hsum] at hlin
  linarith

lemma scalAlg_BQ (n : ℕ) {R S : Curv4 n} (hR : IsAlgCurv R) (hS : IsAlgCurv S) :
    scalAlg (BQ R S) = 2 * ∑ p, ∑ q, ric R p q * ric S p q := by
  have hRS : IsAlgCurv (R + S) := isAlgCurv_add hR hS
  have hlin : scalAlg (Q (R + S)) = scalAlg (Q R) + scalAlg (Q S) + 2 * scalAlg (BQ R S) := by
    rw [Q_add_polarize]
    simp only [scalAlg_add_linv]
    ring
  rw [scalAlg_Q n hRS, scalAlg_Q n hR, scalAlg_Q n hS] at hlin
  have hsum : (∑ p, ∑ q, ric (R + S) p q * ric (R + S) p q)
      = (∑ p, ∑ q, ric R p q * ric R p q)
        + 2 * (∑ p, ∑ q, ric R p q * ric S p q)
        + (∑ p, ∑ q, ric S p q * ric S p q) := by
    rw [show (2:ℝ) * (∑ p, ∑ q, ric R p q * ric S p q)
        = ∑ p, ∑ q, 2 * (ric R p q * ric S p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; rw [Finset.mul_sum]]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro p _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro q _
    simp only [ric_add_linv]
    ring
  rw [hsum] at hlin
  linarith

/-! ## Weyl facts -/

lemma anti34 {W : Curv4 n} (hW : IsAlgCurv W) (i j k l : Fin n) : W i j l k = - W i j k l := by
  rw [← hW.2.1 i j l k, hW.1 k l i j, hW.2.1 i j k l]

lemma knProd_zero_left (B : Fin n → Fin n → ℝ) : knProd (0 : Fin n → Fin n → ℝ) B = 0 := by
  funext i j k l; simp [knProd]

lemma knProd_zero_right (A : Fin n → Fin n → ℝ) : knProd A (0 : Fin n → Fin n → ℝ) = 0 := by
  funext i j k l; simp [knProd]

/-- `scalAlg` is the trace of `ric`. -/
lemma scalAlg_eq_sum_ric {W : Curv4 n} (hW : IsAlgCurv W) : scalAlg W = ∑ i, ric W i i := by
  obtain ⟨hanti, hpair, hbian⟩ := hW
  simp only [scalAlg, ric]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  have h1 : W j i j i = - W i j j i := hanti i j j i
  have h2 : W i j j i = - W i j i j := anti34 ⟨hanti, hpair, hbian⟩ i j i j
  rw [h1, h2]; ring

lemma scalAlg_eq_zero_of_ric_zero {W : Curv4 n} (hW : IsAlgCurv W) (hric : ∀ i j, ric W i j = 0) :
    scalAlg W = 0 := by
  rw [scalAlg_eq_sum_ric hW]
  simp [hric]

/-- If the Ricci tensor and the scalar curvature of `Y` vanish then `ric0 Y = 0`. -/
lemma ric0_eq_zero_of {Y : Curv4 n} (hric : ∀ i j, ric Y i j = 0) (hs : scalAlg Y = 0) :
    ric0 Y = 0 := by
  funext i j
  rw [ric0, hric i j, hs]
  simp

/-- If the traceless Ricci tensor and the scalar curvature of `Y` vanish then `linv a b Y = Y`. -/
lemma linv_of (a b : ℝ) {Y : Curv4 n} (hr : ric0 Y = 0) (hs : scalAlg Y = 0) :
    linv a b Y = Y := by
  rw [linv, hr, knProd_zero_left]
  simp [hs]

lemma ell_of_ric_zero {W : Curv4 n} (hW : IsAlgCurv W) (hric : ∀ i j, ric W i j = 0) (a b : ℝ) :
    ell a b W = W := by
  have hr : ric0 W = 0 := ric0_eq_zero_of hric (scalAlg_eq_zero_of_ric_zero hW hric)
  have hs : scalAlg W = 0 := scalAlg_eq_zero_of_ric_zero hW hric
  rw [ell, hr, knProd_zero_left]
  simp [hs]

lemma ric_Q_eq_zero_of_ric_zero {W : Curv4 n} (hW : IsAlgCurv W) (hric : ∀ i j, ric W i j = 0) :
    ∀ i j, ric (Q W) i j = 0 := by
  intro i j
  rw [ric_Q n hW i j]
  simp [hric]

lemma scalAlg_Q_eq_zero_of_ric_zero {W : Curv4 n} (hW : IsAlgCurv W) (hric : ∀ i j, ric W i j = 0) :
    scalAlg (Q W) = 0 := by
  rw [scalAlg_Q n hW]
  simp [hric]

/-- **Renamed** from `linv_Q_of_ric_zero` (2026, to fix a workspace-wide name clash: the same name
`Work.Diff.Alg.Pinch.linv_Q_of_ric_zero` is declared with a *different* signature in
`Submission/Work/Diff/Alg/Pinch/BW_identity.lean`, so no module could import both this file and
`BW_identity`).  Only this file uses the name. -/
lemma lqk_linv_Q_of_ric_zero {W : Curv4 n} (hW : IsAlgCurv W) (hric : ∀ i j, ric W i j = 0)
    (a b : ℝ) : linv a b (Q W) = Q W :=
  linv_of a b (ric0_eq_zero_of (ric_Q_eq_zero_of_ric_zero hW hric)
    (scalAlg_Q_eq_zero_of_ric_zero hW hric)) (scalAlg_Q_eq_zero_of_ric_zero hW hric)

/-- `knProd (id2 n) (id2 n) = 2 • Iso n`. -/
lemma knProd_id2_id2 : knProd (id2 n) (id2 n) = (2 : ℝ) • Iso n := by
  funext i j k l
  simp only [knProd, id2, Iso, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The polarization against the identity vanishes for a Weyl tensor. -/
lemma BQ_id_id_of_ric_zero {W : Curv4 n} (hW : IsAlgCurv W) (hric : ∀ i j, ric W i j = 0) :
    BQ (knProd (id2 n) (id2 n)) W = 0 := by
  rw [knProd_id2_id2]
  rw [show BQ ((2:ℝ) • Iso n) W = (2:ℝ) • BQ (Iso n) W from BQ_smul_left 2 (Iso n) W]
  rw [show BQ (Iso n) W = knProd (ric W) (id2 n) from by
    rw [BQ_symm]; exact BQ_iso n hW]
  have h0 : ric W = 0 := funext (fun i => funext (fun j => hric i j))
  rw [h0, knProd_zero_left]
  simp

/-! ## Linearity of `ell` and the Ricci tensor of `ell a b R` -/

lemma ell_add (a b : ℝ) (R S : Curv4 n) : ell a b (R + S) = ell a b R + ell a b S := by
  rw [ell, ell, ell, ric0_add', scalAlg_add_linv, knProd_add_left_linv]
  rw [mul_add, add_smul, smul_add]
  abel

lemma ric_ell (n : ℕ) (a b : ℝ) (hn : (n : ℝ) ≠ 0) {R : Curv4 n} (hR : IsAlgCurv R)
    (i j : Fin n) :
    ric (ell a b R) i j = (1 + ((n : ℝ) - 2) * b) * ric0 R i j
      + (scalAlg R * (1 + 2 * ((n : ℝ) - 1) * a) / (n : ℝ)) * id2 n i j := by
  have h1 := ric0_ell_linv n a b hn hR i j
  have h2 := scalAlg_ell_of_ne n a b hn hR
  have h3 : ric (ell a b R) i j
      = ric0 (ell a b R) i j + (scalAlg (ell a b R) / (n : ℝ)) * id2 n i j := by
    rw [ric0]; ring
  rw [h3, h1, h2]; ring

/-! ## The polarization of `Q` against a Weyl tensor -/

lemma scalAlg_BQ_of_ric_zero {S W : Curv4 n} (hS : IsAlgCurv S) (hW : IsAlgCurv W)
    (hric : ∀ i j, ric W i j = 0) : scalAlg (BQ S W) = 0 := by
  rw [scalAlg_BQ n hS hW]
  simp [hric]

lemma ric0_BQ_of_ric_zero {S W : Curv4 n} (hS : IsAlgCurv S) (hW : IsAlgCurv W)
    (hric : ∀ i j, ric W i j = 0) :
    ric0 (BQ S W) = fun i j => ∑ p, ∑ q, ric S p q * W i p j q := by
  have h2 : scalAlg (BQ S W) = 0 := scalAlg_BQ_of_ric_zero hS hW hric
  funext i j
  have h1 : ric (BQ S W) i j
      = ∑ p, ∑ q, (ric S p q * W i p j q + ric W p q * S i p j q) := ric_BQ n hS hW i j
  have hsplit : (∑ p, ∑ q, (ric S p q * W i p j q + ric W p q * S i p j q))
      = (∑ p, ∑ q, ric S p q * W i p j q) + (∑ p, ∑ q, ric W p q * S i p j q) := by
    simp only [Finset.sum_add_distrib]
  have hz : (∑ p, ∑ q, ric W p q * S i p j q) = 0 := by simp [hric]
  rw [ric0, h1, hsplit, hz, h2]
  ring

/-! ## Contractions against the identity -/

lemma sum_id2_mul_aux (f : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, id2 n p q * f p q) = ∑ p, f p p := by
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_eq_single p]
  · simp [id2]
  · intro q _ hq
    rw [id2, if_neg (fun h => hq h.symm), zero_mul]
  · intro hp; exact absurd (Finset.mem_univ p) hp

lemma sum_mul_id2_aux (f : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, f p q * id2 n q p) = ∑ p, f p p := by
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_eq_single p]
  · simp [id2]
  · intro q _ hq
    rw [id2, if_neg (fun h => hq h), mul_zero]
  · intro hp; exact absurd (Finset.mem_univ p) hp

lemma sum_ric0_self (n : ℕ) (hn : (n : ℝ) ≠ 0) {R : Curv4 n} (hR : IsAlgCurv R) :
    (∑ k, ric0 R k k) = 0 := by
  have h1 : (∑ k : Fin n, ric0 R k k)
      = (∑ k : Fin n, (ric R k k - (scalAlg R / (n : ℝ)) * id2 n k k)) := by
    apply Finset.sum_congr rfl; intro k _; rw [ric0]
  rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [scalAlg_eq_sum_ric hR]
  have h2 : (∑ k : Fin n, id2 n k k) = (n : ℝ) := by simp [id2]
  rw [h2, div_mul_cancel₀ _ hn]
  ring

/-- `ric0 (BQ R W)` for a Weyl tensor `W`: the `ric0 R`-contraction. -/
lemma ric0_BQ_eq {R W : Curv4 n} (hR : IsAlgCurv R) (hW : IsAlgCurv W)
    (hric : ∀ i j, ric W i j = 0) :
    ric0 (BQ R W) = fun i j => ∑ p, ∑ q, ric0 R p q * W i p j q := by
  funext i j
  have hRW : ric0 (BQ R W) i j = ∑ p, ∑ q, ric R p q * W i p j q := by
    rw [ric0_BQ_of_ric_zero hR hW hric]
  rw [hRW]
  have hexp : (∑ p, ∑ q, ric R p q * W i p j q)
      = (∑ p, ∑ q, ric0 R p q * W i p j q)
        + ∑ p, ∑ q, (scalAlg R / (n : ℝ)) * id2 n p q * W i p j q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro p _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro q _
    rw [ric0]; ring
  rw [hexp]
  have hdelta : (∑ p, ∑ q, (scalAlg R / (n : ℝ)) * id2 n p q * W i p j q)
      = (scalAlg R / (n : ℝ)) * ric W i j := by
    rw [show (∑ p, ∑ q, (scalAlg R / (n : ℝ)) * id2 n p q * W i p j q)
        = (scalAlg R / (n : ℝ)) * (∑ p, ∑ q, id2 n p q * W i p j q) from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _
      ring]
    rw [sum_id2_mul_aux, sum_self_eq_ric hW i j]
  rw [hdelta, hric i j, mul_zero, add_zero]

/-- `ric0 (knProd (ric0 R) (id2 n)) = (n-2) • ric0 R`. -/
lemma ric0_knProd_ric0_id2 (n : ℕ) (hn : (n : ℝ) ≠ 0) {R : Curv4 n} (hR : IsAlgCurv R)
    (p q : Fin n) :
    ric0 (knProd (ric0 R) (id2 n)) p q = ((n : ℝ) - 2) * ric0 R p q := by
  have htr : (∑ k, ric0 R k k) = 0 := sum_ric0_self n hn hR
  have hric : ric (knProd (ric0 R) (id2 n)) p q = ((n : ℝ) - 2) * ric0 R p q := by
    rw [ric_knProd_id2, htr]; ring
  have hscal : scalAlg (knProd (ric0 R) (id2 n)) = 0 := by
    have hz : (∑ i, ∑ j, ric0 R i j * id2 n j i) = 0 := by
      rw [sum_mul_id2_aux]; exact htr
    rw [scalAlg_knProd, show (∑ i, ric0 R i i) = 0 from htr, hz]
    ring
  rw [ric0, hric, hscal]
  simp

/-- `ric0 (BQ X W)` where `X = knProd (ric0 R) (id2 n)`. -/
lemma ric0_BQ_knProd_eq (n : ℕ) (hn : (n : ℝ) ≠ 0) {R W : Curv4 n} (hR : IsAlgCurv R)
    (hW : IsAlgCurv W) (hric : ∀ i j, ric W i j = 0) :
    ric0 (BQ (knProd (ric0 R) (id2 n)) W)
      = fun i j => ((n : ℝ) - 2) * ∑ p, ∑ q, ric0 R p q * W i p j q := by
  have hX : IsAlgCurv (knProd (ric0 R) (id2 n)) :=
    knProd_isAlgCurv (ric0_symm hR) (fun i j => id2_symm i j)
  have h := ric0_BQ_eq hX hW hric
  funext i j
  rw [show ric0 (BQ (knProd (ric0 R) (id2 n)) W) i j
      = ∑ p, ∑ q, ric0 (knProd (ric0 R) (id2 n)) p q * W i p j q from by
    rw [h]]
  rw [show (∑ p, ∑ q, ric0 (knProd (ric0 R) (id2 n)) p q * W i p j q)
      = ∑ p, ∑ q, ((n : ℝ) - 2) * (ric0 R p q * W i p j q) from by
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [ric0_knProd_ric0_id2 n hn hR]; ring]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.mul_sum]

/-- Combining `f + c • f`. -/
lemma one_add_smul (c : ℝ) (f : Fin n → Fin n → ℝ) : (1 + c) • f = f + c • f := by
  rw [add_smul, one_smul]

/-! ## The crux: `linv a b (BQ (ell a b R) W) = BQ R W` for a Weyl tensor `W` -/

theorem linv_BQ_ell_weyl_of_key (n : ℕ) (hn : (n : ℝ) ≠ 0) {a b : ℝ} {R : Curv4 n}
    (hR : IsAlgCurv R) {W : Curv4 n} (hW : IsAlgCurv W) (hric : ∀ i j, ric W i j = 0)
    (hb : 1 + ((n : ℝ) - 2) * b ≠ 0)
    (hkey : BQ (knProd (ric0 R) (id2 n)) W
      = knProd (fun i j => ∑ p, ∑ q, ric0 R p q * W i p j q) (id2 n)) :
    linv a b (BQ (ell a b R) W) = BQ R W := by
  have hX : IsAlgCurv (knProd (ric0 R) (id2 n)) :=
    knProd_isAlgCurv (ric0_symm hR) (fun i j => id2_symm i j)
  have hell : BQ (ell a b R) W = BQ R W + b • BQ (knProd (ric0 R) (id2 n)) W := by
    rw [ell, BQ_add_left, BQ_add_left, BQ_smul_left, BQ_smul_left, BQ_id_id_of_ric_zero hW hric]
    simp
  have hscal : scalAlg (BQ R W + b • BQ (knProd (ric0 R) (id2 n)) W) = 0 := by
    rw [scalAlg_add_linv, scalAlg_smul_linv, scalAlg_BQ_of_ric_zero hR hW hric,
      scalAlg_BQ_of_ric_zero hX hW hric]
    ring
  have hric0 : knProd (ric0 (BQ R W + b • BQ (knProd (ric0 R) (id2 n)) W)) (id2 n)
      = (1 + b * ((n : ℝ) - 2)) •
          knProd (fun i j => ∑ p, ∑ q, ric0 R p q * W i p j q) (id2 n) := by
    rw [ric0_add', ric0_smul', ric0_BQ_eq hR hW hric, ric0_BQ_knProd_eq n hn hR hW hric]
    change knProd ((fun i j => ∑ p, ∑ q, ric0 R p q * W i p j q)
        + b • (((n : ℝ) - 2) • (fun i j => ∑ p, ∑ q, ric0 R p q * W i p j q))) (id2 n)
      = (1 + b * ((n : ℝ) - 2)) •
          knProd (fun i j => ∑ p, ∑ q, ric0 R p q * W i p j q) (id2 n)
    rw [smul_smul]
    rw [← one_add_smul]
    rw [knProd_smul_left_linv]
  rw [hell, linv, hscal, hric0, hkey]
  have hcoef : (b / (1 + ((n : ℝ) - 2) * b)) * (1 + b * ((n : ℝ) - 2)) = b := by
    have hD : (1 : ℝ) + b * ((n : ℝ) - 2) = 1 + ((n : ℝ) - 2) * b := by ring
    rw [hD]
    exact div_mul_cancel₀ b hb
  have hss2 : (b / (1 + ((n : ℝ) - 2) * b)) •
      ((1 + b * ((n : ℝ) - 2)) • knProd (fun i j => ∑ p, ∑ q, ric0 R p q * W i p j q) (id2 n))
      = ((b / (1 + ((n : ℝ) - 2) * b)) * (1 + b * ((n : ℝ) - 2))) •
        knProd (fun i j => ∑ p, ∑ q, ric0 R p q * W i p j q) (id2 n) :=
    smul_smul _ _ _
  rw [hss2, hcoef]
  simp

/-! ## Weyl-invariance of the difference -/

/-- `bwCorr` depends only on `ric` and `scalAlg`. -/
lemma bwCorr_congr (a b : ℝ) {Y Z : Curv4 n} (h1 : ric Y = ric Z) (h2 : scalAlg Y = scalAlg Z) :
    bwCorr a b Y = bwCorr a b Z := by
  have h3 : ric0 Y = ric0 Z := by
    funext i j
    simp only [ric0, h1, h2]
  have h4 : ric0sq Y = ric0sq Z := by
    funext i j; simp only [ric0sq, h3]
  have h5 : ric0Frob2 Y = ric0Frob2 Z := by simp only [ric0Frob2, h3]
  simp only [bwCorr, h1, h2, h3, h4, h5]

/-- The difference whose vanishing is the theorem. -/
noncomputable def bwDef (a b : ℝ) (R : Curv4 n) : Curv4 n :=
  linv a b (Q (ell a b R)) - (Q R + bwCorr a b R)

/-- **Weyl-invariance**: adding a Weyl tensor does not change `bwDef`. -/
theorem bwDef_add_weyl {a b : ℝ} {R W : Curv4 n} (hW : IsAlgCurv W)
    (hric : ∀ i j, ric W i j = 0)
    (hlinv : linv a b (BQ (ell a b R) W) = BQ R W) :
    bwDef a b (R + W) = bwDef a b R := by
  have hell : ell a b (R + W) = ell a b R + W := by
    rw [ell_add, ell_of_ric_zero hW hric]
  have hricW : ric W = 0 := funext (fun i => funext (fun j => hric i j))
  have hscalW : scalAlg W = 0 := scalAlg_eq_zero_of_ric_zero hW hric
  have hric_add : ric (R + W) = ric R + ric W := by
    funext i j; simp only [Pi.add_apply, ric_add_linv]
  have hcorr : bwCorr a b (R + W) = bwCorr a b R :=
    bwCorr_congr a b (by rw [hric_add, hricW, add_zero])
      (by rw [scalAlg_add_linv, hscalW, add_zero])
  have hQ : Q (ell a b (R + W)) = Q (ell a b R) + Q W + BQ (ell a b R) W + BQ (ell a b R) W := by
    rw [hell, Q_add_polarize]
  have hQW : linv a b (Q W) = Q W := lqk_linv_Q_of_ric_zero hW hric a b
  have hlin : linv a b (Q (ell a b R) + Q W + BQ (ell a b R) W + BQ (ell a b R) W)
      = linv a b (Q (ell a b R)) + Q W + BQ R W + BQ R W := by
    rw [linv_add, linv_add, linv_add, hQW, hlinv]
  simp only [bwDef]
  rw [hQ, hlin, hcorr, Q_add_polarize R W]
  abel

/-! ## The zero tensor -/

lemma ric_zero : ric (0 : Curv4 n) = 0 := by funext i j; simp [ric]
lemma scalAlg_zero : scalAlg (0 : Curv4 n) = 0 := by simp [scalAlg]
lemma ric0_zero : ric0 (0 : Curv4 n) = 0 := by
  funext i j; simp [ric0, ric, scalAlg]

lemma ell_zero (a b : ℝ) : ell a b (0 : Curv4 n) = 0 := by
  have h : (0 : Curv4 n) + b • knProd (ric0 (0 : Curv4 n)) (id2 n)
      + (a / (n : ℝ) * scalAlg (0 : Curv4 n)) • knProd (id2 n) (id2 n) = 0 := by
    rw [ric0_zero, scalAlg_zero, knProd_zero_left]
    simp
  simpa only [ell] using h

lemma Q_zero : Q (0 : Curv4 n) = 0 := by funext i j k l; simp [Q]

lemma linv_zero (a b : ℝ) : linv a b (0 : Curv4 n) = 0 := by
  have h : (0 : Curv4 n) - (b / (1 + ((n : ℝ) - 2) * b)) • knProd (ric0 (0 : Curv4 n)) (id2 n)
      - ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg (0 : Curv4 n))
        • knProd (id2 n) (id2 n) = 0 := by
    rw [ric0_zero, scalAlg_zero, knProd_zero_left]
    simp
  simpa only [linv] using h

lemma bwCorr_zero (a b : ℝ) : bwCorr a b (0 : Curv4 n) = 0 := by
  have h1 : ric (0 : Curv4 n) = 0 := ric_zero
  have h2 : ric0 (0 : Curv4 n) = 0 := ric0_zero
  have h3 : ric0sq (0 : Curv4 n) = 0 := by funext i j; simp [ric0sq, h2]
  have h4 : ric0Frob2 (0 : Curv4 n) = 0 := by simp [ric0Frob2, h2]
  simp only [bwCorr, h1, h2, h3, h4, knProd_zero_left, knProd_zero_right]
  simp

/-! ## The case `n = 2` -/

/-- In dimension `2` every algebraic curvature tensor is a multiple of `Iso 2`. -/
lemma IsAlgCurv_fin_two {R : Curv4 2} (hR : IsAlgCurv R) : R = (R 0 1 0 1) • Iso 2 := by
  funext i j k l
  have hA := hR.1
  have hP := hR.2.1
  have hB := hR.2.2
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [Iso, Pi.smul_apply, smul_eq_mul] <;>
    norm_num <;>
    linarith [hA 0 0 0 0, hA 1 1 0 0, hA 0 0 1 0, hA 1 1 1 1, hA 0 0 0 1, hA 1 1 1 0,
      hA 0 1 1 0, hA 1 0 0 1, hA 0 1 0 0, hA 1 0 1 1, hA 0 0 1 1, hA 1 1 0 1,
      hP 0 1 0 1, hP 0 1 1 0, hP 1 0 0 1, hP 1 0 1 0,
      anti34 hR 0 1 1 1, anti34 hR 1 0 1 1, anti34 hR 0 0 0 0, anti34 hR 1 1 1 1,
      anti34 hR 0 1 0 0, anti34 hR 1 0 0 0, anti34 hR 0 0 0 1, anti34 hR 1 1 0 1,
      hB 0 1 0 1, hB 1 0 1 0, hB 0 1 1 0, hB 1 0 0 1]

/-! ## The reduction to the `knProd A id` case -/

/-- The key Weyl identity of Böhm–Wilking (`BQ (A ∧ id) W = (A · W) ∧ id`). -/
def KeyForm (m : ℕ) (A : Fin m → Fin m → ℝ) (W : Curv4 m) : Prop :=
  BQ (knProd A (id2 m)) W = knProd (fun a b => ∑ p, ∑ q, A p q * W a p b q) (id2 m)

/-- The identity for the Ricci-type family `R = A ∧ id`. -/
def RTForm (m : ℕ) (a b : ℝ) (A : Fin m → Fin m → ℝ) : Prop :=
  linv a b (Q (ell a b (knProd A (id2 m))))
    = Q (knProd A (id2 m)) + bwCorr a b (knProd A (id2 m))

theorem bwDef_of_children
    (hkey : ∀ (m : ℕ) {A : Fin m → Fin m → ℝ}, (∀ i j, A i j = A j i) → ∀ {W : Curv4 m},
      IsAlgCurv W → (∀ i j, ric W i j = 0) → KeyForm m A W)
    (hrt : ∀ (m : ℕ) (a b : ℝ), 1 + 2 * ((m : ℝ) - 1) * a ≠ 0 → 1 + ((m : ℝ) - 2) * b ≠ 0 →
      ∀ {A : Fin m → Fin m → ℝ}, (∀ i j, A i j = A j i) → RTForm m a b A) :
    ∀ (n : ℕ) (a b : ℝ) (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0) (hb : 1 + ((n : ℝ) - 2) * b ≠ 0)
      {R : Curv4 n}, IsAlgCurv R → bwDef a b R = 0 := by
  intro n a b ha hb R hR
  by_cases h3 : 3 ≤ n
  · -- main case `3 ≤ n`
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      exact ne_of_gt this
    have hn1 : (n : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      linarith
    have hn2 : (n : ℝ) - 2 ≠ 0 := by
      have : (2 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 2 < n)
      linarith
    set A : Fin n → Fin n → ℝ := (1 / ((n : ℝ) - 2)) • ric0 R
      + (scalAlg R / (2 * (n : ℝ) * ((n : ℝ) - 1))) • id2 n with hA
    have hAapply : ∀ i j, A i j = (1 / ((n : ℝ) - 2)) * ric0 R i j
        + (scalAlg R / (2 * (n : ℝ) * ((n : ℝ) - 1))) * id2 n i j := by
      intro i j; rw [hA]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hAsym : ∀ i j, A i j = A j i := by
      intro i j; rw [hAapply, hAapply, ric0_symm hR, id2_symm]
    have hsum : (∑ k, A k k) = scalAlg R / (2 * ((n : ℝ) - 1)) := by
      rw [Finset.sum_congr rfl (fun k _ => hAapply k k)]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [sum_ric0_self n hn0 hR]
      have h2 : (∑ k : Fin n, id2 n k k) = (n : ℝ) := by simp [id2]
      rw [h2]
      field_simp
      ring
    have hric : ric (knProd A (id2 n)) = ric R := by
      funext p q
      rw [ric_knProd_id2, hsum, hAapply, ric0]
      simp only [id2]
      field_simp
      ring
    have hXn : IsAlgCurv (knProd A (id2 n)) := knProd_isAlgCurv hAsym (fun i j => id2_symm i j)
    have hWalg : IsAlgCurv (R - knProd A (id2 n)) := isAlgCurv_sub hR hXn
    have hWric : ∀ i j, ric (R - knProd A (id2 n)) i j = 0 := by
      intro i j; rw [ric_sub, hric]; ring
    have hdecomp : knProd A (id2 n) + (R - knProd A (id2 n)) = R := by abel
    have hstep : bwDef a b R = bwDef a b (knProd A (id2 n)) := by
      rw [← hdecomp]
      exact bwDef_add_weyl hWalg hWric
        (linv_BQ_ell_weyl_of_key n hn0 hXn hWalg hWric hb
          (show KeyForm n (ric0 (knProd A (id2 n))) (R - knProd A (id2 n))
            from hkey n (ric0_symm hXn) hWalg hWric))
    rw [hstep]
    exact sub_eq_zero.mpr (show RTForm n a b A from hrt n a b ha hb hAsym)
  · -- `n ≤ 2`
    have h3' : n ≤ 2 := by omega
    interval_cases n
    · exact funext (fun i => Fin.elim0 i)
    · -- n = 1
      have hR0 : R = 0 := by
        funext i j k l
        have hij : i = j := Fin.ext (by omega)
        subst hij
        have h := hR.1 i i k l
        simp only [Pi.zero_apply]
        linarith
      subst hR0
      rw [bwDef, ell_zero, Q_zero, linv_zero, bwCorr_zero]
      simp
    · -- n = 2
      have hstruct : R = (R 0 1 0 1) • Iso 2 := IsAlgCurv_fin_two hR
      have hAsym : ∀ i j, ((R 0 1 0 1) / 2) * id2 2 i j = ((R 0 1 0 1) / 2) * id2 2 j i := by
        intro i j; rw [id2_symm]
      have hkn : knProd (fun i j => ((R 0 1 0 1) / 2) * id2 2 i j) (id2 2) = R := by
        have hfun : (fun i j => ((R 0 1 0 1) / 2) * id2 2 i j)
            = ((R 0 1 0 1) / 2) • (id2 2 : Fin 2 → Fin 2 → ℝ) := rfl
        rw [hfun, knProd_smul_left_linv, knProd_id2_id2, smul_smul,
          show ((R 0 1 0 1) / 2) * 2 = R 0 1 0 1 from by ring]
        exact hstruct.symm
      rw [← hkn]
      exact sub_eq_zero.mpr (show RTForm 2 a b _ from hrt 2 a b ha hb hAsym)

/-! ## The main theorem -/

theorem linv_Q_ell (n : ℕ) (a b : ℝ) (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) :
    Work.Diff.Alg.Pinch.linv a b (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a b R)) =
      Submission.Diff.Alg.Q R
      + (((n : ℝ) - 2) * b ^ 2 - 2 * (a - b)) • Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.ric0 R) (Work.Diff.Alg.Pinch.ric0 R)
      + (2 * a) • Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.ric R) (Work.Diff.Alg.Pinch.ric R)
      + (2 * b ^ 2) • Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.ric0sq R) (Work.Diff.Alg.Pinch.id2 n)
      + ((((n : ℝ) * b ^ 2 * (1 - 2 * b) - 2 * (a - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
            / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) * Work.Diff.Alg.Pinch.ric0Frob2 R)
        • Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.id2 n) (Work.Diff.Alg.Pinch.id2 n) := by
  have h0 := bwDef_of_children
    (fun m {A} hA {W} hW hric => by
      show KeyForm m A W
      funext i j k l
      exact BQ_knProd_W m hA hW hric i j k l)
    (fun m a' b' ha' hb' {A} hA => linv_Q_ell_knProd m a' b' ha' hb' hA)
    n a b ha hb hR
  have h1 : linv a b (Q (ell a b R)) = Q R + bwCorr a b R := by
    simpa only [bwDef, sub_eq_zero] using h0
  rw [h1]
  simp only [bwCorr]
  abel

end Work.Diff.Alg.Pinch