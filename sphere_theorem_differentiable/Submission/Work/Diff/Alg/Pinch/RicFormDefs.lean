import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.ric_Q
import Submission.Work.Diff.Alg.Pinch.scalAlg_Q
import Submission.Work.Diff.Alg.Pinch.ric_knProd_id2
import Submission.Work.Diff.Alg.Pinch.scalAlg_knProd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary objects for the strict Ricci-form lemma `ricForm_X_strict_at_tight_a`

This file holds the small definitions and the elementary linearity facts used by
`Work.Diff.Alg.Pinch.ricForm_X_strict_at_tight_a` (Böhm–Wilking Lemma 3.5, Brendle–Schoen
Proposition 14).

Given a vector `v : Fin n → ℝ` and a four-index array `R` (an orthonormal-frame curvature tensor),
we write

* `bmat v R p q = ∑ᵢⱼ vᵢ vⱼ R i p j q` — the `(0,2)`-tensor obtained by contracting two of the
  indices of `R` with `v` (in the frame literature: `R(v, e_p, v, e_q)`);
* `qform M v = ∑ᵢⱼ M i j vᵢ vⱼ` — the quadratic form of a `(0,2)`-tensor.

The point of `bmat` is that the Ricci tensor of Hamilton's reaction term is
`ric (Q R) i j = 2 ∑_{p q} (ric R) p q · R i p j q` (`Work.Diff.Alg.Pinch.ric_Q`), so that
`∑ᵢⱼ ric (Q R) i j vᵢ vⱼ = 2 ∑_{p q} (ric R) p q · (bmat v R) p q`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- `bmat v R p q = ∑ᵢⱼ vᵢ vⱼ R i p j q`: contract the first and third index of `R` with `v`. -/
noncomputable def bmat (v : Fin n → ℝ) (R : Curv4 n) : Fin n → Fin n → ℝ :=
  fun p q => ∑ i, ∑ j, v i * v j * R i p j q

/-- The quadratic form `∑ᵢⱼ M i j vᵢ vⱼ` of a `(0,2)`-tensor. -/
noncomputable def qform (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * v i * v j

lemma bmat_add (v : Fin n → ℝ) (R S : Curv4 n) :
    bmat v (R + S) = bmat v R + bmat v S := by
  funext p q
  simp only [bmat, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma bmat_sub (v : Fin n → ℝ) (R S : Curv4 n) :
    bmat v (R - S) = bmat v R - bmat v S := by
  funext p q
  simp only [bmat, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma bmat_smul (v : Fin n → ℝ) (c : ℝ) (R : Curv4 n) :
    bmat v (c • R) = c • bmat v R := by
  funext p q
  simp only [bmat, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

lemma bmat_zero (v : Fin n → ℝ) : bmat v (0 : Curv4 n) = 0 := by
  funext p q; simp [bmat]

lemma qform_add (M N : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    qform (M + N) v = qform M v + qform N v := by
  simp only [qform, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma qform_sub (M N : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    qform (M - N) v = qform M v - qform N v := by
  simp only [qform, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The Kronecker delta contracts a double sum into a sum of squares. -/
lemma sum_delta_sq (v : Fin n → ℝ) :
    (∑ i, ∑ j, (if i = j then (1 : ℝ) else 0) * v i * v j) = ∑ i, v i * v i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg (fun h : i = j => hj h.symm)]
    ring
  · intro h; exact absurd (Finset.mem_univ i) h

lemma qform_smul (c : ℝ) (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    qform (c • M) v = c * qform M v := by
  simp only [qform, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

/-- The diagonal of `bmat` is the quadratic form of the Ricci tensor:
`∑ p, bmat v R p p = ∑ᵢⱼ vᵢ vⱼ (ric R) i j`. -/
lemma bmat_diag (v : Fin n → ℝ) {R : Curv4 n} (hR : IsAlgCurv R) :
    (∑ p, bmat v R p p) = ∑ i, ∑ j, v i * v j * ric R i j := by
  obtain ⟨hanti, hpair, _⟩ := hR
  have hanti2 : ∀ i j k l : Fin n, R i j l k = - R i j k l := by
    intro i j k l
    have h1 := hpair i j l k
    have h2 := hanti l k i j
    have h3 := hpair i j k l
    linarith
  have hpt : ∀ i j p : Fin n, R i p j p = R p i p j := by
    intro i j p
    have h1 := hpair i p j p
    have h2 := hanti j p i p
    have h3 := hanti2 p j i p
    have h4 := hpair p j p i
    linarith
  have hL : (∑ p, bmat v R p p) = ∑ i, ∑ j, ∑ p, v i * v j * R p i p j := by
    simp only [bmat]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro p _
    rw [hpt i j p]
  rw [hL]
  simp only [ric]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.mul_sum]


/-- `scalAlg` is the trace of `ric`. -/
lemma scalAlg_eq_sum_ric_aux (W : Curv4 n) (hW : IsAlgCurv W) :
    scalAlg W = ∑ i, ric W i i := by
  obtain ⟨hanti, hpair, _⟩ := hW
  simp only [scalAlg, ric]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  have h1 : W j i j i = - W i j j i := hanti i j j i
  have h2 : W i j j i = - W i j i j := by
    have h3 := hpair i j j i
    have h4 := hanti j i i j
    linarith
  linarith

/-- The trace of the traceless Ricci tensor vanishes. -/
lemma ric0_trace_zero (W : Curv4 n) (hW : IsAlgCurv W) : (∑ i, ric0 W i i) = 0 := by
  have h : ∀ i : Fin n, ric0 W i i = ric W i i - scalAlg W / (n : ℝ) := by
    intro i; simp [ric0, id2]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_sub_distrib]
  have h2 : (∑ _i : Fin n, scalAlg W / (n : ℝ)) = scalAlg W := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [scalAlg]
    · have hn : ((n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp h0)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_div_cancel₀ _ hn]
  rw [h2, scalAlg_eq_sum_ric_aux W hW]
  ring

/-- The Ricci tensor of the Böhm–Wilking transform `ell a b`. -/
theorem ric_ell_aux (a b : ℝ) (hn : (n : ℝ) ≠ 0) {R : Curv4 n} (hR : IsAlgCurv R) (i j : Fin n) :
    ric (ell a b R) i j
      = (1 + ((n : ℝ) - 2) * b) * ric0 R i j
        + (scalAlg R * (1 + 2 * ((n : ℝ) - 1) * a) / (n : ℝ)) * (if i = j then (1 : ℝ) else 0) := by
  have h1 : ric (knProd (ric0 R) (id2 n)) i j = ((n : ℝ) - 2) * ric0 R i j := by
    rw [ric_knProd_id2]
    have h2 : (∑ k, ric0 R k k) = 0 := ric0_trace_zero R hR
    rw [h2]; ring
  have h2 : ric (knProd (id2 n) (id2 n)) i j
      = (2 * ((n : ℝ) - 1)) * (if i = j then (1 : ℝ) else 0) := by
    rw [ric_knProd_id2]
    have h3 : (∑ k, id2 n k k) = (n : ℝ) := by
      have hk : ∀ k : Fin n, id2 n k k = (1 : ℝ) := by intro k; simp [id2]
      rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [h3]
    simp only [id2]
    ring
  have h5 : ric R i j = ric0 R i j + (scalAlg R / (n : ℝ)) * (if i = j then (1 : ℝ) else 0) := by
    have h6 : ric0 R i j = ric R i j - (scalAlg R / (n : ℝ)) * (if i = j then (1 : ℝ) else 0) := by
      simp only [ric0, id2]
    linarith
  have key : (scalAlg R / (n : ℝ)) * (if i = j then (1 : ℝ) else 0)
      + (a / (n : ℝ) * scalAlg R) * (2 * ((n : ℝ) - 1) * (if i = j then (1 : ℝ) else 0))
      = (scalAlg R * (1 + 2 * ((n : ℝ) - 1) * a) / (n : ℝ)) * (if i = j then (1 : ℝ) else 0) := by
    by_cases h : i = j
    · rw [if_pos h]; field_simp
    · rw [if_neg h]; ring
  show ric (R + b • knProd (ric0 R) (id2 n)
      + (a / (n : ℝ) * scalAlg R) • knProd (id2 n) (id2 n)) i j = _
  simp only [ric_add_linv, ric_smul_linv, h1, h2]
  rw [h5]
  linarith [key]

/-- The quadratic form of the traceless Ricci tensor. -/
lemma qform_ric0 (Y : Curv4 n) (v : Fin n → ℝ) :
    qform (ric0 Y) v = qform (ric Y) v - (scalAlg Y / (n : ℝ)) * (∑ i, v i * v i) := by
  have h : ric0 Y
      = ric Y - (scalAlg Y / (n : ℝ)) • (fun i j : Fin n => (if i = j then (1 : ℝ) else 0)) := by
    funext i j
    simp only [ric0, id2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h, qform_sub, qform_smul]
  rw [show qform (fun i j : Fin n => (if i = j then (1 : ℝ) else 0)) v = ∑ i, v i * v i from by
    simp only [qform]; exact sum_delta_sq v]

end Work.Diff.Alg.Pinch
