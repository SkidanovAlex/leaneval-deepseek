import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.RicFormDefs
import Submission.Work.Diff.Alg.Pinch.ric_linv
import Submission.Work.Diff.Alg.Pinch.scal_linv
import Submission.Work.Diff.Alg.Pinch.qform_bmat
import Submission.Work.Diff.Alg.Pinch.qform_ric_Q
import Submission.Work.Diff.Alg.Pinch.bmat_symm
import Submission.Work.Diff.Alg.Pinch.bmat_psd
import Submission.Work.Diff.Alg.Pinch.bmat_knProd_id2
import Submission.Work.Diff.Alg.Pinch.bmat_knProd_id2_id2
import Submission.Work.Diff.Alg.Pinch.qform_kernel
import Submission.Work.Diff.Alg.Pinch.qform_mul_nonneg
import Submission.Work.Diff.Alg.Pinch.inPIC2_ric_eq_zero
import Submission.Work.Diff.Alg.Pinch.ell_isAlgCurv
import Submission.Work.Diff.Alg.Pinch.Q_isAlgCurv
import Submission.Work.Diff.Alg.Pinch.ric_Q
import Submission.Work.Diff.Alg.Pinch.scalAlg_Q
import Submission.Work.Diff.Alg.Pinch.scalAlg_pos_of_inPIC2_ricpinch
import Submission.Work.Diff.Alg.Pinch.ric0_mulVec_of_tight
import Submission.Work.Diff.Alg.Pinch.sum_ricE_sq
import Submission.Work.Diff.Alg.Pinch.W_expansion
import Submission.Work.Diff.Alg.Pinch.Delta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The strict Ricci-form improvement at a tight direction

`Work.Diff.Alg.Pinch.ricForm_X_strict_at_tight_a` (Böhm–Wilking Lemma 3.5 /
Brendle–Schoen Proposition 14).  See `HANDOFF.md` and the docstring of
`Diff/Alg/Pinch/Ccone_transversal_b.lean`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The quadratic form of a `linv`-transform, expanded through its definition. -/
private lemma qform_ric_linv (a b : ℝ) {Y : Curv4 n} (hY : IsAlgCurv Y) (v : Fin n → ℝ) :
    qform (ric (linv a b Y)) v
      = qform (ric Y) v
        - (((n : ℝ) - 2) * b / (1 + ((n : ℝ) - 2) * b))
            * (qform (ric Y) v - (scalAlg Y / (n : ℝ)) * (∑ i, v i * v i))
        - (2 * ((n : ℝ) - 1) * a / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) * scalAlg Y
            * (∑ i, v i * v i) := by
  have hpt : ∀ i j : Fin n, ric (linv a b Y) i j
      = ric Y i j - (((n : ℝ) - 2) * b / (1 + ((n : ℝ) - 2) * b)) * ric0 Y i j
        - (2 * ((n : ℝ) - 1) * a / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) * scalAlg Y
            * (if i = j then (1 : ℝ) else 0) := fun i j => ric_linv n a b hY i j
  rw [show ric (linv a b Y)
      = (ric Y - (((n : ℝ) - 2) * b / (1 + ((n : ℝ) - 2) * b)) • ric0 Y)
        - ((2 * ((n : ℝ) - 1) * a / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) * scalAlg Y)
            • (fun i j : Fin n => (if i = j then (1 : ℝ) else 0)) from by
    funext i j
    rw [hpt i j]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]]
  rw [qform_sub, qform_smul, qform_sub, qform_smul, qform_ric0,
    show qform (fun i j : Fin n => (if i = j then (1 : ℝ) else 0)) v = ∑ i, v i * v i from by
      simp only [qform]; exact sum_delta_sq v]

/-- `∑ᵢⱼ (c δᵢⱼ) Yᵢⱼ = c ∑ᵢ Yᵢᵢ`. -/
private lemma sum_sum_delta_mul (c : ℝ) (Y : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, (c * (if i = j then (1 : ℝ) else 0)) * Y i j) = c * ∑ i, Y i i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg (fun h : i = j => hj h.symm)]
    ring
  · intro h; exact absurd (Finset.mem_univ i) h

theorem ricForm_X_strict_at_tight_a (n : ℕ) (hn2 : 2 ≤ n) {a : ℝ} (ha : 1 / 2 < a)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S) (hS0 : S ≠ 0)
    (hP : Submission.Diff.Alg.InPIC2 S)
    (hric : Work.Diff.Alg.Pinch.RicPinch (1 - 4 / ((n : ℝ) - 2 + 8 * a)) S) :
    ∀ v : Fin n → ℝ, v ≠ 0 →
      ((1 - 4 / ((n : ℝ) - 2 + 8 * a)) * Submission.Diff.Alg.scalAlg S / (n : ℝ))
          * (∑ i, v i * v i)
        = ∑ i, ∑ j, Work.Diff.Alg.Pinch.ric S i j * v i * v j →
      0 < (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric
              (Work.Diff.Alg.Pinch.linv a (1 / 2)
                (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a (1 / 2) S)))
              i j * v i * v j)
        - ((1 - 4 / ((n : ℝ) - 2 + 8 * a)) * Submission.Diff.Alg.scalAlg
              (Work.Diff.Alg.Pinch.linv a (1 / 2)
                (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a (1 / 2) S)))
              / (n : ℝ)) * (∑ i, v i * v i) := by
  intro v hv htight
  set p : ℝ := 1 - 4 / ((n : ℝ) - 2 + 8 * a) with hpdef
  set c : ℝ := 1 + 2 * ((n : ℝ) - 1) * a with hcdef
  set Lam : ℝ := scalAlg S / (n : ℝ) with hLam
  set sg : ℝ := ric0Frob2 S / (n : ℝ) with hsg
  set vv : ℝ := ∑ i, v i * v i with hvv
  set E : Curv4 n := ell a (1 / 2) S with hE
  set QE : Curv4 n := Q E with hQE
  set X : Curv4 n := linv a (1 / 2) QE with hX
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hD4 : (4 : ℝ) < (n : ℝ) - 2 + 8 * a := by nlinarith [ha, hn2R]
  have hD0 : (0 : ℝ) < (n : ℝ) - 2 + 8 * a := by linarith
  have hp_pos : 0 < p := by
    rw [hpdef]
    have h1 : 4 / ((n : ℝ) - 2 + 8 * a) < 1 := by
      rw [div_lt_iff₀ hD0]; linarith
    linarith
  have hp_lt : p < 1 := by
    rw [hpdef]
    have h1 : 0 < 4 / ((n : ℝ) - 2 + 8 * a) := div_pos (by norm_num) hD0
    linarith
  have hc_pos : 0 < c := by rw [hcdef]; nlinarith [ha, hn2R]
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hdene : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0 := by rw [← hcdef]; exact hc_ne
  have hdene' : 1 + (n : ℝ) * a * 2 - a * 2 ≠ 0 := by
    rw [show 1 + (n : ℝ) * a * 2 - a * 2 = 1 + 2 * ((n : ℝ) - 1) * a from by ring]
    exact hdene
  have hdene2 : 1 + 2 * a * ((n : ℝ) - 1) ≠ 0 := by
    rw [show 1 + 2 * a * ((n : ℝ) - 1) = 1 + 2 * ((n : ℝ) - 1) * a from by ring]
    exact hdene
  have hkden : 1 + ((n : ℝ) - 2) * (1 / 2) ≠ 0 := by
    have h1 : 1 + ((n : ℝ) - 2) * (1 / 2) = (n : ℝ) / 2 := by ring
    rw [h1]; exact ne_of_gt (by linarith : (0 : ℝ) < (n : ℝ) / 2)
  have hLam_pos : 0 < Lam := by
    rw [hLam]
    exact scalAlg_pos_of_inPIC2_ricpinch n hn2 ha hS hS0 hP (by rw [← hpdef]; exact hric)
  have hvv_pos : 0 < vv := by
    rw [hvv]
    obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (funext fun i => h i)
    have hmul : 0 < v i₀ * v i₀ := mul_self_pos.mpr hi₀
    have hnn : ∀ i, 0 ≤ v i * v i := fun i => mul_self_nonneg (v i)
    have hle : v i₀ * v i₀ ≤ ∑ i, v i * v i :=
      Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i₀)
    linarith
  have hsg_nn : 0 ≤ sg := by
    rw [hsg]
    have : 0 ≤ ric0Frob2 S := by
      rw [ric0Frob2]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _
    exact div_nonneg this (le_of_lt hnR)
  -- ### the positive semidefinite matrix `M = ric S - p Lam`
  set M : Fin n → Fin n → ℝ := fun i j => ric S i j - (p * Lam) * (if i = j then 1 else 0) with hMdef
  have hMq : ∀ w : Fin n → ℝ, qform M w = qform (ric S) w - (p * Lam) * (∑ i, w i * w i) := by
    intro w
    rw [hMdef]
    rw [show (fun i j : Fin n => ric S i j - (p * Lam) * (if i = j then (1 : ℝ) else 0))
        = ric S - (p * Lam) • (fun i j : Fin n => (if i = j then (1 : ℝ) else 0)) from by
      funext i j; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]]
    rw [qform_sub, qform_smul]
    rw [show qform (fun i j : Fin n => (if i = j then (1 : ℝ) else 0)) w = ∑ i, w i * w i from by
      simp only [qform]; exact sum_delta_sq w]
  have hMpsd : ∀ w : Fin n → ℝ, 0 ≤ qform M w := by
    intro w
    rw [hMq w]
    have h := hric w
    have h' : (p * Lam) * (∑ i, w i * w i) ≤ qform (ric S) w := by
      have h2 : p * Lam = p * scalAlg S / (n : ℝ) := by rw [hLam]; ring
      rw [h2]
      exact h
    linarith
  have hMsym : ∀ i j, M i j = M j i := by
    intro i j
    have hif : (if i = j then (1 : ℝ) else 0) = (if j = i then (1 : ℝ) else 0) := by
      by_cases h : i = j
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    simp only [hMdef]
    rw [ric_symm hS i j, hif]
  have htight' : qform (ric S) v = (p * Lam) * vv := by
    show (∑ i, ∑ j, ric S i j * v i * v j) = (p * Lam) * vv
    rw [← htight]
    rw [show p * scalAlg S / (n : ℝ) = p * Lam from by rw [hLam]; ring]
  have hMv0 : qform M v = 0 := by
    rw [hMq v, htight']
    ring
  have hAv : ∀ i, ∑ j, ric0 S i j * v j = (p - 1) * Lam * v i := by
    intro i
    have h := ric0_mulVec_of_tight n hp_lt hS hric (v := v) (by rw [← hvv]; exact htight) i
    have h2 : (p - 1) * (scalAlg S / (n : ℝ)) = (p - 1) * Lam := by rw [hLam]
    rw [h2] at h
    exact h
  -- ### the sums of the traceless Ricci tensor
  have hvAv : (∑ i, v i * (∑ j, ric0 S i j * v j)) = (p - 1) * Lam * vv := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [hAv i])]
    rw [hvv]
    rw [show (∑ i : Fin n, v i * ((p - 1) * Lam * v i))
        = ((p - 1) * Lam) * (∑ i, v i * v i) from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring]
  have hA2 : (∑ i, (∑ j, ric0 S i j * v j) * (∑ j, ric0 S i j * v j))
      = ((p - 1) * Lam) ^ 2 * vv := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [hAv i])]
    rw [hvv]
    rw [show (∑ i : Fin n, ((p - 1) * Lam * v i) * ((p - 1) * Lam * v i))
        = ((p - 1) * Lam) ^ 2 * (∑ i, v i * v i) from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring]
  -- ### the tensor `B = bmat v S`
  set B : Fin n → Fin n → ℝ := bmat v S with hBdef
  have hBsym : ∀ i j, B i j = B j i := by
    intro i j; rw [hBdef]; exact bmat_symm n hS v i j
  have hBpsd : ∀ w : Fin n → ℝ, 0 ≤ qform B w := by
    intro w; rw [hBdef]; exact bmat_psd n hP v w
  have htrB : (∑ i, B i i) = p * Lam * vv := by
    rw [hBdef, bmat_diag v hS]
    rw [show (∑ i, ∑ j, v i * v j * ric S i j) = qform (ric S) v from by
      simp only [qform]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring]
    exact htight'
  have htrAB : -p * (1 - p) * Lam ^ 2 * vv ≤ ∑ i, ∑ j, ric0 S i j * B i j := by
    have hdecomp : ∀ i j, ric0 S i j = M i j + (p - 1) * Lam * (if i = j then (1 : ℝ) else 0) := by
      intro i j
      rw [show Lam = scalAlg S / (n : ℝ) from hLam]
      simp only [hMdef, ric0, id2]
      ring
    have hsplit : (∑ i, ∑ j, ric0 S i j * B i j)
        = (∑ i, ∑ j, M i j * B i j) + (p - 1) * Lam * (∑ i, B i i) := by
      rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hdecomp i j]))]
      rw [show (∑ i, ∑ j, (M i j + (p - 1) * Lam * (if i = j then (1 : ℝ) else 0)) * B i j)
          = (∑ i, ∑ j, M i j * B i j)
            + (∑ i, ∑ j, ((p - 1) * Lam * (if i = j then (1 : ℝ) else 0)) * B i j) from by
        simp only [add_mul, Finset.sum_add_distrib]]
      rw [show (∑ i, ∑ j, ((p - 1) * Lam * (if i = j then (1 : ℝ) else 0)) * B i j)
          = (p - 1) * Lam * (∑ i, B i i) from sum_sum_delta_mul ((p - 1) * Lam) (fun i j => B i j)]
    have hnn : 0 ≤ ∑ i, ∑ j, M i j * B i j := qform_mul_nonneg n hMsym hBsym hMpsd hBpsd
    rw [hsplit, htrB]
    have : (p - 1) * Lam * (p * Lam * vv) = -p * (1 - p) * Lam ^ 2 * vv := by ring
    linarith [this]
  -- ### the transform `X`
  have hEalg : IsAlgCurv E := by rw [hE]; exact ell_isAlgCurv n a (1 / 2) hS
  have hQEalg : IsAlgCurv QE := by rw [hQE]; exact Q_isAlgCurv n hEalg
  have hXval : X = linv a (1 / 2) (Q (ell a (1 / 2) S)) := by rw [hX, hQE, hE]
  have hlinv : qform (ric X) v
      = qform (ric QE) v
        - (((n : ℝ) - 2) * (1 / 2) / (1 + ((n : ℝ) - 2) * (1 / 2)))
            * (qform (ric QE) v - (scalAlg QE / (n : ℝ)) * vv)
        - (2 * ((n : ℝ) - 1) * a / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) * scalAlg QE * vv := by
    rw [hX, hvv]
    exact qform_ric_linv (n := n) a (1 / 2) hQEalg v
  have hscal : scalAlg X = scalAlg QE / (1 + 2 * ((n : ℝ) - 1) * a) := by
    rw [hX]; exact scal_linv n a (1 / 2) hdene hQEalg
  -- ### `W` and `I2`
  set W : ℝ := ∑ i, ∑ j, ric E i j * bmat v E i j with hWdef
  set I2 : ℝ := ∑ i, ∑ j, ric E i j * ric E i j with hI2def
  have hA1 : qform (ric QE) v = 2 * W := by
    rw [hQE, hWdef, hE] at *
    exact qform_ric_Q n hEalg v
  have hscQE : scalAlg QE = 2 * I2 := by
    rw [hQE, hI2def, hE] at *
    exact scalAlg_Q n hEalg
  have hI2val : I2 = (1 + ((n : ℝ) - 2) * (1 / 2)) ^ 2 * ((n : ℝ) * sg)
      + (Lam * (1 + 2 * ((n : ℝ) - 1) * a)) ^ 2 * (n : ℝ) := by
    rw [hI2def, hE]
    rw [sum_ricE_sq n (a := a) (S := S) hS]
    rw [show (∑ i, ∑ j, ric0 S i j * ric0 S i j) = (n : ℝ) * sg from by
      rw [hsg, ric0Frob2]
      field_simp]
    rw [show scalAlg S * (1 + 2 * ((n : ℝ) - 1) * a) / (n : ℝ)
        = Lam * (1 + 2 * ((n : ℝ) - 1) * a) from by rw [hLam]; ring]
  have hWval : W = (1 + ((n : ℝ) - 2) * (1 / 2))
        * ((∑ i, ∑ j, ric0 S i j * B i j)
           - ((p - 1) * Lam) ^ 2 * vv
           + ((n : ℝ) / 2) * vv * sg
           - 2 * a * Lam * ((p - 1) * Lam * vv))
      + (Lam * (1 + 2 * ((n : ℝ) - 1) * a))
        * (p * Lam * vv + ((n : ℝ) - 2) / 2 * ((p - 1) * Lam * vv)
           + 2 * a * ((n : ℝ) - 1) * Lam * vv) := by
    rw [hWdef, hE]
    have h := W_expansion n hnne (a := a) (S := S) hS (v := v) (Lam := Lam) (sg := sg)
      (vv := vv) (trB := ∑ i, B i i) hLam hsg hvv (by rw [hBdef])
    rw [h]
    rw [hBdef, hA2, hvAv, htrB]
  -- ### assembly
  have hkey1 : qform (ric X) v - (p * scalAlg X / (n : ℝ)) * vv
      = (1 - ((n : ℝ) - 2) * (1 / 2) / (1 + ((n : ℝ) - 2) * (1 / 2))) * (2 * W)
        + ((((n : ℝ) - 2) * (1 / 2) / (1 + ((n : ℝ) - 2) * (1 / 2))) / (n : ℝ)
            - 2 * ((n : ℝ) - 1) * a / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))
            - p / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) * (2 * I2) * vv := by
    rw [hlinv, hscal, hA1, hscQE]
    field_simp [hnne, hdene]
    ring
  have hkey2 : (1 - ((n : ℝ) - 2) * (1 / 2) / (1 + ((n : ℝ) - 2) * (1 / 2))) * (2 * W)
        + ((((n : ℝ) - 2) * (1 / 2) / (1 + ((n : ℝ) - 2) * (1 / 2))) / (n : ℝ)
            - 2 * ((n : ℝ) - 1) * a / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))
            - p / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) * (2 * I2) * vv
      = 2 * (1 - p) * ((2 * a - 1) * Lam ^ 2 + (n : ℝ) ^ 2 * sg / (4 * c)) * vv
        + 2 * ((∑ i, ∑ j, ric0 S i j * B i j) + p * (1 - p) * Lam ^ 2 * vv) := by
    rw [hWval, hI2val, hcdef]
    field_simp [hnne, hdene, hdene2, hdene', hkden]
    ring
  have hmain : qform (ric X) v - (p * scalAlg X / (n : ℝ)) * vv
      = 2 * (1 - p) * ((2 * a - 1) * Lam ^ 2 + (n : ℝ) ^ 2 * sg / (4 * c)) * vv
        + 2 * ((∑ i, ∑ j, ric0 S i j * B i j) + p * (1 - p) * Lam ^ 2 * vv) := by
    rw [hkey1, hkey2]
  have hpos : 0 < 2 * (1 - p) * ((2 * a - 1) * Lam ^ 2 + (n : ℝ) ^ 2 * sg / (4 * c)) * vv := by
    have h1 : 0 < 1 - p := by linarith
    have h2 : 0 < 2 * a - 1 := by linarith
    have h3 : 0 < (2 * a - 1) * Lam ^ 2 := by positivity
    have h4 : 0 ≤ (n : ℝ) ^ 2 * sg / (4 * c) := by positivity
    have h5 : 0 < (2 * a - 1) * Lam ^ 2 + (n : ℝ) ^ 2 * sg / (4 * c) := by linarith
    positivity
  have hbnd : 0 ≤ 2 * ((∑ i, ∑ j, ric0 S i j * B i j) + p * (1 - p) * Lam ^ 2 * vv) := by
    have h1 : 0 ≤ (∑ i, ∑ j, ric0 S i j * B i j) + p * (1 - p) * Lam ^ 2 * vv := by
      linarith [htrAB]
    linarith
  have : (∑ i, ∑ j, ric
        (linv a (1 / 2) (Q (ell a (1 / 2) S))) i j * v i * v j)
      - ((1 - 4 / ((n : ℝ) - 2 + 8 * a)) * scalAlg (linv a (1 / 2) (Q (ell a (1 / 2) S)))
          / (n : ℝ)) * (∑ i, v i * v i) = qform (ric X) v - (p * scalAlg X / (n : ℝ)) * vv := by
    rw [← hpdef]
    rfl
  rw [this, hmain]
  linarith

end Work.Diff.Alg.Pinch
