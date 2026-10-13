/-
  annals_wilkies_conjecture, AREA E3, `Realify` (`ET` = "exp/tan"): CLEAN copy of the
  evaluation-identity / Jacobian-identity chain.

  The delivered modules `EvalID.lean`, `Jac.lean`, `MultiplicityBound_proved.lean` prove the same
  statements, but their proofs route through the two still-unproved interfaces `eval_monoNum`
  (`eval_monoNum.lean`) and `totalDegree_realify_le` (`totalDegree_realify_le.lean`).  Node K4
  (`Work.WilE3.Realify.MultiplicityBound_of_ET`) must be free of unfinished proofs, so here we
  reproduce only the lemmas of that chain that are affected, against the proved replacements
  `Work.WilE3.Realify.ET.eval_monoNum` and `Work.WilE3.Realify.ET.totalDegree_realify_le`.

  Everything else (`eval_rePoly_eq`, `SepChainLocal.ev_add`, `mkChain_ev`, `eventually_chart`,
  `SepChainLocal_fderiv_ev`, `grad_single`, `fderiv_evalUV`, `differentiableAt_evalUV`,
  `reifyMat_det_ne_zero`, …) is imported from the delivered modules unchanged.
-/
import Mathlib
import Submission.Work.WilE3.Realify.Defs
import Submission.Work.WilE3.Realify.EvalMain
import Submission.Work.WilE3.Realify.EvalID
import Submission.Work.WilE3.Realify.Transfer
import Submission.Work.WilE3.Realify.Jac
import Submission.Work.WilE3.Realify.SepChainLocal_fderiv_ev
import Submission.Work.WilE3.Realify.fderiv_evalUV
import Submission.Work.WilE3.Realify.differentiableAt_evalUV
import Submission.Work.WilE3.Realify.reifyMat_det_ne_zero
import Submission.Work.WilE3.Realify.exists_chart_offset
import Submission.Work.WilE3.Realify.MultiplicityBound_proved
import Submission.Work.WilE3.Realify.ET.eval_monoNum

namespace Work.WilE3.Realify.ET

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E

variable {k r : ℕ}

/-! ## The evaluation identity -/

theorem eval_monoNum_re (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (m : (Fin k ⊕ Fin r) →₀ ℕ) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hm : ∀ j, m (Sum.inr j) ≤ N) :
    MvPolynomial.eval (chainPt c cc u v) (rePoly (monoNum (k := k) (r := r) N e m))
      = Wval c cc v ^ N * (cmval c u v m).re := by
  rw [eval_rePoly_eq, eval_monoNum c cc e he N m u v hcos hm]
  simp only [cmval]
  rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, mul_comm]

theorem eval_monoNum_im (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (m : (Fin k ⊕ Fin r) →₀ ℕ) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hm : ∀ j, m (Sum.inr j) ≤ N) :
    MvPolynomial.eval (chainPt c cc u v) (imPoly (monoNum (k := k) (r := r) N e m))
      = Wval c cc v ^ N * (cmval c u v m).im := by
  rw [eval_imPoly_eq, eval_monoNum c cc e he N m u v hcos hm]
  simp only [cmval]
  rw [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add, mul_comm]

theorem eval_realifyRe (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (P : EAPoly k r) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hN : P.totalDegree ≤ N) :
    MvPolynomial.eval (chainPt c cc u v) (realifyRe N e P)
      = Wval c cc v ^ N * (eaEvalC c P (zOf (mkPt u v))).re := by
  rw [realifyRe_sum, map_sum]
  have hterm : ∀ m ∈ P.support,
      MvPolynomial.eval (chainPt c cc u v) (P.coeff m • rePoly (monoNum (k := k) (r := r) N e m))
        = Wval c cc v ^ N * (P.coeff m * (cmval c u v m).re) := by
    intro m hm
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
      eval_monoNum_re c cc e he N m u v hcos
        (fun j => exponent_le_of_totalDegree_le hN hm j)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [← sum_coeff_cmval c P u v, sum_re_eq]
  exact Finset.sum_congr rfl fun m _ => (real_mul_re _ _).symm

theorem eval_realifyIm (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (P : EAPoly k r) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hN : P.totalDegree ≤ N) :
    MvPolynomial.eval (chainPt c cc u v) (realifyIm N e P)
      = Wval c cc v ^ N * (eaEvalC c P (zOf (mkPt u v))).im := by
  rw [realifyIm_sum, map_sum]
  have hterm : ∀ m ∈ P.support,
      MvPolynomial.eval (chainPt c cc u v) (P.coeff m • imPoly (monoNum (k := k) (r := r) N e m))
        = Wval c cc v ^ N * (P.coeff m * (cmval c u v m).im) := by
    intro m hm
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
      eval_monoNum_im c cc e he N m u v hcos
        (fun j => exponent_le_of_totalDegree_le hN hm j)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [← sum_coeff_cmval c P u v, sum_im_eq]
  exact Finset.sum_congr rfl fun m _ => (real_mul_im _ _).symm

/-! ## The realified system -/

theorem evalRealSys_re (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (f g : Fin k → EAPoly k r) (a b : ℝ) (u v : Fin k → ℝ) (i : Fin k)
    (hcos : ∀ j, Real.cos ((∑ l, c.a j l * v l - cc j) / 2) ≠ 0)
    (hNf : (f i).totalDegree ≤ N) (hNg : (g i).totalDegree ≤ N) :
    (mkChain c cc).ev (realSys c cc e N f g a b (Fin.castAdd k i)) (mkPt u v)
      = Wval c cc v ^ N * (eaEvalC c (f i) (zOf (mkPt u v))
          + eps a b * eaEvalC c (g i) (zOf (mkPt u v))).re := by
  rw [realSys_castAdd, SepChainLocal.ev_add, SepChainLocal.ev_add, SepChainLocal.ev_C_mul,
    SepChainLocal.ev_C_mul, mkChain_ev, mkChain_ev, mkChain_ev,
    eval_realifyRe c cc e he N (f i) u v hcos hNf,
    eval_realifyRe c cc e he N (g i) u v hcos hNg,
    eval_realifyIm c cc e he N (g i) u v hcos hNg, re_add_eps_mul_re]
  ring

theorem evalRealSys_im (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (f g : Fin k → EAPoly k r) (a b : ℝ) (u v : Fin k → ℝ) (i : Fin k)
    (hcos : ∀ j, Real.cos ((∑ l, c.a j l * v l - cc j) / 2) ≠ 0)
    (hNf : (f i).totalDegree ≤ N) (hNg : (g i).totalDegree ≤ N) :
    (mkChain c cc).ev (realSys c cc e N f g a b (Fin.natAdd k i)) (mkPt u v)
      = Wval c cc v ^ N * (eaEvalC c (f i) (zOf (mkPt u v))
          + eps a b * eaEvalC c (g i) (zOf (mkPt u v))).im := by
  rw [realSys_natAdd, SepChainLocal.ev_add, SepChainLocal.ev_add, SepChainLocal.ev_C_mul,
    SepChainLocal.ev_C_mul, mkChain_ev, mkChain_ev, mkChain_ev,
    eval_realifyIm c cc e he N (f i) u v hcos hNf,
    eval_realifyIm c cc e he N (g i) u v hcos hNg,
    eval_realifyRe c cc e he N (g i) u v hcos hNg, re_add_eps_mul_im]
  ring

/-! ## The Jacobian identity -/

theorem eventuallyEq_re (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (A B : EAPoly k r) (a b : ℝ) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hNA : A.totalDegree ≤ N) (hNB : B.totalDegree ≤ N) :
    (fun w => (mkChain c cc).ev (realifyRe N e A + MvPolynomial.C a * realifyRe N e B
        + MvPolynomial.C (-b) * realifyIm N e B) w)
      =ᶠ[𝓝 (mkPt u v)]
        (fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w)
          * fun w => (evalUV c A w + eps a b * evalUV c B w).re := by
  filter_upwards [eventually_chart c cc u v hcos] with w hw
  change (mkChain c cc).ev (realifyRe N e A + MvPolynomial.C a * realifyRe N e B
      + MvPolynomial.C (-b) * realifyIm N e B) w
    = (mkChain c cc).ev (WPow (k := k) (r := r) N) w
      * (evalUV c A w + eps a b * evalUV c B w).re
  rw [SepChainLocal.ev_add, SepChainLocal.ev_add, SepChainLocal.ev_C_mul, SepChainLocal.ev_C_mul,
    mkChain_ev_of, mkChain_ev_of, mkChain_ev_of,
    eval_realifyRe c cc e he N A (uOf w) (vOf w) hw hNA,
    eval_realifyRe c cc e he N B (uOf w) (vOf w) hw hNB,
    eval_realifyIm c cc e he N B (uOf w) (vOf w) hw hNB,
    zOf_mkPt_uOf_vOf, ← ev_WPow, re_add_eps_mul_re]
  simp only [evalUV]
  ring

theorem eventuallyEq_im (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (A B : EAPoly k r) (a b : ℝ) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hNA : A.totalDegree ≤ N) (hNB : B.totalDegree ≤ N) :
    (fun w => (mkChain c cc).ev (realifyIm N e A + MvPolynomial.C a * realifyIm N e B
        + MvPolynomial.C b * realifyRe N e B) w)
      =ᶠ[𝓝 (mkPt u v)]
        (fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w)
          * fun w => (evalUV c A w + eps a b * evalUV c B w).im := by
  filter_upwards [eventually_chart c cc u v hcos] with w hw
  change (mkChain c cc).ev (realifyIm N e A + MvPolynomial.C a * realifyIm N e B
      + MvPolynomial.C b * realifyRe N e B) w
    = (mkChain c cc).ev (WPow (k := k) (r := r) N) w
      * (evalUV c A w + eps a b * evalUV c B w).im
  rw [SepChainLocal.ev_add, SepChainLocal.ev_add, SepChainLocal.ev_C_mul, SepChainLocal.ev_C_mul,
    mkChain_ev_of, mkChain_ev_of, mkChain_ev_of,
    eval_realifyIm c cc e he N A (uOf w) (vOf w) hw hNA,
    eval_realifyIm c cc e he N B (uOf w) (vOf w) hw hNB,
    eval_realifyRe c cc e he N B (uOf w) (vOf w) hw hNB,
    zOf_mkPt_uOf_vOf, ← ev_WPow, re_add_eps_mul_im]
  simp only [evalUV]
  ring

theorem ev_d_comb_re (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (A B : EAPoly k r) (a b : ℝ) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hNA : A.totalDegree ≤ N) (hNB : B.totalDegree ≤ N)
    (hzero : eaEvalC c A (zOf (mkPt u v)) + eps a b * eaEvalC c B (zOf (mkPt u v)) = 0)
    (hdiff : DifferentiableAt ℝ (fun w => (evalUV c A w + eps a b * evalUV c B w).re)
      (mkPt u v))
    (l : Fin (k + k)) :
    (mkChain c cc).ev ((mkChain c cc).d l (realifyRe N e A + MvPolynomial.C a * realifyRe N e B
        + MvPolynomial.C (-b) * realifyIm N e B)) (mkPt u v)
      = Wval c cc v ^ N * fderiv ℝ (fun w => (evalUV c A w + eps a b * evalUV c B w).re)
          (mkPt u v) (Pi.single l 1) := by
  have hU : DifferentiableAt ℝ
      (fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w) (mkPt u v) :=
    (SepChainLocal_fderiv_ev (mkChain c cc) (WPow (k := k) (r := r) N) (mkPt u v)
      (mkChain_hx c cc u v hcos)).differentiableAt
  have hmul : fderiv ℝ ((fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w)
        * (fun w => (evalUV c A w + eps a b * evalUV c B w).re)) (mkPt u v)
      = (mkChain c cc).ev (WPow (k := k) (r := r) N) (mkPt u v)
          • fderiv ℝ (fun w => (evalUV c A w + eps a b * evalUV c B w).re) (mkPt u v)
        + (evalUV c A (mkPt u v) + eps a b * evalUV c B (mkPt u v)).re
          • fderiv ℝ (fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w) (mkPt u v) :=
    fderiv_mul hU hdiff
  have hval : (mkChain c cc).ev (WPow (k := k) (r := r) N) (mkPt u v) = Wval c cc v ^ N := by
    rw [ev_WPow, vOf_mkPt]
  have hV0 : (evalUV c A (mkPt u v) + eps a b * evalUV c B (mkPt u v)).re = 0 := by
    rw [evalUV, evalUV, hzero]
    exact Complex.zero_re
  have hderiv : fderiv ℝ (fun w => (mkChain c cc).ev (realifyRe N e A
        + MvPolynomial.C a * realifyRe N e B + MvPolynomial.C (-b) * realifyIm N e B) w)
        (mkPt u v)
      = Wval c cc v ^ N
          • fderiv ℝ (fun w => (evalUV c A w + eps a b * evalUV c B w).re) (mkPt u v) := by
    rw [(eventuallyEq_re c cc e he N A B a b u v hcos hNA hNB).fderiv_eq, hmul, hval, hV0,
      zero_smul, add_zero]
  have hcr := SepChainLocal_fderiv_ev (mkChain c cc) (realifyRe N e A
    + MvPolynomial.C a * realifyRe N e B + MvPolynomial.C (-b) * realifyIm N e B) (mkPt u v)
    (mkChain_hx c cc u v hcos)
  calc (mkChain c cc).ev ((mkChain c cc).d l (realifyRe N e A + MvPolynomial.C a * realifyRe N e B
        + MvPolynomial.C (-b) * realifyIm N e B)) (mkPt u v)
      = (grad (mkChain c cc) (realifyRe N e A + MvPolynomial.C a * realifyRe N e B
          + MvPolynomial.C (-b) * realifyIm N e B) (mkPt u v)) (Pi.single l 1) :=
        (grad_single (mkChain c cc) _ (mkPt u v) l).symm
    _ = fderiv ℝ (fun w => (mkChain c cc).ev (realifyRe N e A
          + MvPolynomial.C a * realifyRe N e B + MvPolynomial.C (-b) * realifyIm N e B) w)
          (mkPt u v) (Pi.single l 1) := by rw [hcr.fderiv]
    _ = (Wval c cc v ^ N
          • fderiv ℝ (fun w => (evalUV c A w + eps a b * evalUV c B w).re) (mkPt u v))
          (Pi.single l 1) := by rw [hderiv]
    _ = Wval c cc v ^ N * fderiv ℝ (fun w => (evalUV c A w + eps a b * evalUV c B w).re)
          (mkPt u v) (Pi.single l 1) := by
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem ev_d_comb_im (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (A B : EAPoly k r) (a b : ℝ) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hNA : A.totalDegree ≤ N) (hNB : B.totalDegree ≤ N)
    (hzero : eaEvalC c A (zOf (mkPt u v)) + eps a b * eaEvalC c B (zOf (mkPt u v)) = 0)
    (hdiff : DifferentiableAt ℝ (fun w => (evalUV c A w + eps a b * evalUV c B w).im)
      (mkPt u v))
    (l : Fin (k + k)) :
    (mkChain c cc).ev ((mkChain c cc).d l (realifyIm N e A + MvPolynomial.C a * realifyIm N e B
        + MvPolynomial.C b * realifyRe N e B)) (mkPt u v)
      = Wval c cc v ^ N * fderiv ℝ (fun w => (evalUV c A w + eps a b * evalUV c B w).im)
          (mkPt u v) (Pi.single l 1) := by
  have hU : DifferentiableAt ℝ
      (fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w) (mkPt u v) :=
    (SepChainLocal_fderiv_ev (mkChain c cc) (WPow (k := k) (r := r) N) (mkPt u v)
      (mkChain_hx c cc u v hcos)).differentiableAt
  have hmul : fderiv ℝ ((fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w)
        * (fun w => (evalUV c A w + eps a b * evalUV c B w).im)) (mkPt u v)
      = (mkChain c cc).ev (WPow (k := k) (r := r) N) (mkPt u v)
          • fderiv ℝ (fun w => (evalUV c A w + eps a b * evalUV c B w).im) (mkPt u v)
        + (evalUV c A (mkPt u v) + eps a b * evalUV c B (mkPt u v)).im
          • fderiv ℝ (fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w) (mkPt u v) :=
    fderiv_mul hU hdiff
  have hval : (mkChain c cc).ev (WPow (k := k) (r := r) N) (mkPt u v) = Wval c cc v ^ N := by
    rw [ev_WPow, vOf_mkPt]
  have hV0 : (evalUV c A (mkPt u v) + eps a b * evalUV c B (mkPt u v)).im = 0 := by
    rw [evalUV, evalUV, hzero]
    exact Complex.zero_im
  have hderiv : fderiv ℝ (fun w => (mkChain c cc).ev (realifyIm N e A
        + MvPolynomial.C a * realifyIm N e B + MvPolynomial.C b * realifyRe N e B) w)
        (mkPt u v)
      = Wval c cc v ^ N
          • fderiv ℝ (fun w => (evalUV c A w + eps a b * evalUV c B w).im) (mkPt u v) := by
    rw [(eventuallyEq_im c cc e he N A B a b u v hcos hNA hNB).fderiv_eq, hmul, hval, hV0,
      zero_smul, add_zero]
  have hcr := SepChainLocal_fderiv_ev (mkChain c cc) (realifyIm N e A
    + MvPolynomial.C a * realifyIm N e B + MvPolynomial.C b * realifyRe N e B) (mkPt u v)
    (mkChain_hx c cc u v hcos)
  calc (mkChain c cc).ev ((mkChain c cc).d l (realifyIm N e A + MvPolynomial.C a * realifyIm N e B
        + MvPolynomial.C b * realifyRe N e B)) (mkPt u v)
      = (grad (mkChain c cc) (realifyIm N e A + MvPolynomial.C a * realifyIm N e B
          + MvPolynomial.C b * realifyRe N e B) (mkPt u v)) (Pi.single l 1) :=
        (grad_single (mkChain c cc) _ (mkPt u v) l).symm
    _ = fderiv ℝ (fun w => (mkChain c cc).ev (realifyIm N e A
          + MvPolynomial.C a * realifyIm N e B + MvPolynomial.C b * realifyRe N e B) w)
          (mkPt u v) (Pi.single l 1) := by rw [hcr.fderiv]
    _ = (Wval c cc v ^ N
          • fderiv ℝ (fun w => (evalUV c A w + eps a b * evalUV c B w).im) (mkPt u v))
          (Pi.single l 1) := by rw [hderiv]
    _ = Wval c cc v ^ N * fderiv ℝ (fun w => (evalUV c A w + eps a b * evalUV c B w).im)
          (mkPt u v) (Pi.single l 1) := by
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem jac_matrix (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (f g : Fin k → EAPoly k r) (a b : ℝ) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hNf : ∀ i, (f i).totalDegree ≤ N) (hNg : ∀ i, (g i).totalDegree ≤ N)
    (hzero : ∀ i, eaEvalC c (f i) (zOf (mkPt u v))
      + eps a b * eaEvalC c (g i) (zOf (mkPt u v)) = 0) :
    Matrix.of (fun (i : Fin (k + k)) (l : Fin (k + k)) =>
        (mkChain c cc).ev ((mkChain c cc).d l (realSys c cc e N f g a b i)) (mkPt u v))
      = (Wval c cc v ^ N) • reifyMat (cplxJac c f g a b u v) := by
  ext i l
  rw [Matrix.of_apply]
  revert i
  refine Fin.addCases (motive := fun i =>
      (mkChain c cc).ev ((mkChain c cc).d l (realSys c cc e N f g a b i)) (mkPt u v)
        = ((Wval c cc v ^ N) • reifyMat (cplxJac c f g a b u v)) i l) ?_ ?_
  · intro i
    revert l
    refine Fin.addCases (motive := fun l =>
        (mkChain c cc).ev ((mkChain c cc).d l (realSys c cc e N f g a b (Fin.castAdd k i)))
            (mkPt u v)
          = ((Wval c cc v ^ N) • reifyMat (cplxJac c f g a b u v)) (Fin.castAdd k i) l) ?_ ?_
    · intro j
      rw [realSys_castAdd, Matrix.smul_apply, reifyMat_left_left,
        ev_d_comb_re c cc e he N (f i) (g i) a b u v hcos (hNf i) (hNg i) (hzero i)
          (differentiableAt_comb_re c (f i) (g i) a b (mkPt u v))
          (Fin.castAdd k j),
        fderiv_comb_re_castAdd c f g a b u v i j]
      simp only [smul_eq_mul, cplxJac, Matrix.of_apply]
    · intro j
      rw [realSys_castAdd, Matrix.smul_apply, reifyMat_left_right,
        ev_d_comb_re c cc e he N (f i) (g i) a b u v hcos (hNf i) (hNg i) (hzero i)
          (differentiableAt_comb_re c (f i) (g i) a b (mkPt u v))
          (Fin.natAdd k j),
        fderiv_comb_re_natAdd c f g a b u v i j]
      simp only [smul_eq_mul, cplxJac, Matrix.of_apply]
  · intro i
    revert l
    refine Fin.addCases (motive := fun l =>
        (mkChain c cc).ev ((mkChain c cc).d l (realSys c cc e N f g a b (Fin.natAdd k i)))
            (mkPt u v)
          = ((Wval c cc v ^ N) • reifyMat (cplxJac c f g a b u v)) (Fin.natAdd k i) l) ?_ ?_
    · intro j
      rw [realSys_natAdd, Matrix.smul_apply, reifyMat_right_left,
        ev_d_comb_im c cc e he N (f i) (g i) a b u v hcos (hNf i) (hNg i) (hzero i)
          (differentiableAt_comb_im c (f i) (g i) a b (mkPt u v))
          (Fin.castAdd k j),
        fderiv_comb_im_castAdd c f g a b u v i j]
      simp only [smul_eq_mul, cplxJac, Matrix.of_apply]
    · intro j
      rw [realSys_natAdd, Matrix.smul_apply, reifyMat_right_right,
        ev_d_comb_im c cc e he N (f i) (g i) a b u v hcos (hNf i) (hNg i) (hzero i)
          (differentiableAt_comb_im c (f i) (g i) a b (mkPt u v))
          (Fin.natAdd k j),
        fderiv_comb_im_natAdd c f g a b u v i j]
      simp only [smul_eq_mul, cplxJac, Matrix.of_apply]

/-! ## The nondegeneracy transfer -/

theorem nondegen_of_cplx (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (f g : Fin k → EAPoly k r) (a b : ℝ) (z : Fin k → ℂ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * (z i).im - cc j) / 2) ≠ 0)
    (hNf : ∀ i, (f i).totalDegree ≤ N) (hNg : ∀ i, (g i).totalDegree ≤ N)
    (hzero : ∀ i, eaEvalC c (f i) z + eps a b * eaEvalC c (g i) z = 0)
    (hnd : (Matrix.of fun i j => eaEvalC c (eaD c j (f i)) z
      + eps a b * eaEvalC c (eaD c j (g i)) z).det ≠ 0) :
    (mkChain c cc).Nondegen (realSys c cc e N f g a b) (cplxPt z) := by
  have hcos' : ∀ j, Real.cos ((∑ i, c.a j i * (vOf (cplxPt z)) i - cc j) / 2) ≠ 0 := by
    simpa [vOf_cplxPt] using hcos
  have hzv : zOf (mkPt (uOf (cplxPt z)) (vOf (cplxPt z))) = z := by
    rw [mkPt_uOf_vOf, zOf_cplxPt]
  constructor
  · intro i
    revert i
    refine Fin.addCases (motive := fun i =>
        (mkChain c cc).ev (realSys c cc e N f g a b i) (cplxPt z) = 0) ?_ ?_
    · intro i
      rw [← mkPt_uOf_vOf (cplxPt z),
        evalRealSys_re c cc e he N f g a b (uOf (cplxPt z)) (vOf (cplxPt z)) i hcos'
        (hNf i) (hNg i), hzv, hzero i]
      simp
    · intro i
      rw [← mkPt_uOf_vOf (cplxPt z),
        evalRealSys_im c cc e he N f g a b (uOf (cplxPt z)) (vOf (cplxPt z)) i hcos'
        (hNf i) (hNg i), hzv, hzero i]
      simp
  · have hJ := jac_matrix c cc e he N f g a b (uOf (cplxPt z)) (vOf (cplxPt z)) hcos'
      hNf hNg (fun i => by rw [hzv]; exact hzero i)
    rw [← mkPt_uOf_vOf (cplxPt z), hJ, Matrix.det_smul]
    have hW : Wval c cc (vOf (cplxPt z)) ≠ 0 := ne_of_gt (Wval_pos c cc (vOf (cplxPt z)))
    refine mul_ne_zero (pow_ne_zero _ (pow_ne_zero N hW)) ?_
    refine reifyMat_det_ne_zero _ ?_
    rwa [cplxJac, hzv]

end

end Work.WilE3.Realify.ET
