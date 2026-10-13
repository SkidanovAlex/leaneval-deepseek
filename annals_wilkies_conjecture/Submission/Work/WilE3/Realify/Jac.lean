/-
  annals_wilkies_conjecture, AREA E3, `Realify` (the realified Jacobian matrix).

  The perturbation parameter of `MultiplicityBound` is *complex*: the complexified system is
  `F_i + ε G_i` with `ε = a + i b`.  Accordingly the realified system is the pair of real
  combinations

    `Re: realifyRe(f_i) + a·realifyRe(g_i) - b·realifyIm(g_i)`,
    `Im: realifyIm(f_i) + a·realifyIm(g_i) + b·realifyRe(g_i)`.

  `jac_matrix`: its Jacobian at `(u,v)` is `Wval^N` times the realification of the complex Jacobian
  `(∂_j (F_i + ε G_i))`.  Together with `reifyMat_det_ne_zero` this is what makes nondegenerate
  complex zeros realify to nondegenerate real zeros.
-/
import Submission.Work.WilE3.Realify.Transfer
import Submission.Work.WilE3.Realify.fderiv_evalUV
import Submission.Work.WilE3.Realify.differentiableAt_evalUV

namespace Work.WilE3.Realify

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E

variable {k r : ℕ}

/-- The complex perturbation parameter `a + i b`. -/
def eps (a b : ℝ) : ℂ := (a : ℂ) + (b : ℂ) * Complex.I

theorem eps_re (a b : ℝ) : (eps a b).re = a := by simp [eps]

theorem eps_im (a b : ℝ) : (eps a b).im = b := by simp [eps]

theorem re_add_eps_mul_re (A B : ℂ) (a b : ℝ) :
    (A + eps a b * B).re = A.re + (a * B.re - b * B.im) := by
  simp only [eps, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero,
    add_zero, zero_add]

theorem re_add_eps_mul_im (A B : ℂ) (a b : ℝ) :
    (A + eps a b * B).im = A.im + (a * B.im + b * B.re) := by
  simp only [eps, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero,
    add_zero, zero_add]

/-- The realified system of a complexified system with a complex perturbation `ε = a + i b`. -/
def realSys (c : EAChain k r) (cc e : Fin r → ℝ) (N : ℕ) (f g : Fin k → EAPoly k r)
    (a b : ℝ) : Fin (k + k) → EAPoly (k + k) (r + r) :=
  Fin.addCases
    (fun i => realifyRe N e (f i) + MvPolynomial.C a * realifyRe N e (g i)
      + MvPolynomial.C (-b) * realifyIm N e (g i))
    (fun i => realifyIm N e (f i) + MvPolynomial.C a * realifyIm N e (g i)
      + MvPolynomial.C b * realifyRe N e (g i))

theorem realSys_castAdd {c : EAChain k r} {cc e : Fin r → ℝ} {N : ℕ}
    {f g : Fin k → EAPoly k r} {a b : ℝ} (i : Fin k) :
    realSys c cc e N f g a b (Fin.castAdd k i)
      = realifyRe N e (f i) + MvPolynomial.C a * realifyRe N e (g i)
        + MvPolynomial.C (-b) * realifyIm N e (g i) := by
  simp only [realSys, Fin.addCases_left]

theorem realSys_natAdd {c : EAChain k r} {cc e : Fin r → ℝ} {N : ℕ}
    {f g : Fin k → EAPoly k r} {a b : ℝ} (i : Fin k) :
    realSys c cc e N f g a b (Fin.natAdd k i)
      = realifyIm N e (f i) + MvPolynomial.C a * realifyIm N e (g i)
        + MvPolynomial.C b * realifyRe N e (g i) := by
  simp only [realSys, Fin.addCases_right]

theorem reifyMat_left_left {A : Matrix (Fin k) (Fin k) ℂ} (i j : Fin k) :
    reifyMat A (Fin.castAdd k i) (Fin.castAdd k j) = (A i j).re := by
  simp only [reifyMat, Matrix.of_apply, Fin.addCases_left]

theorem reifyMat_left_right {A : Matrix (Fin k) (Fin k) ℂ} (i j : Fin k) :
    reifyMat A (Fin.castAdd k i) (Fin.natAdd k j) = -(A i j).im := by
  simp only [reifyMat, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]

theorem reifyMat_right_left {A : Matrix (Fin k) (Fin k) ℂ} (i j : Fin k) :
    reifyMat A (Fin.natAdd k i) (Fin.castAdd k j) = (A i j).im := by
  simp only [reifyMat, Matrix.of_apply, Fin.addCases_right, Fin.addCases_left]

theorem reifyMat_right_right {A : Matrix (Fin k) (Fin k) ℂ} (i j : Fin k) :
    reifyMat A (Fin.natAdd k i) (Fin.natAdd k j) = (A i j).re := by
  simp only [reifyMat, Matrix.of_apply, Fin.addCases_right]

/-- The complex Jacobian of a perturbed complexified system. -/
def cplxJac (c : EAChain k r) (f g : Fin k → EAPoly k r) (a b : ℝ) (u v : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => eaEvalC c (eaD c j (f i)) (zOf (mkPt u v))
    + eps a b * eaEvalC c (eaD c j (g i)) (zOf (mkPt u v))

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

theorem fderiv_comb_re_castAdd (c : EAChain k r) (f g : Fin k → EAPoly k r) (a b : ℝ)
    (u v : Fin k → ℝ) (i j : Fin k) :
    fderiv ℝ (fun w => (evalUV c (f i) w + eps a b * evalUV c (g i) w).re) (mkPt u v)
        (Pi.single (Fin.castAdd k j) 1)
      = (eaEvalC c (eaD c j (f i)) (zOf (mkPt u v))
          + eps a b * eaEvalC c (eaD c j (g i)) (zOf (mkPt u v))).re := by
  have hfun : (fun w : Fin (k + k) → ℝ => (evalUV c (f i) w + eps a b * evalUV c (g i) w).re)
      = (fun w => (evalUV c (f i) w).re) + (a • fun w => (evalUV c (g i) w).re)
        - b • fun w => (evalUV c (g i) w).im := by
    funext w
    rw [re_add_eps_mul_re]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, re_add_eps_mul_re]
  rw [fderiv_sub ((differentiableAt_evalUV c (f i) (mkPt u v)).1.add
        ((differentiableAt_evalUV c (g i) (mkPt u v)).1.const_smul a))
      ((differentiableAt_evalUV c (g i) (mkPt u v)).2.const_smul b),
    fderiv_add (differentiableAt_evalUV c (f i) (mkPt u v)).1
      ((differentiableAt_evalUV c (g i) (mkPt u v)).1.const_smul a),
    fderiv_const_smul (differentiableAt_evalUV c (g i) (mkPt u v)).1 a,
    fderiv_const_smul (differentiableAt_evalUV c (g i) (mkPt u v)).2 b,
    sub_apply, add_apply, smul_apply, smul_apply,
    (fderiv_evalUV c (f i) (mkPt u v) j).1, (fderiv_evalUV c (g i) (mkPt u v) j).1,
    (fderiv_evalUV c (g i) (mkPt u v) j).2.2.1]
  ring

theorem fderiv_comb_re_natAdd (c : EAChain k r) (f g : Fin k → EAPoly k r) (a b : ℝ)
    (u v : Fin k → ℝ) (i j : Fin k) :
    fderiv ℝ (fun w => (evalUV c (f i) w + eps a b * evalUV c (g i) w).re) (mkPt u v)
        (Pi.single (Fin.natAdd k j) 1)
      = -(eaEvalC c (eaD c j (f i)) (zOf (mkPt u v))
          + eps a b * eaEvalC c (eaD c j (g i)) (zOf (mkPt u v))).im := by
  have hfun : (fun w : Fin (k + k) → ℝ => (evalUV c (f i) w + eps a b * evalUV c (g i) w).re)
      = (fun w => (evalUV c (f i) w).re) + (a • fun w => (evalUV c (g i) w).re)
        - b • fun w => (evalUV c (g i) w).im := by
    funext w
    rw [re_add_eps_mul_re]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, re_add_eps_mul_im]
  rw [fderiv_sub ((differentiableAt_evalUV c (f i) (mkPt u v)).1.add
        ((differentiableAt_evalUV c (g i) (mkPt u v)).1.const_smul a))
      ((differentiableAt_evalUV c (g i) (mkPt u v)).2.const_smul b),
    fderiv_add (differentiableAt_evalUV c (f i) (mkPt u v)).1
      ((differentiableAt_evalUV c (g i) (mkPt u v)).1.const_smul a),
    fderiv_const_smul (differentiableAt_evalUV c (g i) (mkPt u v)).1 a,
    fderiv_const_smul (differentiableAt_evalUV c (g i) (mkPt u v)).2 b,
    sub_apply, add_apply, smul_apply, smul_apply,
    (fderiv_evalUV c (f i) (mkPt u v) j).2.1, (fderiv_evalUV c (g i) (mkPt u v) j).2.1,
    (fderiv_evalUV c (g i) (mkPt u v) j).2.2.2]
  ring

theorem fderiv_comb_im_castAdd (c : EAChain k r) (f g : Fin k → EAPoly k r) (a b : ℝ)
    (u v : Fin k → ℝ) (i j : Fin k) :
    fderiv ℝ (fun w => (evalUV c (f i) w + eps a b * evalUV c (g i) w).im) (mkPt u v)
        (Pi.single (Fin.castAdd k j) 1)
      = (eaEvalC c (eaD c j (f i)) (zOf (mkPt u v))
          + eps a b * eaEvalC c (eaD c j (g i)) (zOf (mkPt u v))).im := by
  have hfun : (fun w : Fin (k + k) → ℝ => (evalUV c (f i) w + eps a b * evalUV c (g i) w).im)
      = (fun w => (evalUV c (f i) w).im) + (a • fun w => (evalUV c (g i) w).im)
        + b • fun w => (evalUV c (g i) w).re := by
    funext w
    rw [re_add_eps_mul_im]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, re_add_eps_mul_im]
  rw [fderiv_add ((differentiableAt_evalUV c (f i) (mkPt u v)).2.add
        ((differentiableAt_evalUV c (g i) (mkPt u v)).2.const_smul a))
      ((differentiableAt_evalUV c (g i) (mkPt u v)).1.const_smul b),
    fderiv_add (differentiableAt_evalUV c (f i) (mkPt u v)).2
      ((differentiableAt_evalUV c (g i) (mkPt u v)).2.const_smul a),
    fderiv_const_smul (differentiableAt_evalUV c (g i) (mkPt u v)).2 a,
    fderiv_const_smul (differentiableAt_evalUV c (g i) (mkPt u v)).1 b,
    add_apply, add_apply, smul_apply, smul_apply,
    (fderiv_evalUV c (f i) (mkPt u v) j).2.2.1, (fderiv_evalUV c (g i) (mkPt u v) j).2.2.1,
    (fderiv_evalUV c (g i) (mkPt u v) j).1]
  ring

theorem fderiv_comb_im_natAdd (c : EAChain k r) (f g : Fin k → EAPoly k r) (a b : ℝ)
    (u v : Fin k → ℝ) (i j : Fin k) :
    fderiv ℝ (fun w => (evalUV c (f i) w + eps a b * evalUV c (g i) w).im) (mkPt u v)
        (Pi.single (Fin.natAdd k j) 1)
      = (eaEvalC c (eaD c j (f i)) (zOf (mkPt u v))
          + eps a b * eaEvalC c (eaD c j (g i)) (zOf (mkPt u v))).re := by
  have hfun : (fun w : Fin (k + k) → ℝ => (evalUV c (f i) w + eps a b * evalUV c (g i) w).im)
      = (fun w => (evalUV c (f i) w).im) + (a • fun w => (evalUV c (g i) w).im)
        + b • fun w => (evalUV c (g i) w).re := by
    funext w
    rw [re_add_eps_mul_im]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, re_add_eps_mul_re]
  rw [fderiv_add ((differentiableAt_evalUV c (f i) (mkPt u v)).2.add
        ((differentiableAt_evalUV c (g i) (mkPt u v)).2.const_smul a))
      ((differentiableAt_evalUV c (g i) (mkPt u v)).1.const_smul b),
    fderiv_add (differentiableAt_evalUV c (f i) (mkPt u v)).2
      ((differentiableAt_evalUV c (g i) (mkPt u v)).2.const_smul a),
    fderiv_const_smul (differentiableAt_evalUV c (g i) (mkPt u v)).2 a,
    fderiv_const_smul (differentiableAt_evalUV c (g i) (mkPt u v)).1 b,
    add_apply, add_apply, smul_apply, smul_apply,
    (fderiv_evalUV c (f i) (mkPt u v) j).2.2.2, (fderiv_evalUV c (g i) (mkPt u v) j).2.2.2,
    (fderiv_evalUV c (g i) (mkPt u v) j).2.1]
  ring


theorem differentiableAt_comb_re (c : EAChain k r) (A B : EAPoly k r) (a b : ℝ)
    (w : Fin (k + k) → ℝ) :
    DifferentiableAt ℝ (fun w' => (evalUV c A w' + eps a b * evalUV c B w').re) w := by
  have hfun : (fun w' : Fin (k + k) → ℝ => (evalUV c A w' + eps a b * evalUV c B w').re)
      = (fun w' => (evalUV c A w').re) + (a • fun w' => (evalUV c B w').re)
        - b • fun w' => (evalUV c B w').im := by
    funext w'
    rw [re_add_eps_mul_re]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  exact ((differentiableAt_evalUV c A w).1.add
    ((differentiableAt_evalUV c B w).1.const_smul a)).sub
    ((differentiableAt_evalUV c B w).2.const_smul b)

theorem differentiableAt_comb_im (c : EAChain k r) (A B : EAPoly k r) (a b : ℝ)
    (w : Fin (k + k) → ℝ) :
    DifferentiableAt ℝ (fun w' => (evalUV c A w' + eps a b * evalUV c B w').im) w := by
  have hfun : (fun w' : Fin (k + k) → ℝ => (evalUV c A w' + eps a b * evalUV c B w').im)
      = (fun w' => (evalUV c A w').im) + (a • fun w' => (evalUV c B w').im)
        + b • fun w' => (evalUV c B w').re := by
    funext w'
    rw [re_add_eps_mul_im]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  exact ((differentiableAt_evalUV c A w).2.add
    ((differentiableAt_evalUV c B w).2.const_smul a)).add
    ((differentiableAt_evalUV c B w).1.const_smul b)

/-- **The Jacobian of the realified system is `Wval^N` times the realified complex Jacobian.** -/
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

end

end Work.WilE3.Realify
