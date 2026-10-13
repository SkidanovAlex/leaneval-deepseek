import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Sep
import Submission.Work.WilE3.Realify.EvalMain
import Submission.Work.WilE3.Realify.EvalID
import Submission.Work.WilE3.Realify.Jac
import Submission.Work.WilE3.Realify.SepChainLocal_fderiv_ev
import Submission.Work.WilE3.Realify.fderiv_evalUV
import Submission.Work.WilE3.Realify.differentiableAt_evalUV
import Submission.Work.WilE3.Realify.reifyMat_det_ne_zero
import Submission.Work.WilE3.Realify.totalDegree_realify_le
import Submission.Work.WilE3.Realify.exists_chart_offset
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Realify

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E

variable {k r : ℕ}

/-! ## §A. Elementary preparation -/

/-- `Polynomial.eval` over `ℕ` is monotone (there is no such lemma in Mathlib). -/
theorem eval_mono_nat (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval_add, Polynomial.eval_add]; exact add_le_add hp hq
  | monomial n c =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

/-- The realification of a complex point: `z ↦ (Re z, Im z)`. -/
def cplxPt (z : Fin k → ℂ) : Fin (k + k) → ℝ :=
  mkPt (fun i => (z i).re) (fun i => (z i).im)

theorem zOf_cplxPt (z : Fin k → ℂ) : zOf (cplxPt z) = z := by
  funext i
  simp only [zOf, cplxPt, mkPt_apply_castAdd, mkPt_apply_natAdd]
  simpa using Complex.re_add_im (z i)

theorem cplxPt_injective : Function.Injective (cplxPt (k := k)) := by
  intro z w hzw
  funext i
  have h1 : (cplxPt z) (Fin.castAdd k i) = (cplxPt w) (Fin.castAdd k i) := by rw [hzw]
  have h2 : (cplxPt z) (Fin.natAdd k i) = (cplxPt w) (Fin.natAdd k i) := by rw [hzw]
  simp only [cplxPt, mkPt_apply_castAdd, mkPt_apply_natAdd] at h1 h2
  exact Complex.ext h1 h2

theorem vOf_cplxPt (z : Fin k → ℂ) : vOf (cplxPt z) = fun i => (z i).im := by
  funext i; simp only [vOf, cplxPt, mkPt_apply_natAdd]

theorem uOf_cplxPt (z : Fin k → ℂ) : uOf (cplxPt z) = fun i => (z i).re := by
  funext i; simp only [uOf, cplxPt, mkPt_apply_castAdd]

theorem dist_cplxPt_le (z x : Fin k → ℂ) : dist (cplxPt z) (cplxPt x) ≤ ‖z - x‖ := by
  rw [dist_pi_le_iff (norm_nonneg _)]
  intro l
  revert l
  refine Fin.addCases ?_ ?_
  · intro i
    have h1 : (cplxPt z) (Fin.castAdd k i) = (z i).re := by
      simp only [cplxPt, mkPt_apply_castAdd]
    have h2 : (cplxPt x) (Fin.castAdd k i) = (x i).re := by
      simp only [cplxPt, mkPt_apply_castAdd]
    rw [h1, h2, Real.dist_eq, ← Complex.sub_re]
    exact le_trans (Complex.abs_re_le_norm _) (norm_le_pi_norm (z - x) i)
  · intro i
    have h1 : (cplxPt z) (Fin.natAdd k i) = (z i).im := by
      simp only [cplxPt, mkPt_apply_natAdd]
    have h2 : (cplxPt x) (Fin.natAdd k i) = (x i).im := by
      simp only [cplxPt, mkPt_apply_natAdd]
    rw [h1, h2, Real.dist_eq, ← Complex.sub_im]
    exact le_trans (Complex.abs_im_le_norm _) (norm_le_pi_norm (z - x) i)

theorem mkChain_arg_natAdd' (c : EAChain k r) (cc : Fin r → ℝ) (w : Fin (k + k) → ℝ)
    (j : Fin r) :
    (∑ i, (mkChain c cc).a (Fin.natAdd r j) i * w i) + (mkChain c cc).b (Fin.natAdd r j)
      = (∑ i, c.a j i * (vOf w) i - cc j) / 2 := by
  have h := mkChain_arg_natAdd c cc (uOf w) (vOf w) j
  rwa [mkPt_uOf_vOf] at h

/-- The clearing factor is positive. -/
theorem Wval_pos (c : EAChain k r) (cc : Fin r → ℝ) (v : Fin k → ℝ) :
    0 < Wval c cc v := by
  rw [Wval]
  exact Finset.prod_pos fun j _ => by positivity

/-- The chart condition on a ball: if the half-angle arguments of the base point are at distance
`< π/2` from the poles, so are those of every point of a sufficiently small ball. -/
theorem chart_hcos (c : EAChain k r) (cc : Fin r → ℝ) (x : Fin k → ℂ)
    (hdom : ∀ (j : Fin r) (w : ℝ),
      |w - (∑ i, c.a j i * (x i).im)| < Real.pi / 2 → Real.cos ((w - cc j) / 2) ≠ 0)
    {R : ℝ} (hR0 : 0 ≤ R) (hsmall : 2 * R * (∑ j : Fin r, ∑ i : Fin k, |c.a j i|) < Real.pi / 2)
    {w : Fin (k + k) → ℝ} (hw : ∀ i, |(vOf w) i - (x i).im| < 2 * R) (j : Fin r) :
    Real.cos ((∑ i, c.a j i * (vOf w) i - cc j) / 2) ≠ 0 := by
  apply hdom j
  have h1 : (∑ i, c.a j i * (vOf w) i) - (∑ i, c.a j i * (x i).im)
      = ∑ i, c.a j i * ((vOf w) i - (x i).im) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  have h2 : |∑ i, c.a j i * ((vOf w) i - (x i).im)| ≤ ∑ i : Fin k, |c.a j i| * (2 * R) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (le_of_lt (hw i)) (abs_nonneg _)
  have h3 : ∑ i : Fin k, |c.a j i| * (2 * R) = (∑ i : Fin k, |c.a j i|) * (2 * R) := by
    rw [Finset.sum_mul]
  have h4 : (∑ i : Fin k, |c.a j i|) * (2 * R)
      ≤ (∑ j' : Fin r, ∑ i : Fin k, |c.a j' i|) * (2 * R) := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    refine Finset.single_le_sum (f := fun j' => ∑ i : Fin k, |c.a j' i|) ?_ (Finset.mem_univ j)
    intro j' _
    positivity
  have h5 : (∑ j' : Fin r, ∑ i : Fin k, |c.a j' i|) * (2 * R)
      = 2 * R * (∑ j' : Fin r, ∑ i : Fin k, |c.a j' i|) := by ring
  linarith [h2, h3.le, h4, h5.le, hsmall]

/-! ## §B. Linearity of the polynomial in the perturbation parameter -/

theorem eaD_C_mul (c : EAChain k r) (j : Fin k) (a : ℝ) (Q : EAPoly k r) :
    eaD c j (MvPolynomial.C a * Q) = MvPolynomial.C a * eaD c j Q := by
  rw [API.eaD_mul, API.eaD_C, zero_mul, zero_add]

theorem eaEvalC_C_mul (c : EAChain k r) (a : ℝ) (Q : EAPoly k r) (z : Fin k → ℂ) :
    eaEvalC c (MvPolynomial.C a * Q) z = a * eaEvalC c Q z := by
  rw [API.eaEvalC_mul, API.eaEvalC_C]

theorem eaEvalC_add_C_mul (c : EAChain k r) (P Q : EAPoly k r) (a : ℝ) (z : Fin k → ℂ) :
    eaEvalC c (P + MvPolynomial.C a * Q) z = eaEvalC c P z + a * eaEvalC c Q z := by
  rw [API.eaEvalC_add, eaEvalC_C_mul]

theorem eaEvalC_eaD_add_C_mul (c : EAChain k r) (P Q : EAPoly k r) (a : ℝ) (j : Fin k)
    (z : Fin k → ℂ) :
    eaEvalC c (eaD c j (P + MvPolynomial.C a * Q)) z
      = eaEvalC c (eaD c j P) z + a * eaEvalC c (eaD c j Q) z := by
  rw [API.eaD_add, API.eaEvalC_add, eaD_C_mul, eaEvalC_C_mul]

/-! ## §C. The nondegeneracy transfer -/

/-- A nondegenerate complex zero realifies to a nondegenerate zero of the realified system. -/
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

/-! ## §D. The degree bound -/

theorem totalDegree_add_C_mul_le (P Q : EAPoly k r) (a : ℝ) (B : ℕ)
    (hP : P.totalDegree ≤ B) (hQ : Q.totalDegree ≤ B) :
    (P + MvPolynomial.C a * Q).totalDegree ≤ B := by
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le hP ?_)
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact hQ

theorem totalDegree_one_add_X_sq_le :
    (1 + MvPolynomial.X (0 : Fin 1) ^ 2 : MvPolynomial (Fin 1) ℝ).totalDegree ≤ 2 := by
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · simp
  · rw [MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.totalDegree_monomial (fun₀ | (0 : Fin 1) => 2) (c := 1) (by norm_num)]
    simp

theorem totalDegree_R_le (c : EAChain k r) (cc : Fin r → ℝ) :
    ∑ j : Fin (r + r), ((mkChain c cc).R j).totalDegree ≤ 3 * r := by
  rw [Fin.sum_univ_add]
  have h1 : ∀ j : Fin r, ((mkChain c cc).R (Fin.castAdd r j)).totalDegree ≤ 1 := by
    intro j
    rw [mkChain_R]
    simp only [chainR, Fin.addCases_left]
    rw [MvPolynomial.totalDegree_X]
  have h2 : ∀ j : Fin r, ((mkChain c cc).R (Fin.natAdd r j)).totalDegree ≤ 2 := by
    intro j
    simp only [mkChain_R, chainR, Fin.addCases_right]
    exact totalDegree_one_add_X_sq_le
  have h3 : (∑ j : Fin r, ((mkChain c cc).R (Fin.castAdd r j)).totalDegree) ≤ r * 1 := by
    refine le_trans (Finset.sum_le_sum fun j _ => h1 j) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h4 : (∑ j : Fin r, ((mkChain c cc).R (Fin.natAdd r j)).totalDegree) ≤ r * 2 := by
    refine le_trans (Finset.sum_le_sum fun j _ => h2 j) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  linarith

theorem sum_deg_le (c : EAChain k r) (cc e : Fin r → ℝ) (N N₀ F : ℕ) (f g : Fin k → EAPoly k r)
    (a b : ℝ) (hkF : k ≤ F) (hrF : r ≤ F) (hN : N ≤ N₀ + 1)
    (hf : ∀ i, (f i).totalDegree ≤ N₀) (hg : ∀ i, (g i).totalDegree ≤ N₀) :
    ∑ i : Fin (k + k), atomDeg (realSys c cc e N f g a b i)
      + ∑ j : Fin (r + r), ((mkChain c cc).R j).totalDegree
      ≤ 6 * F * (F + 1) * N₀ + (12 * F * F + 5 * F) := by
  have hb : 3 * r * (N + 1) ≤ 3 * F * (N₀ + 2) := by
    have h4 : N + 1 ≤ N₀ + 2 := by omega
    calc 3 * r * (N + 1) = 3 * (r * (N + 1)) := by ring
      _ ≤ 3 * (F * (N₀ + 2)) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hrF h4)
      _ = 3 * F * (N₀ + 2) := by ring
  have hper : ∀ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.castAdd k i))
      ≤ 3 * N₀ + 3 * F * (N₀ + 2) + 1 := by
    intro i
    have h1 : (realifyRe N e (f i)).totalDegree
        ≤ 3 * (f i).totalDegree + 3 * F * (N₀ + 2) :=
      le_trans (totalDegree_realify_le N e (f i)).1 (Nat.add_le_add_left hb _)
    have h2 : (realifyRe N e (g i)).totalDegree
        ≤ 3 * (g i).totalDegree + 3 * F * (N₀ + 2) :=
      le_trans (totalDegree_realify_le N e (g i)).1 (Nat.add_le_add_left hb _)
    have h3 : (realifyIm N e (g i)).totalDegree
        ≤ 3 * (g i).totalDegree + 3 * F * (N₀ + 2) :=
      le_trans (totalDegree_realify_le N e (g i)).2 (Nat.add_le_add_left hb _)
    have h1' : 3 * (f i).totalDegree ≤ 3 * N₀ := Nat.mul_le_mul_left 3 (hf i)
    have h2' : 3 * (g i).totalDegree ≤ 3 * N₀ := Nat.mul_le_mul_left 3 (hg i)
    have hA : (realifyRe N e (f i)).totalDegree ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by omega
    have hB : (MvPolynomial.C a * realifyRe N e (g i)).totalDegree
        ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      omega
    have hC : (MvPolynomial.C (-b) * realifyIm N e (g i)).totalDegree
        ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      omega
    have hsum : (realifyRe N e (f i) + MvPolynomial.C a * realifyRe N e (g i)
        + MvPolynomial.C (-b) * realifyIm N e (g i)).totalDegree
        ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by
      refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ hC)
      exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le hA hB)
    rw [realSys_castAdd]
    have heq : atomDeg (realifyRe N e (f i) + MvPolynomial.C a * realifyRe N e (g i)
        + MvPolynomial.C (-b) * realifyIm N e (g i))
        = (realifyRe N e (f i) + MvPolynomial.C a * realifyRe N e (g i)
          + MvPolynomial.C (-b) * realifyIm N e (g i)).totalDegree + 1 := rfl
    rw [heq]
    omega
  have hper' : ∀ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.natAdd k i))
      ≤ 3 * N₀ + 3 * F * (N₀ + 2) + 1 := by
    intro i
    have h1 : (realifyIm N e (f i)).totalDegree
        ≤ 3 * (f i).totalDegree + 3 * F * (N₀ + 2) :=
      le_trans (totalDegree_realify_le N e (f i)).2 (Nat.add_le_add_left hb _)
    have h2 : (realifyIm N e (g i)).totalDegree
        ≤ 3 * (g i).totalDegree + 3 * F * (N₀ + 2) :=
      le_trans (totalDegree_realify_le N e (g i)).2 (Nat.add_le_add_left hb _)
    have h3 : (realifyRe N e (g i)).totalDegree
        ≤ 3 * (g i).totalDegree + 3 * F * (N₀ + 2) :=
      le_trans (totalDegree_realify_le N e (g i)).1 (Nat.add_le_add_left hb _)
    have h1' : 3 * (f i).totalDegree ≤ 3 * N₀ := Nat.mul_le_mul_left 3 (hf i)
    have h2' : 3 * (g i).totalDegree ≤ 3 * N₀ := Nat.mul_le_mul_left 3 (hg i)
    have hA : (realifyIm N e (f i)).totalDegree ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by omega
    have hB : (MvPolynomial.C a * realifyIm N e (g i)).totalDegree
        ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      omega
    have hC : (MvPolynomial.C b * realifyRe N e (g i)).totalDegree
        ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      omega
    have hsum : (realifyIm N e (f i) + MvPolynomial.C a * realifyIm N e (g i)
        + MvPolynomial.C b * realifyRe N e (g i)).totalDegree
        ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by
      refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ hC)
      exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le hA hB)
    rw [realSys_natAdd]
    have heq : atomDeg (realifyIm N e (f i) + MvPolynomial.C a * realifyIm N e (g i)
        + MvPolynomial.C b * realifyRe N e (g i))
        = (realifyIm N e (f i) + MvPolynomial.C a * realifyIm N e (g i)
          + MvPolynomial.C b * realifyRe N e (g i)).totalDegree + 1 := rfl
    rw [heq]
    omega
  have hsumA : ∑ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.castAdd k i))
      ≤ k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) := by
    calc ∑ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.castAdd k i))
        ≤ ∑ _i : Fin k, (3 * N₀ + 3 * F * (N₀ + 2) + 1) :=
          Finset.sum_le_sum fun i _ => hper i
      _ = k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsumB : ∑ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.natAdd k i))
      ≤ k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) := by
    calc ∑ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.natAdd k i))
        ≤ ∑ _i : Fin k, (3 * N₀ + 3 * F * (N₀ + 2) + 1) :=
          Finset.sum_le_sum fun i _ => hper' i
      _ = k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsum : ∑ i : Fin (k + k), atomDeg (realSys c cc e N f g a b i)
      ≤ 2 * k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) := by
    rw [Fin.sum_univ_add]
    calc (∑ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.castAdd k i)))
          + (∑ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.natAdd k i)))
        ≤ k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) + k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) :=
          add_le_add hsumA hsumB
      _ = 2 * k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) := by ring
  have hR := totalDegree_R_le c cc
  have hk2 : 2 * k * (3 * N₀ + 3 * F * (N₀ + 2) + 1)
      ≤ 2 * F * (3 * N₀ + 3 * F * (N₀ + 2) + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hkF)
  have h3F : 3 * r ≤ 3 * F := Nat.mul_le_mul_left 3 hrF
  refine le_trans (add_le_add (le_trans hsum hk2) hR) ?_
  have harith : (2 * F * (3 * N₀ + 3 * F * (N₀ + 2) + 1) + 3 * F : ℝ)
      ≤ 6 * F * (F + 1) * N₀ + (12 * F * F + 5 * F) := by
    nlinarith
  have harith2 : 2 * F * (3 * N₀ + 3 * F * (N₀ + 2) + 1) + 3 * F
      ≤ 6 * F * (F + 1) * N₀ + (12 * F * F + 5 * F) := by
    exact_mod_cast harith
  exact le_trans (add_le_add le_rfl h3F) harith2

/-- **The realification step of area E3** (DESIGN §2 E3; `NOTES.md` §3, §5′): Gabrielov's
multiplicity bound for complexified EA systems, from Khovanskii's bound for separable chains.

Realify: `z = u + i v`, and for each chain function `j` put `y_j := e^{(Re ℓ_j) (z)}`,
`t_j := tan ((Im ℓ_j) (z) / 2)` (one `t_j` per *chain function* — this is what makes the
substitution work for arbitrary real coefficients, unlike a coordinate-wise `tan (v_i / 2)`, which
only rationalises integer multiples).  Then `e^{ℓ_j (z)} = y_j (1 + 2 i t_j - t_j²)/(1 + t_j²)`,
so multiplying each complexified equation by `Π_j (1 + t_j²)^{deg}` and taking real and imaginary
parts gives a system of `2k` real equations in the `2k` real variables `(u, v)` with the chain
`(y_j, t_j)`, which is an instance of `Work.WilE3.SepChainLocal` with `φ = Real.exp, R = X` and
`φ = Real.tan, R = 1 + X²` (since `∂y_j/∂u_i = a_{j i} y_j`, `∂t_j/∂v_i = a_{j i} (1 + t_j²)/2`,
all cross-derivatives vanishing, and `Real.tan` satisfies its relation on a `dom` avoiding the
poles).  At a common zero the clearing factor multiplies the Jacobian by the nonzero constant
`Π (1 + t_j²)^{deg}`, and the substitution `v ↦ t` is a local diffeomorphism, so nondegenerate
complex zeros correspond exactly to nondegenerate real zeros of the realified system
(`det_ℝ = |det_ℂ|²` up to the substitution's Jacobian).  The chart `|Im ℓ_j (z)| < π` is periodic
with period `2π`; shifting `b_j` by a multiple of `2π` per `j` covers the finitely many charts a
shrinking ball meets, so Khovanskii's separable-chain bound (`hK`) applies on each and the degrees
of the realified equations are `O (deg)` with constants depending only on `k + r`, `deg R_j ≤ 2`. -/
theorem MultiplicityBound_proved (hK : ∀ F : ℕ, Work.WilE3.SepKhovanskiiLocal F) :
    Work.WilE3.MultiplicityBound := by
  intro F
  obtain ⟨p, hp⟩ := hK (2 * F)
  refine ⟨p.comp (Polynomial.C (6 * F * (F + 1) + 1) * Polynomial.X
      + Polynomial.C (12 * F * F + 5 * F + 1)), ?_⟩
  intro k r c f g x ρ hkr hfx hρpos hρtend
  set N₀ : ℕ := ∑ i, atomDeg (f i) + ∑ i, atomDeg (g i) with hN₀
  set N : ℕ := N₀ + 1 with hN
  -- the chart choice
  have hchart : ∀ j : Fin r, ∃ (cc e : ℝ), (∃ n : ℤ, cc = n * Real.pi) ∧ e = Real.cos cc ∧
      |(∑ i, c.a j i * (x i).im) - cc| ≤ Real.pi / 2 ∧
      (∀ w : ℝ, |w - (∑ i, c.a j i * (x i).im)| < Real.pi / 2 →
        Real.cos ((w - cc) / 2) ≠ 0) ∧
      ((e : ℂ) = Complex.exp ((cc : ℂ) * Complex.I)) :=
    fun j => exists_chart_offset _
  choose cc e hcc hee hβ hccdom hec using hchart
  set A : ℝ := ∑ j : Fin r, ∑ i : Fin k, |c.a j i| with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hρsmall : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ρ ε < Real.pi / (8 * (A + 1)) := by
    have hc : 0 < Real.pi / (8 * (A + 1)) := by positivity
    filter_upwards [hρtend.eventually (Metric.ball_mem_nhds (0 : ℝ) hc)] with ε hε
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (hρpos ε)] at hε
    exact hε
  filter_upwards [hρsmall] with ε hρε
  intro s hs hsz
  -- the perturbation is `ε = a + i b`
  set a : ℝ := ε.re with ha
  set b : ℝ := ε.im with hb
  have heps : eps a b = ε := by
    rw [ha, hb, eps]
    exact Complex.re_add_im ε
  -- the total-degree bound for the perturbed system
  have hftd : ∀ i, (f i).totalDegree ≤ N₀ := by
    intro i
    refine le_trans (Nat.le_succ _) ?_
    rw [hN₀]
    exact le_trans (Finset.single_le_sum (f := fun i => atomDeg (f i))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_right _ _)
  have hgtd : ∀ i, (g i).totalDegree ≤ N₀ := by
    intro i
    refine le_trans (Nat.le_succ _) ?_
    rw [hN₀]
    exact le_trans (Finset.single_le_sum (f := fun i => atomDeg (g i))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left _ _)
  have hdeg := sum_deg_le c cc e N N₀ F f g a b (by omega) (by omega)
    (le_of_eq hN) hftd hgtd
  -- the ball and the chart estimates
  have hρpos' : 0 < ρ ε := hρpos ε
  have hR0 : 0 ≤ ρ ε := le_of_lt hρpos'
  have hsmall2 : 2 * ρ ε * A < Real.pi / 2 := by
    rcases eq_or_lt_of_le hA0 with h0 | h0
    · rw [← h0, mul_zero]
      linarith [Real.pi_pos]
    · have h4 : 2 * ρ ε * A < 2 * (Real.pi / (8 * (A + 1))) * A :=
        mul_lt_mul_of_pos_right (by linarith) h0
      have h5 : 2 * (Real.pi / (8 * (A + 1))) * A = Real.pi * A / (4 * (A + 1)) := by
        field_simp; ring
      rw [h5] at h4
      have h6 : Real.pi * A / (4 * (A + 1)) ≤ Real.pi / 2 := by
        have h7 : Real.pi / 2 - Real.pi * A / (4 * (A + 1))
            = Real.pi * (2 * (A + 1) - A) / (4 * (A + 1)) := by
          field_simp
          ring
        have h8 : 0 ≤ Real.pi * (2 * (A + 1) - A) / (4 * (A + 1)) :=
          div_nonneg (by nlinarith [Real.pi_pos]) (by linarith)
        linarith
      linarith
  have hvclose : ∀ {w : Fin (k + k) → ℝ}, dist w (cplxPt x) < 2 * ρ ε →
      ∀ i, |(vOf w) i - (x i).im| < 2 * ρ ε := by
    intro w hw i
    have h1 : (cplxPt x) (Fin.natAdd k i) = (x i).im := by
      simp only [cplxPt, mkPt_apply_natAdd]
    have h2 : |(vOf w) i - (x i).im| = dist (w (Fin.natAdd k i)) ((cplxPt x) (Fin.natAdd k i)) := by
      rw [Real.dist_eq, h1]
      simp only [vOf]
    rw [h2]
    exact lt_of_le_of_lt (dist_le_pi_dist w (cplxPt x) (Fin.natAdd k i)) hw
  -- membership in the ball
  have hsub : ∀ z ∈ s, cplxPt z ∈ Metric.ball (cplxPt x) (2 * ρ ε) := by
    intro z hz
    rw [Metric.mem_ball]
    have h1 := dist_cplxPt_le z x
    have h2 := hsz z hz
    linarith
  -- the domain condition on the ball
  have hdomD : ∀ w ∈ Metric.ball (cplxPt x) (2 * ρ ε),
      ∀ j, (∑ i, (mkChain c cc).a j i * w i) + (mkChain c cc).b j ∈ (mkChain c cc).dom j := by
    intro w hw j
    revert j
    refine Fin.addCases (motive := fun j => (∑ i, (mkChain c cc).a j i * w i)
        + (mkChain c cc).b j ∈ (mkChain c cc).dom j) ?_ ?_
    · intro j
      rw [mkChain_dom_castAdd]
      exact Set.mem_univ _
    · intro j
      rw [mkChain_dom_natAdd, mkChain_arg_natAdd', Set.mem_ofPred_eq]
      exact chart_hcos c cc x hccdom hR0 hsmall2 (hvclose (Metric.mem_ball.mp hw)) j
  -- the nondegeneracy
  have hnd : ∀ w ∈ s.image (cplxPt (k := k)),
      (mkChain c cc).Nondegen (realSys c cc e N f g a b) w := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
    obtain ⟨hz0, hzd⟩ := hs z hz
    have hcosz : ∀ j, Real.cos ((∑ i, c.a j i * (z i).im - cc j) / 2) ≠ 0 := by
      intro j
      simpa [vOf_cplxPt] using
        chart_hcos c cc x hccdom hR0 hsmall2 (hvclose (Metric.mem_ball.mp (hsub z hz))) j
    refine nondegen_of_cplx c cc e hec N f g a b z hcosz ?_ ?_ ?_ ?_
    · intro i
      exact le_trans (hftd i) (le_of_eq hN.symm |>.trans' (Nat.le_succ N₀))
    · intro i
      exact le_trans (hgtd i) (le_of_eq hN.symm |>.trans' (Nat.le_succ N₀))
    · intro i
      rw [heps]
      exact hz0 i
    · have hmeq : (Matrix.of fun i j => eaEvalC c (eaD c j (f i)) z
            + eps a b * eaEvalC c (eaD c j (g i)) z)
          = Matrix.of fun i j => eaEvalC c (eaD c j (f i)) z
            + ε * eaEvalC c (eaD c j (g i)) z := by
        ext i j
        simp only [Matrix.of_apply]
        rw [heps]
      rw [hmeq]
      exact hzd
  -- Khovanskii's bound
  have hle := hp (k + k) (r + r) (mkChain c cc)
    (realSys c cc e N f g a b)
    (Metric.ball (cplxPt x) (2 * ρ ε)) (s.image (cplxPt (k := k))) (by omega)
    Metric.isBounded_ball hdomD
    (fun w hw => by
      rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
      exact hsub z hz) hnd
  -- the conclusion
  calc s.card
      = (s.image (cplxPt (k := k))).card := (Finset.card_image_of_injective s cplxPt_injective).symm
    _ ≤ p.eval (∑ i, atomDeg (realSys c cc e N f g a b i)
          + ∑ j, ((mkChain c cc).R j).totalDegree) := hle
    _ ≤ p.eval (6 * F * (F + 1) * N₀ + (12 * F * F + 5 * F)) := eval_mono_nat p hdeg
    _ ≤ (p.comp (Polynomial.C (6 * F * (F + 1) + 1) * Polynomial.X
          + Polynomial.C (12 * F * F + 5 * F + 1))).eval N₀ := by
        rw [Polynomial.eval_comp]
        refine eval_mono_nat p ?_
        rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_C]
        nlinarith

end

end Work.WilE3.Realify
