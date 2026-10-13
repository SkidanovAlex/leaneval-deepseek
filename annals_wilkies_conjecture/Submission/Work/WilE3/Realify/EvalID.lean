/-
  annals_wilkies_conjecture, AREA E3, `Realify` (evaluation identity).

  `eval_realifyRe` / `eval_realifyIm`: on the chart (where `cos ((ℓ_j x - cc_j)/2) ≠ 0`), the
  evaluated realified system is `Wval^N` times the real (resp. imaginary) part of the
  complexified system,

    `(mkChain c cc).ev (realifyRe N e P) (u,v) = Wval^N · (eaEvalC c P (u + i v)).re`.

  Since `Wval > 0`, this identifies both the zero sets and (via the product rule) the Jacobians
  of the two systems.
-/
import Submission.Work.WilE3.Realify.EvalMain
import Submission.Work.WilE3.Realify.eval_rePoly_imPoly
import Submission.Work.WilE3.Realify.eval_monoNum

namespace Work.WilE3.Realify

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

variable {k r : ℕ}

/-- The value of the complexified monomial `m` at `(u, v)`: `∏ᵢ zᵢ^{mᵢ} · ∏ⱼ (e^{ℓⱼ})^{mⱼ}`. -/
def cmval (c : EAChain k r) (u v : Fin k → ℝ) (m : (Fin k ⊕ Fin r) →₀ ℕ) : ℂ :=
  (∏ i : Fin k, ((u i : ℂ) + (v i : ℂ) * Complex.I) ^ (m (Sum.inl i)))
    * (∏ j : Fin r, (Complex.exp (∑ i, (c.a j i : ℂ) *
        ((u i : ℂ) + (v i : ℂ) * Complex.I) + (c.b j : ℂ))) ^ (m (Sum.inr j)))

theorem eval_rePoly_eq (gR : Sig k r → ℝ) (q : MvPolynomial (Sig k r) ℂ) :
    MvPolynomial.eval gR (rePoly q)
      = (MvPolynomial.eval (fun s => (gR s : ℂ)) q).re := by
  have h := congrArg Complex.re (eval_rePoly_imPoly gR q)
  simpa [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using h.symm

theorem eval_imPoly_eq (gR : Sig k r → ℝ) (q : MvPolynomial (Sig k r) ℂ) :
    MvPolynomial.eval gR (imPoly q)
      = (MvPolynomial.eval (fun s => (gR s : ℂ)) q).im := by
  have h := congrArg Complex.im (eval_rePoly_imPoly gR q)
  simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using h.symm

/-- The clearing exponent `N` only has to dominate the `t`-exponents, which are bounded by the
total degree. -/
theorem exponent_le_of_totalDegree_le {P : EAPoly k r} {N : ℕ} (hN : P.totalDegree ≤ N)
    {m : (Fin k ⊕ Fin r) →₀ ℕ} (hm : m ∈ P.support) (j : Fin r) :
    m (Sum.inr j) ≤ N := by
  have h1 : m (Sum.inr j) ≤ m.sum (fun _ e => e) := by
    rw [Finsupp.sum]
    by_cases h : m (Sum.inr j) = 0
    · simp [h]
    · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr h)
  exact le_trans h1 (le_trans (MvPolynomial.le_totalDegree hm) hN)

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

theorem sum_coeff_cmval (c : EAChain k r) (P : EAPoly k r) (u v : Fin k → ℝ) :
    (∑ m ∈ P.support, (P.coeff m : ℂ) * cmval c u v m)
      = eaEvalC c P (zOf (mkPt u v)) := by
  conv_rhs => rw [eaEvalC, MvPolynomial.eval₂_eq']
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.coe_algebraMap]
  congr 1
  rw [Fintype.prod_sum_type, zOf_mkPt]
  rfl

theorem sum_re_eq (f : ((Fin k ⊕ Fin r) →₀ ℕ) → ℂ)
    (s : Finset ((Fin k ⊕ Fin r) →₀ ℕ)) :
    (∑ m ∈ s, f m).re = ∑ m ∈ s, (f m).re := by
  rw [← Complex.reCLM_apply, map_sum Complex.reCLM]
  exact Finset.sum_congr rfl fun m _ => Complex.reCLM_apply (f m)

theorem sum_im_eq (f : ((Fin k ⊕ Fin r) →₀ ℕ) → ℂ)
    (s : Finset ((Fin k ⊕ Fin r) →₀ ℕ)) :
    (∑ m ∈ s, f m).im = ∑ m ∈ s, (f m).im := by
  rw [← Complex.imCLM_apply, map_sum Complex.imCLM]
  exact Finset.sum_congr rfl fun m _ => Complex.imCLM_apply (f m)

theorem real_mul_re (a : ℝ) (z : ℂ) : ((a : ℂ) * z).re = a * z.re := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem real_mul_im (a : ℝ) (z : ℂ) : ((a : ℂ) * z).im = a * z.im := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- **The evaluation identity of the realification (real part).** -/
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

/-- **The evaluation identity of the realification (imaginary part).** -/
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

end

end Work.WilE3.Realify
