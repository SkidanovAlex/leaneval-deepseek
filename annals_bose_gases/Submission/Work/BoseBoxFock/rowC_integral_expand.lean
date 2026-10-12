import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.Middle_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.rowC_integral_expand` — the box Fourier transform of the `(s,k)`-double frame

The row (c) of the cubic dictionary (`Submission/Work/BoseBoxFock/Middle_row_c.lean`) produces the
localised integral

    `ℓ^{-3} ∫_w χ_Λ(w) Ksfr(x+w) Kfr(u+w)`

of the product of the two honest frames `Ksfr` and `Kfr`.  This module evaluates it: expanding the
two *finite* lattice sums (`Work.BoseB7.excited (Lab N)`) and using the box Fourier transform of
the window (`Work.BoseBoxFock.integral_chiLam_exp`, together with the evenness of `χ_Λ`) one gets

    `ℓ^{-3} ∫_w χ_Λ(w) Ksfr(x+w) Kfr(u+w)
       = Σ_{s,k} f_L(s)Ŵ₁(k) χ̂(ℓ(s+k)) e^{i⟨s,x⟩} e^{i⟨k,u⟩}`,

which is exactly the `(s,k)`-sum of the dictionary.  The content is
* the integral/sum exchange (`integral_finset_sum`) and the integrability of each summand
  (`χ_Λ` is continuous with compact support, the plane waves are bounded);
* the pointwise factorisation `e^{i⟨p,x+w⟩} = e^{i⟨p,x⟩}e^{i⟨p,w⟩}`;
* the (positive-sign) Fourier integral `∫_w χ_Λ(w)e^{i⟨p,w⟩} = ℓ³χ̂(ℓp)`.

Everything here is `sorry`-free and axiom-clean.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## The elementary pieces -/

/-- `a · (Σ_{i∈s} F i) · (Σ_{j∈t} G j) = Σ_{i∈s} Σ_{j∈t} a·F i·G j` — the (re)association step
used to expand the integrand into the `(s,k)`-double sum. -/
lemma rowC_mul_sum_mul_sum {ι M : Type*} [CommSemiring M] (a : M) (s t : Finset ι) (F G : ι → M) :
    a * (∑ i ∈ s, F i) * (∑ j ∈ t, G j) = ∑ i ∈ s, ∑ j ∈ t, a * F i * G j := by
  rw [show a * (∑ i ∈ s, F i) = ∑ i ∈ s, a * F i from Finset.mul_sum s F a]
  rw [Finset.sum_mul_sum]

/-- **The (positive-sign) Fourier transform of the window.**  `∫ χ_Λ e^{i⟨p,·⟩} = ℓ³χ̂(ℓp)`:
`integral_chiLam_exp` (the conjugate sign) with the substitution `w ↦ -w`, which is legitimate
because `χ_Λ` is even. -/
lemma rowC_integral_chiLam_exp_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Ω) :
    ∫ w, ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * Complex.exp (Complex.I * (inner ℝ p w : ℂ))
      = ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ) := by
  set f : Ω → ℂ := fun w => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
    * Complex.exp (Complex.I * (inner ℝ p w : ℂ)) with hf
  have hneg : ∫ w, f (-w) = ∫ w, f w :=
    (Measure.measurePreserving_neg (volume : Measure Ω)).integral_comp measurableEmbedding_neg f
  have hfneg : (fun w => f (-w)) = fun w => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
      * Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))) := by
    funext w
    simp only [hf]
    rw [Work.BoseB4.BoxData.chiLam_even, inner_neg_right]
    congr 1
    push_cast
    ring_nf
  rw [hfneg] at hneg
  rw [← hneg]
  have h2 : ∫ w, ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ p w : ℂ)))
      = ∫ w, Complex.exp (-(Complex.I * (inner ℝ p w : ℂ)))
        * ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards with w
    rw [mul_comm]
  rw [h2, Work.BoseBoxFock.integral_chiLam_exp hℓ p]

/-- **The two-plane-wave window integral.**  The `w`-integral of `χ_Λ` against the two shifted
plane waves `e^{i⟨p,x+·⟩}`, `e^{i⟨q,u+·⟩}` factorises into the two phases at `x`, `u` times the
Fourier transform at `p+q`. -/
lemma rowC_integral_chiLam_exp_pair {ℓ : ℝ} (hℓ : 0 < ℓ) (p q : Ω) (x u : Ω) :
    ∫ w, ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ p (x + w) : ℂ))
        * Complex.exp (Complex.I * (inner ℝ q (u + w) : ℂ))
      = ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • (p + q)) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ p x : ℂ))
        * Complex.exp (Complex.I * (inner ℝ q u : ℂ)) := by
  set c : ℂ := Complex.exp (Complex.I * (inner ℝ p x : ℂ))
    * Complex.exp (Complex.I * (inner ℝ q u : ℂ)) with hc
  set g : Ω → ℂ := fun w => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
    * Complex.exp (Complex.I * (inner ℝ p w : ℂ))
    * Complex.exp (Complex.I * (inner ℝ q w : ℂ)) with hg
  have hAcongr : (fun w => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ p (x + w) : ℂ))
        * Complex.exp (Complex.I * (inner ℝ q (u + w) : ℂ))) =ᵐ[volume] fun w => c * g w := by
    filter_upwards with w
    simp only [hc, hg]
    simp only [inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  rw [integral_congr_ae hAcongr, integral_const_mul]
  have hgval : ∫ w, g w
      = ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • (p + q)) : ℝ) : ℂ) := by
    refine Eq.trans ?_ (rowC_integral_chiLam_exp_pos hℓ (p + q))
    refine integral_congr_ae ?_
    filter_upwards with w
    simp only [hg]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    rw [inner_add_left]
    push_cast
    ring_nf
  rw [hgval, hc]
  ring_nf

/-- Integrability of the (unfactored) summand of the `(s,k)`-expansion: `χ_Λ` is continuous with
compact support and the plane waves are bounded (norm `1`). -/
lemma rowC_integrable_chiLam_exp_pair {ℓ : ℝ} (hℓ : 0 < ℓ) (p q : Ω) (x u : Ω) :
    Integrable fun w : Ω => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ p (x + w) : ℂ))
      * Complex.exp (Complex.I * (inner ℝ q (u + w) : ℂ)) := by
  have hsupp : Function.support (fun w : Ω => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ))
      ⊆ Function.support (Work.BoseK15.corpusBox.chiLam ℓ) :=
    Function.support_comp_subset (g := (Complex.ofReal : ℝ → ℂ)) (by simp) _
  have hcs1 : HasCompactSupport fun w : Ω => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) :=
    (Work.BoseB4.BoxData.boxL_compact _ ℓ).of_isClosed_subset (isClosed_tsupport _)
      ((closure_mono hsupp).trans (Work.BoseB4.BoxData.tsupport_chiLam_subset _ hℓ))
  have hcont : Continuous fun w : Ω => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ p (x + w) : ℂ))
      * Complex.exp (Complex.I * (inner ℝ q (u + w) : ℂ)) :=
    (Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ ℓ)).mul
      (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp
          ((continuous_const : Continuous fun _ : Ω => p).inner
            (continuous_const.add continuous_id)))))
    |>.mul
      (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp
          ((continuous_const : Continuous fun _ : Ω => q).inner
            (continuous_const.add continuous_id)))))
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.mul_right (HasCompactSupport.mul_right hcs1))

/-! ## The row (c) integral -/

theorem rowC_integral_expand (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x u : EuclideanSpace ℝ (Fin 3)) :
    ((Work.BoseBoxFock.ellH v μ ^ 3 : ℝ) : ℂ)⁻¹
        * ∫ w, ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
            * Work.BoseBoxFock.Ksfr v fc μ N (x + w)
            * Work.BoseBoxFock.Kfr v h μ fu N (u + w)
      = ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
          ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
            ((Work.BoseBoxFock.fLh v fc μ N s * Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)
              * ((Work.BoseK15.corpusBox.hatChi
                    ((Work.BoseBoxFock.ellH v μ) • (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s
                      + Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)) : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s) x : ℂ))
              * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) u : ℂ)) := by
  have hℓ : (0 : ℝ) < ellH v μ := ellH_pos v μ
  have hℓ3 : ((ellH v μ ^ 3 : ℝ) : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact pow_ne_zero _ (ne_of_gt hℓ)
  -- integrability of one summand of the `(s,k)`-double sum
  have hTerm_int : ∀ s k : Lab N, Integrable fun w : Ω =>
        ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * (((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x + w) : ℂ)))
        * (((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (u + w) : ℂ))) := by
    intro s k
    have hbase := rowC_integrable_chiLam_exp_pair hℓ
      (kmomLab (ellH v μ) N s) (kmomLab (ellH v μ) N k) x u
    refine (hbase.const_mul (((fLh v fc μ N s : ℝ) : ℂ)
      * ((W1h v h μ fu N k : ℝ) : ℂ))).congr ?_
    filter_upwards with w
    ring
  -- the pointwise expansion of the integrand into the `(s,k)`-double sum
  have hExpand : (fun w : Ω => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * Kfr v h μ fu N (u + w))
      = fun w : Ω => ∑ s ∈ Work.BoseB7.excited (Lab N),
          ∑ k ∈ Work.BoseB7.excited (Lab N),
          ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * (((fLh v fc μ N s : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x + w) : ℂ)))
          * (((W1h v h μ fu N k : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (u + w) : ℂ))) := by
    funext w
    rw [Ksfr, Kfr]
    exact rowC_mul_sum_mul_sum _ _ _ _ _
  rw [hExpand]
  -- integral/sum exchanges (twice) and the pull-out of the `ℓ^{-3}` normalisation
  rw [integral_finset_sum _ (fun s _ => integrable_finset_sum _ (fun k _ => hTerm_int s k))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_finset_sum _ (fun k _ => hTerm_int s k)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- the value of one summand integral
  have hval : ∫ w, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * (((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x + w) : ℂ)))
        * (((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (u + w) : ℂ)))
      = ((ellH v μ ^ 3 : ℝ) : ℂ) * (((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi
              ((ellH v μ) • (kmomLab (ellH v μ) N s + kmomLab (ellH v μ) N k)) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) u : ℂ))) := by
    rw [show (fun w : Ω => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * (((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x + w) : ℂ)))
        * (((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (u + w) : ℂ))))
      = (fun w : Ω => (((fLh v fc μ N s : ℝ) : ℂ) * ((W1h v h μ fu N k : ℝ) : ℂ))
        * (((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x + w) : ℂ))
        * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (u + w) : ℂ))))
      from funext (fun w => by ring)]
    rw [integral_const_mul, rowC_integral_chiLam_exp_pair hℓ _ _ x u]
    push_cast
    ring
  rw [hval, ← mul_assoc, inv_mul_cancel₀ hℓ3, one_mul]

end Work.BoseBoxFock
