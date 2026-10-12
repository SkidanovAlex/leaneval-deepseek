import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.rowC_integral_expand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Middle_row_c_hold` — the `(c)`-channel of `Middle`

This is the `(c)`-channel of the four-channel split of the cubic row's middle kernel `Middle`
(FS's `qVec`-correction; see `FINDING_Middle_expansion_FALSE.md` §2, where the channel is called
`C`):

`Σ_{s,k} f_L(s)Ŵ₁(k)·χ̂(ℓκ_{s−k})·θ(y)·e^{i⟪κ_s,x⟫}θ(x)·e^{−i⟪κ_k,u⟫}χ_Λ(u)`
`  = θ(y)θ(x)χ_Λ(u)·ℓ^{-3}∫_w χ_Λ(w)·Ksfr(x+w)·Kfr(u+w)dw`.

The proof has three parts:

* `rowC_parity` — the purely combinatorial reindexing `k ↦ −k` of the double sum, which uses the
  guarded additivity `κ_{s−k} = κ_s − κ_k` (`hsub`), the evenness of `W₁` and `χ̂` and
  `κ_{−k} = −κ_k`.  It turns the `(c)`-channel sum into the `+`-combination `κ_s + κ_k`;
* `rowC_integral_expand` (module `Submission.Work.BoseBoxFock.rowC_integral_expand`) — the
  analytic expansion of the integral `ℓ^{-3}∫_w χ_Λ(w)Ksfr(x+w)Kfr(u+w)dw` into the `+`-form
  double sum, via the box Fourier transform `∫χ_Λ e^{i⟪p,·⟫} = ℓ³χ̂(ℓp)`;
* the assembly in `Middle_row_c_hold`, where the common constant `θ(y)θ(x)χ_Λ(u)` is factored out
  of the summands and the two `ℓ`-bookkeepings are matched (`ellH_zpow_neg_three`).

Everything here is `sorry`-free and axiom-clean.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

variable {v : Ω → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}

/-- **The counting identity at the `+`-pair.**  The `hsub`-hypothesis (the guarded additivity of
`kmomLab` on the supports of `f_L` and `Ŵ₁`) applied to the pair `(s, −k)`: on the supports,
`κ_{s+k} = κ_s + κ_k`. -/
lemma kmomLab_add_of_sub
    (hsub : ∀ s ∈ Work.BoseB7.excited (Lab N), fLh v fc μ N s ≠ 0 →
      ∀ k ∈ Work.BoseB7.excited (Lab N), W1h v h μ fu N k ≠ 0 →
      kmomLab (ellH v μ) N (s - k) = kmomLab (ellH v μ) N s - kmomLab (ellH v μ) N k)
    {s k : Lab N} (hs : s ∈ Work.BoseB7.excited (Lab N)) (hs0 : fLh v fc μ N s ≠ 0)
    (hk : k ∈ Work.BoseB7.excited (Lab N)) (hk0 : W1h v h μ fu N k ≠ 0) :
    kmomLab (ellH v μ) N (s + k) = kmomLab (ellH v μ) N s + kmomLab (ellH v μ) N k := by
  have hk0' : W1h v h μ fu N (-k) ≠ 0 := by
    rwa [W1h_neg (v := v) (h := h) (μ := μ) (fu := fu) k]
  have h1 := hsub s hs hs0 (-k) (neg_mem_excited hk) hk0'
  rwa [sub_neg_eq_add, kmomLab_neg, sub_neg_eq_add] at h1

/-- **The `k ↦ −k` reindexing of the `(c)`-channel.**  With `hsub`, the evenness of `Ŵ₁`
(`W1h_neg`), of `χ̂` (`hatChi_neg`) and `κ_{−k} = −κ_k` (`kmomLab_neg`), the `(c)`-channel double
sum can be written with the `+`-combination `κ_s + κ_k` of the momenta and two `+`-phases. -/
lemma rowC_parity (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x u : Ω)
    (hsub : ∀ s ∈ Work.BoseB7.excited (Lab N), fLh v fc μ N s ≠ 0 →
      ∀ k ∈ Work.BoseB7.excited (Lab N), W1h v h μ fu N k ≠ 0 →
      kmomLab (ellH v μ) N (s - k) = kmomLab (ellH v μ) N s - kmomLab (ellH v μ) N k) :
    (∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N (s - k)) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
          * Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) u : ℂ))))
      = (∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi
                ((ellH v μ) • (kmomLab (ellH v μ) N s + kmomLab (ellH v μ) N k)) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) u : ℂ))) := by
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← sum_neg_excited (fun k => ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N (s - k)) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
        * Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) u : ℂ))))]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [W1h_neg (v := v) (h := h) (μ := μ) (fu := fu) k]
  by_cases hw : ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) = 0
  · rw [hw]
    ring
  · have hmul : fLh v fc μ N s * W1h v h μ fu N k ≠ 0 := by simpa using hw
    have hs0 : fLh v fc μ N s ≠ 0 := fun hh => hmul (by rw [hh, zero_mul])
    have hk0 : W1h v h μ fu N k ≠ 0 := fun hh => hmul (by rw [hh, mul_zero])
    simp only [sub_neg_eq_add]
    rw [kmomLab_add_of_sub (v := v) (h := h) (fc := fc) (fu := fu) (μ := μ) (N := N) hsub
      hs hs0 hk hk0]
    rw [show Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N (-k)) u : ℂ)))
          = Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) u : ℂ)) from by
      rw [kmomLab_neg, inner_neg_left]
      congr 1
      push_cast
      ring]

theorem Middle_row_c_hold (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x y u : EuclideanSpace ℝ (Fin 3))
    (hsub : ∀ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      Work.BoseBoxFock.fLh v fc μ N s ≠ 0 →
      ∀ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        Work.BoseBoxFock.W1h v h μ fu N k ≠ 0 →
      Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N (s - k)
        = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s
          - Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) :
    (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        ((Work.BoseBoxFock.fLh v fc μ N s * Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.hatChi ((Work.BoseBoxFock.ellH v μ) •
                  Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N (s - k)) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
              * (Complex.exp (Complex.I * (inner ℝ
                    (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s) x : ℂ))
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x)
              * (Complex.exp (-(Complex.I * (inner ℝ
                    (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) u : ℂ)))
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ))))
      = Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ)
          * (((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
          * ∫ w : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
              * Work.BoseBoxFock.Ksfr v fc μ N (x + w)
              * Work.BoseBoxFock.Kfr v h μ fu N (u + w) := by
  have hpar := rowC_parity v h fc fu μ N x u hsub
  have hcrux := rowC_integral_expand v h fc fu μ N x u
  have hstep1 :
      (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
          ((Work.BoseBoxFock.fLh v fc μ N s * Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.hatChi ((Work.BoseBoxFock.ellH v μ) •
                    Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N (s - k)) : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
                * (Complex.exp (Complex.I * (inner ℝ
                      (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s) x : ℂ))
                  * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x)
                * (Complex.exp (-(Complex.I * (inner ℝ
                      (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) u : ℂ)))
                  * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ))))
        = Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
            * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ)
            * (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
                ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
                  ((Work.BoseBoxFock.fLh v fc μ N s * Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)
                    * ((Work.BoseK15.corpusBox.hatChi ((Work.BoseBoxFock.ellH v μ) •
                        Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N (s - k)) : ℝ) : ℂ)
                    * Complex.exp (Complex.I * (inner ℝ
                        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s) x : ℂ))
                    * Complex.exp (-(Complex.I * (inner ℝ
                        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) u : ℂ)))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hstep2 :
      Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ)
          * (((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
          * ∫ w : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
              * Work.BoseBoxFock.Ksfr v fc μ N (x + w)
              * Work.BoseBoxFock.Kfr v h μ fu N (u + w)
        = Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
            * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ)
            * (((Work.BoseBoxFock.ellH v μ ^ 3 : ℝ) : ℂ)⁻¹
              * ∫ w, ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                  * Work.BoseBoxFock.Ksfr v fc μ N (x + w)
                  * Work.BoseBoxFock.Kfr v h μ fu N (u + w)) := by
    rw [ellH_zpow_neg_three]
    ring
  rw [hstep1, hstep2, hpar, ← hcrux]

end Work.BoseBoxFock
