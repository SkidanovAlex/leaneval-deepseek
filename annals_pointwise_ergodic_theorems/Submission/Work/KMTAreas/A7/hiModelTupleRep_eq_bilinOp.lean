import Mathlib
import Submission.Work.KMTAreas.A7.RepFibre
import Submission.Work.KMTAreas.A7.hiKer_varphiNt_spec
import Submission.Work.KMTAreas.A7.hiKer_varphitildeNt_spec
import Submission.Work.KMTAreas.A7.FiberGeneral
import Submission.Work.KMTPlan.A6.bilinOp_intervalIntegral

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-!
# `modelTupleRep` is the bilinear convolution with the repaired §6 model kernel `hiKmodNRep`

`modelTupleRep` (`Large/Defs.lean`) is the *repaired* §6 model tuple: the same `t`-integral
`∫_{1/2}^1 BtwistExact (T_{φ_{N,t}}^{l₁} f) (T_{φ̃_{N,t}}^{l₂} g) dt` as `modelTuple`, but with the
model symbol's band `uRep ρ l₁ l₂ k₁ k₂ = max (uScale ρ L) (max l₁ l₂ + 3)` (`L = max (max l₁ l₂)
(max k₁ k₂)`) in place of the paper's `uScale ρ L`, and with the band condition `bandCond` added to
its guard (off the band the model is `0`).

`hiKmodNRep ρ P N l₁ l₂ k₁ k₂` (`RepDefs.lean`) is the corresponding kernel: the `t`-integral of the
composition of the twisted kernel `hiTwKernel` at the window `uRep` with the two exact-height
kernels `hiKer ρ lᵢ (·)` of the modulated bumps.

The identity
`modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = bilinOp (hiKmodNRep ρ P ⌊a n⌋ l₁ l₂ k₁ k₂) f g x`
is then the *same* Fubini interchange as for `modelTuple` (`hiModelTuple_eq_bilinOp`), with the
window `uRep` throughout:

* for each `t`, the functional calculus `B_K(T_κ h, T_κ' k) = B_{kernComp K κ κ'}(h,k)`
  (`Work.A7.ModelApproxCore_kernelComp`) rewrites `BtwistExact` applied to the two projections into a
  bilinear convolution with the composed kernel, using `Tex_eq_convOp_hiKer ρ hl₁`, `ρ hl₂` (this is
  where `1 ≤ l₁`, `1 ≤ l₂` are used) and `BtwistExact_eq_bilinOp_hiTw` (definitional);
* the `t`-integral of that bilinear convolution is the bilinear convolution with the `t`-integral of
  the kernel (`Work.KMTPlan.A6.bilinOp_intervalIntegral`, two applications of `integral_tsum`).

The analytic inputs are exactly those of `Work.KMTAreas.A7.{hiTwKernel_summable,
hiKer_varphiNt_spec, hiKer_varphitildeNt_spec}`: absolute summability of the twisted kernel, and for
each of the two `t`-families `hiKer ρ l (φ_{N,t})`, `hiKer ρ l (φ̃_{N,t})` summability in `j`, a
uniform `ℓ¹`-bound on `(1/2,1]`, and measurability of each coefficient.  None of them refers to the
window parameter, so they apply verbatim at `uRep`.  The hypotheses `hcore` and `hband` serve only to
evaluate the guard of `modelTupleRep`.
-/


/-- **The twisted bilinear kernel at an arbitrary window is absolutely summable**: it is the
product of the bounded exact-height arithmetic kernel with the two absolutely summable coefficient
sequences `cw m_*`, `cw m̃_*`.  (The public statement `Work.KMTAreas.A7.hiTwKernel_summable` lives
in a module that does not currently compile, so it is reproduced here; it is independent of the
window parameter and hence applies verbatim at `uRep`.) -/
private theorem hiTwKernel_summable_rep (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u : ℕ) :
    Summable fun p : ℤ × ℤ => ‖Work.KMTAreas.A7.hiTwKernel ρ P l₁ l₂
      (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u) p.1 p.2‖ := by
  have hb : ∀ j₁ j₂ : ℤ,
      ‖arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖
        ≤ ((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ) := by
    intro j₁ j₂
    rw [← arithKernelSet_iwArithFreqsNew]
    exact norm_arithKernelSet_le P (arithQ ρ (max l₁ l₂)) _ _ j₁ j₂
  have h₁ : Summable fun j : ℤ => ‖cw (mStarF u) j‖ := summable_cw_mStarF u
  have h₂ : Summable fun j : ℤ => ‖cw (mStargF P.natDegree u) j‖ :=
    summable_cw_mStargF P.natDegree u
  have hprod : Summable fun p : ℤ × ℤ =>
      ‖cw (mStarF u) p.1‖ * ‖cw (mStargF P.natDegree u) p.2‖ :=
    h₁.mul_of_nonneg h₂ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hbdd : Summable fun p : ℤ × ℤ =>
      (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
        * (‖cw (mStarF u) p.1‖ * ‖cw (mStargF P.natDegree u) p.2‖) :=
    hprod.mul_left _
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hbdd
  simp only [hiTwKernel]
  rw [norm_mul, norm_mul]
  calc ‖arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2‖ * ‖cw (mStarF u) p.1‖
        * ‖cw (mStargF P.natDegree u) p.2‖
      ≤ (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
          * ‖cw (mStarF u) p.1‖ * ‖cw (mStargF P.natDegree u) p.2‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hb p.1 p.2) (norm_nonneg _)) (norm_nonneg _)
    _ = (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
          * (‖cw (mStarF u) p.1‖ * ‖cw (mStargF P.natDegree u) p.2‖) := by ring

/-- **The repaired §6 model tuple is the bilinear convolution with its kernel `hiKmodNRep`.** -/
theorem hiModelTupleRep_eq_bilinOp (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ n : ℕ) {f g : ℤ → ℂ} (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂)
    (hf : Work.KMTAreas.A5.BoundedZ f) (hg : Work.KMTAreas.A5.BoundedZ g) (x : ℤ)
    (hcore : Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n)
    (hband : Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))) :
    Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = Work.KMTAreas.A7.bilinOp (Work.KMTAreas.A7.hiKmodNRep ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂) f g x := by
  obtain ⟨Cf, hfbound⟩ := hf
  obtain ⟨Cg, hgbound⟩ := hg
  have hCf0 : 0 ≤ Cf := le_trans (norm_nonneg (f 0)) (hfbound 0)
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg (g 0)) (hgbound 0)
  have hguard : Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
      ∧ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
      ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n))
      ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) :=
    ⟨hcore.1, hcore.2.1, hcore.2.2, hband⟩
  simp only [modelTupleRep]
  rw [if_pos hguard]
  obtain ⟨hκ, hBb, hmκ⟩ := hiKer_varphiNt_spec ρ l₁ (Nat.floor (a n)) k₁
  obtain ⟨B1, hB1nonneg, hκb⟩ := hBb
  obtain ⟨hκ', hBb', hmκ'⟩ := hiKer_varphitildeNt_spec ρ P l₂ (Nat.floor (a n)) k₂
  obtain ⟨B2, hB2nonneg, hκb'⟩ := hBb'
  have hKsum := hiTwKernel_summable_rep ρ P l₁ l₂ (uRep ρ l₁ l₂ k₁ k₂)
  have hstep : ∀ t : ℝ,
      BtwistExact ρ P l₁ l₂
          (mStarF (uRep ρ l₁ l₂ k₁ k₂))
          (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
          (Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
          (Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x
        = bilinOp (hiTwKernel ρ P l₁ l₂
              (mStarF (uRep ρ l₁ l₂ k₁ k₂))
              (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)))
            (convOp (hiKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t)) f)
            (convOp (hiKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) g) x := by
    intro t
    simp only [Tex_eq_convOp_hiKer ρ hl₁, Tex_eq_convOp_hiKer ρ hl₂,
      BtwistExact_eq_bilinOp_hiTw]
  simp only [hstep]
  rw [Work.KMTPlan.A6.bilinOp_intervalIntegral
      (K := hiTwKernel ρ P l₁ l₂
        (mStarF (uRep ρ l₁ l₂ k₁ k₂))
        (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)))
      (κ := fun t j => hiKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) j)
      (κ' := fun t j => hiKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) j)
      (f := f) (g := g)
      (BK := ∑' p : ℤ × ℤ, ‖hiTwKernel ρ P l₁ l₂
        (mStarF (uRep ρ l₁ l₂ k₁ k₂))
        (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)) p.1 p.2‖)
      (B1 := B1) (B2 := B2) (Cf := Cf) (Cg := Cg) x
      hKsum le_rfl hκ hκ' hκb hκb' hfbound hgbound hCf0 hCg0
      (tsum_nonneg fun _ => norm_nonneg _) hB1nonneg hB2nonneg hmκ hmκ']
  rfl

end Work.KMTAreas.A7
