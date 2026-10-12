import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Polar.fsT_parallelogram
import Submission.Work.BoseKinLoc.Word.momForm_const_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Energy.momForm_hpol` — homogeneity of the polarised large-momentum form

For the large-momentum kinetic word of FS `eq:DefT`,

    `momForm ℓ d u ψ = (2π)⁻³ ∫_p 1_{(d²ℓ)⁻¹<‖p‖}·‖kinFT (θ_u·Q_uψ) p‖²`,

the *polarised* difference `Q(f+g) − Q(f−g)` is homogeneous in its first argument:

    `momForm (t·f+g) − momForm (t·f−g) = t·(momForm (f+g) − momForm (f−g))`.

This is the statement that the polar form `B(f,g) = (Q(f+g) − Q(f−g))/4` of the quadratic
form `momForm` is homogeneous in the first variable.  It is **not** a consequence of the
parallelogram identity (`Polar.momForm_parallelogram`) together with the `2`-homogeneity
(`Word.momForm_const_mul`) alone: on an arbitrary real vector space the two relations
`Q(x+y)+Q(x−y) = 2Q(x)+2Q(y)` and `Q(tx) = t²Q(x)` determine the polarisation only up to
an odd `2`-periodic additive correction (take `Q(x) = x·φ(x)` on `ℝ` with `φ` a wild
additive map: then `Q` satisfies both, but `Q(t+1) − Q(t−1) = 2φ(t) + 2tφ(1) ≠ 4tφ(1)`).

The proof here therefore goes through the *explicit* form of the functional: the box mean
is linear, so the localised mean-free state is linear, so is its `p`-convention Fourier
transform, and on `ℂ` the polarisation of the squared norm is exactly bilinear:

* `Q_u(t·f ± g) = t·Q_u f ± Q_u g` (linearity of `bsQ`, `MomAux.bsQ_const_mul` and
  `FsTAux.bsQ_add`/`bsQ_sub`), hence `boxState (t·f±g) = t·boxState f ± boxState g`;
* `kinFT` is additive on the integrable states (`FsTAux.kinFT_add`/`kinFT_sub`) and
  `ℂ`-linear (`MomAux.kinFT_const_mul`), so the four Fourier transforms pair up;
* pointwise on `ℂ`, `‖tA+B‖² − ‖tA−B‖² = t(‖A+B‖² − ‖A−B‖²)` (`norm_sq_sub_norm_sq_smul`,
  a polynomial identity in the real and imaginary parts);
* the four `p`-integrands are integrable (`FsTAux.integrable_momProj_boxState`), so the
  `p`-integral is linear and subtractive.
-/

open MeasureTheory

namespace Work.BoseFixB2.Energy

/-- Pointwise polarisation of the squared modulus on `ℂ`: the polarised difference of the
squared norms is `ℝ`-homogeneous in the scaling of the first vector. -/
lemma norm_sq_sub_norm_sq_smul (t : ℝ) (A B : ℂ) :
    ‖(t : ℂ) * A + B‖ ^ 2 - ‖(t : ℂ) * A - B‖ ^ 2
      = t * (‖A + B‖ ^ 2 - ‖A - B‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

theorem momForm_hpol {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) (t : ℝ) {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Work.BoseKinLoc.momForm ℓ d u (fun z => t * f z + g z) - Work.BoseKinLoc.momForm ℓ d u (fun z => t * f z - g z) = t * (Work.BoseKinLoc.momForm ℓ d u (fun z => f z + g z) - Work.BoseKinLoc.momForm ℓ d u (fun z => f z - g z)) := by
  have hfsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin 3) => t * f z) :=
    contDiff_const.mul hf
  -- the two localised mean-free states are integrable
  have hIntf : Integrable (Work.BoseKinLoc.Kinetic.boxState ℓ u f) := by
    obtain ⟨h1, -⟩ := Work.BoseKinLoc.Kinetic.boxState_memLp (ℓ := ℓ) hℓ u hf
    exact MeasureTheory.memLp_one_iff_integrable.mp h1
  have hIntg : Integrable (Work.BoseKinLoc.Kinetic.boxState ℓ u g) := by
    obtain ⟨h1, -⟩ := Work.BoseKinLoc.Kinetic.boxState_memLp (ℓ := ℓ) hℓ u hg
    exact MeasureTheory.memLp_one_iff_integrable.mp h1
  -- the localised states of the rescaled combinations
  have hBSp : Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => t * f z + g z)
      = fun x => (t : ℂ) * Work.BoseKinLoc.Kinetic.boxState ℓ u f x
          + Work.BoseKinLoc.Kinetic.boxState ℓ u g x := by
    have h1 : Work.BoseKinLoc.Qfree ℓ u (fun z => t * f z + g z)
        = fun z => t * Work.BoseKinLoc.Qfree ℓ u f z + Work.BoseKinLoc.Qfree ℓ u g z := by
      simp only [Work.BoseKinLoc.Qfree]
      rw [Work.BoseFixB2.Polar.FsTAux.bsQ_add hℓ u hfsm.continuous hg.continuous,
        Work.BoseKinLoc.Word.MomAux.bsQ_const_mul ℓ u t f]
    funext x
    simp only [Work.BoseKinLoc.Kinetic.boxState]
    rw [congrFun h1 x]
    push_cast
    ring
  have hBSm : Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => t * f z - g z)
      = fun x => (t : ℂ) * Work.BoseKinLoc.Kinetic.boxState ℓ u f x
          - Work.BoseKinLoc.Kinetic.boxState ℓ u g x := by
    have h1 : Work.BoseKinLoc.Qfree ℓ u (fun z => t * f z - g z)
        = fun z => t * Work.BoseKinLoc.Qfree ℓ u f z - Work.BoseKinLoc.Qfree ℓ u g z := by
      simp only [Work.BoseKinLoc.Qfree]
      rw [Work.BoseFixB2.Polar.FsTAux.bsQ_sub hℓ u hfsm.continuous hg.continuous,
        Work.BoseKinLoc.Word.MomAux.bsQ_const_mul ℓ u t f]
    funext x
    simp only [Work.BoseKinLoc.Kinetic.boxState]
    rw [congrFun h1 x]
    push_cast
    ring
  have hBSpp : Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z + g z)
      = fun x => Work.BoseKinLoc.Kinetic.boxState ℓ u f x
          + Work.BoseKinLoc.Kinetic.boxState ℓ u g x := by
    have h1 : Work.BoseKinLoc.Qfree ℓ u (fun z => f z + g z)
        = fun z => Work.BoseKinLoc.Qfree ℓ u f z + Work.BoseKinLoc.Qfree ℓ u g z :=
      Work.BoseFixB2.Polar.FsTAux.Qfree_add hℓ u hf.continuous hg.continuous
    funext x
    simp only [Work.BoseKinLoc.Kinetic.boxState]
    rw [congrFun h1 x]
    push_cast
    ring
  have hBSmm : Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z - g z)
      = fun x => Work.BoseKinLoc.Kinetic.boxState ℓ u f x
          - Work.BoseKinLoc.Kinetic.boxState ℓ u g x := by
    have h1 : Work.BoseKinLoc.Qfree ℓ u (fun z => f z - g z)
        = fun z => Work.BoseKinLoc.Qfree ℓ u f z - Work.BoseKinLoc.Qfree ℓ u g z :=
      Work.BoseFixB2.Polar.FsTAux.Qfree_sub hℓ u hf.continuous hg.continuous
    funext x
    simp only [Work.BoseKinLoc.Kinetic.boxState]
    rw [congrFun h1 x]
    push_cast
    ring
  -- the four Fourier transforms
  have hKp : ∀ p, Submission.BoseGases.kinFT
      (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => t * f z + g z)) p
      = (t : ℂ) * Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u f) p
        + Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u g) p := by
    intro p
    rw [hBSp, Work.BoseFixB2.Polar.FsTAux.kinFT_add (hIntf.const_mul (t : ℂ)) hIntg p,
      Work.BoseKinLoc.Word.MomAux.kinFT_const_mul (t : ℂ)
        (Work.BoseKinLoc.Kinetic.boxState ℓ u f) p]
  have hKm : ∀ p, Submission.BoseGases.kinFT
      (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => t * f z - g z)) p
      = (t : ℂ) * Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u f) p
        - Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u g) p := by
    intro p
    rw [hBSm, Work.BoseFixB2.Polar.FsTAux.kinFT_sub (hIntf.const_mul (t : ℂ)) hIntg p,
      Work.BoseKinLoc.Word.MomAux.kinFT_const_mul (t : ℂ)
        (Work.BoseKinLoc.Kinetic.boxState ℓ u f) p]
  have hKpp : ∀ p, Submission.BoseGases.kinFT
      (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z + g z)) p
      = Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u f) p
        + Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u g) p := by
    intro p
    rw [hBSpp, Work.BoseFixB2.Polar.FsTAux.kinFT_add hIntf hIntg p]
  have hKmm : ∀ p, Submission.BoseGases.kinFT
      (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z - g z)) p
      = Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u f) p
        - Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u g) p := by
    intro p
    rw [hBSmm, Work.BoseFixB2.Polar.FsTAux.kinFT_sub hIntf hIntg p]
  -- the four `p`-integrands are integrable
  have hintp := Work.BoseFixB2.Polar.FsTAux.integrable_momProj_boxState (d := d) hℓ u
    (hfsm.add hg)
  have hintm := Work.BoseFixB2.Polar.FsTAux.integrable_momProj_boxState (d := d) hℓ u
    (hfsm.sub hg)
  have hintpp := Work.BoseFixB2.Polar.FsTAux.integrable_momProj_boxState (d := d) hℓ u
    (hf.add hg)
  have hintmm := Work.BoseFixB2.Polar.FsTAux.integrable_momProj_boxState (d := d) hℓ u
    (hf.sub hg)
  -- the `p`-integral identity
  have key : (∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT
          (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => t * f z + g z)) p‖ ^ 2)
      - (∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT
          (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => t * f z - g z)) p‖ ^ 2)
      = t * ((∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT
            (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z + g z)) p‖ ^ 2)
        - (∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT
            (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z - g z)) p‖ ^ 2)) := by
    rw [← MeasureTheory.integral_sub hintp hintm, ← MeasureTheory.integral_sub hintpp hintmm,
      ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [hKp p, hKm p, hKpp p, hKmm p]
    rw [← mul_sub, ← mul_sub, norm_sq_sub_norm_sq_smul t (Submission.BoseGases.kinFT
      (Work.BoseKinLoc.Kinetic.boxState ℓ u f) p)
      (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u g) p)]
    ring
  rw [Work.BoseKinLoc.Kinetic.momForm_eq_boxState ℓ d u (fun z => t * f z + g z),
    Work.BoseKinLoc.Kinetic.momForm_eq_boxState ℓ d u (fun z => t * f z - g z),
    Work.BoseKinLoc.Kinetic.momForm_eq_boxState ℓ d u (fun z => f z + g z),
    Work.BoseKinLoc.Kinetic.momForm_eq_boxState ℓ d u (fun z => f z - g z)]
  linear_combination ((2 * Real.pi) ^ 3)⁻¹ * key

end Work.BoseFixB2.Energy
