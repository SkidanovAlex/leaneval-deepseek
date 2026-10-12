import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.L1Tails.latticeDirichlet
import Submission.Work.BoseBoxFock.L1Tails.secondMomentPlancherelOne
import Submission.Work.BoseBoxFock.PCFU.UnivFrames
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.slotSamplingRefl`

The **reflected** sampling identity: the lattice sampling sum of the momentum second moment of a
slot state is unchanged when the slot function is reflected through an arbitrary point `y`,

    Σ'_n ‖κ_n‖² ‖kinFT (fun z => g (y − z)) (−κ_n)‖² = ℓ³ ∫_x Σ_j ‖∂_{e_j} g(x)‖² ,

for `g` smooth with `tsupport g ⊆ boxL ℓ` (the cube of side `ℓ`).

## Why it is true, and how it is proved

The complexification `G = ↑g` of `g` is as smooth as `g` and has the same support, so the proved
lattice sampling identity `Work.BoseBoxFock.PCFU.samplingDeriv` applies to it, giving

    Σ'_n ‖κ_n‖² ‖kinFT G (κ_n)‖² = ℓ³ ∫_x Σ_j ‖∂_{e_j} g(x)‖²

(the two Fréchet derivatives have the same norm because the complexification is an isometry,
`Work.BoseBoxFock.PCFU.norm_fderiv_complexify`).  It remains to see that the left-hand side does
not change when `G` is replaced by its reflection-translate `z ↦ g (y − z)`.  The substitution
`z ↦ y − z` in the defining integral gives, exactly,

    kinFT (fun z => g (y − z)) (−p) = e^{i⟪y,p⟫} · kinFT G p

(`Work.BoseBoxFock.PCFU.kinFT_refl_comp_sub`), and the phase is unimodular, so the *moduli* agree
and the two lattice sums coincide term by term.

## Proof outline

* `integral_comp_sub_left_vol` — the measure-preserving change of variable `z ↦ y − z`;
* `kinFT_refl_comp_sub` — the phase identity above;
* `norm_fderiv_complexify` — the complexification does not change `‖fderiv‖`;
* the assembly: `samplingDeriv` for the complexification + the termwise norm comparison.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory Filter
open scoped BigOperators Real

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## Auxiliary lemmas -/

/-- The change of variable `z ↦ y - z` leaves the Lebesgue integral unchanged:
`∫_z F (y - z) = ∫_t F t`. -/
lemma integral_comp_sub_left_vol (F : E3 → ℂ) (y : E3) :
    (∫ z : E3, F (y - z)) = ∫ t : E3, F t := by
  have h2 : (∫ z : E3, F (y - z)) = ∫ s : E3, F (-(s - y)) := by
    apply integral_congr_ae
    filter_upwards with s
    show F (y - s) = F (-(s - y))
    rw [neg_sub]
  have h3 : (∫ s : E3, F (-(s - y))) = ∫ s : E3, F (-s) :=
    integral_sub_right_eq_self (fun u : E3 => F (-u)) y
  rw [h2, h3, integral_neg_eq_self]

/-- The reflection/translation covariance of the `p`-convention Fourier transform of a
*real-valued* function: for the reflected function `z ↦ g (y - z)`, the transform at `-p` is the
transform of `g` at `p`, up to the unimodular phase `e^{i⟪y,p⟫}`. -/
theorem kinFT_refl_comp_sub (g : E3 → ℝ) (y p : E3) :
    Submission.BoseGases.kinFT (fun z => ((g (y - z) : ℝ) : ℂ)) (-p)
      = Complex.exp (Complex.I * (inner ℝ y p : ℂ))
        * Submission.BoseGases.kinFT (fun z => ((g z : ℝ) : ℂ)) p := by
  have hpt : ∀ t : E3, Complex.exp (-(Complex.I * (inner ℝ (-p) (y - t) : ℂ))) * ((g t : ℝ) : ℂ)
      = Complex.exp (Complex.I * (inner ℝ y p : ℂ))
        * (Complex.exp (-(Complex.I * (inner ℝ p t) : ℂ)) * ((g t : ℝ) : ℂ)) := by
    intro t
    have harg : -(Complex.I * (inner ℝ (-p) (y - t) : ℂ))
        = Complex.I * (inner ℝ y p : ℂ) + -(Complex.I * (inner ℝ p t) : ℂ) := by
      rw [inner_sub_right, inner_neg_left, inner_neg_left]
      push_cast
      rw [real_inner_comm p y]
      ring
    rw [harg, Complex.exp_add]
    ring
  simp only [Submission.BoseGases.kinFT]
  have hbeta : (∫ z : E3,
        Complex.exp (-(Complex.I * (inner ℝ (-p) z : ℂ))) * ((g (y - z) : ℝ) : ℂ))
      = ∫ z : E3, Complex.exp (-(Complex.I * (inner ℝ (-p) (y - (y - z)) : ℂ)))
          * ((g (y - z) : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [sub_sub_cancel]
  rw [hbeta, integral_comp_sub_left_vol
    (fun w : E3 => Complex.exp (-(Complex.I * (inner ℝ (-p) (y - w) : ℂ))) * ((g w : ℝ) : ℂ)) y,
    integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]

/-- The complexification does not change the (operator-norm) size of the Fréchet derivative. -/
theorem norm_fderiv_complexify {g : E3 → ℝ} (hg : ContDiff ℝ 1 g) (x v : E3) :
    ‖fderiv ℝ (fun z : E3 => ((g z : ℝ) : ℂ)) x v‖ = ‖fderiv ℝ g x v‖ := by
  have hG : (fun z : E3 => ((g z : ℝ) : ℂ)) = ⇑Complex.ofRealCLM ∘ g := by
    funext z; rw [Function.comp_apply, Complex.ofRealCLM_apply]
  have hcomp : fderiv ℝ (fun z : E3 => ((g z : ℝ) : ℂ)) x
      = Complex.ofRealCLM.comp (fderiv ℝ g x) := by
    rw [hG]
    exact (Complex.ofRealCLM.hasFDerivAt.comp x
      ((hg.differentiable_one x).hasFDerivAt)).fderiv
  rw [hcomp]
  show ‖Complex.ofRealCLM (fderiv ℝ g x v)‖ = ‖fderiv ℝ g x v‖
  rw [Complex.ofRealCLM_apply, ← Complex.ofRealLI_apply, Complex.ofRealLI.norm_map]

/-! ## The target -/

theorem slotSamplingRefl {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ) (y : EuclideanSpace ℝ (Fin 3)) :
    ∑' n : Fin 3 → ℤ, ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
        * ‖Submission.BoseGases.kinFT (fun z => ((g (y - z) : ℝ) : ℂ))
            (-(Work.BoseBoxFock.kappaL ℓ n))‖ ^ 2
      = ℓ ^ 3 * ∫ x : EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
          ‖fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  have hcs : HasCompactSupport g :=
    IsCompact.of_isClosed_subset (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
      (isClosed_tsupport g) hgs
  -- the complexification `G = ↑g` is `C¹` with the same (box) support
  have hG1 : ContDiff ℝ 1 (fun z : E3 => ((g z : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp hg1
  have htsG : tsupport (fun z : E3 => ((g z : ℝ) : ℂ)) ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
    refine (closure_mono ?_).trans hgs
    intro z hz
    simpa [Function.mem_support] using hz
  have hGcs : HasCompactSupport (fun z : E3 => ((g z : ℝ) : ℂ)) :=
    IsCompact.of_isClosed_subset (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
      (isClosed_tsupport _) htsG
  -- the lattice sampling identity for the complexification
  have hval : ∑' n : Fin 3 → ℤ, ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
        * ‖Submission.BoseGases.kinFT (fun z : E3 => ((g z : ℝ) : ℂ))
            (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
      = ℓ ^ 3 * ∑ j : Fin 3, ∫ z : E3,
          ‖fderiv ℝ (fun z : E3 => ((g z : ℝ) : ℂ)) z
            (Submission.BoseGases.kcStdBasis j)‖ ^ 2 := by
    have h := (Work.BoseBoxFock.L1Tails.latticeDirichlet hℓ hG1 htsG).tsum_eq
    rw [Work.BoseBoxFock.L1Tails.secondMomentPlancherelOne hG1 hGcs] at h
    exact h
  -- the reflection only multiplies each mode by a unimodular phase
  have hnorm : ∀ p : E3, ‖Submission.BoseGases.kinFT (fun z => ((g (y - z) : ℝ) : ℂ)) (-p)‖
      = ‖Submission.BoseGases.kinFT (fun z : E3 => ((g z : ℝ) : ℂ)) p‖ := by
    intro p
    rw [kinFT_refl_comp_sub g y p, norm_mul,
      show Complex.I * ((inner ℝ y p : ℝ) : ℂ) = ((inner ℝ y p : ℝ) : ℂ) * Complex.I from
        mul_comm _ _,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  -- integrability of the squared directional derivatives of `g`
  have hIntg : ∀ j : Fin 3,
      Integrable (fun z : E3 => ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2) := by
    intro j
    have hcont : Continuous (fun z : E3 => fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)) :=
      (hg1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcsc : HasCompactSupport (fun z : E3 => fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)) :=
      hcs.fderiv_apply ℝ _
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mp
      (hcont.memLp_of_hasCompactSupport hcsc)
  have hsumg : (∑ j : Fin 3, ∫ z : E3, ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2)
      = ∫ x : E3, ∑ j : Fin 3, ‖fderiv ℝ g x (Submission.BoseGases.kcStdBasis j)‖ ^ 2 :=
    (MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun (j : Fin 3) (z : E3) => ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2)
      (fun j _ => hIntg j)).symm
  have hperJ : ∀ j : Fin 3, (∫ z : E3, ‖fderiv ℝ (fun z : E3 => ((g z : ℝ) : ℂ)) z
        (Submission.BoseGases.kcStdBasis j)‖ ^ 2)
      = ∫ z : E3, ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2 := by
    intro j
    apply integral_congr_ae
    filter_upwards with z
    rw [norm_fderiv_complexify hg1 z (Submission.BoseGases.kcStdBasis j)]
  calc ∑' n : Fin 3 → ℤ, ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
        * ‖Submission.BoseGases.kinFT (fun z => ((g (y - z) : ℝ) : ℂ))
            (-(Work.BoseBoxFock.kappaL ℓ n))‖ ^ 2
      = ∑' n : Fin 3 → ℤ, ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
        * ‖Submission.BoseGases.kinFT (fun z : E3 => ((g z : ℝ) : ℂ))
            (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 :=
          tsum_congr (fun n => by rw [hnorm])
    _ = ℓ ^ 3 * ∑ j : Fin 3, ∫ z : E3,
          ‖fderiv ℝ (fun z : E3 => ((g z : ℝ) : ℂ)) z
            (Submission.BoseGases.kcStdBasis j)‖ ^ 2 := hval
    _ = ℓ ^ 3 * ∑ j : Fin 3, ∫ z : E3,
          ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl (fun j _ => hperJ j)
    _ = ℓ ^ 3 * ∫ x : E3, ∑ j : Fin 3,
          ‖fderiv ℝ g x (Submission.BoseGases.kcStdBasis j)‖ ^ 2 := by
          rw [hsumg]
    _ = ℓ ^ 3 * ∫ x : E3, ∑ j : Fin 3,
          ‖fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
          simp only [Submission.BoseGases.kcStdBasis]

end Work.BoseBoxFock.PCFU
