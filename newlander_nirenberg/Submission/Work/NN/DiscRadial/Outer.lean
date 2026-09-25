/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Smoothness of the unfolded extension on the outside of the unit disc

On `σ < 0` the unfolded extension is the reflected sum `∑_i discWt k i · (χ(-b_i σ) · h(y,-b_i σ))`.
Since `χ = seeleyCut` vanishes identically for arguments `≥ 2`, the product `χ(u)·h(y,u)` extends
smoothly to all `u > 0` by `flatMul_contDiffOn_of_smooth`; the reflected sum is then a finite sum
of compositions with the linear reflections `eta (-(discScale i))`.
-/
import Mathlib
import Submission.Work.NN.DiscRadial.Setup
import Submission.Work.NN.DiscRadial.Unfold
import Submission.Work.NN.DiscRadial.Comp
import Submission.Work.NN.DiscRadial.flatMul_contDiffOn
import Submission.Work.NN.Final.eta

noncomputable section
open scoped NNReal ENNReal ContDiff Topology
open Set Metric Filter

namespace Work.NN.DiscRadial

open Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The unfolded extension is `C^k` on the whole outside `σ < 0`. -/
theorem discUnfoldExt_neg_contDiffOn {k : ℕ} {g : X × ℂ → ℂ} {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) {W : Set (X × ℂ)} (hW : IsOpen W)
    (hcd : ContDiffOn ℝ (k : WithTop ENat) (discUnfold g) (W ×ˢ Set.Ioo 0 2))
    (hfin : Work.CR.Flat.holderNorm k β (discUnfold g) (W ×ˢ Set.Ioo 0 2) ≠ ⊤) :
    ContDiffOn ℝ (k : WithTop ENat) (discUnfoldExt k g) (W ×ˢ Set.Iio (0:ℝ)) := by
  have hΦ : ContDiffOn ℝ (k : WithTop ENat)
      (fun z : (X × ℂ) × ℝ => ((seeleyCut z.2 : ℝ) : ℂ) * discUnfold g z) (W ×ˢ Set.Ioi 0) :=
    flatMul_contDiffOn_of_smooth hW hβ0 hβ1 seeleyCut_contDiff
      (fun u hu => seeleyCut_eq_zero (by rw [abs_of_nonneg (by linarith)]; exact hu)) hcd hfin
  have hpre : ∀ i, (eta (X := X × ℂ) (-(discScale i))) ⁻¹' (W ×ˢ Set.Ioi 0)
      = W ×ˢ Set.Iio (0:ℝ) := by
    intro i
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioi, Set.mem_Iio, eta_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by have := discScale_pos i; nlinarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by have := discScale_pos i; nlinarith⟩
  have hsum : ContDiffOn ℝ (k : WithTop ENat)
      (fun z : (X × ℂ) × ℝ => ∑ i ∈ Finset.range (k + 1), (discWt k i : ℂ) •
        ((fun w : (X × ℂ) × ℝ => ((seeleyCut w.2 : ℝ) : ℂ) * discUnfold g w)
          (eta (-(discScale i)) z)))
      (W ×ˢ Set.Iio (0:ℝ)) := by
    refine ContDiffOn.sum fun i _ => ContDiffOn.const_smul _ ?_
    have h1 := hΦ.comp_continuousLinearMap (eta (-(discScale i)))
    rwa [hpre i] at h1
  refine hsum.congr (fun z hz => ?_)
  rw [discUnfoldExt_of_neg hz.2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eta_apply]
  rw [show (discWt k i : ℂ) • (((seeleyCut (-(discScale i) * z.2) : ℝ) : ℂ) * discUnfold g (z.1, -(discScale i) * z.2))
      = (discWt k i) • ((seeleyCut (-(discScale i) * z.2)) • discUnfold g (z.1, -(discScale i) * z.2)) from by
    rw [Complex.real_smul, Complex.real_smul]
    ring]

end Work.NN.DiscRadial
