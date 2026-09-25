import Mathlib
import Submission.Work.NN.Core.perturbed_aux
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.bmPotential_gain
import Submission.Work.NN.Core.bmPotential_dbarDefect_eq
import Submission.Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul
import Submission.Work.NN.Core.Lcoef_uniform_estimate_on
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_univ_ne_top_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.NN.Core.holderNorm_const_mul_le
import Submission.Work.NN.Core.flatMulNorm
import Submission.Work.NN.Core.holderNorm_one_lt_top_of_wirtinger
import Submission.Work.NN.Core.czB_holderNorm_bound_holder
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.NN.Core.dbarCn_dirDeriv_comm
import Submission.Work.NN.Core.isInvertible_one_add_and_inverse_norm_le
import Submission.Work.NN.Core.exists_beltrami_reduction
import Submission.Work.NN.Core.dbarCn_iteratedFDeriv_holder
import Submission.Work.NN.Core.holderNorm_one_lt_top_of_beltramiF
import Submission.Work.NN.Core.holderSeminorm_succ_of_slice
import Submission.Work.NN.Core.perturbed_lossless_quantitative
import Submission.Work.NN.Core.perturbed_finiteness

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter

noncomputable section

variable {n : ℕ}

/-- **The lossless a priori estimate for the perturbed `∂̄`-operator on compactly supported functions.**

Let `A` be smooth and `ε`-small *componentwise* in `C^{k+1,α}` on `polydisc 0 ρ`, with
`J := JstdCn n + A` an almost complex structure, and let `ρ' < ρ` (coordinatewise).  Then for every
`v` of class `C^{k+1}` on `polydisc 0 ρ` which **vanishes off the smaller polydisc** `polydisc 0 ρ'`
(so that `v` has compact support contained in the *open* polydisc and is globally `C^{k+1}`),

  `‖v‖_{C^{k+1,α}(polydisc 0 ρ')} ≤ C · Σ_j ‖(∂̄_J v)_j‖_{C^{k,α}(polydisc 0 ρ')}`

with `C` uniform over all such `A` with `ε ≤ ε₀`. -/
theorem perturbed_lossless {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ'0 : ∀ j, 0 < ρ' j) (hρ' : ∀ j, ρ' j < ρ j)
    (k : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n},
        (∀ m : ℕ, ContDiff ℝ m A) → ∀ {ε : ℝ}, ε ≤ ε₀ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm (k+1) α
            (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ)
          ≤ ENNReal.ofReal ε) →
        (∀ z v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        ∀ v : Work.NN.Core.Cn n → ℂ,
          (∀ z, (∃ i, ρ' i ≤ ‖z i‖) → v z = 0) →
          ContDiffOn ℝ (((k+1 : ℕ)) : WithTop ENat) v (Work.CR.Flat.polydisc 0 ρ) →
          Work.CR.Flat.holderNorm (k+1) α v (Work.CR.Flat.polydisc 0 ρ')
            ≤ ENNReal.ofReal C * (∑ j : Fin n,
                  Work.CR.Flat.holderNorm k α
                    (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) v z (Pi.single j 1))
                    (Work.CR.Flat.polydisc 0 ρ')) := by
  classical
  obtain ⟨εf, hεfpos, hfin⟩ := perturbed_finiteness hn hα0 hα1 hρ0 hρ'0 hρ' k
  obtain ⟨εq, hεqpos, C, hCpos, hquant⟩ :=
    perturbed_lossless_quantitative hn hα0 hα1 hρ0 hρ'0 hρ' k
  refine ⟨min εf εq, lt_min hεfpos hεqpos, C, hCpos, ?_⟩
  intro A hA ε hε hsmall hJ v hvan hv
  by_cases hX : (∑ j : Fin n, Work.CR.Flat.holderNorm k α
      (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) v z (Pi.single j 1))
      (Work.CR.Flat.polydisc 0 ρ')) = ⊤
  · rw [hX, ENNReal.mul_top]
    · exact le_top
    · exact ENNReal.ofReal_ne_zero_iff.mpr hCpos
  · have hXlt : (∑ j : Fin n, Work.CR.Flat.holderNorm k α
        (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) v z (Pi.single j 1))
        (Work.CR.Flat.polydisc 0 ρ')) < ⊤ := lt_top_iff_ne_top.mpr hX
    set ε' : ℝ := max ε 0 with hε'def
    have hε'0 : 0 ≤ ε' := le_max_right _ _
    have hε'f : ε' ≤ εf := max_le (le_trans hε (min_le_left _ _)) hεfpos.le
    have hε'q : ε' ≤ εq := max_le (le_trans hε (min_le_right _ _)) hεqpos.le
    have hsmall' : ∀ i j : Fin n, Work.CR.Flat.holderNorm (k+1) α
        (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ)
          ≤ ENNReal.ofReal ε' := fun i j =>
      (hsmall i j).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hF : Work.CR.Flat.holderNorm (k+1) α v (Work.CR.Flat.polydisc 0 ρ') < ⊤ :=
      hfin hA hε'0 hε'f hsmall' hJ v hvan hv hXlt
    exact hquant hA hε'0 hε'q hsmall' hJ v hvan hv hF

end

end Work.NN.Core
