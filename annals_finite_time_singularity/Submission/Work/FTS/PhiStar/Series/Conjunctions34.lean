/-
# `Work.FTS.PhiStar.Series.Conjunctions34` — conjuncts 3 and 4 of the target, unconditionally

This module combines the proved crux estimates

* `Series/eFam_growth` (`|eFam m θ| ≤ C(m+1)^{3/2}`),
* `Series/eFam_sup_le` (`|eFam m θ| ≤ C(m+1)`, the sharp bound),
* `Series/bmode_decay15` (`|bmode m ψ| ≤ C/(lam m √(2m+1))`),
* `Series/radGreen_phiA_bound` (the direct Green-formula bound for the source `phiA α`, whose
  decay `(2α-10)/t` makes `radGreen_abs_le` unusable),

with the conditional assembly of `Series/SummableModes` and `Series/DecayRem` to obtain,
**unconditionally** for `0 < α ≤ 1/5` and `AngModel α ψ`:

* the absolute summability of the mode series at every point of the open quadrant
  (`summable_modes_inst`), and
* **conjunct 4 of `psiSeries_solves_rem`** (decay of `psiSeries α (RemSource α ψ) · θ` as
  `z → ∞`), together with **conjunct 3** (the Dirichlet values).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Series.SummableModes
import Submission.Work.FTS.PhiStar.Series.DecayRem
import Submission.Work.FTS.PhiStar.Series.eFam_growth
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.PhiStar.Series.bmode_decay15
import Submission.Work.FTS.PhiStar.Series.radGreen_phiA_bound
import Submission.Work.FTS.PhiStar.Series.ResolventSetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-! ## Conversion of the coefficient-decay rate -/

/-- `bmode_decay15`'s rate `1/(lam m · √(2m+1))` is bounded by `(m+1)^{-5/2}` (for `m ≥ 1`),
which is the shape the summability estimates use. -/
theorem bmode_decay_pow (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨Cd, hCd, hdec⟩ := bmode_decay15
  refine ⟨Cd, hCd, fun m hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hdec' := hdec α ψ hα hα5 hψ m hm
  have hkey : (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))⁻¹
      ≤ ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
    have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) := by
      rw [Work.FTS.PhiStar.Gegenbauer.lam]
      have : (0 : ℝ) < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
      positivity
    have hnum : 0 < ((m : ℝ) + 1) ^ ((5 / 2 : ℝ)) := Real.rpow_pos_of_pos hm0 _
    have hS : ((m : ℝ) + 1) ^ ((5 / 2 : ℝ)) ≤
        Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) := by
      have hsplit : ((m : ℝ) + 1) ^ ((5 / 2 : ℝ))
          = ((m : ℝ) + 1) ^ (2 : ℕ) * Real.sqrt ((m : ℝ) + 1) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hm0]
        norm_num
      rw [hsplit]
      have h3 : ((m : ℝ) + 1) ^ (2 : ℕ) ≤ 4 * (m : ℝ) ^ 2 := by
        have hle : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
        have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1) hle 2
        nlinarith [hp]
      have h4 : (4 : ℝ) * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
        rw [Work.FTS.PhiStar.Gegenbauer.lam]
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      have h5 : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      exact mul_le_mul (le_trans h3 h4) h5 (Real.sqrt_nonneg _)
        (le_trans (by positivity : (0 : ℝ) ≤ 4 * (m : ℝ) ^ 2) h4)
    rw [Real.rpow_neg (le_of_lt hm0)]
    exact (inv_le_inv₀ hden hnum).mpr hS
  have hdiv : Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hkey (le_of_lt hCd)
  rw [bmode_eq_cmode m ψ 0]
  exact le_trans hdec' hdiv

/-! ## Summability of the mode series for the remainder source -/

/-- **Absolute summability of the mode series**, unconditionally for `0 < α ≤ 1/5` and
`AngModel α ψ`. -/
theorem summable_modes_inst (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Summable (fun m : ℕ => acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  obtain ⟨Cr, hCr, hR⟩ := radGreen_phiA_bound
  refine summable_modes α ψ hα hψ eFam_growth (bmode_decay_pow α ψ hα hα5 hψ)
    ⟨Cr, hCr, fun m hm z hz => (hR α hα (by linarith) m hm).1 z hz⟩

/-! ## Conjuncts 3 and 4 of the target -/

/-- **Conjunct 4**: for every `θ ∈ Iθ` the mode series of the remainder source tends to `0` as
`z → ∞` (unconditionally, for `0 < α ≤ 1/5` and `AngModel α ψ`). -/
theorem psiSeries_tendsto_zero_inst (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ)
        Filter.atTop (nhds 0) := by
  obtain ⟨Cr, hCr, hR⟩ := radGreen_phiA_bound
  refine psiSeries_tendsto_zero_RemSource α ψ hα hψ eFam_growth
    (bmode_decay_pow α ψ hα hα5 hψ)
    ⟨Cr, hCr, fun m hm z hz => (hR α hα (by linarith) m hm).2 z hz⟩
    (fun z hz θ hθ => ?_)
  exact summable_norm_iff.mpr (summable_modes_inst α ψ hα hα5 hψ z hz θ hθ)

/-- **Conjunct 3**: the Dirichlet values of the mode series (unconditional). -/
theorem psiSeries_dirichlet_inst (α : ℝ) (ψ : ℝ → ℝ) :
    ∀ z : ℝ, psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z 0 = 0 ∧
      psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z (Real.pi / 2) = 0 :=
  fun z => ⟨psiSeries_zero_right α _ z, psiSeries_zero_left α _ z⟩

end Work.FTS.PhiStar.Series
