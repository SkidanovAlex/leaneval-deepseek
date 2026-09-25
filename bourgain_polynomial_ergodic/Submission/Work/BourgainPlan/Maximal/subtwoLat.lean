/-
# The lattice maximal-vs-values principle (the corrected `hLattice`) — assembly

Owner: the `subtwo` owner.  See `LATTICE_PRINCIPLE_STATUS.md` (this directory) and
`Submission/Work/Maximal/LATTICE_PRINCIPLE_WARNING.md`:

* the `hlattice`/`hLattice` binder used in `Submission/Work/Maximal/` is **FALSE as stated**
  (an a.e.-change of `H` leaves `hlMax` unchanged but can kill the values on the lattice);
* the minimal true fix is to add `Continuous H`;
* the corrected statement is `mstLatticePrinciple` below (a `sorry`-free, axiom-clean theorem):
  the `(Q,m,c)` statement follows from the *unit-lattice core* `lat_unit_lattice_core` (which is
  built from the two lattice inputs `lat_hlMax_kernel_estimate_uniform` and
  `latDiscMaxC_lintegral_rpow_le`), and the reduction is `mstLatticePrinciple_of_core` (proved here
  using the affine invariance of `hlMax` and the Fourier scaling/translation rules).
-/
import Mathlib
import Submission.Work.IonescuWainger.young_count_lp
import Submission.Work.BourgainPlan.Maximal.subtwoLatDefs
import Submission.Work.BourgainPlan.Maximal.lat_sampling_reproduce
import Submission.Work.BourgainPlan.Maximal.latHlMax_dilate
import Submission.Work.BourgainPlan.Maximal.latAffine
import Submission.Work.Maximal.mstWide_defs
import Submission.Commons.Analysis.Fourier.fourier_comp_mul_left
import Submission.Work.Analysis.Fourier.fourier_comp_add
import Submission.Work.BourgainPlan.Maximal.lat_unit_lattice_core
import Submission.Work.BourgainPlan.Maximal.lat_hlMax_kernel_estimate_uniform
import Submission.Work.BourgainPlan.Maximal.latDiscMaxC_lintegral_rpow_le
import Submission.Work.BourgainPlan.Maximal.latDiscMax_lintegral_rpow_le

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped BigOperators ENNReal FourierTransform

noncomputable section

/-- **The corrected `hLattice`**, modulo the unit-lattice core.  This is the binder of
`Submission/Work/Maximal/mstWideModel_lr_maximal.lean` (and of `wideLat_class_bound`,
`mstWideLrLarge`) with the necessary hypothesis `Continuous H` added; without it the statement is
false (see `LATTICE_PRINCIPLE_STATUS.md` §1).

The reduction from the general sublattice `Qℤ + m` with shift `c` to the unit lattice with shift
`c/Q` uses `latHlMax_dilate` (affine invariance of `hlMax`), `integrable_comp_affine`,
`lintegral_comp_affine`, and the Fourier scaling/translation rules
(`Commons.Analysis.Fourier.fourier_comp_mul_left`, `Commons.Analysis.Fourier.fourier_comp_add`). -/
theorem mstLatticePrinciple_of_core {r : ℝ} (hr : 1 < r)
    (hcore : ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ → ℂ), Continuous H → MeasureTheory.Integrable H →
      (∀ ξ : ℝ, 1 / 4 < |ξ| → FourierTransform.fourier H ξ = 0) → ∀ s : ℝ,
      (∑' x : ℤ, (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖) ((x : ℝ) - s)) ^ r)
        ≤ ENNReal.ofReal (C ^ r) * ∑' x : ℤ, ENNReal.ofReal (‖H (x : ℝ)‖ ^ r)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ → ℂ) (δ : ℝ), 0 < δ → Continuous H →
      MeasureTheory.Integrable H →
      (∀ ξ : ℝ, δ < |ξ| → FourierTransform.fourier H ξ = 0) →
      ∀ (Q : ℕ), 1 ≤ Q → δ * (Q : ℝ) ≤ 1 / 4 → ∀ (m : ℤ) (c : ℝ),
        (∑' x : ℤ, (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖)
            ((Q : ℝ) * (x : ℝ) + (m : ℝ) - c)) ^ r)
          ≤ ENNReal.ofReal (C ^ r) *
            ∑' x : ℤ, ENNReal.ofReal (‖H ((Q : ℝ) * (x : ℝ) + (m : ℝ))‖ ^ r) := by
  obtain ⟨C, hCpos, hC⟩ := hcore
  refine ⟨C, hCpos, fun H δ hδ hHc hH1 hband Q hQ1 hδQ m c => ?_⟩
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
  set Ht : ℝ → ℂ := fun y => H ((Q : ℝ) * y + (m : ℝ)) with hHtdef
  have hHtc : Continuous Ht := hHc.comp (by fun_prop)
  have hHt1 : MeasureTheory.Integrable Ht := integrable_comp_affine hH1 hQ0 m
  -- the band of the rescaled function
  have hHtband : ∀ ξ : ℝ, 1 / 4 < |ξ| → FourierTransform.fourier Ht ξ = 0 := by
    intro ξ hξ
    have hξQ : δ * (Q : ℝ) < |ξ| := lt_of_le_of_lt hδQ hξ
    have hlt : δ < |ξ / (Q : ℝ)| := by
      rw [abs_div, abs_of_pos hQ0, lt_div_iff₀ hQ0]
      exact hξQ
    have hfac : FourierTransform.fourier Ht ξ
        = ((Q : ℂ))⁻¹ * (Complex.exp
            ((↑(2 * Real.pi * (m : ℝ) * (ξ / (Q : ℝ))) * Complex.I) : ℂ)
              * FourierTransform.fourier H (ξ / (Q : ℝ))) := by
      change FourierTransform.fourier
        (fun y : ℝ => (fun z : ℝ => H (z + (m : ℝ))) ((Q : ℝ) * y)) ξ = _
      rw [Commons.Analysis.Fourier.fourier_comp_mul_left
        (fun z : ℝ => H (z + (m : ℝ))) hQ0 ξ]
      rw [Commons.Analysis.Fourier.fourier_comp_add H (m : ℝ) (ξ / (Q : ℝ))]
      push_cast
      ring
    rw [hfac, hband (ξ / (Q : ℝ)) hlt, mul_zero, mul_zero]
  have key := hC Ht hHtc hHt1 hHtband (c / (Q : ℝ))
  -- identify the two sums
  have hL : (∑' x : ℤ, (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖)
        ((Q : ℝ) * (x : ℝ) + (m : ℝ) - c)) ^ r)
      = ∑' x : ℤ, (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖Ht y‖)
        ((x : ℝ) - c / (Q : ℝ))) ^ r := by
    refine tsum_congr fun x => ?_
    congr 1
    rw [show (Q : ℝ) * (x : ℝ) + (m : ℝ) - c
        = (Q : ℝ) * ((x : ℝ) - c / (Q : ℝ)) + (m : ℝ) from by field_simp; ring]
    rw [latHlMax_dilate (fun y : ℝ => ENNReal.ofReal ‖H y‖) hQ0 (m : ℝ)
      ((x : ℝ) - c / (Q : ℝ))]
  have hR : (∑' x : ℤ, ENNReal.ofReal (‖H ((Q : ℝ) * (x : ℝ) + (m : ℝ))‖ ^ r))
      = ∑' x : ℤ, ENNReal.ofReal (‖Ht (x : ℝ)‖ ^ r) := rfl
  rw [hL, hR]
  exact key

/-- **The corrected `hLattice`** (see `LATTICE_PRINCIPLE_STATUS.md`): the lattice
maximal-vs-values principle for continuous band-limited functions.  This is the binder used in
`Submission/Work/Maximal/` with the necessary hypothesis `Continuous H` added (without it the
statement is false).

Assembly: `mstLatticePrinciple_of_core` (the `(Q,m,c)` rescaling, proved here) applied to
`lat_unit_lattice_core` with the two lattice inputs `lat_hlMax_kernel_estimate_uniform`
(the two-regime domination) and `latDiscMaxC_lintegral_rpow_le` (the centred discrete
Hardy--Littlewood maximal inequality, from its one-sided form `latDiscMax_lintegral_rpow_le`). -/
theorem mstLatticePrinciple {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ → ℂ) (δ : ℝ), 0 < δ → Continuous H →
      MeasureTheory.Integrable H →
      (∀ ξ : ℝ, δ < |ξ| → FourierTransform.fourier H ξ = 0) →
      ∀ (Q : ℕ), 1 ≤ Q → δ * (Q : ℝ) ≤ 1 / 4 → ∀ (m : ℤ) (c : ℝ),
        (∑' x : ℤ, (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖)
            ((Q : ℝ) * (x : ℝ) + (m : ℝ) - c)) ^ r)
          ≤ ENNReal.ofReal (C ^ r) *
            ∑' x : ℤ, ENNReal.ofReal (‖H ((Q : ℝ) * (x : ℝ) + (m : ℝ))‖ ^ r) :=
  mstLatticePrinciple_of_core hr
    (lat_unit_lattice_core hr
      (lat_hlMax_kernel_estimate_uniform (ψ := latPsi) latPsi_one latPsi_zero)
      (latDiscMaxC_lintegral_rpow_le hr (latDiscMax_lintegral_rpow_le hr)))

end

end Work.BourgainPlan.Maximal

