import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi
import Submission.Work.HP.IntForm
import Submission.Work.HP.PFCountDefs
import Submission.Work.HP.PFAssembly
import Submission.Work.HP.HP2.frontier_tube_le
import Submission.Work.HP.HP2.cone_region_lower
import Submission.Work.HP.HP2.Psi_lip_sharp
import Submission.Work.HP.HP2.Psi_sublevelV2
import Submission.Work.HP.HP2.tube_ok_threshold
import Submission.Work.HP.HP2.class_count_lower
import Submission.Work.HP.HP2.primConeSet_sigma_lower
import Submission.Work.HP.HP2.NVloc_ge_ncard
import Submission.Work.HP.HP2.PF_eventually
import Submission.Work.HP.tendsto_wOf_atTop

/-!
# The product-factors bound (`Work.HP.product_factors`)

This instantiates `Work.HP.product_factors_of` (`Submission/Work/HP/PFAssembly.lean`) with the
concrete ingredients of node N13:

* `Work.HP.HP2.frontier_tube_le` (from `Psi_sublevel` and `Psi_lip_sharp`) and
  `Work.HP.HP2.cone_region_lower` give the tube threshold `Work.HP.HP2.tube_ok_threshold`,
* `Work.HP.HP2.class_count_lower` is the per-residue-class lower bound (Möbius inversion,
  `grid_coset_lower`/`grid_coset_upper`),
* `Work.HP.HP2.primConeSet_sigma_lower` sums it over the `σ W^n` good classes,
* `Work.HP.HP2.NVloc_ge_ncard` bounds `N_V^loc` from below by the number of cone lattice points,
* `Work.HP.HP2.PF_eventually` supplies the eventual threshold,
* and the additive term `C/(Aφ)^{1/n}` of the paper's statement is added for free (`C > 0`).

The result is exactly the hypothesis `hPF` of `Work.HP.prop2_of_pf`.
-/

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Finset
open scoped BigOperators Pointwise

namespace Work.HP

open HP2

/-- **The product-factors bound (paper's Lemma 5.1).**  For primitive `a` with `‖a‖ ≤ A`, real
solubility, `A ≥ A₀` and `φ > 1`,
`σ(a; W(w(Aφ))) · τ(a; log (Aφ)) ≪ N_V^loc(Aφ)/φ + (Aφ)^{-1/n}`. -/
theorem product_factors (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ C A₀ : ℝ, 0 < C ∧ ∀ A φ : ℝ, A₀ ≤ A → 1 < φ → ∀ a : Mon d n → ℤ,
      IsPrim a → eNorm a ≤ A → RealSol d n a →
        sigmaLoc d n a (bigW (wOf (A * φ))) * tauArch d n (toR a) (Real.log (A * φ))
          ≤ C * NVloc d n a (A * φ) / φ + C / (A * φ) ^ ((1 : ℝ) / (n : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  have hn1 : 1 ≤ n := by omega
  obtain ⟨Csub, Ksub, hCsub, hKsub, hsub⟩ := Psi_sublevel d n hd1 hn1
  obtain ⟨Clip, hClip, hlip⟩ := Psi_lip_sharp d n hd1
  obtain ⟨Cfront, hCfront, hfront⟩ :=
    frontier_tube_le d n hd1 Csub Ksub Clip hCsub hKsub hClip hsub hlip
  obtain ⟨ccone, hccone, hcone⟩ := cone_region_lower d n hd1
  obtain ⟨m, κ, A₀₁, hκ1, -, htube⟩ :=
    tube_ok_threshold d n Cfront ccone Ksub hCfront hKsub hccone hfront hcone
  have htubef : ∀ᶠ B in atTop, ∀ (a : Mon d n → ℤ) (T : ℝ),
      a ≠ 0 → RealSol d n a → 1 ≤ T →
      (bigW (wOf B) : ℝ) * (Real.log B) ^ m * κ ≤ T →
      TubeOk d n a (Real.log B) T (bigW (wOf B) : ℝ) :=
    Filter.eventually_atTop.mpr ⟨A₀₁, htube⟩
  have hNV : ∀ (a : Mon d n → ℤ) (B R : ℝ),
      R = B ^ (1 / ((n : ℝ) + 1 - d)) → 0 < R → 0 < eNorm a →
      (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) *
        (((primConeSet d n a (Real.log B) R (bigW (wOf B))).ncard : ℝ) /
          (Real.sqrt ((NN d n : ℕ) : ℝ) * R ^ d)) ≤ NVloc d n a B := by
    intro a B R hR hRpos hepos
    have h := NVloc_ge_ncard d n a B R hR hRpos hepos
    rw [mul_div_assoc] at h
    simpa only [primConeSet] using h
  have hevent : ∀ (m : ℕ) (κ : ℝ), 0 < κ → ∀ᶠ B in atTop,
      1 ≤ Real.log B ∧ 8 ≤ wOf B ∧
        (bigW (wOf B) : ℝ) * (Real.log B) ^ m * κ ≤ B ^ (1 / ((n : ℝ) + 1 - d)) := by
    intro m κ hκ
    filter_upwards [PF_eventually d n hdn m κ hκ,
      tendsto_wOf_atTop.eventually_ge_atTop (8 : ℝ)] with B h1 h2
    exact ⟨h1.1, h2, h1.2⟩
  obtain ⟨C, A₀, hC, hmain⟩ :=
    product_factors_of d n hd hdn m κ hκ1 htubef
      (class_count_lower d n hd hdn m κ hκ1 ccone hccone hcone)
      (primConeSet_sigma_lower d n hd hdn) hNV hevent
  refine ⟨C, max A₀ 1, hC, ?_⟩
  intro A φ hA hφ a hprim hnorm hsol
  have hA0 : A₀ ≤ A := le_trans (le_max_left _ _) hA
  have hA1 : (1 : ℝ) ≤ A := le_trans (le_max_right _ _) hA
  have hφpos : 0 < φ := lt_trans zero_lt_one hφ
  have h := hmain A φ hA0 hφ a hprim hnorm hsol
  have hAφpos : 0 < A * φ := by nlinarith
  have hpos : 0 ≤ C / (A * φ) ^ ((1 : ℝ) / (n : ℝ)) :=
    div_nonneg hC.le (Real.rpow_nonneg hAφpos.le _)
  linarith

end Work.HP
