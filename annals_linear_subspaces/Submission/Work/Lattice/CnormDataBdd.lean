import Mathlib
import Submission.Work.Lattice.CnormLevel
import Submission.Work.Lattice.CnormIntegral
import Submission.Work.Dani.LiftFamily
import Submission.Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_comp_isometry

/-!
# The max-norm flow data is bounded below

The max-norm data of the flow, `flowMaxData Λ₀ ℓ t j hjd`, is an infimum of `log cnorm` of flowed
wedges.  To use the Lipschitz bounds `CnormLevel.flowMaxData_shift_le/ge` and the continuity
`CnormLevel.continuous_flowMaxData` one must know that it is bounded below; this module supplies
the bound for the relevant `Λ₀ = g(ℤᵈ)` with `g` a linear isometry (the §3 sheared flow lattice).

Ingredients:

* **`cnorm_eFlow_ge_floor`** — the two-sign floor for the max-norm flow:
  `e^{−|h|·j·max(1/ℓ,1/(d−ℓ))}·cnorm w ≤ cnorm (⋀^j a_h w)` for all `h ∈ ℝ`
  (for `h ≥ 0` it is `CnormLevel.cnorm_exp_neg_le`; for `h < 0` the dominant block argument
  `cnorm = sup'_u cnorm_u` + `σ_u ≤ σ_j` gives `cnorm (⋀^j a_h w) ≥ e^{h·j/(d−ℓ)}·cnorm w`);
* **`bddBelow_flowMaxDataSet_imageSpan`** — hence, for `Λ₀ = g(ℤᵈ)` (`g` a linear isometry), the
  data is bounded below: for `v` a family in `Λ₀`, `v = g ∘ m` with `m` an integer family, so
  `cnorm (⋀v) ≥ ‖⋀v‖/√(choose d j) = ‖⋀m‖/√(choose d j) ≥ 1/√(choose d j)`
  (`norm_le_sqrt_card_mul_cnorm`, `norm_iMulti_comp_isometry`, `intWedge_norm_ge_one`).

Module `Submission.Work.Lattice.CnormDataBdd`, namespace `Submission.CnormDataBdd`.
-/

noncomputable section

open LinearSubspaces Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.FlowRate
open Submission.FlowRateAsymptotic
open Submission.FlowDataMax
open Submission.CnormLevel
open Submission.CnormIntegral

namespace Submission.CnormDataBdd

variable {d : ℕ}

/-- The maximal flow exponent `j·max(1/ℓ,1/(d−ℓ))`. -/
noncomputable def rateMax (d j ℓ : ℕ) : ℝ :=
  (j : ℝ) * max (1 / (ℓ : ℝ)) (1 / (((d - ℓ : ℕ)) : ℝ))

/-- The `σ` at the zero block: `sig j ℓ 0 = −j/ℓ`. -/
lemma sig_zero_eq {j ℓ : ℕ} : sig (d := d) j ℓ 0 = -((j : ℝ) / (ℓ : ℝ)) := by
  have hsl : slope (d := d) ℓ = 1 / (ℓ : ℝ) + 1 / ((d : ℝ) - (ℓ : ℝ)) := rfl
  rw [sig, hsl]
  ring

/-- **The two-sign floor of the max-norm flow.**  For every real `h`,
`e^{−|h|·rateMax} · cnorm w ≤ cnorm (⋀^j a_h w)`. -/
theorem cnorm_eFlow_ge_floor {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d) (h : ℝ)
    (w : WK d j) :
    Real.exp (-(rateMax d j ℓ * |h|)) * cnorm hjd w ≤
      cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ h) w) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hdmR : (0 : ℝ) < (((d - ℓ : ℕ)) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hℓd)]
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hmax1 : 1 / (ℓ : ℝ) ≤ max (1 / (ℓ : ℝ)) (1 / (((d - ℓ : ℕ)) : ℝ)) := le_max_left _ _
  have hmax2 : 1 / (((d - ℓ : ℕ)) : ℝ) ≤ max (1 / (ℓ : ℝ)) (1 / (((d - ℓ : ℕ)) : ℝ)) :=
    le_max_right _ _
  have hrm1 : (j : ℝ) / (ℓ : ℝ) ≤ rateMax d j ℓ := by
    rw [rateMax, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hmax1 hj0
  have hrm2 : (j : ℝ) / (((d - ℓ : ℕ)) : ℝ) ≤ rateMax d j ℓ := by
    rw [rateMax, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hmax2 hj0
  -- the exact block decomposition and the argmax block
  rw [eFlow_eq, cnorm_map_flow (d := d) hℓ0 hℓd h hjd w, cnorm_eq_sup'_blockElem hjd w]
  obtain ⟨u0, hu0mem, hu0eq⟩ := Finset.exists_mem_eq_sup'
    (⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩ : (Finset.range (j + 1)).Nonempty)
    (fun u => cnorm hjd (blockElem (d := d) (k := j) (ℓ := ℓ) w u))
  rw [hu0eq]
  have hu0k : u0 ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu0mem)
  -- the two-sided bound on `σ_{u0}`
  have hσlo : -((j : ℝ) / (ℓ : ℝ)) ≤ sig (d := d) j ℓ u0 := by
    have h1 := sig_mono (d := d) hℓ0 hℓd (k := j) (Nat.zero_le u0)
    rwa [sig_zero_eq (d := d)] at h1
  have hσhi : sig (d := d) j ℓ u0 ≤ (j : ℝ) / (((d - ℓ : ℕ)) : ℝ) := by
    have h1 := sig_mono (d := d) hℓ0 hℓd (k := j) hu0k
    rwa [sig_self (d := d) (j := j) hℓ0 hℓd] at h1
  -- the exponent comparison
  have hexp : -(rateMax d j ℓ * |h|) ≤ h * sig (d := d) j ℓ u0 := by
    by_cases hh : 0 ≤ h
    · have h1 : h * (-(rateMax d j ℓ)) ≤ h * (-((j : ℝ) / (ℓ : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith [hrm1]) hh
      have h2 : h * (-((j : ℝ) / (ℓ : ℝ))) ≤ h * sig (d := d) j ℓ u0 :=
        mul_le_mul_of_nonneg_left hσlo hh
      have h3 : -(rateMax d j ℓ * |h|) = h * (-(rateMax d j ℓ)) := by
        rw [abs_of_nonneg hh]; ring
      rw [h3]
      linarith [h1, h2]
    · have hh' : h < 0 := lt_of_not_ge hh
      have h1 : h * rateMax d j ℓ ≤ h * ((j : ℝ) / (((d - ℓ : ℕ)) : ℝ)) :=
        mul_le_mul_of_nonpos_left hrm2 (le_of_lt hh')
      have h2 : h * ((j : ℝ) / (((d - ℓ : ℕ)) : ℝ)) ≤ h * sig (d := d) j ℓ u0 :=
        mul_le_mul_of_nonpos_left hσhi (le_of_lt hh')
      have h3 : -(rateMax d j ℓ * |h|) = h * rateMax d j ℓ := by
        rw [abs_of_neg hh']; ring
      rw [h3]
      linarith [h1, h2]
  refine le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (cnorm_nonneg hjd _)) ?_
  exact Finset.le_sup'
    (f := fun u => Real.exp (h * sig (d := d) j ℓ u) *
      cnorm hjd (blockElem (d := d) (k := j) (ℓ := ℓ) w u)) hu0mem

/-- **The max-norm flow data of `g(ℤᵈ)` (`g` a linear isometry) is bounded below.** -/
theorem bddBelow_flowMaxDataSet_imageSpan {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d)
    (hj1 : 1 ≤ j) (g : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) :
    BddBelow (flowMaxDataSet (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t j hjd) := by
  classical
  refine ⟨-(rateMax d j ℓ * |t|) - Real.log (Real.sqrt (Nat.choose d j)), ?_⟩
  rintro r ⟨v, hv, hli, rfl⟩
  -- lift to integer vectors
  obtain ⟨m, hm, hmv⟩ := Submission.LiftFamily.exists_int_lift (d := d)
    (g : RD d ≃ₗ[ℝ] RD d) j v hv
  have hvm : (fun i => g (m i)) = v := funext hmv
  have hmli : LinearIndependent ℝ m :=
    Submission.LiftFamily.linearIndependent_of_lift (d := d) (g : RD d ≃ₗ[ℝ] RD d) hmv hli
  -- the Euclidean wedge of `v` has norm ≥ 1
  have hmz : ∀ r : Fin j, ∀ t' : Fin d, ∃ z : ℤ, m r t' = z :=
    fun r t' => Submission.CnormIntegral.intPoints_coord_int (m r) (hm r) t'
  have hnorm1 : (1 : ℝ) ≤ ‖exteriorPower.ιMulti ℝ j v‖ := by
    have h := Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one hj1 m hmz hmli
    have heq : ‖exteriorPower.ιMulti ℝ j v‖ = ‖exteriorPower.ιMulti ℝ j m‖ := by
      rw [← hvm, Commons.Analysis.InnerProductSpace.norm_iMulti_comp_isometry g m]
    rwa [heq]
  -- the max norm dominates the Euclidean norm up to `√(choose d j)`
  have hCpos : (0 : ℝ) < Real.sqrt (Nat.choose d j) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos hjd)
  have hcnorm_ge : ‖exteriorPower.ιMulti ℝ j v‖ / Real.sqrt (Nat.choose d j) ≤
      cnorm hjd (exteriorPower.ιMulti ℝ j v) := by
    have h := norm_le_sqrt_card_mul_cnorm (d := d) hjd (exteriorPower.ιMulti ℝ j v)
    rw [div_le_iff₀ hCpos]
    linarith [h]
  have hOne : 1 / Real.sqrt (Nat.choose d j) ≤ cnorm hjd (exteriorPower.ιMulti ℝ j v) := by
    refine le_trans ?_ hcnorm_ge
    rw [div_le_div_iff₀ hCpos hCpos, one_mul]
    exact le_mul_of_one_le_left hCpos.le hnorm1
  -- positivity of the wedge and the floor bound
  have hwne : exteriorPower.ιMulti ℝ j v ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent v hli
  have hwpos : 0 < cnorm hjd (exteriorPower.ιMulti ℝ j v) :=
    cnorm_pos_of_ne_zero hjd _ hwne
  have hfloor := cnorm_eFlow_ge_floor (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd t
    (exteriorPower.ιMulti ℝ j v)
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) hwpos) hfloor
  rw [Real.log_mul (Real.exp_ne_zero _) hwpos.ne', Real.log_exp] at hlog
  -- `log cnorm (⋀v) ≥ log (1/√C) = −log √C`
  have hlog2 : -Real.log (Real.sqrt (Nat.choose d j)) ≤
      Real.log (cnorm hjd (exteriorPower.ιMulti ℝ j v)) := by
    have := Real.log_le_log (by positivity : (0:ℝ) < 1 / Real.sqrt (Nat.choose d j)) hOne
    rwa [Real.log_div one_ne_zero hCpos.ne', Real.log_one, zero_sub] at this
  linarith [hlog, hlog2]


/-- The shifted-data bounds for the isometry-image lattice, with the boundedness hypothesis
discharged. -/
theorem flowMaxData_imageSpan_shift_le {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d)
    (hj1 : 1 ≤ j) (g : RD d ≃ₗᵢ[ℝ] RD d) {t h : ℝ} (hh : 0 ≤ h) :
    flowMaxData (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ (t + h) j hjd ≤
      flowMaxData (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t j hjd +
        h * (j : ℝ) / ((d - ℓ : ℕ) : ℝ) :=
  flowMaxData_shift_le (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd _ 
    (fun t => bddBelow_flowMaxDataSet_imageSpan (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd hj1 g t)
    hh

theorem flowMaxData_imageSpan_shift_ge {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d)
    (hj1 : 1 ≤ j) (g : RD d ≃ₗᵢ[ℝ] RD d) {t h : ℝ} (hh : 0 ≤ h) :
    flowMaxData (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t j hjd ≤
      flowMaxData (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ (t + h) j hjd +
        h * (j : ℝ) / (ℓ : ℝ) :=
  flowMaxData_shift_ge (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd _
    (fun t => bddBelow_flowMaxDataSet_imageSpan (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd hj1 g t)
    hh

/-- **Continuity of the max-norm data of the §3 sheared flow lattice**, with the boundedness
hypothesis discharged. -/
theorem continuous_flowMaxData_imageSpan {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d)
    (hj1 : 1 ≤ j) (g : RD d ≃ₗᵢ[ℝ] RD d) :
    Continuous fun t : ℝ =>
      flowMaxData (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t j hjd :=
  continuous_flowMaxData (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd _
    (fun t => bddBelow_flowMaxDataSet_imageSpan (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd hj1 g t)


end Submission.CnormDataBdd

end
