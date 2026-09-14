import Submission.NBody.MarchalModelTwoSided
import Submission.NBody.MarchalGoodDirection
import Submission.NBody.MarchalModelInstantiate
import Submission.Commons.Analysis.Integral.integral_theta_model_potential_realpow_le_strict

/-!
# The two-sided model negativity, with the potential bound discharged

This is the fully instantiated version of `exists_model_dir_negative_two_sided_avoid`: the potential
bounds `hpotR`, `hpotL` are produced from the commons lemma
`Commons.Analysis.Integral.integral_theta_model_potential_realpow_le_strict` (as in
`exists_model_dir_negative_of_blowup`), and the exceptional set is the union over the cluster pairs
of the "bad" directions (parallel to a limit pair separation), which is null by
`volume_badSet_eq_zero`.  The conclusion is the **good direction** of the symmetric bump: a single
displacement `δ = ρ • circleDir e f θ` which is not parallel to any pair separation of either limit
shape, and for which the sum of the two sides' model action differences is strictly negative.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The two-sided model negativity with the good direction**, fully instantiated. -/
theorem exists_model_dir_two_sided_of_blowup {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) (hne : (k.erase i₀).Nonempty)
    {κR κL T : ℝ} (hκR : 0 < κR) (hκL : 0 < κL) (hT : 0 < T) (sbarR sbarL : EN E N)
    (hsbarncR : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbarR i ≠ sbarR j)
    (hsbarncL : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbarL i ≠ sbarL j)
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0)
    {ρmax : ℝ} (hρmax : 0 < ρmax) (hρmaxT : ρmax ≤ T / 2)
    (hsmallR : ∀ j ∈ k.erase i₀,
      ρmax / (Real.sqrt κR * (T / 2) ^ ((2:ℝ)/3) * ‖sbarR i₀ - sbarR j‖) ≤ 1/8)
    (hsmallL : ∀ j ∈ k.erase i₀,
      ρmax / (Real.sqrt κL * (T / 2) ^ ((2:ℝ)/3) * ‖sbarL i₀ - sbarL j‖) ≤ 1/8) :
    ∃ ρ > (0:ℝ), ρ ≤ ρmax ∧ ∃ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      (∀ j ∈ k.erase i₀, (inner ℝ (sbarR i₀ - sbarR j) (ρ • circleDir e f θ))^2
          < ‖sbarR i₀ - sbarR j‖^2 * ‖ρ • circleDir e f θ‖^2)
      ∧ (∀ j ∈ k.erase i₀, (inner ℝ (sbarL i₀ - sbarL j) (ρ • circleDir e f θ))^2
          < ‖sbarL i₀ - sbarL j‖^2 * ‖ρ • circleDir e f θ‖^2)
      ∧ modelDiff m k i₀ κR sbarR T (ρ • circleDir e f θ)
          + modelDiff m k i₀ κL sbarL T (ρ • circleDir e f θ) < 0 := by
  classical
  -- non-degeneracy of the pair separations
  have hzR : ∀ j ∈ k.erase i₀, 0 < ‖sbarR i₀ - sbarR j‖ := by
    intro j hj
    rw [Finset.mem_erase] at hj
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hsbarncR i₀ hi₀ j hj.2 hj.1.symm h))
  have hzL : ∀ j ∈ k.erase i₀, 0 < ‖sbarL i₀ - sbarL j‖ := by
    intro j hj
    rw [Finset.mem_erase] at hj
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hsbarncL i₀ hi₀ j hj.2 hj.1.symm h))
  -- the potential bounds, one per side
  have hpotR : ∀ ρ ∈ Set.Ioo (0:ℝ) ρmax,
      (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        modelPotVal m k i₀ κR sbarR T (ρ • circleDir e f θ)
          ≤ - potGainA m k i₀ κR sbarR * ρ ^ ((1:ℝ)/2)
            + potGainB m k i₀ κR T sbarR * ρ ^ 2 := by
    intro ρ hρ
    have hρpos : 0 < ρ := hρ.1
    have hρT2 : ρ ≤ T / 2 := le_trans hρ.2.le hρmaxT
    have hρT : ρ < T := by linarith
    refine circleAvg_modelPotVal_bound hm hκR hT hρpos hρT2 sbarR e f he hf hef hzR ?_
    intro j hj
    have hzj : 0 < ‖sbarR i₀ - sbarR j‖ := hzR j hj
    have hsmall : ρ / (Real.sqrt κR * (T - ρ) ^ ((2:ℝ)/3) * ‖sbarR i₀ - sbarR j‖) ≤ 1/8 :=
      le_trans (div_le_div_ramp (Real.sqrt_pos.mpr hκR) hT hρpos hρmax hρ.2.le hρmaxT hzj)
        (hsmallR j hj)
    have hcomm := Commons.Analysis.Integral.integral_theta_model_potential_realpow_le_strict
      (E := E) e f (sbarR i₀ - sbarR j) he hf hef (c := Real.sqrt κR) (T := T) (ρ := ρ)
      (z := ‖sbarR i₀ - sbarR j‖) (Real.sqrt_pos.mpr hκR) hT hρpos hρT rfl hzj hsmall
    refine circleAvg_potPairVal_le hρpos he hf hef rfl ?_
    rw [phiWeight]
    exact hcomm
  have hpotL : ∀ ρ ∈ Set.Ioo (0:ℝ) ρmax,
      (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        modelPotVal m k i₀ κL sbarL T (ρ • circleDir e f θ)
          ≤ - potGainA m k i₀ κL sbarL * ρ ^ ((1:ℝ)/2)
            + potGainB m k i₀ κL T sbarL * ρ ^ 2 := by
    intro ρ hρ
    have hρpos : 0 < ρ := hρ.1
    have hρT2 : ρ ≤ T / 2 := le_trans hρ.2.le hρmaxT
    have hρT : ρ < T := by linarith
    refine circleAvg_modelPotVal_bound hm hκL hT hρpos hρT2 sbarL e f he hf hef hzL ?_
    intro j hj
    have hzj : 0 < ‖sbarL i₀ - sbarL j‖ := hzL j hj
    have hsmall : ρ / (Real.sqrt κL * (T - ρ) ^ ((2:ℝ)/3) * ‖sbarL i₀ - sbarL j‖) ≤ 1/8 :=
      le_trans (div_le_div_ramp (Real.sqrt_pos.mpr hκL) hT hρpos hρmax hρ.2.le hρmaxT hzj)
        (hsmallL j hj)
    have hcomm := Commons.Analysis.Integral.integral_theta_model_potential_realpow_le_strict
      (E := E) e f (sbarL i₀ - sbarL j) he hf hef (c := Real.sqrt κL) (T := T) (ρ := ρ)
      (z := ‖sbarL i₀ - sbarL j‖) (Real.sqrt_pos.mpr hκL) hT hρpos hρT rfl hzj hsmall
    refine circleAvg_potPairVal_le hρpos he hf hef rfl ?_
    rw [phiWeight]
    exact hcomm
  -- the exceptional set is null
  set Bs : Set ℝ := (⋃ j ∈ (k.erase i₀ : Set (Fin N)),
      ({θ : ℝ | (inner ℝ (sbarR i₀ - sbarR j) (circleDir e f θ))^2 = ‖sbarR i₀ - sbarR j‖^2}
        ∪ {θ : ℝ | (inner ℝ (sbarL i₀ - sbarL j) (circleDir e f θ))^2
            = ‖sbarL i₀ - sbarL j‖^2})) with hBs
  have hBnull : volume Bs = 0 := by
    rw [hBs, MeasureTheory.measure_biUnion_null_iff (k.erase i₀).finite_toSet.countable]
    intro j hj
    rw [Finset.mem_coe] at hj
    have huR : sbarR i₀ - sbarR j ≠ 0 := sub_ne_zero.mpr fun h =>
      hsbarncR i₀ hi₀ j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm h
    have huL : sbarL i₀ - sbarL j ≠ 0 := sub_ne_zero.mpr fun h =>
      hsbarncL i₀ hi₀ j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm h
    exact measure_union_null (volume_badSet_eq_zero huR he hf hef)
      (volume_badSet_eq_zero huL he hf hef)
  obtain ⟨ρ, hρpos, hρle, θ, hθI, hθB, hneg⟩ :=
    exists_model_dir_negative_two_sided_avoid hm hi₀ hκR hκL hT sbarR sbarL e f he hf hef
      hBnull (AR := potGainA m k i₀ κR sbarR) (BR := potGainB m k i₀ κR T sbarR)
      (AL := potGainA m k i₀ κL sbarL) (BL := potGainB m k i₀ κL T sbarL)
      (add_pos (potGainA_pos hm hκR sbarR hne hzR) (potGainA_pos hm hκL sbarL hne hzL))
      (potGainB_nonneg hm hκR hT sbarR) (potGainB_nonneg hm hκL hT sbarL)
      hρmax hρmaxT hpotR hpotL
  refine ⟨ρ, hρpos, hρle, θ, hθI, ?_, ?_, hneg⟩
  · intro j hj
    have hmem : ({θ : ℝ | (inner ℝ (sbarR i₀ - sbarR j) (circleDir e f θ))^2
          = ‖sbarR i₀ - sbarR j‖^2}
        ∪ {θ : ℝ | (inner ℝ (sbarL i₀ - sbarL j) (circleDir e f θ))^2
            = ‖sbarL i₀ - sbarL j‖^2}) ⊆ Bs := by
      rw [hBs]
      exact Set.subset_iUnion₂_of_subset j (Finset.mem_coe.mpr hj) (subset_refl _)
    exact goodDir_of_notMem_badSet (u := sbarR i₀ - sbarR j)
      (sub_ne_zero.mpr fun h =>
        hsbarncR i₀ hi₀ j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm h)
      he hf hef hρpos (fun hmem' => hθB (hmem (Or.inl hmem')))
  · intro j hj
    have hmem : ({θ : ℝ | (inner ℝ (sbarR i₀ - sbarR j) (circleDir e f θ))^2
          = ‖sbarR i₀ - sbarR j‖^2}
        ∪ {θ : ℝ | (inner ℝ (sbarL i₀ - sbarL j) (circleDir e f θ))^2
            = ‖sbarL i₀ - sbarL j‖^2}) ⊆ Bs := by
      rw [hBs]
      exact Set.subset_iUnion₂_of_subset j (Finset.mem_coe.mpr hj) (subset_refl _)
    refine goodDir_of_notMem_badSet (u := sbarL i₀ - sbarL j)
      (sub_ne_zero.mpr fun h =>
        hsbarncL i₀ hi₀ j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm h)
      he hf hef hρpos ?_
    intro hmem'
    exact hθB (hmem (Or.inr hmem'))

end Submission.NBody
