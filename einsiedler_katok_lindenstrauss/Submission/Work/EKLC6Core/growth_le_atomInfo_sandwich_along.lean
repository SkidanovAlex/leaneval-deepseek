import Mathlib
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.box_mass_asymptotic_condExp_along
import Submission.Work.EKLC6Core.HcondSig_eq_growth_free
import Submission.Work.EKLC6Core.radius_independence_along
import Submission.Work.EKLC6Core.orbit_telescope_gl_along

/-!
# `EKLC6Core.growth_le_atomInfo_sandwich_along`

The good-time sandwich of Pisa 7.18/7.34 in its `MeasurePreserving`, single-direction form:
`Work.EKLC6Core.growth_le_atomInfo_sandwich_mp` with the full `A`-covariance
`ACovariant ν X''` replaced by the covariance along the integer multiples of the single
direction `t` (`Work.EKLC6Core.ACovariantAlong ν t X''`).

The proof is line-for-line the one of `growth_le_atomInfo_sandwich_mp`; the two
covariance-carrying inputs (`radius_independence` and the orbit telescoping of Pisa 7.34) are
replaced by their `_along` forms:

* `Work.EKLC6Core.radius_independence_along`,
* `Work.EKLC6Core.orbit_telescope_gl_along` (in the `aShift` spelling).

Everything else in that proof (Birkhoff along `aDiag t ·`, the radius sandwich `V_mass_facts_gl`,
the positivity of the shape mass `shape_mass_pos`, the limit algebra) uses the covariance
nowhere and is copied verbatim.

-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- `orbit_telescope_gl_along` rephrased with `aShift t = (fun y => aDiag t • y)` (the two
statements are definitionally equal; the assembly below is written against the `aShift`
spelling, as in `Work.EKLC6Core.HcondSigFree.orbit_telescope_gl_mp_shift`). -/
theorem orbit_telescope_gl_along_shift {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') (hX'' : μ X''ᶜ = 0)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, ∀ n : ℕ,
      (∑ j ∈ Finset.range n, atomInfo A U ν t ((aShift t)^[j] x))
        = Real.log ((ν ((aShift t)^[n] x) (shape A U ((aShift t)^[n] x))).toReal)
          - Real.log ((ν x (shape A U x)).toReal)
          + ∑ j ∈ Finset.range n, growthFun U ν t ((aShift t)^[j+1] x) := by
  exact orbit_telescope_gl_along (μ := μ) t hL hU hcov hX'' hmp hplaq hZ

theorem growth_le_atomInfo_sandwich_along {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') (hX'' : μ X''ᶜ = 0)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun U ν t) μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A)
    (hdec : MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hZ : μ Zᶜ = 0)
    (hmeas_atom : AEMeasurable (Work.EKLC6Core.atomInfo A U ν t) μ)
    {Y : ℕ → Set Work.EKLContract.X3} {δ R : ℕ → ℝ}
    (hYmeas : ∀ k : ℕ, @MeasurableSet Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 (Y k))
    (hδ : ∀ k, 0 < δ k) (hR : ∀ k, 0 < R k)
    (hY : ∀ (k : ℕ) (y : Work.EKLContract.X3), y ∈ Y k →
      (Work.EKLContract.V (δ k) ∩ (U : Set Work.EKLContract.SL3)) ⊆
          Work.EKLContract.shape A U y ∧
        Work.EKLContract.shape A U y ⊆ Work.EKLContract.V (R k))
    (hvisit : ∀ᵐ x ∂μ, ∃ k : ℕ, ∃ᶠ n in Filter.atTop,
      (Work.EKLContract.aDiag t ^ n) • x ∈ Y k) :
    ENNReal.ofReal (MeasureTheory.integral μ (fun x => Work.EKLC6Core.growthFun U ν t x)) ≤
      MeasureTheory.lintegral μ (fun x => ENNReal.ofReal (Work.EKLC6Core.atomInfo A U ν t x)) := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  rcases eq_or_ne (∫⁻ x, ENNReal.ofReal (atomInfo A U ν t x) ∂μ) ⊤ with htop | hne
  · rw [htop]; exact le_top
  have hAi_nn : 0 ≤ᵐ[μ] (fun x : X3 => atomInfo A U ν t x) :=
    Filter.Eventually.of_forall (fun x => atomInfo_nonneg_gl hdec x)
  have hAi_aesm : AEStronglyMeasurable (fun x : X3 => atomInfo A U ν t x) μ :=
    hmeas_atom.aestronglyMeasurable
  have hAi_int : Integrable (fun x : X3 => atomInfo A U ν t x) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hAi_aesm hAi_nn).mp hne
  have hbg : Integrable (fun x : X3 => growthFun U ν t x) μ := hint
  have hbAi := Work.EKLComp.birkhoff_all μ (aShift t) hmp
    (fun x : X3 => atomInfo A U ν t x) hAi_int
  have hbg' := Work.EKLComp.birkhoff_all μ (aShift t) hmp
    (fun x : X3 => growthFun U ν t x) hbg
  have hTpow := aShift_pow_apply (t := t)
  have hRI : ∀ᵐ x ∂μ, ∀ k : ℕ,
      (Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
          ((ν ((aShift t)^[n] x) (V (δ k) ∩ (U : Set SL3))).toReal))
          Filter.atTop (nhds 0)) ∧
      (Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
          ((ν ((aShift t)^[n] x) (V (R k) ∩ (U : Set SL3))).toReal))
          Filter.atTop (nhds 0)) := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    have h1 := radius_independence_along (μ := μ) t hL hU hcov hX'' hmp hint hcontr (hδ k)
    have h2 := radius_independence_along (μ := μ) t hL hU hcov hX'' hmp hint hcontr (hR k)
    filter_upwards [h1, h2] with x hx1 hx2
    exact ⟨hx1.congr (fun n => by rw [hTpow n x]), hx2.congr (fun n => by rw [hTpow n x])⟩
  have hkey : condExp (MeasurableSpace.invariants (aShift t)) μ
        (fun x : X3 => atomInfo A U ν t x) =ᵐ[μ]
      condExp (MeasurableSpace.invariants (aShift t)) μ (fun x : X3 => growthFun U ν t x) := by
    have hAll : ∀ᵐ x ∂μ, ∀ j : ℕ, (aShift t)^[j] x ∈ X' ∩ X'' ∩ Z := by
      rw [MeasureTheory.ae_all_iff]
      intro j
      have hj : MeasurePreserving ((aShift t)^[j]) μ μ := hmp.iterate j
      have h1 : ∀ᵐ x ∂μ, (aShift t)^[j] x ∈ X' :=
        hj.quasiMeasurePreserving.ae (by rw [MeasureTheory.ae_iff]; exact hL.conull)
      have h2 : ∀ᵐ x ∂μ, (aShift t)^[j] x ∈ X'' :=
        hj.quasiMeasurePreserving.ae (by rw [MeasureTheory.ae_iff]; exact hX'')
      have h3 : ∀ᵐ x ∂μ, (aShift t)^[j] x ∈ Z :=
        hj.quasiMeasurePreserving.ae (by rw [MeasureTheory.ae_iff]; exact hZ)
      filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
      exact ⟨⟨hx1, hx2⟩, hx3⟩
    have hTel := orbit_telescope_gl_along_shift (μ := μ) t hL hU hcov hX'' hmp hplaq hZ
    filter_upwards [hbAi, hbg', hTel, hRI, hvisit, hAll] with x hbAi_x hbg_x hTel_x hRI_x hvis hxg
    obtain ⟨k, hfreq⟩ := hvis
    have hfreq' : ∀ N : ℕ, ∃ n : ℕ, N + 1 ≤ n ∧ (aDiag t ^ n) • x ∈ Y k :=
      fun N => (Filter.frequently_atTop).mp hfreq (N + 1)
    choose φ hφ using hfreq'
    have hφmemA : ∀ n : ℕ, (aDiag t ^ φ n) • x ∈ Y k := fun n => (hφ n).2
    have hφmem : ∀ n : ℕ, (aShift t)^[φ n] x ∈ Y k := fun n => by
      rw [hTpow]; exact hφmemA n
    have hφtop : Filter.Tendsto φ Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      exact ⟨b, fun a ha => le_trans ha (le_trans (Nat.le_succ a) (hφ a).1)⟩
    have hLim1 : Filter.Tendsto (fun n : ℕ => Work.EKLComp.Birkhoff.birkA (aShift t)
        (fun x : X3 => atomInfo A U ν t x) (φ n) x) Filter.atTop
        (nhds (condExp (MeasurableSpace.invariants (aShift t)) μ
          (fun x : X3 => atomInfo A U ν t x) x)) := hbAi_x.comp hφtop
    have hsumg : ∀ n : ℕ, (∑ j ∈ Finset.range (φ n), growthFun U ν t ((aShift t)^[j+1] x))
        = ((φ n : ℝ) + 1) * Work.EKLComp.Birkhoff.birkA (aShift t)
            (fun x : X3 => growthFun U ν t x) (φ n + 1) x - growthFun U ν t x := by
      intro n
      have hcast : ((φ n + 1 : ℕ) : ℝ) = (φ n : ℝ) + 1 := by push_cast; ring
      rw [Work.EKLComp.Birkhoff.birkA_def, hcast, Finset.sum_range_succ']
      simp only [Function.iterate_zero_apply]
      have hne : ((φ n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have hest : ∀ n : ℕ, Work.EKLComp.Birkhoff.birkA (aShift t)
          (fun x : X3 => atomInfo A U ν t x) (φ n) x
        = ((φ n : ℝ)⁻¹ * ((φ n : ℝ) + 1)) * Work.EKLComp.Birkhoff.birkA (aShift t)
            (fun x : X3 => growthFun U ν t x) (φ n + 1) x
          + (φ n : ℝ)⁻¹ * (Real.log ((ν ((aShift t)^[φ n] x)
                (shape A U ((aShift t)^[φ n] x))).toReal)
              - Real.log ((ν x (shape A U x)).toReal) - growthFun U ν t x) := by
      intro n
      have htel := hTel_x (φ n)
      rw [Work.EKLComp.Birkhoff.birkA_def]
      rw [show (∑ k ∈ Finset.range (φ n),
            (fun x : X3 => atomInfo A U ν t x) ((aShift t)^[k] x))
          = ∑ k ∈ Finset.range (φ n), atomInfo A U ν t ((aShift t)^[k] x) from rfl, htel]
      rw [hsumg n]
      ring
    have hφinv_nn : ∀ n : ℕ, (0 : ℝ) ≤ (φ n : ℝ)⁻¹ :=
      fun n => inv_nonneg.mpr (Nat.cast_nonneg _)
    have hψlim : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * Real.log
        ((ν ((aShift t)^[φ n] x) (shape A U ((aShift t)^[φ n] x))).toReal))
        Filter.atTop (nhds 0) := by
      have hlow : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * Real.log
          ((ν ((aShift t)^[φ n] x) (V (δ k) ∩ (U : Set SL3))).toReal))
          Filter.atTop (nhds 0) := (hRI_x k).1.comp hφtop
      have hup : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * Real.log
          ((ν ((aShift t)^[φ n] x) (V (R k) ∩ (U : Set SL3))).toReal))
          Filter.atTop (nhds 0) := (hRI_x k).2.comp hφtop
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup ?_ ?_
      · intro n
        have hy : (aShift t)^[φ n] x ∈ Y k := hφmem n
        have hgood : (aShift t)^[φ n] x ∈ X' ∩ X'' ∩ Z := hxg (φ n)
        have hbox := V_mass_facts_gl hL hgood.1.1 (hδ k)
        have hspos := shape_mass_pos hL hplaq hgood.1.1 hgood.2
        have hle : (ν ((aShift t)^[φ n] x) (V (δ k) ∩ (U : Set SL3))).toReal
            ≤ (ν ((aShift t)^[φ n] x) (shape A U ((aShift t)^[φ n] x))).toReal :=
          ENNReal.toReal_mono (ne_of_lt hspos.2) (measure_mono (hY k _ hy).1)
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (ENNReal.toReal_pos (ne_of_gt hbox.2.1) (ne_of_lt hbox.2.2)) hle)
          (hφinv_nn n)
      · intro n
        have hy : (aShift t)^[φ n] x ∈ Y k := hφmem n
        have hgood : (aShift t)^[φ n] x ∈ X' ∩ X'' ∩ Z := hxg (φ n)
        have hbox := V_mass_facts_gl hL hgood.1.1 (hR k)
        have hspos := shape_mass_pos hL hplaq hgood.1.1 hgood.2
        have hle : ν ((aShift t)^[φ n] x) (shape A U ((aShift t)^[φ n] x))
            ≤ ν ((aShift t)^[φ n] x) (V (R k) ∩ (U : Set SL3)) := by
          rw [hbox.1]
          exact measure_mono (hY k _ hy).2
        have hle' : (ν ((aShift t)^[φ n] x) (shape A U ((aShift t)^[φ n] x))).toReal
            ≤ (ν ((aShift t)^[φ n] x) (V (R k) ∩ (U : Set SL3))).toReal :=
          ENNReal.toReal_mono (ne_of_lt hbox.2.2) hle
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (ENNReal.toReal_pos (ne_of_gt hspos.1) (ne_of_lt hspos.2)) hle')
          (hφinv_nn n)
    have hcastφ : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hφtop
    have h_inv : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
      (hcastφ.const_div_atTop 1).congr (fun n => one_div (φ n : ℝ))
    have hβ : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * ((φ n : ℝ) + 1)) Filter.atTop
        (nhds 1) := by
      have hone : Filter.Tendsto (fun n : ℕ => (1 : ℝ) + (φ n : ℝ)⁻¹) Filter.atTop
          (nhds 1) := by simpa using tendsto_const_nhds.add h_inv
      refine hone.congr' (Filter.Eventually.of_forall (fun n => ?_))
      have hne : (φ n : ℝ) ≠ 0 := by
        have h : 0 < φ n := by have h1 := (hφ n).1; omega
        exact_mod_cast h.ne'
      field_simp
    have hΦtop : Filter.Tendsto (fun n : ℕ => φ n + 1) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      exact ⟨b, fun a ha => by have h := (hφ a).1; omega⟩
    have hB : Filter.Tendsto (fun n : ℕ => Work.EKLComp.Birkhoff.birkA (aShift t)
        (fun x : X3 => growthFun U ν t x) (φ n + 1) x) Filter.atTop
        (nhds (condExp (MeasurableSpace.invariants (aShift t)) μ
          (fun x : X3 => growthFun U ν t x) x)) := hbg_x.comp hΦtop
    have htail : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * (Real.log
          ((ν ((aShift t)^[φ n] x) (shape A U ((aShift t)^[φ n] x))).toReal)
        - Real.log ((ν x (shape A U x)).toReal) - growthFun U ν t x)) Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ *
          (Real.log ((ν x (shape A U x)).toReal) + growthFun U ν t x)) Filter.atTop (nhds 0) := by
        have h := h_inv.mul_const (Real.log ((ν x (shape A U x)).toReal) + growthFun U ν t x)
        simpa using h
      have hcomb : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * Real.log
            ((ν ((aShift t)^[φ n] x) (shape A U ((aShift t)^[φ n] x))).toReal)
          - (φ n : ℝ)⁻¹ * (Real.log ((ν x (shape A U x)).toReal) + growthFun U ν t x))
          Filter.atTop (nhds 0) := by simpa using hψlim.sub h2
      refine hcomb.congr' (Filter.Eventually.of_forall (fun n => ?_))
      ring
    have hlim_rhs : Filter.Tendsto (fun n : ℕ =>
          ((φ n : ℝ)⁻¹ * ((φ n : ℝ) + 1)) * Work.EKLComp.Birkhoff.birkA (aShift t)
            (fun x : X3 => growthFun U ν t x) (φ n + 1) x
          + (φ n : ℝ)⁻¹ * (Real.log ((ν ((aShift t)^[φ n] x)
                (shape A U ((aShift t)^[φ n] x))).toReal)
              - Real.log ((ν x (shape A U x)).toReal) - growthFun U ν t x)) Filter.atTop
        (nhds (condExp (MeasurableSpace.invariants (aShift t)) μ
          (fun x : X3 => growthFun U ν t x) x)) := by
      have h := (hβ.mul hB).add htail
      simpa using h
    have hLim2 : Filter.Tendsto (fun n : ℕ => Work.EKLComp.Birkhoff.birkA (aShift t)
        (fun x : X3 => atomInfo A U ν t x) (φ n) x) Filter.atTop
        (nhds (condExp (MeasurableSpace.invariants (aShift t)) μ
          (fun x : X3 => growthFun U ν t x) x)) :=
      hlim_rhs.congr' (Filter.Eventually.of_forall (fun n => (hest n).symm))
    exact tendsto_nhds_unique hLim1 hLim2
  have hcs : (fun x : X3 => condExp (MeasurableSpace.invariants (aShift t)) μ
        (fun x : X3 => atomInfo A U ν t x) x)
      =ᵐ[μ] (fun x : X3 => condExp (MeasurableSpace.invariants (aShift t)) μ
        (fun x : X3 => growthFun U ν t x) x) := hkey
  have hIntEq : ∫ x, growthFun U ν t x ∂μ = ∫ x, atomInfo A U ν t x ∂μ := by
    have h1 : ∫ x, condExp (MeasurableSpace.invariants (aShift t)) μ
          (fun x : X3 => atomInfo A U ν t x) x ∂μ = ∫ x, atomInfo A U ν t x ∂μ :=
      MeasureTheory.integral_condExp (μ := μ) (f := fun x : X3 => atomInfo A U ν t x)
        (m := MeasurableSpace.invariants (aShift t)) (m₀ := inferInstance)
        (MeasurableSpace.invariants_le (aShift t))
    have h2 : ∫ x, condExp (MeasurableSpace.invariants (aShift t)) μ
          (fun x : X3 => growthFun U ν t x) x ∂μ = ∫ x, growthFun U ν t x ∂μ :=
      MeasureTheory.integral_condExp (μ := μ) (f := fun x : X3 => growthFun U ν t x)
        (m := MeasurableSpace.invariants (aShift t)) (m₀ := inferInstance)
        (MeasurableSpace.invariants_le (aShift t))
    rw [← h2, ← h1]
    exact MeasureTheory.integral_congr_ae hcs.symm
  calc ENNReal.ofReal (MeasureTheory.integral μ (fun x => growthFun U ν t x))
      = ENNReal.ofReal (∫ x, atomInfo A U ν t x ∂μ) := by rw [hIntEq]
    _ ≤ ∫⁻ x, ENNReal.ofReal (atomInfo A U ν t x) ∂μ :=
        ofReal_integral_le_lintegral_ofReal hAi_int
    _ = MeasureTheory.lintegral μ (fun x => ENNReal.ofReal (atomInfo A U ν t x)) := rfl



end Work.EKLC6Core

end
