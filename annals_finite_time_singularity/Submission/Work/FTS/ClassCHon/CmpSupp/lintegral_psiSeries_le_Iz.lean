import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.ClassC.lintegral_psiSeries_le_of_trunc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.CmpSupp

/-- Almost every `z ∈ Iz = [0,∞)` satisfies `0 < z`. -/
theorem ae_mem_Ioi_of_Iz :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [MeasureTheory.ae_restrict_iff (p := fun z : ℝ => 0 < z)
    (by exact measurableSet_Ioi)]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ)) ?_
    (MeasureTheory.measure_singleton 0)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  push Not at hx
  simp only [Set.mem_singleton_iff]
  simp only [Work.Spaces.Iz, Set.mem_Ici] at hx
  exact le_antisymm hx.2 hx.1

/-- Almost every `θ ∈ Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
theorem ae_mem_Ioo_of_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [MeasureTheory.ae_restrict_iff
    (p := fun θ : ℝ => θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (by exact measurableSet_Ioo)]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_
    ((Set.toFinite ({0, Real.pi / 2} : Set ℝ)).measure_zero MeasureTheory.volume)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  push Not at hx
  simp only [Work.Spaces.Iθ, Set.mem_Icc] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hx with ⟨⟨h1, h2⟩, h3⟩
  rcases lt_or_eq_of_le h1 with h | h
  · right
    by_contra hne
    exact h3 ⟨h, lt_of_le_of_ne h2 hne⟩
  · exact Or.inl h.symm

theorem lintegral_psiSeries_le_Iz {α : ℝ} {F : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hconv : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) Filter.atTop
        (nhds (Work.FTS.PhiStar.Series.psiSeries α F z θ)))
    (hmeas : ∀ N : ℕ, AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hbd : ∀ N : ℕ, (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) ≤ ENNReal.ofReal C) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) ≤ ENNReal.ofReal C := by
  -- ## Step 1: Fatou's lemma in the angular variable, for each `z > 0`.
  have htheta : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ Filter.liminf (fun N : ℕ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop := by
    intro z hz
    have hfat := MeasureTheory.lintegral_liminf_le'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) (u := Filter.atTop)
      (f := fun (N : ℕ) (θ : ℝ) => ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (fun N => Work.FTS.ClassC.lplst_theta_integrand_aemeasurable α F N z)
    -- the pointwise identification of the `liminf` with the angular energy of `psiSeries`
    have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Filter.liminf (fun N : ℕ => ENNReal.ofReal
          ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop
        = ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      intro θ hθ
      have hc : Continuous (fun x : ℝ => ENNReal.ofReal
          (x ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
        ENNReal.continuous_ofReal.comp
          (((continuous_id.pow 2).mul continuous_const).mul continuous_const)
      exact (hc.continuousAt.tendsto.comp (hconv z hz θ hθ)).liminf_eq
    have hae : (fun θ : ℝ => Filter.liminf (fun N : ℕ => ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
      ae_mem_Ioo_of_Iθ.mono fun θ hθ => hpt θ hθ
    rw [MeasureTheory.lintegral_congr_ae hae] at hfat
    exact hfat
  -- ## Step 2: Fatou's lemma in the radial variable.
  have hzfat := MeasureTheory.lintegral_liminf_le'
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) (u := Filter.atTop)
    (f := fun (N : ℕ) (z : ℝ) => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
      ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
    hmeas
  -- ## Step 3: compare the target with the (radial) `liminf` of the angular energies.
  have hmono : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
      ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, Filter.liminf (fun N : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop :=
    MeasureTheory.lintegral_mono_ae <| ae_mem_Ioi_of_Iz.mono fun z hz => htheta z hz
  -- ## Step 4: the uniform bound on the truncations bounds the `liminf`.
  have hbound : Filter.liminf (fun N : ℕ => ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop
      ≤ ENNReal.ofReal C := by
    have hbdd : Filter.IsBoundedUnder (fun x1 x2 : ℝ≥0∞ => x2 ≤ x1) Filter.atTop
        (fun N : ℕ => ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
      Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩
    exact Filter.liminf_le_of_frequently_le (Filter.Eventually.of_forall hbd).frequently hbdd
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, Filter.liminf (fun N : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop := hmono
    _ ≤ Filter.liminf (fun N : ℕ => ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop := hzfat
    _ ≤ ENNReal.ofReal C := hbound

end Work.FTS.ClassCHon.CmpSupp
