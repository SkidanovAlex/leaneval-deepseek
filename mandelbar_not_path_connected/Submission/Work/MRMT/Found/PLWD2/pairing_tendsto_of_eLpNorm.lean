import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found.PLWD2

open MeasureTheory Filter

/-- If the `u n` converge to `D` in `L²` on a compact `K` (measured by `eLpNorm` of the difference),
and `ψ` is a continuous function supported in `K`, then the pairings `∫ z, u n z * ψ z` converge
to `∫ z, D z * ψ z`.

The proof is Hölder's inequality in the form `‖∫ f·ψ‖ ≤ ‖f‖_{L²} · ‖ψ‖_{L²}`, together with the
fact that a continuous function supported in a compact set is bounded, hence lies in `L²` there
(so `‖ψ‖_{L²} < ∞` and the pairing is a bounded linear functional). -/
theorem pairing_tendsto_of_eLpNorm {u : ℕ → ℂ → ℂ} {D ψ : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hψc : Continuous ψ) (hψs : Function.support ψ ⊆ K)
    (hu : ∀ n, MeasureTheory.MemLp (u n) 2 ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict K))
    (hcon : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun z => u n z - D z) 2
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict K)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ z, u n z * ψ z) Filter.atTop (nhds (∫ z, D z * ψ z)) := by
  classical
  set μ₀ : Measure ℂ := (MeasureTheory.volume : MeasureTheory.Measure ℂ) with hμ₀
  set ν : Measure ℂ := μ₀.restrict K with hν
  have hvolK : μ₀ K < ⊤ := by rw [hμ₀]; exact hK.measure_lt_top
  have hinstν : IsFiniteMeasure ν := by rw [hν]; exact isFiniteMeasure_restrict.mpr hvolK.ne
  -- `ψ` is bounded (continuous on the compact `K`, zero outside it), hence in `L²(ν)`.
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hψc.continuousOn
  have hψbound : ∀ z, ‖ψ z‖ ≤ max C 0 := by
    intro z
    by_cases hz : z ∈ K
    · exact le_trans (hC z hz) (le_max_left _ _)
    · have hz0 : ψ z = 0 := by
        by_contra h
        exact hz (hψs (Function.mem_support.mpr h))
      simp [hz0]
  have hψaesm : AEStronglyMeasurable ψ ν := hψc.aestronglyMeasurable.restrict
  have hψtop : MemLp ψ ⊤ ν := memLp_top_of_bound hψaesm (max C 0) (Eventually.of_forall hψbound)
  have hψL2 : MemLp ψ 2 ν := hψtop.mono_exponent (by simp)
  -- `eLpNorm (u n - D)` is eventually finite, so `u n - D` is eventually in `L²`; hence so is `D`.
  have hfin : ∀ᶠ n in Filter.atTop, eLpNorm (fun z => u n z - D z) 2 ν < ⊤ := by
    have h1 := (ENNReal.tendsto_nhds_zero.mp hcon) 1 (by norm_num)
    filter_upwards [h1] with n hn
    exact lt_of_le_of_lt hn (by simp)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfin
  have hHmem : MemLp (fun z => u N z - D z) 2 ν := memLp_iff.mpr (hN N le_rfl)
  have hDmem : MemLp D 2 ν := by
    have hdeq : D = u N - fun z => u N z - D z := by funext z; simp
    rw [hdeq]
    exact (hu N).sub hHmem
  have hIntu : ∀ n, Integrable (fun z => u n z * ψ z) ν := fun n => (hu n).integrable_mul hψL2
  have hIntD : Integrable (fun z => D z * ψ z) ν := hDmem.integrable_mul hψL2
  -- the difference of the pairings is the pairing of the difference
  have hIsubJ : ∀ n, (∫ z, u n z * ψ z ∂ν) - (∫ z, D z * ψ z ∂ν)
      = ∫ z, (u n z - D z) * ψ z ∂ν := by
    intro n
    rw [← integral_sub (hIntu n) hIntD]
    congr 1
    funext z
    ring
  -- Hölder bound, eventually in `n`
  have hbnd : ∀ᶠ n in Filter.atTop, ‖∫ z, (u n z - D z) * ψ z ∂ν‖
      ≤ (eLpNorm (fun z => u n z - D z) 2 ν).toReal * (eLpNorm ψ 2 ν).toReal := by
    filter_upwards [hfin] with n hfinn
    have haesm : AEStronglyMeasurable (fun z => u n z - D z) ν := by
      by_contra h
      rw [eLpNorm_of_not_aestronglyMeasurable h] at hfinn
      exact absurd hfinn (lt_irrefl _)
    have hHolder : eLpNorm (fun z => (u n z - D z) * ψ z) 1 ν
        ≤ eLpNorm (fun z => u n z - D z) 2 ν * eLpNorm ψ 2 ν := by
      have hb := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1)
        (fun a b : ℂ => a * b) 1 continuous_mul haesm hψaesm
        (Eventually.of_forall (fun z => by rw [norm_mul]; simp))
      simpa using hb
    have h1 : ‖∫ z, (u n z - D z) * ψ z ∂ν‖
        ≤ (∫⁻ z, ENNReal.ofReal ‖(u n z - D z) * ψ z‖ ∂ν).toReal :=
      norm_integral_le_lintegral_norm _
    have h2 : (∫⁻ z, ENNReal.ofReal ‖(u n z - D z) * ψ z‖ ∂ν)
        ≤ eLpNorm (fun z => (u n z - D z) * ψ z) 1 ν := by
      simpa only [ofReal_norm] using (lintegral_enorm_le_eLpNorm_one (μ := ν)
        (f := fun z => (u n z - D z) * ψ z))
    have hne : eLpNorm (fun z => u n z - D z) 2 ν * eLpNorm ψ 2 ν ≠ ⊤ :=
      ne_of_lt (ENNReal.mul_lt_top hfinn hψL2.eLpNorm_lt_top)
    calc ‖∫ z, (u n z - D z) * ψ z ∂ν‖
        ≤ (∫⁻ z, ENNReal.ofReal ‖(u n z - D z) * ψ z‖ ∂ν).toReal := h1
      _ ≤ (eLpNorm (fun z => u n z - D z) 2 ν * eLpNorm ψ 2 ν).toReal :=
            ENNReal.toReal_mono hne (le_trans h2 hHolder)
      _ = (eLpNorm (fun z => u n z - D z) 2 ν).toReal * (eLpNorm ψ 2 ν).toReal :=
            ENNReal.toReal_mul
  -- the pairings of the differences tend to `0`
  have hlim0 : Filter.Tendsto (fun n => ∫ z, (u n z - D z) * ψ z ∂ν) Filter.atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) hbnd ?_
    have ht : Filter.Tendsto (fun n => (eLpNorm (fun z => u n z - D z) 2 ν).toReal)
        Filter.atTop (nhds 0) :=
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcon
    simpa using ht.mul_const (eLpNorm ψ 2 ν).toReal
  -- hence the pairings converge on `L²(ν)`
  have hlimν : Filter.Tendsto (fun n => ∫ z, u n z * ψ z ∂ν) Filter.atTop
      (nhds (∫ z, D z * ψ z ∂ν)) := by
    have h2 : Filter.Tendsto (fun n => (∫ z, (u n z - D z) * ψ z ∂ν) + (∫ z, D z * ψ z ∂ν))
        Filter.atTop (nhds (0 + ∫ z, D z * ψ z ∂ν)) := hlim0.add tendsto_const_nhds
    simp only [zero_add] at h2
    refine h2.congr' ?_
    filter_upwards with n
    rw [← hIsubJ n]
    ring
  -- finally transfer the integrals from `ν = volume.restrict K` to `volume`
  have htr : ∀ g : ℂ → ℂ, Function.support g ⊆ K →
      ∫ z, g z ∂μ₀ = ∫ z, g z ∂ν := by
    intro g hg
    have h := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ₀) (s := K) (f := g)
      (fun z hz => by
        by_contra hc
        exact hz (hg (Function.mem_support.mpr hc)))
    rw [← h, hν]
  have hfun : (fun n => ∫ z, u n z * ψ z ∂μ₀) = fun n => ∫ z, u n z * ψ z ∂ν := by
    funext n
    exact htr (fun z => u n z * ψ z)
      (fun z hz => hψs (Function.support_mul_subset_right (u n) ψ hz))
  rw [hfun, htr (fun z => D z * ψ z)
      (fun z hz => hψs (Function.support_mul_subset_right D ψ hz))]
  exact hlimν

end Work.MRMT.Found.PLWD2
