import Mathlib

namespace Work.Rigidity.PeriodicDecay

open Complex Filter Asymptotics Set
open scoped Real Topology

theorem periodic_exp_decay_sq_contOn {F : ℂ → ℂ} {ψ : ℝ → ℝ}
    (hper : Function.Periodic F 1)
    (hcont : ContinuousOn F {z : ℂ | -1 < z.im})
    (hhol : Filter.Eventually (fun z : ℂ => DifferentiableAt ℂ F z)
      (Filter.comap Complex.im Filter.atTop))
    (hψ : Filter.Tendsto ψ Filter.atTop (nhds 0))
    (hbd : ∀ z : ℂ, 0 < z.im → ‖F z‖ ≤ ψ z.im * Real.exp (-(2 * Real.pi * z.im))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 ≤ z.im →
      ‖F z‖ ≤ C * Real.exp (-(4 * Real.pi * z.im)) := by
  -- The map `z ↦ qParam 1 z = exp (2 π i z)` is `1`-periodic.
  have hqper : Function.Periodic (Function.Periodic.qParam 1) 1 := by
    intro z
    rw [Function.Periodic.qParam, Function.Periodic.qParam]
    simp only [ofReal_one, div_one]
    rw [show 2 * ↑Real.pi * I * (z + 1) = 2 * ↑Real.pi * I * z + 2 * ↑Real.pi * I by ring]
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  -- The quotient `g = F / q` is `1`-periodic, holomorphic near `I∞` and tends to `0` there.
  set g : ℂ → ℂ := fun z => F z / Function.Periodic.qParam 1 z with hgdef
  have hgper : Function.Periodic g 1 := by
    change Function.Periodic (F / Function.Periodic.qParam 1) 1
    exact hper.div hqper
  have hghol : ∀ᶠ z in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ g z := by
    filter_upwards [hhol] with z hz
    exact hz.div (Function.Periodic.differentiable_qParam.differentiableAt)
      (Function.Periodic.qParam_ne_zero z)
  have hgzero : Filter.ZeroAtFilter (Filter.comap Complex.im Filter.atTop) g := by
    rw [Filter.ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero]
    have hψim : Tendsto (fun z : ℂ => ψ z.im) (Filter.comap Complex.im Filter.atTop) (𝓝 0) :=
      hψ.comp Filter.tendsto_comap
    refine squeeze_zero' ?_ ?_ hψim
    · filter_upwards with z using norm_nonneg _
    · filter_upwards [Filter.tendsto_comap.eventually (Ioi_mem_atTop (0 : ℝ))] with z hz
      have him : 0 < z.im := hz
      have h1 := hbd z him
      show ‖g z‖ ≤ ψ z.im
      simp only [hgdef]
      rw [norm_div, Function.Periodic.norm_qParam, div_one]
      rw [div_le_iff₀ (Real.exp_pos _)]
      calc ‖F z‖ ≤ ψ z.im * Real.exp (-(2 * Real.pi * z.im)) := h1
        _ = ψ z.im * Real.exp (-2 * Real.pi * z.im) := by
              rw [show -(2 * Real.pi * z.im) = -2 * Real.pi * z.im by ring]
  -- Exponential decay of `g` at `I∞`: `g = O (exp (-2 π im))`.
  have hO : g =O[Filter.comap Complex.im Filter.atTop]
      fun z => Real.exp (-2 * Real.pi * z.im / 1) :=
    Function.Periodic.exp_decay_of_zero_at_inf (h := 1) (f := g) one_pos hgper hghol hgzero
  obtain ⟨c, hc⟩ := hO.bound
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hc
  obtain ⟨R, hR⟩ := hc
  have hdecay : ∀ z : ℂ, R ≤ z.im → ‖F z‖ ≤ c * Real.exp (-(4 * Real.pi * z.im)) := by
    intro z hz
    have hg_bd : ‖g z‖ ≤ c * Real.exp (-2 * Real.pi * z.im) := by
      have h := hR z.im hz z rfl
      rw [Real.norm_of_nonneg (Real.exp_nonneg _), div_one] at h
      exact h
    have hq : Function.Periodic.qParam 1 z ≠ 0 := Function.Periodic.qParam_ne_zero z
    have hFg : F z = g z * Function.Periodic.qParam 1 z := by
      simp only [hgdef]
      rw [div_mul_cancel₀ _ hq]
    have hexp : Real.exp (-2 * Real.pi * z.im) * Real.exp (-2 * Real.pi * z.im)
        = Real.exp (-(4 * Real.pi * z.im)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖F z‖ = ‖g z * Function.Periodic.qParam 1 z‖ := by rw [hFg]
      _ = ‖g z‖ * ‖Function.Periodic.qParam 1 z‖ := norm_mul _ _
      _ = ‖g z‖ * Real.exp (-2 * Real.pi * z.im) := by
            rw [Function.Periodic.norm_qParam, div_one]
      _ ≤ (c * Real.exp (-2 * Real.pi * z.im)) * Real.exp (-2 * Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right hg_bd (Real.exp_nonneg _)
      _ = c * Real.exp (-(4 * Real.pi * z.im)) := by rw [mul_assoc, hexp]
  -- A uniform bound on the compact strip `0 ≤ im ≤ R₀`, `0 ≤ re ≤ 1`.
  set R₀ : ℝ := max R 0 with hR₀
  have hRnonneg : 0 ≤ R₀ := le_max_right _ _
  have hRR₀ : R ≤ R₀ := le_max_left _ _
  have hbox : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) R₀) :=
    isCompact_Icc.prod isCompact_Icc
  have hlin : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) R₀) := by
    apply Continuous.continuousOn
    exact (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) R₀) {z : ℂ | -1 < z.im} := by
    intro p hp
    have h2 : 0 ≤ p.2 := hp.2.1
    simp only [Set.mem_ofPred_eq]
    have him : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 := by simp
    rw [him]; linarith
  have hcontbox : ContinuousOn (fun p : ℝ × ℝ => F ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) R₀) :=
    hcont.comp hlin hmaps
  obtain ⟨M, hM⟩ := hbox.exists_bound_of_continuousOn hcontbox
  have hstrip : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ R₀ → ‖F z‖ ≤ M := by
    intro z hz0 hzR
    set z' : ℂ := z - (((⌊z.re⌋ : ℤ)) : ℂ) with hz'def
    have hz'_im : z'.im = z.im := by simp [hz'def]
    have hz'_re_ge : 0 ≤ z'.re := by
      rw [hz'def]
      simp only [Complex.sub_re, Complex.intCast_re]
      exact sub_nonneg.mpr (Int.floor_le z.re)
    have hz'_re_le : z'.re ≤ 1 := by
      rw [hz'def]
      simp only [Complex.sub_re, Complex.intCast_re]
      have h := Int.lt_floor_add_one z.re
      linarith
    have hmem : (z'.re, z'.im) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) R₀ :=
      ⟨⟨hz'_re_ge, hz'_re_le⟩, by rw [hz'_im]; exact ⟨hz0, hzR⟩⟩
    have hperz : F z = F z' := by
      have hp := hper.int_mul ⌊z.re⌋ z'
      simp only [mul_one] at hp
      rwa [show z' + (((⌊z.re⌋ : ℤ)) : ℂ) = z by rw [hz'def]; ring] at hp
    have hthis := hM (z'.re, z'.im) hmem
    rw [Complex.re_add_im, ← hperz] at hthis
    exact hthis
  have hMnonneg : 0 ≤ M := by
    have h := hM ((0:ℝ), (0:ℝ)) (by
      simp only [Set.mem_prod]
      exact ⟨⟨le_refl 0, zero_le_one⟩, ⟨le_refl 0, hRnonneg⟩⟩)
    have hz : (((0:ℝ):ℂ) + ((0:ℝ):ℂ) * Complex.I) = 0 := by simp
    rw [hz] at h
    exact le_trans (norm_nonneg (F 0)) h
  refine ⟨max (max c 0) (M * Real.exp (4 * Real.pi * R₀)), ?_, ?_⟩
  · exact le_trans (le_max_right c 0) (le_max_left _ _)
  · intro z hz0
    have hC : c ≤ max (max c 0) (M * Real.exp (4 * Real.pi * R₀)) :=
      le_trans (le_max_left c 0) (le_max_left _ _)
    have hC2 : M * Real.exp (4 * Real.pi * R₀) ≤
        max (max c 0) (M * Real.exp (4 * Real.pi * R₀)) := le_max_right _ _
    rcases le_or_gt R₀ z.im with hzR | hzR
    · have h := hdecay z (le_trans hRR₀ hzR)
      calc ‖F z‖ ≤ c * Real.exp (-(4 * Real.pi * z.im)) := h
        _ ≤ max (max c 0) (M * Real.exp (4 * Real.pi * R₀)) * Real.exp (-(4 * Real.pi * z.im)) :=
              mul_le_mul_of_nonneg_right hC (Real.exp_nonneg _)
    · have h := hstrip z hz0 (le_of_lt hzR)
      have h1 : M ≤ (M * Real.exp (4 * Real.pi * R₀)) * Real.exp (-(4 * Real.pi * z.im)) := by
        have hprod : Real.exp (4 * Real.pi * R₀) * Real.exp (-(4 * Real.pi * z.im))
            = Real.exp (4 * Real.pi * (R₀ - z.im)) := by
          rw [← Real.exp_add]; congr 1; ring
        have hge1 : 1 ≤ Real.exp (4 * Real.pi * (R₀ - z.im)) := by
          rw [Real.one_le_exp_iff]
          nlinarith [Real.pi_pos, le_of_lt hzR]
        calc M = M * 1 := by ring
          _ ≤ M * (Real.exp (4 * Real.pi * R₀) * Real.exp (-(4 * Real.pi * z.im))) :=
                mul_le_mul_of_nonneg_left (by rw [hprod]; exact hge1) hMnonneg
          _ = (M * Real.exp (4 * Real.pi * R₀)) * Real.exp (-(4 * Real.pi * z.im)) := by ring
      calc ‖F z‖ ≤ M := h
        _ ≤ (M * Real.exp (4 * Real.pi * R₀)) * Real.exp (-(4 * Real.pi * z.im)) := h1
        _ ≤ max (max c 0) (M * Real.exp (4 * Real.pi * R₀)) * Real.exp (-(4 * Real.pi * z.im)) :=
              mul_le_mul_of_nonneg_right hC2 (Real.exp_nonneg _)

end Work.Rigidity.PeriodicDecay
