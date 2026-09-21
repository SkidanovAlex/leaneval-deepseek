import Mathlib
import Submission.Work.OddBridge.dvi_reduce
import Submission.Work.OddBridge.Defs

namespace Work.OddBridge

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- **Differentiability of the Abel average of `KvecM`.**

`u ↦ ∫₀¹ (√(τ(1-τ)))⁻¹ • KvecM n h (u+τ(σ-u)) σ (x σ) (y σ) x' y' dτ` is differentiable at `s`,
for `a < s < σ ≤ 1`, as soon as the manifest kernel evaluated along the two chord endpoints is
`C²` on the box `[a,1]²`.  The proof differentiates under the integral sign: the moving point
`u + τ(σ-u)` stays in `[a,1]` for `u` near `s` and `τ ∈ [0,1]`, while the Abel weight
`(√(τ(1-τ)))⁻¹` and its `u`-derivative weight `(1-τ)(√(τ(1-τ)))⁻¹` are both integrable. -/
lemma kvecMAverage_differentiableAt_of_contDiffOn (n : ℕ) {h x y : ℝ → ℝ} {a s σ : ℝ}
    (ha : a < s) (hsσ : s < σ) (hσ1 : σ ≤ 1)
    (hK : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Work.OddBridge.KvecM n h p.1 p.2
        (x p.2) (y p.2) (deriv x p.2) (deriv y p.2))
        (Set.Icc a 1 ×ˢ Set.Icc a 1)) :
    DifferentiableAt ℝ (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
        Work.OddBridge.KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s := by
  have hs1 : s < 1 := lt_of_lt_of_le hsσ hσ1
  have ha1 : a < 1 := lt_trans ha hs1
  have hσmem : σ ∈ Set.Icc a 1 := ⟨le_of_lt (lt_trans ha hsσ), hσ1⟩
  have hσs_pos : 0 < σ - s := sub_pos.mpr hsσ
  -- a small symmetric neighbourhood of `s` on which the moving point never leaves `(a,σ)`
  set δ : ℝ := min (s - a) (σ - s) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδ_le_a : δ ≤ (s - a) / 2 := by
    rw [hδdef]
    exact div_le_div_of_nonneg_right (min_le_left (s - a) (σ - s)) (by norm_num)
  have hδ_le_σ : δ ≤ (σ - s) / 2 := by
    rw [hδdef]
    exact div_le_div_of_nonneg_right (min_le_right (s - a) (σ - s)) (by norm_num)
  have hsδa : a < s - δ := by linarith
  have hsδσ : s + δ < σ := by linarith
  have hnhds : Set.Ioo (s - δ) (s + δ) ∈ 𝓝 s :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hs_mem : s ∈ Set.Ioo (s - δ) (s + δ) := ⟨by linarith, by linarith⟩
  -- the moving point stays in the box
  have hzle : ∀ u ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      u + τ * (σ - u) ∈ Set.Icc a 1 := by
    intro u hu τ hτ
    have hu1 : a < u := lt_trans hsδa hu.1
    have hu2 : u < σ := lt_trans hu.2 hsδσ
    have hsub : 0 ≤ σ - u := sub_nonneg.mpr (le_of_lt hu2)
    have h1 : 0 ≤ τ * (σ - u) := mul_nonneg hτ.1 hsub
    have h2 : τ * (σ - u) ≤ σ - u := mul_le_of_le_one_left hsub hτ.2
    constructor <;> linarith
  have hint : ∀ u ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Icc (0:ℝ) 1, τ < 1 →
      u + τ * (σ - u) ∈ Set.Ioo a 1 := by
    intro u hu τ hτ hτ1
    have hu1 : a < u := lt_trans hsδa hu.1
    have hu2 : u < σ := lt_trans hu.2 hsδσ
    have hsub : 0 < σ - u := sub_pos.mpr hu2
    have hpos : 0 ≤ τ * (σ - u) := mul_nonneg hτ.1 (le_of_lt hsub)
    have hlt : τ * (σ - u) < σ - u := by
      have h1 : 0 < 1 - τ := sub_pos.mpr hτ1
      nlinarith [mul_pos h1 hsub]
    constructor
    · linarith
    · linarith
  -- the one-variable kernel `Φ z = KvecM n h z σ (x σ) (y σ) x' y'`
  set Φ : ℝ → (Fin 2 → ℝ) :=
    fun z => KvecM n h z σ (x σ) (y σ) (deriv x σ) (deriv y σ) with hΦdef
  have hΦcd : ContDiffOn ℝ 2 Φ (Set.Icc a 1) := by
    have hg : ContDiffOn ℝ 2 (fun z : ℝ => (z, σ)) (Set.Icc a 1) := by fun_prop
    have hmaps : Set.MapsTo (fun z : ℝ => (z, σ)) (Set.Icc a 1)
        (Set.Icc a 1 ×ˢ Set.Icc a 1) := fun z hz => ⟨hz, hσmem⟩
    have h := hK.comp hg hmaps
    simpa [hΦdef, Function.comp_def] using h
  have hΦdiffOn : DifferentiableOn ℝ Φ (Set.Icc a 1) := hΦcd.differentiableOn (by norm_num)
  have hderivcont : ContinuousOn (deriv Φ) (Set.Ioo a 1) :=
    (hΦcd.mono Set.Ioo_subset_Icc_self).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  -- a uniform bound on the relevant derivative
  obtain ⟨M, hM0, hMbound⟩ :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Set.Icc a 1, ‖derivWithin Φ (Set.Icc a 1) z‖ ≤ M := by
    have hcont := hΦcd.continuousOn_derivWithin (uniqueDiffOn_Icc ha1) (by norm_num)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    exact ⟨max C 0, le_max_right _ _, fun z hz => le_trans (hC z hz) (le_max_left _ _)⟩
  -- the chain rule along the moving point
  have hchain : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ u ∈ Set.Ioo (s - δ) (s + δ),
      HasDerivAt (fun u : ℝ => Φ (u + τ * (σ - u)))
        ((1 - τ) • deriv Φ (u + τ * (σ - u))) u := by
    intro τ hτ u hu
    rcases eq_or_lt_of_le hτ.2 with h1 | h1
    · subst h1
      have hconst : (fun u : ℝ => Φ (u + 1 * (σ - u))) = fun _ => Φ σ := by
        funext v; congr 1; ring
      rw [hconst]
      have harg : u + 1 * (σ - u) = σ := by ring
      rw [harg, sub_self, zero_smul]
      exact hasDerivAt_const _ _
    · have hz : u + τ * (σ - u) ∈ Set.Ioo a 1 :=
        hint u hu τ ⟨le_of_lt hτ.1, le_of_lt h1⟩ h1
      have hd : HasDerivAt Φ (deriv Φ (u + τ * (σ - u))) (u + τ * (σ - u)) :=
        hΦdiffOn.hasDerivAt
          (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hz) Set.Ioo_subset_Icc_self)
      have hinner : HasDerivAt (fun v : ℝ => v + τ * (σ - v)) (1 - τ) u := by
        have hv : (fun v : ℝ => v + τ * (σ - v)) = fun v => (1 - τ) * v + τ * σ := by
          funext v; ring
        rw [hv]
        simpa using ((hasDerivAt_id u).const_mul (1 - τ)).add_const (τ * σ)
      have hcomp := HasDerivAt.scomp (𝕜 := ℝ) (𝕜' := ℝ) (F := Fin 2 → ℝ) u hd hinner
      simpa [Function.comp_def] using hcomp
  -- the two integrands
  set Ffun : ℝ → ℝ → (Fin 2 → ℝ) :=
    fun u τ => (Real.sqrt (τ * (1 - τ)))⁻¹ • Φ (u + τ * (σ - u)) with hFfun
  set Ffun' : ℝ → ℝ → (Fin 2 → ℝ) :=
    fun u τ => (Real.sqrt (τ * (1 - τ)))⁻¹ • ((1 - τ) • deriv Φ (u + τ * (σ - u)))
    with hFfun'
  have hF_meas : ∀ᶠ u in 𝓝 s, AEStronglyMeasurable (Ffun u) (volume.restrict (Ι (0:ℝ) 1)) := by
    filter_upwards [hnhds] with u hu
    rw [hFfun]
    have hcont : ContinuousOn (fun τ : ℝ => Φ (u + τ * (σ - u))) (Set.Ioo 0 1) :=
      hΦcd.continuousOn.comp (by fun_prop)
        (fun τ hτ => hzle u hu τ (Set.Ioo_subset_Icc_self hτ))
    exact Commons.Geometry.Ulam.abel_weight_smul_measurable _ hcont
  have hF_int : IntervalIntegrable (Ffun s) volume (0:ℝ) 1 := by
    rw [hFfun]
    have hcont : ContinuousOn (fun τ : ℝ => Φ (s + τ * (σ - s))) (Set.uIcc 0 1) :=
      hΦcd.continuousOn.comp (by fun_prop) (fun τ hτ => by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
        exact hzle s hs_mem τ hτ)
    exact Commons.Geometry.Ulam.intervalIntegrable_abel_weight.smul_continuousOn hcont
  have hF'_meas : AEStronglyMeasurable (Ffun' s) (volume.restrict (Ι (0:ℝ) 1)) := by
    rw [hFfun']
    have hcont : ContinuousOn (fun τ : ℝ => (1 - τ) • deriv Φ (s + τ * (σ - s)))
        (Set.Ioo 0 1) := by
      have h1 : ContinuousOn (fun τ : ℝ => deriv Φ (s + τ * (σ - s))) (Set.Ioo 0 1) :=
        hderivcont.comp (by fun_prop)
          (fun τ hτ => hint s hs_mem τ (Set.Ioo_subset_Icc_self hτ) hτ.2)
      exact (by fun_prop : ContinuousOn (fun τ : ℝ => (1 - τ)) (Set.Ioo 0 1)).smul h1
    exact Commons.Geometry.Ulam.abel_weight_smul_measurable _ hcont
  have h_bound : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Ι (0:ℝ) 1 →
      ∀ u ∈ Set.Ioo (s - δ) (s + δ), ‖Ffun' u τ‖ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * M := by
    rw [hFfun']
    refine Filter.Eventually.of_forall (fun τ hτ u hu => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
    have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hle1 : 0 ≤ 1 - τ := by linarith [hτ.2]
    have hbnd : ‖(1 - τ) • deriv Φ (u + τ * (σ - u))‖ ≤ M := by
      rcases eq_or_lt_of_le hτ.2 with h1 | h1
      · rw [h1, sub_self, zero_smul, norm_zero]; exact hM0
      · have hz : u + τ * (σ - u) ∈ Set.Ioo a 1 :=
          hint u hu τ ⟨le_of_lt hτ.1, le_of_lt h1⟩ h1
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hle1]
        rw [show deriv Φ (u + τ * (σ - u))
            = derivWithin Φ (Set.Icc a 1) (u + τ * (σ - u)) from
          (derivWithin_of_mem_nhds (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hz)
            Set.Ioo_subset_Icc_self)).symm]
        calc (1 - τ) * ‖derivWithin Φ (Set.Icc a 1) (u + τ * (σ - u))‖
            ≤ 1 * M :=
              mul_le_mul (by linarith [hτ.1]) (hMbound _ (Set.Ioo_subset_Icc_self hz))
                (norm_nonneg _) zero_le_one
          _ = M := one_mul M
    calc ‖(Real.sqrt (τ * (1 - τ)))⁻¹ • ((1 - τ) • deriv Φ (u + τ * (σ - u)))‖
        = ‖(Real.sqrt (τ * (1 - τ)))⁻¹‖ * ‖(1 - τ) • deriv Φ (u + τ * (σ - u))‖ :=
          norm_smul _ _
      _ = (Real.sqrt (τ * (1 - τ)))⁻¹ * ‖(1 - τ) • deriv Φ (u + τ * (σ - u))‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hw]
      _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * M := mul_le_mul_of_nonneg_left hbnd hw
  have hbound_int : IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * M)
      volume (0:ℝ) 1 :=
    Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const M
  have h_diff : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Ι (0:ℝ) 1 →
      ∀ u ∈ Set.Ioo (s - δ) (s + δ), HasDerivAt (fun u : ℝ => Ffun u τ) (Ffun' u τ) u := by
    rw [hFfun, hFfun']
    refine Filter.Eventually.of_forall (fun τ hτ u hu => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
    exact (hchain τ hτ u hu).const_smul (Real.sqrt (τ * (1 - τ)))⁻¹
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0:ℝ)) (b := 1) (μ := volume)
    (F := Ffun) (F' := Ffun') (x₀ := s) (s := Set.Ioo (s - δ) (s + δ))
    (bound := fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * M)
    hnhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  exact hmain.2.differentiableAt

end

end Work.OddBridge
