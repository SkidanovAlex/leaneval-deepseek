import Mathlib
import Submission.Work.VolterraLong.volterra_long_exists_C1

/-!
# The `+ε` variant of `deriv_from_equation_aux`

Same proof as `Work.VolterraLong.deriv_from_equation_aux` (module
`Submission.Work.VolterraLong.volterra_long_exists_C1`) but with the derivative bound
`‖fderiv (G s) z - A s‖ ≤ Cg * ‖z - Z₀ s‖ + ε` (an additive `ε`, as supplied by the
perturbation estimates) and the resulting constant `κ = Cg * K1 * ε + ε`.

The only two places where the proof changes are the definition of `κ` and the estimate
`hJA : ‖J - A₀‖ ≤ κ`: the additive `ε` is carried through, and the hypothesis
`B * (Cg * K1 * ε + ε) ≤ 1/2` is used verbatim.  Everything else --- the algebraic
decomposition of the slope, the three limit statements, and the final pincer argument ---
is unchanged.
-/

namespace Work.VolterraLong

open Set Filter MeasureTheory
open Work.VolterraLong.C1
open scoped Topology Interval

theorem deriv_from_equation_eps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → E → E} {Θ : ℝ → ℝ → E → E} {Ξ : ℝ → E} {Gs : ℝ → E → E}
    {Θs : ℝ → ℝ → E → E} {Ξs : ℝ → E} {Z₀ Z V : ℝ → E} {A : ℝ → E ≃L[ℝ] E}
    {B Cg K1 ε : ℝ} (hε : 0 < ε) (hB : 0 < B) (hCg : 0 ≤ Cg) (hK1 : 0 ≤ K1)
    (hAinv : ∀ s ∈ Set.Icc a b, ‖((A s).symm : E →L[ℝ] E)‖ ≤ B)
    (hZ : ContinuousOn Z (Set.Icc a b))
    (hZclose : ∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ K1 * ε) (hK1ε : K1 * ε ≤ 1)
    (hκB : B * (Cg * K1 * ε + ε) ≤ 1 / 2)
    (hsol : ∀ s ∈ Set.Icc a b, G s (Z s) = (∫ σ in s..b, Θ s σ (Z σ)) + Ξ s)
    (hG : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ : Continuous Ξ)
    (hGs : ∀ s ∈ Set.Icc a b, ∀ z : E, HasDerivAt (fun u : ℝ => G u z) (Gs s z) s)
    (hGs_cont : Continuous (fun p : ℝ × E => Gs p.1 p.2))
    (hΘs : ∀ s ∈ Set.Icc a b, ∀ σ : ℝ, ∀ z : E,
      HasDerivAt (fun u : ℝ => Θ u σ z) (Θs s σ z) s)
    (hΘs_cont : Continuous (fun p : ℝ × ℝ × E => Θs p.1 p.2.1 p.2.2))
    (hΞs : ∀ s : ℝ, HasDerivAt Ξ (Ξs s) s) (hΞs_cont : Continuous Ξs)
    (hdiff : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      DifferentiableAt ℝ (fun w => G s w) z)
    (hder : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      ‖fderiv ℝ (fun w => G s w) z - (A s : E →L[ℝ] E)‖ ≤ Cg * ‖z - Z₀ s‖ + ε)
    (hV : ∀ s ∈ Set.Icc a b, fderiv ℝ (fun w => G s w) (Z s) (V s)
      = - Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s) :
    ∀ s ∈ Set.Icc a b, HasDerivWithinAt Z (V s) (Set.Icc a b) s := by
  intro s hs
  set J : E →L[ℝ] E := fderiv ℝ (fun w => G s w) (Z s) with hJdef
  set A₀ : E →L[ℝ] E := (A s : E →L[ℝ] E) with hA₀def
  set κ : ℝ := Cg * K1 * ε + ε with hκdef
  have hZs1 : dist (Z s) (Z₀ s) ≤ 1 := le_trans (hZclose s hs) hK1ε
  have hZs_mem : Z s ∈ Metric.closedBall (Z₀ s) 1 := Metric.mem_closedBall.mpr hZs1
  have hJ : HasFDerivAt (fun w => G s w) J (Z s) := by
    rw [hJdef]; exact (hdiff s hs (Z s) hZs_mem).hasFDerivAt
  have hlittle : (fun x => G s x - G s (Z s) - J (x - Z s)) =o[𝓝 (Z s)]
      (fun x => x - Z s) := hJ.isLittleO
  have hJA : ‖J - A₀‖ ≤ κ := by
    rw [hJdef, hA₀def, hκdef]
    have h1 := hder s hs (Z s) hZs_mem
    have h2 : ‖Z s - Z₀ s‖ ≤ K1 * ε := by
      have h3 := hZclose s hs; rwa [dist_eq_norm] at h3
    have h2' : Cg * ‖Z s - Z₀ s‖ ≤ Cg * (K1 * ε) := mul_le_mul_of_nonneg_left h2 hCg
    calc ‖fderiv ℝ (fun w => G s w) (Z s) - (A s : E →L[ℝ] E)‖
        ≤ Cg * ‖Z s - Z₀ s‖ + ε := h1
      _ ≤ Cg * (K1 * ε) + ε := by linarith
      _ = Cg * K1 * ε + ε := by ring
  have hκB' : B * κ ≤ 1 / 2 := by rw [hκdef]; exact hκB
  -- the filter
  have hl_le : 𝓝[Set.Icc a b \ {s}] s ≤ 𝓝[{s}ᶜ] s :=
    nhdsWithin_mono s (fun x hx => hx.2)
  have hl_nhds : 𝓝[Set.Icc a b \ {s}] s ≤ 𝓝 s := le_trans hl_le nhdsWithin_le_nhds
  have hl_Icc : 𝓝[Set.Icc a b \ {s}] s ≤ 𝓝[Set.Icc a b] s :=
    nhdsWithin_mono s (fun x hx => hx.1)
  have hZtend : Tendsto Z (𝓝[Set.Icc a b \ {s}] s) (𝓝 (Z s)) :=
    (hZ.continuousWithinAt hs).tendsto.mono_left hl_Icc
  -- ## continuity helpers
  have huIcc_sub : ∀ {u : ℝ}, u ∈ Set.Icc a b → Set.uIcc s u ⊆ Set.Icc a b := by
    intro u hu
    have hs' : s ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hs
    have hu' : u ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hu
    have h := Set.uIcc_subset_uIcc hs' hu'
    rwa [Set.uIcc_of_le hab] at h
  have hcont_Θ_Z : ∀ (u : ℝ), u ∈ Set.Icc a b →
      ContinuousOn (fun σ : ℝ => Θ u σ (Z σ)) (Set.uIcc s u) := by
    intro u hu
    have h1 : ContinuousOn (fun σ : ℝ => (u, σ, Z σ)) (Set.uIcc s u) := by
      refine continuousOn_const.prodMk (continuousOn_id.prodMk ?_)
      exact hZ.comp continuousOn_id (fun σ hσ => huIcc_sub hu hσ)
    exact hΘ.comp_continuousOn h1
  have hcont_Θ_Icc : ∀ (u : ℝ), u ∈ Set.Icc a b →
      ContinuousOn (fun σ : ℝ => Θ u σ (Z σ)) (Set.Icc s b) := by
    intro u hu
    have h1 : ContinuousOn (fun σ : ℝ => (u, σ, Z σ)) (Set.Icc a b) := by
      refine continuousOn_const.prodMk (continuousOn_id.prodMk ?_)
      exact hZ.comp continuousOn_id (fun σ hσ => hσ)
    exact (hΘ.comp_continuousOn h1).mono (show Set.Icc s b ⊆ Set.Icc a b from
      Set.Icc_subset_Icc hs.1 (le_refl b))
  have hcont_Θs_Icc : ContinuousOn (fun σ : ℝ => Θs s σ (Z σ)) (Set.Icc s b) := by
    have h1 : ContinuousOn (fun σ : ℝ => (s, σ, Z σ)) (Set.Icc a b) := by
      refine continuousOn_const.prodMk (continuousOn_id.prodMk ?_)
      exact hZ.comp continuousOn_id (fun σ hσ => hσ)
    exact (hΘs_cont.comp_continuousOn h1).mono (show Set.Icc s b ⊆ Set.Icc a b from
      Set.Icc_subset_Icc hs.1 (le_refl b))
  have hcont_tuple_box : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.2, Z p.2))
      (Set.Icc a b ×ˢ Set.Icc s b) := by
    refine continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.prodMk ?_)
    exact hZ.comp continuous_snd.continuousOn (fun p hp => ⟨le_trans hs.1 hp.2.1, hp.2.2⟩)
  have hcont_Θ_box : ContinuousOn (fun p : ℝ × ℝ => Θ p.1 p.2 (Z p.2))
      (Set.Icc a b ×ˢ Set.Icc s b) := hΘ.comp_continuousOn hcont_tuple_box
  have hcont_Θs_box : ContinuousOn (fun p : ℝ × ℝ => Θs p.1 p.2 (Z p.2))
      (Set.Icc a b ×ˢ Set.Icc s b) := hΘs_cont.comp_continuousOn hcont_tuple_box
  -- ## the algebraic identity
  have hkey : ∀ u ∈ Set.Icc a b, u ≠ s →
      J (slope Z s u - V s)
        = (((u - s)⁻¹ • (Ξ u - Ξ s) - Ξs s)
          + (-((u - s)⁻¹ • (∫ σ in s..u, Θ u σ (Z σ))) + Θ s s (Z s))
          + ((u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ)))
              - (∫ σ in s..b, Θs s σ (Z σ)))
          + (Gs s (Z s) - (u - s)⁻¹ • (∫ r in s..u, Gs r (Z u))))
        - (u - s)⁻¹ • (G s (Z u) - G s (Z s) - J (Z u - Z s)) := by
    intro u hu hus
    have huI : u ∈ Set.Icc a b := hu
    have hi_Θu_su : IntervalIntegrable (fun σ : ℝ => Θ u σ (Z σ)) volume s u :=
      (hcont_Θ_Z u huI).intervalIntegrable
    have hi_Θu_us : IntervalIntegrable (fun σ : ℝ => Θ u σ (Z σ)) volume u s := hi_Θu_su.symm
    have hi_Θu_sb : IntervalIntegrable (fun σ : ℝ => Θ u σ (Z σ)) volume s b :=
      (hcont_Θ_Icc u huI).intervalIntegrable_of_Icc hs.2
    have hi_Θs_sb : IntervalIntegrable (fun σ : ℝ => Θ s σ (Z σ)) volume s b :=
      (hcont_Θ_Icc s hs).intervalIntegrable_of_Icc hs.2
    have hFTC : G u (Z u) - G s (Z u) = ∫ r in s..u, Gs r (Z u) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r => G r (Z u))
        (f' := fun r => Gs r (Z u))]
      · intro r hr
        exact hGs r (huIcc_sub huI hr) (Z u)
      · refine ContinuousOn.intervalIntegrable (u := fun r : ℝ => Gs r (Z u)) ?_
        have h1 : ContinuousOn (fun r : ℝ => (r, Z u)) (Set.uIcc s u) :=
          continuousOn_id.prodMk continuousOn_const
        exact hGs_cont.comp_continuousOn h1
    have hIntSplit : (∫ σ in u..b, Θ u σ (Z σ)) - (∫ σ in s..b, Θ s σ (Z σ))
        = -(∫ σ in s..u, Θ u σ (Z σ))
          + (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ))) := by
      rw [intervalIntegral.integral_sub hi_Θu_sb hi_Θs_sb]
      rw [← intervalIntegral.integral_add_adjacent_intervals hi_Θu_us hi_Θu_sb]
      rw [intervalIntegral.integral_symm s u]
      module
    have hdiff : G u (Z u) - G s (Z s)
        = ((∫ σ in u..b, Θ u σ (Z σ)) - (∫ σ in s..b, Θ s σ (Z σ))) + (Ξ u - Ξ s) := by
      rw [hsol u huI, hsol s hs]; abel
    have hexp : (u - s)⁻¹ • (G u (Z u) - G s (Z s))
        = -(u - s)⁻¹ • (∫ σ in s..u, Θ u σ (Z σ))
          + (u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ)))
          + (u - s)⁻¹ • (Ξ u - Ξ s) := by
      rw [hdiff, hIntSplit]
      module
    have hJslope : J (slope Z s u)
        = (u - s)⁻¹ • (G u (Z u) - G s (Z s))
          - (u - s)⁻¹ • (∫ r in s..u, Gs r (Z u))
          - (u - s)⁻¹ • (G s (Z u) - G s (Z s) - J (Z u - Z s)) := by
      rw [show slope Z s u = (u - s)⁻¹ • (Z u - Z s) from rfl, map_smul]
      have hJeq : J (Z u - Z s) = (G u (Z u) - G s (Z s)) - (∫ r in s..u, Gs r (Z u))
          - (G s (Z u) - G s (Z s) - J (Z u - Z s)) := by
        have h0 : J (Z u - Z s)
            = (G s (Z u) - G s (Z s)) - (G s (Z u) - G s (Z s) - J (Z u - Z s)) := by
          rw [sub_sub_cancel]
        rw [h0, ← hFTC]; module
      conv_lhs => rw [hJeq]
      module
    have hJv : J (V s) = - Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s := by
      rw [hJdef]; exact hV s hs
    rw [map_sub, hJslope, hJv, hexp]
    module
  -- ## the limit statements
  have T1 : Tendsto (fun u => (u - s)⁻¹ • (Ξ u - Ξ s) - Ξs s)
      (𝓝[Set.Icc a b \ {s}] s) (𝓝 0) := by
    have h : Tendsto (fun u => (u - s)⁻¹ • (Ξ u - Ξ s))
        (𝓝[Set.Icc a b \ {s}] s) (𝓝 (Ξs s)) := by
      have h1 := (hΞs s).tendsto_slope.mono_left hl_le
      have h2 : slope Ξ s = fun u => (u - s)⁻¹ • (Ξ u - Ξ s) := by
        funext u; simp [slope]
      rwa [h2] at h1
    simpa using h.sub_const (Ξs s)
  have hΦΘ : ContinuousWithinAt (fun p : ℝ × ℝ => Θ p.1 p.2 (Z p.2))
      (Set.Icc a b ×ˢ Set.Icc a b) (s, s) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.2, Z p.2))
        (Set.Icc a b ×ˢ Set.Icc a b) := by
      refine continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.prodMk ?_)
      exact hZ.comp continuous_snd.continuousOn (fun p hp => hp.2)
    exact (hΘ.comp_continuousOn h1).continuousWithinAt (by exact ⟨hs, hs⟩)
  have hΦGs : ContinuousWithinAt (fun p : ℝ × ℝ => Gs p.2 (Z p.1))
      (Set.Icc a b ×ˢ Set.Icc a b) (s, s) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (p.2, Z p.1)) (Set.Icc a b ×ˢ Set.Icc a b) :=
      continuous_snd.continuousOn.prodMk (hZ.comp continuous_fst.continuousOn (fun p hp => hp.1))
    exact (hGs_cont.comp_continuousOn h1).continuousWithinAt (by exact ⟨hs, hs⟩)
  have T2 : Tendsto (fun u => -((u - s)⁻¹ • (∫ σ in s..u, Θ u σ (Z σ))) + Θ s s (Z s))
      (𝓝[Set.Icc a b \ {s}] s) (𝓝 0) := by
    have h := interval_average_tendsto (f := fun u σ => Θ u σ (Z σ)) (s := s)
      (l := 𝓝[Set.Icc a b \ {s}] s) hl_le ?_ ?_
    · simpa using h.neg.add_const (Θ s s (Z s))
    · intro ε hεpos
      obtain ⟨δ, hδpos, hδprop⟩ := Metric.continuousWithinAt_iff.mp hΦΘ ε hεpos
      filter_upwards [self_mem_nhdsWithin, hl_nhds (Metric.ball_mem_nhds s hδpos)] with u huA huB
      intro σ hσ
      have hmem : (u, σ) ∈ Set.Icc a b ×ˢ Set.Icc a b := by
        refine ⟨huA.1, ?_⟩
        rcases le_total s u with h | h
        · rw [Set.uIcc_of_le h] at hσ; exact ⟨le_trans hs.1 hσ.1, le_trans hσ.2 huA.1.2⟩
        · rw [Set.uIcc_of_ge h] at hσ; exact ⟨le_trans huA.1.1 hσ.1, le_trans hσ.2 hs.2⟩
      exact hδprop hmem (lt_of_le_of_lt (dist_prod_pair_le hσ) huB)
    · filter_upwards [self_mem_nhdsWithin] with u huA
      exact (hcont_Θ_Z u huA.1).intervalIntegrable
  have T4 : Tendsto (fun u => Gs s (Z s) - (u - s)⁻¹ • (∫ r in s..u, Gs r (Z u)))
      (𝓝[Set.Icc a b \ {s}] s) (𝓝 0) := by
    have h := interval_average_tendsto (f := fun u r => Gs r (Z u)) (s := s)
      (l := 𝓝[Set.Icc a b \ {s}] s) hl_le ?_ ?_
    · simpa using h.const_sub (Gs s (Z s))
    · intro ε hεpos
      obtain ⟨δ, hδpos, hδprop⟩ := Metric.continuousWithinAt_iff.mp hΦGs ε hεpos
      filter_upwards [self_mem_nhdsWithin, hl_nhds (Metric.ball_mem_nhds s hδpos)] with u huA huB
      intro σ hσ
      have hmem : (u, σ) ∈ Set.Icc a b ×ˢ Set.Icc a b := by
        refine ⟨huA.1, ?_⟩
        rcases le_total s u with h | h
        · rw [Set.uIcc_of_le h] at hσ; exact ⟨le_trans hs.1 hσ.1, le_trans hσ.2 huA.1.2⟩
        · rw [Set.uIcc_of_ge h] at hσ; exact ⟨le_trans huA.1.1 hσ.1, le_trans hσ.2 hs.2⟩
      exact hδprop hmem (lt_of_le_of_lt (dist_prod_pair_le hσ) huB)
    · filter_upwards [self_mem_nhdsWithin] with u huA
      refine ContinuousOn.intervalIntegrable (u := fun r : ℝ => Gs r (Z u)) ?_
      have h1 : ContinuousOn (fun r : ℝ => (r, Z u)) (Set.uIcc s u) :=
        continuousOn_id.prodMk continuousOn_const
      exact hGs_cont.comp_continuousOn h1
  have T3 : Tendsto (fun u => (u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ)))
      - (∫ σ in s..b, Θs s σ (Z σ))) (𝓝[Set.Icc a b \ {s}] s) (𝓝 0) := by
    have hder' : HasDerivWithinAt (fun x => ∫ t in s..b, Θ x t (Z t))
        (∫ t in s..b, Θs s t (Z t)) (Set.Icc a b) s :=
      param_interval_deriv (a := a) (b := b) (c := s) (d := b)
        hs.2 hs hcont_Θ_box hcont_Θs_box (fun x hx t ht => hΘs x hx t (Z t))
    have h2 : Tendsto (fun u => (u - s)⁻¹ •
        ((∫ t in s..b, Θ u t (Z t)) - (∫ t in s..b, Θ s t (Z t))))
        (𝓝[Set.Icc a b \ {s}] s) (𝓝 (∫ t in s..b, Θs s t (Z t))) := by
      refine ((hasDerivWithinAt_iff_tendsto_slope).mp hder').congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u huA
      simp [slope]
    have h3 : Tendsto (fun u => (u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ))))
        (𝓝[Set.Icc a b \ {s}] s) (𝓝 (∫ σ in s..b, Θs s σ (Z σ))) := by
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u huA
      congr 1
      exact (intervalIntegral.integral_sub ((hcont_Θ_Icc u huA.1).intervalIntegrable_of_Icc hs.2)
        ((hcont_Θ_Icc s hs).intervalIntegrable_of_Icc hs.2)).symm
    simpa using h3.sub_const (∫ σ in s..b, Θs s σ (Z σ))
  -- ## combining the limits
  have hlim : Tendsto (fun u =>
      ((u - s)⁻¹ • (Ξ u - Ξ s) - Ξs s)
      + (-((u - s)⁻¹ • (∫ σ in s..u, Θ u σ (Z σ))) + Θ s s (Z s))
      + ((u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ))) - (∫ σ in s..b, Θs s σ (Z σ)))
      + (Gs s (Z s) - (u - s)⁻¹ • (∫ r in s..u, Gs r (Z u))))
      (𝓝[Set.Icc a b \ {s}] s) (𝓝 0) := by
    simpa using ((T1.add T2).add T3).add T4
  have htail : ∀ c > 0, ∀ᶠ u in 𝓝[Set.Icc a b \ {s}] s,
      ‖G s (Z u) - G s (Z s) - J (Z u - Z s)‖ ≤ c * ‖Z u - Z s‖ := by
    intro c hc
    have h1 : ∀ᶠ x in 𝓝 (Z s), ‖G s x - G s (Z s) - J (x - Z s)‖ ≤ c * ‖x - Z s‖ :=
      hlittle.def hc
    exact hZtend.eventually h1
  -- ## conclusion
  refine (hasDerivWithinAt_iff_tendsto_slope).mpr ?_
  rw [Metric.tendsto_nhds]
  intro η hη
  have hηB : 0 < η / (16 * B) := by positivity
  set c : ℝ := min (1 / (8 * B)) (η / (16 * B * (‖V s‖ + 1))) with hcdef
  have hcpos : 0 < c := lt_min (by positivity) (by positivity)
  have hcB : B * c ≤ 1 / 8 := by
    have h1 : c ≤ 1 / (8 * B) := by rw [hcdef]; exact min_le_left _ _
    calc B * c ≤ B * (1 / (8 * B)) := mul_le_mul_of_nonneg_left h1 hB.le
      _ = 1 / 8 := by field_simp
  have hcV : c * ‖V s‖ ≤ η / (16 * B) := by
    have h1 : c ≤ η / (16 * B * (‖V s‖ + 1)) := by rw [hcdef]; exact min_le_right _ _
    have hVnn : 0 ≤ ‖V s‖ := norm_nonneg _
    have h2 : 0 < 16 * B * (‖V s‖ + 1) := by positivity
    have h3 : η * ‖V s‖ / (‖V s‖ + 1) ≤ η := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖V s‖ + 1)]
      nlinarith [hη.le, hVnn]
    have h4 : c * ‖V s‖ ≤ (η / (16 * B * (‖V s‖ + 1))) * ‖V s‖ :=
      mul_le_mul_of_nonneg_right h1 hVnn
    have h5 : (η / (16 * B * (‖V s‖ + 1))) * ‖V s‖ = (η * ‖V s‖ / (‖V s‖ + 1)) / (16 * B) := by
      field_simp
    rw [h5] at h4
    calc c * ‖V s‖ ≤ (η * ‖V s‖ / (‖V s‖ + 1)) / (16 * B) := h4
      _ ≤ η / (16 * B) := by
          apply div_le_div_of_nonneg_right h3 (by positivity)
  have hsmall : ∀ᶠ u in 𝓝[Set.Icc a b \ {s}] s, ‖((u - s)⁻¹ • (Ξ u - Ξ s) - Ξs s)
      + (-((u - s)⁻¹ • (∫ σ in s..u, Θ u σ (Z σ))) + Θ s s (Z s))
      + ((u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ))) - (∫ σ in s..b, Θs s σ (Z σ)))
      + (Gs s (Z s) - (u - s)⁻¹ • (∫ r in s..u, Gs r (Z u)))‖ ≤ η / (16 * B) := by
    have h1 : ∀ᶠ u in 𝓝[Set.Icc a b \ {s}] s, ‖((u - s)⁻¹ • (Ξ u - Ξ s) - Ξs s)
        + (-((u - s)⁻¹ • (∫ σ in s..u, Θ u σ (Z σ))) + Θ s s (Z s))
        + ((u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ))) - (∫ σ in s..b, Θs s σ (Z σ)))
        + (Gs s (Z s) - (u - s)⁻¹ • (∫ r in s..u, Gs r (Z u)))‖ < η / (16 * B) := by
      have h := (Metric.tendsto_nhds.mp hlim.norm) (η / (16 * B)) hηB
      filter_upwards [h] with u hu
      simpa using hu
    filter_upwards [h1] with u hu
    exact le_of_lt hu
  filter_upwards [hsmall, htail c hcpos, self_mem_nhdsWithin] with u hu1 hu2 hu3
  have huI : u ∈ Set.Icc a b := hu3.1
  have hkey' := hkey u huI (fun h => hu3.2 (by simpa [h]))
  have hgam : ‖(u - s)⁻¹ • (G s (Z u) - G s (Z s) - J (Z u - Z s))‖ ≤ c * ‖slope Z s u‖ := by
    rw [norm_smul, show slope Z s u = (u - s)⁻¹ • (Z u - Z s) from rfl, norm_smul]
    have h1 : ‖G s (Z u) - G s (Z s) - J (Z u - Z s)‖ ≤ c * ‖Z u - Z s‖ := hu2
    have h2 : 0 ≤ |(u - s)⁻¹| := abs_nonneg _
    calc |(u - s)⁻¹| * ‖G s (Z u) - G s (Z s) - J (Z u - Z s)‖
        ≤ |(u - s)⁻¹| * (c * ‖Z u - Z s‖) := mul_le_mul_of_nonneg_left h1 h2
      _ = c * (|(u - s)⁻¹| * ‖Z u - Z s‖) := by ring
  have hJb : ‖J (slope Z s u - V s)‖ ≤ η / (16 * B) + c * ‖slope Z s u‖ := by
    rw [hkey']
    exact le_trans (norm_sub_le _ _) (add_le_add hu1 hgam)
  have hVsplit : ‖slope Z s u‖ ≤ ‖slope Z s u - V s‖ + ‖V s‖ := by
    calc ‖slope Z s u‖ = ‖(slope Z s u - V s) + V s‖ := by abel_nf
      _ ≤ ‖slope Z s u - V s‖ + ‖V s‖ := norm_add_le _ _
  have h1 : ‖A₀ (slope Z s u - V s)‖ ≤ κ * ‖slope Z s u - V s‖
      + (η / (16 * B) + c * ‖slope Z s u‖) := by
    have hsplit : A₀ (slope Z s u - V s) = (A₀ - J) (slope Z s u - V s) + J (slope Z s u - V s) := by
      rw [ContinuousLinearMap.sub_apply]; abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ hJb)
    calc ‖(A₀ - J) (slope Z s u - V s)‖ ≤ ‖A₀ - J‖ * ‖slope Z s u - V s‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ κ * ‖slope Z s u - V s‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          simpa [norm_sub_rev] using hJA
  have h2 : ‖slope Z s u - V s‖ ≤ B * ‖A₀ (slope Z s u - V s)‖ := by
    have h1 := hAinv s hs
    calc ‖slope Z s u - V s‖ = ‖((A s).symm : E →L[ℝ] E) (A₀ (slope Z s u - V s))‖ := by
          rw [hA₀def]; simp
      _ ≤ B * ‖A₀ (slope Z s u - V s)‖ :=
          le_trans (ContinuousLinearMap.le_opNorm _ _) (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  have h3 : ‖slope Z s u - V s‖
      ≤ (B * κ + B * c) * ‖slope Z s u - V s‖ + B * (η / (16 * B) + c * ‖V s‖) := by
    have h2' := mul_le_mul_of_nonneg_left h1 hB.le
    have h4 : B * (κ * ‖slope Z s u - V s‖ + (η / (16 * B) + c * ‖slope Z s u‖))
        ≤ (B * κ + B * c) * ‖slope Z s u - V s‖ + B * (η / (16 * B) + c * ‖V s‖) := by
      have h5 : c * ‖slope Z s u‖ ≤ c * (‖slope Z s u - V s‖ + ‖V s‖) :=
        mul_le_mul_of_nonneg_left hVsplit hcpos.le
      nlinarith [h5, hcpos.le, hB.le, norm_nonneg (slope Z s u - V s), norm_nonneg (V s),
        mul_nonneg hB.le hcpos.le]
    linarith [h2, h2', h4]
  have h5 : (1 - B * κ - B * c) * ‖slope Z s u - V s‖ ≤ B * (η / (16 * B) + c * ‖V s‖) := by
    nlinarith [h3, hκB', hcB]
  have h6 : (1:ℝ) / 4 ≤ 1 - B * κ - B * c := by linarith [hκB', hcB]
  have h7 : ‖slope Z s u - V s‖ ≤ 4 * (B * (η / (16 * B) + c * ‖V s‖)) := by
    nlinarith [h5, h6, norm_nonneg (slope Z s u - V s)]
  calc dist (slope Z s u) (V s) = ‖slope Z s u - V s‖ := dist_eq_norm _ _
    _ ≤ 4 * (B * (η / (16 * B) + c * ‖V s‖)) := h7
    _ ≤ 4 * (B * (η / (16 * B) + η / (16 * B))) := by
        have h8 : B * (η / (16 * B) + c * ‖V s‖) ≤ B * (η / (16 * B) + η / (16 * B)) :=
          mul_le_mul_of_nonneg_left (by linarith [hcV]) hB.le
        linarith
    _ = η / 2 := by field_simp; ring
    _ < η := by linarith



end Work.VolterraLong
