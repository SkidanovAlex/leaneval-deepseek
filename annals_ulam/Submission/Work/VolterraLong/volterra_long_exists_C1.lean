import Mathlib
import Submission.Work.VolterraLong.Main
import Submission.Work.VolterraLong.C1.interval_average_tendsto
import Submission.Work.VolterraLong.C1.param_interval_deriv
import Submission.Work.VolterraLong.C1.solve_near_equiv
import Submission.Work.VolterraLong.C1.data_diff_bound

/-!
# `C1` long-interval existence for the Volterra system

This file proves `Work.VolterraLong.volterra_long_exists_C1`: for data `G, Θ, Ξ` which is `ε`-close
to base data `(G₀,Θ₀,Ξ₀)` admitting a base solution `Z₀` (with derivative `Z₀s`), the Volterra
system `(★) G(s,Z s) = ∫_s^b Θ(s,σ,Z σ) dσ + Ξ s` has a solution on the whole interval `[a,b]`
whose derivative is `O(ε)`-close to `Z₀s`.

Existence of a solution `Z` is the long-interval fixed point theorem `volterra_long_exists`.  Its
derivative `V` is obtained from the *linearised* equation
`fderiv (G s) (Z s) (V s) = -Gs s (Z s) - Θ s s (Z s) + ∫_s^b Θs s σ (Z σ) + Ξs s`, solved
pointwise by the perturbed-inverse lemma `C1.solve_near_equiv` with quantitative bounds.  The
pointwise differentiability of `Z` (with derivative `V`) is `deriv_from_equation_aux`, built from
the two analytic side lemmas `C1.param_interval_deriv` (differentiation under the integral sign
within a closed interval) and `C1.interval_average_tendsto` (averaging on a shrinking interval).
Finally `exists_extension_hasDerivAt` extends `Z` off `[a,b]` so that the two-sided derivative at
the endpoints is the one-sided derivative of the solution.
-/

namespace Work.VolterraLong

open Set Filter MeasureTheory
open Work.VolterraLong.C1
open scoped Topology Interval

/-- If `σ` lies between `s` and `u`, then `(u, σ)` is at distance at most `dist u s` from `(s, s)`. -/
lemma dist_prod_pair_le {s u σ : ℝ} (hσ : σ ∈ Set.uIcc s u) :
    dist (u, σ) (s, s) ≤ dist u s := by
  rw [Prod.dist_eq, max_le_iff]
  refine ⟨le_rfl, ?_⟩
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total s u with h | h
  · rw [Set.uIcc_of_le h] at hσ
    rw [abs_of_nonneg (by linarith [hσ.1] : (0 : ℝ) ≤ σ - s),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - s)]
    linarith [hσ.2]
  · rw [Set.uIcc_of_ge h] at hσ
    rw [abs_of_nonpos (by linarith [hσ.2] : σ - s ≤ 0),
      abs_of_nonpos (by linarith : u - s ≤ 0)]
    linarith [hσ.1]

lemma deriv_from_equation_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → E → E} {Θ : ℝ → ℝ → E → E} {Ξ : ℝ → E} {Gs : ℝ → E → E}
    {Θs : ℝ → ℝ → E → E} {Ξs : ℝ → E} {Z₀ Z V : ℝ → E} {A : ℝ → E ≃L[ℝ] E}
    {B Cg K1 ε : ℝ} (hε : 0 < ε) (hB : 0 < B) (hCg : 0 ≤ Cg) (hK1 : 0 ≤ K1)
    (hAinv : ∀ s ∈ Set.Icc a b, ‖((A s).symm : E →L[ℝ] E)‖ ≤ B)
    (hZ : ContinuousOn Z (Set.Icc a b))
    (hZclose : ∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ K1 * ε) (hK1ε : K1 * ε ≤ 1)
    (hκB : B * (Cg * K1 * ε) ≤ 1 / 2)
    (hsol : ∀ s ∈ Set.Icc a b, G s (Z s) = (∫ σ in s..b, Θ s σ (Z σ)) + Ξ s)
    (hG : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ : Continuous Ξ)
    (hGs : ∀ s ∈ Set.Icc a b, ∀ z : E, HasDerivAt (fun u : ℝ => G u z) (Gs s z) s)
    (hGs_cont : Continuous (fun p : ℝ × E => Gs p.1 p.2))
    (hΘs : ∀ s ∈ Set.Icc a b, ∀ σ : ℝ, ∀ z : E, HasDerivAt (fun u : ℝ => Θ u σ z) (Θs s σ z) s)
    (hΘs_cont : Continuous (fun p : ℝ × ℝ × E => Θs p.1 p.2.1 p.2.2))
    (hΞs : ∀ s : ℝ, HasDerivAt Ξ (Ξs s) s) (hΞs_cont : Continuous Ξs)
    (hdiff : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      DifferentiableAt ℝ (fun w => G s w) z)
    (hder : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      ‖fderiv ℝ (fun w => G s w) z - (A s : E →L[ℝ] E)‖ ≤ Cg * ‖z - Z₀ s‖)
    (hV : ∀ s ∈ Set.Icc a b, fderiv ℝ (fun w => G s w) (Z s) (V s)
      = - Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s) :
    ∀ s ∈ Set.Icc a b, HasDerivWithinAt Z (V s) (Set.Icc a b) s := by
  intro s hs
  set J : E →L[ℝ] E := fderiv ℝ (fun w => G s w) (Z s) with hJdef
  set A₀ : E →L[ℝ] E := (A s : E →L[ℝ] E) with hA₀def
  set κ : ℝ := Cg * K1 * ε with hκdef
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
    calc ‖fderiv ℝ (fun w => G s w) (Z s) - (A s : E →L[ℝ] E)‖ ≤ Cg * ‖Z s - Z₀ s‖ := h1
      _ ≤ Cg * (K1 * ε) := mul_le_mul_of_nonneg_left h2 hCg
      _ = Cg * K1 * ε := by ring
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


lemma exists_extension_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a ≤ b) {Z V : ℝ → E}
    (hV : ∀ s ∈ Set.Icc a b, HasDerivWithinAt Z (V s) (Set.Icc a b) s) :
    ∃ Z' : ℝ → E, (∀ s ∈ Set.Icc a b, Z' s = Z s) ∧
      (∀ s ∈ Set.Icc a b, HasDerivAt Z' (V s) s) := by
  classical
  let Z' : ℝ → E := fun s => if s ≤ a then Z a + (s - a) • V a
    else if s ≤ b then Z s else Z b + (s - b) • V b
  have haff_a : HasDerivAt (fun s : ℝ => Z a + (s - a) • V a) (V a) a := by
    have h1 : HasDerivAt (fun s : ℝ => s - a) 1 a := (hasDerivAt_id a).sub_const a
    have h2 : HasDerivAt (fun s : ℝ => (s - a) • V a) ((1 : ℝ) • V a) a := h1.smul_const (V a)
    have h3 := h2.const_add (Z a)
    simpa using h3
  have haff_b : HasDerivAt (fun s : ℝ => Z b + (s - b) • V b) (V b) b := by
    have h1 : HasDerivAt (fun s : ℝ => s - b) 1 b := (hasDerivAt_id b).sub_const b
    have h2 : HasDerivAt (fun s : ℝ => (s - b) • V b) ((1 : ℝ) • V b) b := h1.smul_const (V b)
    have h3 := h2.const_add (Z b)
    simpa using h3
  have hZ'eq : ∀ s ∈ Set.Icc a b, Z' s = Z s := by
    intro s hs
    dsimp only [Z']
    rcases le_or_gt s a with h | h
    · rw [if_pos h]
      have hsa : s = a := le_antisymm h hs.1
      subst hsa
      simp
    · rw [if_neg (not_le.mpr h), if_pos hs.2]
  have hIic : Set.EqOn Z' (fun s : ℝ => Z a + (s - a) • V a) (Set.Iic a) := by
    intro s hs
    dsimp only [Z']
    rw [if_pos (Set.mem_Iic.mp hs)]
  have hIci : Set.EqOn Z' (fun s : ℝ => Z b + (s - b) • V b) (Set.Ici b) := by
    intro s hs
    have hbs : b ≤ s := Set.mem_Ici.mp hs
    dsimp only [Z']
    rcases le_or_gt s a with h1 | h1
    · rw [if_pos h1]
      have hsa' : s = a := le_antisymm h1 (le_trans hab hbs)
      have hab' : a = b := le_antisymm hab (le_trans hbs h1)
      rw [hsa', hab']
    · rw [if_neg (not_le.mpr h1)]
      rcases le_or_gt s b with h2 | h2
      · rw [if_pos h2]
        have hsb : s = b := le_antisymm h2 hbs
        rw [hsb]
        simp
      · rw [if_neg (not_le.mpr h2)]
  have hA : HasDerivWithinAt Z' (V a) (Set.Iic a) a :=
    haff_a.hasDerivWithinAt.congr hIic (hIic (by simp))
  have hB : HasDerivWithinAt Z' (V a) (Set.Icc a b) a :=
    (hV a (by simp [hab])).congr (fun x hx => hZ'eq x hx) (hZ'eq a (by simp [hab]))
  have hC : HasDerivWithinAt Z' (V b) (Set.Ici b) b :=
    haff_b.hasDerivWithinAt.congr hIci (hIci (by simp))
  have hD : HasDerivWithinAt Z' (V b) (Set.Icc a b) b :=
    (hV b (by simp [hab])).congr (fun x hx => hZ'eq x hx) (hZ'eq b (by simp [hab]))
  refine ⟨Z', hZ'eq, ?_⟩
  intro s hs
  rcases eq_or_lt_of_le hs.1 with hsa | hsa
  · subst hsa
    by_cases hab' : a = b
    · subst hab'
      have hunion : Set.Iic a ∪ Set.Ici a = Set.univ := Set.Iic_union_Ici
      have h2 : HasDerivWithinAt Z' (V a) Set.univ a := by
        rw [← hunion]; exact hA.union hC
      simpa using h2
    · have hlt : a < b := lt_of_le_of_ne hab hab'
      have hunion : Set.Iic a ∪ Set.Icc a b = Set.Iic b := Set.Iic_union_Icc_eq_Iic hab
      have h2 : HasDerivWithinAt Z' (V a) (Set.Iic b) a := by
        rw [← hunion]; exact hA.union hB
      exact h2.hasDerivAt (Iic_mem_nhds hlt)
  · rcases eq_or_lt_of_le hs.2 with hsb | hsb
    · subst hsb
      have hunion : Set.Icc a s ∪ Set.Ici s = Set.Ici a := Set.Icc_union_Ici_eq_Ici hsa.le
      have h2 : HasDerivWithinAt Z' (V s) (Set.Ici a) s := by
        rw [← hunion]; exact hD.union hC
      exact h2.hasDerivAt (Ici_mem_nhds hsa)
    · have h1 : HasDerivAt Z (V s) s := (hV s hs).hasDerivAt (Icc_mem_nhds hsa hsb)
      refine h1.congr_of_eventuallyEq ?_
      have hε : 0 < min (s - a) (b - s) := lt_min (sub_pos.mpr hsa) (sub_pos.mpr hsb)
      filter_upwards [Metric.ball_mem_nhds s hε] with x hx
      have hxa : a < x := by
        have h2 : dist x s < s - a := lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_left _ _)
        rw [dist_eq_norm, Real.norm_eq_abs] at h2
        have := abs_lt.mp h2
        linarith [this.1]
      have hxb : x ≤ b := by
        have h2 : dist x s < b - s := lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_right _ _)
        rw [dist_eq_norm, Real.norm_eq_abs] at h2
        have := abs_lt.mp h2
        linarith [this.2]
      dsimp only [Z']
      rw [if_neg (not_le.mpr hxa), if_pos hxb]
theorem volterra_long_exists_C1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E ≃L[ℝ] E) (G0 G : ℝ → E → E) (Θ0 Θ : ℝ → ℝ → E → E) (Ξ0 Ξ : ℝ → E)
    (G0s Gs : ℝ → E → E) (Θ0s Θs : ℝ → ℝ → E → E) (Ξ0s Ξs : ℝ → E) (Z₀ Z₀s : ℝ → E)
    {B L Cg LG L1 : ℝ} (hB : 0 < B) (hL : 0 ≤ L) (hCg : 0 ≤ Cg) (hLG : 0 ≤ LG) (hL1 : 0 ≤ L1)
    (hA_spec : ∀ s ∈ Set.Icc a b, (A s : E →L[ℝ] E) = fderiv ℝ (fun z => G0 s z) (Z₀ s))
    (hA_cont : ContinuousOn (fun s => ((A s).symm : E →L[ℝ] E)) (Set.Icc a b))
    (hAb : ∀ s ∈ Set.Icc a b, ‖((A s).symm : E →L[ℝ] E)‖ ≤ B)
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ)
    (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b))
    (hZ₀s : ∀ s ∈ Set.Icc a b, HasDerivAt Z₀ (Z₀s s) s)
    (hZ₀s_cont : ContinuousOn Z₀s (Set.Icc a b))
    (hΘ0_cont : Continuous (fun p : ℝ × ℝ × E => Θ0 p.1 p.2.1 p.2.2))
    (hbase : ∀ s ∈ Set.Icc a b, G0 s (Z₀ s) = (∫ σ in s..b, Θ0 s σ (Z₀ σ)) + Ξ0 s)
    (hΘ_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) 1, ‖Θ s σ z - Θ s σ z'‖ ≤ L * ‖z - z'‖)
    (hdiff : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      DifferentiableAt ℝ (fun w => G s w) z)
    (hGs : ∀ s ∈ Set.Icc a b, ∀ z : E, HasDerivAt (fun u : ℝ => G u z) (Gs s z) s)
    (hG0s : ∀ s ∈ Set.Icc a b, ∀ z : E, HasDerivAt (fun u : ℝ => G0 u z) (G0s s z) s)
    (hΘs : ∀ s ∈ Set.Icc a b, ∀ σ : ℝ, ∀ z : E, HasDerivAt (fun u : ℝ => Θ u σ z) (Θs s σ z) s)
    (hΘ0s : ∀ s ∈ Set.Icc a b, ∀ σ : ℝ, ∀ z : E, HasDerivAt (fun u : ℝ => Θ0 u σ z) (Θ0s s σ z) s)
    (hΞs : ∀ s : ℝ, HasDerivAt Ξ (Ξs s) s)
    (hΞ0s : ∀ s : ℝ, HasDerivAt Ξ0 (Ξ0s s) s)
    (hGs_cont : Continuous (fun p : ℝ × E => Gs p.1 p.2))
    (hG0s_cont : Continuous (fun p : ℝ × E => G0s p.1 p.2))
    (hΘs_cont : Continuous (fun p : ℝ × ℝ × E => Θs p.1 p.2.1 p.2.2))
    (hΘ0s_cont : Continuous (fun p : ℝ × ℝ × E => Θ0s p.1 p.2.1 p.2.2))
    (hΞs_cont : Continuous Ξs) (hΞ0s_cont : Continuous Ξ0s)
    (hGs_lip : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      ∀ z' ∈ Metric.closedBall (Z₀ s) 1, ‖Gs s z - Gs s z'‖ ≤ LG * ‖z - z'‖)
    (hΘs_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) 1, ‖Θs s σ z - Θs s σ z'‖ ≤ L1 * ‖z - z'‖)
    (hbase_s : ∀ s ∈ Set.Icc a b, G0s s (Z₀ s) + (fderiv ℝ (fun z => G0 s z) (Z₀ s)) (Z₀s s)
      = - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s)
    (hder : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      ‖fderiv ℝ (fun w => G s w) z - (A s : E →L[ℝ] E)‖ ≤ Cg * ‖z - Z₀ s‖) :
    ∃ K1 K2 ε₀ : ℝ, 0 < K1 ∧ 0 < K2 ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∀ s ∈ Set.Icc a b, dist (Ξ s) (Ξ0 s) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1, dist (G s z) (G0 s z) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
        dist (Θ s σ z) (Θ0 s σ z) < ε) →
      (∀ s ∈ Set.Icc a b, dist (Ξs s) (Ξ0s s) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1, dist (Gs s z) (G0s s z) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
        dist (Θs s σ z) (Θ0s s σ z) < ε) →
      ∃ Z : ℝ → E, ContinuousOn Z (Set.Icc a b) ∧ Work.VolterraLong.SolvesOn a b G Θ Ξ Z ∧
        (∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ K1 * ε) ∧
        (∀ s ∈ Set.Icc a b, dist (deriv Z s) (Z₀s s) ≤ K2 * ε) := by

  classical
  obtain ⟨ε₀₁, hε₀₁pos, hexist⟩ := Work.VolterraLong.volterra_long_exists hab A G0 G Θ0 Θ Ξ0 Ξ Z₀ hB hL hCg
    hA_spec hA_cont hAb hG_cont hΘ_cont hΞ_cont hZ₀_cont hΘ0_cont hbase hΘ_lip hdiff
  set K1 : ℝ := 2 * B * (2 + (b - a)) * Real.exp ((4 * B * L + 1) * (b - a)) with hK1def
  have hK1pos : 0 < K1 := by
    rw [hK1def]
    have h1 : (0:ℝ) < 2 + (b - a) := by linarith
    positivity
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ s ∈ Set.Icc a b, ‖Z₀s s‖ ≤ S := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hZ₀s_cont
    exact ⟨max C 0, fun s hs => le_trans (hC s hs) (le_max_left C 0)⟩
  have hSnonneg : 0 ≤ S := le_trans (norm_nonneg _) (hS a (by simp [hab]))
  set M : ℝ := (1 + LG * K1) + (1 + L * K1) + (b - a + 1) * (1 + L1 * K1) + 1 with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    have h1 : 0 ≤ LG * K1 := mul_nonneg hLG hK1pos.le
    have h2 : 0 ≤ L * K1 := mul_nonneg hL hK1pos.le
    have h3 : 0 ≤ L1 * K1 := mul_nonneg hL1 hK1pos.le
    have h4 : 0 ≤ (b - a + 1) * (1 + L1 * K1) := by
      have h5 : (0:ℝ) ≤ b - a + 1 := by linarith
      positivity
    linarith
  set K2 : ℝ := 2 * B * (Cg * K1 * S + M) with hK2def
  have hK2pos : 0 < K2 := by
    rw [hK2def]
    have h1 : 0 ≤ Cg * K1 * S := by positivity
    positivity
  set ε₀ : ℝ := min ε₀₁ (1 / (1 + K1 + 2 * B * Cg * K1)) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    refine lt_min hε₀₁pos ?_
    have h1 : 0 < 1 + K1 + 2 * B * Cg * K1 := by positivity
    positivity
  refine ⟨K1, K2, ε₀, hK1pos, hK2pos, hε₀pos, ?_⟩
  intro ε hε hεε₀ hΞc hGc hΘc hΞsc hGsc hΘsc
  have hε₁ : ε < ε₀₁ := lt_of_lt_of_le hεε₀ (min_le_left _ _)
  have hε₂ : ε < 1 / (1 + K1 + 2 * B * Cg * K1) := lt_of_lt_of_le hεε₀ (min_le_right _ _)
  have hden : 0 < 1 + K1 + 2 * B * Cg * K1 := by positivity
  have hεden : ε * (1 + K1 + 2 * B * Cg * K1) < 1 := (lt_div_iff₀ hden).mp hε₂
  have h2BCgK1 : 0 ≤ 2 * B * Cg * K1 := by positivity
  have hK1ε : K1 * ε ≤ 1 := by
    have hstep : ε * K1 ≤ ε * (1 + K1 + 2 * B * Cg * K1) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      linarith
    have hlt : K1 * ε < 1 := by
      calc K1 * ε = ε * K1 := by ring
        _ ≤ ε * (1 + K1 + 2 * B * Cg * K1) := hstep
        _ < 1 := hεden
    exact le_of_lt hlt
  have hκ1 : B * (Cg * K1 * ε) ≤ 1 / 2 := by
    have hstep : ε * (2 * B * Cg * K1) ≤ ε * (1 + K1 + 2 * B * Cg * K1) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      linarith
    have h2 : 2 * B * Cg * K1 * ε < 1 := by
      calc 2 * B * Cg * K1 * ε = ε * (2 * B * Cg * K1) := by ring
        _ ≤ ε * (1 + K1 + 2 * B * Cg * K1) := hstep
        _ < 1 := hεden
    linarith
  obtain ⟨Z, hZcont, hZsol, hZclose⟩ := hexist ε hε hε₁ hΞc hGc hΘc
    (fun s hs z hz => le_trans (hder s hs z hz) (le_add_of_nonneg_right hε.le))
  have hZclose' : ∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ K1 * ε := by
    intro s hs
    have h := hZclose s hs
    rwa [hK1def]
  have hZs_mem : ∀ s ∈ Set.Icc a b, Z s ∈ Metric.closedBall (Z₀ s) 1 := by
    intro s hs
    rw [Metric.mem_closedBall]
    exact le_trans (hZclose' s hs) hK1ε
  have hderJ : ∀ s ∈ Set.Icc a b,
      ‖fderiv ℝ (fun w => G s w) (Z s) - (A s : E →L[ℝ] E)‖ ≤ Cg * K1 * ε := by
    intro s hs
    have h1 := hder s hs (Z s) (hZs_mem s hs)
    have h2 : ‖Z s - Z₀ s‖ ≤ K1 * ε := by
      have h3 := hZclose' s hs
      rwa [dist_eq_norm] at h3
    have h4 : Cg * ‖Z s - Z₀ s‖ ≤ Cg * (K1 * ε) := mul_le_mul_of_nonneg_left h2 hCg
    calc ‖fderiv ℝ (fun w => G s w) (Z s) - (A s : E →L[ℝ] E)‖
        ≤ Cg * ‖Z s - Z₀ s‖ := h1
      _ ≤ Cg * (K1 * ε) := h4
      _ = Cg * K1 * ε := by ring
  have hexistsV : ∀ s ∈ Set.Icc a b, ∃ v : E,
      fderiv ℝ (fun w => G s w) (Z s) v
        = (- Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s)
      ∧ ‖v - Z₀s s‖ ≤ K2 * ε := by
    intro s hs
    have hdata := data_diff_bound hab hε hK1pos.le hL hLG hL1 hZclose' hK1ε
      hZcont hZ₀_cont hΘs_cont hΘ0s_cont hGs_lip hΘ_lip hΘs_lip hGsc hΘc hΘsc hΞsc s hs
    have hδ : ‖(- Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s)
        - (- G0s s (Z₀ s) - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s)‖ ≤ M * ε := by
      rw [hMdef]; exact hdata
    have hbase' : (A s : E →L[ℝ] E) (Z₀s s)
        = (- G0s s (Z₀ s) - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s) := by
      have h := hbase_s s hs
      rw [← hA_spec s hs] at h
      have h2 : (A s : E →L[ℝ] E) (Z₀s s)
          = - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s - G0s s (Z₀ s) := by
        rw [← h]; abel
      rw [h2]; abel
    obtain ⟨v, hv1, hv2⟩ := solve_near_equiv (A := A s)
      (J := fderiv ℝ (fun w => G s w) (Z s))
      (B := B) (κ := Cg * K1 * ε) (δ := M * ε) hB (hAb s hs) (hderJ s hs) hκ1 hbase' hδ
    refine ⟨v, hv1, le_trans hv2 ?_⟩
    rw [hK2def]
    have hb1 : (Cg * K1 * ε) * ‖Z₀s s‖ ≤ (Cg * K1 * S) * ε := by
      calc (Cg * K1 * ε) * ‖Z₀s s‖ = (Cg * K1 * ‖Z₀s s‖) * ε := by ring
        _ ≤ (Cg * K1 * S) * ε := by
            apply mul_le_mul_of_nonneg_right _ hε.le
            exact mul_le_mul_of_nonneg_left (hS s hs) (by positivity)
    nlinarith [hb1, hB, hε.le, hMpos.le]
  let V : ℝ → E := fun s => if h : s ∈ Set.Icc a b then Classical.choose (hexistsV s h) else 0
  have hVeq : ∀ s ∈ Set.Icc a b, fderiv ℝ (fun w => G s w) (Z s) (V s)
      = (- Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s) := by
    intro s hs
    dsimp only [V]
    rw [dif_pos hs]
    exact (Classical.choose_spec (hexistsV s hs)).1
  have hVclose : ∀ s ∈ Set.Icc a b, dist (V s) (Z₀s s) ≤ K2 * ε := by
    intro s hs
    dsimp only [V]
    rw [dif_pos hs, dist_eq_norm]
    exact (Classical.choose_spec (hexistsV s hs)).2
  have hVderiv : ∀ s ∈ Set.Icc a b, HasDerivWithinAt Z (V s) (Set.Icc a b) s :=
    deriv_from_equation_aux (hab := hab) (hε := hε) (hB := hB) (hCg := hCg)
      (hK1 := hK1pos.le) (hAinv := hAb) (hZ := hZcont) (hZclose := hZclose')
      (hK1ε := hK1ε) (hκB := hκ1) (hsol := hZsol) (hG := hG_cont) (hΘ := hΘ_cont)
      (hΞ := hΞ_cont) (hGs := hGs) (hGs_cont := hGs_cont) (hΘs := hΘs)
      (hΘs_cont := hΘs_cont) (hΞs := hΞs) (hΞs_cont := hΞs_cont) (hdiff := hdiff)
      (hder := hder) (hV := hVeq)
  obtain ⟨Z', hZ'eq, hZ'deriv⟩ := exists_extension_hasDerivAt hab hVderiv
  refine ⟨Z', ?_, ?_, ?_, ?_⟩
  · exact hZcont.congr (fun s hs => hZ'eq s hs)
  · intro s hs
    rw [hZ'eq s hs]
    have hcongr : (∫ σ in s..b, Θ s σ (Z' σ)) = (∫ σ in s..b, Θ s σ (Z σ)) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      have hx' : x ∈ Set.Icc a b := by
        have h1 : x ∈ Set.uIcc s b := hx
        rw [Set.uIcc_of_le hs.2] at h1
        exact ⟨le_trans hs.1 h1.1, h1.2⟩
      rw [hZ'eq x hx']
    rw [hcongr]
    exact hZsol s hs
  · intro s hs
    rw [hZ'eq s hs]
    exact hZclose' s hs
  · intro s hs
    have hderiv : deriv Z' s = V s := (hZ'deriv s hs).deriv
    rw [hderiv]
    exact hVclose s hs


end Work.VolterraLong
