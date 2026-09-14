import Submission.NBody.WeakToStrong
import Submission.NBody.EnergyLevel

/-!
# Regularity of `h`-minimisers at the endpoints

An `h`-minimiser is `C²` on the interior of its interval of definition (`minimizer_contDiffOn_two`).
Here we show that it is `C¹` *up to the endpoints*: the velocity `deriv γ` has a limit at the left
endpoint, and the energy identity `½‖v‖²ₘ - U(γ a) = h` holds there.  This is the input needed to
read off *initial data* `(γ a, v)` of a minimiser, which the Maderna--Venturelli argument uses when
it approximates a calibrating curve by a sequence of `h`-minimisers.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **A Lipschitz function on an interval has a limit at the endpoint.**  If `f : ℝ → F` (with `F`
complete) satisfies a Lipschitz bound with constant `K ≥ 0` on `(a, c)`, then `f` has a limit at
`a` from the right. -/
theorem tendsto_atRight_of_dist_le_mul {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    {f : ℝ → F} {a c K : ℝ} (hac : a < c) (hK : 0 ≤ K)
    (hlip : ∀ s ∈ Set.Ioo a c, ∀ t ∈ Set.Ioo a c, dist (f s) (f t) ≤ K * dist s t) :
    ∃ v, Tendsto f (𝓝[>] a) (𝓝 v) := by
  have hCauchy : Cauchy (Filter.map f (𝓝[>] (a : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨?_, ?_⟩
    · have h : (𝓝[>] (a : ℝ)).NeBot := nhdsGT_neBot a
      exact map_neBot
    · intro ε hε
      set δ : ℝ := min (c - a) (ε / (K + 1)) with hδdef
      have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
      have hδca : δ ≤ c - a := min_le_left _ _
      refine ⟨f '' Set.Ioo a (a + δ), ?_, ?_⟩
      · refine mem_map.mpr (mem_of_superset (Ioo_mem_nhdsGT (a := a + δ) (b := a) (by linarith)) ?_)
        intro x hx; exact ⟨x, hx, rfl⟩
      · rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
        have hsc : s < c := by have := hs.2; linarith
        have htc : t < c := by have := ht.2; linarith
        calc dist (f s) (f t) ≤ K * dist s t := hlip s ⟨hs.1, hsc⟩ t ⟨ht.1, htc⟩
          _ = K * |s - t| := by rw [Real.dist_eq]
          _ < ε := by
              have h1 : |s - t| < δ := by
                rw [abs_lt]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
              have h2 : K * |s - t| ≤ K * δ := mul_le_mul_of_nonneg_left h1.le hK
              have h3 : K * δ ≤ K * (ε / (K + 1)) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) hK
              have h4 : K * (ε / (K + 1)) < ε := by
                rw [show K * (ε / (K + 1)) = K * ε / (K + 1) by ring, div_lt_iff₀ (by positivity)]
                nlinarith
              linarith
  obtain ⟨v, hv⟩ := CompleteSpace.complete hCauchy
  exact ⟨v, hv⟩

/-- **Left-endpoint regularity of an `h`-minimiser.**  The velocity of an `h`-minimiser has a limit
at the left endpoint, and the energy identity holds there. -/
theorem minimizer_deriv_tendsto_left {m : Fin N → ℝ} {h T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ 0 T)
    (hnc : ∀ t ∈ Set.Icc 0 T, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ 0 T)
    (hfin : actionPot m h (γ 0) (γ T) < ⊤) :
    ∃ v : EN E N, Tendsto (deriv γ) (𝓝[>] (0 : ℝ)) (𝓝 v) ∧
      (1 / 2) * (∑ i, m i * ‖v i‖ ^ 2) - U m (γ 0) = h := by
  classical
  have hc0 : (0 : ℝ) < T / 2 := by linarith
  have hcT : T / 2 < T := by linarith
  have hγcont : ContinuousOn γ (Set.Icc 0 T) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hT.le] at h
  have hgradcont : ContinuousOn (fun t => ∇_[m] (U m) (γ t)) (Set.Icc 0 T) :=
    continuousOn_weightedGrad_comp (continuousOn_fderiv_U_comp (m := m) hγcont hnc)
  have hgradc : ContinuousOn (fun t => ∇_[m] (U m) (γ t)) (Set.Icc 0 (T / 2)) :=
    hgradcont.mono (Set.Icc_subset_Icc_right hcT.le)
  obtain ⟨K, hK⟩ := (isCompact_Icc.image_of_continuousOn hgradc).isBounded.exists_norm_le
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK _ ⟨0, ⟨le_rfl, hc0.le⟩, rfl⟩)
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (deriv γ) (∇_[m] (U m) (γ t)) t :=
    minimizer_hasDerivAt_deriv hm hh hT hac hnc hmin hfin
  -- the Lipschitz bound on `(0, T/2)`
  have hmain : ∀ s ∈ Set.Ioo (0 : ℝ) (T / 2), ∀ t ∈ Set.Ioo (0 : ℝ) (T / 2), s ≤ t →
      dist (deriv γ s) (deriv γ t) ≤ K * dist s t := by
    intro s hs t ht hst
    have htT : t < T := by linarith [ht.2, hcT]
    have hsub : Set.uIcc s t ⊆ Set.Icc 0 T := by
      rw [uIcc_of_le hst]
      exact Set.Icc_subset_Icc hs.1.le htT.le
    have hFTC : deriv γ t - deriv γ s = ∫ x in s..t, ∇_[m] (U m) (γ x) := by
      have h' : (∫ x in s..t, ∇_[m] (U m) (γ x)) = deriv γ t - deriv γ s := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := deriv γ)
          (f' := fun x => ∇_[m] (U m) (γ x)) (a := s) (b := t) ?_ ?_
        · intro x hx
          rw [uIcc_of_le hst] at hx
          exact hderiv x ⟨lt_of_lt_of_le hs.1 hx.1, lt_of_le_of_lt hx.2 htT⟩
        · exact ContinuousOn.intervalIntegrable (hgradcont.mono hsub)
      exact h'.symm
    have hnorm : dist (deriv γ s) (deriv γ t) = ‖∫ x in s..t, ∇_[m] (U m) (γ x)‖ := by
      rw [dist_eq_norm, norm_sub_rev, hFTC]
    rw [hnorm, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
    calc ‖∫ x in s..t, ∇_[m] (U m) (γ x)‖
        ≤ ∫ x in s..t, ‖∇_[m] (U m) (γ x)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hst
      _ ≤ ∫ x in s..t, K := by
          refine intervalIntegral.integral_mono_on hst ?_ ?_ ?_
          · exact (ContinuousOn.intervalIntegrable (hgradcont.mono hsub)).norm
          · exact intervalIntegrable_const
          · intro x hx
            exact hK _ ⟨x, ⟨le_trans hs.1.le hx.1, le_trans hx.2 ht.2.le⟩, rfl⟩
      _ = K * (t - s) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hlip : ∀ s ∈ Set.Ioo (0 : ℝ) (T / 2), ∀ t ∈ Set.Ioo (0 : ℝ) (T / 2),
      dist (deriv γ s) (deriv γ t) ≤ K * dist s t := by
    intro s hs t ht
    rcases le_total s t with hst | hts
    · exact hmain s hs t ht hst
    · rw [dist_comm (deriv γ s) (deriv γ t), dist_comm s t]
      exact hmain t ht s hs hts
  obtain ⟨v, hv⟩ := tendsto_atRight_of_dist_le_mul (F := EN E N) (f := deriv γ)
    (a := 0) (c := T / 2) (K := K) hc0 hK0 hlip
  refine ⟨v, hv, ?_⟩
  -- the energy identity at the limit
  have hE : ∀ t ∈ Set.Ioo (0 : ℝ) T, energy m γ t = h :=
    minimizer_energy_eq_level hm hh hT hac hnc hmin hfin
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), energy m γ t = h := by
    filter_upwards [Ioo_mem_nhdsGT (a := T) (b := (0 : ℝ)) hT] with t ht using hE t ht
  have hconst : Tendsto (fun t => energy m γ t) (𝓝[>] (0 : ℝ)) (𝓝 h) :=
    tendsto_const_nhds.congr' (by filter_upwards [hev] with t ht using ht.symm)
  have hvi : ∀ i : Fin N, Tendsto (fun t : ℝ => deriv γ t i) (𝓝[>] (0 : ℝ)) (𝓝 (v i)) := fun i => by
    have h := ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin N => E) i).continuous.tendsto v).comp hv
    simpa [Function.comp_def, PiLp.proj_apply] using h
  have hγ0 : Tendsto (fun t : ℝ => γ t) (𝓝[>] (0 : ℝ)) (𝓝 (γ 0)) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδp⟩ := (Metric.continuousOn_iff.mp hγcont) 0 ⟨le_rfl, hT.le⟩ ε hε
    refine ⟨min δ T, lt_min hδ hT, ?_⟩
    intro x hx hxd
    have hxT : x ≤ T := by
      have h1 : dist x 0 < T := lt_of_lt_of_le hxd (min_le_right δ T)
      rw [Real.dist_eq, sub_zero, abs_of_pos hx] at h1
      exact h1.le
    have hxd' : dist x 0 < δ := lt_of_lt_of_le hxd (min_le_left δ T)
    exact hδp x ⟨le_of_lt hx, hxT⟩ hxd'
  have hUcont : ContinuousAt (U m) (γ 0) :=
    (continuousOn_U (m := m) (E := E) (N := N)).continuousAt
      (isOpen_setOf_withoutCollisions.mem_nhds (hnc 0 ⟨le_rfl, hT.le⟩))
  have hlim : Tendsto (fun t => energy m γ t) (𝓝[>] (0 : ℝ))
      (𝓝 ((1 / 2) * (∑ i, m i * ‖v i‖ ^ 2) - U m (γ 0))) := by
    have hkin : Tendsto (fun t : ℝ => (1 / 2) * (∑ i, m i * ‖deriv γ t i‖ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 / 2) * (∑ i, m i * ‖v i‖ ^ 2))) := by
      refine Tendsto.const_mul (1 / 2) ?_
      refine tendsto_finsetSum (Finset.univ : Finset (Fin N))
        (f := fun i t => m i * ‖deriv γ t i‖ ^ 2) (a := fun i => m i * ‖v i‖ ^ 2) ?_
      intro i _
      exact Tendsto.const_mul (m i) (((hvi i).norm).pow 2)
    have hpot : Tendsto (fun t : ℝ => U m (γ t)) (𝓝[>] (0 : ℝ)) (𝓝 (U m (γ 0))) :=
      hUcont.tendsto.comp hγ0
    exact hkin.sub hpot
  exact tendsto_nhds_unique hlim hconst

end Submission.NBody
