/-
  WilE7 / CS-slice, node N1a (the arc form of "nondegenerate zeros do not accumulate").

  `no_arc_nondegenerate_zeros`: an analytic arc `γ` through `0` cannot run, for all small `s > 0`,
  through points `γ s ≠ 0` at which `g` vanishes with surjective differential.

  The proof is elementary and does not need curve selection:

  * `g ∘ γ` vanishes on the open interval `(0, ε)`, so on the sub-interval `(0, δ)`
    (where `δ` is small enough that `γ` is analytic near every point) its derivative is `0`;
  * the chain rule gives `fderiv g (γ s) ∘ fderiv γ s = 0`;
  * at such an `s` the differential `fderiv ℝ g (γ s)` is a surjective endomorphism of the
    finite dimensional space `Fin j → ℝ`, hence *injective*, so `fderiv ℝ γ s = 0`;
  * `γ` therefore has zero derivative on the convex open set `(0, δ)`, hence is constant there,
    and continuity at `0` together with `γ 0 = 0` forces that constant to be `0` —
    contradicting `γ s ≠ 0`.

  No extra hypothesis (e.g. analytic curve selection) is needed; the reduction of the *closure*
  statement `nondegZeros_not_accum` to this arc statement is what uses curve selection.
-/
import Mathlib
import Submission.Work.WilE7.FrontierCS.eventually_ne_of_range_top

open Set Filter Topology
open scoped Topology

namespace Work.WilE7.FrontierCS

theorem no_arc_nondegenerate_zeros {j : ℕ} {g : (Fin j → ℝ) → (Fin j → ℝ)}
    (hg : AnalyticOnNhd ℝ g Set.univ) {γ : ℝ → (Fin j → ℝ)}
    (hγ : AnalyticAt ℝ γ 0) (hγ0 : γ 0 = 0) :
    ¬ ∃ ε > (0 : ℝ), ∀ s ∈ Set.Ioo (0 : ℝ) ε,
      γ s ≠ 0 ∧ g (γ s) = 0 ∧ (fderiv ℝ g (γ s)).range = ⊤ := by
  rintro ⟨ε, hε, h⟩
  -- A radius on which `γ` is analytic at every point.
  obtain ⟨r, hr, hball⟩ := hγ.exists_ball_analyticOnNhd
  set δ : ℝ := min r ε with hδ
  have hδpos : 0 < δ := by rw [hδ]; exact lt_min hr hε
  have hU_ball : Set.Ioo (0:ℝ) δ ⊆ Metric.ball (0:ℝ) r := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs.1]
    rw [hδ] at hs
    exact lt_of_lt_of_le hs.2 (min_le_left _ _)
  have hU_Ioo : Set.Ioo (0:ℝ) δ ⊆ Set.Ioo (0:ℝ) ε := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    rw [hδ] at hs; exact lt_of_lt_of_le hs.2 (min_le_right _ _)
  -- On `(0, δ)` the derivative of `γ` vanishes.
  have key : ∀ s ∈ Set.Ioo (0:ℝ) δ, fderiv ℝ γ s = 0 := by
    intro s hs
    have hsr : s ∈ Metric.ball (0:ℝ) r := hU_ball hs
    have han : AnalyticAt ℝ γ s := hball s hsr
    have hγd : DifferentiableAt ℝ γ s := han.differentiableAt
    have hgd : DifferentiableAt ℝ g (γ s) := (hg (γ s) trivial).differentiableAt
    have hse : s ∈ Set.Ioo (0:ℝ) ε := hU_Ioo hs
    have hsurj : (fderiv ℝ g (γ s)).range = ⊤ := (h s hse).2.2
    have heq : (g ∘ γ) =ᶠ[𝓝 s] (fun _ => (0 : Fin j → ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hse] with t ht
      exact (h t ht).2.1
    have h1 : fderiv ℝ (g ∘ γ) s = 0 := by
      rw [heq.fderiv_eq]; simp
    have h2 := fderiv_comp (𝕜 := ℝ) (f := γ) (g := g) s hgd hγd
    rw [h2] at h1
    -- A surjective endomorphism of `Fin j → ℝ` is injective.
    have hinj : Function.Injective (fderiv ℝ g (γ s)) := by
      have hsurj' : Function.Surjective
          ((fderiv ℝ g (γ s) : (Fin j → ℝ) →L[ℝ] (Fin j → ℝ)) :
            (Fin j → ℝ) →ₗ[ℝ] (Fin j → ℝ)) := LinearMap.range_eq_top.mp hsurj
      exact LinearMap.injective_iff_surjective.mpr hsurj'
    refine ContinuousLinearMap.ext fun v => ?_
    have hv : (fderiv ℝ g (γ s)) ((fderiv ℝ γ s) v) = 0 := by
      have := congrArg (fun L : ℝ →L[ℝ] (Fin j → ℝ) => L v) h1
      simpa using this
    exact hinj (hv.trans (map_zero _).symm)
  have hdiff : DifferentiableOn ℝ γ (Set.Ioo (0:ℝ) δ) :=
    fun s hs => (hball s (hU_ball hs)).differentiableAt.differentiableWithinAt
  have hfac : Set.EqOn (fderiv ℝ γ) 0 (Set.Ioo (0:ℝ) δ) := fun s hs => key s hs
  obtain ⟨a, ha⟩ := isOpen_Ioo.exists_is_const_of_fderiv_eq_zero isPreconnected_Ioo hdiff hfac
  -- `γ` is constant with value `a` on `(0, δ)`; continuity at `0` forces `a = γ 0 = 0`.
  have ha0 : a = 0 := by
    have hmem : Set.Ioo (0:ℝ) δ ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT hδpos
    have hconst : (fun _ => a) =ᶠ[𝓝[>] (0:ℝ)] γ := by
      filter_upwards [hmem] with x hx using (ha x hx).symm
    have ht1 : Tendsto γ (𝓝[>] (0:ℝ)) (𝓝 a) :=
      Filter.Tendsto.congr' hconst tendsto_const_nhds
    have ht2 : Tendsto γ (𝓝[>] (0:ℝ)) (𝓝 (γ 0)) :=
      hγ.continuousAt.mono_left nhdsWithin_le_nhds
    have := tendsto_nhds_unique ht1 ht2
    rwa [hγ0] at this
  have hs0 : δ/2 ∈ Set.Ioo (0:ℝ) δ := ⟨by linarith, by linarith⟩
  exact (h (δ/2) (hU_Ioo hs0)).1 (by rw [ha (δ/2) hs0, ha0])

end Work.WilE7.FrontierCS
