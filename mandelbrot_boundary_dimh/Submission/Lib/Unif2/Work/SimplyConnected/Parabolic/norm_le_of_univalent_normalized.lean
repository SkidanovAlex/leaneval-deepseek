import Mathlib
import Submission.Lib.Unif2.Work.Parabolic.Basic
import Submission.Lib.Unif2.UnivalentCompactness
import Submission.Lib.Unif2.Work.SimplyConnected.Parabolic.PlanarEstimates
import Submission.Lib.Unif2.Work.SimplyConnected.Parabolic.exists_bound_of_bound_on_ball
import Submission.Lib.Unif2.Work.SimplyConnected.Parabolic.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.Parabolic.ChartPlumbing

/-!
# Local boundedness of normalised univalent families on a Riemann surface

Hubbard, *Teichmüller theory* Vol. 1, Chapter 1 (the uniformization theorem), the "normal
families" step of the parabolic case (Anghel–Bruin–Stan, Appendix AC): a family of injective
holomorphic `ψ : X → ℂ`, holomorphic and injective on open connected domains `Ω ⊇ U`, normalised by
`ψ x₀ = 0` and `deriv (ψ ∘ chart) (chart x₀) = 1` in the preferred chart at `x₀`, is *uniformly*
bounded on every compact subset of `U`.

The proof is the classical one, in a form that avoids hyperbolic metrics.  The universal growth
bound for normalised univalent functions on the unit disc (`Submission.UnivalentCompactness`) is
rescaled at a point of the surface to give a growth estimate on a disc there, and Cauchy's estimate
converts a value bound on a small disc at a point into a value bound on a larger disc around it
(`exists_bound_of_bound_on_ball`).  The set `S` of points where the family is bounded on a
*neighbourhood* is open by definition and closed in `U` by that one-step propagation, so it
exhausts the connected set `U`; compactness of `K` then produces a single bound.
-/

namespace Work.SimplyConnected.Parabolic

set_option maxHeartbeats 800000

open scoped Topology Manifold ContDiff
open Filter Metric Set

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X}

theorem isOpen_goodSet (x₀ : X) (U : Set X) : IsOpen (goodSet x₀ U) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨V, hVo, hVU, hzV, hbdd⟩
  exact Filter.mem_of_superset (hVo.mem_nhds hzV) fun z' hz' => ⟨V, hVo, hVU, hz', hbdd⟩

/-- **The seed.**  At the normalisation point the family is bounded on a chart ball, by the growth
bound applied to the chart representation (`f p = 0`, `deriv f p = 1`). -/
theorem mem_goodSet_self {U : Set X} (hUo : IsOpen U) (hx₀ : x₀ ∈ U) {C : ℝ}
    (hC : HasGrowthBound C) : x₀ ∈ goodSet x₀ U := by
  obtain ⟨ρ, hρ, htgt, hUsub⟩ := exists_chart_ball_subset (X := X) hUo hx₀
  set R : ℝ := ρ / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRρ : R < ρ := by rw [hRdef]; linarith
  have hhalfpos : 0 < R / 2 := by linarith
  have hhalfρ : R / 2 ≤ ρ := by linarith
  have hhalfR : R / 2 ≤ R := by linarith
  have hsubρ : Metric.ball ((chartAt ℂ x₀) x₀) R ⊆ Metric.ball ((chartAt ℂ x₀) x₀) ρ :=
    Metric.ball_subset_ball hRρ.le
  have hsubhalf : Metric.ball ((chartAt ℂ x₀) x₀) (R / 2) ⊆ Metric.ball ((chartAt ℂ x₀) x₀) ρ :=
    Metric.ball_subset_ball hhalfρ
  -- the chart representation is analytic and injective on the ball of radius `R`
  have htgtR : Metric.ball ((chartAt ℂ x₀) x₀) R ⊆ (chartAt ℂ x₀).target :=
    fun w hw => htgt (hsubρ hw)
  have hthalf : Metric.ball ((chartAt ℂ x₀) x₀) (R / 2) ⊆ (chartAt ℂ x₀).target :=
    fun w hw => htgt (hsubhalf hw)
  have hsubR : (chartAt ℂ x₀).symm '' Metric.ball ((chartAt ℂ x₀) x₀) R ⊆
      U ∩ (chartAt ℂ x₀).source := by
    rintro w ⟨u, hu, rfl⟩
    exact ⟨hUsub ⟨u, hsubρ hu, rfl⟩, (chartAt ℂ x₀).map_target (htgt (hsubρ hu))⟩
  refine ⟨(chartAt ℂ x₀).symm '' Metric.ball ((chartAt ℂ x₀) x₀) (R / 2),
    (chartAt ℂ x₀).isOpen_image_symm_of_subset_target Metric.isOpen_ball hthalf,
    (fun w hw => by
      obtain ⟨u, hu, rfl⟩ := hw
      exact hUsub ⟨u, hsubhalf hu, rfl⟩),
    ⟨(chartAt ℂ x₀) x₀, Metric.mem_ball_self hhalfpos,
      (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)⟩,
    R * growthFun C (1 / 2), by
      exact mul_nonneg hRpos.le (growthFun_nonneg hC.1 (by norm_num) (by norm_num)), ?_⟩
  rintro Ω hΩo hΩc hUΩ ψ hψ hinj h0 hder x ⟨w, hw, rfl⟩
  have han := analyticAt_comp_chartAt_symm (X := X) (Ω := Ω) (U := U) (ψ := ψ) (z := x₀)
    (a := (chartAt ℂ x₀) x₀) (ρ := R) hψ hUΩ hsubR htgtR
  have hinj' := injOn_comp_chartAt_symm (X := X) (Ω := Ω) (U := U) (ψ := ψ) (z := x₀)
    (a := (chartAt ℂ x₀) x₀) (ρ := R) hinj hUΩ hsubR htgtR
  have hf0 : (ψ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
    show ψ ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀)) = 0
    rw [(chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)]
    exact h0
  have hgrowth := norm_sub_le_of_growth hC.1 hC.2 hRpos han hinj'
    (by rw [hder]; exact one_ne_zero)
  have hwR : w ∈ Metric.ball ((chartAt ℂ x₀) x₀) R := Metric.ball_subset_ball hhalfR hw
  have h1 := hgrowth w hwR
  rw [hf0, hder, norm_one, mul_one] at h1
  have h2 : ‖w - (chartAt ℂ x₀) x₀‖ / R ≤ 1 / 2 := by
    rw [div_le_iff₀ hRpos]
    have := hw
    rw [Metric.mem_ball, dist_eq_norm] at this
    linarith
  have h3 : growthFun C (‖w - (chartAt ℂ x₀) x₀‖ / R) ≤ growthFun C (1 / 2) :=
    growthFun_mono hC.1 (by positivity) h2 (by norm_num)
  have h4 : ‖(ψ ∘ (chartAt ℂ x₀).symm) w‖ ≤ R * growthFun C (1 / 2) := by
    simpa using h1.trans (mul_le_mul_of_nonneg_left h3 hRpos.le)
  simpa using h4

/-- **The propagation (closedness) step.**  If a point `z ∈ U` is a limit of points at which the
family is locally uniformly bounded, then the family is uniformly bounded on a neighbourhood of `z`:
one propagation step (`exists_bound_of_bound_on_ball`) from a witness at a nearby point `y` bounds
the family on a chart ball around `z`. -/
theorem mem_goodSet_of_mem_closure {U : Set X} (hUo : IsOpen U) {C : ℝ} (hC : HasGrowthBound C)
    {z : X} (hzU : z ∈ U) (hzcl : z ∈ closure (goodSet x₀ U)) : z ∈ goodSet x₀ U := by
  obtain ⟨ρ, hρ, htgt, hUsub⟩ := exists_chart_ball_subset (X := X) hUo hzU
  have hε : (0 : ℝ) < ρ / 8 := by linarith only [hρ]
  have hερ : ρ / 8 < ρ := by linarith only [hρ]
  have hhalf : (0 : ℝ) < ρ / 2 := by linarith only [hρ]
  -- a point `y` of `goodSet` in the chart source, close to `z`
  have hnhds : (chartAt ℂ z).source ∩ (chartAt ℂ z) ⁻¹' Metric.ball ((chartAt ℂ z) z) (ρ / 8) ∈ 𝓝 z :=
    Filter.inter_mem ((chartAt ℂ z).open_source.mem_nhds (mem_chart_source ℂ z))
      (((chartAt ℂ z).continuousAt (mem_chart_source ℂ z)).preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)))
  obtain ⟨y, hyW, hyS⟩ :=
    mem_closure_iff_nhds.mp hzcl ((chartAt ℂ z).source ∩
      (chartAt ℂ z) ⁻¹' Metric.ball ((chartAt ℂ z) z) (ρ / 8)) hnhds
  obtain ⟨hySrc, hyClose⟩ := hyW
  obtain ⟨V, hVo, hVU, hyV, B, hB0, hB⟩ := hyS
  -- a chart ball around `y` inside the witness `V`
  have hcyTgt : (chartAt ℂ z) y ∈ (chartAt ℂ z).target := (chartAt ℂ z).map_source hySrc
  have hyV' : (chartAt ℂ z).symm ((chartAt ℂ z) y) ∈ V := by
    rw [(chartAt ℂ z).left_inv hySrc]; exact hyV
  obtain ⟨s, hs, hsV⟩ := Metric.mem_nhds_iff.mp
    (((chartAt ℂ z).continuousAt_symm hcyTgt).preimage_mem_nhds (hVo.mem_nhds hyV'))
  -- shrink it so that it is smaller than the analyticity radius
  have hs' : (0 : ℝ) < min s (ρ / 4) := lt_min hs (by linarith only [hρ])
  have hs's : min s (ρ / 4) ≤ s := min_le_left s (ρ / 4)
  have hs'ρ : min s (ρ / 4) < ρ / 2 := by
    have := min_le_right s (ρ / 4)
    linarith only [this, hρ]
  -- the one-step propagation
  obtain ⟨K, hK0, hK⟩ := exists_bound_of_bound_on_ball (C := C) hC.1 hC.2
    (a := (chartAt ℂ z) y) (R := ρ / 2) (s := min s (ρ / 4)) (M := B) hhalf hs' hs'ρ hB0
  -- geometry: the `ρ/2`-ball around `y` sits in the `ρ`-ball around `z`
  have hsubρ : Metric.ball ((chartAt ℂ z) y) (ρ / 2) ⊆ Metric.ball ((chartAt ℂ z) z) ρ := by
    intro w hw
    have h1 : dist w ((chartAt ℂ z) z)
        ≤ dist w ((chartAt ℂ z) y) + dist ((chartAt ℂ z) y) ((chartAt ℂ z) z) :=
      dist_triangle w ((chartAt ℂ z) y) ((chartAt ℂ z) z)
    have h2 : dist w ((chartAt ℂ z) y) < ρ / 2 := Metric.mem_ball.mp hw
    have h3 : dist ((chartAt ℂ z) y) ((chartAt ℂ z) z) < ρ / 8 := Metric.mem_ball.mp hyClose
    have h4 : ρ / 2 + ρ / 8 ≤ ρ := by linarith only [hρ]
    rw [Metric.mem_ball]
    linarith only [h1, h2, h3, h4]
  have hcyTgtR : Metric.ball ((chartAt ℂ z) y) (ρ / 2) ⊆ (chartAt ℂ z).target :=
    fun w hw => htgt (hsubρ hw)
  have hcySubR : (chartAt ℂ z).symm '' Metric.ball ((chartAt ℂ z) y) (ρ / 2) ⊆
      U ∩ (chartAt ℂ z).source := by
    rintro w ⟨u, hu, rfl⟩
    exact ⟨hUsub ⟨u, hsubρ hu, rfl⟩, (chartAt ℂ z).map_target (hcyTgtR hu)⟩
  refine ⟨(chartAt ℂ z).symm '' Metric.ball ((chartAt ℂ z) z) (ρ / 8),
    (chartAt ℂ z).isOpen_image_symm_of_subset_target Metric.isOpen_ball
      (fun w hw => htgt (Metric.ball_subset_ball hερ.le hw)),
    (fun w hw => by
      obtain ⟨u, hu, rfl⟩ := hw
      exact hUsub ⟨u, Metric.ball_subset_ball hερ.le hu, rfl⟩),
    ⟨(chartAt ℂ z) z, Metric.mem_ball_self hε, (chartAt ℂ z).left_inv (mem_chart_source ℂ z)⟩,
    B * K, mul_nonneg hB0 hK0, ?_⟩
  rintro Ω hΩo hΩc hUΩ ψ hψ hinj h0 hder x ⟨w, hw, rfl⟩
  have han := analyticAt_comp_chartAt_symm (X := X) (Ω := Ω) (U := U) (ψ := ψ) (z := z)
    (a := (chartAt ℂ z) y) (ρ := ρ / 2) hψ hUΩ hcySubR hcyTgtR
  have hinj' := injOn_comp_chartAt_symm (X := X) (Ω := Ω) (U := U) (ψ := ψ) (z := z)
    (a := (chartAt ℂ z) y) (ρ := ρ / 2) hinj hUΩ hcySubR hcyTgtR
  have hderiv := deriv_comp_chartAt_symm_ne_zero (ψ := ψ) (z := z) (y := y)
    (ρ := ρ / 2) hhalf han hinj'
  have hMb : ∀ u ∈ Metric.ball ((chartAt ℂ z) y) (min s (ρ / 4)), ‖(ψ ∘ (chartAt ℂ z).symm) u‖ ≤ B := by
    intro u hu
    exact hB hΩo hΩc hUΩ ψ hψ hinj h0 hder ((chartAt ℂ z).symm u)
      (hsV (Metric.ball_subset_ball hs's hu))
  have hwR : w ∈ Metric.ball ((chartAt ℂ z) y) (ρ / 2 / 2) := by
    have h1 : dist w ((chartAt ℂ z) y)
        ≤ dist w ((chartAt ℂ z) z) + dist ((chartAt ℂ z) z) ((chartAt ℂ z) y) :=
      dist_triangle w ((chartAt ℂ z) z) ((chartAt ℂ z) y)
    have h2 : dist w ((chartAt ℂ z) z) < ρ / 8 := Metric.mem_ball.mp hw
    have h3 : dist ((chartAt ℂ z) z) ((chartAt ℂ z) y) < ρ / 8 := by
      rw [dist_comm]; exact Metric.mem_ball.mp hyClose
    have h4 : ρ / 8 + ρ / 8 = ρ / 2 / 2 := by ring
    rw [Metric.mem_ball]
    linarith only [h1, h2, h3, h4]
  exact hK (f := fun u => ψ ((chartAt ℂ z).symm u)) han hinj' hderiv hMb w hwR


/-- **Local boundedness of normalised univalent families.**  Every member of the family of
injective holomorphic maps `ψ : X → ℂ` which are holomorphic and injective on an open connected
domain `Ω ⊇ U` and normalised by `ψ x₀ = 0`, `deriv (ψ ∘ chart) (chart x₀) = 1` is bounded on the
compact set `K ⊆ U` by one constant independent of `ψ` and `Ω`. -/
theorem norm_le_of_univalent_normalized {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {x₀ : X} {U : Set X} (hUo : IsOpen U) (hUc : IsConnected U) (hx₀ : x₀ ∈ U)
    (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ B : ℝ, ∀ ⦃Ω : Set X⦄, IsOpen Ω → IsConnected Ω → U ⊆ Ω →
      ∀ (ψ : X → ℂ), (∀ x ∈ Ω, Submission.HolomorphicOnXAt ψ x) → Set.InjOn ψ Ω → ψ x₀ = 0 →
      deriv (ψ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1 →
      ∀ x ∈ K, ‖ψ x‖ ≤ B := by
  obtain ⟨C, hC, hgrowth⟩ := Submission.exists_growth_bound_normalized_injective
  have hG : HasGrowthBound C := ⟨hC, hgrowth⟩
  have hseed : x₀ ∈ goodSet x₀ U := mem_goodSet_self (X := X) (x₀ := x₀) hUo hx₀ hG
  have hclosed : U ∩ closure (goodSet x₀ U) ⊆ goodSet x₀ U :=
    fun z hz => mem_goodSet_of_mem_closure (X := X) (x₀ := x₀) hUo hG hz.1 hz.2
  -- `goodSet x₀ U` is clopen in `U`, hence all of `U`
  have hsub : U ⊆ goodSet x₀ U := by
    have hcover : U ⊆ goodSet x₀ U ∪ (closure (goodSet x₀ U))ᶜ := by
      intro z hz
      by_cases h : z ∈ closure (goodSet x₀ U)
      · exact Or.inl (hclosed ⟨hz, h⟩)
      · exact Or.inr h
    have hdisj : Disjoint (goodSet x₀ U) (closure (goodSet x₀ U))ᶜ :=
      Set.disjoint_left.mpr fun x hx hx' => hx' (subset_closure hx)
    rcases hUc.2.subset_or_subset (isOpen_goodSet x₀ U) isClosed_closure.isOpen_compl hdisj
      hcover with h | h
    · exact h
    · exact absurd (h hx₀) fun hx => hx (subset_closure hseed)
  have hKsub : K ⊆ goodSet x₀ U := fun x hx => hsub (hKU hx)
  -- a finite subcover of `K` by open sets on which the family is uniformly bounded
  have hcover : K ⊆ ⋃ i : {V : Set X // IsOpen V ∧ V ⊆ U ∧ IsUnifBddOn x₀ U V}, (i.1 : Set X) := by
    intro x hx
    obtain ⟨V, hVo, hVU, hxV, hbdd⟩ := hKsub hx
    exact Set.mem_iUnion.mpr ⟨⟨V, hVo, hVU, hbdd⟩, hxV⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun i : {V : Set X // IsOpen V ∧ V ⊆ U ∧ IsUnifBddOn x₀ U V} => (i.1 : Set X))
    (fun i => i.2.1) hcover
  refine ⟨∑ i ∈ t, |Classical.choose i.2.2.2| + 1, ?_⟩
  intro Ω hΩo hΩc hUΩ ψ hψ hinj h0 hder x hx
  obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
  have h1 : ‖ψ x‖ ≤ Classical.choose i.2.2.2 :=
    (Classical.choose_spec i.2.2.2).2 hΩo hΩc hUΩ ψ hψ hinj h0 hder x hxi
  have h2 : Classical.choose i.2.2.2 ≤ ∑ j ∈ t, |Classical.choose j.2.2.2| + 1 := by
    have h3 : Classical.choose i.2.2.2 ≤ |Classical.choose i.2.2.2| := le_abs_self _
    have h4 : |Classical.choose i.2.2.2| ≤ ∑ j ∈ t, |Classical.choose j.2.2.2| :=
      Finset.single_le_sum (f := fun j => |Classical.choose j.2.2.2|) (fun j _ => abs_nonneg _) hit
    linarith only [h3, h4]
  linarith only [h1, h2]

end

end Work.SimplyConnected.Parabolic
