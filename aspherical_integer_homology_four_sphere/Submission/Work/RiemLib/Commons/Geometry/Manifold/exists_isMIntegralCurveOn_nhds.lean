import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Order.CompletePartialOrder

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Manifold ContDiff Bundle Topology
open Bundle Set Metric

namespace Commons.Geometry.Manifold

/-- **Banach-space local flow for a `C¹` vector field, with joint continuity.**

For a vector field `f : E → E` on a Banach space which is continuously differentiable at `x₀`,
there are `ε > 0`, `r > 0` and a flow `α : E → ℝ → E` such that for every `x` in the closed ball
of radius `r` around `x₀`, `α x 0 = x` and `α x` is an integral curve of `f` on `[-ε, ε]`, and
such that `(x, t) ↦ α x t` is continuous on `closedBall x₀ r × [-ε, ε]`.

This is the Banach-space form of the uniform Picard--Lindelöf theorem
(`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`). -/
theorem exists_flow_contDiffAt_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) :
    ∃ (ε : ℝ) (r : ℝ), 0 < ε ∧ 0 < r ∧ ∃ α : E → ℝ → E,
      (∀ x ∈ closedBall x₀ r, α x 0 = x ∧
        ∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (α x) (f (α x t)) (Icc (-ε) ε) t) ∧
      ContinuousOn (fun p : E × ℝ => α p.1 p.2) (closedBall x₀ r ×ˢ Icc (-ε) ε) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hPL⟩ := IsPicardLindelof.of_contDiffAt_one hf
  obtain ⟨h1, h2, h3, h4⟩ := hPL 0
  have hIcc : Icc (0 - ε) (0 + ε) = Icc (-ε) ε := by
    ext t; simp [zero_sub, zero_add]
  have hPL0 : IsPicardLindelof (fun _ => f) (tmin := -ε) (tmax := ε)
      ⟨0, by simp [le_of_lt hε]⟩ x₀ a r L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      exact h1 t (hIcc ▸ ht)
    · intro x hx
      exact hIcc ▸ h2 x hx
    · intro t ht x hx
      exact h3 t (hIcc ▸ ht) x hx
    · simpa [zero_sub, zero_add, sub_zero, neg_neg, neg_sub] using h4
  obtain ⟨α, hα1, hα2⟩ :=
    IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn hPL0
  exact ⟨ε, r, hε, hr, fun x t => α ⟨x, t⟩, fun x hx => hα1 x hx, hα2⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Local flow box for a smooth vector field on a manifold.**  For a `C^∞` section `v` of the
tangent bundle and a point `x₀`, there are a uniform time `ε > 0`, an open neighbourhood `U ∋ x₀`,
and a jointly continuous flow `γ` on `U` with, for every `x ∈ U`, `γ x 0 = x` and `γ x` an integral
curve of `v` on `(-ε, ε)`.

This is the manifold form of the uniform Picard--Lindelöf theorem (the chartwise ODE
`exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀` plus the chart transition
maps), and it is the ODE input of Grove--Shiohama's step 3. -/
theorem exists_isMIntegralCurveOn_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M))) (x₀ : M) :
    ∃ (ε : ℝ) (U : Set M), 0 < ε ∧ IsOpen U ∧ x₀ ∈ U ∧
      ∃ γ : M → ℝ → M, (∀ x ∈ U, γ x 0 = x) ∧
        (∀ x ∈ U, IsMIntegralCurveOn (γ x) v (Set.Ioo (-ε) ε)) ∧
        ContinuousOn (fun p : M × ℝ => γ p.1 p.2) (U ×ˢ Set.Ioo (-ε) ε) := by
  classical
  -- the chartwise vector field
  set F : E → E := fun z => (extChartAt (I.prod (modelWithCornersSelf ℝ E))
      (⟨x₀, v x₀⟩ : TangentBundle I M)
      (⟨(extChartAt I x₀).symm z, v ((extChartAt I x₀).symm z)⟩ : TangentBundle I M)).2 with hF
  have hFdiff : ContDiffAt ℝ 1 F (extChartAt I x₀ x₀) := by
    have hv' := hv.contMDiffAt (x := x₀)
    rw [contMDiffAt_iff] at hv'
    obtain ⟨_, hv'⟩ := hv'
    exact ((hv'.contDiffAt (range_mem_nhds_isInteriorPoint
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))).snd.of_le (by norm_num))
  obtain ⟨ε, r, hε, hr, α, hα, hαcont⟩ := exists_flow_contDiffAt_one hFdiff
  -- the chart target is open, and contains the centre
  have hT_open : IsOpen (extChartAt I x₀).target := (chartAt H x₀).isOpen_extend_target
  have hx₀_int : extChartAt I x₀ x₀ ∈ interior (extChartAt I x₀).target := by
    rw [hT_open.interior_eq]
    exact (extChartAt I x₀).map_source (mem_extChartAt_source x₀)
  -- continuity of the flow at the centre
  have hnhds : (closedBall (extChartAt I x₀ x₀) r ×ˢ Icc (-ε) ε) ∈
      𝓝 (extChartAt I x₀ x₀, (0 : ℝ)) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (Metric.closedBall_mem_nhds _ hr)
      (Icc_mem_nhds (by linarith : (-ε : ℝ) < 0) (by linarith : (0 : ℝ) < ε))
  have hcontAt : ContinuousAt (fun p : E × ℝ => α p.1 p.2) (extChartAt I x₀ x₀, 0) :=
    hαcont.continuousAt hnhds
  have hα00 : α (extChartAt I x₀ x₀) 0 = extChartAt I x₀ x₀ :=
    (hα _ (mem_closedBall_self hr.le)).1
  have hEv : ∀ᶠ q in 𝓝 (extChartAt I x₀ x₀, (0 : ℝ)),
      α q.1 q.2 ∈ interior (extChartAt I x₀).target :=
    hcontAt.eventually (isOpen_interior.mem_nhds (by
      show α (extChartAt I x₀ x₀) 0 ∈ interior (extChartAt I x₀).target
      rw [hα00]; exact hx₀_int))
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.mem_nhds_iff.mp hEv
  -- final constants
  set R : ℝ := min r (ρ / 2) / 2 with hR
  set Δ : ℝ := min ε (ρ / 2) / 2 with hΔ
  have hR0 : 0 < R := by rw [hR]; exact div_pos (lt_min hr (by linarith)) (by norm_num)
  have hΔ0 : 0 < Δ := by rw [hΔ]; exact div_pos (lt_min hε (by linarith)) (by norm_num)
  have hRr : R ≤ r := by rw [hR]; linarith [min_le_left r (ρ / 2)]
  have hΔε : Δ ≤ ε := by rw [hΔ]; linarith [min_le_left ε (ρ / 2)]
  have hRρ : R < ρ := by rw [hR]; linarith [min_le_right r (ρ / 2)]
  have hΔρ : Δ < ρ := by rw [hΔ]; linarith [min_le_right ε (ρ / 2)]
  set U : Set M := (extChartAt I x₀) ⁻¹' ball (extChartAt I x₀ x₀) R ∩ (extChartAt I x₀).source
    with hU
  have hUopen : IsOpen U := by
    rw [hU, inter_comm]
    exact (continuousOn_extChartAt x₀).isOpen_inter_preimage
      (chartAt H x₀).isOpen_extend_source isOpen_ball
  have hx₀U : x₀ ∈ U := by
    rw [hU]
    exact ⟨mem_ball_self hR0, mem_extChartAt_source x₀⟩
  set γ : M → ℝ → M := fun x t => (extChartAt I x₀).symm (α (extChartAt I x₀ x) t) with hγ
  refine ⟨Δ, U, hΔ0, hUopen, hx₀U, γ, ?_, ?_, ?_⟩
  · -- initial condition
    intro x hxU
    have hxs : x ∈ (extChartAt I x₀).source := hxU.2
    have hxc : extChartAt I x₀ x ∈ closedBall (extChartAt I x₀ x₀) r := by
      have h1 : dist (extChartAt I x₀ x) (extChartAt I x₀ x₀) < R := hxU.1
      rw [mem_closedBall]
      linarith
    show (extChartAt I x₀).symm (α (extChartAt I x₀ x) 0) = x
    rw [(hα (extChartAt I x₀ x) hxc).1, PartialEquiv.left_inv _ hxs]
  · -- integral curve property
    intro x hxU t ht
    have hxc : extChartAt I x₀ x ∈ closedBall (extChartAt I x₀ x₀) r := by
      have h1 : dist (extChartAt I x₀ x) (extChartAt I x₀ x₀) < R := hxU.1
      rw [mem_closedBall]
      linarith
    have htε : t ∈ Icc (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    let y : M := (extChartAt I x₀).symm (α (extChartAt I x₀ x) t)
    have hmemT : (extChartAt I x₀ x, t) ∈ ball (extChartAt I x₀ x₀, (0 : ℝ)) ρ := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · have h1 : dist (extChartAt I x₀ x) (extChartAt I x₀ x₀) < R := hxU.1
        linarith
      · rw [Real.dist_eq, sub_zero]
        have h1 : |t| < Δ := abs_lt.mpr ht
        linarith
    have hαt_int : α (extChartAt I x₀ x) t ∈ interior (extChartAt I x₀).target := hρ' hmemT
    have hαt_tgt : α (extChartAt I x₀ x) t ∈ (extChartAt I x₀).target := interior_subset hαt_int
    have hy_src : y ∈ (extChartAt I x₀).source := by
      show (extChartAt I x₀).symm (α (extChartAt I x₀ x) t) ∈ (extChartAt I x₀).source
      exact (extChartAt I x₀).target_subset_preimage_source hαt_tgt
    have hy_src' : y ∈ (extChartAt I y).source := mem_extChartAt_source y
    have hderiv : HasDerivAt (α (extChartAt I x₀ x))
        (tangentCoordChange I y x₀ y (v y)) t := by
      have h1 : HasDerivWithinAt (α (extChartAt I x₀ x)) (F (α (extChartAt I x₀ x) t))
          (Icc (-ε) ε) t := (hα (extChartAt I x₀ x) hxc).2 t htε
      have h2 : HasDerivAt (α (extChartAt I x₀ x)) (F (α (extChartAt I x₀ x) t)) t :=
        h1.hasDerivAt (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
      have hFval : F (α (extChartAt I x₀ x) t) = tangentCoordChange I y x₀ y (v y) := by
        rw [hF]
        show (extChartAt (I.prod (modelWithCornersSelf ℝ E)) (⟨x₀, v x₀⟩ : TangentBundle I M)
          (⟨y, v y⟩ : TangentBundle I M)).2 = tangentCoordChange I y x₀ y (v y)
        rfl
      rw [hFval] at h2
      exact h2
    have hAt : HasMFDerivAt% (γ x) t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ x t))) := by
      refine ⟨?_, ?_⟩
      · show ContinuousAt (fun t' : ℝ => (extChartAt I x₀).symm (α (extChartAt I x₀ x) t')) t
        exact (continuousAt_extChartAt_symm'' hαt_tgt).comp hderiv.continuousAt
      · refine HasDerivWithinAt.hasFDerivWithinAt ?_
        simp only [mfld_simps, hasDerivWithinAt_univ]
        change HasDerivAt ((extChartAt I y ∘ (extChartAt I x₀).symm) ∘
          (α (extChartAt I x₀ x))) (v y) t
        rw [← tangentCoordChange_self (I := I) (x := y) (z := y) (v := v y) hy_src',
          ← tangentCoordChange_comp (x := x₀) ⟨⟨hy_src', hy_src⟩, hy_src'⟩]
        apply HasFDerivAt.comp_hasDerivAt _ _ hderiv
        apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
          mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
            subset_trans interior_subset (extChartAt_target_subset_range ..), isOpen_interior, hαt_int⟩
        rw [← (extChartAt I x₀).right_inv hαt_tgt]
        exact hasFDerivWithinAt_tangentCoordChange ⟨hy_src, hy_src'⟩
    exact hAt.hasMFDerivWithinAt
  · -- joint continuity
    have hTsub : ball (extChartAt I x₀ x₀) R ×ˢ Ioo (-Δ) Δ ⊆
        closedBall (extChartAt I x₀ x₀) r ×ˢ Icc (-ε) ε := by
      intro q hq
      exact ⟨ball_subset_closedBall.trans (closedBall_subset_closedBall hRr) hq.1,
        ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
    have hαT : MapsTo (fun q : E × ℝ => α q.1 q.2)
        (ball (extChartAt I x₀ x₀) R ×ˢ Ioo (-Δ) Δ) (extChartAt I x₀).target := by
      intro q hq
      apply interior_subset
      apply hρ'
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · have h1 : dist q.1 (extChartAt I x₀ x₀) < R := hq.1
        linarith
      · rw [Real.dist_eq, sub_zero]
        have h1 : |q.2| < Δ := abs_lt.mpr hq.2
        linarith
    have hK : ContinuousOn (fun q : E × ℝ => (extChartAt I x₀).symm (α q.1 q.2))
        (ball (extChartAt I x₀ x₀) R ×ˢ Ioo (-Δ) Δ) :=
      (continuousOn_extChartAt_symm x₀).comp (hαcont.mono hTsub) hαT
    have hG1 : ContinuousOn (fun p : M × ℝ => extChartAt I x₀ p.1) (U ×ˢ Ioo (-Δ) Δ) :=
      (continuousOn_extChartAt x₀).comp (continuousOn_fst : ContinuousOn (fun p : M × ℝ => p.1)
        (U ×ˢ Ioo (-Δ) Δ)) (fun p hp => hp.1.2)
    have hG2 : ContinuousOn (fun p : M × ℝ => p.2) (U ×ˢ Ioo (-Δ) Δ) :=
      (continuousOn_snd : ContinuousOn (fun p : M × ℝ => p.2) (U ×ˢ Ioo (-Δ) Δ))
    have hG := hG1.prodMk hG2
    have hGmaps : MapsTo (fun p : M × ℝ => (extChartAt I x₀ p.1, p.2)) (U ×ˢ Ioo (-Δ) Δ)
        (ball (extChartAt I x₀ x₀) R ×ˢ Ioo (-Δ) Δ) := fun p hp => ⟨hp.1.1, hp.2⟩
    exact hK.comp hG hGmaps

end Commons.Geometry.Manifold