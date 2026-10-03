import Mathlib
import Submission.Lib.Unif2.Work.Modulus.Defs

/-!
# The punctured Riemann surface `X ∖ {z₀}` is connected

For a connected Riemann surface `X` (a connected complex one-manifold) and a point `z₀ : X`, the
punctured surface `X ∖ {z₀}` is connected.  This is a purely topological fact: removing a point from
a connected `2`-dimensional manifold leaves a connected space, because a point has a neighbourhood
whose punctured version is connected (a punctured disc).

The proof splits into three parts, each of independent interest:

* `Work.Modulus.isPreconnected_ball_diff_center`: a punctured disc in `ℂ` is preconnected (it is the
  image of `ℂ ∖ {0}` under the homeomorphism `ℂ ≃ₜ ball c ρ`);
* `Work.Modulus.isPreconnected_compl_singleton_of_isOpen_nhds`: the purely topological glue — if `X`
  is connected and `V ∋ p` is open with `V ∖ {p}` preconnected, then `X ∖ {p}` is preconnected;
* `Work.Modulus.exists_isOpen_nhds_isPreconnected_diff_singleton`: a chart at `z₀` provides such a
  `V` (the inverse image of a small disc).

Together they give `Work.Modulus.puncturedConnected`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff
open Set Metric

noncomputable section

namespace Work.Modulus

/-- **A punctured disc in `ℂ` is preconnected.**  For `ρ > 0`, the ball `ball c ρ` with its centre
removed is preconnected.  The proof transports preconnectedness from `ℂ ∖ {0}` along the
homeomorphism `OpenPartialHomeomorph.univBall c ρ : ℂ → ball c ρ`, which sends `0` to `c`. -/
theorem isPreconnected_ball_diff_center {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    IsPreconnected (Metric.ball c ρ \ {c}) := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have h0 : IsPreconnected ({0}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank hrank 0).isPreconnected
  have hinj : Function.Injective (OpenPartialHomeomorph.univBall (c : ℂ) ρ) :=
    fun x y h => (OpenPartialHomeomorph.univBall (c : ℂ) ρ).injOn
      (by simp [OpenPartialHomeomorph.univBall_source])
      (by simp [OpenPartialHomeomorph.univBall_source]) h
  have himg : OpenPartialHomeomorph.univBall (c : ℂ) ρ '' ({0}ᶜ : Set ℂ)
      = Metric.ball c ρ \ {c} := by
    rw [Set.compl_eq_univ_sdiff, Set.image_sdiff hinj,
      ← OpenPartialHomeomorph.univBall_source (c : ℂ) ρ,
      OpenPartialHomeomorph.image_source_eq_target,
      OpenPartialHomeomorph.univBall_target (c : ℂ) hρ,
      Set.image_singleton, OpenPartialHomeomorph.univBall_apply_zero]
  rw [← himg]
  exact h0.image _ ((OpenPartialHomeomorph.continuous_univBall (c : ℂ) ρ).continuousOn.mono
    (Set.subset_univ _))

/-- **Auxiliary topological step.**  Let `X` be a preconnected space, `p : X`, and `V ∋ p` an open
set.  Suppose `{p}ᶜ` is covered by two open sets `u`, `v` whose intersection misses `{p}ᶜ`, and
suppose `u` meets `{p}ᶜ`.  Then `u` meets the *punctured* neighbourhood `V ∖ {p}`.

This is the point where preconnectedness of `X` is used: if `V ∩ u ⊆ {p}`, then either `{p}` is
clopen (when `p ∈ u`) or `u` and `V ∪ v` are two disjoint nonempty open sets covering `X`. -/
theorem isPreconnected_compl_singleton_aux {X : Type*} [TopologicalSpace X] [T1Space X]
    [PreconnectedSpace X] {p : X} {V u v : Set X} (hV : IsOpen V) (hpV : p ∈ V)
    (hu : IsOpen u) (hv : IsOpen v) (huv : {p}ᶜ ⊆ u ∪ v)
    (hd : u ∩ v ∩ {p}ᶜ = ∅) (hune : (u ∩ {p}ᶜ).Nonempty) :
    ((V \ {p}) ∩ u).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hVu : V ∩ u ⊆ {p} := by
    intro x hx
    by_contra hx'
    exact (Set.eq_empty_iff_forall_notMem.mp h) x ⟨⟨hx.1, hx'⟩, hx.2⟩
  by_cases hpu : p ∈ u
  · have hEq : V ∩ u = {p} := by
      refine Subset.antisymm hVu fun x hx => ?_
      rw [mem_singleton_iff] at hx
      rw [hx]
      exact ⟨hpV, hpu⟩
    have hopen : IsOpen ({p} : Set X) := hEq ▸ hV.inter hu
    have hne : ({p}ᶜ : Set X).Nonempty := hune.mono inter_subset_right
    have hsub : (univ : Set X) ⊆ {p} ∪ {p}ᶜ := by
      intro x _
      by_cases hxp : x = p
      · exact Or.inl hxp
      · exact Or.inr (by simpa using hxp)
    have hpre := isPreconnected_univ ({p} : Set X) ({p}ᶜ) hopen isOpen_compl_singleton hsub
      ⟨p, trivial, mem_singleton p⟩ (hne.mono fun y hy => ⟨trivial, hy⟩)
    obtain ⟨x, hx⟩ := hpre
    obtain ⟨-, hx'⟩ := hx
    exact hx'.2 hx'.1
  · have hVue : V ∩ u = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hx1 := hVu hx
      rw [mem_singleton_iff] at hx1
      exact hpu (hx1 ▸ hx.2)
    have hdisj : u ∩ (V ∪ v) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      rcases hx with ⟨hxu, hxV | hxv⟩
      · exact (Set.eq_empty_iff_forall_notMem.mp hVue) x ⟨hxV, hxu⟩
      · have hxuvc : x ∈ ({p}ᶜ : Set X) := by
          rw [mem_compl_iff, mem_singleton_iff]
          intro hxp; exact hpu (hxp ▸ hxu)
        have hmem : x ∈ u ∩ v ∩ {p}ᶜ := ⟨⟨hxu, hxv⟩, hxuvc⟩
        rw [hd] at hmem
        exact hmem
    have hcover : u ∪ (V ∪ v) = univ := by
      rw [eq_univ_iff_forall]
      intro x
      rcases eq_or_ne x p with rfl | hx
      · exact Or.inr (Or.inl hpV)
      · have hxc : x ∈ ({p}ᶜ : Set X) := by simpa using hx
        rcases huv hxc with hxu | hxv
        · exact Or.inl hxu
        · exact Or.inr (Or.inr hxv)
    have hne1 : (univ ∩ u).Nonempty := hune.mono fun x hx => ⟨trivial, hx.1⟩
    have hne2 : (univ ∩ (V ∪ v)).Nonempty := ⟨p, trivial, Or.inl hpV⟩
    have hsub2 : (univ : Set X) ⊆ u ∪ (V ∪ v) := by
      intro x _
      rw [hcover]
      trivial
    have hpre := isPreconnected_univ u (V ∪ v) hu (hV.union hv) hsub2 hne1 hne2
    obtain ⟨x, hx⟩ := hpre
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) x hx.2

/-- **Removing a point from a connected space with a connected punctured neighbourhood.**  If `X` is
a connected `T₁` space, `p : X`, and `V ∋ p` is an open neighbourhood with `V ∖ {p}` preconnected,
then `X ∖ {p}` is preconnected. -/
theorem isPreconnected_compl_singleton_of_isOpen_nhds
    {X : Type*} [TopologicalSpace X] [T1Space X] [ConnectedSpace X] {p : X} {V : Set X}
    (hVopen : IsOpen V) (hpV : p ∈ V) (hVpc : IsPreconnected (V \ {p})) :
    IsPreconnected ({p}ᶜ : Set X) := by
  intro u v hu hv huv hune hvne
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hd : u ∩ v ∩ {p}ᶜ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    exact (Set.eq_empty_iff_forall_notMem.mp hemp) x ⟨hx.2, hx.1⟩
  have hune' : (u ∩ {p}ᶜ).Nonempty := hune.mono fun x hx => ⟨hx.2, hx.1⟩
  have hvne' : (v ∩ {p}ᶜ).Nonempty := hvne.mono fun x hx => ⟨hx.2, hx.1⟩
  have h1 : ((V \ {p}) ∩ u).Nonempty :=
    isPreconnected_compl_singleton_aux hVopen hpV hu hv huv hd hune'
  have h2 : ((V \ {p}) ∩ v).Nonempty := by
    refine isPreconnected_compl_singleton_aux hVopen hpV hv hu ?_ ?_ hvne'
    · intro x hx; exact (huv hx).elim Or.inr Or.inl
    · rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact (Set.eq_empty_iff_forall_notMem.mp hd) x ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
  have h3 := hVpc u v hu hv (fun x hx => huv hx.2) h1 h2
  obtain ⟨x, hx⟩ := h3
  exact (Set.eq_empty_iff_forall_notMem.mp hemp) x ⟨hx.1.2, hx.2⟩

/-- **A chart gives a punctured neighbourhood with connected punctured part.**  For any point `z₀` of
a charted space over `ℂ` there is an open neighbourhood `V` of `z₀` such that `V ∖ {z₀}` is
preconnected (and nonempty). -/
theorem exists_isOpen_nhds_isPreconnected_diff_singleton {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] (z₀ : X) :
    ∃ V : Set X, IsOpen V ∧ z₀ ∈ V ∧ IsPreconnected (V \ {z₀}) ∧ (V \ {z₀}).Nonempty := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (chartAt ℂ z₀).open_target (chartAt ℂ z₀ z₀)
    (mem_chart_target ℂ z₀)
  have hpoint : chartAt ℂ z₀ z₀ + ((ρ/2 : ℝ) : ℂ) ∈
      Metric.ball (chartAt ℂ z₀ z₀) ρ \ {chartAt ℂ z₀ z₀} := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
        Complex.norm_of_nonneg (by positivity)]
      linarith
    · rw [mem_singleton_iff]
      intro h
      have h2 : ((ρ/2 : ℝ) : ℂ) = 0 := by
        have := congrArg (fun z : ℂ => z - chartAt ℂ z₀ z₀) h
        simpa using this
      linarith [Complex.ofReal_eq_zero.mp h2]
  have hset : (chartAt ℂ z₀).symm '' Metric.ball (chartAt ℂ z₀ z₀) ρ \ {z₀}
      = (chartAt ℂ z₀).symm '' (Metric.ball (chartAt ℂ z₀ z₀) ρ \ {chartAt ℂ z₀ z₀}) := by
    ext y
    constructor
    · rintro ⟨hy, hyne⟩
      obtain ⟨w, hw, rfl⟩ := hy
      refine ⟨w, ⟨hw, ?_⟩, rfl⟩
      intro hwc
      refine hyne ?_
      have h2 : (chartAt ℂ z₀).symm w = z₀ := by
        rw [show w = chartAt ℂ z₀ z₀ from hwc,
          (chartAt ℂ z₀).left_inv (mem_chart_source ℂ z₀)]
      simpa using h2
    · rintro ⟨w, ⟨hw, hwc⟩, rfl⟩
      refine ⟨⟨w, hw, rfl⟩, ?_⟩
      intro hzw
      have h1 : (chartAt ℂ z₀) ((chartAt ℂ z₀).symm w) = chartAt ℂ z₀ z₀ := by
        rw [show (chartAt ℂ z₀).symm w = z₀ from hzw]
      rw [(chartAt ℂ z₀).right_inv (hball hw)] at h1
      exact hwc h1
  refine ⟨(chartAt ℂ z₀).symm '' Metric.ball (chartAt ℂ z₀ z₀) ρ, ?_, ?_, ?_, ?_⟩
  · exact (chartAt ℂ z₀).isOpen_image_symm_of_subset_target Metric.isOpen_ball hball
  · exact ⟨chartAt ℂ z₀ z₀, mem_ball_self hρ,
      (chartAt ℂ z₀).left_inv (mem_chart_source ℂ z₀)⟩
  · rw [hset]
    exact (isPreconnected_ball_diff_center hρ).image _
      ((chartAt ℂ z₀).symm.continuousOn.mono fun y hy => hball hy.1)
  · rw [hset]
    exact Set.Nonempty.image _ ⟨_, hpoint⟩

/-- **The punctured Riemann surface is connected.**  For a connected complex one-manifold `X` and a
point `z₀`, the complement `X ∖ {z₀}`, regarded as the open subset `puncturedOpens z₀`, is
connected. -/
theorem puncturedConnected
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (z₀ : X) : ConnectedSpace (puncturedOpens z₀) := by
  obtain ⟨V, hVopen, hzV, hVpc, hVne⟩ :=
    exists_isOpen_nhds_isPreconnected_diff_singleton z₀
  have hpc : IsPreconnected ({z₀}ᶜ : Set X) :=
    isPreconnected_compl_singleton_of_isOpen_nhds hVopen hzV hVpc
  have hne : ({z₀}ᶜ : Set X).Nonempty := hVne.mono fun x hx => hx.2
  have hconn : IsConnected ({z₀}ᶜ : Set X) := ⟨hne, hpc⟩
  exact isConnected_iff_connectedSpace.mp hconn

end Work.Modulus
