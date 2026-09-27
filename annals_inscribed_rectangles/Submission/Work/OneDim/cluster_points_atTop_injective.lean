import Mathlib

/-!
# Injective curves in a 1-manifold have at most one cluster point at `+∞`

The main result of this file is `Work.OneDim.cluster_points_atTop_injective`: an injective
continuous curve `γ : ℝ → C` into a (Hausdorff) 1-manifold has at most one cluster point at
`+∞`.

The argument is the classical "crossings" one.  Take a chart `φ` at `x`, pick `r > 0` with
`closedBall (φ x) r ⊆ φ.target` small enough that `y` lies outside `φ.source ∩ φ ⁻¹' closedBall (φ x) r`
(the closure of the chart ball `N = φ.source ∩ φ⁻¹' ball (φ x) r`), and let `M` be an open
neighbourhood of `y` disjoint from `closure N` (a compact set can be separated from a point it does
not contain).  Since `x` and `y` are cluster points at `+∞`, the curve meets both `N` and `M` at
arbitrarily large times; choosing

`t₁ < s₁ < t₂ < s₂ < t₃ < s₃` with `γ tᵢ ∈ N`, `γ sᵢ ∈ M`

and applying connectedness of an interval, the curve must cross `∂N` in each of the three disjoint
intervals `[tᵢ, sᵢ]`, giving three distinct crossing times.  But in a 1-manifold the boundary of a
chart ball is a *sphere* in `ℝ¹`, hence has at most two points, and `γ` is injective: a
contradiction.

The key one-dimensional input is `sphere_fin_one_subset`: in `EuclideanSpace ℝ (Fin 1)` the sphere
around a point consists of at most two points.  (Smoothness is not used: only the charted-space
structure and Hausdorffness enter.)
-/

namespace Work.OneDim

open scoped Manifold
open Set Topology Filter

/-- In `ℝ¹` the distance is the absolute value of the difference of the (single) coordinates. -/
lemma dist_euclideanSpace_fin_one (x y : EuclideanSpace ℝ (Fin 1)) :
    dist x y = |x.ofLp 0 - y.ofLp 0| := by
  rw [EuclideanSpace.dist_eq]
  simp [dist_eq_norm, Real.sqrt_sq_eq_abs]

/-- **The sphere in `ℝ¹` has at most two points.**  Every point at distance `r` from `cx` is one of
`cx + r • e`, `cx - r • e`. -/
lemma sphere_fin_one_subset (cx : EuclideanSpace ℝ (Fin 1)) (r : ℝ) :
    Metric.sphere cx r ⊆ ({cx + r • EuclideanSpace.single (𝕜 := ℝ) 0 1,
      cx - r • EuclideanSpace.single (𝕜 := ℝ) 0 1} : Set (EuclideanSpace ℝ (Fin 1))) := by
  intro z hz
  rw [Metric.mem_sphere, dist_euclideanSpace_fin_one] at hz
  have h1 : z - cx = (z.ofLp 0 - cx.ofLp 0) • EuclideanSpace.single (𝕜 := ℝ) 0 1 := by
    ext i
    fin_cases i
    simp
  have hzeq : z = cx + (z.ofLp 0 - cx.ofLp 0) • EuclideanSpace.single (𝕜 := ℝ) 0 1 := by
    nth_rewrite 1 [show z = cx + (z - cx) by abel]
    rw [h1]
  have hr : 0 ≤ r := by rw [← hz]; positivity
  rcases (abs_eq hr).mp hz with h | h
  · left; rw [hzeq, h]
  · right; rw [hzeq, h, neg_smul, sub_eq_add_neg]; simp

/-- **Crossing lemma.**  A continuous curve which is inside an open set `N` at time `a` and outside
the closure of `N` at time `b ≥ a` crosses the boundary of `N` at some intermediate time. -/
lemma curve_exists_mem_boundary_of_isOpen {X : Type*} [TopologicalSpace X] {N : Set X}
    (hN : IsOpen N) {f : ℝ → X} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (ha : f a ∈ N) (hb : f b ∉ closure N) :
    ∃ u ∈ Set.Icc a b, f u ∈ closure N \ N := by
  by_contra h
  have h' : ∀ u ∈ Set.Icc a b, f u ∉ closure N \ N := fun u hu hu' => h ⟨u, hu, hu'⟩
  have hsub : f '' Set.Icc a b ⊆ N ∪ (closure N)ᶜ := by
    rintro z ⟨u, hu, rfl⟩
    by_cases hz : f u ∈ N
    · exact Or.inl hz
    · exact Or.inr fun hzcl => h' u hu ⟨hzcl, hz⟩
  have hconn : IsPreconnected (f '' Set.Icc a b) :=
    isPreconnected_Icc.image f hf.continuousOn
  have hdisj : Disjoint N (closure N)ᶜ := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact hz2 (subset_closure hz1)
  rcases IsPreconnected.subset_or_subset hN isClosed_closure.isOpen_compl hdisj hsub hconn with
    h'' | h''
  · exact hb (subset_closure (h'' ⟨b, ⟨hab, le_rfl⟩, rfl⟩))
  · exact h'' ⟨a, ⟨le_rfl, hab⟩, rfl⟩ (subset_closure ha)

/-- **Separation of a compact set from a point it does not contain**, in a Hausdorff space: there is
an open neighbourhood of the point which is disjoint from the compact set. -/
lemma exists_isOpen_disjoint_of_isCompact_notMem {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K) {y : X} (hy : y ∉ K) :
    ∃ M : Set X, IsOpen M ∧ y ∈ M ∧ Disjoint M K := by
  have h : ∀ z : K, ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ (z : X) ∈ U ∧ y ∈ V ∧ Disjoint U V :=
    fun z => t2_separation (by rintro rfl; exact hy z.2)
  choose U V hUo hVo hzU hyV hUV using h
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => U z) (fun z => hUo z)
    (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩)
  refine ⟨⋂ z ∈ t, V z, isOpen_biInter_finset (s := t) (fun z _ => hVo z),
    Set.mem_iInter₂.mpr (fun z _ => hyV z), ?_⟩
  rw [Set.disjoint_left]
  intro w hwM hwK
  obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.mp (ht hwK)
  exact (Set.disjoint_left.mp (hUV i)) hwi (Set.mem_iInter₂.mp hwM i hi)

/-- **Pigeonhole.**  An injective map cannot take three (distinct) prescribed values in a two-point
set. -/
lemma not_injective_three_into_pair {C : Type*} [TopologicalSpace C] [T2Space C]
    (f : ℝ → C) (hinj : Function.Injective f) {u1 u2 u3 : ℝ} (h12 : u1 < u2) (h23 : u2 < u3)
    {p q : C} (h1 : f u1 ∈ ({p, q} : Set C)) (h2 : f u2 ∈ ({p, q} : Set C))
    (h3 : f u3 ∈ ({p, q} : Set C)) : False := by
  classical
  have hcard : ({u1, u2, u3} : Finset ℝ).card = 3 := by
    simp [h12.ne, h23.ne, (h12.trans h23).ne]
  have himg : (Finset.image f ({u1, u2, u3} : Finset ℝ)).card = 3 := by
    rw [Finset.card_image_of_injOn hinj.injOn, hcard]
  have hsub : Finset.image f ({u1, u2, u3} : Finset ℝ) ⊆ ({p, q} : Finset C) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · simpa using h1
    · simpa using h2
    · simpa using h3
  have hle : (Finset.image f ({u1, u2, u3} : Finset ℝ)).card ≤ 2 := by
    refine (Finset.card_le_card hsub).trans ?_
    calc ({p, q} : Finset C).card ≤ ({q} : Finset C).card + 1 := Finset.card_insert_le p {q}
      _ = 2 := by simp
  omega

/-- **No oscillation for an injective curve in a 1-manifold.**  An injective continuous curve
`γ : ℝ → C` into a 1-manifold has at most one cluster point at `+∞`.  The proof is the standard
"two crossings" argument: a chart ball `N` around a point has a boundary with exactly two points,
and an injective curve can pass through each of them at most once; hence the curve enters/leaves
`N` at most twice, so if `x` is a cluster point then the curve is eventually inside a small chart
ball around `x`; two distinct cluster points give disjoint chart balls, a contradiction. -/
theorem cluster_points_atTop_injective {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) C] [T2Space C]
    (γ : ℝ → C) (hγ : Continuous γ) (hinj : Function.Injective γ) {x y : C}
    (hx : ClusterPt x (Filter.map γ Filter.atTop))
    (hy : ClusterPt y (Filter.map γ Filter.atTop)) :
    x = y := by
  classical
  by_contra hne
  -- ## Step 1: a chart at `x` and a ball around `φ x` whose closed ball misses `y`
  obtain ⟨φ, r, hxφ, hr, hrsub, hyK⟩ :
      ∃ (φ : OpenPartialHomeomorph C (EuclideanSpace ℝ (Fin 1))) (r : ℝ),
        x ∈ φ.source ∧ 0 < r ∧ Metric.closedBall (φ x) r ⊆ φ.target ∧
          y ∉ φ.source ∩ φ ⁻¹' Metric.closedBall (φ x) r := by
    refine ⟨chartAt (EuclideanSpace ℝ (Fin 1)) x, ?_⟩
    set φ₀ := chartAt (EuclideanSpace ℝ (Fin 1)) x with hφ₀
    have hxsrc : x ∈ φ₀.source := mem_chart_source _ _
    obtain ⟨ε, hε, hεsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (φ₀.open_target.mem_nhds (φ₀.map_source hxsrc))
    by_cases hyφ : y ∈ φ₀.source
    · -- shrink the radius so that `φ₀ y` lies outside the closed ball
      have hne' : φ₀ y ≠ φ₀ x := by
        intro h
        have h' : φ₀.symm (φ₀ y) = φ₀.symm (φ₀ x) := by rw [h]
        rw [φ₀.left_inv hyφ, φ₀.left_inv hxsrc] at h'
        exact hne h'.symm
      have hd : 0 < dist (φ₀ y) (φ₀ x) := dist_pos.mpr hne'
      refine ⟨min ε (dist (φ₀ y) (φ₀ x) / 2), hxsrc, lt_min hε (by linarith),
        (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hεsub, ?_⟩
      intro hmem
      have h1 : dist (φ₀ y) (φ₀ x) ≤ dist (φ₀ y) (φ₀ x) / 2 :=
        le_trans (Metric.mem_closedBall.mp hmem.2) (min_le_right _ _)
      linarith
    · exact ⟨ε, hxsrc, hε, hεsub, fun hmem => hyφ hmem.1⟩
  -- ## Step 2: the chart ball `N`, its compact closure and a separated neighbourhood `M` of `y`
  set N : Set C := φ.source ∩ φ ⁻¹' Metric.ball (φ x) r with hNdef
  set K : Set C := φ.source ∩ φ ⁻¹' Metric.closedBall (φ x) r with hKdef
  have hK_eq : K = φ.symm '' Metric.closedBall (φ x) r := by
    rw [hKdef]
    exact (φ.symm_image_eq_source_inter_preimage hrsub).symm
  have hNopen : IsOpen N := by rw [hNdef]; exact φ.isOpen_inter_preimage Metric.isOpen_ball
  have hKcompact : IsCompact K := by
    rw [hK_eq]
    exact (isCompact_closedBall _ _).image_of_continuousOn (φ.symm.continuousOn_toFun.mono hrsub)
  have hNsubK : N ⊆ K := by
    rw [hNdef, hKdef]
    exact Set.inter_subset_inter le_rfl (preimage_mono Metric.ball_subset_closedBall)
  have hclN : closure N ⊆ K := closure_minimal hNsubK hKcompact.isClosed
  obtain ⟨M, hMopen, hyM, hMdisj⟩ :=
    exists_isOpen_disjoint_of_isCompact_notMem hKcompact hyK
  have hMdisj' : Disjoint M (closure N) := hMdisj.mono_right hclN
  have hxN : x ∈ N := by rw [hNdef]; exact ⟨hxφ, Metric.mem_ball_self hr⟩
  have hNnhds : N ∈ 𝓝 x := hNopen.mem_nhds hxN
  have hMnhds : M ∈ 𝓝 y := hMopen.mem_nhds hyM
  -- ## Step 3: the curve hits both `N` and `M` at arbitrarily large times
  have hitN : ∀ T : ℝ, ∃ t > T, γ t ∈ N := by
    intro T
    have hmem : N ∩ γ '' Set.Ioi T ∈ 𝓝 x ⊓ Filter.map γ Filter.atTop :=
      Filter.inter_mem_inf hNnhds (Filter.image_mem_map (Filter.Ioi_mem_atTop T))
    obtain ⟨z, hzN, hz⟩ := hx.nonempty_of_mem hmem
    obtain ⟨t, htT, rfl⟩ := hz
    exact ⟨t, htT, hzN⟩
  have hitM : ∀ T : ℝ, ∃ t > T, γ t ∈ M := by
    intro T
    have hmem : M ∩ γ '' Set.Ioi T ∈ 𝓝 y ⊓ Filter.map γ Filter.atTop :=
      Filter.inter_mem_inf hMnhds (Filter.image_mem_map (Filter.Ioi_mem_atTop T))
    obtain ⟨z, hzM, hz⟩ := hy.nonempty_of_mem hmem
    obtain ⟨t, htT, rfl⟩ := hz
    exact ⟨t, htT, hzM⟩
  -- ## Step 4: the boundary of `N` is contained in a two-point set
  have hboundary : ∀ z : C, z ∈ closure N \ N →
      z ∈ ({φ.symm (φ x + r • EuclideanSpace.single (𝕜 := ℝ) 0 1),
        φ.symm (φ x - r • EuclideanSpace.single (𝕜 := ℝ) 0 1)} : Set C) := by
    rintro z ⟨hzcl, hzN⟩
    have hzK : z ∈ K := hclN hzcl
    rw [hKdef] at hzK
    have hzsource : z ∈ φ.source := hzK.1
    have hzcb : φ z ∈ Metric.closedBall (φ x) r := hzK.2
    have hznb : φ z ∉ Metric.ball (φ x) r := by
      intro hb
      exact hzN (by rw [hNdef]; exact ⟨hzsource, hb⟩)
    have hzsphere : φ z ∈ Metric.sphere (φ x) r := by
      rw [Metric.mem_sphere]
      exact le_antisymm (Metric.mem_closedBall.mp hzcb)
        (le_of_not_gt fun hh => hznb (Metric.mem_ball.mpr hh))
    rcases sphere_fin_one_subset (φ x) r hzsphere with h | h
    · left; rw [← φ.left_inv hzsource, h]
    · right; rw [← φ.left_inv hzsource, h]; simp
  -- ## Step 5: three disjoint crossings
  obtain ⟨t1, ht1, hγt1⟩ := hitN 0
  obtain ⟨s1, hs1, hγs1⟩ := hitM t1
  obtain ⟨t2, ht2, hγt2⟩ := hitN s1
  obtain ⟨s2, hs2, hγs2⟩ := hitM t2
  obtain ⟨t3, ht3, hγt3⟩ := hitN s2
  obtain ⟨s3, hs3, hγs3⟩ := hitM t3
  obtain ⟨u1, hu1, hbu1⟩ := curve_exists_mem_boundary_of_isOpen hNopen hγ (le_of_lt hs1) hγt1
    (Set.disjoint_left.mp hMdisj' hγs1)
  obtain ⟨u2, hu2, hbu2⟩ := curve_exists_mem_boundary_of_isOpen hNopen hγ (le_of_lt hs2) hγt2
    (Set.disjoint_left.mp hMdisj' hγs2)
  obtain ⟨u3, hu3, hbu3⟩ := curve_exists_mem_boundary_of_isOpen hNopen hγ (le_of_lt hs3) hγt3
    (Set.disjoint_left.mp hMdisj' hγs3)
  have h12 : u1 < u2 := lt_of_le_of_lt hu1.2 (lt_of_lt_of_le ht2 hu2.1)
  have h23 : u2 < u3 := lt_of_le_of_lt hu2.2 (lt_of_lt_of_le ht3 hu3.1)
  exact not_injective_three_into_pair γ hinj h12 h23 (hboundary _ hbu1) (hboundary _ hbu2)
    (hboundary _ hbu3)

end Work.OneDim
