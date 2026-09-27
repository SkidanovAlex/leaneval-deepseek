import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.MaxPrincipleRegion
import Submission.RiemannSurface

/-!
# The locally uniform limit of the normalized Green functions of an exhaustion is bounded above
off a compact set

This module supplies `Work.Drive.bddAbove_off_compact_of_isGreenOn_limit`, the statement that the
locally uniform limit `E` on `X \ {a}` of the normalized Green functions `G (φ k) · - G (φ k) x₁`
of an exhaustion `Ω` of the surface is bounded above off a compact set.

The proof is the classical maximum principle for the normalized Green functions.  Fix a compact
neighbourhood `K₀ = chartClosedBall` of `a` inside `Ω 0`, and a point `y₀ ∈ K₀`, `y₀ ≠ a`.  For
each `k` the function `u k := G (φ k) · - G (φ k) y₀` is harmonic on `Ω (φ k) \ {a}` and satisfies
`u k < 0` off a compact subset of `Ω (φ k)` (the relative-compactness clause of `IsGreenOn`, applied
with `ε = G (φ k) y₀ / 2`), so the maximum principle
`Work.Drive.le_of_harmonicOnX_of_le_on_frontier` bounds `u k` on `Ω (φ k) \ K₀` by
`max 0 (sup over the frontier of K₀ of u k)`.  Since `u k` and `E - E y₀` agree in the limit on the
compact frontier of `K₀`, and since the normalization at `y₀` is harmless
(`h k = u k + h k y₀`), letting `k → ∞` gives `E x ≤ max (E y₀) B` off `K₀`, where `B` bounds `E`
on the frontier of `K₀`.
-/

namespace Work.Drive

open Filter Set
open scoped Topology Manifold ContDiff

/-- `frontier (A \ B) ⊆ frontier A ∪ frontier B`. -/
theorem frontier_sdiff_subset {Y : Type*} [TopologicalSpace Y] {A B : Set Y} :
    frontier (A \ B) ⊆ frontier A ∪ frontier B := by
  rw [Set.sdiff_eq]
  intro x hx
  have h := frontier_inter_subset A Bᶜ hx
  rw [frontier_compl] at h
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2

/-- **Maximum principle on `Ω \ K`.**  Let `Ω` be open in a Riemann surface, `K ⊆ Ω` compact with
`a ∈ interior K`, and let `u` be harmonic on `Ω \ {a}` and *negative off a compact subset of `Ω`*
(this is how the Green function of an exhaustion vanishes at the ideal boundary, cf. the third
clause of `Work.SimplyConnected.ABS.IsGreenOn`).  If `u ≤ M₀` on the frontier of `K`, then
`u ≤ max 0 M₀` on `Ω \ K`.

Proof: the superlevel set `S = {z ∈ Ω | z ∉ K ∧ max 0 M₀ < u z}` is open, is contained in the
compact set of the decay hypothesis, has compact closure and does not meet `interior K`, so `u` is
continuous on `closure S` and the maximum principle with frontier limsup
(`Submission.SubharmonicOnX.le_of_frontier_limsup`) gives `u ≤ max 0 M₀` on `S`, whence `S = ∅`. -/
theorem le_of_harmonicOnX_of_le_on_frontier {X : Type*} [TopologicalSpace X] [T2Space X]
    [PreconnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω K : Set X} {a : X} (hΩ : IsOpen Ω) (hK : IsCompact K) (haK : a ∈ interior K)
    (hKΩ : K ⊆ Ω) {u : X → ℝ} (hu : Submission.HarmonicOnX u (Ω \ {a}))
    (hdecay : ∃ K' : Set X, IsCompact K' ∧ K' ⊆ Ω ∧ ∀ x ∈ Ω, x ∉ K' → u x < 0)
    {M₀ : ℝ} (hM₀ : ∀ y ∈ frontier K, u y ≤ M₀) :
    ∀ z ∈ Ω \ K, u z ≤ max 0 M₀ := by
  classical
  obtain ⟨K', hK'c, hK'Ω, hK'⟩ := hdecay
  have haKmem : a ∈ K := interior_subset haK
  set M : ℝ := max 0 M₀ with hMdef
  set S : Set X := {z : X | z ∈ Ω ∧ z ∉ K ∧ M < u z} with hSdef
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨hzΩ, hzK, hzM⟩ := hz
    have hzne : z ≠ a := fun h => hzK (h ▸ haKmem)
    have hcont : ContinuousAt u z := (hu z ⟨hzΩ, hzne⟩).continuousAt
    have h1 : ∀ᶠ w in 𝓝 z, M < u w := hcont.eventually (isOpen_Ioi.mem_nhds hzM)
    have h2 : Ω ∈ 𝓝 z := hΩ.mem_nhds hzΩ
    have h3 : Kᶜ ∈ 𝓝 z := hK.isClosed.isOpen_compl.mem_nhds hzK
    filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
    exact ⟨hw2, hw3, hw1⟩
  have hSsub : S ⊆ K' := by
    intro z hz
    by_contra hzK'
    have h1 : u z < 0 := hK' z hz.1 hzK'
    have h2 : M < u z := hz.2.2
    have h3 : 0 ≤ M := le_max_left 0 M₀
    linarith
  have hSclint : closure S ⊆ (interior K)ᶜ :=
    closure_minimal (fun z hz h => hz.2.1 (interior_subset h)) isOpen_interior.isClosed_compl
  have hScl : closure S ⊆ K' := closure_minimal hSsub hK'c.isClosed
  have hScomp : IsCompact (closure S) := hK'c.of_isClosed_subset isClosed_closure hScl
  have haS : a ∉ closure S := fun h => hSclint h haK
  have haS' : a ∉ S := fun h => h.2.1 haKmem
  by_cases hSe : S = ∅
  · intro z hz
    have hzS : z ∉ S := by rw [hSe]; simp
    exact le_of_not_gt fun h => hzS ⟨hz.1, hz.2, h⟩
  · have hfrontne : frontier S ≠ ∅ := by
      intro h
      rcases (frontier_eq_empty_iff.mp h) with h' | h'
      · exact hSe h'
      · exact haS' (h' ▸ mem_univ a)
    have hsub : Submission.SubharmonicOnX u S := by
      refine ⟨fun z hz => ?_, fun z hz => ?_⟩
      · have hzne : z ≠ a := fun h => hz.2.1 (h ▸ haKmem)
        exact ((hu z ⟨hz.1, hzne⟩).continuousAt).continuousWithinAt
      · have hzne : z ≠ a := fun h => hz.2.1 (h ▸ haKmem)
        exact (hu z ⟨hz.1, hzne⟩).subharmonic
    have hlim : ∀ ξ ∈ frontier S, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[S] ξ, u z ≤ M + ε := by
      intro ξ hξ ε hε
      have hξcl : ξ ∈ closure S := frontier_subset_closure hξ
      have hξΩ : ξ ∈ Ω := hK'Ω (hScl hξcl)
      have hξne : ξ ≠ a := fun h => haS (h ▸ hξcl)
      have hcont : ContinuousAt u ξ := (hu ξ ⟨hξΩ, hξne⟩).continuousAt
      have hξle : u ξ ≤ M := by
        by_cases hξK : ξ ∈ K
        · refine le_trans (hM₀ ξ ?_) (le_max_right 0 M₀)
          exact ⟨hK.isClosed.closure_eq.symm ▸ hξK, hSclint hξcl⟩
        · have hnotS : ξ ∉ S := by
            have h2 : ξ ∉ interior S := hξ.2
            rwa [hSopen.interior_eq] at h2
          exact le_of_not_gt fun h => hnotS ⟨hξΩ, hξK, h⟩
      have h1 : ∀ᶠ z in 𝓝 ξ, u z ≤ M + ε := by
        have hlt : u ξ < M + ε := by linarith
        exact (hcont.eventually (isOpen_Iio.mem_nhds hlt)).mono fun z hz => le_of_lt hz
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds h1
    have hne : (frontier S).Nonempty := Set.nonempty_iff_ne_empty.mpr hfrontne
    have hle := Submission.SubharmonicOnX.le_of_frontier_limsup hSopen hsub hScomp hne
      (a := M) hlim
    intro z hz
    by_contra hcon
    exact hcon (hle z ⟨hz.1, hz.2, lt_of_not_ge hcon⟩)

/-- **A closed chart ball inside a prescribed neighbourhood.**  Every neighbourhood `W` of a point
`a` of a Riemann surface contains a closed chart ball around `a` (whose Euclidean radius is chosen
small enough that the closed ball also lies in the chart target). -/
theorem exists_chartClosedBall_subset_of_mem_nhds {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [ChartedSpace ℂ Y] {W : Set Y} {a : Y} (hW : W ∈ 𝓝 a) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall ((chartAt ℂ a) a) ρ ⊆ (chartAt ℂ a).target ∧
      Submission.chartClosedBall (chartAt ℂ a) ((chartAt ℂ a) a) ρ ⊆ W := by
  set c := chartAt ℂ a with hc
  have hatgt : c a ∈ c.target := c.map_source (mem_chart_source ℂ a)
  have hsrc : c.source ∈ 𝓝 a := c.open_source.mem_nhds (mem_chart_source ℂ a)
  have hcont : ContinuousAt c.symm (c a) := c.continuousAt_symm hatgt
  have hpull : c.symm ⁻¹' (W ∩ c.source) ∈ 𝓝 (c a) := by
    refine hcont.preimage_mem_nhds ?_
    rw [c.left_inv (mem_chart_source ℂ a)]
    exact inter_mem hW hsrc
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpull
  obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds hatgt)
  have hlt₁ : min δ δ₂ / 2 < δ := by have h := min_le_left δ δ₂; linarith
  have hlt₂ : min δ δ₂ / 2 < δ₂ := by have h := min_le_right δ δ₂; linarith
  refine ⟨min δ δ₂ / 2, by positivity, ?_, ?_⟩
  · exact (Metric.closedBall_subset_ball hlt₂).trans hδ₂sub
  · intro x hx
    rw [Submission.mem_chartClosedBall] at hx
    obtain ⟨hxsrc, hxcl⟩ := hx
    have hxball : c x ∈ Metric.ball (c a) δ := Metric.closedBall_subset_ball hlt₁ hxcl
    have hmem : c.symm (c x) ∈ W ∩ c.source := hδsub hxball
    rw [c.left_inv hxsrc] at hmem
    exact hmem.1

/-- **The locally uniform limit of the normalized Green functions of an exhaustion is bounded above off a compact set.**  `Ω n` is a nested exhaustion by relatively compact open sets with `a ∈ Ω n` and `⋃ n, Ω n = univ`, `G n` is the Green function of `Ω n` with pole `a` (`IsGreenOn`), `φ` tends to infinity (e.g. is strictly monotone, as the Montel extraction provides), and `E` is the locally uniform limit on `X \ {a}` of the normalized functions `G (φ k) · - G (φ k) x₁`.  Then `E ≤ c` off some compact set, for some real `c`.

Route.  Fix a relatively compact `K₀ ∋ a`, say `K₀ := Ω 0`.  For each `k`, the normalized function `h k := G (φ k) · - G (φ k) x₁` is harmonic on `Ω (φ k) \ {a}`, and at the frontier of `Ω (φ k)` its values are `-G (φ k) x₁ ≤ 0`: the positivity of the Green function together with the relative-compactness clause of `IsGreenOn` (which says `G (φ k) < ε` off a compact subset of `Ω (φ k)`) makes `G (φ k)` tend to `0` at each frontier point of `Ω (φ k)`.  The maximum principle on `Ω (φ k) \ closure K₀` (for large `k`) therefore gives `h k ≤ max (0, sup_{∂K₀} h k)` there.  Fixing `x ∉ closure K₀`, the convergence `φ k → ∞` together with `⋃ n, Ω n = univ` gives `x ∈ Ω (φ k)` for all large `k`, so `E x ≤ max (0, sup_{∂K₀} E)`, the supremum over `∂K₀` being finite by the local uniform convergence on that compact set. -/
theorem bddAbove_off_compact_of_isGreenOn_limit {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {a x₁ : X} {Ω : ℕ → Set X} {G : ℕ → X → ℝ} {φ : ℕ → ℕ} {E : X → ℝ}
    (haΩ : ∀ n, a ∈ Ω n) (hΩo : ∀ n, IsOpen (Ω n))
    (hΩcomp : ∀ n, IsCompact (closure (Ω n)))
    (hmono : ∀ n, Ω n ⊆ Ω (n + 1))
    (hcov : (⋃ n, Ω n) = Set.univ)
    (hφ : Tendsto φ atTop atTop)
    (hG : ∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n))
    (hconv : TendstoLocallyUniformlyOn (fun k => fun x => G (φ k) x - G (φ k) x₁) E atTop
      (Set.univ \ {a})) :
    ∃ (K : Set X) (c : ℝ), IsCompact K ∧ ∀ x ∉ K, E x ≤ c := by
  classical
  -- monotonicity of the exhaustion
  have hmono_le : ∀ n m : ℕ, n ≤ m → Ω n ⊆ Ω m := by
    intro n m hnm
    induction hnm with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hmono _)
  -- a compact core `K₀ ∋ a` inside `Ω 0`
  obtain ⟨ρ, hρ, hρtgt, hρΩ⟩ :=
    exists_chartClosedBall_subset_of_mem_nhds (W := Ω 0) ((hΩo 0).mem_nhds (haΩ 0))
  set K₀ : Set X := Submission.chartClosedBall (chartAt ℂ a) ((chartAt ℂ a) a) ρ with hK₀def
  have hK₀comp : IsCompact K₀ := Submission.isCompact_chartClosedBall hρtgt
  have hK₀Ω : K₀ ⊆ Ω 0 := hρΩ
  have haK₀ : a ∈ interior K₀ := by
    have h1 : a ∈ Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) ρ :=
      ⟨mem_chart_source ℂ a, Metric.mem_ball.mpr (by rw [dist_self]; exact hρ)⟩
    exact interior_maximal (Submission.chartBall_subset_chartClosedBall _ _ _)
      (Submission.chartBall_isOpen _ _ _) h1
  -- an auxiliary point `y₀ ∈ K₀ \ {a}`
  have hpt : ((chartAt ℂ a) a + ((ρ / 2 : ℝ) : ℂ)) ∈ Metric.ball ((chartAt ℂ a) a) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have h1 : ‖(((ρ / 2 : ℝ)) : ℂ)‖ ^ 2 = (ρ / 2) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_ofReal, sq]
    nlinarith [norm_nonneg (((ρ / 2 : ℝ)) : ℂ), hρ]
  have httgt : ((chartAt ℂ a) a + ((ρ / 2 : ℝ) : ℂ)) ∈ (chartAt ℂ a).target :=
    hρtgt (Metric.ball_subset_closedBall hpt)
  set y₀ : X := (chartAt ℂ a).symm ((chartAt ℂ a) a + ((ρ / 2 : ℝ) : ℂ)) with hy₀def
  have hy₀chart : (chartAt ℂ a) y₀ = (chartAt ℂ a) a + ((ρ / 2 : ℝ) : ℂ) := by
    rw [hy₀def]; exact (chartAt ℂ a).right_inv httgt
  have hy₀ball : y₀ ∈ Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) ρ :=
    ⟨(chartAt ℂ a).map_target httgt, by
      show (chartAt ℂ a) y₀ ∈ Metric.ball ((chartAt ℂ a) a) ρ
      rw [hy₀chart]; exact hpt⟩
  have hy₀ne : y₀ ≠ a := by
    intro h
    have h2 : (chartAt ℂ a) y₀ = (chartAt ℂ a) a := by rw [h]
    have h4 : (chartAt ℂ a) a + ((ρ / 2 : ℝ) : ℂ) = (chartAt ℂ a) a := by
      rw [← hy₀chart, h2]
    have h5 : (chartAt ℂ a) a + ((ρ / 2 : ℝ) : ℂ) = (chartAt ℂ a) a + 0 := by
      rw [add_zero]; exact h4
    have h3 : (((ρ / 2 : ℝ)) : ℂ) = 0 := add_left_cancel h5
    have h6 : ρ / 2 = 0 := Complex.ofReal_eq_zero.mp h3
    linarith
  have hy₀Ω0 : y₀ ∈ Ω 0 :=
    hK₀Ω (Submission.chartBall_subset_chartClosedBall _ _ _ hy₀ball)
  have hy₀Ω : ∀ n, y₀ ∈ Ω n := fun n => hmono_le 0 n (Nat.zero_le n) hy₀Ω0
  -- the frontier of `K₀` is compact and disjoint from `a`
  have hfrontsub : frontier K₀ ⊆ Set.univ \ {a} := by
    intro y hy
    exact ⟨mem_univ y, fun h => hy.2 (h ▸ haK₀)⟩
  have hfrontcomp : IsCompact (frontier K₀) :=
    hK₀comp.of_isClosed_subset isClosed_frontier hK₀comp.isClosed.frontier_subset
  have hfrontK₀ : frontier K₀ ⊆ K₀ := hK₀comp.isClosed.frontier_subset
  -- a bound for `E` on that frontier
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ y ∈ frontier K₀, E y ≤ B := by
    have hU : TendstoUniformlyOn (fun k => fun z => G (φ k) z - G (φ k) x₁) E atTop
        (frontier K₀) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hfrontcomp).mp
        (hconv.mono hfrontsub)
    have hone : ∀ᶠ k in atTop, ∀ y ∈ frontier K₀,
        dist (E y) (G (φ k) y - G (φ k) x₁) < 1 :=
      (Metric.tendstoUniformlyOn_iff.mp hU) 1 one_pos
    rw [eventually_atTop] at hone
    obtain ⟨k₁, hk₁⟩ := hone
    have hk₁' : ∀ y ∈ frontier K₀, |E y - (G (φ k₁) y - G (φ k₁) x₁)| < 1 := by
      intro y hy
      have h := hk₁ k₁ le_rfl y hy
      rw [Real.dist_eq] at h
      exact h
    have hcontk : ContinuousOn (fun y : X => G (φ k₁) y - G (φ k₁) x₁) (frontier K₀) := by
      intro y hy
      have hyΩ : y ∈ Ω 0 := hK₀Ω (hfrontK₀ hy)
      have hyne : y ≠ a := (hfrontsub hy).2
      have hcy : ContinuousAt (fun z : X => G (φ k₁) z - G (φ k₁) x₁) y :=
        (((hG (φ k₁)).2.1 y
          ⟨hmono_le 0 (φ k₁) (Nat.zero_le _) hyΩ, hyne⟩).continuousAt).sub
          continuousAt_const
      exact hcy.continuousWithinAt
    obtain ⟨C, hC⟩ := hfrontcomp.exists_bound_of_continuousOn hcontk
    refine ⟨C + 1, fun y hy => ?_⟩
    have h1 : |E y - (G (φ k₁) y - G (φ k₁) x₁)| < 1 := hk₁' y hy
    have h2 : |G (φ k₁) y - G (φ k₁) x₁| ≤ C := by
      rw [← Real.norm_eq_abs]; exact hC y hy
    calc E y ≤ |E y| := le_abs_self _
      _ = |(E y - (G (φ k₁) y - G (φ k₁) x₁)) + (G (φ k₁) y - G (φ k₁) x₁)| := by
          rw [sub_add_cancel]
      _ ≤ |E y - (G (φ k₁) y - G (φ k₁) x₁)| + |G (φ k₁) y - G (φ k₁) x₁| :=
          abs_add_le _ _
      _ ≤ C + 1 := by linarith
  -- the main estimate
  refine ⟨K₀, max (E y₀) B, hK₀comp, ?_⟩
  intro x hxK₀
  have hxne : x ≠ a := fun h => hxK₀ (h ▸ interior_subset haK₀)
  obtain ⟨N, hxN⟩ : ∃ N : ℕ, x ∈ Ω N := by
    have hxU : x ∈ ⋃ n, Ω n := by rw [hcov]; exact mem_univ x
    simpa using hxU
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ4 : 4 * δ = ε := by rw [hδdef]; ring
  have hxφ : ∀ᶠ k in atTop, x ∈ Ω (φ k) := by
    filter_upwards [hφ.eventually (Filter.eventually_ge_atTop N)] with k hk
    exact hmono_le N (φ k) hk hxN
  have hyφ : ∀ᶠ k in atTop, y₀ ∈ Ω (φ k) := Filter.Eventually.of_forall fun k => hy₀Ω (φ k)
  have hptx : ∀ᶠ k in atTop, |G (φ k) x - G (φ k) x₁ - E x| < δ := by
    have h := hconv.tendsto_at (show x ∈ Set.univ \ {a} from ⟨mem_univ x, hxne⟩)
    have h2 := h.eventually (Metric.ball_mem_nhds (E x) hδ)
    filter_upwards [h2] with k hk
    rwa [Real.dist_eq] at hk
  have hpty : ∀ᶠ k in atTop, |G (φ k) y₀ - G (φ k) x₁ - E y₀| < δ := by
    have h := hconv.tendsto_at (show y₀ ∈ Set.univ \ {a} from ⟨mem_univ y₀, hy₀ne⟩)
    have h2 := h.eventually (Metric.ball_mem_nhds (E y₀) hδ)
    filter_upwards [h2] with k hk
    rwa [Real.dist_eq] at hk
  have hUnif : ∀ᶠ k in atTop, ∀ y ∈ frontier K₀,
      |G (φ k) y - G (φ k) x₁ - E y| < δ := by
    have hU : TendstoUniformlyOn (fun k => fun z => G (φ k) z - G (φ k) x₁) E atTop
        (frontier K₀) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hfrontcomp).mp
        (hconv.mono hfrontsub)
    have h := (Metric.tendstoUniformlyOn_iff.mp hU) δ hδ
    filter_upwards [h] with k hk y hy
    have h2 := hk y hy
    rw [Real.dist_eq] at h2
    rw [abs_sub_comm]
    exact h2
  obtain ⟨k, hkxΩ, hky₀Ω, hkxδ, hky₀δ, hkunif⟩ :=
    (hxφ.and (hyφ.and (hptx.and (hpty.and hUnif)))).exists
  -- the maximum principle for `u k = G (φ k) · - G (φ k) y₀`
  have hharm : Submission.HarmonicOnX (fun z : X => G (φ k) z - G (φ k) y₀)
      (Ω (φ k) \ {a}) :=
    ((hG (φ k)).2.1).sub (Submission.harmonicOnX_const (G (φ k) y₀))
  have hGpos : 0 < G (φ k) y₀ := (hG (φ k)).1 y₀ hky₀Ω hy₀ne
  have hdecay : ∃ K' : Set X, IsCompact K' ∧ K' ⊆ Ω (φ k) ∧
      ∀ z ∈ Ω (φ k), z ∉ K' → G (φ k) z - G (φ k) y₀ < 0 := by
    obtain ⟨K', hK'c, hK'Ω, hK'⟩ := (hG (φ k)).2.2.1 (G (φ k) y₀ / 2) (by linarith)
    exact ⟨K', hK'c, hK'Ω, fun z hzΩ hzK => by
      have := hK' z hzΩ hzK
      linarith⟩
  have hM₀ : ∀ y ∈ frontier K₀, G (φ k) y - G (φ k) y₀ ≤ B - E y₀ + 2 * δ := by
    intro y hy
    have h1 : G (φ k) y - G (φ k) x₁ - E y < δ :=
      lt_of_le_of_lt (le_abs_self _) (hkunif y hy)
    have h2 : E y ≤ B := hB y hy
    have h3 : E y₀ - δ < G (φ k) y₀ - G (φ k) x₁ := by
      have h4 := hky₀δ
      rw [abs_lt] at h4
      linarith
    have hid : G (φ k) y - G (φ k) y₀
        = (G (φ k) y - G (φ k) x₁) - (G (φ k) y₀ - G (φ k) x₁) := by ring
    rw [hid]
    linarith
  have hle₀ := le_of_harmonicOnX_of_le_on_frontier (Ω := Ω (φ k)) (K := K₀) (a := a)
    (M₀ := B - E y₀ + 2 * δ) (hΩo (φ k)) hK₀comp haK₀
    (hK₀Ω.trans (hmono_le 0 (φ k) (Nat.zero_le _))) hharm hdecay hM₀
  have hxle : G (φ k) x - G (φ k) y₀ ≤ max 0 (B - E y₀ + 2 * δ) := hle₀ x ⟨hkxΩ, hxK₀⟩
  have hxk : G (φ k) x - G (φ k) x₁ ≤ max 0 (B - E y₀ + 2 * δ) + (E y₀ + δ) := by
    have h2 : G (φ k) y₀ - G (φ k) x₁ < E y₀ + δ := by
      have h4 := hky₀δ
      rw [abs_lt] at h4
      linarith
    have hid : G (φ k) x - G (φ k) x₁
        = (G (φ k) x - G (φ k) y₀) + (G (φ k) y₀ - G (φ k) x₁) := by ring
    rw [hid]
    linarith
  have hEx : E x ≤ max 0 (B - E y₀) + E y₀ + ε := by
    have h1 : E x < G (φ k) x - G (φ k) x₁ + δ := by
      have h4 := hkxδ
      rw [abs_lt] at h4
      linarith
    have hmax : max 0 (B - E y₀ + 2 * δ) ≤ max 0 (B - E y₀) + 2 * δ := by
      have h5 : B - E y₀ + 2 * δ ≤ max 0 (B - E y₀) + 2 * δ := by
        have h6 := le_max_right (0 : ℝ) (B - E y₀)
        linarith
      exact max_le (by linarith [le_max_left (0 : ℝ) (B - E y₀)]) h5
    linarith
  have hid2 : max 0 (B - E y₀) + E y₀ = max (E y₀) B := by
    rcases le_total (E y₀) B with h | h
    · rw [max_eq_right h, max_eq_right (by linarith : (0 : ℝ) ≤ B - E y₀)]
      ring
    · rw [max_eq_left h, max_eq_left (by linarith : B - E y₀ ≤ (0 : ℝ))]
      ring
  rwa [hid2] at hEx

end Work.Drive
