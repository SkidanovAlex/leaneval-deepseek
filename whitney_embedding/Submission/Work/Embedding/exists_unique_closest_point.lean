import Mathlib
import Submission.Work.Projection.mfderiv_chartAt_decomp
import Submission.Work.Embedding.uniform_lower_bound_fderiv
import Submission.Work.Embedding.uniform_bound_fderiv
import Submission.Work.Embedding.uniform_bound_fderiv_fderiv
import Submission.Work.Embedding.strictConvexOn_norm_sub_of_bounds

/-!
# Positive reach of a compact smooth submanifold of `ℝ^N`

The main result of this file, `Work.Embedding.exists_unique_closest_point`, is the statement that a
compact smooth submanifold of `ℝ^N` (given as the image of an injective smooth immersion of a
compact manifold) has *positive reach*: every point sufficiently close to the image has a unique
closest point in the image.

The proof is the classical one.  At a point `p` of `M`, in the chart at `p` the map `e` is
represented by `chartRepN e p = e ∘ (chartAt p).symm`, a `C²` map whose derivative is injective on a
neighbourhood of the chart image of `p`.  Hence, on a small ball around the chart image of `p`,
`D(chartRepN e p)` is bounded below by a constant `κ > 0` and `D²(chartRepN e p)` is bounded above
by a constant `C`; it follows (`strictConvexOn_norm_sub_of_bounds`) that for `w` close to `e p` the
function `u ↦ ‖w - chartRepN e p u‖ ^ 2` is *strictly convex* on the ball (its second derivative
along every line is positive, since the linear term `‖Dψ d‖²` dominates the curvature term).  Strict
convexity gives uniqueness of the minimum on the ball for `w` close to `e p`.

The local statement is then upgraded to a global one: if uniqueness failed for every `ε`, we would
get a sequence `y_k` with two distinct closest points `x_k ≠ z_k`, and by compactness (after passing
to a subsequence) both converge to a common limit `p` (they must have the same image under `e`,
because `dist (e x_k) (e z_k) ≤ 2 · infDist`).  For large `k` both points lie in the local chart
ball around `p` and are minima of the local distance function, contradicting the local strict
convexity.

The remaining `ε > 0` is the threshold in the statement; the existence of a closest point for each
small `y` is a compactness argument (a continuous function on a compact space attains its minimum).
-/

namespace Work.Embedding

open scoped Manifold ContDiff
open Topology Metric Filter

variable {n N : ℕ}

/-- The chart representation of `e` at `p`, `u ↦ e ((chartAt p).symm u)`.  It is only "meaningful"
on the target of the chart, and junk outside, but this is irrelevant since all the arguments below
take place inside the target. -/
noncomputable def chartRepN {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M → EuclideanSpace ℝ (Fin N)) (p : M) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N) :=
  fun u => e ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm u)

/-- On the chart source, the chart representation recovers `e`. -/
lemma chartRepN_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M → EuclideanSpace ℝ (Fin N)) (p : M) (x : M)
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    chartRepN e p ((chartAt (EuclideanSpace ℝ (Fin n)) p) x) = e x :=
  congrArg e ((chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv hx)

/-- The chart representation of a smooth map is smooth on the target of the chart. -/
lemma contMDiffOn_chartRepN {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e) (p : M) :
    ContMDiffOn (𝓡 n) (𝓡 N) ∞ (chartRepN e p)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
  have h1 : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := p)
  exact ContMDiffOn.comp (t := Set.univ) he.contMDiffOn h1 fun u _ => trivial

/-- The chart representation of a smooth map is `C^∞` at each point of the target of the chart. -/
lemma contDiffAt_chartRepN {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e) (p : M)
    {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) :
    ContDiffAt ℝ ∞ (chartRepN e p) u :=
  (contMDiffOn_chartRepN e he p).contDiffOn.contDiffAt
    ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_target.mem_nhds hu)

/-- The chart representation of a smooth immersion has injective Fréchet derivative at every point
of the chart target.  (This is the version of `Work.Embedding.injective_fderiv_chartRep` at
smoothness level `∞`, which is what the main theorem assumes.) -/
lemma injective_fderiv_chartRep_infty {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e)
    (himm : ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 N) e x))
    (p : M) {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) :
    Function.Injective (fderiv ℝ (chartRepN e p) u) := by
  obtain ⟨hxsrc, hxmap⟩ := (chartAt (EuclideanSpace ℝ (Fin n)) p).map_target hu,
    (chartAt (EuclideanSpace ℝ (Fin n)) p).right_inv hu
  have hdec := Work.Projection.mfderiv_chartAt_decomp e he p
    ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm u) hxsrc
  rw [hxmap] at hdec
  have hsurj : Function.Surjective
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p)
        ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm u)) :=
    (mdifferentiable_chart (I := 𝓡 n) p).mfderiv_surjective hxsrc
  intro a b hab
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  refine congrArg (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm u)) (himm _ ?_)
  rw [hdec]
  exact hab

/-- **Local data at a point.**  For every `p : M` there are a radius `ρ` whose closed ball around
the chart image of `p` lies in the chart target, positive numbers `δ, κ, C, L` with
`δ + L ρ < κ²/C`, such that the chart representation of `e` at `p` is `L`-Lipschitz on the ball
`ball (chart p) ρ`, and such that for every `w` with `‖w - e p‖ < δ` the function
`u ↦ ‖w - chartRepN e p u‖ ^ 2` is strictly convex on that ball. -/
theorem local_data {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e)
    (himm : ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 N) e x)) (p : M) :
    ∃ ρ δ κ C L : ℝ, 0 < ρ ∧ 0 < δ ∧ 0 < κ ∧ 0 < C ∧ 0 < L ∧
      δ + L * ρ < κ ^ 2 / C ∧
      closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ ⊆
        (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧
      (∀ u ∈ ball ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ,
        ∀ v ∈ ball ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ,
          ‖chartRepN e p u - chartRepN e p v‖ ≤ L * ‖u - v‖) ∧
      (∀ w : EuclideanSpace ℝ (Fin N), ‖w - e p‖ < δ →
        StrictConvexOn ℝ (ball ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ)
          (fun u => ‖w - chartRepN e p u‖ ^ 2)) := by
  obtain ⟨ρ₀, hρ₀pos, hρ₀sub⟩ : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ₀ ⊆
        (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_target.mem_nhds
        ((chartAt (EuclideanSpace ℝ (Fin n)) p).map_source (mem_chart_source _ p)))
    exact ⟨r / 2, by linarith, (closedBall_subset_ball (by linarith)).trans hsub⟩
  have hcd : ∀ u ∈ closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ₀,
      ContDiffAt ℝ 2 (chartRepN e p) u := by
    intro u hu
    exact (contDiffAt_chartRepN e he p (hρ₀sub hu)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hcd1 : ∀ u ∈ closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ₀,
      ContDiffAt ℝ 1 (chartRepN e p) u := fun u hu => (hcd u hu).of_le (by norm_num)
  have hinj : ∀ u ∈ closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ₀,
      Function.Injective (fderiv ℝ (chartRepN e p) u) := fun u hu =>
    injective_fderiv_chartRep_infty e he himm p (hρ₀sub hu)
  obtain ⟨κ, hκpos, hκbd⟩ := uniform_lower_bound_fderiv (isCompact_closedBall _ ρ₀)
    ⟨_, mem_closedBall_self hρ₀pos.le⟩ hcd1 hinj
  obtain ⟨L, hLpos, hLbd⟩ := uniform_bound_fderiv (isCompact_closedBall _ ρ₀) hcd1
  obtain ⟨C, hCpos, hCbd⟩ := uniform_bound_fderiv_fderiv (isCompact_closedBall _ ρ₀) hcd
  have hLip_closed : ∀ u ∈ closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ₀,
      ∀ v ∈ closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ₀,
        ‖chartRepN e p u - chartRepN e p v‖ ≤ L * ‖u - v‖ := by
    intro u hu v hv
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (x := u) (y := v)
      (fun x hx => (hcd x hx).differentiableAt (by norm_num)) hLbd
      (convex_closedBall _ _) hu hv
    rw [norm_sub_rev (chartRepN e p u) (chartRepN e p v), norm_sub_rev u v]
    exact h
  have hρpos : 0 < min (ρ₀ / 2) (κ ^ 2 / C / (2 * L)) :=
    lt_min (by linarith) (by positivity)
  have hsub : closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) p) p)
      (min (ρ₀ / 2) (κ ^ 2 / C / (2 * L))) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    (closedBall_subset_closedBall (le_trans (min_le_left _ _) (by linarith))).trans hρ₀sub
  have hballmem : ∀ u ∈ ball ((chartAt (EuclideanSpace ℝ (Fin n)) p) p)
      (min (ρ₀ / 2) (κ ^ 2 / C / (2 * L))),
      u ∈ closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ₀ := fun u hu =>
    closedBall_subset_closedBall (le_trans (min_le_left _ _) (by linarith))
      (ball_subset_closedBall hu)
  have hLipschitz : ∀ u ∈ ball ((chartAt (EuclideanSpace ℝ (Fin n)) p) p)
      (min (ρ₀ / 2) (κ ^ 2 / C / (2 * L))),
      ∀ v ∈ ball ((chartAt (EuclideanSpace ℝ (Fin n)) p) p)
        (min (ρ₀ / 2) (κ ^ 2 / C / (2 * L))),
        ‖chartRepN e p u - chartRepN e p v‖ ≤ L * ‖u - v‖ :=
    fun u hu v hv => hLip_closed u (hballmem u hu) v (hballmem v hv)
  have heps' : κ ^ 2 / C / 4 + L * min (ρ₀ / 2) (κ ^ 2 / C / (2 * L)) < κ ^ 2 / C := by
    have h1 : L * min (ρ₀ / 2) (κ ^ 2 / C / (2 * L)) ≤ L * (κ ^ 2 / C / (2 * L)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hLpos.le
    have h2 : L * (κ ^ 2 / C / (2 * L)) = κ ^ 2 / C / 2 := by
      field_simp
    have h3 : 0 < κ ^ 2 / C := by positivity
    linarith
  refine ⟨min (ρ₀ / 2) (κ ^ 2 / C / (2 * L)), κ ^ 2 / C / 4, κ, C, L,
    hρpos, by positivity, hκpos, hCpos, hLpos, heps', hsub, hLipschitz, ?_⟩
  intro w hw
  have hw' : ‖w - chartRepN e p ((chartAt (EuclideanSpace ℝ (Fin n)) p) p)‖ < κ ^ 2 / C / 4 := by
    rwa [chartRepN_chart e p p (mem_chart_source (EuclideanSpace ℝ (Fin n)) p)]
  exact strictConvexOn_norm_sub_of_bounds hρpos hκpos hCpos hLpos heps'
    (fun u hu => hcd u (hballmem u hu))
    (fun u hu d => hκbd u (hballmem u hu) d)
    (fun u hu d₁ d₂ => hCbd u (hballmem u hu) d₁ d₂)
    (fun u hu v hv => hLipschitz u hu v hv) w hw'


/-- **Local uniqueness of the closest point.**  Let the squared distance function to the chart
representation of `e` at `p` be strictly convex on `ball (chart p) ρ` for every `w` with
`‖w - e p‖ < δ`.  Then two closest points of `w` in the image whose chart coordinates lie in that
ball coincide. -/
lemma eq_of_both_minimal {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M → EuclideanSpace ℝ (Fin N)) {p : M} {ρ δ : ℝ}
    (hsc : ∀ w : EuclideanSpace ℝ (Fin N), ‖w - e p‖ < δ →
      StrictConvexOn ℝ (ball ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ)
        (fun u => ‖w - chartRepN e p u‖ ^ 2))
    {w : EuclideanSpace ℝ (Fin N)} (hw : ‖w - e p‖ < δ)
    {x₁ x₂ : M} (hx₁ : x₁ ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hx₂ : x₂ ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hmem₁ : (chartAt (EuclideanSpace ℝ (Fin n)) p) x₁ ∈
      ball ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ)
    (hmem₂ : (chartAt (EuclideanSpace ℝ (Fin n)) p) x₂ ∈
      ball ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ)
    (hm₁ : ∀ z : M, dist w (e x₁) ≤ dist w (e z))
    (hm₂ : ∀ z : M, dist w (e x₂) ≤ dist w (e z)) : x₁ = x₂ := by
  have hmin₁ : ∀ u ∈ ball ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ,
      ‖w - chartRepN e p ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₁)‖ ^ 2 ≤
        ‖w - chartRepN e p u‖ ^ 2 := by
    intro u _
    have h := hm₁ ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm u)
    rw [dist_eq_norm, dist_eq_norm] at h
    rw [chartRepN_chart e p x₁ hx₁]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  by_contra hne
  have hval : ‖w - chartRepN e p ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₁)‖ ^ 2 =
      ‖w - chartRepN e p ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₂)‖ ^ 2 := by
    rw [chartRepN_chart e p x₁ hx₁, chartRepN_chart e p x₂ hx₂, ← dist_eq_norm,
      ← dist_eq_norm]
    exact congrArg (· ^ 2) (le_antisymm (hm₁ x₂) (hm₂ x₁))
  have hmid : (1 / 2 : ℝ) • ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₁) +
      (1 / 2 : ℝ) • ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₂) ∈
      ball ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) ρ :=
    (hsc w hw).1 hmem₁ hmem₂ (by norm_num) (by norm_num) (by norm_num)
  have hne' : ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₁) ≠
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₂) := by
    intro h
    apply hne
    have h2 : (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₁) =
        (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
          ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₂) := by rw [h]
    rwa [(chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv hx₁,
      (chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv hx₂] at h2
  obtain ⟨-, hstrictf⟩ := hsc w hw
  have hstrict : ‖w - chartRepN e p ((1 / 2 : ℝ) • ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₁) +
        (1 / 2 : ℝ) • ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₂))‖ ^ 2 <
      (1 / 2 : ℝ) • ‖w - chartRepN e p ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₁)‖ ^ 2 +
        (1 / 2 : ℝ) • ‖w - chartRepN e p ((chartAt (EuclideanSpace ℝ (Fin n)) p) x₂)‖ ^ 2 :=
    hstrictf hmem₁ hmem₂ hne' (by norm_num) (by norm_num) (by norm_num)
  have hge := hmin₁ _ hmid
  rw [hval] at hstrict hge
  simp only [smul_eq_mul] at hstrict
  linarith

/-- **Positive reach.**  A compact smooth submanifold of `ℝ^N` has positive reach: every point
sufficiently close to the image of `e` has a unique closest point in the image. -/
theorem exists_unique_closest_point {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [Nonempty M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e)
    (hinj : Function.Injective e)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 N) e x)) :
    ∃ ε > 0, ∀ y : EuclideanSpace ℝ (Fin N),
      infDist y (Set.range e) < ε →
        ∃! x : M, dist y (e x) = infDist y (Set.range e) := by
  haveI : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  have hmain : ∃ ε > 0, ∀ y : EuclideanSpace ℝ (Fin N), infDist y (Set.range e) < ε →
      ∀ x z : M, dist y (e x) = infDist y (Set.range e) →
        dist y (e z) = infDist y (Set.range e) → x = z := by
    by_contra hcon
    have hcon1 : ∀ ε : ℝ, 0 < ε → ¬ (∀ y : EuclideanSpace ℝ (Fin N),
        infDist y (Set.range e) < ε → ∀ x z : M,
          dist y (e x) = infDist y (Set.range e) →
            dist y (e z) = infDist y (Set.range e) → x = z) :=
      fun ε hε hP => hcon ⟨ε, hε, hP⟩
    have hkey : ∀ k : ℕ, ∃ q : EuclideanSpace ℝ (Fin N) × M × M,
        infDist q.1 (Set.range e) < 1 / (k + 1) ∧
        dist q.1 (e q.2.1) = infDist q.1 (Set.range e) ∧
        dist q.1 (e q.2.2) = infDist q.1 (Set.range e) ∧ q.2.1 ≠ q.2.2 := by
      intro k
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have h := hcon1 (1 / ((k : ℝ) + 1)) hpos
      push Not at h
      obtain ⟨y, hy, x, z, hx, hz, hxz⟩ := h
      exact ⟨(y, x, z), by simpa using hy, hx, hz, hxz⟩
    choose g hg using hkey
    have hr_le : ∀ k : ℕ, infDist (g k).1 (Set.range e) ≤ 1 / (k + 1 : ℝ) :=
      fun k => (hg k).1.le
    have hr_tend : Tendsto (fun k : ℕ => infDist (g k).1 (Set.range e)) atTop (𝓝 0) :=
      squeeze_zero (fun k => Metric.infDist_nonneg) hr_le
        tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨p, -, φ, hφ_mono, hφ_tend⟩ :=
      isCompact_univ.tendsto_subseq (x := fun k => ((g k).2.1, (g k).2.2)) fun k => trivial
    obtain ⟨p₁, p₂⟩ := p
    have hxt : Tendsto (fun k => (g (φ k)).2.1) atTop (𝓝 p₁) :=
      (continuous_fst.tendsto (p₁, p₂)).comp hφ_tend
    have hzt : Tendsto (fun k => (g (φ k)).2.2) atTop (𝓝 p₂) :=
      (continuous_snd.tendsto (p₁, p₂)).comp hφ_tend
    have hp_eq : p₁ = p₂ := by
      have h1 : Tendsto (fun k => dist (e ((g (φ k)).2.1)) (e ((g (φ k)).2.2))) atTop
          (𝓝 (dist (e p₁) (e p₂))) :=
        ((he.continuous.tendsto p₁).comp hxt).dist ((he.continuous.tendsto p₂).comp hzt)
      have h2 : Tendsto (fun k => dist (e ((g (φ k)).2.1)) (e ((g (φ k)).2.2))) atTop
          (𝓝 0) := by
        refine squeeze_zero (g := fun k => 2 * infDist (g (φ k)).1 (Set.range e))
          (fun k => dist_nonneg) (fun k => ?_) ?_
        · calc dist (e ((g (φ k)).2.1)) (e ((g (φ k)).2.2))
              ≤ dist (e ((g (φ k)).2.1)) ((g (φ k)).1) +
                dist ((g (φ k)).1) (e ((g (φ k)).2.2)) := dist_triangle _ _ _
            _ = 2 * infDist (g (φ k)).1 (Set.range e) := by
              rw [dist_comm (e ((g (φ k)).2.1)) ((g (φ k)).1), (hg (φ k)).2.1,
                (hg (φ k)).2.2.1]
              ring
        · have hh := hr_tend.comp hφ_mono.tendsto_atTop
          simpa using hh.const_mul 2
      exact hinj (eq_of_dist_eq_zero (tendsto_nhds_unique h1 h2))
    have hzt' : Tendsto (fun k => (g (φ k)).2.2) atTop (𝓝 p₁) := by
      rw [hp_eq]; exact hzt
    obtain ⟨ρ, δ, κ, C, L, hρ, hδ, hκ, hC, hL, hδρ, hball_sub, hLip, hsc⟩ :=
      local_data e he himm p₁
    have hρ'pos : 0 < min (ρ / 2) (δ / (2 * L)) := lt_min (by linarith) (by positivity)
    have hρ'le : min (ρ / 2) (δ / (2 * L)) ≤ ρ :=
      le_trans (min_le_left _ _) (by linarith)
    have hρ'le' : L * min (ρ / 2) (δ / (2 * L)) ≤ δ / 2 := by
      calc L * min (ρ / 2) (δ / (2 * L)) ≤ L * (δ / (2 * L)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hL.le
        _ = δ / 2 := by field_simp
    have hchart_cont : ContinuousAt (chartAt (EuclideanSpace ℝ (Fin n)) p₁) p₁ :=
      (chartAt (EuclideanSpace ℝ (Fin n)) p₁).continuousOn_toFun.continuousAt
        ((chartAt (EuclideanSpace ℝ (Fin n)) p₁).open_source.mem_nhds
          (mem_chart_source _ p₁))
    have hevA : ∀ᶠ k in atTop,
        (g (φ k)).2.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p₁).source ∧
        (chartAt (EuclideanSpace ℝ (Fin n)) p₁) ((g (φ k)).2.1) ∈
          ball ((chartAt (EuclideanSpace ℝ (Fin n)) p₁) p₁) (min (ρ / 2) (δ / (2 * L))) := by
      have h1 : ∀ᶠ k in atTop,
          (g (φ k)).2.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p₁).source :=
        hxt.eventually ((chartAt (EuclideanSpace ℝ (Fin n)) p₁).open_source.mem_nhds
          (mem_chart_source _ p₁))
      have h2 : ∀ᶠ k in atTop,
          (chartAt (EuclideanSpace ℝ (Fin n)) p₁) ((g (φ k)).2.1) ∈
            ball ((chartAt (EuclideanSpace ℝ (Fin n)) p₁) p₁)
              (min (ρ / 2) (δ / (2 * L))) :=
        (hchart_cont.tendsto.comp hxt).eventually
          (isOpen_ball.mem_nhds (mem_ball_self hρ'pos))
      exact h1.and h2
    have hevB : ∀ᶠ k in atTop,
        (g (φ k)).2.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p₁).source ∧
        (chartAt (EuclideanSpace ℝ (Fin n)) p₁) ((g (φ k)).2.2) ∈
          ball ((chartAt (EuclideanSpace ℝ (Fin n)) p₁) p₁) (min (ρ / 2) (δ / (2 * L))) := by
      have h1 : ∀ᶠ k in atTop,
          (g (φ k)).2.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p₁).source :=
        hzt'.eventually ((chartAt (EuclideanSpace ℝ (Fin n)) p₁).open_source.mem_nhds
          (mem_chart_source _ p₁))
      have h2 : ∀ᶠ k in atTop,
          (chartAt (EuclideanSpace ℝ (Fin n)) p₁) ((g (φ k)).2.2) ∈
            ball ((chartAt (EuclideanSpace ℝ (Fin n)) p₁) p₁)
              (min (ρ / 2) (δ / (2 * L))) :=
        (hchart_cont.tendsto.comp hzt').eventually
          (isOpen_ball.mem_nhds (mem_ball_self hρ'pos))
      exact h1.and h2
    have hevC : ∀ᶠ k in atTop, infDist (g (φ k)).1 (Set.range e) < δ / 2 :=
      (hr_tend.comp hφ_mono.tendsto_atTop).eventually_lt_const (by linarith)
    obtain ⟨k, ⟨hkA, hkB⟩, hkC⟩ := ((hevA.and hevB).and hevC).exists
    have hw : ‖(g (φ k)).1 - e p₁‖ < δ := by
      have htp : dist ((g (φ k)).1) (e p₁) ≤ infDist ((g (φ k)).1) (Set.range e) + L *
          min (ρ / 2) (δ / (2 * L)) := by
        calc dist ((g (φ k)).1) (e p₁)
            ≤ dist ((g (φ k)).1) (e ((g (φ k)).2.1)) +
              dist (e ((g (φ k)).2.1)) (e p₁) := dist_triangle _ _ _
          _ = infDist ((g (φ k)).1) (Set.range e) + dist (e ((g (φ k)).2.1)) (e p₁) := by
              rw [(hg (φ k)).2.1]
          _ ≤ infDist ((g (φ k)).1) (Set.range e) +
              L * min (ρ / 2) (δ / (2 * L)) := by
              refine add_le_add le_rfl ?_
              have hstep : dist (e ((g (φ k)).2.1)) (e p₁) ≤
                  L * min (ρ / 2) (δ / (2 * L)) := by
                rw [dist_eq_norm, ← chartRepN_chart e p₁ ((g (φ k)).2.1) hkA.1,
                  ← chartRepN_chart e p₁ p₁
                    (mem_chart_source (EuclideanSpace ℝ (Fin n)) p₁)]
                calc ‖chartRepN e p₁ ((chartAt (EuclideanSpace ℝ (Fin n)) p₁) ((g (φ k)).2.1)) -
                      chartRepN e p₁ ((chartAt (EuclideanSpace ℝ (Fin n)) p₁) p₁)‖
                    ≤ L * ‖(chartAt (EuclideanSpace ℝ (Fin n)) p₁) ((g (φ k)).2.1) -
                        (chartAt (EuclideanSpace ℝ (Fin n)) p₁) p₁‖ :=
                      hLip _ (ball_subset_ball hρ'le hkA.2) _ (mem_ball_self hρ)
                  _ ≤ L * min (ρ / 2) (δ / (2 * L)) := by
                      apply mul_le_mul_of_nonneg_left _ hL.le
                      rw [← dist_eq_norm]
                      exact (mem_ball.mp hkA.2).le
              exact hstep
      rw [← dist_eq_norm]
      linarith [hkC, hρ'le']
    have hm₁ : ∀ z : M, dist ((g (φ k)).1) (e ((g (φ k)).2.1)) ≤
        dist ((g (φ k)).1) (e z) := by
      intro z
      rw [(hg (φ k)).2.1]
      exact Metric.infDist_le_dist_of_mem (Set.mem_range_self z)
    have hm₂ : ∀ z : M, dist ((g (φ k)).1) (e ((g (φ k)).2.2)) ≤
        dist ((g (φ k)).1) (e z) := by
      intro z
      rw [(hg (φ k)).2.2.1]
      exact Metric.infDist_le_dist_of_mem (Set.mem_range_self z)
    exact (hg (φ k)).2.2.2 (eq_of_both_minimal e hsc hw hkA.1 hkB.1
      (ball_subset_ball hρ'le hkA.2) (ball_subset_ball hρ'le hkB.2) hm₁ hm₂)
  obtain ⟨ε, hεpos, hε⟩ := hmain
  refine ⟨ε, hεpos, fun y hy => ?_⟩
  have hex : ∃ x : M, dist y (e x) = infDist y (Set.range e) := by
    obtain ⟨x₀, -, hmin⟩ := isCompact_univ.exists_isMinOn ⟨Classical.arbitrary M, trivial⟩
      (continuous_const.dist he.continuous).continuousOn
    refine ⟨x₀, le_antisymm ?_ (Metric.infDist_le_dist_of_mem (Set.mem_range_self x₀))⟩
    refine (Metric.isGLB_infDist (s := Set.range e)
      ⟨e x₀, Set.mem_range_self x₀⟩).2 ?_
    rintro t ⟨z, hz, rfl⟩
    obtain ⟨w, rfl⟩ := hz
    exact hmin (a := w) trivial
  obtain ⟨x₀, hx₀⟩ := hex
  exact ⟨x₀, hx₀, fun z hz => hε y hy z x₀ hz hx₀⟩

end Work.Embedding
