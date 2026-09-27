import Mathlib
import Submission.Work.SimplyConnected.ABS.harnackChain

/-!
# Harnack chains over a preconnected open set

The third brick of the Harnack layer: the *existence* of Harnack chains with a uniform length over a
compact set.  For `U` open and preconnected, `x₀ ∈ U` and `K ⊆ U` compact there is a single `N`
such that every point of `K` is joined to `x₀` by a Harnack chain of at most `N` balls inside `U`;
consequently every non-negative harmonic function on `U` satisfies a *two-sided* bound
`h y ≤ 25 ^ N h x₀` and `h x₀ ≤ 25 ^ N h y` on `K`, uniformly in `h`.  This is the "Harnack gives
the uniform rate" step of the classical proof recorded in
`Work.SimplyConnected.ABS.posHarmonicDominatedOfLocalBarrier`.

## The construction

* A **Harnack link** `HarnackLink U y z` is the data of a chart ball `B` around some centre `w`,
  contained in `U` (with the closed Euclidean ball inside the chart target), which contains *both*
  `y` and `z` in its half-radius sub-ball.  The relation is symmetric *by construction*, and the
  chart-ball Harnack inequality makes `h y` and `h z` comparable with the absolute factor `25`
  (`5 · 5`) for every non-negative harmonic `h` on `U`.

* `ReachFrom U x₀ n y` is the (symmetric) "reachable in `n` links" predicate; along such a chain a
  non-negative harmonic function is comparable at the ends with the factor `25 ^ n`
  (`reach_comparable`).

* Every point `y ∈ U` has an open neighbourhood all of whose points are linked to `y`
  (`exists_harnackLink_nhds`, the "one more step" lemma).  Hence the set `A` of points reachable
  from `x₀` is open, and it is closed in `U`: a limit point `y ∈ U` of reached points has a chart
  ball containing a reached point `z` in its half-radius sub-ball, and — the point of the symmetric
  formulation — that *same* ball links `z` to `y`.  Preconnectedness of `U`
  (`IsPreconnected.subset_of_closure_inter_subset`) then gives `A = U`.

* Finally the open cover `U = ⋃ n, interior {y | y reached in ≤ n links}` is refined by compactness
  of `K` to a finite subcover, and the largest index gives `N`.
-/

open Filter Set Metric
open scoped Topology Manifold ContDiff

noncomputable section

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **A Harnack link.**  Two points `y, z` of the open set `U` are linked when some chart ball `B`
(with centre `w` and radius `r`, contained in `U`, the closed Euclidean ball lying in the chart
target) contains both of them in its half-radius sub-ball.  The relation is symmetric by
construction and the chart-ball Harnack inequality compares the values of a non-negative harmonic
function at the two ends (`HarnackLink.comparable`). -/
def HarnackLink (U : Set X) (y z : X) : Prop :=
  ∃ (w : X) (r : ℝ), 0 < r ∧
    Metric.closedBall ((chartAt ℂ w) w) r ⊆ (chartAt ℂ w).target ∧
    Submission.chartBall (chartAt ℂ w) ((chartAt ℂ w) w) r ⊆ U ∧
    y ∈ Submission.chartBall (chartAt ℂ w) ((chartAt ℂ w) w) (r / 2) ∧
    z ∈ Submission.chartBall (chartAt ℂ w) ((chartAt ℂ w) w) (r / 2)

/-- The chart balls of radius `ρ` are contained in those of radius `ρ' ≥ ρ`. -/
theorem chartBall_mono_radius {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    Submission.chartBall c a ρ ⊆ Submission.chartBall c a ρ' :=
  fun _ hx => ⟨hx.1, Metric.ball_subset_ball h hx.2⟩

/-- A Harnack link is symmetric. -/
theorem HarnackLink.symm {U : Set X} {y z : X} (h : HarnackLink U y z) : HarnackLink U z y := by
  obtain ⟨w, r, hr, htgt, hsub, hy, hz⟩ := h
  exact ⟨w, r, hr, htgt, hsub, hz, hy⟩

theorem HarnackLink.mem_left {U : Set X} {y z : X} (h : HarnackLink U y z) : y ∈ U := by
  obtain ⟨w, r, hr, -, hsub, hy, -⟩ := h
  exact hsub (chartBall_mono_radius (by linarith : r / 2 ≤ r) hy)

theorem HarnackLink.mem_right {U : Set X} {y z : X} (h : HarnackLink U y z) : z ∈ U :=
  h.symm.mem_left

/-- **Comparability along a Harnack link**: a non-negative harmonic function on `U` takes comparable
values at the two ends, with the absolute factor `25 = 5 · 5` (twice the chart-ball Harnack
inequality applied at the common centre). -/
theorem HarnackLink.comparable {U : Set X} {h : X → ℝ} (hh : Submission.HarmonicOnX h U)
    (hpos : ∀ x ∈ U, 0 ≤ h x) {y z : X} (hL : HarnackLink U y z) :
    h y ≤ 25 * h z ∧ h z ≤ 25 * h y := by
  obtain ⟨w, r, hr, htgt, hsub, hy, hz⟩ := hL
  have hL' : HarnackLink U y z := ⟨w, r, hr, htgt, hsub, hy, hz⟩
  obtain ⟨h1, h2⟩ := harnack_comparable_on_shrunk_ball hh hpos hr htgt hsub y hy
  obtain ⟨h3, h4⟩ := harnack_comparable_on_shrunk_ball hh hpos hr htgt hsub z hz
  have hyU : 0 ≤ h y := hpos y hL'.mem_left
  have hzU : 0 ≤ h z := hpos z hL'.mem_right
  constructor
  · calc h y ≤ 5 * h w := h1
      _ ≤ 5 * (5 * h z) := mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ = 25 * h z := by ring
  · calc h z ≤ 5 * h w := h3
      _ ≤ 5 * (5 * h y) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 25 * h y := by ring

/-- **Reachability by a Harnack chain.**  `ReachFrom U x n y` says that `y` is reached from `x` in
`n` Harnack links inside `U`. -/
inductive ReachFrom (U : Set X) (x : X) : ℕ → X → Prop
  | refl : ReachFrom U x 0 x
  | step {n : ℕ} {y : X} (hxy : ReachFrom U x n y) {z : X} (hL : HarnackLink U y z) :
      ReachFrom U x (n + 1) z

/-- Every point reached by a chain inside `U` lies in `U` (provided the start point does). -/
theorem ReachFrom.mem {U : Set X} {x : X} (hx : x ∈ U) :
    ∀ {n : ℕ} {y : X}, ReachFrom U x n y → y ∈ U := by
  intro n y h
  induction h with
  | refl => exact hx
  | step hxy hL ih => exact hL.mem_right



/-- **Comparability along a Harnack chain.**  A non-negative harmonic function on `U` is comparable
at the two ends of a chain of `n` links, with the factor `25 ^ n`. -/
theorem reach_comparable {U : Set X} {h : X → ℝ} (hh : Submission.HarmonicOnX h U)
    (hpos : ∀ x ∈ U, 0 ≤ h x) {x : X} :
    ∀ (n : ℕ) (y : X), ReachFrom U x n y → h y ≤ 25 ^ n * h x ∧ h x ≤ 25 ^ n * h y := by
  intro n
  induction n with
  | zero =>
      intro y hy
      cases hy with
      | refl => simp
  | succ k ih =>
      intro y hy
      cases hy with
      | step hxy hL =>
          obtain ⟨ih1, ih2⟩ := ih _ hxy
          obtain ⟨hL1, hL2⟩ := HarnackLink.comparable hh hpos hL
          refine ⟨?_, ?_⟩
          · exact le_trans hL2 (le_trans (mul_le_mul_of_nonneg_left ih1 (by norm_num))
              (le_of_eq (by rw [pow_succ]; ring)))
          · exact le_trans ih2 (le_trans (mul_le_mul_of_nonneg_left hL1 (by norm_num))
              (le_of_eq (by rw [pow_succ]; ring)))

/-- A closed chart ball around `x` contained in a neighbourhood of `x`. -/
private theorem exists_chartClosedBall_subset_of_nhds {U : Set X} {x : X} (hU : U ∈ nhds x) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Submission.chartClosedBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ ⊆ U := by
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hxmap : (chartAt ℂ x) x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hxsrc
  have hU' : U ∈ nhds ((chartAt ℂ x).symm ((chartAt ℂ x) x)) := by
    rwa [(chartAt ℂ x).left_inv hxsrc]
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (((chartAt ℂ x).continuousAt_symm hxmap).preimage_mem_nhds hU')
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro y hy
  rw [Submission.mem_chartClosedBall] at hy
  have hy' : (chartAt ℂ x) y ∈ Metric.ball ((chartAt ℂ x) x) ε := by
    rw [Metric.mem_ball]
    have h1 : dist ((chartAt ℂ x) y) ((chartAt ℂ x) x) ≤ ε / 2 := hy.2
    linarith
  have h2 : (chartAt ℂ x).symm ((chartAt ℂ x) y) ∈ U := hεsub hy'
  rwa [(chartAt ℂ x).left_inv hy.1] at h2

/-- **The "one more step" lemma.**  Every point `y` of an open set `U` has an open neighbourhood
all of whose points are linked to `y` by a Harnack link inside `U`. -/
theorem exists_harnackLink_nhds {U : Set X} (hUo : IsOpen U) {y : X} (hy : y ∈ U) :
    ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ W ⊆ U ∧ ∀ z ∈ W, HarnackLink U y z := by
  obtain ⟨r₁, hr₁, hr₁tgt⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ y).open_target.mem_nhds ((chartAt ℂ y).map_source (mem_chart_source ℂ y)))
  obtain ⟨r₂, hr₂, hr₂sub⟩ := exists_chartClosedBall_subset_of_nhds (hUo.mem_nhds hy)
  set r : ℝ := min r₁ r₂ / 2 with hrdef
  have hrpos : 0 < r := half_pos (lt_min hr₁ hr₂)
  have hrlt : r < r₁ := by
    rw [hrdef]; have := min_le_left r₁ r₂; linarith
  have hrle : r ≤ r₂ := by
    rw [hrdef]; have := min_le_right r₁ r₂; linarith
  have htgt : Metric.closedBall ((chartAt ℂ y) y) r ⊆ (chartAt ℂ y).target :=
    (Metric.closedBall_subset_ball hrlt).trans hr₁tgt
  have hsub : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) r ⊆ U := fun z hz =>
    hr₂sub (Submission.chartBall_subset_chartClosedBall _ _ _ (chartBall_mono_radius hrle hz))
  have hyW : y ∈ Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) (r / 2) := by
    rw [Submission.mem_chartBall]
    exact ⟨mem_chart_source ℂ y, by rw [Metric.mem_ball, dist_self]; linarith⟩
  refine ⟨Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) (r / 2),
    Submission.chartBall_isOpen _ _ _, hyW,
    (chartBall_mono_radius (by linarith : r / 2 ≤ r)).trans hsub, ?_⟩
  intro z hz
  exact ⟨y, r, hrpos, htgt, hsub, hyW, hz⟩

/-- **Every point of a preconnected open set is reachable from any base point** by a Harnack chain
inside the set. -/
theorem reachable_of_preconnected {U : Set X} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    {x₀ : X} (hx₀ : x₀ ∈ U) {y : X} (hy : y ∈ U) :
    ∃ n : ℕ, ReachFrom U x₀ n y := by
  set A : Set X := {y : X | ∃ n : ℕ, ReachFrom U x₀ n y} with hAdef
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hyA
    obtain ⟨n, hn⟩ := hyA
    obtain ⟨W, hWo, hyW, -, hlink⟩ := exists_harnackLink_nhds hUo (ReachFrom.mem hx₀ hn)
    exact Filter.mem_of_superset (hWo.mem_nhds hyW)
      (fun z hz => ⟨n + 1, ReachFrom.step hn (hlink z hz)⟩)
  have hAnonempty : (U ∩ A).Nonempty := ⟨x₀, hx₀, 0, ReachFrom.refl⟩
  have hcl : closure A ∩ U ⊆ A := by
    rintro y ⟨hycl, hyU⟩
    obtain ⟨W, hWo, hyW, -, hlink⟩ := exists_harnackLink_nhds hUo hyU
    obtain ⟨z, hzW, hzA⟩ := (mem_closure_iff.mp hycl) W hWo hyW
    obtain ⟨m, hm⟩ := hzA
    exact ⟨m + 1, ReachFrom.step hm (hlink z hzW).symm⟩
  exact hUpc.subset_of_closure_inter_subset hAopen hAnonempty hcl hy

/-- **Harnack chains of bounded length over a compact set.**  For `U` open and preconnected,
`x₀ ∈ U` and `K ⊆ U` compact, there is `N` such that every `y ∈ K` is reached from `x₀` by a chain
of at most `N` links inside `U`. -/
theorem exists_harnack_chain_of_preconnected {U : Set X} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    {x₀ : X} (hx₀ : x₀ ∈ U) {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ N : ℕ, ∀ y ∈ K, ∃ m ≤ N, ReachFrom U x₀ m y := by
  set A : ℕ → Set X := fun n => {y : X | ∃ m : ℕ, m ≤ n ∧ ReachFrom U x₀ m y} with hAdef
  have hmemA : ∀ (n : ℕ) (y : X), ReachFrom U x₀ n y → y ∈ interior (A (n + 1)) := by
    intro n
    induction n with
    | zero =>
        intro y hy
        cases hy with
        | refl =>
            obtain ⟨W, hWo, hxW, -, hlink⟩ := exists_harnackLink_nhds hUo hx₀
            refine mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hWo.mem_nhds hxW) ?_)
            intro z hz
            exact ⟨1, by omega, ReachFrom.step ReachFrom.refl (hlink z hz)⟩
    | succ k ih =>
        intro y hy
        cases hy with
        | step hxy hL =>
            obtain ⟨w, r, hr, htgt, hsub, hyw, hzw⟩ := hL
            have hchain : ReachFrom U x₀ (k + 1) y :=
              ReachFrom.step hxy ⟨w, r, hr, htgt, hsub, hyw, hzw⟩
            refine mem_interior_iff_mem_nhds.mpr ?_
            refine Filter.mem_of_superset
              ((Submission.chartBall_isOpen (chartAt ℂ w) ((chartAt ℂ w) w) (r / 2)).mem_nhds hzw)
              ?_
            intro z hz
            exact ⟨_, le_rfl, ReachFrom.step hchain ⟨w, r, hr, htgt, hsub, hzw, hz⟩⟩
  have hcover : K ⊆ ⋃ n : ℕ, interior (A n) := by
    intro y hyK
    obtain ⟨m, hm⟩ := reachable_of_preconnected hUo hUpc hx₀ (hKU hyK)
    exact mem_iUnion.mpr ⟨m + 1, hmemA m y hm⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun n : ℕ => interior (A n))
    (fun n => isOpen_interior) hcover
  refine ⟨t.sup id, fun y hyK => ?_⟩
  obtain ⟨n, hnt, hyn⟩ := mem_iUnion₂.mp (ht hyK)
  have hynA : y ∈ A n := interior_subset hyn
  obtain ⟨m, hmn, hm⟩ := hynA
  exact ⟨m, le_trans hmn (Finset.le_sup (f := id) hnt), hm⟩

/-- **The uniform Harnack bound on a compact subset of a preconnected open set.**  Non-negative
harmonic functions on `U` are comparable at `x₀` and at every point of `K` with one constant,
independent of the function. -/
theorem harnack_uniform_bound_of_preconnected {U : Set X} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    {x₀ : X} (hx₀ : x₀ ∈ U) {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ N : ℕ, ∀ y ∈ K, ∀ h : X → ℝ, Submission.HarmonicOnX h U → (∀ x ∈ U, 0 ≤ h x) →
      h y ≤ 25 ^ N * h x₀ ∧ h x₀ ≤ 25 ^ N * h y := by
  obtain ⟨N, hN⟩ := exists_harnack_chain_of_preconnected hUo hUpc hx₀ hK hKU
  refine ⟨N, fun y hyK h hh hpos => ?_⟩
  obtain ⟨m, hmN, hm⟩ := hN y hyK
  obtain ⟨h1, h2⟩ := reach_comparable hh hpos m y hm
  have hpow : (25 : ℝ) ^ m ≤ 25 ^ N := pow_le_pow_right₀ (by norm_num) hmN
  have hxy : 0 ≤ h x₀ := hpos x₀ hx₀
  have hyy : 0 ≤ h y := hpos y (hKU hyK)
  exact ⟨le_trans h1 (mul_le_mul_of_nonneg_right hpow hxy),
    le_trans h2 (mul_le_mul_of_nonneg_right hpow hyy)⟩

end Work.SimplyConnected.ABS
