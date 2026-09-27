import Mathlib
import Submission.Work.Drive.N2.modelBall

set_option linter.unusedSectionVars false

/-!
# The level-determines-the-point property of a model-adapted flow

`Work.Drive.N2.hmono_of_chartODE` is the property `hmono` consumed by
`Work.Drive.N2.exists_crossingTransportTb` (and, in its localised form, by
`Work.Drive.N2.crossingTransportDrawingAt`): *the level determines the point on an orbit* of the
model-adapted flow, i.e. `f (Φ (s, y)) = f (Φ (t, y)) → Φ (s, y) = Φ (t, y)`.

## What is proved here

* `Work.Drive.N2.isOpen_modelBall` — the model ball of a chart is open;
* `Work.Drive.N2.level_law_of_avoid`, `Work.Drive.N2.ode_of_mem` — the *restarted* forms of the
  level law and of the chart ODE (the published clauses are stated with the interval from `0`; these
  versions hold on an arbitrary interval, using the flow law `hΦcomp`);
* `Work.Drive.N2.deriv_orbit_eq_of_mem_modelBall` — inside the model ball of the chart `i` the orbit
  function `σ ↦ f (Φ (σ, y))` has the chart-ODE derivative
  `2 β i (‖u‖²) ‖u‖²`, `u = φ i (Φ (σ, y))`;
* `Work.Drive.N2.deriv_orbit_eq_one_of_eventually_notMem` — where the orbit avoids every model ball
  the same function has slope exactly `1`;
* `Work.Drive.N2.hmono_of_chartODE` — the main theorem: from
  * the two **analytic data** `hderivnn` (the orbit function has non-negative derivative everywhere)
    and `hzero` (a vanishing derivative forces the orbit into the closed core ball
    `‖φ i ·‖² ≤ r i ² / 2` of a chart),
  * the **interface** `hode0` (on a core interval the chart coordinates of the orbit have zero
    derivative),
  * continuity of the orbit function and of the chart coordinates (`hFcd`, `hct`) and the ball
    hypotheses (`hCsub`, `hCcl`, `hCball`, `hdisj`),

  the level determines the point on every orbit.

The proof of the main theorem: the orbit function is monotone (`hderivnn`), so equal endpoints force
it to be constant on `[s,t]`; its derivative then vanishes at every interior point, so (`hzero`)
every interior point of the orbit lies in a core ball; the core balls sit inside the pairwise
disjoint *open* model balls, so by connectedness of the image of `(s,t)` the orbit meets a single
core ball `i₀`; there `hode0` gives zero derivative of the chart coordinates, so those are constant
on `(s,t)`; finally continuity at the endpoints (`hct`) and injectivity of the chart give
`Φ (s, y) = Φ (t, y)`.

## What remains for the unconditional statement

The two analytic data `hderivnn`, `hzero` are *true* for the flow of
`Work.Drive.N2.exists_modelAdapted_levelFlow_chartODE`, and the argument is short; the analysis is
recorded in `Submission/Work/Drive/N2/NOTES_hmono_state.md`:

* `hderivnn`: the chart ODE gives `F' = 2 β i (‖u‖²) ‖u‖² ≥ 0` at points of a model ball and the
  level law gives slope `1` off the balls, hence (by density of the union of these two open regions
  in every neighbourhood, `F'` being continuous) `F' ≥ 0` everywhere;
* `hzero`: if the orbit is in a model ball at `τ` then the chart formula forces
  `2 β i (‖u‖²) ‖u‖² = 0`, i.e. the core; and if it is *not* in any ball then `F' ≠ 0`: either the
  level law gives slope `1`, or ball points accumulate at `τ`, in which case the chart values tend to
  `1` by the identities `2 · (r i)² · β i ((r i)²) = 1` (`chartMult_mul`) and the continuity of
  `β i = chartMult (r i)` at `(r i)²` (`chartMult_contDiff`), so `F' = 1` again.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- The model ball of a chart is open. -/
lemma isOpen_modelBall (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ) :
    IsOpen (modelBall φ r) := by
  have h : modelBall φ r = φ.source ∩ φ ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r := by
    ext y
    simp only [modelBall, mem_ofPred_eq, mem_inter_iff, mem_preimage, Metric.mem_ball,
      dist_eq_norm, sub_zero]
  rw [h]
  exact φ.isOpen_inter_preimage Metric.isOpen_ball

/-- **The level law, restarted at an arbitrary time.**  If the orbit piece `Φ (·, y)` over `[τ₁, τ₂]`
avoids all model balls, then `f` rises at unit speed over it. -/
lemma level_law_of_avoid {f : M → ℝ} {Φ : ℝ × M → M}
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    {ι : Type*} (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ι → ℝ)
    (hlevel : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i, Φ (u, y) ∉ modelBall (φ i) (r i)) →
      f (Φ (t, y)) = f y + t)
    {y : M} {τ₁ τ₂ : ℝ} (hτ : τ₁ ≤ τ₂)
    (hav : ∀ u ∈ Set.Icc τ₁ τ₂, ∀ i, Φ (u, y) ∉ modelBall (φ i) (r i)) :
    f (Φ (τ₂, y)) = f (Φ (τ₁, y)) + (τ₂ - τ₁) := by
  have h0 : min 0 (τ₂ - τ₁) = 0 := min_eq_left (by linarith)
  have h1 : max 0 (τ₂ - τ₁) = τ₂ - τ₁ := max_eq_right (by linarith)
  have hmain := hlevel (Φ (τ₁, y)) (τ₂ - τ₁) (fun u hu i => by
    rw [h0, h1] at hu
    have hu' : u + τ₁ ∈ Set.Icc τ₁ τ₂ := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [hΦcomp u τ₁ y]
    exact hav (u + τ₁) hu' i)
  have hpt : Φ (τ₂ - τ₁, Φ (τ₁, y)) = Φ (τ₂, y) := by
    rw [hΦcomp (τ₂ - τ₁) τ₁ y, show τ₂ - τ₁ + τ₁ = τ₂ by ring]
  rw [hpt] at hmain
  exact hmain

/-- **The chart ODE, restarted at an arbitrary time.** -/
lemma ode_of_mem {Φ : ℝ × M → M}
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    {ι : Type*} (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ : ι → ℝ) (β : ι → ℝ → ℝ) {C : ι → Set M}
    (hode : ∀ (i : ι) (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C i) →
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
          (β i (‖φ i (Φ (t, y))‖ ^ 2) * (s₁ i * φ i (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
          (β i (‖φ i (Φ (t, y))‖ ^ 2) * (s₂ i * φ i (Φ (t, y)) 1)) t)
    {y : M} {τ₁ τ₂ : ℝ} (hτ : τ₁ ≤ τ₂) (i : ι)
    (hav : ∀ u ∈ Set.Icc τ₁ τ₂, Φ (u, y) ∈ C i) :
    HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
        (β i (‖φ i (Φ (τ₂, y))‖ ^ 2) * (s₁ i * φ i (Φ (τ₂, y)) 0)) τ₂ ∧
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
        (β i (‖φ i (Φ (τ₂, y))‖ ^ 2) * (s₂ i * φ i (Φ (τ₂, y)) 1)) τ₂ := by
  have h0 : min 0 (τ₂ - τ₁) = 0 := min_eq_left (by linarith)
  have h1 : max 0 (τ₂ - τ₁) = τ₂ - τ₁ := max_eq_right (by linarith)
  have hmem : ∀ u ∈ Set.Icc (min 0 (τ₂ - τ₁)) (max 0 (τ₂ - τ₁)), Φ (u, Φ (τ₁, y)) ∈ C i := by
    intro u hu
    rw [h0, h1] at hu
    have hu' : u + τ₁ ∈ Set.Icc τ₁ τ₂ := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [hΦcomp u τ₁ y]
    exact hav (u + τ₁) hu'
  have hpt : Φ (τ₂ - τ₁, Φ (τ₁, y)) = Φ (τ₂, y) := by
    rw [hΦcomp (τ₂ - τ₁) τ₁ y, show τ₂ - τ₁ + τ₁ = τ₂ by ring]
  obtain ⟨h0', h1'⟩ := hode i (Φ (τ₁, y)) (τ₂ - τ₁) hmem
  rw [hpt] at h0' h1'
  have hshift0 : ∀ x : ℝ,
      (fun s : ℝ => φ i (Φ (s, Φ (τ₁, y))) 0) (-τ₁ + x) = φ i (Φ (x, y)) 0 := by
    intro x
    show φ i (Φ (-τ₁ + x, Φ (τ₁, y))) 0 = φ i (Φ (x, y)) 0
    rw [hΦcomp (-τ₁ + x) τ₁ y, show -τ₁ + x + τ₁ = x by ring]
  have hshift1 : ∀ x : ℝ,
      (fun s : ℝ => φ i (Φ (s, Φ (τ₁, y))) 1) (-τ₁ + x) = φ i (Φ (x, y)) 1 := by
    intro x
    show φ i (Φ (-τ₁ + x, Φ (τ₁, y))) 1 = φ i (Φ (x, y)) 1
    rw [hΦcomp (-τ₁ + x) τ₁ y, show -τ₁ + x + τ₁ = x by ring]
  constructor
  · have h0'' : HasDerivAt (fun s : ℝ => φ i (Φ (s, Φ (τ₁, y))) 0)
        (β i (‖φ i (Φ (τ₂, y))‖ ^ 2) * (s₁ i * φ i (Φ (τ₂, y)) 0)) (-τ₁ + τ₂) := by
      rw [show -τ₁ + τ₂ = τ₂ - τ₁ by ring]; exact h0'
    have h := HasDerivAt.comp_const_add (𝕜 := ℝ) (-τ₁) τ₂ h0''
    simpa only [hshift0] using h
  · have h1'' : HasDerivAt (fun s : ℝ => φ i (Φ (s, Φ (τ₁, y))) 1)
        (β i (‖φ i (Φ (τ₂, y))‖ ^ 2) * (s₂ i * φ i (Φ (τ₂, y)) 1)) (-τ₁ + τ₂) := by
      rw [show -τ₁ + τ₂ = τ₂ - τ₁ by ring]; exact h1'
    have h := HasDerivAt.comp_const_add (𝕜 := ℝ) (-τ₁) τ₂ h1''
    simpa only [hshift1] using h

end Work.Drive.N2

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- **The chart formula for the derivative of the orbit function.**  Inside the model ball of the
chart `i` the orbit function is `f (x i) + chartQ (φ i)` and its derivative along the orbit is
`2 β i (‖u‖²) ‖u‖²`. -/
lemma deriv_orbit_eq_of_mem_modelBall {f : M → ℝ} {Φ : ℝ × M → M} (hΦcont : Continuous Φ)
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    {ι : Type*} (x : ι → M)
    (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ r : ι → ℝ) {C : ι → Set M} (β : ι → ℝ → ℝ)
    (hCball : ∀ i, modelBall (φ i) (r i) ⊆ C i)
    (hval : ∀ (i : ι) (y : M), y ∈ (φ i).source →
      f y = f (x i) + chartQ (φ i) (s₁ i) (s₂ i) y)
    (hode : ∀ (i : ι) (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C i) →
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
          (β i (‖φ i (Φ (t, y))‖ ^ 2) * (s₁ i * φ i (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
          (β i (‖φ i (Φ (t, y))‖ ^ 2) * (s₂ i * φ i (Φ (t, y)) 1)) t)
    (hsgn : ∀ i, (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1))
    {y : M} {i : ι} {τ : ℝ} (hb : Φ (τ, y) ∈ modelBall (φ i) (r i)) :
    deriv (fun σ : ℝ => f (Φ (σ, y))) τ
      = 2 * β i (‖φ i (Φ (τ, y))‖ ^ 2)
          * ((φ i (Φ (τ, y)) 0) ^ 2 + (φ i (Φ (τ, y)) 1) ^ 2) := by
  have hγ : Continuous fun σ : ℝ => Φ (σ, y) := hΦcont.comp (continuous_id.prodMk continuous_const)
  have hnhds : (fun σ : ℝ => Φ (σ, y)) ⁻¹' (modelBall (φ i) (r i)) ∈ 𝓝 τ :=
    hγ.continuousAt.preimage_mem_nhds ((isOpen_modelBall _ _).mem_nhds hb)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hmem : ∀ u ∈ Set.Icc (τ - ε / 2) τ, Φ (u, y) ∈ C i := by
    intro u hu
    have h1 : dist u τ < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2, hε]
    exact hCball i (hεsub h1)
  obtain ⟨hd0, hd1⟩ := ode_of_mem (φ := φ) (s₁ := s₁) (s₂ := s₂) (β := β) (C := C)
      hΦcomp hode (by linarith [hε]) i hmem
  set u₀ : ℝ → ℝ := fun σ => φ i (Φ (σ, y)) 0 with hu₀
  set u₁ : ℝ → ℝ := fun σ => φ i (Φ (σ, y)) 1 with hu₁
  have hp0 : HasDerivAt (fun σ : ℝ => s₁ i * u₀ σ ^ 2)
      (s₁ i * (2 * u₀ τ ^ (2 - 1) * (β i (‖φ i (Φ (τ, y))‖ ^ 2) * (s₁ i * u₀ τ)))) τ :=
    (hd0.pow 2).const_mul (s₁ i)
  have hp1 : HasDerivAt (fun σ : ℝ => s₂ i * u₁ σ ^ 2)
      (s₂ i * (2 * u₁ τ ^ (2 - 1) * (β i (‖φ i (Φ (τ, y))‖ ^ 2) * (s₂ i * u₁ τ)))) τ :=
    (hd1.pow 2).const_mul (s₂ i)
  have hs1 : s₁ i ^ 2 = 1 := by rcases (hsgn i).1 with h | h <;> rw [h] <;> norm_num
  have hs2 : s₂ i ^ 2 = 1 := by rcases (hsgn i).2 with h | h <;> rw [h] <;> norm_num
  have hEq : s₁ i * (2 * u₀ τ ^ (2 - 1) * (β i (‖φ i (Φ (τ, y))‖ ^ 2) * (s₁ i * u₀ τ)))
      + s₂ i * (2 * u₁ τ ^ (2 - 1) * (β i (‖φ i (Φ (τ, y))‖ ^ 2) * (s₂ i * u₁ τ)))
      = 2 * β i (‖φ i (Φ (τ, y))‖ ^ 2) * (u₀ τ ^ 2 + u₁ τ ^ 2) := by
    have h21 : (2 : ℕ) - 1 = 1 := rfl
    simp only [h21, pow_one]
    have h1 : s₁ i * s₁ i = 1 := by rw [← sq, hs1]
    have h2 : s₂ i * s₂ i = 1 := by rw [← sq, hs2]
    linear_combination (2 * u₀ τ ^ 2 * β i (‖φ i (Φ (τ, y))‖ ^ 2)) * h1
      + (2 * u₁ τ ^ 2 * β i (‖φ i (Φ (τ, y))‖ ^ 2)) * h2
  have hG : HasDerivAt (fun σ : ℝ => s₁ i * u₀ σ ^ 2 + s₂ i * u₁ σ ^ 2)
      (2 * β i (‖φ i (Φ (τ, y))‖ ^ 2) * (u₀ τ ^ 2 + u₁ τ ^ 2)) τ := by
    have h := hp0.add hp1
    rw [hEq] at h
    exact h
  have hev : (fun σ : ℝ => f (Φ (σ, y))) =ᶠ[𝓝 τ]
      (fun σ : ℝ => f (x i) + (s₁ i * u₀ σ ^ 2 + s₂ i * u₁ σ ^ 2)) := by
    filter_upwards [hnhds] with σ hσ
    rw [hval i (Φ (σ, y)) hσ.1]
    rfl
  have hmain : HasDerivAt (fun σ : ℝ => f (Φ (σ, y)))
      (2 * β i (‖φ i (Φ (τ, y))‖ ^ 2) * (u₀ τ ^ 2 + u₁ τ ^ 2)) τ :=
    (hG.const_add (f (x i))).congr_of_eventuallyEq hev
  rw [hmain.deriv]

/-- **Off the model balls the orbit function has slope `1`.** -/
lemma deriv_orbit_eq_one_of_eventually_notMem {f : M → ℝ} {Φ : ℝ × M → M}
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    {ι : Type*} (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ι → ℝ)
    (hlevel : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i, Φ (u, y) ∉ modelBall (φ i) (r i)) →
      f (Φ (t, y)) = f y + t)
    {y : M} {τ : ℝ}
    (hav : ∀ᶠ σ in 𝓝 τ, ∀ i, Φ (σ, y) ∉ modelBall (φ i) (r i)) :
    deriv (fun σ : ℝ => f (Φ (σ, y))) τ = 1 := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hav
  have hoff : ∀ σ : ℝ, dist σ τ < ε → ∀ i, Φ (σ, y) ∉ modelBall (φ i) (r i) := hεsub
  have hev : (fun σ : ℝ => f (Φ (σ, y)))
      =ᶠ[𝓝 τ] (fun σ : ℝ => f (Φ (τ, y)) + (σ - τ)) := by
    filter_upwards [Metric.ball_mem_nhds τ hε] with σ hσ
    have hd : dist σ τ < ε := hσ
    have hdb : -(ε) < σ - τ ∧ σ - τ < ε := by
      rw [Real.dist_eq] at hd
      exact abs_lt.mp hd
    rcases le_total τ σ with hle | hle
    · have hsub : ∀ u ∈ Set.Icc τ σ, dist u τ < ε := by
        intro u hu
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hu.1, hu.2, hε, hdb.1, hdb.2]
      have h := level_law_of_avoid hΦcomp φ r hlevel hle (fun u hu i => hoff u (hsub u hu) i)
      exact h
    · have hsub : ∀ u ∈ Set.Icc σ τ, dist u τ < ε := by
        intro u hu
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hu.1, hu.2, hε, hdb.1, hdb.2]
      have h := level_law_of_avoid hΦcomp φ r hlevel hle (fun u hu i => hoff u (hsub u hu) i)
      linarith
  have h1 : HasDerivAt (fun σ : ℝ => f (Φ (τ, y)) + (σ - τ)) 1 τ :=
    ((hasDerivAt_id τ).sub_const τ).const_add (f (Φ (τ, y)))
  rw [(h1.congr_of_eventuallyEq hev).deriv]

end Work.Drive.N2

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- **The orbit function has non-negative derivative everywhere** (the first of the two analytic
data consumed by `hmono_of_chartODE`).  Inside a model ball the chart ODE gives the chart value
`2 β i (‖u‖²) ‖u‖² ≥ 0`; where a whole neighbourhood avoids the balls the level law gives slope `1`;
hence the set `{F' ≥ 0}`, closed because `F` is `C¹`, meets every neighbourhood of every point and is
therefore all of `ℝ`. -/
lemma orbit_deriv_nonneg {f : M → ℝ} {Φ : ℝ × M → M} (hΦcont : Continuous Φ)
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    {ι : Type*} (x : ι → M)
    (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ r : ι → ℝ) {C : ι → Set M} (β : ι → ℝ → ℝ)
    (hCball : ∀ i, modelBall (φ i) (r i) ⊆ C i) (hβnn : ∀ i σ, 0 ≤ β i σ)
    (hval : ∀ (i : ι) (y : M), y ∈ (φ i).source →
      f y = f (x i) + chartQ (φ i) (s₁ i) (s₂ i) y)
    (hlevel : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i, Φ (u, y) ∉ modelBall (φ i) (r i)) →
      f (Φ (t, y)) = f y + t)
    (hode : ∀ (i : ι) (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C i) →
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
          (β i (‖φ i (Φ (t, y))‖ ^ 2) * (s₁ i * φ i (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
          (β i (‖φ i (Φ (t, y))‖ ^ 2) * (s₂ i * φ i (Φ (t, y)) 1)) t)
    (hsgn : ∀ i, (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1))
    (y : M) (hFcd : ContDiff ℝ 1 (fun σ : ℝ => f (Φ (σ, y)))) :
    ∀ σ : ℝ, 0 ≤ deriv (fun τ : ℝ => f (Φ (τ, y))) σ := by
  intro τ
  by_contra hcon
  rw [not_le] at hcon
  have hclosed : IsClosed {σ : ℝ | 0 ≤ deriv (fun σ : ℝ => f (Φ (σ, y))) σ} :=
    isClosed_le continuous_const (hFcd.continuous_deriv (by norm_num))
  have hmem : τ ∈ closure {σ : ℝ | 0 ≤ deriv (fun σ : ℝ => f (Φ (σ, y))) σ} := by
    rw [Metric.mem_closure_iff]
    intro ρ hρ
    by_cases h1 : Φ (τ, y) ∈ ⋃ i, modelBall (φ i) (r i)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp h1
      refine ⟨τ, ?_, by simpa using hρ⟩
      change 0 ≤ deriv (fun σ : ℝ => f (Φ (σ, y))) τ
      rw [deriv_orbit_eq_of_mem_modelBall hΦcont hΦcomp x φ s₁ s₂ r β hCball hval hode hsgn hi]
      exact mul_nonneg (mul_nonneg (by norm_num) (hβnn i _)) (by positivity)
    · by_cases h2 : ∃ σ : ℝ, dist σ τ < ρ ∧ Φ (σ, y) ∈ ⋃ i, modelBall (φ i) (r i)
      · obtain ⟨σ, hσ, hσ'⟩ := h2
        obtain ⟨i, hi⟩ := mem_iUnion.mp hσ'
        refine ⟨σ, ?_, by rw [dist_comm]; exact hσ⟩
        change 0 ≤ deriv (fun σ : ℝ => f (Φ (σ, y))) σ
        rw [deriv_orbit_eq_of_mem_modelBall hΦcont hΦcomp x φ s₁ s₂ r β hCball hval hode hsgn hi]
        exact mul_nonneg (mul_nonneg (by norm_num) (hβnn i _)) (by positivity)
      · refine ⟨τ, ?_, by simpa using hρ⟩
        have hav : ∀ᶠ σ in 𝓝 τ, ∀ i, Φ (σ, y) ∉ modelBall (φ i) (r i) := by
          refine Filter.eventually_of_mem (Metric.ball_mem_nhds τ hρ) ?_
          intro σ hσ i hi
          exact h2 ⟨σ, hσ, mem_iUnion.mpr ⟨i, hi⟩⟩
        change 0 ≤ deriv (fun σ : ℝ => f (Φ (σ, y))) τ
        rw [deriv_orbit_eq_one_of_eventually_notMem hΦcomp φ r hlevel hav]
        norm_num
  exact absurd (hclosed.closure_subset hmem) (not_le.mpr hcon)

/-- **A vanishing derivative forces the orbit into a core ball** (the second analytic datum
consumed by `hmono_of_chartODE`).  Inside a model ball the chart formula forces `β i = 0`, i.e. the
core.  Off the balls the derivative is `1`: either a whole neighbourhood avoids the balls (the level
law), or model balls accumulate at `τ`, and then along the filter of times whose image lies in one
fixed ball the orbit function equals the chart expression, whose values tend to
`2 · (r k)² · β k ((r k)²) = 1`. -/
lemma orbit_deriv_zero_mem_core {f : M → ℝ} {Φ : ℝ × M → M} (hΦcont : Continuous Φ)
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    {ι : Type*} [Fintype ι] (x : ι → M)
    (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ r : ι → ℝ) (hr : ∀ i, 0 < r i) {C : ι → Set M} (β : ι → ℝ → ℝ)
    (hCsub : ∀ i, C i ⊆ (φ i).source) (hCcl : ∀ i, closure (C i) ⊆ (φ i).source)
    (hCball : ∀ i, modelBall (φ i) (r i) ⊆ C i)
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (φ i).source (φ j).source)
    (hβnn : ∀ i σ, 0 ≤ β i σ) (hβz : ∀ i σ, β i σ = 0 ↔ σ ≤ r i ^ 2 / 2)
    (hβcont : ∀ i, ContinuousAt (β i) ((r i) ^ 2))
    (hβmul : ∀ i, 2 * (r i) ^ 2 * β i ((r i) ^ 2) = 1)
    (hval : ∀ (i : ι) (y : M), y ∈ (φ i).source →
      f y = f (x i) + chartQ (φ i) (s₁ i) (s₂ i) y)
    (hlevel : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i, Φ (u, y) ∉ modelBall (φ i) (r i)) →
      f (Φ (t, y)) = f y + t)
    (hode : ∀ (i : ι) (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C i) →
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
          (β i (‖φ i (Φ (t, y))‖ ^ 2) * (s₁ i * φ i (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
          (β i (‖φ i (Φ (t, y))‖ ^ 2) * (s₂ i * φ i (Φ (t, y)) 1)) t)
    (hsgn : ∀ i, (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1))
    (y : M) (hFcd : ContDiff ℝ 1 (fun σ : ℝ => f (Φ (σ, y))))
    (hct : ∀ (i : ι) (j : Fin 2) (σ : ℝ), Φ (σ, y) ∈ (φ i).source →
      ContinuousAt (fun τ : ℝ => φ i (Φ (τ, y)) j) σ) :
    ∀ τ : ℝ, deriv (fun σ : ℝ => f (Φ (σ, y))) τ = 0 →
      ∃ i : ι, Φ (τ, y) ∈ C i ∧ (‖φ i (Φ (τ, y))‖ : ℝ) ^ 2 ≤ (r i) ^ 2 / 2 := by
  intro τ h0
  have hγ : Continuous fun σ : ℝ => Φ (σ, y) := hΦcont.comp (continuous_id.prodMk continuous_const)
  by_cases hb : Φ (τ, y) ∈ ⋃ i, modelBall (φ i) (r i)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hb
    have hd := deriv_orbit_eq_of_mem_modelBall hΦcont hΦcomp x φ s₁ s₂ r β hCball hval hode hsgn hi
    rw [hd] at h0
    refine ⟨i, hCball i hi, ?_⟩
    have hu : (φ i (Φ (τ, y)) 0) ^ 2 + (φ i (Φ (τ, y)) 1) ^ 2
        = (‖φ i (Φ (τ, y))‖ : ℝ) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      norm_num [Fin.sum_univ_two]
    have hprod : 2 * β i (‖φ i (Φ (τ, y))‖ ^ 2)
        * ((φ i (Φ (τ, y)) 0) ^ 2 + (φ i (Φ (τ, y)) 1) ^ 2) = 0 := h0
    have hkey : β i (‖φ i (Φ (τ, y))‖ ^ 2) = 0 ∨ (‖φ i (Φ (τ, y))‖ : ℝ) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hprod with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 (by norm_num)
        · exact Or.inl h2
      · exact Or.inr (by rw [← hu]; exact h1)
    rcases hkey with h1 | h1
    · exact (hβz i _).mp h1
    · rw [h1]
      positivity
  · -- off the model balls: the derivative is `1`
    have hone : deriv (fun σ : ℝ => f (Φ (σ, y))) τ = 1 := by
      by_cases hacc : τ ∈ closure ((fun σ : ℝ => Φ (σ, y)) ⁻¹' (⋃ i, modelBall (φ i) (r i)))
      · obtain ⟨k, hk⟩ : ∃ k, τ ∈ closure ((fun σ : ℝ => Φ (σ, y)) ⁻¹' modelBall (φ k) (r k)) := by
          rw [preimage_iUnion, closure_iUnion_of_finite] at hacc
          exact mem_iUnion.mp hacc
        have hτcl : Φ (τ, y) ∈ closure (modelBall (φ k) (r k)) := by
          rw [mem_closure_iff_nhds] at hk ⊢
          intro V hV
          obtain ⟨σ, hσV, hσA⟩ := hk ((fun σ : ℝ => Φ (σ, y)) ⁻¹' V)
            (hγ.continuousAt.preimage_mem_nhds hV)
          exact ⟨Φ (σ, y), hσV, hσA⟩
        have hsrcτ : Φ (τ, y) ∈ (φ k).source := hCcl k (closure_mono (hCball k) hτcl)
        have hnormτ : (‖φ k (Φ (τ, y))‖ : ℝ) = r k := by
          refine le_antisymm ?_ ?_
          · -- a cluster point of the model ball has chart image in the closed ball
            by_contra hlt
            rw [not_le] at hlt
            have hδ1 : r k < (r k + ‖φ k (Φ (τ, y))‖) / 2 := by linarith
            have hδ2 : (r k + ‖φ k (Φ (τ, y))‖) / 2 < ‖φ k (Φ (τ, y))‖ := by linarith
            have hcZ : ContinuousAt (fun z : M => (‖φ k z‖ : ℝ)) (Φ (τ, y)) :=
              continuous_norm.continuousAt.comp ((φ k).continuousAt hsrcτ)
            have hW : ((φ k).source ∩
                {z : M | (r k + ‖φ k (Φ (τ, y))‖) / 2 < ‖φ k z‖}) ∈ 𝓝 (Φ (τ, y)) :=
              Filter.inter_mem ((φ k).open_source.mem_nhds hsrcτ)
                (hcZ.preimage_mem_nhds (isOpen_Ioi.mem_nhds hδ2))
            obtain ⟨z, hzW, hzmb⟩ := mem_closure_iff_nhds.mp hτcl _ hW
            exact absurd (lt_trans hzmb.2 hδ1) (not_lt.mpr (le_of_lt hzW.2))
          · by_contra hlt
            rw [not_le] at hlt
            exact (fun hcon => hb (mem_iUnion.mpr ⟨k, hcon⟩)) ⟨hsrcτ, hlt⟩
        have hlim1 : Tendsto (fun σ : ℝ => β k (‖φ k (Φ (σ, y))‖ ^ 2))
            (𝓝[(fun σ : ℝ => Φ (σ, y)) ⁻¹' modelBall (φ k) (r k)] τ) (𝓝 (β k ((r k) ^ 2))) := by
          refine (hβcont k).tendsto.comp ?_
          have h2 : ContinuousAt (fun σ : ℝ => (‖φ k (Φ (σ, y))‖ : ℝ) ^ 2) τ :=
            (ContinuousAt.comp
              (f := fun σ : ℝ => Φ (σ, y)) (g := fun z : M => (‖φ k z‖ : ℝ))
              (continuous_norm.continuousAt.comp ((φ k).continuousAt hsrcτ))
              hγ.continuousAt).pow 2
          simpa only [hnormτ] using h2.tendsto.mono_left nhdsWithin_le_nhds
        have hlim2 : Tendsto (fun σ : ℝ => (φ k (Φ (σ, y)) 0) ^ 2 + (φ k (Φ (σ, y)) 1) ^ 2)
            (𝓝[(fun σ : ℝ => Φ (σ, y)) ⁻¹' modelBall (φ k) (r k)] τ) (𝓝 ((r k) ^ 2)) := by
          have h2 : ContinuousAt
              (fun σ : ℝ => (φ k (Φ (σ, y)) 0) ^ 2 + (φ k (Φ (σ, y)) 1) ^ 2) τ :=
            ((hct k 0 τ hsrcτ).pow 2).add ((hct k 1 τ hsrcτ).pow 2)
          have hval0 : (φ k (Φ (τ, y)) 0) ^ 2 + (φ k (Φ (τ, y)) 1) ^ 2 = (r k) ^ 2 := by
            have hnorm : (φ k (Φ (τ, y)) 0) ^ 2 + (φ k (Φ (τ, y)) 1) ^ 2
                = (‖φ k (Φ (τ, y))‖ : ℝ) ^ 2 := by
              rw [EuclideanSpace.norm_sq_eq]
              norm_num [Fin.sum_univ_two]
            rw [hnorm, hnormτ]
          have ht : Tendsto (fun σ : ℝ => (φ k (Φ (σ, y)) 0) ^ 2 + (φ k (Φ (σ, y)) 1) ^ 2)
              (𝓝[(fun σ : ℝ => Φ (σ, y)) ⁻¹' modelBall (φ k) (r k)] τ)
              (𝓝 ((φ k (Φ (τ, y)) 0) ^ 2 + (φ k (Φ (τ, y)) 1) ^ 2)) :=
            h2.tendsto.mono_left nhdsWithin_le_nhds
          simpa only [hval0] using ht
        have hlim : Tendsto (fun σ : ℝ => 2 * β k (‖φ k (Φ (σ, y))‖ ^ 2)
                * ((φ k (Φ (σ, y)) 0) ^ 2 + (φ k (Φ (σ, y)) 1) ^ 2))
            (𝓝[(fun σ : ℝ => Φ (σ, y)) ⁻¹' modelBall (φ k) (r k)] τ) (𝓝 1) := by
          have h3 := (hlim1.const_mul 2).mul hlim2
          have hval : 2 * β k ((r k) ^ 2) * (r k) ^ 2 = 1 := by
            calc 2 * β k ((r k) ^ 2) * (r k) ^ 2
                = 2 * (r k) ^ 2 * β k ((r k) ^ 2) := by ring
              _ = 1 := hβmul k
          simpa only [hval] using h3
        have hchart : (fun σ : ℝ => deriv (fun τ : ℝ => f (Φ (τ, y))) σ)
            =ᶠ[𝓝[(fun σ : ℝ => Φ (σ, y)) ⁻¹' modelBall (φ k) (r k)] τ]
            (fun σ : ℝ => 2 * β k (‖φ k (Φ (σ, y))‖ ^ 2)
                * ((φ k (Φ (σ, y)) 0) ^ 2 + (φ k (Φ (σ, y)) 1) ^ 2)) := by
          filter_upwards [self_mem_nhdsWithin] with σ hσ
          exact deriv_orbit_eq_of_mem_modelBall hΦcont hΦcomp x φ s₁ s₂ r β hCball hval hode hsgn hσ
        have hcont' : ContinuousAt (fun σ : ℝ => deriv (fun τ : ℝ => f (Φ (τ, y))) σ) τ :=
          (hFcd.continuous_deriv (by norm_num)).continuousAt
        exact tendsto_nhds_unique' (mem_closure_iff_nhdsWithin_neBot.mp hk)
          (hcont'.tendsto.mono_left nhdsWithin_le_nhds) (Tendsto.congr' hchart.symm hlim)
      · -- a neighbourhood avoids the balls
        have hnb : ∀ᶠ σ in 𝓝 τ, ∀ i, Φ (σ, y) ∉ modelBall (φ i) (r i) := by
          have hclosed :
              (closure (⋃ i, (fun σ : ℝ => Φ (σ, y)) ⁻¹' modelBall (φ i) (r i)))ᶜ ∈ 𝓝 τ := by
            refine isClosed_closure.isOpen_compl.mem_nhds ?_
            simpa only [Set.preimage_iUnion, Set.mem_compl_iff] using hacc
          exact Filter.mem_of_superset hclosed
            (fun σ hσ i hi => hσ (subset_closure (mem_iUnion.mpr ⟨i, hi⟩)))
        exact deriv_orbit_eq_one_of_eventually_notMem hΦcomp φ r hlevel hnb
    rw [hone] at h0
    exact absurd h0 (by norm_num)

/-- **`hmono` for a model-adapted flow, from the two analytic data.**

The two data are exactly what the model-adapted flow of
`Work.Drive.N2.exists_modelAdapted_levelFlow_chartODE` provides (see the module docstring for the
proof): along every orbit, `f` increases (`hderivnn`), and a vanishing rate forces the orbit into
the closed core ball `‖φ i ·‖² ≤ r i ² / 2` of a chart (`hzero`).  The final hypothesis `hode0`
says that on such a core the chart coordinates of the orbit have zero derivative (it follows from
the chart ODE and `β i = 0` on the core).  The conclusion is the property `hmono` used by
`Work.Drive.N2.exists_crossingTransportTb` and `Work.Drive.N2.crossingTransportDrawingAt`. -/
theorem hmono_of_chartODE {f : M → ℝ} {Φ : ℝ × M → M} (hΦcont : Continuous Φ)
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    {ι : Type*} [Fintype ι]
    (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (C : ι → Set M) (hCsub : ∀ i, C i ⊆ (φ i).source)
    (hCcl : ∀ i, closure (C i) ⊆ (φ i).source)
    (hCball : ∀ i, modelBall (φ i) (r i) ⊆ C i)
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (φ i).source (φ j).source)
    (hFcd : ∀ y : M, ContDiff ℝ 1 (fun σ : ℝ => f (Φ (σ, y))))
    (hct : ∀ (i : ι) (y : M) (j : Fin 2) (σ : ℝ), Φ (σ, y) ∈ (φ i).source →
      ContinuousAt (fun τ : ℝ => φ i (Φ (τ, y)) j) σ)
    (hderivnn : ∀ (y : M) (σ : ℝ), 0 ≤ deriv (fun τ : ℝ => f (Φ (τ, y))) σ)
    (hzero : ∀ (y : M) (τ : ℝ), deriv (fun σ : ℝ => f (Φ (σ, y))) τ = 0 →
      ∃ i : ι, Φ (τ, y) ∈ C i ∧ (‖φ i (Φ (τ, y))‖ : ℝ) ^ 2 ≤ (r i) ^ 2 / 2)
    (hode0 : ∀ (i : ι) (y : M) (a b : ℝ), a ≤ b → (∀ u ∈ Set.Icc a b, Φ (u, y) ∈ C i) →
      (‖φ i (Φ (b, y))‖ : ℝ) ^ 2 ≤ (r i) ^ 2 / 2 →
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0) 0 b ∧
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1) 0 b) :
    ∀ (y : M) (s t : ℝ), f (Φ (s, y)) = f (Φ (t, y)) → Φ (s, y) = Φ (t, y) := by
  intro y s t hft
  have hγ : Continuous fun σ : ℝ => Φ (σ, y) := hΦcont.comp (continuous_id.prodMk continuous_const)
  have key : ∀ s t : ℝ, s ≤ t → f (Φ (s, y)) = f (Φ (t, y)) → Φ (s, y) = Φ (t, y) := by
    intro s t hst hft
    rcases lt_or_eq_of_le hst with hlt | heq
    · have hmono : MonotoneOn (fun σ : ℝ => f (Φ (σ, y))) (Set.Icc s t) :=
        monotoneOn_of_deriv_nonneg (convex_Icc s t)
          (hFcd y).continuous.continuousOn
          (fun u hu => ((hFcd y).differentiable (by norm_num)).differentiableAt.differentiableWithinAt)
          (fun u hu => hderivnn y u)
      have hconst : ∀ σ ∈ Set.Icc s t, f (Φ (σ, y)) = f (Φ (s, y)) := by
        intro σ hσ
        have h1 : f (Φ (s, y)) ≤ f (Φ (σ, y)) :=
          hmono (left_mem_Icc.mpr (le_of_lt hlt)) hσ hσ.1
        have h2 : f (Φ (σ, y)) ≤ f (Φ (t, y)) :=
          hmono hσ (right_mem_Icc.mpr (le_of_lt hlt)) hσ.2
        rw [← hft] at h2
        linarith
      have hderiv0 : ∀ σ ∈ Set.Ioo s t, deriv (fun τ : ℝ => f (Φ (τ, y))) σ = 0 := by
        intro σ hσ
        have hev : (fun τ : ℝ => f (Φ (τ, y))) =ᶠ[𝓝 σ] (fun _ => f (Φ (s, y))) := by
          filter_upwards [isOpen_Ioo.mem_nhds hσ] with τ hτ
          exact hconst τ (Set.Ioo_subset_Icc_self hτ)
        exact ((hasDerivAt_const σ (f (Φ (s, y)))).congr_of_eventuallyEq hev).deriv
      -- the orbit over `(s,t)` enters a single model ball, hence a single core
      obtain ⟨σ₀, hσ₀⟩ : ∃ σ : ℝ, σ ∈ Set.Ioo s t := ⟨(s + t) / 2, by constructor <;> linarith⟩
      obtain ⟨i₀, hi₀C, hi₀core⟩ := hzero y σ₀ (hderiv0 σ₀ hσ₀)
      have hcore : ∀ σ ∈ Set.Ioo s t, ∃ i : ι, Φ (σ, y) ∈ C i ∧
          (‖φ i (Φ (σ, y))‖ : ℝ) ^ 2 ≤ (r i) ^ 2 / 2 := fun σ hσ => hzero y σ (hderiv0 σ hσ)
      have hpre : IsPreconnected ((fun σ : ℝ => Φ (σ, y)) '' Set.Ioo s t) :=
        IsPreconnected.image (isPreconnected_Ioo (a := s) (b := t)) (f := fun σ => Φ (σ, y)) hγ.continuousOn
      have hcov : (fun σ : ℝ => Φ (σ, y)) '' Set.Ioo s t ⊆
          modelBall (φ i₀) (r i₀) ∪ ⋃ j ∈ ({i₀}ᶜ : Set ι), modelBall (φ j) (r j) := by
        rintro p ⟨σ, hσ, rfl⟩
        obtain ⟨i, hiC, hicore⟩ := hcore σ hσ
        have hb : Φ (σ, y) ∈ modelBall (φ i) (r i) :=
          ⟨hCsub i hiC, by nlinarith [hicore, hr i, norm_nonneg (φ i (Φ (σ, y)))]⟩
        by_cases hi : i = i₀
        · exact Or.inl (hi ▸ hb)
        · exact Or.inr (mem_iUnion₂.mpr ⟨i, by simp [hi], hb⟩)
      have hdisj' : Disjoint (modelBall (φ i₀) (r i₀))
          (⋃ j ∈ ({i₀}ᶜ : Set ι), modelBall (φ j) (r j)) := by
        rw [Set.disjoint_left]
        rintro p hp hp'
        obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp hp'
        have hji : i₀ ≠ j := by
          intro h
          exact hj (by rw [← h]; exact Set.mem_singleton i₀)
        exact (Set.disjoint_left.mp (hdisj i₀ j hji) hp.1) hpj.1
      have hsub : (fun σ : ℝ => Φ (σ, y)) '' Set.Ioo s t ⊆ modelBall (φ i₀) (r i₀) := by
        rcases hpre.subset_or_subset (isOpen_modelBall _ _)
          (isOpen_iUnion fun j => isOpen_iUnion fun _ => isOpen_modelBall _ _) hdisj' hcov with h | h
        · exact h
        · exfalso
          have hb₀ : Φ (σ₀, y) ∈ modelBall (φ i₀) (r i₀) :=
            ⟨hCsub i₀ hi₀C, by nlinarith [hi₀core, hr i₀]⟩
          exact (Set.disjoint_left.mp hdisj' hb₀) (h ⟨σ₀, hσ₀, rfl⟩)
      have hcore_i₀ : ∀ σ ∈ Set.Ioo s t,
          (‖φ i₀ (Φ (σ, y))‖ : ℝ) ^ 2 ≤ (r i₀) ^ 2 / 2 := by
        intro σ hσ
        obtain ⟨i, hiC, hicore⟩ := hcore σ hσ
        have hb : Φ (σ, y) ∈ modelBall (φ i) (r i) :=
          ⟨hCsub i hiC, by nlinarith [hicore, hr i, norm_nonneg (φ i (Φ (σ, y)))]⟩
        have hii : i = i₀ := by
          by_contra hne
          have h1 : Φ (σ, y) ∈ (φ i).source := hCsub i hiC
          have h2 : Φ (σ, y) ∈ (φ i₀).source := (hsub ⟨σ, hσ, rfl⟩).1
          have h3 : Disjoint ((φ i).source) ((φ i₀).source) := hdisj i i₀ hne
          exact (Set.disjoint_left.mp h3 h1) h2
        subst hii
        exact hicore
      -- the chart coordinates are constant on `(s,t)`
      have hderiv : ∀ (j : Fin 2) (u : ℝ), u ∈ Set.Ioo s t →
          HasDerivAt (fun τ : ℝ => φ i₀ (Φ (τ, y)) j) 0 u := by
        intro j u hu
        have hmid : (s + u) / 2 ∈ Set.Ioo s t := ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have hle' : (s + u) / 2 ≤ u := by linarith [hu.1]
        have hmemC : ∀ v ∈ Set.Icc ((s + u) / 2) u, Φ (v, y) ∈ C i₀ := fun v hv =>
          hCball i₀ (hsub ⟨v, ⟨by linarith [hv.1, hu.1], by linarith [hv.2, hu.2]⟩, rfl⟩)
        obtain ⟨hd0, hd1⟩ := hode0 i₀ y ((s + u) / 2) u hle' hmemC (hcore_i₀ u hu)
        fin_cases j
        · exact hd0
        · exact hd1
      have hconstIoo : ∀ (j : Fin 2) ⦃σ σ' : ℝ⦄, σ ∈ Set.Ioo s t → σ' ∈ Set.Ioo s t →
          φ i₀ (Φ (σ, y)) j = φ i₀ (Φ (σ', y)) j := by
        intro j σ σ' hσ hσ'
        have aux : ∀ ⦃a b : ℝ⦄, a ∈ Set.Ioo s t → b ∈ Set.Ioo s t → a ≤ b →
            φ i₀ (Φ (a, y)) j = φ i₀ (Φ (b, y)) j := by
          intro a b ha hb hab
          have hIoo : ∀ u ∈ interior (Set.Icc a b), u ∈ Set.Ioo s t := by
            intro u hu
            rw [interior_Icc] at hu
            exact ⟨by linarith [hu.1, ha.1], by linarith [hu.2, hb.2]⟩
          have hsrcm : ∀ u ∈ Set.Icc a b, Φ (u, y) ∈ (φ i₀).source := fun u hu =>
            hCsub i₀ (hCball i₀ (hsub ⟨u, ⟨by linarith [hu.1, ha.1], by linarith [hu.2, hb.2]⟩, rfl⟩))
          have hneg : ∀ u ∈ interior (Set.Icc a b),
              HasDerivAt (fun τ : ℝ => -(φ i₀ (Φ (τ, y)) j)) 0 u := by
            intro u hu
            have h := (hderiv j u (hIoo u hu)).const_mul (-1 : ℝ)
            simpa using h
          have hmono1 : MonotoneOn (fun τ : ℝ => φ i₀ (Φ (τ, y)) j) (Set.Icc a b) :=
            monotoneOn_of_deriv_nonneg (convex_Icc a b)
              (fun u hu => (hct i₀ y j u (hsrcm u hu)).continuousWithinAt)
              (fun u hu => (hderiv j u (hIoo u hu)).differentiableAt.differentiableWithinAt)
              (fun u hu => by rw [(hderiv j u (hIoo u hu)).deriv])
          have hmono2 : MonotoneOn (fun τ : ℝ => -(φ i₀ (Φ (τ, y)) j)) (Set.Icc a b) :=
            monotoneOn_of_deriv_nonneg (convex_Icc a b)
              (fun u hu => (hct i₀ y j u (hsrcm u hu)).neg.continuousWithinAt)
              (fun u hu => (hneg u hu).differentiableAt.differentiableWithinAt)
              (fun u hu => by rw [(hneg u hu).deriv])
          exact le_antisymm (hmono1 ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
            (by have := hmono2 ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab; simpa using this)
        rcases le_total σ σ' with h | h
        · exact aux hσ hσ' h
        · exact (aux hσ' hσ h).symm
      -- the orbit is constant, by continuity at the endpoints
      have hs_cl : Φ (s, y) ∈ closure (modelBall (φ i₀) (r i₀)) := by
        have h1 : s ∈ closure (Set.Ioo s t) := by
          rw [closure_Ioo (ne_of_lt hlt)]; exact ⟨le_rfl, le_of_lt hlt⟩
        have h2 : (fun σ : ℝ => Φ (σ, y)) '' closure (Set.Ioo s t) ⊆
            closure ((fun σ : ℝ => Φ (σ, y)) '' Set.Ioo s t) :=
          image_closure_subset_closure_image hγ
        exact closure_mono hsub (h2 ⟨s, h1, rfl⟩)
      have ht_cl : Φ (t, y) ∈ closure (modelBall (φ i₀) (r i₀)) := by
        have h1 : t ∈ closure (Set.Ioo s t) := by
          rw [closure_Ioo (ne_of_lt hlt)]; exact ⟨le_of_lt hlt, le_rfl⟩
        have h2 : (fun σ : ℝ => Φ (σ, y)) '' closure (Set.Ioo s t) ⊆
            closure ((fun σ : ℝ => Φ (σ, y)) '' Set.Ioo s t) :=
          image_closure_subset_closure_image hγ
        exact closure_mono hsub (h2 ⟨t, h1, rfl⟩)
      have hsrc : Φ (s, y) ∈ (φ i₀).source := hCcl i₀ (closure_mono (hCball i₀) hs_cl)
      have hsrc' : Φ (t, y) ∈ (φ i₀).source := hCcl i₀ (closure_mono (hCball i₀) ht_cl)
      haveI : NeBot (𝓝[Set.Ioo s t] s) := nhdsWithin_neBot.mpr
        (mem_closure_iff_nhds.mp (by
          rw [closure_Ioo (ne_of_lt hlt)]; exact ⟨le_rfl, le_of_lt hlt⟩))
      haveI : NeBot (𝓝[Set.Ioo s t] t) := nhdsWithin_neBot.mpr
        (mem_closure_iff_nhds.mp (by
          rw [closure_Ioo (ne_of_lt hlt)]; exact ⟨le_of_lt hlt, le_rfl⟩))
      have hmid : (s + t) / 2 ∈ Set.Ioo s t := ⟨by linarith, by linarith⟩
      have hmid_cont : ∀ j : Fin 2,
          Tendsto (fun σ : ℝ => φ i₀ (Φ (σ, y)) j) (𝓝[Set.Ioo s t] s)
              (𝓝 (φ i₀ (Φ (s, y)) j)) ∧
          Tendsto (fun σ : ℝ => φ i₀ (Φ (σ, y)) j) (𝓝[Set.Ioo s t] s)
              (𝓝 (φ i₀ (Φ ((s + t) / 2, y)) j)) := by
        intro j
        have hcj : ContinuousAt (fun σ : ℝ => φ i₀ (Φ (σ, y)) j) s :=
          hct i₀ y j s hsrc
        refine ⟨hcj.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
        have hev : (fun σ : ℝ => φ i₀ (Φ (σ, y)) j) =ᶠ[𝓝[Set.Ioo s t] s]
            (fun _ => φ i₀ (Φ ((s + t) / 2, y)) j) := by
          filter_upwards [self_mem_nhdsWithin] with σ hσ
          exact hconstIoo j hσ hmid
        exact tendsto_const_nhds.congr' hev.symm
      refine (φ i₀).injOn hsrc hsrc' (PiLp.ext fun j => ?_)
      obtain ⟨h1, h2⟩ := hmid_cont j
      have h3 : φ i₀ (Φ (s, y)) j = φ i₀ (Φ ((s + t) / 2, y)) j :=
        tendsto_nhds_unique h1 h2
      have hcj : ContinuousAt (fun σ : ℝ => φ i₀ (Φ (σ, y)) j) t :=
        hct i₀ y j t hsrc'
      have h4 : Tendsto (fun σ : ℝ => φ i₀ (Φ (σ, y)) j) (𝓝[Set.Ioo s t] t)
          (𝓝 (φ i₀ (Φ (t, y)) j)) := hcj.tendsto.mono_left nhdsWithin_le_nhds
      have h5 : Tendsto (fun σ : ℝ => φ i₀ (Φ (σ, y)) j) (𝓝[Set.Ioo s t] t)
          (𝓝 (φ i₀ (Φ ((s + t) / 2, y)) j)) := by
        have hev : (fun σ : ℝ => φ i₀ (Φ (σ, y)) j) =ᶠ[𝓝[Set.Ioo s t] t]
            (fun _ => φ i₀ (Φ ((s + t) / 2, y)) j) := by
          filter_upwards [self_mem_nhdsWithin] with σ hσ
          exact hconstIoo j hσ hmid
        exact tendsto_const_nhds.congr' hev.symm
      have h6 : φ i₀ (Φ (t, y)) j = φ i₀ (Φ ((s + t) / 2, y)) j :=
        tendsto_nhds_unique h4 h5
      rw [h3, h6]
    · rw [heq]
  rcases le_total s t with h | h
  · exact key s t h hft
  · exact (key t s h hft.symm).symm
