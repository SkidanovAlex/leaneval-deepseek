import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.Sweep
import Submission.Lib.Unif2.ChartLogClamp
import Submission.Lib.Unif2.MaxPrincipleRegion

/-!
# The sweep of the clamped logarithmic potential

This module assembles the **conditional reduction** of the uniformization theorem to the
existence of the Green function.

* `Submission.sweep G U` is the *least superharmonic majorant* of the barrier `G` on the open set
  `U`: the pointwise infimum of the sweep family `sweepFamily G U`.  If the family is nonempty
  then the sweep is harmonic on `U` (`sweep_harmonic`, from `Sweep.lean`), it dominates the
  barrier (`barrier_le_sweep`), it is dominated by *every* member of the family
  (`sweep_le_of_mem`) and it is non-negative whenever the barrier is (`sweep_nonneg`).
* **`Submission.sweep_pos`** — the sweep is *strictly positive* on `U` as soon as the barrier is
  strictly positive in a neighbourhood of the (nonempty) complement of `U`.  The classical proof
  used here: the set `S = {x ∈ U | E x = 0}` is clopen in `X` (open by the local strong maximum
  principle applied to `-E`, closed because `E > 0` near the boundary of `U`), so `S = ∅` or
  `S = X` by connectedness of `X`; but `S ⊆ U ≠ X`.
* `Submission.greenBarrier z₀ ρ` — the barrier of the Green-function construction, i.e. the
  clamped logarithmic potential `chartLogClamp` of the preferred chart at `z₀`; it is
  subharmonic on `univ ∖ {z₀}` (`subharmonicOnX_greenBarrier`) and satisfies the logarithmic
  lower bound `log (ρ / s)` on every smaller chart ball
  (`greenBarrier_lower_bound`), whence the sweep has a logarithmic pole
  (`sweep_greenBarrier_log_pole`).

Everything here is conditional on `(sweepFamily …).Nonempty`, which is *exactly* the existence of
a positive superharmonic function on `X` with a logarithmic pole at `z₀` (hyperbolicity of `X`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section SweepBasic

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {G : X → ℝ} {U : Set X}

/-- The **sweep** (balayage) of the barrier `G` on `U`: the pointwise infimum of the
superharmonic functions on `U` dominating `G`; the *least superharmonic majorant* of `G`. -/
def sweep (G : X → ℝ) (U : Set X) : X → ℝ := lowerEnvelope (sweepFamily G U)

/-- Every member of the sweep family dominates the sweep. -/
theorem sweep_le_of_mem {v : X → ℝ} (hv : v ∈ sweepFamily G U) {x : X} (hx : x ∈ U) :
    sweep G U x ≤ v x := by
  have hbdd : BddBelow ((fun f : X → ℝ => f x) '' sweepFamily G U) :=
    ⟨G x, by
      rintro y ⟨w, hw, rfl⟩
      exact sweepFamily_le hw hx⟩
  exact csInf_le hbdd (mem_image_of_mem _ hv)

/-- A lower bound satisfied by every member of the sweep family is a lower bound of the sweep. -/
theorem le_sweep_of_le (hne : (sweepFamily G U).Nonempty) {a : ℝ} {x : X} (hx : x ∈ U)
    (h : ∀ v ∈ sweepFamily G U, a ≤ v x) : a ≤ sweep G U x :=
  le_csInf (hne.image _) (by
    rintro b ⟨v, hv, rfl⟩
    exact h v hv)

/-- The sweep dominates the barrier. -/
theorem barrier_le_sweep (hne : (sweepFamily G U).Nonempty) {x : X} (hx : x ∈ U) :
    G x ≤ sweep G U x :=
  le_sweep_of_le hne hx (fun v hv => sweepFamily_le hv hx)

/-- The sweep of a non-negative barrier is non-negative. -/
theorem sweep_nonneg (hne : (sweepFamily G U).Nonempty) (hGnn : ∀ x ∈ U, 0 ≤ G x)
    {x : X} (hx : x ∈ U) : 0 ≤ sweep G U x :=
  le_sweep_of_le hne hx (fun v hv => le_trans (hGnn x hx) (sweepFamily_le hv hx))

/-- The sweep of a subharmonic barrier on an open set is harmonic. -/
theorem sweep_harmonic (hU : IsOpen U) (hG : SubharmonicOnX G U)
    (hne : (sweepFamily G U).Nonempty) : HarmonicOnX (sweep G U) U :=
  lowerEnvelope_sweepFamily_harmonic hU hG hne

end SweepBasic

section SweepPos

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {G : X → ℝ} {U : Set X}

/-- **Strict positivity of the sweep.**  If the barrier `G` is non-negative on the open set `U`,
strictly positive near the complement of `U` (in the sense of `hbdy`), `U ≠ univ`, and the sweep
family is nonempty, then the sweep is strictly positive on `U`. -/
theorem sweep_pos (hU : IsOpen U) (hG : SubharmonicOnX G U) (hne : (sweepFamily G U).Nonempty)
    (hGnn : ∀ x ∈ U, 0 ≤ G x) (hex : ∃ x : X, x ∉ U)
    (hbdy : ∀ x : X, x ∉ U → ∃ s : Set X, s ∈ 𝓝 x ∧ ∀ y ∈ s, y ∈ U → 0 < G y) :
    ∀ x ∈ U, 0 < sweep G U x := by
  have hEharm : HarmonicOnX (sweep G U) U := sweep_harmonic hU hG hne
  have hEnn : ∀ x ∈ U, 0 ≤ sweep G U x := fun x hx => sweep_nonneg hne hGnn hx
  have hEG : ∀ x ∈ U, G x ≤ sweep G U x := fun x hx => barrier_le_sweep hne hx
  set S : Set X := {x : X | x ∈ U ∧ sweep G U x = 0} with hSdef
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxU, hx0⟩
    have hsub : SubharmonicOnXAt (fun y : X => -(sweep G U y)) x :=
      ((hEharm x hxU).neg).subharmonic
    have hle : ∀ y ∈ U, -(sweep G U y) ≤ -(sweep G U x) := fun y hy => by
      rw [hx0, neg_zero]
      exact neg_nonpos.mpr (hEnn y hy)
    obtain ⟨V, hVn, hVeq⟩ := SubharmonicOnXAt.eqOn_of_le hsub (hU.mem_nhds hxU) hle
    refine mem_of_superset (inter_mem hVn (hU.mem_nhds hxU)) ?_
    rintro y ⟨hyV, hyU⟩
    have h1 : -(sweep G U y) = -(sweep G U x) := hVeq y hyV
    rw [hx0, neg_zero] at h1
    exact ⟨hyU, by linarith⟩
  have hScompl : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    rintro x hxS
    by_cases hxU : x ∈ U
    · -- `x ∈ U` and `E x ≠ 0`, hence `E x > 0` near `x`
      have hxpos : 0 < sweep G U x := lt_of_le_of_ne (hEnn x hxU) (fun h0 => hxS ⟨hxU, h0.symm⟩)
      have hcont : ContinuousAt (sweep G U) x := (hEharm x hxU).continuousAt
      have hmem : {y : X | 0 < sweep G U y} ∈ 𝓝 x :=
        hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hxpos)
      refine mem_of_superset hmem ?_
      rintro y hy
      exact fun hyS => absurd hyS.2 (ne_of_gt hy)
    · -- `x ∉ U`: the barrier is positive on a neighbourhood of `x`, where the sweep is too
      obtain ⟨s, hsn, hsG⟩ := hbdy x hxU
      refine mem_of_superset hsn ?_
      rintro y hy
      rintro ⟨hyU, hy0⟩
      exact absurd (lt_of_lt_of_le (hsG y hy hyU) (hEG y hyU)) (not_lt.mpr (le_of_eq hy0))
  have hScl : IsClopen S := ⟨isOpen_compl_iff.mp hScompl, hSopen⟩
  obtain ⟨x₀, hx₀⟩ := hex
  have hx₀S : x₀ ∉ S := fun h => hx₀ h.1
  intro x hxU
  refine lt_of_le_of_ne (hEnn x hxU) (fun h0 => ?_)
  have hxS : x ∈ S := ⟨hxU, h0.symm⟩
  have hsub : univ ⊆ S :=
    (connectedSpace_iff_univ.mp ‹ConnectedSpace X›).isPreconnected.subset_isClopen hScl
      ⟨x, mem_univ x, hxS⟩
  exact hx₀S (hsub (mem_univ x₀))

end SweepPos

/-! ## The barrier of the Green-function construction -/

section GreenBarrier

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The **barrier of the Green-function construction**: the clamped logarithmic potential of the
preferred chart at `z₀`, with clamping radius `ρ`. -/
def greenBarrier (z₀ : X) (ρ : ℝ) : X → ℝ :=
  chartLogClamp (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ

theorem greenBarrier_apply (z₀ : X) (ρ : ℝ) (x : X) :
    greenBarrier z₀ ρ x
      = chartLogClamp (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ x := rfl

/-- The barrier is subharmonic on `X` minus the pole. -/
theorem subharmonicOnX_greenBarrier {z₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall ((chartAt ℂ z₀) z₀) ρ ⊆ (chartAt ℂ z₀).target) :
    SubharmonicOnX (greenBarrier z₀ ρ) (univ \ {z₀}) :=
  subharmonicOnX_chartLogClamp hρ hsub

/-- On the chart ball of radius `s < ρ` around the pole, the barrier dominates `log (ρ / s)`. -/
theorem greenBarrier_lower_bound {z₀ : X} {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hsρ : s < ρ)
    {x : X} (hx : x ∈ chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) s)
    (hxne : (chartAt ℂ z₀) x ≠ (chartAt ℂ z₀) z₀) :
    Real.log (ρ / s) ≤ greenBarrier z₀ ρ x :=
  chartLogClamp_lower_bound hρ hs hsρ.le hx hxne

/-- A smaller chart ball around the pole is a neighbourhood of the pole. -/
theorem chartBall_greenBarrier_mem_nhds {z₀ : X} {s : ℝ} (hs : 0 < s) :
    chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) s ∈ 𝓝 z₀ :=
  chartBall_mem_nhds hs (mem_chart_source ℂ z₀) rfl

/-- The sweep of the Green barrier has a logarithmic pole at `z₀`. -/
theorem sweep_greenBarrier_log_pole {z₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall ((chartAt ℂ z₀) z₀) ρ ⊆ (chartAt ℂ z₀).target)
    (hne : (sweepFamily (greenBarrier z₀ ρ) (univ \ {z₀})).Nonempty) (C : ℝ) :
    ∃ V : Set X, V ∈ 𝓝 z₀ ∧
      ∀ y ∈ V, y ≠ z₀ → C < sweep (greenBarrier z₀ ρ) (univ \ {z₀}) y := by
  set m : ℝ := min 1 (Real.exp (-C)) with hmdef
  have hmpos : 0 < m := lt_min one_pos (Real.exp_pos _)
  have hmle : m ≤ 1 := min_le_left _ _
  have hmle' : m ≤ Real.exp (-C) := min_le_right _ _
  set s : ℝ := ρ * m / 2 with hsdef
  have hs : 0 < s := by rw [hsdef]; positivity
  have hsρ : s < ρ := by
    rw [hsdef]
    nlinarith [hρ, hmpos, hmle]
  have hsx : s < ρ * Real.exp (-C) := by
    rw [hsdef]
    have h2 : ρ * m / 2 < ρ * m := by nlinarith [hρ, hmpos]
    have h3 : ρ * m ≤ ρ * Real.exp (-C) := mul_le_mul_of_nonneg_left hmle' hρ.le
    linarith
  refine ⟨chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) s,
    chartBall_greenBarrier_mem_nhds hs, ?_⟩
  intro y hy hyne
  have hysrc : y ∈ (chartAt ℂ z₀).source := hy.1
  have hyU : y ∈ (univ \ {z₀} : Set X) := ⟨mem_univ y, hyne⟩
  have hyne' : (chartAt ℂ z₀) y ≠ (chartAt ℂ z₀) z₀ := by
    intro h
    exact hyne ((chartAt ℂ z₀).injOn hysrc (mem_chart_source ℂ z₀) h)
  have h1 : Real.log (ρ / s) ≤ greenBarrier z₀ ρ y :=
    greenBarrier_lower_bound hρ hs hsρ hy hyne'
  have h2 : greenBarrier z₀ ρ y ≤ sweep (greenBarrier z₀ ρ) (univ \ {z₀}) y :=
    barrier_le_sweep hne hyU
  have h3 : C < Real.log (ρ / s) := by
    have hr : Real.exp C < ρ / s := by
      have h4 : s * Real.exp C < ρ := by
        have hsx' : s < ρ * (Real.exp C)⁻¹ := by simpa [Real.exp_neg] using hsx
        have h5 := mul_lt_mul_of_pos_right hsx' (Real.exp_pos C)
        rw [mul_assoc ρ ((Real.exp C)⁻¹) (Real.exp C),
          inv_mul_cancel₀ (ne_of_gt (Real.exp_pos C)), mul_one] at h5
        linarith
      rwa [lt_div_iff₀ hs, mul_comm]
    have h5 := Real.log_lt_log (Real.exp_pos C) hr
    rwa [Real.log_exp] at h5
  linarith

end GreenBarrier

end Submission
