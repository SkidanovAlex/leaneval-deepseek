import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.germCHelpers
import Submission.Work.EQ.germC_step_algebra
import Submission.Work.EQ.germC_apply_ne
import Submission.Work.EQ.germC_snd_deriv

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN.md and DESIGN_CORE.md (orchestrator designs; your lemma is one node). Defs: Submission/Work/EQ/Defs.lean + DefsCore.lean (namespace Work.EQ; do NOT edit). The proved UNIFORMIZATION library is in this workspace (Submission.UnifMain etc.; see DESIGN_CORE 'Library use'). NOTE: importing UnifMain makes `open Topology` resolve to Work.Topology — write `open _root_.Topology`.

# germC_facts: the stable germ in rectangular coordinates (1–2k)

**Claim.** `germC` is analytic near 0 and `germC 0 = A₁ = (-1/2, 0)`. Consecutive germ points form a
`RegPair`, and the principal backward branch `invBranch a true` inverts the step. Also
`y = (germC u).2` is injective near 0 with `y'(0) = (1-a)/2`.

**Numerically checked** (a = 3/10, series of `h` to `u¹³` from `GermFE`, complex `u = 0.05+0.02i`,
`0.1-0.03i`):
* both `EqRelC` equations to 1e-16;
* `invBranch true` inverts to 1e-16;
* `y'(0) = 0.35 = (1-a)/2`;
* `x(0) = -1/2`.

**Route.**
* `dslope` makes every factor analytic. The denominator at 0 is `(λ-1)h'(0) = 1-λ ≠ 0`.
* `EqRelC(P,Q)` with `Q = germC(λu)`: write `P = (X,Y)` and `W := Y/(X-a/2) = h(λu)` (algebra).
  The relation reduces to `GermFE` at `λu`, i.e. `hh`'s last clause, after the substitution
  `A,B,C = h(u), h(λu), h(λ²u)`. Do this by clearing denominators.
* The nondegeneracy conditions hold at `u = 0`, since `(-1/2 ∓ a/2)² ≠ 0`, and hence nearby by continuity.
* Principal branch: at `Q = A₁`, `ρ' = (1-a)/2 > 0` and `invBranch true A₁ = A₁`. The identity then holds
  on a connected neighbourhood, because both sides are analytic and agree on the real segment.
  Alternatively, compare the explicit `x`-coordinates.

**Pitfall.** `GermFE` uses the principal `cpow (1/2)`. Near `B = 0` it is analytic, so no branch issues
arise.
-/

namespace Work.EQ

open Complex Metric Filter Set
open scoped Topology

noncomputable section

set_option maxHeartbeats 1600000

/-- **The local stable curve in rectangular coordinates.** `germC` is analytic near `0`,
passes through `A₁ = (-1/2, 0)`, is conjugated by the principal branch to `u ↦ λu`, and its
`y`-coordinate is a local coordinate (`y'(0) = (1 - a)/2`). -/
theorem germC_facts {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ρ : ℝ, 0 < ρ ∧ AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρ) ∧
      germC a h 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
      (∀ u ∈ Metric.ball (0 : ℂ) ρ, RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)) ∧
        invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u) ∧
      Set.InjOn (fun u => (germC a h u).2) (Metric.ball 0 ρ) ∧
      deriv (fun u => (germC a h u).2) 0 = ((1 - a) / 2 : ℝ) := by
  obtain ⟨hr, hAn, h0, hderiv, hreal, hFE⟩ := hh
  have hl0 : 0 < eqLam a := by rw [eqLam]; positivity
  have hl1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by simpa using hr
  have hAn0 : AnalyticAt ℂ h 0 := hAn 0 hmem0
  have hAnA0 : AnalyticAt ℂ (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 := by
    have h1 : AnalyticAt ℂ (fun v : ℂ => (eqLam a : ℂ) * v) 0 :=
      analyticAt_const.mul analyticAt_id
    have h2 : AnalyticAt ℂ h ((eqLam a : ℂ) * 0) := hAn _ (by simpa using hmem0)
    simpa [Function.comp_def] using h2.comp h1
  have hAa0 : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 0 = -(eqLam a : ℂ) := by
    rw [dslope_same]; exact deriv_eqLam_mul hderiv
  have hDA0 : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 0 = 1 - (eqLam a : ℂ) := by
    rw [dslope_same]
    change deriv ((fun v : ℂ => h ((eqLam a : ℂ) * v)) - h) 0 = 1 - (eqLam a : ℂ)
    rw [deriv_sub hAnA0.differentiableAt hAn0.differentiableAt, deriv_eqLam_mul hderiv, hderiv]
    ring
  have hDHa0 : dslope h 0 0 = -1 := by rw [dslope_same, hderiv]
  have hgerm0 : germC a h 0 = ((-1 / 2 : ℂ), (0 : ℂ)) := by
    have hpair : germC a h 0 =
        (a * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 0 /
          dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 0 - a / 2,
         a * 0 * dslope h 0 0 * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 0 /
          dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 0) := rfl
    rw [hpair, hAa0, hDA0, hDHa0]
    refine Prod.ext ?_ ?_
    · have hreal' : a * (-(eqLam a)) / (1 - eqLam a) - a / 2 = -(1/2 : ℝ) := by
        rw [eqLam]; field_simp [ha0.ne']; ring
      have hcast := congrArg (fun x : ℝ => (x : ℂ)) hreal'
      push_cast at hcast
      convert hcast using 2 <;> ring
    · ring
  -- the denominator `dslope (h ∘ (λ·) - h) 0 ·` does not vanish near `0`
  have hDA0ne : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 0 ≠ 0 := by
    rw [hDA0, sub_ne_zero]
    intro hcon
    have : eqLam a = 1 := by exact_mod_cast hcon.symm
    linarith
  have hDAcont : ContinuousAt
      (fun u : ℂ => dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 u) 0 :=
    (analyticAt_dslope (hAnA0.sub hAn0)).continuousAt
  obtain ⟨ρ₁', hρ₁'pos, hρ₁'⟩ := exists_ball_of_eventually (hDAcont.eventually_ne hDA0ne)
  set ρ₁ : ℝ := min ρ₁' r with hρ₁def
  have hρ₁pos : 0 < ρ₁ := by rw [hρ₁def]; exact lt_min hρ₁'pos hr
  have hρ₁r : ρ₁ ≤ r := by rw [hρ₁def]; exact min_le_right _ _
  have hρ₁ne : ∀ u ∈ Metric.ball (0 : ℂ) ρ₁,
      dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 u ≠ 0 := by
    intro u hu
    exact hρ₁' u (Metric.ball_subset_ball (by rw [hρ₁def]; exact min_le_left _ _) hu)
  have hAnC : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρ₁) := by
    intro u hu
    have huρ : ‖u‖ < ρ₁ := by
      have h := hu; rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h; exact h
    have hu_lt : ‖u‖ < r := lt_of_lt_of_le huρ hρ₁r
    have hu_ballr : u ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hu_lt
    have hlam : AnalyticAt ℂ (fun v : ℂ => h ((eqLam a : ℂ) * v)) u :=
      analyticAt_h_comp hAn hl0 hl1 hr hu_lt
    have hAatu : AnalyticAt ℂ (dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0) u :=
      analyticAt_dslope hlam
    have hDAtu : AnalyticAt ℂ (dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0) u :=
      analyticAt_dslope (hlam.sub (hAn u hu_ballr))
    have hDHatu : AnalyticAt ℂ (dslope h 0) u :=
      analyticAt_dslope (hAn u hu_ballr)
    have hne := hρ₁ne u hu
    have hpair : AnalyticAt ℂ (fun u : ℂ =>
        (a * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 u /
          dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 u - a / 2,
         a * u * dslope h 0 u * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 u /
          dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 u)) u := by
      refine AnalyticAt.prod ?_ ?_
      · exact ((analyticAt_const.mul hAatu).div hDAtu hne).sub analyticAt_const
      · exact (((analyticAt_const.mul analyticAt_id).mul hDHatu).mul hAatu).div hDAtu hne
    exact hpair
  have hAnY : AnalyticAt ℂ (fun u : ℂ => (germC a h u).2) 0 := by
    have hproj : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (germC a h 0) :=
      (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _
    have h1 := hproj.comp (hAnC 0 (by simp [hρ₁pos]))
    simpa [Function.comp_def] using h1
  have hderivY : deriv (fun u : ℂ => (germC a h u).2) 0 = (((1 - a) / 2 : ℝ) : ℂ) :=
    germC_snd_deriv ha0 ha1 ⟨hr, hAn, h0, hderiv, hreal, hFE⟩
  have hstr : HasStrictDerivAt (fun u : ℂ => (germC a h u).2) (((1 - a) / 2 : ℝ) : ℂ) 0 := by
    have h1 := hAnY.hasStrictDerivAt
    rwa [hderivY] at h1
  have hstrne : (((1 - a) / 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; linarith
  have hF := hstr.hasStrictFDerivAt_equiv hstrne
  set e : OpenPartialHomeomorph ℂ ℂ :=
    hF.toOpenPartialHomeomorph (fun u : ℂ => (germC a h u).2) with hedef
  have hmem_src : (0 : ℂ) ∈ e.source := hF.mem_toOpenPartialHomeomorph_source
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hmem_src)
  have hinj : Set.InjOn (fun u : ℂ => (germC a h u).2) (Metric.ball (0 : ℂ) ε) := by
    intro x hx y hy hxy
    exact e.injOn (hε hx) (hε hy) hxy
  -- non-degeneracy of the two local radii
  have hPnd : ∀ᶠ u in 𝓝 (0 : ℂ),
      ((germC a h u).1 - ((a / 2 : ℝ) : ℂ)) ^ 2 + (germC a h u).2 ^ 2 ≠ 0 := by
    have hcont : ContinuousAt
        (fun u : ℂ => ((germC a h u).1 - ((a / 2 : ℝ) : ℂ)) ^ 2 + (germC a h u).2 ^ 2) 0 := by
      have hg := (hAnC 0 (by simp [hρ₁pos])).continuousAt
      exact ((hg.fst.sub continuousAt_const).pow 2).add (hg.snd.pow 2)
    refine hcont.eventually_ne ?_
    rw [hgerm0]
    have hx : ((-1 / 2 : ℂ) - ((a / 2 : ℝ) : ℂ)) ≠ 0 := by
      rw [show ((-1 / 2 : ℂ) - ((a / 2 : ℝ) : ℂ)) = (((-1 - a) / 2 : ℝ) : ℂ) by
        push_cast; ring]
      simp only [Complex.ofReal_ne_zero]
      exact div_ne_zero (by linarith) (by norm_num)
    simpa using pow_ne_zero 2 hx
  have hQnd : ∀ᶠ u in 𝓝 (0 : ℂ),
      ((germC a h ((eqLam a : ℂ) * u)).1 + ((a / 2 : ℝ) : ℂ)) ^ 2
        + (germC a h ((eqLam a : ℂ) * u)).2 ^ 2 ≠ 0 := by
    have hcont : ContinuousAt
        (fun u : ℂ => ((germC a h ((eqLam a : ℂ) * u)).1 + ((a / 2 : ℝ) : ℂ)) ^ 2
          + (germC a h ((eqLam a : ℂ) * u)).2 ^ 2) 0 := by
      have hcomp : ContinuousAt (fun u : ℂ => germC a h ((eqLam a : ℂ) * u)) 0 := by
        have hinner : ContinuousAt (fun u : ℂ => (eqLam a : ℂ) * u) 0 := by fun_prop
        have h1 : ContinuousAt (germC a h) ((eqLam a : ℂ) * 0) := by
          rw [mul_zero]
          exact (hAnC 0 (by simp [hρ₁pos])).continuousAt
        exact h1.comp' hinner
      exact ((hcomp.fst.add continuousAt_const).pow 2).add (hcomp.snd.pow 2)
    refine hcont.eventually_ne ?_
    rw [mul_zero, hgerm0]
    have hx : ((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) ≠ 0 := by
      rw [show ((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) = (((a - 1) / 2 : ℝ) : ℂ) by
        push_cast; ring]
      simp only [Complex.ofReal_ne_zero]
      exact div_ne_zero (by linarith) (by norm_num)
    simpa using pow_ne_zero 2 hx
  -- positivity of the real part of `R = -E S` near `0`
  set F : ℂ → ℝ := fun u => ((-((a : ℂ) * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0
        ((eqLam a : ℂ) * u) / dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0
        ((eqLam a : ℂ) * u))) *
      (1 + h ((eqLam a : ℂ) * u) ^ 2) ^ (1 / 2 : ℂ)).re with hFdef
  have hRev : ∀ᶠ u in 𝓝 (0 : ℂ), 0 < F u := by
    have hinner : ContinuousAt (fun u : ℂ => (eqLam a : ℂ) * u) 0 := by fun_prop
    have houter : ContinuousAt (fun z : ℂ => dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 z)
        ((eqLam a : ℂ) * 0) := by
      rw [mul_zero]
      exact (analyticAt_dslope hAnA0).continuousAt
    have houter2 : ContinuousAt
        (fun z : ℂ => dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 z)
        ((eqLam a : ℂ) * 0) := by
      rw [mul_zero]
      exact (analyticAt_dslope (hAnA0.sub hAn0)).continuousAt
    have hbase : ContinuousAt (fun u : ℂ => dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0
        ((eqLam a : ℂ) * u)) 0 := houter.comp' hinner
    have hden : ContinuousAt (fun u : ℂ => dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0
        ((eqLam a : ℂ) * u)) 0 := houter2.comp' hinner
    have hdiv : ContinuousAt (fun u : ℂ => (a : ℂ) *
        dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 ((eqLam a : ℂ) * u) /
        dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 ((eqLam a : ℂ) * u)) 0 :=
      (continuousAt_const.mul hbase).div hden (by simpa using hDA0ne)
    have hfh : ContinuousAt (fun u : ℂ => h ((eqLam a : ℂ) * u)) 0 := by
      have h1 : ContinuousAt h ((eqLam a : ℂ) * 0) := by
        rw [mul_zero]
        exact hAn0.continuousAt
      exact h1.comp' hinner
    have hcp : ContinuousAt
        (fun u : ℂ => (1 + h ((eqLam a : ℂ) * u) ^ 2) ^ (1 / 2 : ℂ)) 0 := by
      have hf : ContinuousAt (fun u : ℂ => 1 + h ((eqLam a : ℂ) * u) ^ 2) 0 :=
        continuousAt_const.add (hfh.pow 2)
      have h := ContinuousAt.cpow (f := fun u : ℂ => 1 + h ((eqLam a : ℂ) * u) ^ 2)
        (g := fun _ : ℂ => (1 / 2 : ℂ)) hf continuousAt_const ?_
      · simpa using h
      · rw [show (1 : ℂ) + h ((eqLam a : ℂ) * 0) ^ 2 = 1 by rw [mul_zero, h0]; ring]
        exact Or.inl zero_lt_one
    have hcont : ContinuousAt F 0 := by
      rw [hFdef]
      exact Complex.continuous_re.continuousAt.comp' (hdiv.neg.mul hcp)
    have hval0 : F 0 = (1 - a) / 2 := by
      rw [hFdef]
      beta_reduce
      rw [mul_zero, h0, hAa0, hDA0]
      have hone : (1 + (0 : ℂ) ^ 2) ^ (1 / 2 : ℂ) = 1 := by
        rw [show (1 : ℂ) + 0 ^ 2 = 1 by ring, one_cpow]
      rw [hone, mul_one]
      have hreal : a * (-(eqLam a)) / (1 - eqLam a) = (a - 1) / 2 := by
        rw [eqLam]; field_simp [ha0.ne']; ring
      have h3 : (a : ℂ) * (-(eqLam a : ℂ)) / (1 - (eqLam a : ℂ)) = (((a - 1) / 2 : ℝ) : ℂ) := by
        exact_mod_cast hreal
      rw [h3]
      simp only [Complex.neg_re, Complex.ofReal_re]
      ring
    have ht : Tendsto F (𝓝 (0 : ℂ)) (𝓝 ((1 - a) / 2)) := by
      have h := hcont.tendsto
      rwa [hval0] at h
    have hconst : Tendsto (fun _ : ℂ => (0 : ℝ)) (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds
    exact hconst.eventually_lt ht (by linarith)
  obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ := exists_ball_of_eventually hPnd
  obtain ⟨ρ₃, hρ₃pos, hρ₃⟩ := exists_ball_of_eventually hQnd
  obtain ⟨ρ₄, hρ₄pos, hρ₄⟩ := exists_ball_of_eventually hRev
  set ρ₀ : ℝ := min ρ₁ (min ρ₂ (min ρ₃ ρ₄)) with hρ₀def
  have hρ₀le₁ : ρ₀ ≤ ρ₁ := by rw [hρ₀def]; exact min_le_left _ _
  have hρ₀le₂ : ρ₀ ≤ ρ₂ := by
    rw [hρ₀def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ₀le₃ : ρ₀ ≤ ρ₃ := by
    rw [hρ₀def]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ₀le₄ : ρ₀ ≤ ρ₄ := by
    rw [hρ₀def]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρ₀pos : 0 < ρ₀ := by
    rw [hρ₀def]
    exact lt_min hρ₁pos (lt_min hρ₂pos (lt_min hρ₃pos hρ₄pos))
  set ρ : ℝ := min ρ₀ ε with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min hρ₀pos hεpos
  have hρle₀ : ρ ≤ ρ₀ := by rw [hρdef]; exact min_le_left _ _
  have hρleε : ρ ≤ ε := by rw [hρdef]; exact min_le_right _ _
  have hρle₁ : ρ ≤ ρ₁ := le_trans hρle₀ hρ₀le₁
  have hρle₂ : ρ ≤ ρ₂ := le_trans hρle₀ hρ₀le₂
  have hρle₃ : ρ ≤ ρ₃ := le_trans hρle₀ hρ₀le₃
  have hρle₄ : ρ ≤ ρ₄ := le_trans hρle₀ hρ₀le₄
  have hndP0 : (((-1 / 2 : ℂ) - ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2) ≠ 0 := by
    have hx : ((-1 / 2 : ℂ) - ((a / 2 : ℝ) : ℂ)) ≠ 0 := by
      rw [show ((-1 / 2 : ℂ) - ((a / 2 : ℝ) : ℂ)) = (((-1 - a) / 2 : ℝ) : ℂ) by
        push_cast; ring]
      simp only [Complex.ofReal_ne_zero]
      exact div_ne_zero (by linarith) (by norm_num)
    simpa using pow_ne_zero 2 hx
  have hndQ0 : (((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2) ≠ 0 := by
    have hx : ((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) ≠ 0 := by
      rw [show ((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) = (((a - 1) / 2 : ℝ) : ℂ) by
        push_cast; ring]
      simp only [Complex.ofReal_ne_zero]
      exact div_ne_zero (by linarith) (by norm_num)
    simpa using pow_ne_zero 2 hx
  have hinv0 : invBranch a true ((-1 / 2 : ℂ), (0 : ℂ)) = ((-1 / 2 : ℂ), (0 : ℂ)) := by
    have hcp : (((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2) ^ (1 / 2 : ℂ)
        = (((1 - a) / 2 : ℝ) : ℂ) := by
      have hx : ((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2
          = ((((1 - a) / 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hx, ofReal_cpow_half (by positivity), Real.sqrt_sq (by linarith)]
    have hx : ((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) = -(((1 - a) / 2 : ℝ) : ℂ) := by
      push_cast; ring
    have hne : (((1 - a) / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact div_ne_zero (by linarith) (by norm_num)
    simp only [invBranch, ite_true]
    rw [hcp, hx]
    refine Prod.ext ?_ ?_
    · field_simp
      ring
    · ring
  refine ⟨ρ, hρpos, hAnC.mono (Metric.ball_subset_ball hρle₁), hgerm0, ?_, ?_, hderivY⟩
  · intro u hu
    have hu₁ : u ∈ Metric.ball (0 : ℂ) ρ₁ := Metric.ball_subset_ball hρle₁ hu
    have hu_ball0 : u ∈ Metric.ball (0 : ℂ) ρ₀ := Metric.ball_subset_ball hρle₀ hu
    have huρ₁ : ‖u‖ < ρ₁ := by
      have h := hu₁; rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h; exact h
    have hu_lt : ‖u‖ < r := lt_of_lt_of_le huρ₁ hρ₁r
    rcases eq_or_ne u 0 with rfl | hu0
    · rw [mul_zero, hgerm0]
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · norm_num
      · ring
      · exact hndP0
      · exact hndQ0
      · exact hinv0
    · have hlu_ne : (eqLam a : ℂ) * u ≠ 0 :=
        mul_ne_zero (by exact_mod_cast (ne_of_gt hl0)) hu0
      have hlu_ball₁ : (eqLam a : ℂ) * u ∈ Metric.ball (0 : ℂ) ρ₁ := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact norm_mul_lt_of_lt hl0 hl1 hρ₁pos huρ₁
      have hBA : h ((eqLam a : ℂ) * u) - h u ≠ 0 := by
        have h1 : u * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 u
            = h ((eqLam a : ℂ) * u) - h u :=
          mul_dslope_eq (f := fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) (v := u)
            (by rw [mul_zero, h0]; ring)
        rw [← h1]
        exact mul_ne_zero hu0 (hρ₁ne u hu₁)
      have hCB : h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u) ≠ 0 := by
        have h1 : ((eqLam a : ℂ) * u) * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0
            ((eqLam a : ℂ) * u)
            = h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u) :=
          mul_dslope_eq (f := fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) (v := (eqLam a : ℂ) * u)
            (by rw [mul_zero, h0]; ring)
        rw [← h1]
        exact mul_ne_zero hlu_ne (hρ₁ne _ hlu_ball₁)
      have hFE' : (h ((eqLam a : ℂ) * u) - h u) *
            (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u)) +
          (a : ℂ) * h ((eqLam a : ℂ) * u) *
            (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h u) *
            (1 + h ((eqLam a : ℂ) * u) ^ 2) ^ (1 / 2 : ℂ) = 0 := by
        have h1 := hFE ((eqLam a : ℂ) * u) (by
          rw [Metric.mem_ball, dist_eq_norm, sub_zero]
          have hnorm : ‖(eqLam a : ℂ) * u‖ = eqLam a * ‖u‖ := by
            rw [norm_mul]
            have h2 : ‖(eqLam a : ℂ)‖ = eqLam a := by simp [Real.norm_eq_abs, abs_of_pos hl0]
            rw [h2]
          rw [hnorm]
          exact mul_lt_mul_of_pos_left hu_lt hl0)
        simp only [GermFE] at h1
        rw [show ((eqLam a : ℂ) * u) / (eqLam a : ℂ) = u by
          rw [mul_div_cancel_left₀ _ (by exact_mod_cast (ne_of_gt hl0))]] at h1
        exact h1
      set E : ℂ := (a : ℂ) * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 ((eqLam a : ℂ) * u) /
          dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 ((eqLam a : ℂ) * u) with hEdef
      set S : ℂ := (1 + h ((eqLam a : ℂ) * u) ^ 2) ^ (1 / 2 : ℂ) with hSdef
      set R : ℂ := (-E) * S with hRdef
      have hS' : S ^ 2 = 1 + h ((eqLam a : ℂ) * u) ^ 2 := by
        rw [hSdef]; exact cpow_half_sq _
      have hEval : E = (a : ℂ) * h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) /
          (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u)) := by
        have h1 : ((eqLam a : ℂ) * u) * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0
            ((eqLam a : ℂ) * u) = h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) :=
          mul_dslope_eq (f := fun v : ℂ => h ((eqLam a : ℂ) * v)) (v := (eqLam a : ℂ) * u)
            (by rw [mul_zero, h0])
        have h2 : ((eqLam a : ℂ) * u) * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0
            ((eqLam a : ℂ) * u)
            = h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u) :=
          mul_dslope_eq (f := fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) (v := (eqLam a : ℂ) * u)
            (by rw [mul_zero, h0]; ring)
        have hDA2ne : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 ((eqLam a : ℂ) * u)
            ≠ 0 := hρ₁ne _ hlu_ball₁
        refine (eq_div_iff hCB).mpr ?_
        rw [hEdef, ← h2, ← h1]
        field_simp
      have hu_ball2 : u ∈ Metric.ball (0 : ℂ) ρ₂ := Metric.ball_subset_ball hρ₀le₂ hu_ball0
      have hu_ball3 : u ∈ Metric.ball (0 : ℂ) ρ₃ := Metric.ball_subset_ball hρ₀le₃ hu_ball0
      have hu_ball4 : u ∈ Metric.ball (0 : ℂ) ρ₄ := Metric.ball_subset_ball hρ₀le₄ hu_ball0
      have hRe : 0 < R.re := by
        rw [hRdef]
        have hFu : 0 < F u := hρ₄ u hu_ball4
        have hFeq : F u = ((-E) * S).re := by rw [hFdef]
        rw [← hFeq]
        exact hFu
      have hstep := germC_step_algebra (a := a) (A := h u) (B := h ((eqLam a : ℂ) * u))
        (C := h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u))) (E := E) (S := S) (R := R)
        hBA hCB hFE' hS' hEval hRdef hRe
      have hP : germC a h u =
          ((a : ℂ) * h ((eqLam a : ℂ) * u) / (h ((eqLam a : ℂ) * u) - h u) - ((a / 2 : ℝ) : ℂ),
            h u * ((a : ℂ) * h ((eqLam a : ℂ) * u) / (h ((eqLam a : ℂ) * u) - h u))) := by
        rw [germC_apply_ne h0 hu0]
        refine Prod.ext ?_ ?_ <;> ring
      have hQ : germC a h ((eqLam a : ℂ) * u) = (E - ((a / 2 : ℝ) : ℂ), h ((eqLam a : ℂ) * u) * E) := by
        rw [germC_apply_ne h0 hlu_ne]
        refine Prod.ext ?_ ?_
        · rw [hEval]
        · rw [hEval]; ring
      rw [hP, hQ]
      exact ⟨⟨hstep.1, by rw [← hP]; exact hρ₂ u hu_ball2,
        by rw [← hQ]; exact hρ₃ u hu_ball3⟩, hstep.2⟩
  · exact hinj.mono (Metric.ball_subset_ball hρleε)


end

end Work.EQ
