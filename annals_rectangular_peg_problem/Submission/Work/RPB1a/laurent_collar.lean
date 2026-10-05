import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.Helpers
import Submission.Work.RPB1a.laurentPoly_exp
import Submission.Work.RPB1a.laurentPoly_differentiableOn
import Submission.Work.RPB1a.injOn_laurentPoly_sphere
import Submission.Work.RPB1a.deriv_laurentPoly_ne_zero_on_sphere
import Submission.Work.RPB1a.exists_nhds_injOn_of_analyticAt

/-!
# RPB1a: the Laurent collar (node `N3` of the conformal-map route)

Let `v = trigPoly N a` be a smooth `2π`-periodic embedded immersed loop in `ℂ` and let
`Γ = laurentPoly N a` be its Laurent form, so that `Γ (e^{it}) = v t` (`laurentPoly_exp`).  This
file proves that `Γ` is injective with nonvanishing derivative on a thin inversion-symmetric annulus
`annulus ρ = {ρ < ‖w‖ < ρ⁻¹}`, the collar of the unit circle: node `N3` of
`RECTPEG_B1_LEAD.md` §3.

The two inputs coming from the circle are

* `injOn_laurentPoly_sphere` — `Γ` is injective on `{‖w‖ = 1}` (transport of
  injectivity-mod-`2π` of `v` across `w = e^{it}`);
* `deriv_laurentPoly_ne_zero_on_sphere` — `Γ'(z) ≠ 0` on `{‖w‖ = 1}` (chain rule through
  `t ↦ e^{it}`, using `deriv v t ≠ 0`),

and the two inputs coming from the local theory of holomorphic functions are

* `analyticAt_laurentPoly` with `exists_nhds_injOn_of_analyticAt` — `Γ` is locally injective at
  every point of the circle (inverse function theorem at a point with `Γ' ≠ 0`);
* `continuousAt_deriv_laurentPoly` — `Γ'` is continuous there.

The compactness step `exists_annulus_injOn_deriv_ne_zero` then bootstraps local statements at the
circle to the collar, exactly as in `RECTPEG_B1_LEAD.md` §4 (`N3`): if no thin annulus worked, one
would find obstructions in `annulus (1 - 1/(k+2))`, whose norms tend to `1`; compactness of a closed
ball extracts a convergent subsequence, the limit lies on the circle and is an obstruction there —
by continuity of `Γ` and `Γ'`, and for injectivity by local injectivity at the (equal) limits.
-/

namespace Work.RPB1a

open Complex Set Metric Filter
open scoped ContDiff Real Topology
open Work.RPB1a

set_option autoImplicit false

noncomputable section

/-! ## Elementary metric facts about the annuli `annulus ρ` -/

/-- The annuli are nested: a larger `ρ` gives a smaller annulus. -/
theorem annulus_mono {ρ ρ' : ℝ} (h0 : 0 < ρ) (h : ρ ≤ ρ') : annulus ρ' ⊆ annulus ρ := by
  intro w hw
  obtain ⟨h1, h2⟩ := hw
  exact ⟨lt_of_le_of_lt h h1, lt_of_lt_of_le h2 (inv_anti₀ h0 h)⟩

/-- Points of `annulus ρ` have norm within `max (1 - ρ) (ρ⁻¹ - 1)` of `1`. -/
theorem abs_norm_sub_one_lt_max_of_mem_annulus {ρ : ℝ} {w : ℂ} (hw : w ∈ annulus ρ) :
    |‖w‖ - 1| < max (1 - ρ) (ρ⁻¹ - 1) := by
  obtain ⟨h1, h2⟩ := hw
  refine abs_lt.mpr ⟨?_, ?_⟩
  · have : 1 - ‖w‖ < max (1 - ρ) (ρ⁻¹ - 1) :=
      lt_of_lt_of_le (by linarith) (le_max_left _ _)
    linarith
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

/-- If `x k ∈ annulus (ρ k)` and `ρ k → 1`, then `‖x k‖ → 1`. -/
theorem tendsto_norm_of_mem_annulus {ρ : ℕ → ℝ} {x : ℕ → ℂ}
    (hρ : Tendsto ρ atTop (nhds 1)) (hx : ∀ k, x k ∈ annulus (ρ k)) :
    Tendsto (fun k => ‖x k‖) atTop (nhds 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hm : Tendsto (fun k => max (1 - ρ k) ((ρ k)⁻¹ - 1)) atTop (nhds 0) := by
    have h1 : Tendsto (fun k => 1 - ρ k) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hρ
    have h2 : Tendsto (fun k => (ρ k)⁻¹ - 1) atTop (nhds 0) := by
      have hinv : Tendsto (fun k => (ρ k)⁻¹) atTop (nhds (1 : ℝ)) := by
        simpa using hρ.inv₀ (one_ne_zero)
      simpa using hinv.sub (tendsto_const_nhds (x := (1 : ℝ)))
    simpa using h1.max h2
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hm
  rw [Real.norm_eq_abs]
  exact le_of_lt (abs_norm_sub_one_lt_max_of_mem_annulus (hx k))

/-- A point of the unit sphere of `ℂ` is nonzero. -/
theorem sphere_ne_zero {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : z ≠ 0 := by
  rintro rfl
  simp at hz

/-! ## Analyticity and continuity of a Laurent polynomial off the origin -/

/-- A Laurent polynomial is continuous at every nonzero point. -/
theorem continuousAt_laurentPoly (N : ℕ) (a : ℤ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    ContinuousAt (laurentPoly N a) w :=
  (hasDerivAt_laurentPoly N a hw).continuousAt

/-- The derivative of a Laurent polynomial is continuous at every nonzero point. -/
theorem continuousAt_deriv_laurentPoly (N : ℕ) (a : ℤ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    ContinuousAt (deriv (laurentPoly N a)) w := by
  have hcont : ContinuousAt
      (fun y : ℂ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, a n * (n : ℂ) * y ^ (n - 1)) w :=
    tendsto_finsetSum _ fun n _ =>
      (continuousAt_zpow₀ w (n - 1) (Or.inl hw)).const_mul (a n * (n : ℂ))
  refine hcont.congr ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hw)] with y hy
  exact (deriv_laurentPoly N a (by simpa using hy)).symm

/-- A Laurent polynomial is analytic at every nonzero point. -/
theorem analyticAt_laurentPoly (N : ℕ) (a : ℤ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    AnalyticAt ℂ (laurentPoly N a) w :=
  ((laurentPoly_differentiableOn N a).analyticOn isOpen_compl_singleton).analyticAt
    (isOpen_compl_singleton.mem_nhds (by simpa using hw))

/-! ## The compactness core -/

/-- **Collar lemma, compactness core.**  A continuous map `F : ℂ → ℂ` that is injective on the unit
circle, locally injective near it, with continuous nonvanishing derivative on the circle, is
injective with nonvanishing derivative on a thin inversion-symmetric annulus.

Both conclusions are proved separately by contradiction.  If no `ρ < 1` works, one finds
obstructions in `annulus (1 - 1/(k+2))`, whose norms tend to `1`; compactness of a closed ball
extracts a convergent subsequence, whose limit lies on the circle and is an obstruction there, by
continuity — and, for injectivity, by equality of the two limits together with local injectivity. -/
theorem exists_annulus_injOn_deriv_ne_zero {F : ℂ → ℂ}
    (hcont : ∀ z ∈ sphere (0 : ℂ) 1, ContinuousAt F z)
    (hinj : Set.InjOn F (sphere (0 : ℂ) 1))
    (hloc : ∀ z ∈ sphere (0 : ℂ) 1, ∃ U ∈ nhds z, Set.InjOn F U)
    (hdc : ∀ z ∈ sphere (0 : ℂ) 1, ContinuousAt (deriv F) z)
    (hdz : ∀ z ∈ sphere (0 : ℂ) 1, deriv F z ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ Set.InjOn F (annulus ρ) ∧
      ∀ w ∈ annulus ρ, deriv F w ≠ 0 := by
  -- the sequence of radii tending to `1` from below
  set r : ℕ → ℝ := fun k => 1 - 1 / ((k : ℝ) + 2) with hrdef
  have hr_pos : ∀ k, 0 < r k := by
    intro k
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hlt : 1 / ((k : ℝ) + 2) < 1 := by
      rw [div_lt_one hk2]
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [hrdef]
    linarith
  have hr_lt_one : ∀ k, r k < 1 := by
    intro k
    have hpos : 0 < 1 / ((k : ℝ) + 2) := by positivity
    rw [hrdef]
    linarith
  have hr_tend : Tendsto r atTop (nhds 1) := by
    have hdiv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (nhds 0) := by
      have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have hcomp : Tendsto (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) + 1)) atTop (nhds 0) :=
        h.comp (tendsto_add_atTop_nat 1)
      have hfun : (fun k : ℕ => 1 / ((k : ℝ) + 2)) =
          fun k => 1 / (((k + 1 : ℕ) : ℝ) + 1) := by
        funext k; push_cast; ring
      rwa [hfun]
    rw [hrdef]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hdiv
  -- the derivative is nonvanishing on a thin annulus
  have hderiv : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ w ∈ annulus ρ, deriv F w ≠ 0 := by
    by_contra hc
    push Not at hc
    choose x hx hxz using fun k => hc (r k) (hr_pos k) (hr_lt_one k)
    have hnorm : Tendsto (fun k => ‖x k‖) atTop (nhds 1) := tendsto_norm_of_mem_annulus hr_tend hx
    have hbdd : ∀ᶠ k in atTop, ‖x k‖ ≤ 2 :=
      hnorm.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2))
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hbdd
    obtain ⟨z, _, φ, hφmono, hφtend⟩ :=
      (isCompact_closedBall (0 : ℂ) 2).tendsto_subseq (x := fun j => x (j + k₀))
        (fun j => mem_closedBall.mpr (by simpa using hk₀ (j + k₀) (Nat.le_add_left k₀ j)))
    have hnorm' : Tendsto (fun j => ‖x (j + k₀)‖) atTop (nhds 1) :=
      hnorm.comp (tendsto_add_atTop_nat k₀)
    have hz1 : ‖z‖ = 1 :=
      (tendsto_nhds_unique (hnorm'.comp hφmono.tendsto_atTop) hφtend.norm).symm
    have hzS : z ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere, dist_zero_right]
      exact hz1
    have hz0 : deriv F z = 0 := by
      have h1 : Tendsto (fun j => deriv F (x (φ j + k₀))) atTop (nhds (deriv F z)) :=
        ((hdc z hzS).tendsto).comp hφtend
      have h2 : Tendsto (fun j => deriv F (x (φ j + k₀))) atTop (nhds 0) := by
        have hfun : (fun j => deriv F (x (φ j + k₀))) = fun _ => 0 := by
          funext j; exact hxz (φ j + k₀)
        rw [hfun]; exact tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    exact hdz z hzS hz0
  -- injectivity on a thin annulus
  have hinjA : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ Set.InjOn F (annulus ρ) := by
    by_contra hc
    have hbad : ∀ ρ, 0 < ρ → ρ < 1 → ∃ p : ℂ × ℂ, p.1 ∈ annulus ρ ∧ p.2 ∈ annulus ρ ∧
        F p.1 = F p.2 ∧ p.1 ≠ p.2 := by
      intro ρ h0 h1
      by_contra h
      refine hc ⟨ρ, h0, h1, ?_⟩
      intro a ha b hb hab
      by_contra hne
      exact h ⟨(a, b), ha, hb, hab, hne⟩
    choose u hu using fun k => hbad (r k) (hr_pos k) (hr_lt_one k)
    have hnorm1 : Tendsto (fun k => ‖(u k).1‖) atTop (nhds 1) :=
      tendsto_norm_of_mem_annulus hr_tend fun k => (hu k).1
    have hnorm2 : Tendsto (fun k => ‖(u k).2‖) atTop (nhds 1) :=
      tendsto_norm_of_mem_annulus hr_tend fun k => (hu k).2.1
    have hbdd : ∀ᶠ k in atTop, u k ∈ closedBall (0 : ℂ) 2 ×ˢ closedBall (0 : ℂ) 2 := by
      filter_upwards [hnorm1.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2)),
        hnorm2.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2))] with k h1 h2
      exact ⟨mem_closedBall.mpr (by simpa using h1), mem_closedBall.mpr (by simpa using h2)⟩
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hbdd
    obtain ⟨p, _, φ, hφmono, hφtend⟩ :=
      ((isCompact_closedBall (0 : ℂ) 2).prod (isCompact_closedBall (0 : ℂ) 2)).tendsto_subseq
        (x := fun j => u (j + k₀)) (fun j => hk₀ (j + k₀) (Nat.le_add_left k₀ j))
    have hφ1 : Tendsto (fun j => (u (φ j + k₀)).1) atTop (nhds p.1) := by
      have h := hφtend
      rw [nhds_prod_eq] at h
      exact h.fst
    have hφ2 : Tendsto (fun j => (u (φ j + k₀)).2) atTop (nhds p.2) := by
      have h := hφtend
      rw [nhds_prod_eq] at h
      exact h.snd
    have hp1S : p.1 ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere, dist_zero_right]
      exact (tendsto_nhds_unique
        ((hnorm1.comp (tendsto_add_atTop_nat k₀)).comp hφmono.tendsto_atTop) hφ1.norm).symm
    have hp2S : p.2 ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere, dist_zero_right]
      exact (tendsto_nhds_unique
        ((hnorm2.comp (tendsto_add_atTop_nat k₀)).comp hφmono.tendsto_atTop) hφ2.norm).symm
    have hFeq : F p.1 = F p.2 := by
      have h1 : Tendsto (fun j => F (u (φ j + k₀)).1) atTop (nhds (F p.1)) :=
        ((hcont p.1 hp1S).tendsto).comp hφ1
      have h2 : Tendsto (fun j => F (u (φ j + k₀)).2) atTop (nhds (F p.2)) :=
        ((hcont p.2 hp2S).tendsto).comp hφ2
      have h12 : (fun j => F (u (φ j + k₀)).1) = fun j => F (u (φ j + k₀)).2 := by
        funext j; exact (hu (φ j + k₀)).2.2.1
      rw [h12] at h1
      exact tendsto_nhds_unique h1 h2
    have hpeq : p.1 = p.2 := hinj hp1S hp2S hFeq
    obtain ⟨U, hU, hUinj⟩ := hloc p.1 hp1S
    have hU' : U ∈ nhds p.2 := hpeq ▸ hU
    have hev1 : ∀ᶠ j in atTop, (u (φ j + k₀)).1 ∈ U := hφ1.eventually hU
    have hev2 : ∀ᶠ j in atTop, (u (φ j + k₀)).2 ∈ U := hφ2.eventually hU'
    obtain ⟨j, hj1, hj2⟩ := (hev1.and hev2).exists
    exact (hu (φ j + k₀)).2.2.2 (hUinj hj1 hj2 (hu (φ j + k₀)).2.2.1)
  obtain ⟨ρd, hρd0, hρd1, hρdz⟩ := hderiv
  obtain ⟨ρi, hρi0, hρi1, hρiinj⟩ := hinjA
  refine ⟨max ρd ρi, lt_of_lt_of_le hρd0 (le_max_left _ _), max_lt hρd1 hρi1, ?_, ?_⟩
  · exact hρiinj.mono (annulus_mono hρi0 (le_max_right _ _))
  · intro w hw
    exact hρdz w (annulus_mono hρd0 (le_max_left _ _) hw)

/-! ## The Laurent collar -/

theorem laurent_collar (N : ℕ) (a : ℤ → ℂ) (hv : IsSmoothLoop (trigPoly N a)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ Set.InjOn (laurentPoly N a) (annulus ρ) ∧
      ∀ w ∈ annulus ρ, deriv (laurentPoly N a) w ≠ 0 := by
  refine exists_annulus_injOn_deriv_ne_zero (F := laurentPoly N a) ?_ ?_ ?_ ?_ ?_
  · -- `Γ` is continuous at the circle
    intro z hz
    exact continuousAt_laurentPoly N a (sphere_ne_zero hz)
  · -- `Γ` is injective on the circle
    exact injOn_laurentPoly_sphere N a hv
  · -- `Γ` is locally injective at the circle (inverse function theorem)
    intro z hz
    exact exists_nhds_injOn_of_analyticAt (analyticAt_laurentPoly N a (sphere_ne_zero hz))
      (deriv_laurentPoly_ne_zero_on_sphere N a hv z hz)
  · -- `Γ'` is continuous at the circle
    intro z hz
    exact continuousAt_deriv_laurentPoly N a (sphere_ne_zero hz)
  · -- `Γ' ≠ 0` on the circle
    exact deriv_laurentPoly_ne_zero_on_sphere N a hv

end

end Work.RPB1a
