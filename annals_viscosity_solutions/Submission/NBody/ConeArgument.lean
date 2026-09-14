import Submission.NBody.ChazyContinuity
import Submission.NBody.MinimizerEndpoint
import Submission.NBody.Identification

/-!
# The cone argument: the limit shape is parallel to the direction `a`

This file contains the last ingredient of the variational chapter: the proof that the limit shape
`b` of the calibrating curve `γ` is *parallel* to the prescribed collision-free direction `a`
(`b = c • a` for some real `c`).  The idea (Maderna--Venturelli §4.3, step 3) is:

* the `h`-minimisers `γ_k` from `γ 1` to `λ_k • a` have initial data tending to that of `γ`
  (position `γ 1` exactly, velocity `→ (deriv γ) 1`);
* Chazy's continuity of the limit shape then puts the terminal shape `τ_k⁻¹ • γ_k(τ_k) =
  (λ_k/τ_k) • a` within `ε` of a configuration `b_k` with `dist b_k b < ε`;
* hence `‖(λ_k/τ_k) • a - b‖ ≤ 2ε` along a sequence `k → ∞` with `ε → 0`, and since `a ≠ 0` this
  forces `b ∈ ℝ a`.

The technical difficulty (resolved here) is that the minimisers are only solutions of the state
equation on the *half-open* interval `(0, τ_k]`:  at the left endpoint the velocity is only a
one-sided derivative and at the right endpoint the state is not known to be differentiable.  This
is handled by
* `exists_tendsto_deriv_left_of_isHMinimizer` (the velocity has a left limit at the right endpoint,
  by applying the left-endpoint result to the time-reversed minimiser),
* `exists_minimizerState` (the state of the minimiser, corrected at both endpoints, solves the state
  equation on the closed interval `[0, τ_k]`),
* `chazy_continuity_Ioc` (Chazy's continuity for curves whose equation is only known on `(0,S]`,
  where the comparison with the reference solution is performed on `[θ,t₁]` for a small `θ > 0`).
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 3200000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}
variable [Nontrivial E]

namespace Submission.NBody



theorem exists_tendsto_deriv_left_of_isHMinimizer {m : Fin N → ℝ} {h τ : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hτ : 0 < τ)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hnc : ∀ t ∈ Set.Icc 0 τ, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ 0 τ)
    (hfin : actionPot m h (γ 0) (γ τ) < ⊤) :
    ∃ L : EN E N, Tendsto (deriv γ) (𝓝[<] τ) (𝓝 L) := by
  have hmin' : actionOn m h γ 0 τ = actionPot m h (γ 0) (γ τ) := hmin
  set γr : ℝ → EN E N := fun s => γ (τ - s) with hγrdef
  have hacr : AbsolutelyContinuousOnInterval γr 0 τ := by
    rw [hγrdef]; exact absolutelyContinuousOnInterval_comp_rev hac
  have hncr : ∀ t ∈ Set.Icc 0 τ, WithoutCollisions (γr t) := by
    intro t ht
    rw [hγrdef]
    exact hnc (τ - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have honr : actionOn m h γr 0 τ = actionOn m h γ 0 τ := by
    rw [hγrdef]; exact actionOn_comp_rev
  have hminr : IsHMinimizer m h γr 0 τ := by
    show actionOn m h γr 0 τ = actionPot m h (γr 0) (γr τ)
    rw [honr, hmin', show γr 0 = γ τ from by rw [hγrdef]; simp,
      show γr τ = γ 0 from by rw [hγrdef]; simp, actionPot_comm]
  have hfinr : actionPot m h (γr 0) (γr τ) < ⊤ := by
    have h1 : actionPot m h (γr 0) (γr τ) = actionOn m h γr 0 τ := hminr.symm
    rw [h1, honr, hmin']
    exact hfin
  obtain ⟨v, hv, -⟩ := minimizer_deriv_tendsto_left hm hh hτ hacr hncr hminr hfinr
  refine ⟨-v, ?_⟩
  have hg : Tendsto (fun s : ℝ => deriv γ (τ - s)) (𝓝[>] (0:ℝ)) (𝓝 (-v)) := by
    have h1 : deriv γr = fun s : ℝ => -deriv γ (τ - s) := by
      funext s
      rw [hγrdef, deriv_comp_const_sub]
    rw [h1] at hv
    simpa using hv.neg
  have hmap : Tendsto (fun u : ℝ => τ - u) (𝓝[<] τ) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := (tendsto_const_nhds (x := τ) (f := 𝓝[<] τ)).sub
        (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (α := ℝ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact sub_pos.mpr (show u < τ from hu)
  have hcomp := hg.comp hmap
  have hfun : (fun s : ℝ => deriv γ (τ - s)) ∘ (fun u : ℝ => τ - u) = deriv γ := by
    funext u
    simp only [Function.comp_apply]
    rw [show τ - (τ - u) = u by ring]
  rwa [hfun] at hcomp

/-- The state of an `h`-minimiser, made two-sided at both ends (initial velocity at `0`, the limit
of the velocity at the right endpoint `τ`), satisfies the state equation on the closed interval and
is continuous there. -/
theorem exists_minimizerState {m : Fin N → ℝ} {h τ : ℝ} {γ : ℝ → EN E N} {v : EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hτ : 0 < τ)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hnc : ∀ t ∈ Set.Icc 0 τ, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ 0 τ) (hfin : actionPot m h (γ 0) (γ τ) < ⊤)
    (hv : Tendsto (deriv γ) (𝓝[>] (0 : ℝ)) (𝓝 v)) :
    ∃ (L : EN E N) (W : ℝ → EN E N × EN E N), W 0 = (γ 0, v) ∧ W τ = (γ τ, L) ∧
      (∀ t ∈ Set.Ioc (0 : ℝ) τ, HasDerivAt W (stateField m (W t)) t) ∧
      Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 (W 0)) ∧
      Tendsto (deriv γ) (𝓝[<] τ) (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_deriv_left_of_isHMinimizer hm hh hτ hac hnc hmin hfin
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) τ,
      HasDerivAt (fun s => (γ s, deriv γ s)) (stateField m (γ t, deriv γ t)) t :=
    minimizer_hasDerivAt_state hm hh hτ hac hnc hmin hfin
  have hfst : ∀ t ∈ Set.Ioo (0 : ℝ) τ, HasDerivAt (fun s => γ s) (deriv γ t) t := by
    intro t ht
    have h := (ContinuousLinearMap.fst ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt t
      (hderiv t ht)
    simpa [stateField, Function.comp_def] using h
  have hsnd : ∀ t ∈ Set.Ioo (0 : ℝ) τ, HasDerivAt (fun s => deriv γ s)
      (weightedGrad m (U m) (γ t)) t := by
    intro t ht
    have h := (ContinuousLinearMap.snd ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt t
      (hderiv t ht)
    simpa [stateField, Function.comp_def] using h
  have hγcont : ContinuousOn γ (Set.Icc 0 τ) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hτ.le] at h
  set W : ℝ → EN E N × EN E N := fun t =>
    if t = 0 then (γ 0, v) else if t < τ then (γ t, deriv γ t)
      else (γ τ, L) + (t - τ) • stateField m (γ τ, L) with hWdef
  have hW0 : W 0 = (γ 0, v) := by simp [hWdef]
  have hWτ : W τ = (γ τ, L) := by
    have h : W τ = (γ τ, L) + (τ - τ) • stateField m (γ τ, L) := by
      simp only [hWdef]; rw [if_neg (ne_of_gt hτ), if_neg (lt_irrefl τ)]
    rw [h, sub_self, zero_smul, add_zero]
  have hWeq : ∀ t ∈ Set.Ioo (0 : ℝ) τ, W t = (γ t, deriv γ t) := by
    intro t ht
    simp only [hWdef]; rw [if_neg (ne_of_gt ht.1), if_pos ht.2]
  -- the linear right branch
  set wl : ℝ → EN E N × EN E N :=
    fun t => (γ τ, L) + (t - τ) • stateField m (γ τ, L) with hwldef
  have hlin : ∀ x : ℝ, HasDerivAt wl (stateField m (γ τ, L)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => t - τ) (1 : ℝ) x := (hasDerivAt_id x).sub_const τ
    have h2 : HasDerivAt (fun t : ℝ => (t - τ) • stateField m (γ τ, L))
        ((1 : ℝ) • stateField m (γ τ, L)) x := h1.smul_const _
    have h3 := h2.const_add ((γ τ, L) : EN E N × EN E N)
    simpa [hwldef] using h3
  have hwlfst : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (wl t).1) L x := by
    intro x
    have h := (ContinuousLinearMap.fst ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt x (hlin x)
    simpa [stateField, Function.comp_def] using h
  have hwlsnd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (wl t).2)
      (weightedGrad m (U m) (γ τ)) x := by
    intro x
    have h := (ContinuousLinearMap.snd ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt x (hlin x)
    simpa [stateField, Function.comp_def] using h
  -- the left-limit set-up
  have hmem : Set.Ioo (0 : ℝ) τ ∈ 𝓝[Set.Iio τ] τ :=
    (mem_nhdsWithin_iff_exists_mem_nhds_inter (s := Set.Iio τ) (a := τ)
      (t := Set.Ioo (0 : ℝ) τ)).mpr ⟨Set.Ioi (0 : ℝ), Ioi_mem_nhds hτ, fun x hx => hx⟩
  have hmemIcc0 : Set.Icc (0 : ℝ) τ ∈ 𝓝[>] (0 : ℝ) :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hτ) (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  have hmemIcc : Set.Icc (0 : ℝ) τ ∈ 𝓝[Set.Iio τ] τ :=
    Filter.mem_of_superset hmem (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  have hmemIoo : Set.Iio τ ∈ 𝓝[Set.Ioo (0 : ℝ) τ] τ := by
    refine Filter.mem_of_superset (self_mem_nhdsWithin : Set.Ioo (0:ℝ) τ ∈ 𝓝[Set.Ioo (0:ℝ) τ] τ) ?_
    exact fun x hx => hx.2
  -- differentiability of the two components on `(0,τ)`
  have hWfst_diff : DifferentiableOn ℝ (fun s => (W s).1) (Set.Ioo (0 : ℝ) τ) := by
    intro x hx
    have hev : (fun s => (W s).1) =ᶠ[𝓝 x] fun s => γ s := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
      rw [hWeq s hs]
    exact ((hfst x hx).congr_of_eventuallyEq hev).differentiableAt.differentiableWithinAt
  have hWsnd_diff : DifferentiableOn ℝ (fun s => (W s).2) (Set.Ioo (0 : ℝ) τ) := by
    intro x hx
    have hev : (fun s => (W s).2) =ᶠ[𝓝 x] fun s => deriv γ s := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
      rw [hWeq s hs]
    exact ((hsnd x hx).congr_of_eventuallyEq hev).differentiableAt.differentiableWithinAt
  -- continuity of the two components within `(0,τ)` at `τ`
  have hγleft : Tendsto γ (𝓝[<] τ) (𝓝 (γ τ)) :=
    ((hγcont.continuousWithinAt ⟨hτ.le, le_rfl⟩).mono_of_mem_nhdsWithin hmemIcc).tendsto
  have hgradleft : Tendsto (fun s => weightedGrad m (U m) (γ s)) (𝓝[<] τ)
      (𝓝 (weightedGrad m (U m) (γ τ))) := by
    have h1 : ContinuousOn (fun s => weightedGrad m (U m) (γ s)) (Set.Icc 0 τ) :=
      continuousOn_weightedGrad_comp (continuousOn_fderiv_U_comp (m := m) hγcont hnc)
    exact ((h1.continuousWithinAt ⟨hτ.le, le_rfl⟩).mono_of_mem_nhdsWithin hmemIcc).tendsto
  have hWfst_cont : ContinuousWithinAt (fun s => (W s).1) (Set.Ioo (0 : ℝ) τ) τ := by
    have h1 : Tendsto (fun s => (W s).1) (𝓝[Set.Ioo (0 : ℝ) τ] τ) (𝓝 (γ τ)) := by
      have h2 : Tendsto (fun s => γ s) (𝓝[Set.Ioo (0 : ℝ) τ] τ) (𝓝 (γ τ)) :=
        hγleft.mono_left (nhdsWithin_mono τ (fun x hx => hx.2))
      exact h2.congr' (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [hWeq s hs])
    rw [ContinuousWithinAt, hWτ]
    exact h1
  have hWsnd_cont : ContinuousWithinAt (fun s => (W s).2) (Set.Ioo (0 : ℝ) τ) τ := by
    have h1 : Tendsto (fun s => (W s).2) (𝓝[Set.Ioo (0 : ℝ) τ] τ) (𝓝 L) := by
      have h2 : Tendsto (fun s => deriv γ s) (𝓝[Set.Ioo (0 : ℝ) τ] τ) (𝓝 L) :=
        hL.mono_left (nhdsWithin_mono τ (fun x hx => hx.2))
      exact h2.congr' (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [hWeq s hs])
    rw [ContinuousWithinAt, hWτ]
    exact h1
  -- the derivatives tend to the right limits
  have hWfst_tend : Tendsto (fun x => deriv (fun s => (W s).1) x) (𝓝[<] τ) (𝓝 L) := by
    refine hL.congr' ?_
    filter_upwards [hmem] with x hx
    exact Filter.EventuallyEq.deriv_eq (by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
      rw [hWeq s hs])
  have hWsnd_tend : Tendsto (fun x => deriv (fun s => (W s).2) x) (𝓝[<] τ)
      (𝓝 (weightedGrad m (U m) (γ τ))) := by
    refine hgradleft.congr' ?_
    filter_upwards [hmem] with x hx
    have h3 : (fun s => (W s).2) =ᶠ[𝓝 x] fun s => deriv γ s := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
      rw [hWeq s hs]
    exact ((Filter.EventuallyEq.deriv_eq h3).trans (hsnd x hx).deriv).symm
  have hleft : HasDerivWithinAt W (stateField m (W τ)) (Set.Iic τ) τ := by
    have h1 : HasDerivWithinAt (fun s => (W s).1) L (Set.Iic τ) τ :=
      hasDerivWithinAt_Iic_of_tendsto_deriv hWfst_diff hWfst_cont hmem hWfst_tend
    have h2 : HasDerivWithinAt (fun s => (W s).2) (weightedGrad m (U m) (γ τ)) (Set.Iic τ) τ :=
      hasDerivWithinAt_Iic_of_tendsto_deriv hWsnd_diff hWsnd_cont hmem hWsnd_tend
    have h3 := h1.prodMk h2
    rw [hWτ, stateField]
    simpa using h3
  have hright : HasDerivWithinAt W (stateField m (W τ)) (Set.Ici τ) τ := by
    have h1 : HasDerivAt wl (stateField m (γ τ, L)) τ := hlin τ
    rw [show stateField m (γ τ, L) = stateField m (W τ) from by rw [hWτ]] at h1
    refine h1.hasDerivWithinAt.congr ?_ ?_
    · intro t ht
      simp only [hWdef, hwldef]
      rw [if_neg (ne_of_gt (lt_of_lt_of_le hτ ht)), if_neg (not_lt.mpr ht)]
    · rw [hWτ]
      simp [hwldef]
  have hτderiv : HasDerivAt W (stateField m (W τ)) τ := by
    have h := hleft.union hright
    rw [Iic_union_Ici] at h
    exact h.hasDerivAt univ_mem
  refine ⟨L, W, hW0, hWτ, ?_, ?_, hL⟩
  · intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · have hev : W =ᶠ[𝓝 t] (fun s => (γ s, deriv γ s)) := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨ht.1, hlt⟩] with s hs
        exact hWeq s hs
      have h1 := (hderiv t ⟨ht.1, hlt⟩).congr_of_eventuallyEq hev
      have h2 : W t = (γ t, deriv γ t) := hev.eq_of_nhds
      rw [h2]
      exact h1
    · subst heq
      exact hτderiv
  · have hγ0 : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 (γ 0)) :=
      (hγcont.continuousWithinAt ⟨le_rfl, hτ.le⟩).mono_left
        (nhdsWithin_le_iff.mpr hmemIcc0)
    have h1 : Tendsto (fun s : ℝ => (γ s, deriv γ s)) (𝓝[>] (0 : ℝ)) (𝓝 (γ 0, v)) :=
      (Prod.tendsto_iff (fun s : ℝ => (γ s, deriv γ s)) (γ 0, v)).mpr ⟨hγ0, hv⟩
    have hev : (fun s : ℝ => (γ s, deriv γ s)) =ᶠ[𝓝[>] (0 : ℝ)] W := by
      filter_upwards [Ioo_mem_nhdsGT hτ] with s hs
      exact (hWeq s hs).symm
    have h2 := h1.congr' hev
    rw [hW0]
    exact h2






/-- **Chazy's continuity of the limit shape, for curves whose equation is only known on `(0,S]`.**
Version of `chazy_continuity` in which the perturbed curve `w` is only assumed to solve the state
equation on `Set.Ioc 0 S` (instead of the closed interval `Set.Icc 0 S`) and to be continuous from
the right at `0`; the comparison with the reference motion is then performed on `[θ, t₁]` for a
small `θ > 0`, where both curves are genuine two-sided solutions. -/
theorem chazy_continuity_Ioc {m : Fin N → ℝ} {a : EN E N} (ha : WithoutCollisions a)
    {z : ℝ → EN E N × EN E N}
    (hnc : ∀ t : ℝ, 0 ≤ t → WithoutCollisions (z t).1)
    (hz : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt z (stateField m (z t)) t)
    (hasym : Tendsto (fun t : ℝ => t⁻¹ • (z t).1) atTop (𝓝 a))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (w : ℝ → EN E N × EN E N) (S : ℝ), t₁ ≤ S →
        (∀ t ∈ Set.Ioc (0 : ℝ) S, HasDerivAt w (stateField m (w t)) t) →
        Tendsto w (𝓝[>] (0 : ℝ)) (𝓝 (w 0)) →
        dist (w 0) (z 0) < δ →
        (∀ t ∈ Set.Icc t₁ S, dist (w t).1 (t • a) < t * ε ∧ dist (w t).2 a < 2 * ε / 3) ∧
        ∃ b : EN E N, dist b a < ε ∧ ∃ t₂ : ℝ, t₁ ≤ t₂ ∧
          ∀ t ∈ Set.Icc t₂ S, dist (t⁻¹ • (w t).1) b < ε := by
  classical
  classical
  -- the geometry of the ball around `a`
  obtain ⟨ρnc, hρnc, hncball⟩ := exists_ball_withoutCollisions (E := E) (N := N) ha
  obtain ⟨ρK, hρK, K, hKbound⟩ := exists_bound_weightedGrad (m := m) ha
  set ρ : ℝ := min ε (min ρnc ρK) with hρdef
  have hρ : 0 < ρ := lt_min hε (lt_min hρnc hρK)
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρnc' : ρ ≤ ρnc := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρK' : ρ ≤ ρK := le_trans (min_le_right _ _) (min_le_right _ _)
  have hncρ : ∀ y : EN E N, dist y a ≤ ρ → WithoutCollisions y := fun y hy =>
    hncball y (le_trans hy hρnc')
  have hbρ : ∀ y : EN E N, dist y a ≤ ρ → ‖weightedGrad m (U m) y‖ ≤ K := fun y hy =>
    hKbound y (le_trans hy hρK')
  -- the asymptotic behaviour of the reference motion
  have hvel : Tendsto (fun t : ℝ => (z t).2) atTop (𝓝 a) :=
    tendsto_vel_of_firstOrder ha (fun t ht => hnc t ht.le)
      (fun t ht => hz t (Set.mem_Ici.mpr ht.le)) hasym
  have hnorm1 : ∀ᶠ t : ℝ in atTop, dist (t⁻¹ • (z t).1) a < ρ / 6 := by
    filter_upwards [(Metric.tendsto_nhds.mp hasym) (ρ / 6) (by linarith)] with t ht
    exact ht
  have hnorm2 : ∀ᶠ t : ℝ in atTop, dist (z t).2 a < ρ / 6 :=
    (Metric.tendsto_nhds.mp hvel) (ρ / 6) (by linarith)
  have hbig : ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ 3 * K / ρ < t := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      eventually_gt_atTop (max (3 * K / ρ) 1)] with t h1 h2
    exact ⟨h1, lt_of_le_of_lt (le_max_left _ _) h2⟩
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hnorm1.and (hnorm2.and hbig))
  set t₁ : ℝ := max 1 T₀ with ht₁def
  have ht₁1 : 1 ≤ t₁ := le_max_left _ _
  have ht₁T : T₀ ≤ t₁ := le_max_right _ _
  have ht₁ : 0 < t₁ := lt_of_lt_of_le one_pos ht₁1
  have htK : K / t₁ < ρ / 3 := by
    have h1 : 3 * K / ρ < t₁ := (hT₀ t₁ ht₁T).2.2.2
    rw [div_lt_iff₀ hρ] at h1
    rw [div_lt_iff₀ ht₁]
    nlinarith
  have hposT : dist (z t₁).1 (t₁ • a) < t₁ * (ρ / 6) := by
    have h := (hT₀ t₁ ht₁T).1
    have h1 : (z t₁).1 = t₁ • (t₁⁻¹ • (z t₁).1) := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht₁), one_smul]
    rw [h1, dist_smul₀, Real.norm_eq_abs, abs_of_pos ht₁]
    exact mul_lt_mul_of_pos_left h ht₁
  have hvelT : dist (z t₁).2 a < ρ / 6 := (hT₀ t₁ ht₁T).2.1
  -- the uniform Lipschitz tube along the reference motion
  obtain ⟨r, hr, K', hLip⟩ :=
    Commons.Topology.Metric.exists_uniform_lipschitz_tube_of_locally
      (f := stateField m) (u := z) (a := 0) (b := t₁) ht₁.le
      (fun t ht => (hz t (Set.mem_Ici.mpr ht.1)).continuousAt.continuousWithinAt)
      (fun x hx => by
        obtain ⟨t, ht_mem, rfl⟩ := hx
        exact exists_lipschitzOnWith_stateField m (z t) (hnc t ht_mem.1))
  have hK'0 : (0 : ℝ) ≤ (K' : ℝ) := K'.coe_nonneg
  set c : ℝ := min (r / 2) (ρ / 6) * Real.exp (-(K' : ℝ) * t₁) / 6 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  set δ : ℝ := min 1 c with hδdef
  have hδ : 0 < δ := lt_min one_pos hcpos
  have hδc : δ ≤ c := min_le_right _ _
  have hc_eq : 3 * c * Real.exp ((K' : ℝ) * t₁) = min (r / 2) (ρ / 6) / 2 := by
    have h3 : Real.exp (-(K' : ℝ) * t₁) * Real.exp ((K' : ℝ) * t₁) = 1 := by
      rw [← Real.exp_add, show -(K' : ℝ) * t₁ + (K' : ℝ) * t₁ = 0 by ring, Real.exp_zero]
    calc 3 * c * Real.exp ((K' : ℝ) * t₁)
        = 3 * (min (r / 2) (ρ / 6) * Real.exp (-(K' : ℝ) * t₁) / 6)
            * Real.exp ((K' : ℝ) * t₁) := by rw [hcdef]
      _ = 3 * (min (r / 2) (ρ / 6))
            * (Real.exp (-(K' : ℝ) * t₁) * Real.exp ((K' : ℝ) * t₁)) / 6 := by ring
      _ = min (r / 2) (ρ / 6) / 2 := by rw [h3]; ring
  refine ⟨t₁, ht₁, δ, hδ, ?_⟩
  intro w S ht₁S hw hw0lim hw0dist
  -- the reference motion is continuous from the right at `0`
  have hz0lim : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 (z 0)) :=
    (hz 0 (Set.mem_Ici.mpr le_rfl)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨η₁, hη₁, hη₁'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hw0lim) c hcpos
  obtain ⟨η₂, hη₂, hη₂'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hz0lim) c hcpos
  set θ : ℝ := min (min η₁ η₂) t₁ / 2 with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ < η₁ := by
    rw [hθdef]
    have h := min_le_left (min η₁ η₂) t₁
    have h' := min_le_left η₁ η₂
    linarith
  have hθ2 : θ < η₂ := by
    rw [hθdef]
    have h := min_le_left (min η₁ η₂) t₁
    have h' := min_le_right η₁ η₂
    linarith
  have hθt₁ : θ < t₁ := by
    rw [hθdef]
    have h := min_le_right (min η₁ η₂) t₁
    linarith
  have hwθ : dist (w θ) (w 0) < c :=
    hη₁' hθpos (by rwa [Real.dist_eq, sub_zero, abs_of_pos hθpos])
  have hzθ : dist (z θ) (z 0) < c :=
    hη₂' hθpos (by rwa [Real.dist_eq, sub_zero, abs_of_pos hθpos])
  have hzθ' : dist (z 0) (z θ) < c := by rw [dist_comm]; exact hzθ
  have hcloseθ : dist (w θ) (z θ) < 3 * c := by
    have h1 : dist (w θ) (z θ) ≤ dist (w θ) (w 0) + dist (w 0) (z θ) := dist_triangle _ _ _
    have h2 : dist (w 0) (z θ) ≤ dist (w 0) (z 0) + dist (z 0) (z θ) := dist_triangle _ _ _
    have h3 : dist (w 0) (z 0) < δ := hw0dist
    calc dist (w θ) (z θ) ≤ dist (w θ) (w 0) + dist (w 0) (z θ) := h1
      _ ≤ dist (w θ) (w 0) + (dist (w 0) (z 0) + dist (z 0) (z θ)) := by linarith
      _ < c + (δ + c) := by linarith [hwθ, h3, hzθ']
      _ ≤ c + (c + c) := by linarith [hδc]
      _ = 3 * c := by ring
  -- the comparison on `[θ, t₁]`
  have hsmall : dist (w θ) (z θ) * Real.exp ((K' : ℝ) * (t₁ - θ)) ≤ r := by
    have hexp : Real.exp ((K' : ℝ) * (t₁ - θ)) ≤ Real.exp ((K' : ℝ) * t₁) :=
      Real.exp_le_exp.mpr (by nlinarith [hK'0, hθpos, hθt₁])
    have h1 : dist (w θ) (z θ) * Real.exp ((K' : ℝ) * (t₁ - θ))
        ≤ 3 * c * Real.exp ((K' : ℝ) * t₁) :=
      mul_le_mul (le_of_lt hcloseθ) hexp (Real.exp_pos _).le (by positivity)
    have h2 : 0 < min (r / 2) (ρ / 6) := lt_min (by linarith) (by linarith)
    have h3 := min_le_left (r / 2) (ρ / 6)
    rw [hc_eq] at h1
    linarith
  obtain ⟨v, hvθ, hvderiv, hvclose⟩ :=
    Commons.Analysis.ODE.solution_close_of_lipschitz_family (f := stateField m) (u := z)
      (a := θ) (b := t₁) hθt₁.le hr hK'0
      (fun t ht x y hx hy => hLip t ⟨le_trans hθpos.le ht.1, ht.2⟩ x y hx hy)
      (fun t ht => hz t (Set.mem_Ici.mpr (le_trans hθpos.le ht.1))) (w θ) hsmall
  have hbound : ∀ t ∈ Set.Icc θ t₁, dist (v t) (z t) ≤ min (r / 2) (ρ / 6) / 2 := by
    intro t ht
    refine le_trans (hvclose t ht) ?_
    have hexp : Real.exp ((K' : ℝ) * (t - θ)) ≤ Real.exp ((K' : ℝ) * t₁) :=
      Real.exp_le_exp.mpr (by nlinarith [hK'0, hθpos, ht.1, ht.2])
    have h1 : dist (w θ) (z θ) * Real.exp ((K' : ℝ) * (t - θ))
        ≤ 3 * c * Real.exp ((K' : ℝ) * t₁) :=
      mul_le_mul (le_of_lt hcloseθ) hexp (Real.exp_pos _).le (by positivity)
    rw [hc_eq] at h1
    exact h1
  -- uniqueness: `w` agrees with `v` on `[θ, t₁]`
  have hEq : Set.EqOn v w (Set.Icc θ t₁) := by
    refine Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz (f := stateField m)
      (u := v) (v := w) hθt₁.le ?_ ?_ ?_ ?_
    · intro t ht
      exact hvderiv t ht
    · intro t ht
      exact hw t ⟨lt_of_lt_of_le hθpos ht.1, le_trans ht.2 ht₁S⟩
    · intro t ht
      refine ⟨K', Metric.ball (v t) (r / 2), Metric.ball_mem_nhds _ (by linarith), ?_⟩
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro x hx y hy
      have h4 : dist (v t) (z t) ≤ min (r / 2) (ρ / 6) / 2 := hbound t ht
      have hbl : ∀ u ∈ Metric.ball (v t) (r / 2), dist u (z t) ≤ r := by
        intro u hu
        have hur : dist u (v t) < r / 2 := Metric.mem_ball.mp hu
        calc dist u (z t) ≤ dist u (v t) + dist (v t) (z t) := dist_triangle _ _ _
          _ ≤ r / 2 + r / 2 := by linarith [hur.le, h4, min_le_left (r / 2) (ρ / 6)]
          _ = r := by ring
      exact hLip t ⟨le_trans hθpos.le ht.1, ht.2⟩ x y (hbl x hx) (hbl y hy)
    · rw [hvθ]
  have hwt₁ : dist (w t₁) (z t₁) < min (r / 2) (ρ / 6) := by
    have h1 : v t₁ = w t₁ := hEq ⟨hθt₁.le, le_rfl⟩
    have h2 := hbound t₁ ⟨hθt₁.le, le_rfl⟩
    have h6 : 0 < min (r / 2) (ρ / 6) := lt_min (by linarith) (by linarith)
    rw [← h1]
    linarith
  have h3 : dist (w t₁) (z t₁) < ρ / 6 := lt_of_lt_of_le hwt₁ (min_le_right _ _)
  have hpt₁ : dist (w t₁).1 (t₁ • a) < t₁ * ρ / 3 := by
    have h1 : dist (w t₁).1 (t₁ • a) ≤ dist (w t₁).1 (z t₁).1 + dist (z t₁).1 (t₁ • a) :=
      dist_triangle _ _ _
    have h2 : dist (w t₁).1 (z t₁).1 ≤ dist (w t₁) (z t₁) := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    have h4 : ρ / 6 + ρ / 6 ≤ t₁ * ρ / 3 := by nlinarith [hρ, ht₁1]
    linarith [h1, h2, h3, hposT, h4]
  have hvt₁ : dist (w t₁).2 a < ρ / 3 := by
    have h1 : dist (w t₁).2 a ≤ dist (w t₁).2 (z t₁).2 + dist (z t₁).2 a := dist_triangle _ _ _
    have h2 : dist (w t₁).2 (z t₁).2 ≤ dist (w t₁) (z t₁) := by
      rw [Prod.dist_eq]; exact le_max_right _ _
    linarith [h1, h2, h3, hvelT, min_le_right (r / 2) (ρ / 6)]
  -- the tube on `[t₁,S]`
  have hwIcc : ∀ t ∈ Set.Icc t₁ S, HasDerivAt w (stateField m (w t)) t := fun t ht =>
    hw t ⟨lt_of_lt_of_le ht₁ ht.1, ht.2⟩
  obtain ⟨htube, hshape⟩ :=
    chazy_continuity_tube (m := m) (a := a) (ρ := ρ) (K := K) (t₁ := t₁) (S := S)
      hρ ht₁ htK hncρ hbρ ht₁S hwIcc hpt₁ hvt₁ hε
  refine ⟨fun t ht => tube_mono hρε (le_of_lt (lt_of_lt_of_le ht₁ ht.1)) (htube t ht).1 (htube t ht).2, ?_⟩
  obtain ⟨b, hb, t₂, ht₂, hshape'⟩ := hshape
  exact ⟨b, lt_of_le_of_lt hb (by linarith), t₂, ht₂, hshape'⟩



/-! ## §4 The cone argument: the limit shape is parallel to `a` -/

/-- **The limit shape of the calibrating curve is parallel to the prescribed direction `a`.**

The `h`-minimisers `γ_k` run from `γ 1` to `λ_k • a` in time `τ_k → ∞`, with initial velocities
converging to `(deriv γ) 1`.  Chazy's continuity of the limit shape (in the form
`chazy_continuity_Ioc`) puts the terminal configuration `γ_k(τ_k) = λ_k • a` inside the tube around
the ray `t ↦ t • b`, whence `‖(λ_k/τ_k) • a - b‖ < ε` for arbitrarily large `k` and arbitrarily
small `ε > 0`; since `a ≠ 0` this forces `b ∈ ℝ a`. -/
theorem exists_parallel_of_limitShape
    {m : Fin N → ℝ} {h : ℝ} {a b : EN E N} {γ : ℝ → EN E N}
    {γs : ℕ → ℝ → EN E N} {τ lam : ℕ → ℝ} {v : ℕ → EN E N}
    (hN : 2 ≤ N) (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hM : MarchalProperty (E := E) m h)
    (ha_nc : WithoutCollisions a) (ha_norm : ‖a‖_[m] = 1)
    (hb_nc : WithoutCollisions b)
    (hγsol : IsNBodySolution m γ) (hγnc : ∀ t > 0, WithoutCollisions (γ t))
    (hshape : Tendsto (fun t : ℝ => t⁻¹ • γ t) atTop (𝓝 b))
    (hτ : ∀ k, 0 < τ k) (hτtop : Tendsto τ atTop atTop)
    (hlam : ∀ k, 0 ≤ lam k)
    (h0 : ∀ k, γs k 0 = γ 1) (h1 : ∀ k, γs k (τ k) = lam k • a)
    (hac : ∀ k, AbsolutelyContinuousOnInterval (γs k) 0 (τ k))
    (hmin : ∀ k, IsHMinimizer m h (γs k) 0 (τ k))
    (hncγs : ∀ k, ∀ t ∈ Set.Icc 0 (τ k), WithoutCollisions (γs k t))
    (hv : ∀ k, Tendsto (deriv (γs k)) (𝓝[>] (0 : ℝ)) (𝓝 (v k)))
    (hvtop : Tendsto v atTop (𝓝 (deriv γ 1))) :
    ∃ c : ℝ, 0 ≤ c ∧ b = c • a := by
  have hNpos : 0 < N := by omega
  obtain ⟨α, β, hα, hβ, hest⟩ := actionPot_le_holder (E := E) (N := N) hNpos hm hh.le
  -- the reference state `t ↦ (γ (t+1), γ'(t+1))`
  set z : ℝ → EN E N × EN E N := fun t => (γ (t + 1), deriv γ (t + 1)) with hzdef
  have hnc_z : ∀ t : ℝ, 0 ≤ t → WithoutCollisions (z t).1 := by
    intro t ht
    exact hγnc (t + 1) (by linarith)
  have hz : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt z (stateField m (z t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (γ s, deriv γ s))
        (stateField m (γ (t + 1), deriv γ (t + 1))) (t + 1) :=
      hasDerivAt_state_of_isNBodySolution m hγsol (by
        rw [Set.mem_Ioi]
        have h0 : (0 : ℝ) ≤ t := ht
        linarith)
    have h2 := h1.comp_add_const t 1
    simpa [hzdef] using h2
  have hasym_z : Tendsto (fun t : ℝ => t⁻¹ • (z t).1) atTop (𝓝 b) := by
    have h1 : Tendsto (fun t : ℝ => ((t + 1)⁻¹ : ℝ) • γ (t + 1)) atTop (𝓝 b) := by
      have h := hshape.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
      simpa only [Function.comp_def, id_eq] using h
    have hγbound : ∀ᶠ t : ℝ in atTop, ‖γ (t + 1)‖ ≤ (‖b‖ + 1) * (t + 1) := by
      have h2 : ∀ᶠ t : ℝ in atTop, dist ((t + 1)⁻¹ • γ (t + 1)) b < 1 :=
        (Metric.tendsto_nhds.mp h1) 1 one_pos
      filter_upwards [h2, eventually_gt_atTop (0 : ℝ)] with t ht ht0
      have h4 : ‖(t + 1)⁻¹ • γ (t + 1)‖ < ‖b‖ + 1 := by
        have h5 : |‖(t + 1)⁻¹ • γ (t + 1)‖ - ‖b‖| ≤ dist ((t + 1)⁻¹ • γ (t + 1)) b := by
          rw [dist_eq_norm]
          exact abs_norm_sub_norm_le _ _
        linarith [(abs_le.mp h5).2]
      calc ‖γ (t + 1)‖ = (t + 1) * ‖(t + 1)⁻¹ • γ (t + 1)‖ := by
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr (by linarith : (0 : ℝ) < t + 1)),
              mul_inv_cancel_left₀ (by linarith : (t + 1) ≠ 0)]
        _ ≤ (t + 1) * (‖b‖ + 1) := by
            exact mul_le_mul_of_nonneg_left h4.le (by linarith)
        _ = (‖b‖ + 1) * (t + 1) := by ring
    have h2 : Tendsto (fun t : ℝ => t⁻¹ • γ (t + 1) - ((t + 1)⁻¹ : ℝ) • γ (t + 1))
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h3 : ∀ᶠ t : ℝ in atTop,
          ‖t⁻¹ • γ (t + 1) - ((t + 1)⁻¹ : ℝ) • γ (t + 1)‖ ≤ (‖b‖ + 1) / t := by
        filter_upwards [hγbound, eventually_gt_atTop (0 : ℝ)] with t hb ht
        have h4 : t⁻¹ • γ (t + 1) - ((t + 1)⁻¹ : ℝ) • γ (t + 1)
            = (t⁻¹ - (t + 1)⁻¹) • γ (t + 1) := by rw [sub_smul]
        rw [h4, norm_smul, Real.norm_eq_abs]
        have h5 : t⁻¹ - (t + 1)⁻¹ = 1 / (t * (t + 1)) := by
          rw [inv_sub_inv (by linarith) (by linarith)]; ring
        have h6 : 0 < t⁻¹ - (t + 1)⁻¹ := by rw [h5]; positivity
        rw [abs_of_pos h6, h5]
        calc 1 / (t * (t + 1)) * ‖γ (t + 1)‖ ≤ 1 / (t * (t + 1)) * ((‖b‖ + 1) * (t + 1)) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = (‖b‖ + 1) / t := by field_simp
      exact squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) h3
        (tendsto_const_nhds.div_atTop tendsto_id)
    have h4 := h2.add h1
    simpa using h4
  -- for every `ε > 0` there is `k` with the terminal shape close to `b`
  have hmain : ∀ ε > 0, ∃ k : ℕ, dist ((lam k / τ k) • a) b < ε := by
    intro ε hε
    obtain ⟨t₁, ht₁, δ, hδ, hconcl⟩ :=
      chazy_continuity_Ioc (E := E) (N := N) (m := m) (a := b) (z := z) hb_nc hnc_z hz hasym_z
        (show (0 : ℝ) < ε / 2 by linarith)
    have hev1 : ∀ᶠ k : ℕ in atTop, t₁ ≤ τ k := tendsto_atTop.1 hτtop t₁
    have hev2 : ∀ᶠ k : ℕ in atTop, dist (v k) (deriv γ 1) < δ :=
      (Metric.tendsto_nhds.mp hvtop) δ hδ
    obtain ⟨k, hk⟩ := eventually_atTop.1 (hev1.and hev2)
    have hk1 : t₁ ≤ τ k := (hk k le_rfl).1
    have hk2 : dist (v k) (deriv γ 1) < δ := (hk k le_rfl).2
    obtain ⟨L, W, hW0, hWτ, hWderiv, hWcont, -⟩ :=
      exists_minimizerState (m := m) (h := h) (τ := τ k) (γ := γs k) (v := v k) hm hh
        (hτ k) (hac k) (hncγs k) (hmin k)
        (lt_of_le_of_lt (hest _ _) ENNReal.ofReal_lt_top) (hv k)
    have hclose : dist (W 0) (z 0) < δ := by
      rw [hW0, h0 k]
      have hz0 : z 0 = (γ 1, deriv γ 1) := by
        simp [hzdef]
      rw [hz0]
      simpa using hk2
    obtain ⟨htube, -⟩ := hconcl W (τ k) hk1 hWderiv hWcont hclose
    have htmem : τ k ∈ Set.Icc t₁ (τ k) := ⟨hk1, le_rfl⟩
    have h1' : dist (W (τ k)).1 (τ k • b) < τ k * (ε / 2) := (htube (τ k) htmem).1
    have h2' : (W (τ k)).1 = lam k • a := by rw [hWτ, h1 k]
    rw [h2'] at h1'
    have h3' : dist ((lam k / τ k) • a) b < ε / 2 := by
      have hdist : dist ((lam k / τ k) • a) b
          = (τ k)⁻¹ * dist (lam k • a) (τ k • b) := by
        rw [dist_eq_norm, dist_eq_norm,
          show (lam k / τ k) • a - b = (τ k)⁻¹ • (lam k • a - τ k • b) by
            rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ (ne_of_gt (hτ k)), one_smul,
              div_eq_inv_mul],
          norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hτ k))]
      rw [hdist]
      have h10 : (τ k)⁻¹ * (τ k * (ε / 2)) = ε / 2 := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hτ k)), one_mul]
      calc (τ k)⁻¹ * dist (lam k • a) (τ k • b)
          < (τ k)⁻¹ * (τ k * (ε / 2)) := mul_lt_mul_of_pos_left h1' (inv_pos.mpr (hτ k))
        _ = ε / 2 := h10
    exact ⟨k, by linarith⟩
  -- conclude `b ∈ ℝ a`
  choose k hk using fun n : ℕ => hmain ((1 : ℝ) / (n + 1)) (by positivity)
  have hconv : Tendsto (fun n : ℕ => (lam (k n) / τ (k n)) • a) atTop (𝓝 b) :=
    tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero (fun n => dist_nonneg) (fun n => (hk n).le)
        (by
          have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
            tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
          have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).div_atTop h1
          simpa [Nat.cast_add, Nat.cast_one] using h))
  have ha_ne : a ≠ 0 := by
    intro h0'
    have h1 : ‖a‖_[m] = 0 := (weightedNorm_eq_zero_iff hm a).mpr h0'
    rw [ha_norm] at h1
    norm_num at h1
  have hanorm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha_ne
  have hinner : Tendsto (fun n : ℕ => inner ℝ ((lam (k n) / τ (k n)) • a) a) atTop
      (𝓝 (inner ℝ b a)) :=
    hconv.inner tendsto_const_nhds
  have hcoef : Tendsto (fun n : ℕ => lam (k n) / τ (k n)) atTop
      (𝓝 (inner ℝ b a / ‖a‖ ^ 2)) := by
    have h1 : (fun n : ℕ => inner ℝ ((lam (k n) / τ (k n)) • a) a)
        = fun n : ℕ => (lam (k n) / τ (k n)) * ‖a‖ ^ 2 := by
      funext n
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [h1] at hinner
    have h2 : Tendsto (fun n : ℕ => (lam (k n) / τ (k n)) * ‖a‖ ^ 2 / ‖a‖ ^ 2) atTop
        (𝓝 (inner ℝ b a / ‖a‖ ^ 2)) :=
      hinner.div_const _
    refine h2.congr' ?_
    filter_upwards with n
    field_simp
  have hlim2 : Tendsto (fun n : ℕ => (lam (k n) / τ (k n)) • a) atTop
      (𝓝 ((inner ℝ b a / ‖a‖ ^ 2) • a)) := hcoef.smul_const a
  have hc_nonneg : 0 ≤ inner ℝ b a / ‖a‖ ^ 2 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hcoef
      (Filter.Eventually.of_forall fun n => div_nonneg (hlam (k n)) (le_of_lt (hτ (k n))))
  exact ⟨inner ℝ b a / ‖a‖ ^ 2, hc_nonneg, tendsto_nhds_unique hconv hlim2⟩

end Submission.NBody
