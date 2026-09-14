import ChallengeDeps
import Submission.NBody.ChazyShape
import Submission.NBody.Chazy
import Submission.NBody.FirstVariation
import Submission.NBody.Continuation
import Submission.Commons.Analysis.ODE.solution_close_of_lipschitz_family
import Submission.Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz
import Submission.Commons.Topology.Metric.exists_uniform_lipschitz_tube_of_locally

/-!
# Chazy's continuity of the limit shape

Chazy's lemma, second part: *the limit shape depends continuously on the initial data*.  If `z` is a
motion (a solution of the state equation on `[0,∞)`, with collision-free positions and asymptotic
shape `a`, i.e. `t⁻¹ • (z t).1 → a` with `a` collision-free), then every solution starting close
enough to `z 0` exists on any prescribed interval and inherits the asymptotics: it stays in the
tube around the ray `t ↦ t • a` and its shape stays close to a configuration `b` with `dist b a < ε`.

The statement is the finite-horizon form used by the cone argument of the paper: for every `ε > 0`
there are `t₁` and `δ` such that for every `S ≥ t₁` and every solution `w` on `[0,S]` with
`dist (w 0) (z 0) < δ` the assertions hold on `[t₁,S]`.  (Global existence is *not* needed: the
shape is compared with the terminal velocity, as in `Submission.NBody.ChazyShape`.)
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Chazy's lemma, first part, in state form.**  A solution of the state equation whose normalized
configuration converges to a collision-free configuration `a` has asymptotic velocity `a`. -/
lemma tendsto_vel_of_firstOrder {m : Fin N → ℝ} {z : ℝ → EN E N × EN E N} {a : EN E N}
    (ha : WithoutCollisions a)
    (hnc : ∀ t : ℝ, 0 < t → WithoutCollisions (z t).1)
    (hz : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt z (stateField m (z t)) t)
    (hasym : Tendsto (fun t : ℝ => t⁻¹ • (z t).1) atTop (𝓝 a)) :
    Tendsto (fun t : ℝ => (z t).2) atTop (𝓝 a) := by
  obtain ⟨K, hK⟩ := eventually_norm_weightedGrad_le_inv_sq m ha hasym
  have hderiv : ∀ t ∈ Set.Ici (1 : ℝ),
      HasDerivAt (fun s : ℝ => (z s).2) (weightedGrad m (U m) (z t).1) t := by
    intro t ht
    have h := (ContinuousLinearMap.snd ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt t
      (hz t (by rw [Set.mem_Ioi]; exact lt_of_lt_of_le (by norm_num) ht))
    simpa [stateField, Function.comp_def] using h
  have hcont : ContinuousOn (fun t : ℝ => weightedGrad m (U m) (z t).1) (Set.Ici (1 : ℝ)) := by
    have hzcont : ContinuousOn (fun t : ℝ => (z t).1) (Set.Ici (1 : ℝ)) := fun t ht =>
      (continuous_fst.continuousAt.comp
        (hz t (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) ht)).continuousAt).continuousWithinAt
    have hmaps : MapsTo (fun t : ℝ => (z t).1) (Set.Ici (1 : ℝ))
        {x : EN E N | WithoutCollisions x} := fun t ht =>
      hnc t (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) ht)
    exact continuousOn_weightedGrad_comp (m := m)
      ((Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv
        (isOpen_setOf_withoutCollisions (E := E) (N := N))
        (contDiffOn_U (m := m) (n := 1))).comp hzcont hmaps)
  obtain ⟨l, hl⟩ :=
    Commons.Analysis.Asymptotics.exists_tendsto_atTop_of_eventually_norm_le_inv_sq
      (by norm_num : (0 : ℝ) < 1) hderiv hcont hK
  have hxderiv : ∀ t ∈ Set.Ici (1 : ℝ), HasDerivAt (fun s : ℝ => (z s).1) ((z t).2) t := by
    intro t ht
    have h := (ContinuousLinearMap.fst ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt t
      (hz t (by rw [Set.mem_Ioi]; exact lt_of_lt_of_le (by norm_num) ht))
    simpa [stateField, Function.comp_def] using h
  have hb' : Tendsto (fun t : ℝ => t⁻¹ • ((z t).1 - (z 1).1)) atTop (𝓝 a) := by
    have h0 : Tendsto (fun t : ℝ => t⁻¹ • (z 1).1) atTop (𝓝 (0 : EN E N)) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul (tendsto_const_nhds (x := (z 1).1))
      simpa using h
    simpa [smul_sub, sub_zero] using hasym.sub h0
  have hxlim := Commons.Analysis.Calculus.tendsto_smul_inv_sub_of_tendsto_deriv (T := 1) hxderiv hl
  rw [tendsto_nhds_unique hxlim hb'] at hl
  exact hl

/-- A `K`-tube around the ray `t ↦ t • a` can be chosen inside the `ε`-tube when `K ≤ ε`. -/
lemma tube_mono {a : EN E N} {ρ ε : ℝ} (h : ρ ≤ ε) {t : ℝ} (ht : 0 ≤ t)
    {z : EN E N × EN E N} (h1 : dist z.1 (t • a) < t * ρ) (h2 : dist z.2 a < 2 * ρ / 3) :
    dist z.1 (t • a) < t * ε ∧ dist z.2 a < 2 * ε / 3 :=
  ⟨lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_left h ht),
    lt_of_lt_of_le h2 (by linarith)⟩

/-- **Chazy's continuity of the limit shape.** -/
theorem chazy_continuity {m : Fin N → ℝ} {a : EN E N} (ha : WithoutCollisions a)
    {z : ℝ → EN E N × EN E N}
    (hnc : ∀ t : ℝ, 0 ≤ t → WithoutCollisions (z t).1)
    (hz : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt z (stateField m (z t)) t)
    (hasym : Tendsto (fun t : ℝ => t⁻¹ • (z t).1) atTop (𝓝 a))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ w₀ : EN E N × EN E N, dist w₀ (z 0) < δ →
      ∀ S : ℝ, t₁ ≤ S → ∀ w : ℝ → EN E N × EN E N, w 0 = w₀ →
        (∀ t ∈ Set.Icc (0 : ℝ) S, HasDerivAt w (stateField m (w t)) t) →
        (∀ t ∈ Set.Icc t₁ S, dist (w t).1 (t • a) < t * ε ∧ dist (w t).2 a < 2 * ε / 3) ∧
        ∃ b : EN E N, dist b a < ε ∧ ∃ t₂ : ℝ, t₁ ≤ t₂ ∧
          ∀ t ∈ Set.Icc t₂ S, dist (t⁻¹ • (w t).1) b < ε := by
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
  set δ : ℝ := min 1 (min (r / 2) (ρ / 6) * Real.exp (-(K' : ℝ) * t₁)) with hδdef
  have hexp : 0 < Real.exp (-(K' : ℝ) * t₁) := Real.exp_pos _
  have hδ : 0 < δ := lt_min one_pos (mul_pos (lt_min (by linarith) (by linarith)) hexp)
  refine ⟨t₁, ht₁, δ, hδ, ?_⟩
  intro w₀ hw₀ S ht₁S w hw0 hw
  -- the perturbed solution on `[0,t₁]` constructed from the initial datum
  have hsmall : dist w₀ (z 0) * Real.exp ((K' : ℝ) * (t₁ - 0)) ≤ r := by
    have h1 : dist w₀ (z 0) < δ := hw₀
    have h2 : δ ≤ min (r / 2) (ρ / 6) * Real.exp (-(K' : ℝ) * t₁) := min_le_right _ _
    have h4 : 0 < Real.exp ((K' : ℝ) * (t₁ - 0)) := Real.exp_pos _
    have h3 : dist w₀ (z 0) * Real.exp ((K' : ℝ) * (t₁ - 0))
        < min (r / 2) (ρ / 6) * Real.exp (-(K' : ℝ) * t₁) * Real.exp ((K' : ℝ) * (t₁ - 0)) :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_right h1 h4) (mul_le_mul_of_nonneg_right h2 h4.le)
    have h5 : min (r / 2) (ρ / 6) * Real.exp (-(K' : ℝ) * t₁) * Real.exp ((K' : ℝ) * (t₁ - 0))
        = min (r / 2) (ρ / 6) := by
      rw [mul_assoc, ← Real.exp_add,
        show -(K' : ℝ) * t₁ + (K' : ℝ) * (t₁ - 0) = 0 by ring, Real.exp_zero, mul_one]
    rw [h5] at h3
    exact le_trans h3.le (le_trans (min_le_left (r / 2) (ρ / 6)) (by linarith))
  obtain ⟨v, hv0, hvderiv, hvclose⟩ :=
    Commons.Analysis.ODE.solution_close_of_lipschitz_family (f := stateField m) (u := z)
      (a := 0) (b := t₁) ht₁.le hr hK'0
      (fun t ht x y hx hy => hLip t ht x y hx hy)
      (fun t ht => hz t (Set.mem_Ici.mpr ht.1)) w₀ hsmall
  -- uniqueness: the given solution agrees with it
  have hEq : Set.EqOn v w (Set.Icc 0 t₁) := by
    refine Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz (f := stateField m)
      (u := v) (v := w) ht₁.le ?_ ?_ ?_ ?_
    · intro t ht
      exact hvderiv t ht
    · intro t ht
      exact hw t ⟨ht.1, le_trans ht.2 ht₁S⟩
    · intro t ht
      -- `v t` is within `r/2` of `z t`, so the Lipschitz family around `z t` gives a Lipschitz
      -- neighbourhood of `v t`
      refine ⟨K', Metric.ball (v t) (r / 2), Metric.ball_mem_nhds _ (by linarith), ?_⟩
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro x hx y hy
      have hv1 : dist (v t) (z t) ≤ dist w₀ (z 0) * Real.exp ((K' : ℝ) * (t - 0)) :=
        hvclose t ⟨ht.1, ht.2⟩
      have h4 : dist (v t) (z t) < min (r / 2) (ρ / 6) := by
        have h5 : dist w₀ (z 0) * Real.exp ((K' : ℝ) * (t - 0))
            ≤ dist w₀ (z 0) * Real.exp ((K' : ℝ) * (t₁ - 0)) := by
          have h6 : Real.exp ((K' : ℝ) * (t - 0)) ≤ Real.exp ((K' : ℝ) * (t₁ - 0)) :=
            Real.exp_le_exp.mpr (by nlinarith [hK'0, ht.1, ht.2])
          exact mul_le_mul_of_nonneg_left h6 dist_nonneg
        have h7 : dist w₀ (z 0) * Real.exp ((K' : ℝ) * (t₁ - 0))
            < min (r / 2) (ρ / 6) := by
          have h9 : δ ≤ min (r / 2) (ρ / 6) * Real.exp (-(K' : ℝ) * t₁) := min_le_right _ _
          have h10 : dist w₀ (z 0) < δ := hw₀
          have h4' : 0 < Real.exp ((K' : ℝ) * (t₁ - 0)) := Real.exp_pos _
          have h11 : dist w₀ (z 0) * Real.exp ((K' : ℝ) * (t₁ - 0))
              < δ * Real.exp ((K' : ℝ) * (t₁ - 0)) := mul_lt_mul_of_pos_right h10 h4'
          have h12 : δ * Real.exp ((K' : ℝ) * (t₁ - 0))
              ≤ (min (r / 2) (ρ / 6) * Real.exp (-(K' : ℝ) * t₁))
                * Real.exp ((K' : ℝ) * (t₁ - 0)) :=
            mul_le_mul_of_nonneg_right h9 h4'.le
          have h13 : min (r / 2) (ρ / 6) * Real.exp (-(K' : ℝ) * t₁)
              * Real.exp ((K' : ℝ) * (t₁ - 0)) = min (r / 2) (ρ / 6) := by
            rw [mul_assoc, ← Real.exp_add,
              show -(K' : ℝ) * t₁ + (K' : ℝ) * (t₁ - 0) = 0 by ring, Real.exp_zero, mul_one]
          linarith [h11, h12, h13.le, h13.ge]
        exact lt_of_le_of_lt (hv1.trans h5) h7
      have hbl : ∀ u ∈ Metric.ball (v t) (r / 2), dist u (z t) ≤ r := by
        intro u hu
        have hur : dist u (v t) < r / 2 := Metric.mem_ball.mp hu
        calc dist u (z t) ≤ dist u (v t) + dist (v t) (z t) := dist_triangle _ _ _
          _ ≤ r / 2 + r / 2 := by linarith [hur.le, lt_of_lt_of_le h4 (min_le_left (r / 2) (ρ / 6))]
          _ = r := by ring
      exact hLip t ⟨ht.1, ht.2⟩ x y (hbl x hx) (hbl y hy)
    · rw [hv0, hw0]
  -- conclusion: the tube at time `t₁` for `w`
  have hwt₁ : dist (w t₁) (z t₁) < min (r / 2) (ρ / 6) := by
    have h1 : v t₁ = w t₁ := hEq ⟨ht₁.le, le_rfl⟩
    rw [← h1]
    have hv1 := hvclose t₁ ⟨ht₁.le, le_rfl⟩
    have h4 : dist w₀ (z 0) < δ := hw₀
    have h9 : δ ≤ min (r / 2) (ρ / 6) * Real.exp (-(K' : ℝ) * t₁) := min_le_right _ _
    have h4' : 0 < Real.exp ((K' : ℝ) * t₁) := Real.exp_pos _
    have h11 : dist w₀ (z 0) * Real.exp ((K' : ℝ) * (t₁ - 0))
        < δ * Real.exp ((K' : ℝ) * t₁) := by
      have : (t₁ : ℝ) - 0 = t₁ := by ring
      rw [this]
      exact mul_lt_mul_of_pos_right h4 h4'
    have h12 : δ * Real.exp ((K' : ℝ) * t₁)
        ≤ min (r / 2) (ρ / 6) * Real.exp (-(K' : ℝ) * t₁) * Real.exp ((K' : ℝ) * t₁) :=
      mul_le_mul_of_nonneg_right h9 h4'.le
    have h13 : min (r / 2) (ρ / 6) * Real.exp (-(K' : ℝ) * t₁) * Real.exp ((K' : ℝ) * t₁)
        = min (r / 2) (ρ / 6) := by
      rw [mul_assoc, ← Real.exp_add, show -(K' : ℝ) * t₁ + (K' : ℝ) * t₁ = 0 by ring,
        Real.exp_zero, mul_one]
    linarith [hv1, h11, h12, h13.le, h13.ge]
  have hpt₁ : dist (w t₁).1 (t₁ • a) < t₁ * ρ / 3 := by
    have h1 : dist (w t₁).1 (t₁ • a) ≤ dist (w t₁).1 (z t₁).1 + dist (z t₁).1 (t₁ • a) :=
      dist_triangle _ _ _
    have h2 : dist (w t₁).1 (z t₁).1 ≤ dist (w t₁) (z t₁) := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    have h3 : dist (w t₁) (z t₁) < ρ / 6 := lt_of_lt_of_le hwt₁ (min_le_right (r / 2) (ρ / 6))
    have h4 : ρ / 6 + ρ / 6 ≤ t₁ * ρ / 3 := by nlinarith [hρ, ht₁1]
    linarith [h1, h2, h3, hposT, h4]
  have hvt₁ : dist (w t₁).2 a < ρ / 3 := by
    have h1 : dist (w t₁).2 a ≤ dist (w t₁).2 (z t₁).2 + dist (z t₁).2 a := dist_triangle _ _ _
    have h2 : dist (w t₁).2 (z t₁).2 ≤ dist (w t₁) (z t₁) := by
      rw [Prod.dist_eq]; exact le_max_right _ _
    linarith [h1, h2, hwt₁, hvelT, min_le_right (r / 2) (ρ / 6)]
  -- apply the tube/asymptotic lemma on `[t₁,S]`
  have hwIcc : ∀ t ∈ Set.Icc t₁ S, HasDerivAt w (stateField m (w t)) t := fun t ht =>
    hw t ⟨le_trans (le_of_lt ht₁) ht.1, ht.2⟩
  obtain ⟨htube, hshape⟩ :=
    chazy_continuity_tube (m := m) (a := a) (ρ := ρ) (K := K) (t₁ := t₁) (S := S)
      hρ ht₁ htK hncρ hbρ ht₁S hwIcc hpt₁ hvt₁ hε
  refine ⟨fun t ht => tube_mono hρε (le_of_lt (lt_of_lt_of_le ht₁ ht.1)) (htube t ht).1 (htube t ht).2, ?_⟩
  obtain ⟨b, hb, t₂, ht₂, hshape'⟩ := hshape
  exact ⟨b, lt_of_le_of_lt hb (by linarith), t₂, ht₂, hshape'⟩

end Submission.NBody
