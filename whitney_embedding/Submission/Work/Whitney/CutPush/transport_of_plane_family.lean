import Mathlib

/-!
# Transporting a smooth family of planes to a fixed plane

Let `E` be a finite-dimensional real normed space and `pr : ℝ → E →L[ℝ] E` a smooth family of
idempotent ("projection") operators of constant rank.  Then there is a smooth family `Λ t` of linear
isomorphisms with `Λ t (range (pr t)) = range (pr 0)` for `t ∈ [0,1]`, together with a smooth family
of inverses.

This is the triviality of the smooth plane bundle `t ↦ range (pr t)` over the interval (a
contractible base); it is the last missing brick of the collar-flattening route
(`CutPush/NOTES_collar_route_v4.md` §S53f): the fibre family of the collar construction must land in
a *fixed* plane `P₀`, while the slice's own base plane `P_τ` moves, so the moving planes must be
transported to a fixed one.

## The construction

* **Small steps.**  For two projections with `‖pr - pr'‖ < 1` the map `1 - pr' + pr` is a linear
  isomorphism (it is within distance `< 1` of the identity) carrying `range pr'` onto `range pr`
  (`small_step_mem_range`, `small_step_injective`);
* **uniform smallness** on the compact interval `[-2,2]` (`exists_close_of_close_param`, by
  Heine–Cantor applied to the evaluation `(t,y) ↦ pr t y` on a compact product);
* **marching.**  With `N` so large that `2/N` is below that scale, the levels
  `ℓ k τ = ψ τ * k / N` (where `ψ` is a smooth, globally `2`-bounded function with `ψ = id` on
  `[-1,1]`) give factors `1 - pr (ℓ (k+1) τ) + pr (ℓ k τ)` whose consecutive projections differ by
  less than `1`; composing them from `k = N-1` down to `0` (`marchFac`) transports
  `range (pr (ℓ N τ)) = range (pr τ)` into `range (pr (ℓ 0 τ)) = range (pr 0)` for `τ ∈ [0,1]`
  (the telescoping `marchFac_mem`);
* the result is a smooth family of isomorphisms; the inverse family is Mathlib's
  `ContinuousLinearMap.inverse` of it, smooth by `IsInvertible.contDiffAt_map_inverse`.
-/

open scoped ContDiff
open Set

namespace Work.Whitney.CutPush

set_option maxHeartbeats 8000000

theorem exists_close_of_close_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E]
    (P : ℝ → E →L[ℝ] E) (hP : Continuous fun p : ℝ × E => P p.1 p.2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, |s - t| < δ → ‖P s - P t‖ < ε := by
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hKcpt : IsCompact ((Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) ×ˢ Metric.closedBall (0 : E) 1) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall (0 : E) 1)
  have hcont : ContinuousOn (fun p : (ℝ × ℝ) × E => P p.1.1 p.2 - P p.1.2 p.2)
      ((Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) ×ˢ Metric.closedBall (0 : E) 1) :=
    (((hP.comp (continuous_fst.fst.prodMk continuous_snd)).continuousOn).sub
      ((hP.comp (continuous_fst.snd.prodMk continuous_snd)).continuousOn))
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.uniformContinuousOn_iff.mp
      (hKcpt.uniformContinuousOn_of_continuous hcont)) (ε / 2) hε2
  refine ⟨δ, hδpos, ?_⟩
  intro s hs t ht hst
  refine lt_of_le_of_lt ?_ (by linarith : ε / 2 < ε)
  rw [ContinuousLinearMap.opNorm_le_iff (by linarith : (0 : ℝ) ≤ ε / 2)]
  intro y
  by_cases hy : y = 0
  · simp [hy]
  have hyn : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  set z : E := ‖y‖⁻¹ • y with hz
  have hz1 : ‖z‖ ≤ 1 := by
    rw [hz, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hyn.le)]
    exact le_of_eq (inv_mul_cancel₀ (ne_of_gt hyn))
  have hzmem : z ∈ Metric.closedBall (0 : E) 1 := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  have h1 : (((s, t), z) : (ℝ × ℝ) × E)
      ∈ (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) ×ˢ Metric.closedBall (0 : E) 1 := ⟨⟨hs, ht⟩, hzmem⟩
  have h2 : (((s, s), z) : (ℝ × ℝ) × E)
      ∈ (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) ×ˢ Metric.closedBall (0 : E) 1 := ⟨⟨hs, hs⟩, hzmem⟩
  have hd : dist (((s, t), z) : (ℝ × ℝ) × E) (((s, s), z) : (ℝ × ℝ) × E) = |s - t| := by
    rw [dist_prod_same_right, Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _),
      abs_sub_comm]
  have hlt : ‖P s z - P t z‖ < ε / 2 := by
    have h := hδ (((s, t), z) : (ℝ × ℝ) × E) h1 (((s, s), z) : (ℝ × ℝ) × E) h2
      (by rw [hd]; exact hst)
    simpa [dist_eq_norm] using h
  have hyz : y = ‖y‖ • z := by
    rw [hz, smul_smul, mul_inv_cancel₀ (ne_of_gt hyn), one_smul]
  have hmain : ‖(P s - P t) y‖ = ‖y‖ * ‖(P s - P t) z‖ := by
    conv_lhs => rw [hyz, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hyn]
  rw [hmain]
  calc ‖y‖ * ‖(P s - P t) z‖ ≤ ‖y‖ * (ε / 2) := mul_le_mul_of_nonneg_left hlt.le hyn.le
    _ = ε / 2 * ‖y‖ := by ring

/-- The small-step map `1 - pr' + pr` carries `range pr'` into `range pr`. -/
theorem small_step_mem_range {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {pr pr' : E →L[ℝ] E} (hidem' : pr' * pr' = pr')
    {y : E} (hy : y ∈ LinearMap.range (pr' : E →ₗ[ℝ] E)) :
    ((1 - pr' + pr : E →L[ℝ] E) y) ∈ LinearMap.range (pr : E →ₗ[ℝ] E) := by
  obtain ⟨w, rfl⟩ := hy
  have hw : pr' (pr' w) = pr' w := by
    have := congrArg (fun f : E →L[ℝ] E => f w) hidem'
    simpa using this
  refine ⟨pr' w, ?_⟩
  change pr (pr' w) = (1 - pr' + pr) (pr' w)
  rw [show (1 - pr' + pr : E →L[ℝ] E) (pr' w)
      = (1 : E →L[ℝ] E) (pr' w) - pr' (pr' w) + pr (pr' w) from rfl,
    ContinuousLinearMap.one_apply, hw, sub_self, zero_add]

/-- The small-step map is injective when the two projections are within distance `1`. -/
theorem small_step_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {pr pr' : E →L[ℝ] E} (h : ‖pr - pr'‖ < 1) :
    Function.Injective ((1 - pr' + pr : E →L[ℝ] E)) := by
  intro a b hab
  have h0 : (1 - pr' + pr) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have h1 : (1 : E →L[ℝ] E) - (1 - pr' + pr) = pr' - pr := by
    ext y
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply]
    abel
  have h2 : a - b = (pr' - pr) (a - b) := by
    have h1y := congrArg (fun f : E →L[ℝ] E => f (a - b)) h1
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at h1y
    rw [h0, sub_zero] at h1y
    simpa only [ContinuousLinearMap.sub_apply] using h1y
  have h3 : ‖a - b‖ ≤ ‖pr - pr'‖ * ‖a - b‖ := by
    conv_lhs => rw [h2]
    calc ‖(pr' - pr) (a - b)‖ ≤ ‖pr' - pr‖ * ‖a - b‖ := (pr' - pr).le_opNorm _
      _ = ‖pr - pr'‖ * ‖a - b‖ := by rw [← norm_neg, neg_sub]
  have hpos : 0 < 1 - ‖pr - pr'‖ := by linarith
  have h5 : ‖a - b‖ = 0 := by
    by_contra hne
    have hlt : 0 < ‖a - b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have := mul_pos hpos hlt
    nlinarith [h3]
  exact sub_eq_zero.mp (norm_eq_zero.mp h5)

/-- The marching product of a family of factors: `marchFac F j = F (j-1) * (… * (F 0 * 1))`. -/
noncomputable def marchFac {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → E →L[ℝ] E) : ℕ → E →L[ℝ] E
  | 0 => 1
  | (j + 1) => F j * marchFac F j

@[simp] theorem marchFac_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → E →L[ℝ] E) : marchFac F 0 = 1 := rfl

@[simp] theorem marchFac_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → E →L[ℝ] E) (j : ℕ) : marchFac F (j + 1) = F j * marchFac F j := rfl

/-- Telescoping a chain of submodules along the marching product. -/
theorem marchFac_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {F : ℕ → E →L[ℝ] E} {P : ℕ → Submodule ℝ E}
    (hF : ∀ j : ℕ, j < N → ∀ y : E, y ∈ P (N - j) → (F j) y ∈ P (N - (j + 1))) :
    ∀ j : ℕ, j ≤ N → ∀ y : E, y ∈ P N → (marchFac F j) y ∈ P (N - j) := by
  intro j hj
  induction j with
  | zero => intro y hy; simpa using hy
  | succ i ih =>
      intro y hy
      rw [marchFac_succ]
      have hi : i < N := by omega
      simpa only [ContinuousLinearMap.mul_apply] using
        hF i hi ((marchFac F i) y) (ih (by omega) y hy)

theorem exists_transport_of_plane_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {k : ℕ}
    (pr : ℝ → E →L[ℝ] E)
    (hpr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => pr p.1 p.2))
    (hidem : ∀ t, pr t * pr t = pr t)
    (hrank : ∀ t : ℝ, Module.finrank ℝ (LinearMap.range (pr t : E →ₗ[ℝ] E)) = k) :
    ∃ (Λ Λinv : ℝ → E →L[ℝ] E),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Λ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Λinv ∧
      (∀ t y, Λinv t (Λ t y) = y) ∧ (∀ t y, Λ t (Λinv t y) = y) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        LinearMap.range ((Λ t).toLinearMap.comp (pr t).toLinearMap)
          = LinearMap.range (pr 0).toLinearMap) := by
  classical
  -- ## step 1: a uniform scale on which `pr` moves by less than `1`
  obtain ⟨δ1, hδ1pos, hδ1⟩ :=
    exists_close_of_close_param pr hpr.continuous (by norm_num : (0 : ℝ) < 1)
  -- ## step 2: a number of steps
  obtain ⟨N, hNpos, hN⟩ : ∃ N : ℕ, (0 : ℝ) < (N : ℝ) ∧ 2 / (N : ℝ) < δ1 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / δ1)
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 / δ1) hn.le
    refine ⟨n, hn0, ?_⟩
    rw [div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ1pos] at hn
    linarith
  -- ## step 3: the bounded smooth reparametrisation
  obtain ⟨ψ, hψsm, hψid, hψbd⟩ : ∃ ψ : ℝ → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ τ : ℝ, |τ| ≤ 1 → ψ τ = τ) ∧
      (∀ τ : ℝ, |ψ τ| ≤ 2) := by
    refine ⟨fun τ => τ * Real.smoothTransition (2 - τ ^ 2), ?_, ?_, ?_⟩
    · fun_prop
    · intro τ hτ
      have hτ2 : τ ^ 2 ≤ 1 := by
        have h := abs_le.mp hτ
        nlinarith [h.1, h.2, sq_nonneg τ, sq_abs τ]
      have h : 1 ≤ 2 - τ ^ 2 := by linarith
      show τ * Real.smoothTransition (2 - τ ^ 2) = τ
      rw [Real.smoothTransition.one_of_one_le h, mul_one]
    · intro τ
      rw [abs_mul]
      by_cases h : |τ| ≤ 2
      · have h2 : |Real.smoothTransition (2 - τ ^ 2)| ≤ 1 := by
          rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
          exact Real.smoothTransition.le_one _
        calc |τ| * |Real.smoothTransition (2 - τ ^ 2)| ≤ 2 * 1 :=
              mul_le_mul h h2 (abs_nonneg _) (by norm_num)
          _ = 2 := by norm_num
      · have h0 : Real.smoothTransition (2 - τ ^ 2) = 0 := by
          apply Real.smoothTransition.zero_of_nonpos
          have h2 : τ ^ 2 > 4 := by nlinarith [sq_abs τ]
          linarith
        rw [h0, abs_zero, mul_zero]
        norm_num
  -- ## step 4: the levels
  let ℓ : ℕ → ℝ → ℝ := fun j τ => ψ τ * (j : ℝ) / (N : ℝ)
  have hℓ_succ : ∀ j τ, ℓ (j + 1) τ = ψ τ * ((j + 1 : ℕ) : ℝ) / (N : ℝ) := fun j τ => rfl
  -- ## step 5: the step-size bound, the levels lie in `[-2,2]`, and small steps
  have hfac_step : ∀ j : ℕ, ∀ τ : ℝ, |ℓ (j + 1) τ - ℓ j τ| ≤ 2 / (N : ℝ) := by
    intro j τ
    have h1 : ψ τ * ((j + 1 : ℕ) : ℝ) / (N : ℝ) - ψ τ * (j : ℝ) / (N : ℝ)
        = ψ τ / (N : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]; ring
    change |ψ τ * ((j + 1 : ℕ) : ℝ) / (N : ℝ) - ψ τ * (j : ℝ) / (N : ℝ)| ≤ 2 / (N : ℝ)
    rw [h1, abs_div, abs_of_pos hNpos, div_le_div_iff_of_pos_right hNpos]
    exact hψbd τ
  have hlev_abs : ∀ j : ℕ, j ≤ N → ∀ τ : ℝ, |ℓ j τ| ≤ 2 := by
    intro j hj τ
    have hjN0 : (0 : ℝ) ≤ (j : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg j) hNpos.le
    have hjN : (j : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNpos]
      exact_mod_cast hj
    have habs : |ℓ j τ| = |ψ τ| * ((j : ℝ) / (N : ℝ)) := by
      change |ψ τ * (j : ℝ) / (N : ℝ)| = |ψ τ| * ((j : ℝ) / (N : ℝ))
      rw [abs_div, abs_mul, abs_of_pos hNpos,
        show |(j : ℝ)| = (j : ℝ) from abs_of_nonneg (Nat.cast_nonneg j)]
      ring
    rw [habs]
    calc |ψ τ| * ((j : ℝ) / (N : ℝ)) ≤ 2 * 1 :=
          mul_le_mul (hψbd τ) hjN hjN0 (by norm_num)
      _ = 2 := by norm_num
  have hlev_mem : ∀ j : ℕ, j ≤ N → ∀ τ : ℝ, ℓ j τ ∈ Icc (-2 : ℝ) 2 := by
    intro j hj τ
    exact ⟨by nlinarith [hlev_abs j hj τ, neg_abs_le (ℓ j τ)],
      by nlinarith [hlev_abs j hj τ, le_abs_self (ℓ j τ)]⟩
  have hsmall : ∀ (a b : ℝ), a ∈ Icc (-2 : ℝ) 2 → b ∈ Icc (-2 : ℝ) 2 → |a - b| < δ1 →
      ‖pr a - pr b‖ < 1 := fun a b ha hb h => hδ1 a ha b hb h
  have hstep_close : ∀ k : ℕ, k < N → ∀ τ : ℝ,
      ‖pr (ℓ (k + 1) τ) - pr (ℓ k τ)‖ < 1 := by
    intro k hk τ
    have hk1 : k + 1 ≤ N := by omega
    refine hsmall (ℓ (k + 1) τ) (ℓ k τ)
      (hlev_mem (k + 1) hk1 τ) (hlev_mem k (by omega) τ) ?_
    have h1 : ℓ (k + 1) τ - ℓ k τ = ψ τ / (N : ℝ) := by
      change ψ τ * ((k + 1 : ℕ) : ℝ) / (N : ℝ) - ψ τ * (k : ℝ) / (N : ℝ) = ψ τ / (N : ℝ)
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [h1, abs_div, abs_of_pos hNpos]
    have h2 : |ψ τ| / (N : ℝ) ≤ 2 / (N : ℝ) := by
      rw [div_le_div_iff_of_pos_right hNpos]
      exact hψbd τ
    linarith
  have hfac_inj : ∀ k : ℕ, k < N → ∀ τ : ℝ,
      Function.Injective ((1 - pr (ℓ (k + 1) τ) + pr (ℓ k τ) : E →L[ℝ] E)) := by
    intro k hk τ
    have h := hstep_close k hk τ
    have h' : ‖pr (ℓ k τ) - pr (ℓ (k + 1) τ)‖ < 1 := by rw [norm_sub_rev]; exact h
    exact small_step_injective h'
  have hfac_range : ∀ k : ℕ, k < N → ∀ τ : ℝ, ∀ y : E,
      y ∈ LinearMap.range (pr (ℓ (k + 1) τ) : E →ₗ[ℝ] E) →
      ((1 - pr (ℓ (k + 1) τ) + pr (ℓ k τ) : E →L[ℝ] E)) y
        ∈ LinearMap.range (pr (ℓ k τ) : E →ₗ[ℝ] E) := by
    intro k hk τ y hy
    exact small_step_mem_range (hidem (ℓ (k + 1) τ)) hy
  -- ## step 7: the range induction
  have hF : ∀ (τ : ℝ) (j : ℕ), j < N → ∀ y : E,
      y ∈ LinearMap.range (pr (ℓ (N - j) τ) : E →ₗ[ℝ] E) →
      ((1 - pr (ℓ (N - 1 - j + 1) τ) + pr (ℓ (N - 1 - j) τ) : E →L[ℝ] E)) y
        ∈ LinearMap.range (pr (ℓ (N - (j + 1)) τ) : E →ₗ[ℝ] E) := by
    intro τ j hj y hy
    have hy' : y ∈ LinearMap.range (pr (ℓ ((N - 1 - j) + 1) τ) : E →ₗ[ℝ] E) := by
      rw [show (N - 1 - j) + 1 = N - j from by omega]
      exact hy
    have := hfac_range (N - 1 - j) (by omega) τ y hy'
    simpa [show N - 1 - j = N - (j + 1) from by omega] using this
  have hstep_mem : ∀ (τ : ℝ) (j : ℕ), j ≤ N → ∀ (x : E),
      (marchFac (fun k => (1 - pr (ℓ (N - 1 - k + 1) τ) + pr (ℓ (N - 1 - k) τ)
        : E →L[ℝ] E)) j) ((pr (ℓ N τ)) x) ∈
        LinearMap.range (pr (ℓ (N - j) τ) : E →ₗ[ℝ] E) := by
    intro τ j hj x
    exact marchFac_mem (P := fun k => LinearMap.range (pr (ℓ k τ) : E →ₗ[ℝ] E))
      (fun k hk y hy => hF τ k hk y hy) j hj _ ⟨x, rfl⟩
  have hΛapp : ∀ (τ : ℝ) (x : E),
      (marchFac (fun k => (1 - pr (ℓ (N - 1 - k + 1) τ) + pr (ℓ (N - 1 - k) τ)
        : E →L[ℝ] E)) N) ((pr (ℓ N τ)) x) ∈
        LinearMap.range (pr (ℓ 0 τ) : E →ₗ[ℝ] E) := by
    intro τ x
    simpa using hstep_mem τ N le_rfl x
  -- ## step 8: the two families
  let Fac : ℝ → ℕ → E →L[ℝ] E := fun τ k => 1 - pr (ℓ (N - 1 - k + 1) τ) + pr (ℓ (N - 1 - k) τ)
  let Λ : ℝ → E →L[ℝ] E := fun τ => marchFac (Fac τ) N
  have hFac_sm : ∀ k : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun τ : ℝ => Fac τ k) := by
    intro k
    have h1 : ∀ c : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun τ : ℝ => pr (ψ τ * c / (N : ℝ))) := by
      intro c
      rw [contDiff_clm_apply_iff]
      intro y
      have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun τ : ℝ => (ψ τ * c / (N : ℝ), y)) :=
        (((hψsm.mul contDiff_const).div_const _).prodMk contDiff_const)
      exact hpr.comp h2
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun τ : ℝ => pr (ℓ (N - 1 - k + 1) τ)) :=
      h1 ((N - 1 - k + 1 : ℕ) : ℝ)
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun τ : ℝ => pr (ℓ (N - 1 - k) τ)) :=
      h1 ((N - 1 - k : ℕ) : ℝ)
    exact ((contDiff_const.sub h2).add h3)
  have hΛ_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Λ := by
    have h : ∀ j : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun τ : ℝ => marchFac (Fac τ) j) := by
      intro j
      induction j with
      | zero => simpa using contDiff_const
      | succ i ih =>
          have h1 : (fun τ : ℝ => marchFac (Fac τ) (i + 1))
              = fun τ : ℝ => Fac τ i * marchFac (Fac τ) i := by
            funext τ; rw [marchFac_succ]
          rw [h1]
          exact (hFac_sm i).clm_comp ih
    exact h N
  have hΛ_inj : ∀ τ : ℝ, Function.Injective (Λ τ) := by
    intro τ
    have h : ∀ j : ℕ, j ≤ N → Function.Injective (marchFac (Fac τ) j) := by
      intro j hj
      induction j with
      | zero => simpa using Function.injective_id
      | succ i ih =>
          have hi : i < N := by omega
          have h1 : (marchFac (Fac τ) (i + 1)) = Fac τ i * marchFac (Fac τ) i := marchFac_succ _ _
          rw [h1]
          exact (hfac_inj (N - 1 - i) (by omega) τ).comp (ih (by omega))
    exact h N le_rfl
  have hinv : ∀ τ : ℝ, (Λ τ).IsInvertible := by
    intro τ
    have hbij : Function.Bijective (Λ τ) :=
      ⟨hΛ_inj τ, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (rfl : Module.finrank ℝ E = Module.finrank ℝ E)).mp (hΛ_inj τ)⟩
    refine ⟨(LinearEquiv.ofBijective (Λ τ : E →ₗ[ℝ] E) hbij).toContinuousLinearEquiv, ?_⟩
    ext x
    rfl
  have hΛinv_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun τ : ℝ => ContinuousLinearMap.inverse (Λ τ)) := by
    rw [contDiff_iff_contDiffAt]
    intro τ
    exact (hinv τ).contDiffAt_map_inverse.comp τ hΛ_sm.contDiffAt
  refine ⟨Λ, fun τ => ContinuousLinearMap.inverse (Λ τ), hΛ_sm, hΛinv_sm, ?_, ?_, ?_⟩
  · intro τ y
    have h := congrArg (fun g : E →L[ℝ] E => g y) ((hinv τ).inverse_comp_self)
    simpa using h
  · intro τ y
    have h := congrArg (fun g : E →L[ℝ] E => g y) ((hinv τ).self_comp_inverse)
    simpa using h
  · intro τ hτ
    have hτψ : ψ τ = τ := hψid τ (by rw [abs_of_nonneg hτ.1]; exact hτ.2)
    have hℓ0 : ℓ 0 τ = 0 := by
      show ψ τ * ((0 : ℕ) : ℝ) / (N : ℝ) = 0
      simp
    have hℓN : ℓ N τ = τ := by
      show ψ τ * ((N : ℕ) : ℝ) / (N : ℝ) = τ
      rw [mul_div_assoc, div_self (ne_of_gt hNpos), mul_one]
      exact hτψ
    have hincl : LinearMap.range ((Λ τ).toLinearMap.comp (pr τ).toLinearMap)
        ≤ LinearMap.range (pr 0 : E →ₗ[ℝ] E) := by
      rintro y ⟨x, rfl⟩
      have h := hΛapp τ x
      rw [hℓN, hℓ0] at h
      simpa using h
    have hfr : Module.finrank ℝ ↥(LinearMap.range ((Λ τ).toLinearMap.comp (pr τ).toLinearMap))
        = Module.finrank ℝ ↥(LinearMap.range (pr τ : E →ₗ[ℝ] E)) := by
      have h1 : LinearMap.range ((Λ τ).toLinearMap.comp (pr τ).toLinearMap)
          = Submodule.map (Λ τ).toLinearMap (LinearMap.range (pr τ : E →ₗ[ℝ] E)) :=
        LinearMap.range_comp _ _
      rw [h1]
      exact (LinearEquiv.finrank_eq ((LinearMap.range (pr τ : E →ₗ[ℝ] E)).equivMapOfInjective
        (Λ τ).toLinearMap (hΛ_inj τ))).symm
    refine Submodule.eq_of_le_of_finrank_eq hincl ?_
    rw [hfr, hrank τ, ← hrank 0]


/-- The transport of `exists_transport_of_plane_family`, in the *jointly smooth* form consumed by
`Work.Whitney.CutPush.exists_collar_flattening_of_fiberFamily`. -/
theorem exists_transport_of_plane_family_joint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {k : ℕ}
    (pr : ℝ → E →L[ℝ] E)
    (hpr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => pr p.1 p.2))
    (hidem : ∀ t, pr t * pr t = pr t)
    (hrank : ∀ t : ℝ, Module.finrank ℝ (LinearMap.range (pr t : E →ₗ[ℝ] E)) = k) :
    ∃ (Λ Λinv : ℝ → E →L[ℝ] E),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => Λ p.1 p.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => Λinv p.1 p.2) ∧
      (∀ t y, Λinv t (Λ t y) = y) ∧ (∀ t y, Λ t (Λinv t y) = y) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        LinearMap.range ((Λ t).toLinearMap.comp (pr t).toLinearMap)
          = LinearMap.range (pr 0).toLinearMap) := by
  obtain ⟨Λ, Λinv, h1, h2, h3, h4, h5⟩ := exists_transport_of_plane_family pr hpr hidem hrank
  exact ⟨Λ, Λinv, (h1.comp contDiff_fst).clm_apply contDiff_snd,
    (h2.comp contDiff_fst).clm_apply contDiff_snd, h3, h4, h5⟩

end Work.Whitney.CutPush
