import Mathlib
import Submission.Model
import Submission.ModelCore
import Submission.ModelVarConv
import Submission.ModelUniq

/-!
# Two-point expansion estimate for the time-`ρ` slice flow map

Task: prove the final theorem `exp_two_point_bound` (fill in the proof).

## Setup

For a `C³` invertible metric family `g : E → Bilin E`, consider the geodesic first-order field
`V := odeField g : E × E → E × E`.  We are given a local flow `Φ` on the unit ball around the rest
point `z₀ := (x₀, 0)`, with window `Icc (-ρ) ρ`:

  * `hΦ₀`: for `z ∈ closedBall z₀ 1`: `Φ z 0 = z` and `HasDerivAt (Φ z) (V (Φ z t)) t` for
    `t ∈ Icc (-ρ) ρ`;
  * `hCont`: for `z ∈ closedBall z₀ 1` and `t ∈ Icc 0 ρ`, the trajectory stays in `closedBall z₀ 2`;
  * `hLip`: for each `t ∈ Icc (-ρ) ρ`, `LipschitzOnWith Lf (fun z => Φ z t) (closedBall z₀ 1)`;
  * `hVLip`: `LipschitzOnWith K V (closedBall z₀ 2)` (available e.g. from
    `Submission.Model.field_lipschitzOn` in Submission/ExpFieldLip.lean, or reprove).

For `u, v` in `closedBall 0 ρ` define the two slice-flow endpoints
`z_u(t) := Φ (x₀, (1/ρ) • u) t`, `z_v(t) := Φ (x₀, (1/ρ) • v) t`.  Their initial data lie in
`closedBall z₀ 1` since `‖(0, u/ρ)‖ = ‖u‖/ρ ≤ 1`.

## Claim (what to prove)

    ‖((Φ (x₀,(1/ρ)•u) ρ).1 - (Φ (x₀,(1/ρ)•v) ρ).1) - (u - v)‖ ≤ ((K : ℝ) * (Lf : ℝ) * ρ) * ‖u - v‖

for all `u, v ∈ closedBall 0 ρ`.

## Proof outline

Let `a := u/ρ`, `b := v/ρ`, `w := (u - v)/ρ`.  Define the difference curve
`Δ(t) := z_u(t) - z_v(t)` and remove the linear part:
`q(t) := Δ(t) - (t • w, w)` (a pair: first component `t • w`, second `w`).  Then:

* `q(0) = 0`;
* first component: `q₁' = q₂` (because `V(z).1 = z.2`);
* second component: `q₂' = V₂(z_u) - V₂(z_v)` where `V₂(z) := (V z).2`; since `V₂ = snd ∘ V`
  is `K`-Lipschitz on `closedBall z₀ 2` and both trajectories stay there (`hCont`),
  `‖q₂'(t)‖ ≤ K ‖Δ(t)‖`;
* the flow Lipschitz bound gives `‖Δ(t)‖ ≤ Lf * ‖a - b‖ = Lf * ‖u - v‖/ρ` for `t ∈ Icc 0 ρ`
  (`hLip`, both initial data in the unit ball);
* hence `‖q₂'(t)‖ ≤ (K * Lf * ‖u - v‖ / ρ)` on `[0, ρ]`; since `q₂(0) = 0`, fencing gives
  `‖q₂(t)‖ ≤ (K * Lf * ‖u - v‖ / ρ) * t`, and then `‖q₁(ρ)‖ = ‖q₁(ρ) - q₁(0)‖ =
  ‖∫₀^ρ q₂‖ ≤ (K*Lf*‖u-v‖/ρ) * ρ²  ≤  K*Lf*ρ*‖u-v‖`.

  The first component at `t = ρ` is exactly the claimed expression, since
  `q₁(ρ) = (Φ (x₀,a) ρ).1 - (Φ (x₀,b) ρ).1 - ρ w` and `ρ w = u - v`.

Fencing tools (Mathlib, `Analysis/Calculus/MeanValue.lean`):

* `norm_image_sub_le_of_norm_deriv_le_segment' {f' : ℝ → E} {C : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ C) : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a)`
* for a *nonconstant* bound use `image_norm_le_of_norm_deriv_right_le_deriv_boundary` or integrate:
  `‖∫ τ in a..b, g τ‖ ≤ ∫ τ in a..b, ‖g τ‖` (intervalIntegral facts).
  Since the second bound has the form `‖q₂(t)‖ ≤ c * t`, you can either integrate twice or use
  the fencing theorem with bounding function `B(t) := c * t` for `q₂` and then with
  `B(t) := c * t^2 / 2` for `q₁` (there is `image_norm_le_of_norm_deriv_right_le_deriv_boundary`
  which takes `B` with `HasDerivAt B (B' x) x` for all `x` and `‖f' x‖ ≤ B' x`).

Derivative facts you need: `Δ` and `q` are differentiable on `[0,ρ]` with the derivatives above,
because each `z_u` has `HasDerivAt` at every `t ∈ Icc (-ρ) ρ` (`hΦ₀`).  Convert
`HasDerivAt` to `HasDerivWithinAt` on `Icc 0 ρ` as needed.

## Hints

* Norm on `E × E` is the sup norm: `‖(a, b)‖ = max ‖a‖ ‖b‖`; in particular
  `‖x.1‖ ≤ ‖x‖`, `‖x.2‖ ≤ ‖x‖` (`norm_fst_le`, `norm_snd_le`), and
  `‖(x₁, x₂) - (y₁, y₂)‖ = ‖(x₁ - y₁, x₂ - y₂)‖`.
* Membership: `mem_closedBall`, `mem_Icc`, `dist_eq_norm`.
* You may find it cleanest to introduce helper lemmas inside this file.

Do NOT change the statement.  You may add helper lemmas.  No gaps or axioms may remain.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric Filter

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- Two-point expansion estimate for the time-`ρ` slice map of the geodesic flow. -/
lemma exp_two_point_bound (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) (ρ : ℝ) (hρ : 0 < ρ)
    (Lf K : NNReal) (Φ : (E × E) → ℝ → (E × E))
    (hΦ₀ : ∀ z ∈ closedBall (x₀, 0) (1 : ℝ), Φ z 0 = z ∧
       ∀ t ∈ Icc (-ρ) ρ, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    (hCont : ∀ z ∈ closedBall (x₀, 0) (1 : ℝ), ∀ t ∈ Icc 0 ρ,
       Φ z t ∈ closedBall (x₀, 0) (2 : ℝ))
    (hLip : ∀ t ∈ Icc (-ρ) ρ,
       LipschitzOnWith Lf (fun z => Φ z t) (closedBall (x₀, 0) (1 : ℝ)))
    (hVLip : LipschitzOnWith K (odeField g) (closedBall (x₀, 0) (2 : ℝ))) :
    ∀ u v : E, u ∈ closedBall (0 : E) ρ → v ∈ closedBall (0 : E) ρ →
      ‖((Φ (x₀, (1 / ρ) • u) ρ).1 - (Φ (x₀, (1 / ρ) • v) ρ).1) - (u - v)‖ ≤
        ((K : ℝ) * (Lf : ℝ) * ρ) * ‖u - v‖ := by
  intro u v hu hv
  let a : E := (1 / ρ) • u
  let b : E := (1 / ρ) • v
  let w : E := a - b
  let V : E × E → E × E := odeField g
  let zu : ℝ → E × E := fun t => Φ (x₀, a) t
  let zv : ℝ → E × E := fun t => Φ (x₀, b) t
  let q₁ : ℝ → E := fun t => (zu t - zv t).1 - t • w
  let r₂ : ℝ → E := fun t => (zu t).2 - (zv t).2
  let f2 : ℝ → E := fun t => (V (zu t)).2 - (V (zv t)).2
  let C2 : ℝ := (K : ℝ) * (Lf : ℝ) * ‖a - b‖
  have hu_norm : ‖u‖ ≤ ρ := by
    rw [mem_closedBall, dist_eq_norm] at hu
    simpa using hu
  have hv_norm : ‖v‖ ≤ ρ := by
    rw [mem_closedBall, dist_eq_norm] at hv
    simpa using hv
  have ha_norm : ‖a‖ ≤ 1 := by
    dsimp [a]
    calc
      ‖(1 / ρ) • u‖ = ‖(1 / ρ)‖ * ‖u‖ := by rw [norm_smul]
      _ = (1 / ρ) * ‖u‖ := by rw [Real.norm_of_nonneg (by positivity : 0 ≤ (1 / ρ : ℝ))]
      _ ≤ (1 / ρ) * ρ := by exact mul_le_mul_of_nonneg_left hu_norm (by positivity : 0 ≤ (1 / ρ : ℝ))
      _ = 1 := by field_simp [hρ.ne']
  have hb_norm : ‖b‖ ≤ 1 := by
    dsimp [b]
    calc
      ‖(1 / ρ) • v‖ = ‖(1 / ρ)‖ * ‖v‖ := by rw [norm_smul]
      _ = (1 / ρ) * ‖v‖ := by rw [Real.norm_of_nonneg (by positivity : 0 ≤ (1 / ρ : ℝ))]
      _ ≤ (1 / ρ) * ρ := by exact mul_le_mul_of_nonneg_left hv_norm (by positivity : 0 ≤ (1 / ρ : ℝ))
      _ = 1 := by field_simp [hρ.ne']
  have hza_mem : (x₀, a) ∈ closedBall (x₀, 0) (1 : ℝ) := by
    rw [mem_closedBall, dist_eq_norm]
    have h : ‖(x₀, a) - (x₀, 0)‖ = ‖a‖ := by simp
    rwa [h]
  have hzb_mem : (x₀, b) ∈ closedBall (x₀, 0) (1 : ℝ) := by
    rw [mem_closedBall, dist_eq_norm]
    have h : ‖(x₀, b) - (x₀, 0)‖ = ‖b‖ := by simp
    rwa [h]
  have hzu_d (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) : HasDerivAt zu (V (zu t)) t := by
    simpa [V, zu] using (hΦ₀ (x₀, a) hza_mem).2 t ht
  have hzv_d (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) : HasDerivAt zv (V (zv t)) t := by
    simpa [V, zv] using (hΦ₀ (x₀, b) hzb_mem).2 t ht
  have hzu1 (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) : HasDerivAt (fun s : ℝ => (zu s).1) ((zu t).2) t := by
    have hf := (hzu_d t ht).hasFDerivAt.fst.hasDerivAt
    simpa [V, odeField] using hf
  have hzv1 (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) : HasDerivAt (fun s : ℝ => (zv s).1) ((zv t).2) t := by
    have hf := (hzv_d t ht).hasFDerivAt.fst.hasDerivAt
    simpa [V, odeField] using hf
  have hzu2 (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) : HasDerivAt (fun s : ℝ => (zu s).2) (V (zu t)).2 t := by
    have hf := (hzu_d t ht).hasFDerivAt.snd.hasDerivAt
    simpa [V] using hf
  have hzv2 (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) : HasDerivAt (fun s : ℝ => (zv s).2) (V (zv t)).2 t := by
    have hf := (hzv_d t ht).hasFDerivAt.snd.hasDerivAt
    simpa [V] using hf
  have hr2_d (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) : HasDerivAt r₂ (f2 t) t := by
    change HasDerivAt (fun s : ℝ => (zu s).2 - (zv s).2) ((V (zu t)).2 - (V (zv t)).2) t
    exact (hzu2 t ht).sub (hzv2 t ht)
  have hq1_d (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) :
      HasDerivAt q₁ ((zu t).2 - (zv t).2 - w) t := by
    change HasDerivAt (fun s : ℝ => (zu s - zv s).1 - s • w) ((zu t).2 - (zv t).2 - w) t
    have h1 := (hzu1 t ht).sub (hzv1 t ht)
    have hlin : HasDerivAt (fun s : ℝ => s • w) w t := by
      simpa using (hasDerivAt_id t).smul_const w
    exact h1.sub hlin
  have hzu0 : zu 0 = (x₀, a) := by
    simpa [zu] using (hΦ₀ (x₀, a) hza_mem).1
  have hzv0 : zv 0 = (x₀, b) := by
    simpa [zv] using (hΦ₀ (x₀, b) hzb_mem).1
  have hq10 : q₁ 0 = 0 := by
    dsimp [q₁]
    rw [hzu0, hzv0]
    simp
  have hr2_0 : r₂ 0 = w := by
    dsimp [r₂]
    rw [hzu0, hzv0]
  have hC2bnd : ∀ x ∈ Ico 0 ρ, ‖f2 x‖ ≤ C2 := by
    intro x hx
    have hxI : x ∈ Icc 0 ρ := ⟨hx.1, le_of_lt hx.2⟩
    have hxρ : x ∈ Icc (-ρ) ρ := ⟨by linarith [hx.1, hρ], le_of_lt hx.2⟩
    have hzuIn : Φ (x₀, a) x ∈ closedBall (x₀, 0) (2 : ℝ) := hCont (x₀, a) hza_mem x hxI
    have hzvIn : Φ (x₀, b) x ∈ closedBall (x₀, 0) (2 : ℝ) := hCont (x₀, b) hzb_mem x hxI
    have hzud : ‖Φ (x₀, a) x - Φ (x₀, b) x‖ ≤ (Lf : ℝ) * ‖a - b‖ := by
      simpa [dist_eq_norm] using (hLip x hxρ).dist_le_mul (x₀, a) hza_mem (x₀, b) hzb_mem
    have hvd : ‖V (Φ (x₀, a) x) - V (Φ (x₀, b) x)‖ ≤ (K : ℝ) * ‖Φ (x₀, a) x - Φ (x₀, b) x‖ := by
      simpa [dist_eq_norm] using
        (hVLip.dist_le_mul (Φ (x₀, a) x) hzuIn (Φ (x₀, b) x) hzvIn)
    calc
      ‖f2 x‖ ≤ ‖V (Φ (x₀, a) x) - V (Φ (x₀, b) x)‖ := by
        dsimp [f2]
        simpa using norm_snd_le (V (Φ (x₀, a) x) - V (Φ (x₀, b) x))
      _ ≤ (K : ℝ) * ‖Φ (x₀, a) x - Φ (x₀, b) x‖ := hvd
      _ ≤ (K : ℝ) * ((Lf : ℝ) * ‖a - b‖) := by
        exact mul_le_mul_of_nonneg_left hzud (by positivity : 0 ≤ (K : ℝ))
      _ = C2 := by
        dsimp [C2]
        ring
  have hr2_bound : ∀ x ∈ Icc 0 ρ, ‖r₂ x - r₂ 0‖ ≤ C2 * x := by
    intro x hx
    have hderw : ∀ y ∈ Icc 0 ρ, HasDerivWithinAt r₂ (f2 y) (Icc 0 ρ) y := by
      intro y hy
      have hyρ : y ∈ Icc (-ρ) ρ := ⟨by linarith [hy.1, hρ], hy.2⟩
      exact (hr2_d y hyρ).hasDerivWithinAt
    have hfence := (norm_image_sub_le_of_norm_deriv_le_segment' (f := r₂) (f' := f2)
      (a := 0) (b := ρ) hderw hC2bnd) x hx
    simpa using hfence
  have hC2ge0 : 0 ≤ C2 := by
    dsimp [C2]
    positivity
  have hq1_rho : ‖q₁ ρ‖ ≤ C2 * ρ ^ 2 := by
    let B : ℝ → ℝ := fun x => C2 * x ^ 2
    let B' : ℝ → ℝ := fun x => 2 * C2 * x
    have hB (x : ℝ) : HasDerivAt B (B' x) x := by
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have hcc := hsq.const_mul C2
      have heq : C2 * (2 * x) = 2 * C2 * x := by ring
      simpa [B, B', heq] using hcc
    have hf1 : ContinuousOn q₁ (Icc 0 ρ) := by
      exact HasDerivAt.continuousOn (s := Icc 0 ρ) (fun x hx => hq1_d x (by
        exact ⟨by linarith [hx.1, hρ], hx.2⟩))
    have hf1' : ∀ x ∈ Ico 0 ρ, HasDerivWithinAt q₁ ((zu x).2 - (zv x).2 - w) (Ici x) x := by
      intro x hx
      have hxρ : x ∈ Icc (-ρ) ρ := ⟨by linarith [hx.1, hρ], le_of_lt hx.2⟩
      exact (hq1_d x hxρ).hasDerivWithinAt
    have ha : ‖q₁ 0‖ ≤ B 0 := by
      simp [B, hq10]
    have hbnd : ∀ x ∈ Ico 0 ρ, ‖(zu x).2 - (zv x).2 - w‖ ≤ B' x := by
      intro x hx
      have hxI : x ∈ Icc 0 ρ := ⟨hx.1, le_of_lt hx.2⟩
      -- ‖(zu x).2 - (zv x).2 - w‖ = ‖r₂ x - w‖ ≤ ‖r₂ x - r₂ 0‖ + 0 ...
      have hvr : (zu x).2 - (zv x).2 - w = r₂ x - r₂ 0 := by
        rw [← hr2_0]
      have hb := hr2_bound x hxI
      have hmain : ‖r₂ x - r₂ 0‖ ≤ C2 * x := by simpa using hb
      rw [hvr]
      have hx0 : 0 ≤ x := hx.1
      have hle : C2 * x ≤ 2 * C2 * x := by
        nlinarith [hC2ge0, hx0]
      exact le_trans hmain hle
    have hres := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := q₁) (f' := fun x => (zu x).2 - (zv x).2 - w) (a := 0) (b := ρ) (B := B) (B' := B')
      hf1 hf1' ha hB hbnd
    have hres' := hres (right_mem_Icc.mpr (le_of_lt hρ))
    simpa [B] using hres'
  have hnormab : ‖a - b‖ = ‖u - v‖ / ρ := by
    dsimp [a, b]
    rw [← smul_sub]
    calc
      ‖(1 / ρ) • (u - v)‖ = ‖(1 / ρ)‖ * ‖u - v‖ := by rw [norm_smul]
      _ = (1 / ρ) * ‖u - v‖ := by rw [Real.norm_of_nonneg (by positivity : 0 ≤ (1 / ρ : ℝ))]
      _ = ‖u - v‖ / ρ := by ring
  have hq1rho_ub : ‖q₁ ρ‖ ≤ (K : ℝ) * (Lf : ℝ) * ρ * ‖u - v‖ := by
    calc
      ‖q₁ ρ‖ ≤ C2 * ρ ^ 2 := hq1_rho
      _ = (K : ℝ) * (Lf : ℝ) * ρ * ‖u - v‖ := by
        dsimp [C2]
        rw [hnormab]
        field_simp [hρ.ne']
  have hρw : ρ • w = u - v := by
    dsimp [w, a, b]
    rw [smul_sub]
    rw [smul_smul, smul_smul]
    have hm : ρ * (1 / ρ) = 1 := by field_simp [hρ.ne']
    rw [hm]
    simp
  have hq1rho_eq : q₁ ρ = ((Φ (x₀, (1 / ρ) • u) ρ).1 - (Φ (x₀, (1 / ρ) • v) ρ).1) - (u - v) := by
    dsimp [q₁, zu, zv]
    rw [hρw]
  rw [← hq1rho_eq]
  exact hq1rho_ub

end

end Submission.Model
