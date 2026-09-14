import Submission.NBody.MinimizerEndpoint
import Submission.NBody.LimitShape
import Submission.NBody.MadernaEstimate

/-!
# The approximation of a calibrating curve by `h`-minimisers

Maderna--Venturelli approximate the calibrating curve `γ` of a horofunction directed by `a` by the
`h`-minimisers `γ_k` from `q₀ = γ 1` to `p k`, where `p k = λ_k • a` is the sequence defining the
horofunction.  This module sets up that approximation:

* `exists_tau_minimizer_to` : the minimisers exist for all large `k`;
* `tau_lower_bound` / `tau_tendsto_atTop` : their travel times `τ_k` tend to `+∞`;
* `action_lt_of_uniform_bound` and `exists_uniform_action_bound` : the action of `γ_k` restricted
  to a fixed `[0,T]` is uniformly bounded;
* `exists_uniformly_convergent_subseq` : Arzelà--Ascoli extraction of a uniformly convergent
  subsequence on `[0,T]`.

The *identification* of the limit (the calibration limit and the concatenation argument) and the
conclusion `γ̇_k(0) → γ̇(1)` are the next steps.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## Existence of the minimisers -/

/-- For all sufficiently large `k` the configurations `q₀` and `p k` differ, so that an
`h`-minimiser joining them exists (Tonelli's theorem, dimension `≥ 2`). -/
lemma exists_minimizer_to {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hdim : 2 ≤ Module.finrank ℝ E) {q0 : EN E N} (hq0 : WithoutCollisions q0)
    {p : ℕ → EN E N} (hpnc : ∀ k, WithoutCollisions (p k))
    (hpgrow : Tendsto (fun k => ‖p k‖) atTop atTop) :
    ∀ᶠ k : ℕ in atTop, ∃ (τ : ℝ) (γk : ℝ → EN E N), 0 < τ ∧ γk 0 = q0 ∧ γk τ = p k ∧
      AbsolutelyContinuousOnInterval γk 0 τ ∧ IsHMinimizer m h γk 0 τ := by
  have hev : ∀ᶠ k : ℕ in atTop, q0 ≠ p k := by
    have h2 : ∀ᶠ k : ℕ in atTop, ‖q0‖ < ‖p k‖ := hpgrow.eventually (eventually_gt_atTop ‖q0‖)
    filter_upwards [h2] with k hk h
    rw [h] at hk
    exact absurd hk (lt_irrefl _)
  filter_upwards [hev] with k hk
  obtain ⟨τ, hτ, γk, h0, h1, hac, hEq⟩ :=
    exists_minimizer_of_avoiding hm hh hdim hk hq0 (hpnc k)
  refine ⟨τ, γk, hτ, h0, h1, hac, ?_⟩
  show actionOn m h γk 0 τ = actionPot m h (γk 0) (γk τ)
  rw [h0, h1]
  exact hEq

/-! ## The travel times tend to infinity -/

/-- **The travel time of an `h`-minimiser.** -/
lemma tau_lower_bound {m : Fin N → ℝ} {h : ℝ} {α β c : ℝ} {q0 p : EN E N} {τ : ℝ}
    {γk : ℝ → EN E N}
    (hτ : 0 < τ) (h0 : γk 0 = q0) (h1 : γk τ = p)
    (hac : AbsolutelyContinuousOnInterval γk 0 τ) (hmin : IsHMinimizer m h γk 0 τ)
    (hc : 0 < c) (hmc : ∀ i, c ≤ m i) (hh : 0 ≤ h)
    (hα : 0 < α) (hβ : 0 < β)
    (hest : ∀ x y : EN E N, actionPot m h x y ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2))) :
    (1 / 2) * c * ‖q0 - p‖ ^ 2 / (Real.sqrt (α + h * β) * (1 + ‖q0 - p‖)) ≤ τ := by
  have hCpos : 0 < Real.sqrt (α + h * β) :=
    Real.sqrt_pos.mpr (by nlinarith [hα, hβ, hh, mul_nonneg hh hβ.le])
  have hup : ∀ r : ℝ, 0 ≤ r →
      Real.sqrt (α * r + h * β * r ^ 2) ≤ Real.sqrt (α + h * β) * (1 + r) := by
    intro r hr0
    have h1 : α * r + h * β * r ^ 2 ≤ (α + h * β) * (1 + r) ^ 2 := by
      nlinarith [hr0, hα, hβ, hh, mul_nonneg hh hβ.le, mul_nonneg hα.le hr0,
        mul_nonneg (mul_nonneg hh hβ.le) hr0]
    calc Real.sqrt (α * r + h * β * r ^ 2) ≤ Real.sqrt ((α + h * β) * (1 + r) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (α + h * β) * (1 + r) := by
          rw [Real.sqrt_mul (x := α + h * β) (show (0:ℝ) ≤ α + h * β by
              nlinarith [hα, hβ, hh, mul_nonneg hh hβ.le])]
          rw [Real.sqrt_sq (show (0:ℝ) ≤ 1 + r by linarith)]
  have hbdd : ∀ x y : EN E N, actionPot m h x y ≤
      ENNReal.ofReal (Real.sqrt (α + h * β) * (1 + ‖x - y‖)) := fun x y =>
    (hest x y).trans (ENNReal.ofReal_le_ofReal (hup ‖x - y‖ (norm_nonneg _)))
  have hden : (0 : ℝ) < Real.sqrt (α + h * β) * (1 + ‖q0 - p‖) :=
    mul_pos hCpos (by linarith [norm_nonneg (q0 - p)])
  have hle := IsHMinimizer.ofReal_tau_le hac h0 h1 hmin hc hmc hh hτ
  have hA : ENNReal.ofReal ((1 / 2) * c * ‖q0 - p‖ ^ 2 / τ + h * τ)
      ≤ ENNReal.ofReal (Real.sqrt (α + h * β) * (1 + ‖q0 - p‖)) :=
    hle.trans (hbdd q0 p)
  have hstep : (1 / 2) * c * ‖q0 - p‖ ^ 2 / τ + h * τ
      ≤ Real.sqrt (α + h * β) * (1 + ‖q0 - p‖) :=
    (ENNReal.ofReal_le_ofReal_iff (le_of_lt hden)).mp hA
  have h1 : (1 / 2) * c * ‖q0 - p‖ ^ 2 / τ ≤ Real.sqrt (α + h * β) * (1 + ‖q0 - p‖) := by
    have hpos : 0 ≤ h * τ := mul_nonneg hh hτ.le
    linarith
  rw [div_le_iff₀ hden]
  calc (1 / 2) * c * ‖q0 - p‖ ^ 2
      ≤ (Real.sqrt (α + h * β) * (1 + ‖q0 - p‖)) * τ := (div_le_iff₀ hτ).mp h1
    _ = τ * (Real.sqrt (α + h * β) * (1 + ‖q0 - p‖)) := mul_comm _ _

/-! ## The travel times tend to infinity -/

/-- If the target configurations escape to infinity then so do the travel times of the minimisers. -/
lemma tau_tendsto_atTop {m : Fin N → ℝ} {h : ℝ} {α β c : ℝ} {q0 : EN E N}
    {p : ℕ → EN E N} {τ : ℕ → ℝ} {γs : ℕ → ℝ → EN E N}
    (hτ : ∀ k, 0 < τ k) (h0 : ∀ k, γs k 0 = q0) (h1 : ∀ k, γs k (τ k) = p k)
    (hac : ∀ k, AbsolutelyContinuousOnInterval (γs k) 0 (τ k))
    (hmin : ∀ k, IsHMinimizer m h (γs k) 0 (τ k))
    (hc : 0 < c) (hmc : ∀ i, c ≤ m i) (hh : 0 ≤ h)
    (hα : 0 < α) (hβ : 0 < β)
    (hest : ∀ x y : EN E N, actionPot m h x y ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2)))
    (hpgrow : Tendsto (fun k => ‖p k‖) atTop atTop) :
    Tendsto τ atTop atTop := by
  have hCpos : 0 < Real.sqrt (α + h * β) :=
    Real.sqrt_pos.mpr (by nlinarith [hα, hβ, hh, mul_nonneg hh hβ.le])
  -- the distances escape
  have hpnorm : Tendsto (fun k => ‖p k - q0‖) atTop atTop := by
    rw [tendsto_atTop_atTop] at hpgrow ⊢
    intro b
    obtain ⟨K, hK⟩ := hpgrow (b + ‖q0‖)
    exact ⟨K, fun k hk => by
      have h2 := hK k hk
      calc b ≤ ‖p k‖ - ‖q0‖ := by linarith
        _ ≤ ‖p k - q0‖ := by
            have h3 := norm_add_le (p k - q0) q0
            simp only [sub_add_cancel] at h3
            linarith⟩
  -- the lower bound grows
  have hgrowth : Tendsto (fun k => c * ‖p k - q0‖ / (4 * Real.sqrt (α + h * β))) atTop atTop := by
    have hpos : 0 < c / (4 * Real.sqrt (α + h * β)) := div_pos hc (by positivity)
    have := hpnorm.const_mul_atTop hpos
    refine this.congr' ?_
    filter_upwards with k
    rw [div_eq_mul_inv]
    ring
  refine tendsto_atTop_mono' atTop ?_ hgrowth
  filter_upwards [hpnorm.eventually_ge_atTop 1] with k hk
  have hlow := tau_lower_bound (hτ k) (h0 k) (h1 k) (hac k) (hmin k) hc hmc hh hα hβ hest
  have hden : (0 : ℝ) < Real.sqrt (α + h * β) * (1 + ‖q0 - p k‖) :=
    mul_pos hCpos (by have h := norm_nonneg (q0 - p k); linarith)
  rw [div_le_iff₀ hden] at hlow
  have hdist : ‖q0 - p k‖ = ‖p k - q0‖ := norm_sub_rev _ _
  rw [hdist] at hlow
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * Real.sqrt (α + h * β))]
  have hXpos : 0 < ‖p k - q0‖ := by linarith
  -- from the lower bound at `r = ‖p k - q0‖`
  have hden2 : (0 : ℝ) < 2 * Real.sqrt (α + h * β) * ‖p k - q0‖ := by positivity
  have h2 : (c * ‖p k - q0‖) * (2 * Real.sqrt (α + h * β) * ‖p k - q0‖)
      ≤ (τ k * (4 * Real.sqrt (α + h * β))) * (2 * Real.sqrt (α + h * β) * ‖p k - q0‖) := by
    have h1r : 1 + ‖p k - q0‖ ≤ 2 * ‖p k - q0‖ := by linarith
    have hA : Real.sqrt (α + h * β) * (1 + ‖p k - q0‖)
        ≤ Real.sqrt (α + h * β) * (2 * ‖p k - q0‖) :=
      mul_le_mul_of_nonneg_left h1r hCpos.le
    have hB : τ k * (Real.sqrt (α + h * β) * (1 + ‖p k - q0‖))
        ≤ τ k * (Real.sqrt (α + h * β) * (2 * ‖p k - q0‖)) :=
      mul_le_mul_of_nonneg_left hA (hτ k).le
    nlinarith [hlow, hB]
  exact le_of_mul_le_mul_right h2 hden2

/-! ## The uniform bound on the action of a fixed time interval -/

/-- Elementary: `X² ≤ K(1+X)` with `K ≥ 0` gives `X ≤ max 1 (2K)`. -/
lemma le_max_one_two_mul {X K : ℝ} (hK : 0 ≤ K) (h : X ^ 2 ≤ K * (1 + X)) :
    X ≤ max 1 (2 * K) := by
  rcases le_total X 1 with h1 | h1
  · exact h1.trans (le_max_left _ _)
  · have h2 : X * X ≤ X * (2 * K) := by nlinarith [h, h1, hK]
    exact (le_of_mul_le_mul_left h2 (by linarith)).trans (le_max_right _ _)

/-- **Uniform bound on the action over a fixed interval.**  On `[0,T]` the minimisers `γ_k` have
uniformly bounded action; consequently their configurations on `[0,T]` stay in a fixed ball and the
family is uniformly Hölder continuous. -/
lemma exists_uniform_action_bound {m : Fin N → ℝ} {h : ℝ} {α β c : ℝ} {q0 : EN E N}
    {p : ℕ → EN E N} {τ : ℕ → ℝ} {γs : ℕ → ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 ≤ h)
    (hτ : ∀ k, 0 < τ k) (h0 : ∀ k, γs k 0 = q0) (h1 : ∀ k, γs k (τ k) = p k)
    (hac : ∀ k, AbsolutelyContinuousOnInterval (γs k) 0 (τ k))
    (hmin : ∀ k, IsHMinimizer m h (γs k) 0 (τ k))
    (hc : 0 < c) (hmc : ∀ i, c ≤ m i)
    (hα : 0 < α) (hβ : 0 < β)
    (hest : ∀ x y : EN E N, actionPot m h x y ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2)))
    (hτtop : Tendsto τ atTop atTop) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, ∀ᶠ k in atTop, actionOn m h (γs k) 0 T ≤ ENNReal.ofReal C := by
  have hCpos : 0 < Real.sqrt (α + h * β) :=
    Real.sqrt_pos.mpr (by nlinarith [hα, hβ, hh, mul_nonneg hh hβ.le])
  have hup : ∀ r : ℝ, 0 ≤ r →
      Real.sqrt (α * r + h * β * r ^ 2) ≤ Real.sqrt (α + h * β) * (1 + r) := by
    intro r hr0
    have h1 : α * r + h * β * r ^ 2 ≤ (α + h * β) * (1 + r) ^ 2 := by
      nlinarith [hr0, hα, hβ, hh, mul_nonneg hh hβ.le, mul_nonneg hα.le hr0,
        mul_nonneg (mul_nonneg hh hβ.le) hr0]
    calc Real.sqrt (α * r + h * β * r ^ 2) ≤ Real.sqrt ((α + h * β) * (1 + r) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (α + h * β) * (1 + r) := by
          rw [Real.sqrt_mul (x := α + h * β) (show (0:ℝ) ≤ α + h * β by
                nlinarith [hα, hβ, hh, mul_nonneg hh hβ.le])]
          rw [Real.sqrt_sq (show (0:ℝ) ≤ 1 + r by linarith)]
  have hK0 : 0 ≤ 2 * T * Real.sqrt (α + h * β) / c :=
    div_nonneg (by positivity) hc.le
  refine ⟨Real.sqrt (α + h * β) * (1 + max 1 (2 * (2 * T * Real.sqrt (α + h * β) / c))), ?_⟩
  filter_upwards [hτtop.eventually_gt_atTop T] with k hk
  have hfin : actionPot m h (γs k 0) (γs k (τ k)) < ⊤ := by
    rw [h0 k, h1 k]; exact lt_of_le_of_lt (hest q0 (p k)) ENNReal.ofReal_lt_top
  have hminT : IsHMinimizer m h (γs k) 0 T :=
    IsHMinimizer.sub_left (hac k) (hmin k) (IsHMinimizer.actionOn_lt_top (hmin k) hfin) hT hk
  have hA : actionOn m h (γs k) 0 T = actionPot m h (γs k 0) (γs k T) := hminT
  rw [hA, h0 k]
  refine (hest q0 (γs k T)).trans (ENNReal.ofReal_le_ofReal ?_)
  set X : ℝ := ‖q0 - γs k T‖ with hX
  have hX0 : 0 ≤ X := norm_nonneg _
  -- the time estimate
  have hacT : AbsolutelyContinuousOnInterval (γs k) 0 T :=
    (hac k).mono (by
      rw [uIcc_of_le hT.le, uIcc_of_le (hτ k).le]
      exact Set.Icc_subset_Icc le_rfl hk.le)
  have hle := IsHMinimizer.ofReal_tau_le (γ := γs k) (τ := T) (x := q0) (y := γs k T)
    hacT (h0 k) rfl hminT hc hmc hh hT
  rw [← hX] at hle
  have hstep : (1 / 2) * c * X ^ 2 / T + h * T ≤ Real.sqrt (α * X + h * β * X ^ 2) :=
    (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg (α * X + h * β * X ^ 2))).mp
      (hle.trans (hest q0 (γs k T)))
  have hK : X ^ 2 ≤ (2 * T * Real.sqrt (α + h * β) / c) * (1 + X) := by
    have h2 : (1 / 2) * c * X ^ 2 / T ≤ Real.sqrt (α + h * β) * (1 + X) := by
      have h3 := hup X hX0
      have h4 : 0 ≤ h * T := mul_nonneg hh hT.le
      linarith
    have h5 : (2 * T / c) * ((1 / 2) * c * X ^ 2 / T)
        ≤ (2 * T / c) * (Real.sqrt (α + h * β) * (1 + X)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h6 : (2 * T / c) * ((1 / 2) * c * X ^ 2 / T) = X ^ 2 := by
      field_simp; try ring
    have h7 : (2 * T / c) * (Real.sqrt (α + h * β) * (1 + X))
        = (2 * T * Real.sqrt (α + h * β) / c) * (1 + X) := by ring
    rw [h6, h7] at h5
    exact h5
  refine (hup X hX0).trans ?_
  have hXb := le_max_one_two_mul hK0 hK
  exact mul_le_mul_of_nonneg_left (by linarith) hCpos.le

/-! ## The uniform `L²` bound and the Arzelà--Ascoli extraction -/

/-- The integral of the kinetic energy is bounded by the action. -/
lemma lintegral_ofReal_kinetic_le_actionOn {m : Fin N → ℝ} {h : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h) (γ : ℝ → EN E N) (a b : ℝ) :
    (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (kinetic m (deriv γ t))) ≤ actionOn m h γ a b := by
  rw [actionOn]
  exact lintegral_mono fun t => by
    by_cases hc : WithoutCollisions (γ t)
    · exact ofReal_kinetic_le_lagrangian hm hh hc (deriv γ t)
    · rw [lagrangian, if_neg hc]; exact le_top

/-- **Arzelà--Ascoli extraction for the approximating minimisers.**  A family of curves with a
uniform bound on the action on `[0,T]` has a subsequence converging uniformly on `[0,T]`; its
limit is absolutely continuous and starts at `q₀`. -/
lemma exists_uniform_subseq_of_action_bound {m : Fin N → ℝ} {h : ℝ} {q0 : EN E N}
    {τ : ℕ → ℝ} {γs : ℕ → ℝ → EN E N}
    (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h) {c : ℝ} (hc : 0 < c) (hmc : ∀ i, c ≤ m i)
    (h0 : ∀ k, γs k 0 = q0)
    (hac : ∀ k, AbsolutelyContinuousOnInterval (γs k) 0 (τ k))
    {T : ℝ} (hT : 0 < T) (hτT : ∀ᶠ k in atTop, T ≤ τ k)
    (hbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, actionOn m h (γs k) 0 T ≤ ENNReal.ofReal C) :
    ∃ (φ : ℕ → ℕ) (ζ : ℝ → EN E N), StrictMono φ ∧ ζ 0 = q0 ∧
      ContinuousOn ζ (Set.Icc 0 T) ∧ AbsolutelyContinuousOnInterval ζ 0 T ∧
      TendstoUniformlyOn (fun k => γs (φ k)) ζ atTop (Set.Icc 0 T) := by
  obtain ⟨C, hC0, hCbd⟩ := hbd
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp (hτT.and hCbd)
  have hM₀' : ∀ k ≥ M₀, T ≤ τ k ∧ actionOn m h (γs k) 0 T ≤ ENNReal.ofReal C := hM₀
  set F : ℕ → ℝ → EN E N := fun n => γs (n + M₀) with hF
  have hF0 : ∀ n, F n 0 = q0 := fun n => h0 _
  have hFle : ∀ n, T ≤ τ (n + M₀) := fun n => (hM₀' (n + M₀) (Nat.le_add_left M₀ n)).1
  have hFbd : ∀ n, actionOn m h (F n) 0 T ≤ ENNReal.ofReal C :=
    fun n => (hM₀' (n + M₀) (Nat.le_add_left M₀ n)).2
  have hFac : ∀ n, AbsolutelyContinuousOnInterval (F n) 0 T := by
    intro n
    refine (hac (n + M₀)).mono ?_
    rw [uIcc_of_le hT.le, uIcc_of_le (le_trans hT.le (hFle n))]
    exact Set.Icc_subset_Icc le_rfl (hFle n)
  -- the mass-weighted kinetic energy is uniformly bounded
  have hkin : ∀ n, (∫⁻ t in Set.Ioc 0 T,
      ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖(deriv (F n) t).ofLp i‖ ^ 2))
      ≤ ENNReal.ofReal ((Real.sqrt C) ^ 2) := by
    intro n
    rw [Real.sq_sqrt hC0, ← lintegral_ofReal_kinetic_eq]
    exact (lintegral_ofReal_kinetic_le_actionOn hm hh (F n) 0 T).trans (hFbd n)
  -- the (unweighted) Dirichlet energy is uniformly bounded
  have hcpos : (0:ℝ) ≤ (1 / 2) * c := by linarith
  have hsq : ∀ n, (∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (‖deriv (F n) t‖ ^ 2))
      ≤ ENNReal.ofReal ((Real.sqrt (C / ((1 / 2) * c))) ^ 2) := by
    intro n
    rw [Real.sq_sqrt (div_nonneg hC0 hcpos)]
    have h1 := euclidean_energy_le_of_kinetic (γ := F n) (τ := T) hc hmc (M := Real.sqrt C)
      (by rw [Real.sq_sqrt hC0]
          exact (lintegral_ofReal_kinetic_le_actionOn hm hh (F n) 0 T).trans (hFbd n))
    rwa [Real.sq_sqrt hC0] at h1
  have hcont : ∀ n, ContinuousOn (F n) (Set.Icc 0 T) := by
    intro n
    have h := (hFac n).continuousOn
    rwa [uIcc_of_le hT.le] at h
  obtain ⟨φ, hφmono, ζ, hζcont, hζconv⟩ :=
    exists_uniform_subseq (M := Real.sqrt (C / ((1 / 2) * c))) (Real.sqrt_nonneg _) hT.le
      hcont hFac hsq ⟨q0, hF0⟩
  have hζac : AbsolutelyContinuousOnInterval ζ 0 T :=
    (Commons.MeasureTheory.Integral.massWeighted_kinetic_le_liminf (F := fun n => F (φ n))
      hc hmc hT.le (Real.sqrt_nonneg C) hζcont hζconv (fun n => hFac (φ n))
      (fun n => hkin (φ n))).1
  have hζ0 : ζ 0 = q0 := by
    refine tendsto_nhds_unique (hζconv.tendsto_at (Set.left_mem_Icc.mpr hT.le)) ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with k
    exact (hF0 (φ k)).symm
  refine ⟨fun k => φ k + M₀, ζ, fun a b hab => Nat.add_lt_add_right (hφmono hab) M₀, hζ0,
    hζcont, hζac, ?_⟩
  simpa only [hF] using hζconv

/-! ## The calibration limit -/

/-- **The calibration identity for a uniform limit.**  Let `γ_k` be `h`-minimisers from `q₀` to
`p k`, with travel times `τ k`, converging uniformly on `[0,T]` along a subsequence to `ζ`, where
`T < τ k`.  Assume the normalised potentials `normPot m h (p k)` converge uniformly on compacts to
the horofunction `u`.  Then `ζ` calibrates `u` on `[0,T]`:
`A(ζ|[0,T]) = u q₀ - u (ζ T)`. -/
lemma actionOn_eq_ofReal_of_uniform_limit {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ}
    {p : ℕ → EN E N} {q0 : EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hdom : Dominated m h u)
    (huni : ∀ K : Set (EN E N), IsCompact K →
      TendstoUniformlyOn (fun k x => normPot m h (p k) x) u atTop K)
    {α β C c T : ℝ} (hα : 0 < α) (hβ : 0 < β) (hC0 : 0 ≤ C) (hT : 0 < T)
    (hest : ∀ x z : EN E N, actionPot m h x z ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2)))
    (hc : 0 < c) (hmc : ∀ i, c ≤ m i)
    {τ : ℕ → ℝ} {γs : ℕ → ℝ → EN E N} {φ : ℕ → ℕ} {ζ : ℝ → EN E N}
    (h0 : ∀ k, γs k 0 = q0) (h1 : ∀ k, γs k (τ k) = p k)
    (hac : ∀ k, AbsolutelyContinuousOnInterval (γs k) 0 (τ k))
    (hmin : ∀ k, IsHMinimizer m h (γs k) 0 (τ k))
    (hφ : StrictMono φ) (hτT : ∀ k, T < τ k)
    (hbd : ∀ k, actionOn m h (γs k) 0 T ≤ ENNReal.ofReal C)
    (hζ0 : ζ 0 = q0) (hζcont : ContinuousOn ζ (Set.Icc 0 T))
    (hζac : AbsolutelyContinuousOnInterval ζ 0 T)
    (hconv : TendstoUniformlyOn (fun k => γs (φ k)) ζ atTop (Set.Icc 0 T)) :
    actionOn m h ζ 0 T = ENNReal.ofReal (u q0 - u (ζ T)) := by
  have hfin : ∀ a b : EN E N, actionPot m h a b < ⊤ :=
    fun a b => lt_of_le_of_lt (hest a b) ENNReal.ofReal_lt_top
  have hhm : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hhh : 0 ≤ h := hh.le
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hTmem : T ∈ Set.Icc 0 T := Set.mem_Icc.mpr ⟨hT.le, le_rfl⟩
  -- the sub-curves are absolutely continuous on `[0,T]`
  have hFac : ∀ k, AbsolutelyContinuousOnInterval (γs (φ k)) 0 T := by
    intro k
    refine (hac (φ k)).mono ?_
    rw [uIcc_of_le hT.le, uIcc_of_le (le_trans hT.le (hτT (φ k)).le)]
    exact Set.Icc_subset_Icc le_rfl (hτT (φ k)).le
  have hFcont : ∀ k, ContinuousOn (γs (φ k)) (Set.Icc 0 T) := by
    intro k
    have h := (hFac k).continuousOn
    rwa [uIcc_of_le hT.le] at h
  have hFcontIoc : ∀ k, ContinuousOn (γs (φ k)) (Set.Ioc 0 T) :=
    fun k => (hFcont k).mono Set.Ioc_subset_Icc_self
  -- the kinetic energy bound
  have hkin : ∀ k, (∫⁻ t in Set.Ioc 0 T,
      ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖(deriv (γs (φ k)) t).ofLp i‖ ^ 2))
      ≤ ENNReal.ofReal ((Real.sqrt C) ^ 2) := by
    intro k
    rw [Real.sq_sqrt hC0, ← lintegral_ofReal_kinetic_eq]
    exact (lintegral_ofReal_kinetic_le_actionOn hhm hhh (γs (φ k)) 0 T).trans (hbd (φ k))
  -- convergence of the values of `normPot` at the moving endpoint
  have hlim2 : Tendsto (fun k => normPot m h (p (φ k)) (γs (φ k) T)) atTop (𝓝 (u (ζ T))) := by
    have hx : Tendsto (fun k => γs (φ k) T) atTop (𝓝 (ζ T)) := hconv.tendsto_at hTmem
    have hpt : Tendsto (fun k => normPot m h (p (φ k)) (ζ T)) atTop (𝓝 (u (ζ T))) :=
      ((huni {ζ T} isCompact_singleton).seq_tendstoUniformlyOn φ hφtop).tendsto_at
        (Set.mem_singleton (ζ T))
    have hdiff : Tendsto (fun k => normPot m h (p (φ k)) (γs (φ k) T)
        - normPot m h (p (φ k)) (ζ T)) atTop (𝓝 0) := by
      have hz : Tendsto (fun k => ‖γs (φ k) T - ζ T‖) atTop (𝓝 0) := by
        have h' : Tendsto (fun k => γs (φ k) T - ζ T) atTop (𝓝 (ζ T - ζ T)) :=
          hx.sub (tendsto_const_nhds (x := ζ T))
        simpa using h'.norm
      have hp2 : Tendsto (fun k => α * ‖γs (φ k) T - ζ T‖
          + h * β * ‖γs (φ k) T - ζ T‖ ^ 2) atTop (𝓝 (α * 0 + h * β * 0 ^ 2)) :=
        (tendsto_const_nhds.mul hz).add (tendsto_const_nhds.mul (hz.pow 2))
      have hs : Tendsto (fun k => Real.sqrt (α * ‖γs (φ k) T - ζ T‖
          + h * β * ‖γs (φ k) T - ζ T‖ ^ 2)) atTop (𝓝 0) := by
        have h3 := (Real.continuous_sqrt.tendsto (α * 0 + h * β * 0 ^ 2)).comp hp2
        have h4 : Real.sqrt (α * 0 + h * β * 0 ^ 2) = 0 := by simp
        rwa [h4] at h3
      have hbd' : ∀ k, ‖normPot m h (p (φ k)) (γs (φ k) T)
          - normPot m h (p (φ k)) (ζ T)‖
          ≤ Real.sqrt (α * ‖γs (φ k) T - ζ T‖ + h * β * ‖γs (φ k) T - ζ T‖ ^ 2) := by
        intro k
        rw [Real.norm_eq_abs]
        exact normPot_sub_le hα.le hβ.le hest (p (φ k)) _ _
      exact squeeze_zero_norm hbd' hs
    have hsum := hpt.add hdiff
    have heq : (fun k => normPot m h (p (φ k)) (ζ T)
        + (normPot m h (p (φ k)) (γs (φ k) T) - normPot m h (p (φ k)) (ζ T)))
        = fun k => normPot m h (p (φ k)) (γs (φ k) T) := by
      funext k; ring
    rw [heq] at hsum
    simpa using hsum
  -- convergence of the actions
  have hAlim : Tendsto (fun k => actionOn m h (γs (φ k)) 0 T) atTop
      (𝓝 (ENNReal.ofReal (u q0 - u (ζ T)))) := by
    have hq : Tendsto (fun k => normPot m h (p (φ k)) q0) atTop (𝓝 (u q0)) :=
      ((huni {q0} isCompact_singleton).seq_tendstoUniformlyOn φ hφtop).tendsto_at
        (Set.mem_singleton q0)
    have hev : (fun k => actionOn m h (γs (φ k)) 0 T) =ᶠ[atTop]
        fun k => ENNReal.ofReal (normPot m h (p (φ k)) q0
          - normPot m h (p (φ k)) (γs (φ k) T)) :=
      Eventually.of_forall fun k =>
        actionOn_eq_ofReal_normPot_sub (hac (φ k)) (hmin (φ k)) (hfin q0 (p (φ k)))
          (h0 (φ k)) (h1 (φ k)) hT (hτT (φ k))
    exact ((ENNReal.continuous_ofReal.tendsto _).comp (hq.sub hlim2)).congr' hev.symm
  refine le_antisymm ?_ ?_
  · -- the upper bound, by lower semicontinuity of the action
    have hsq : (∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv ζ t)))
        ≤ liminf (fun k => ∫⁻ t in Set.Ioc 0 T,
            ENNReal.ofReal (kinetic m (deriv (γs (φ k)) t))) atTop := by
      have hMW := Commons.MeasureTheory.Integral.massWeighted_kinetic_le_liminf
        (m := m) (c := c) hc hmc hT.le (Real.sqrt_nonneg C) hζcont hconv
        (fun k => hFac k) hkin
      simpa only [lintegral_ofReal_kinetic_eq] using hMW.2
    have hp : (∫⁻ t in Set.Ioc 0 T, pairPot m (ζ t))
        ≤ liminf (fun k => ∫⁻ t in Set.Ioc 0 T, pairPot m (γs (φ k) t)) atTop :=
      lintegral_pairPot_le_liminf' hhm
        (fun t ht => hconv.tendsto_at (Set.mem_Icc.mpr ⟨ht.1.le, ht.2⟩)) hFcontIoc
    have hmain := actionOn_le_liminf hm hhh
      (aemeasurable_pairPot_comp (hζcont.mono Set.Ioc_subset_Icc_self) measurableSet_Ioc) hsq hp
    rw [hAlim.liminf_eq] at hmain
    exact hmain
  · -- the lower bound, by domination
    calc ENNReal.ofReal (u q0 - u (ζ T))
        ≤ actionPot m h (ζ T) q0 := hdom (ζ T) q0
      _ = actionPot m h q0 (ζ T) := actionPot_comm m h (ζ T) q0
      _ ≤ actionOn m h ζ 0 T := actionPot_le_of_interval hT hζ0 rfl hζac

/-- **The convergence of the approximating minimisers to the calibrating curve.**  For every `T > 0`
some subsequence of the `h`-minimisers `γ_k` (from `q₀` to `p k`, with travel times `τ_k → ∞`)
converges uniformly on `[0,T]` to a curve `ζ` with `ζ 0 = q₀` which calibrates the horofunction `u`:
`A(ζ|[0,T]) = u q₀ - u (ζ T)`. -/
theorem exists_calibrating_limit {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ} {p : ℕ → EN E N}
    {q0 : EN E N} (hN : 0 < N) (hm : ∀ i, 0 < m i) (hh : 0 < h) (hdom : Dominated m h u)
    (huni : ∀ K : Set (EN E N), IsCompact K →
      TendstoUniformlyOn (fun k x => normPot m h (p k) x) u atTop K)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hest : ∀ x z : EN E N, actionPot m h x z ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2)))
    {τ : ℕ → ℝ} {γs : ℕ → ℝ → EN E N}
    (hτ0 : ∀ k, 0 < τ k) (h0 : ∀ k, γs k 0 = q0) (h1 : ∀ k, γs k (τ k) = p k)
    (hac : ∀ k, AbsolutelyContinuousOnInterval (γs k) 0 (τ k))
    (hmin : ∀ k, IsHMinimizer m h (γs k) 0 (τ k))
    (hτtop : Tendsto τ atTop atTop) {T : ℝ} (hT : 0 < T) :
    ∃ (φ : ℕ → ℕ) (ζ : ℝ → EN E N), StrictMono φ ∧ ζ 0 = q0 ∧
      ContinuousOn ζ (Set.Icc 0 T) ∧ AbsolutelyContinuousOnInterval ζ 0 T ∧
      TendstoUniformlyOn (fun k => γs (φ k)) ζ atTop (Set.Icc 0 T) ∧
      actionOn m h ζ 0 T = ENNReal.ofReal (u q0 - u (ζ T)) := by
  classical
  obtain ⟨c, hc, hmc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    rcases isEmpty_or_nonempty (Fin N) with hN' | hN'
    · exact False.elim (isEmptyElim (⟨0, hN⟩ : Fin N))
    · refine ⟨Finset.univ.inf' Finset.univ_nonempty m, ?_, fun i => ?_⟩
      · rw [Finset.lt_inf'_iff]; intro i _; exact hm i
      · exact Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨C₀, hC₀bd⟩ :=
    exists_uniform_action_bound (m := m) (h := h) (c := c) (q0 := q0) hm hh.le
      hτ0 h0 h1 hac hmin hc hmc hα hβ hest hτtop hT
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCbd : ∀ᶠ k in atTop, actionOn m h (γs k) 0 T ≤ ENNReal.ofReal C :=
    hC₀bd.mono fun k hk => hk.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hcomb : ∀ᶠ k in atTop, T < τ k ∧ actionOn m h (γs k) 0 T ≤ ENNReal.ofReal C :=
    (hτtop.eventually_gt_atTop T).and hCbd
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp hcomb
  have hM₀' : ∀ k ≥ M₀, T < τ k ∧ actionOn m h (γs k) 0 T ≤ ENNReal.ofReal C := hM₀
  set γs' : ℕ → ℝ → EN E N := fun n => γs (n + M₀) with hγs'
  set τ' : ℕ → ℝ := fun n => τ (n + M₀) with hτ'
  set p' : ℕ → EN E N := fun n => p (n + M₀) with hp'
  have h0' : ∀ n, γs' n 0 = q0 := fun n => h0 _
  have h1' : ∀ n, γs' n (τ' n) = p' n := fun n => h1 _
  have hac' : ∀ n, AbsolutelyContinuousOnInterval (γs' n) 0 (τ' n) := fun n => hac _
  have hmin' : ∀ n, IsHMinimizer m h (γs' n) 0 (τ' n) := fun n => hmin _
  have hτT' : ∀ n, T < τ' n := fun n => (hM₀' (n + M₀) (Nat.le_add_left M₀ n)).1
  have hbd' : ∀ n, actionOn m h (γs' n) 0 T ≤ ENNReal.ofReal C :=
    fun n => (hM₀' (n + M₀) (Nat.le_add_left M₀ n)).2
  obtain ⟨φ₁, ζ, hφ₁, hζ0, hζcont, hζac, hconv⟩ :=
    exists_uniform_subseq_of_action_bound (m := m) (h := h) (q0 := q0) (τ := τ') (γs := γs')
      (fun i => (hm i).le) hh.le hc hmc h0' hac' hT
      (Eventually.of_forall fun n => (hτT' n).le)
      ⟨C, hC0, Eventually.of_forall hbd'⟩
  have huni' : ∀ K : Set (EN E N), IsCompact K →
      TendstoUniformlyOn (fun k x => normPot m h (p' k) x) u atTop K := by
    intro K hK
    have h1s := (huni K hK).seq_tendstoUniformlyOn (fun k => k + M₀) (tendsto_add_atTop_nat M₀)
    simpa only [hp', Function.comp_apply] using h1s
  have hcal := actionOn_eq_ofReal_of_uniform_limit (m := m) (h := h) (u := u) (p := p')
    hm hh hdom huni' hα hβ hC0 hT hest hc hmc h0' h1' hac' hmin' hφ₁ hτT' hbd'
    hζ0 hζcont hζac hconv
  exact ⟨fun k => φ₁ k + M₀, ζ, fun a b hab => Nat.add_lt_add_right (hφ₁ hab) M₀, hζ0,
    hζcont, hζac, by simpa only [hγs'] using hconv, hcal⟩

end Submission.NBody
