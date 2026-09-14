import Submission.NBody.MadernaEstimate
import Submission.NBody.Tonelli
import Submission.NBody.Minimizer
import Mathlib

/-!
# The calibrating curve of a horofunction

This file proves the key construction of Maderna--Venturelli (`thm-horofuns.have.lamin` and the
first step of `thm-calib.direct.horo`): starting from the horofunction `𝔲` obtained as the limit
of the normalised action potentials `x ↦ φ_h(x, p_k) - φ_h(0, p_k)` along a sequence of
configurations `p_k` receding to infinity, there is, through every configuration `x`, a curve
`γ : [0,+∞) → Eᴺ` with `γ 0 = x` which is

* an `h`-minimiser on every `[0,t]` (`IsHMinimizer m h γ 0 t`), and
* **calibrating** the horofunction: `A_{L+h}(γ|[0,t]) = 𝔲(x) - 𝔲(γ t)`.

This is the paper's construction of hyperbolic motions from horofunctions; it does not use Zorn's
lemma or von Zeipel's theorem, because the minimisers `γ_k` from `x` to `p_k` (whose action is
related to the normalised potentials by exact equalities) already converge along compact time
intervals to the calibrating curve.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The **normalised action potential** `x ↦ φ_h(x,p) - φ_h(0,p)`, whose limits are the
horofunctions of the paper. -/
noncomputable def normPot (m : Fin N → ℝ) (h : ℝ) (p : EN E N) (x : EN E N) : ℝ :=
  (actionPot m h x p).toReal - (actionPot m h 0 p).toReal

/-- Two finite action potentials are close when the configurations are. -/
lemma actionPot_toReal_sub_le {m : Fin N → ℝ} {h : ℝ} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (hest : ∀ x y : EN E N, actionPot m h x y ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2)))
    (p x z : EN E N) :
    |(actionPot m h x p).toReal - (actionPot m h z p).toReal|
      ≤ Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2) := by
  set Φ : ℝ := Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2) with hΦ
  have hΦ0 : 0 ≤ Φ := Real.sqrt_nonneg _
  have h1 : actionPot m h x p ≤ actionPot m h x z + actionPot m h z p :=
    actionPot_triangle m h x z p
  have h2 : actionPot m h z p ≤ actionPot m h z x + actionPot m h x p :=
    actionPot_triangle m h z x p
  have h3 : (actionPot m h x p).toReal
      ≤ (actionPot m h x z).toReal + (actionPot m h z p).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(hfin x z).ne, (hfin z p).ne⟩) h1
    rwa [ENNReal.toReal_add (hfin x z).ne (hfin z p).ne] at h
  have h4 : (actionPot m h z p).toReal
      ≤ (actionPot m h z x).toReal + (actionPot m h x p).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(hfin z x).ne, (hfin x p).ne⟩) h2
    rwa [ENNReal.toReal_add (hfin z x).ne (hfin x p).ne] at h
  have h5 : (actionPot m h x z).toReal ≤ Φ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hest x z)
    rwa [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h
  have h6 : (actionPot m h z x).toReal ≤ Φ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hest z x)
    rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), norm_sub_rev] at h
    exact h
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- The normalised potentials of a convergent horofunction sequence have a common Hölder modulus. -/
lemma normPot_sub_le {m : Fin N → ℝ} {h : ℝ} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hest : ∀ x y : EN E N, actionPot m h x y ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2)))
    (p x z : EN E N) :
    |normPot m h p x - normPot m h p z|
      ≤ Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2) := by
  have hfin : ∀ a b : EN E N, actionPot m h a b < ⊤ :=
    fun a b => lt_of_le_of_lt (hest a b) ENNReal.ofReal_lt_top
  have := actionPot_toReal_sub_le hα hβ hfin hest p x z
  have hsub : normPot m h p x - normPot m h p z
      = (actionPot m h x p).toReal - (actionPot m h z p).toReal := by
    simp only [normPot]; ring
  rw [hsub]
  exact this

/-- An elementary consequence of `d² ≤ C √(α d + γ d²)`. -/
lemma le_max_one_mul_sqrt {α γ d C : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hC : 0 ≤ C) (hd : 0 ≤ d)
    (h : d ^ 2 ≤ C * Real.sqrt (α * d + γ * d ^ 2)) :
    d ≤ max 1 (C * Real.sqrt (α + γ)) := by
  rcases le_total d 1 with h1 | h1
  · exact h1.trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one h1
    have hαγ : (0:ℝ) ≤ α + γ := by linarith
    have hle : α * d + γ * d ^ 2 ≤ (α + γ) * d ^ 2 := by
      have hsq : d ≤ d ^ 2 := by nlinarith
      have h1' : α * d ≤ α * d ^ 2 := mul_le_mul_of_nonneg_left hsq hα
      nlinarith [h1']
    have hkey : Real.sqrt (α * d + γ * d ^ 2) ≤ Real.sqrt (α + γ) * d := by
      calc Real.sqrt (α * d + γ * d ^ 2) ≤ Real.sqrt ((α + γ) * d ^ 2) :=
            Real.sqrt_le_sqrt hle
        _ = Real.sqrt (α + γ) * d := by rw [Real.sqrt_mul hαγ, Real.sqrt_sq hdpos.le]
    have h2 : d ^ 2 ≤ C * (Real.sqrt (α + γ) * d) := h.trans (mul_le_mul_of_nonneg_left hkey hC)
    have h3 : d * d ≤ d * (C * Real.sqrt (α + γ)) := by nlinarith [h2]
    exact le_of_mul_le_mul_left h3 hdpos


/-- The same estimate with the *second* argument varying. -/
lemma actionPot_toReal_sub_le' {m : Fin N → ℝ} {h : ℝ} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (hest : ∀ x y : EN E N, actionPot m h x y ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2)))
    (x p q : EN E N) :
    |(actionPot m h x p).toReal - (actionPot m h x q).toReal|
      ≤ Real.sqrt (α * ‖p - q‖ + h * β * ‖p - q‖ ^ 2) := by
  have hmain := actionPot_toReal_sub_le hα hβ hfin hest x q p
  rw [actionPot_comm m h q x, actionPot_comm m h p x, norm_sub_rev] at hmain
  rw [abs_sub_comm]
  exact hmain

/-- **The key identity.**  For an `h`-minimiser `κ` from `y` to `p` on `[0,s]`, the action of the
initial piece `[0,t]` is the difference of the normalised potentials:
`A(κ|[0,t]) = φ_h(y,p) - φ_h(κ t, p)`. -/
lemma actionOn_eq_ofReal_normPot_sub {m : Fin N → ℝ} {h : ℝ} {κ : ℝ → EN E N} {y p : EN E N}
    {s t : ℝ} (hac : AbsolutelyContinuousOnInterval κ 0 s)
    (hmin : IsHMinimizer m h κ 0 s) (hfin : actionPot m h y p < ⊤)
    (h0 : κ 0 = y) (h1 : κ s = p) (ht0 : 0 < t) (hts : t < s) :
    actionOn m h κ 0 t = ENNReal.ofReal (normPot m h p y - normPot m h p (κ t)) := by
  have hsp : actionPot m h y p = actionOn m h κ 0 t + actionPot m h (κ t) p := by
    have h2' : actionOn m h κ t s = actionPot m h (κ t) p := by
      have hsub := IsHMinimizer.sub_right hac hmin (by rw [hmin, h0, h1]; exact hfin) ht0 hts
      rw [hsub, h1]
    calc actionPot m h y p = actionPot m h (κ 0) (κ s) := by rw [h0, h1]
      _ = actionOn m h κ 0 s := hmin.symm
      _ = actionOn m h κ 0 t + actionOn m h κ t s := actionOn_add κ ht0.le hts.le
      _ = actionOn m h κ 0 t + actionPot m h (κ t) p := by rw [h2']
  have hX : actionOn m h κ 0 t < ⊤ := by
    rw [hsp] at hfin
    exact (ENNReal.add_lt_top.mp hfin).1
  have hY : actionPot m h (κ t) p < ⊤ := by
    rw [hsp] at hfin
    exact (ENNReal.add_lt_top.mp hfin).2
  have hto : (actionPot m h y p).toReal
      = (actionOn m h κ 0 t).toReal + (actionPot m h (κ t) p).toReal := by
    rw [hsp, ENNReal.toReal_add hX.ne hY.ne]
  have hXto : (actionOn m h κ 0 t).toReal
      = (actionPot m h y p).toReal - (actionPot m h (κ t) p).toReal := by linarith
  rw [← ENNReal.ofReal_toReal hX.ne, hXto]
  simp only [normPot]
  ring

/-- **Uniform convergence at a varying point.**  If the normalised potentials converge uniformly on
a ball containing a sequence `z` and its limit, and `u` has the common Hölder modulus, then the
values at the varying points converge. -/
lemma tendsto_normPot_comp {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ} {P : ℕ → EN E N}
    {z : ℕ → EN E N} {z₀ c₀ : EN E N} {R α β : ℝ}
    (huni : TendstoUniformlyOn (fun k x => normPot m h (P k) x) u atTop (Metric.closedBall c₀ R))
    (hu_mod : ∀ x z : EN E N, dist (u x) (u z)
      ≤ Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2))
    (hz : ∀ k, z k ∈ Metric.closedBall c₀ R) (hz₀ : z₀ ∈ Metric.closedBall c₀ R)
    (hlim : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun k => normPot m h (P k) (z k)) atTop (𝓝 (u z₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hunif : ∀ᶠ k in atTop, dist (normPot m h (P k) (z k)) (u (z k)) < ε / 2 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp huni) (ε / 2) hε2
    filter_upwards [h] with k hk
    simpa [dist_comm] using hk (z k) (hz k)
  have hsmall : ∀ᶠ k in atTop, dist (u (z k)) (u z₀) < ε / 2 := by
    have hd0 : Tendsto (fun k => ‖z k - z₀‖) atTop (𝓝 0) := by
      have h' : Tendsto (fun k => z k - z₀) atTop (𝓝 (z₀ - z₀)) :=
        hlim.sub (tendsto_const_nhds (x := z₀))
      simpa using h'.norm
    have hp : Tendsto (fun k => α * ‖z k - z₀‖ + h * β * ‖z k - z₀‖ ^ 2) atTop
        (𝓝 (α * 0 + h * β * 0 ^ 2)) :=
      (tendsto_const_nhds.mul hd0).add (tendsto_const_nhds.mul (hd0.pow 2))
    have hs : Tendsto (fun k => Real.sqrt (α * ‖z k - z₀‖ + h * β * ‖z k - z₀‖ ^ 2)) atTop
        (𝓝 0) := by
      have h3 := (Real.continuous_sqrt.tendsto (α * 0 + h * β * 0 ^ 2)).comp hp
      have h4 : Real.sqrt (α * 0 + h * β * 0 ^ 2) = 0 := by simp
      rw [h4] at h3
      exact h3
    filter_upwards [hs.eventually (Iio_mem_nhds hε2)] with k hk
    exact lt_of_le_of_lt (hu_mod _ _) hk
  filter_upwards [hunif, hsmall] with k h1 h2
  calc dist (normPot m h (P k) (z k)) (u z₀)
      ≤ dist (normPot m h (P k) (z k)) (u (z k)) + dist (u (z k)) (u z₀) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

/-- **The one-step construction.**  Given a sequence `p k → ∞` of collision-free configurations and
the horofunction `u` obtained as the limit of the normalised potentials
`x ↦ φ_h(x, p k) - φ_h(0,p k)`, for every configuration `y` and every `T > 0` there is a curve `γ`
on `[0,T]` with `γ 0 = y` which is an `h`-minimiser on `[0,T]` and calibrates `u`:
`A(γ|[0,t]) = u y - u (γ t)` for all `t ∈ (0,T]`. -/
theorem exists_calibrating_interval {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ} {p : ℕ → EN E N}
    (hN : 0 < N) (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hdom : Dominated m h u)
    (hpnc : ∀ k, WithoutCollisions (p k))
    (hpgrow : Tendsto (fun k => ‖p k‖) atTop atTop)
    (huni : ∀ K : Set (EN E N), IsCompact K →
      TendstoUniformlyOn (fun k x => normPot m h (p k) x) u atTop K)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hest : ∀ x z : EN E N, actionPot m h x z ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2)))
    {y : EN E N} {T : ℝ} (hT : 0 < T) :
    ∃ γ : ℝ → EN E N, γ 0 = y ∧ AbsolutelyContinuousOnInterval γ 0 T ∧
      IsHMinimizer m h γ 0 T ∧
      ∀ t ∈ Set.Ioc 0 T, actionOn m h γ 0 t = ENNReal.ofReal (u y - u (γ t)) := by
  classical
  have hfin : ∀ a b : EN E N, actionPot m h a b < ⊤ :=
    fun a b => lt_of_le_of_lt (hest a b) ENNReal.ofReal_lt_top
  obtain ⟨c, hc, hmc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    rcases isEmpty_or_nonempty (Fin N) with hN' | hN'
    · exact False.elim (isEmptyElim (⟨0, hN⟩ : Fin N))
    · refine ⟨Finset.univ.inf' Finset.univ_nonempty m, ?_, fun i => ?_⟩
      · rw [Finset.lt_inf'_iff]; intro i _; exact hm i
      · exact Finset.inf'_le _ (Finset.mem_univ i)
  have hupt : ∀ x : EN E N, Tendsto (fun k => normPot m h (p k) x) atTop (𝓝 (u x)) :=
    fun x => (huni {x} isCompact_singleton).tendsto_at (Set.mem_singleton x)
  have hu_mod : ∀ x z : EN E N,
      |u x - u z| ≤ Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2) := by
    intro x z
    have hlim : Tendsto (fun k => |normPot m h (p k) x - normPot m h (p k) z|) atTop
        (𝓝 |u x - u z|) := ((hupt x).sub (hupt z)).abs
    exact le_of_tendsto hlim (Eventually.of_forall fun k => normPot_sub_le hα.le hβ.le hest _ _ _)
  have hu_dist : ∀ x z : EN E N, dist (u x) (u z) ≤
      Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2) := by
    intro x z; rw [Real.dist_eq]; exact hu_mod x z
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ k ≥ N₀, y ≠ p k := by
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hpgrow.eventually (eventually_gt_atTop ‖y‖))
    refine ⟨N₀, fun k hk hkp => ?_⟩
    rw [hkp] at hN₀
    exact absurd (hN₀ k hk) (lt_irrefl _)
  have hmin' : ∀ k : ℕ, ∃ τ : ℝ, ∃ κ : ℝ → EN E N, 0 < τ ∧ κ 0 = y ∧ κ τ = p (k + N₀) ∧
      AbsolutelyContinuousOnInterval κ 0 τ ∧ actionOn m h κ 0 τ = actionPot m h y (p (k + N₀)) := by
    intro k
    obtain ⟨τ, hτ, κ, h0, h1, hac, hA⟩ :=
      exists_minimizer hm hh (hN₀ (k + N₀) (by omega)) (hpnc _) (hfin y _)
    exact ⟨τ, κ, hτ, h0, h1, hac, hA⟩
  choose τ κ hτ0 hκ0 hκp hκac hκA using hmin'
  -- the time spent by the minimisers diverges
  have hgrow_shift : Tendsto (fun k => ‖p (k + N₀)‖) atTop atTop :=
    hpgrow.comp (tendsto_add_atTop_nat N₀)
  have hd_grow : Tendsto (fun k => ‖y - p (k + N₀)‖) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp hgrow_shift (‖y‖ + max b 0)
    refine ⟨N, fun k hk => ?_⟩
    have hk' : ‖y‖ + max b 0 ≤ ‖p (k + N₀)‖ := hN k hk
    have h2 : ‖p (k + N₀)‖ ≤ ‖y‖ + ‖y - p (k + N₀)‖ := by
      calc ‖p (k + N₀)‖ = ‖y + (p (k + N₀) - y)‖ := by
              rw [show y + (p (k + N₀) - y) = p (k + N₀) by abel]
        _ ≤ ‖y‖ + ‖p (k + N₀) - y‖ := norm_add_le _ _
        _ = ‖y‖ + ‖y - p (k + N₀)‖ := by rw [norm_sub_rev]
    linarith [le_max_left b 0]
  -- the time spent by the minimisers diverges
  have hτ_ev : ∀ᶠ k in atTop, T < τ k := by
    set S : ℝ := Real.sqrt (α + h * β) with hS
    have hSpos : 0 < S := by
      rw [hS]; exact Real.sqrt_pos.mpr (by positivity)
    have hcoef : 0 < c / (2 * S) := by positivity
    filter_upwards [hd_grow.eventually (eventually_ge_atTop (max 1 (T / (c / (2 * S)) + 1)))]
      with k hk
    set d : ℝ := ‖y - p (k + N₀)‖ with hd
    have hd1 : 1 ≤ d := le_trans (le_max_left _ _) hk
    have hchain : (1 / 2) * c * d ^ 2 / τ k + h * τ k
        ≤ Real.sqrt (α * d + h * β * d ^ 2) := by
      have h1 : ENNReal.ofReal ((1 / 2) * c * d ^ 2 / τ k + h * τ k)
          ≤ actionPot m h y (p (k + N₀)) := by
        rw [← hκA k]
        simpa only [← hd] using
          ofReal_chord_sq_div_add_le_actionOn hc hmc hh.le (hτ0 k) (hκ0 k) (hκp k) (hκac k)
      exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp
        (h1.trans (hest y (p (k + N₀))))
    have hkey0 : (1 / 2) * c * d ^ 2 / τ k ≤ Real.sqrt (α * d + h * β * d ^ 2) := by
      linarith [hchain, mul_pos hh (hτ0 k)]
    have hSd : Real.sqrt (α * d + h * β * d ^ 2) ≤ S * d := by
      rw [hS]
      have hαγ : (0 : ℝ) ≤ α + h * β := by positivity
      have hle : α * d + h * β * d ^ 2 ≤ (α + h * β) * d ^ 2 := by
        have hsq : d ≤ d ^ 2 := by nlinarith
        have h1 : α * d ≤ α * d ^ 2 := mul_le_mul_of_nonneg_left hsq hα.le
        nlinarith [h1]
      calc Real.sqrt (α * d + h * β * d ^ 2) ≤ Real.sqrt ((α + h * β) * d ^ 2) :=
            Real.sqrt_le_sqrt hle
        _ = Real.sqrt (α + h * β) * d := by
            rw [Real.sqrt_mul hαγ, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ d)]
    have hkey : (1 / 2) * c * d ^ 2 / τ k ≤ S * d := hkey0.trans hSd
    have hkey2 : (1 / 2) * c * d ^ 2 ≤ (S * d) * τ k := by
      rw [div_le_iff₀ (hτ0 k)] at hkey
      exact hkey
    have h6 : c * d ≤ 2 * S * τ k := by
      have h7 : d * (c * d) ≤ d * (2 * S * τ k) := by nlinarith [hkey2]
      exact le_of_mul_le_mul_left h7 (lt_of_lt_of_le zero_lt_one hd1)
    have hτge : (c / (2 * S)) * d ≤ τ k := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * S)]
      linarith [h6, mul_comm (2 * S) (τ k)]
    have hdT : T / (c / (2 * S)) + 1 ≤ d := le_trans (le_max_right _ _) hk
    have hgoal : T < (c / (2 * S)) * d := by
      have h1 : T < (T / (c / (2 * S)) + 1) * (c / (2 * S)) := by
        rw [add_mul, div_mul_cancel₀ T (ne_of_gt hcoef), one_mul]
        linarith
      calc T < (T / (c / (2 * S)) + 1) * (c / (2 * S)) := h1
        _ ≤ d * (c / (2 * S)) := mul_le_mul_of_nonneg_right hdT hcoef.le
        _ = (c / (2 * S)) * d := mul_comm _ _
    linarith
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hτ_ev
  -- the shifted sequences
  set K : ℕ → ℝ → EN E N := fun k => κ (k + N₁) with hKdef
  set Tau : ℕ → ℝ := fun k => τ (k + N₁) with hTaudef
  set P : ℕ → EN E N := fun k => p ((k + N₁) + N₀) with hPdef
  have hTau0 : ∀ k, 0 < Tau k := fun k => hτ0 _
  have hK0 : ∀ k, K k 0 = y := fun k => hκ0 _
  have hKTau : ∀ k, K k (Tau k) = P k := fun k => hκp _
  have hKac : ∀ k, AbsolutelyContinuousOnInterval (K k) 0 (Tau k) := fun k => hκac _
  have hKA : ∀ k, actionOn m h (K k) 0 (Tau k) = actionPot m h y (P k) := fun k => hκA _
  have hTauT : ∀ k, T < Tau k := fun k => hN₁ _ (by omega)
  have hPnc : ∀ k, WithoutCollisions (P k) := fun k => hpnc _
  have hKmin : ∀ k, IsHMinimizer m h (K k) 0 (Tau k) := by
    intro k
    rw [IsHMinimizer, hK0 k, hKTau k]
    exact hKA k
  have hKAf : ∀ k, actionOn m h (K k) 0 (Tau k) < ⊤ := by
    intro k; rw [hKA k]; exact hfin y (P k)
  have hPuni : ∀ S' : Set (EN E N), IsCompact S' →
      TendstoUniformlyOn (fun k x => normPot m h (P k) x) u atTop S' := by
    intro S' hS'
    have h1 := (huni S' hS').seq_tendstoUniformlyOn (fun k => k + N₀)
      (tendsto_add_atTop_nat N₀)
    have h2 := h1.seq_tendstoUniformlyOn (fun k => k + N₁) (tendsto_add_atTop_nat N₁)
    simpa only [Function.comp_apply] using h2
  have hminT : ∀ k, IsHMinimizer m h (K k) 0 T :=
    fun k => IsHMinimizer.sub_left (hKac k) (hKmin k) (hKAf k) hT (hTauT k)
  have hKacT : ∀ k, AbsolutelyContinuousOnInterval (K k) 0 T := by
    intro k
    refine (hKac k).mono ?_
    rw [uIcc_of_le hT.le, uIcc_of_le (hTau0 k).le]
    exact Set.Icc_subset_Icc le_rfl (le_of_lt (hTauT k))
  have hKac_le : ∀ k t, 0 < t → t ≤ T → AbsolutelyContinuousOnInterval (K k) 0 t := by
    intro k t ht0 htT
    refine (hKac k).mono ?_
    rw [uIcc_of_le ht0.le, uIcc_of_le (hTau0 k).le]
    exact Set.Icc_subset_Icc le_rfl (htT.trans (le_of_lt (hTauT k)))
  have hmin_le : ∀ k t, 0 < t → t ≤ T → IsHMinimizer m h (K k) 0 t := by
    intro k t ht0 htT
    rcases lt_or_eq_of_le htT with hlt | heq
    · exact IsHMinimizer.sub_left (hKac k) (hKmin k) (hKAf k) ht0
        (hlt.trans_le (le_of_lt (hTauT k)))
    · rw [heq]; exact hminT k
  -- the displacement bound
  set R : ℝ := max 1 (2 * T * Real.sqrt (α + h * β) / c) with hRdef
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRnn : 0 ≤ R := le_trans zero_le_one hR1
  have hdisp : ∀ k t, t ∈ Set.Ioc 0 T → ‖y - K k t‖ ≤ R := by
    intro k t ht
    have hAle : actionOn m h (K k) 0 t
        ≤ ENNReal.ofReal (Real.sqrt (α * ‖y - K k t‖ + h * β * ‖y - K k t‖ ^ 2)) := by
      have h1 := hmin_le k t ht.1 ht.2
      rw [IsHMinimizer] at h1
      rw [h1, hK0 k]
      exact hest y (K k t)
    have hAge : ENNReal.ofReal ((1 / 2) * c * ‖y - K k t‖ ^ 2 / t + h * t)
        ≤ actionOn m h (K k) 0 t :=
      ofReal_chord_sq_div_add_le_actionOn hc hmc hh.le ht.1 (hK0 k) rfl (hKac_le k t ht.1 ht.2)
    have hreal : (1 / 2) * c * ‖y - K k t‖ ^ 2 / t + h * t
        ≤ Real.sqrt (α * ‖y - K k t‖ + h * β * ‖y - K k t‖ ^ 2) :=
      (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp (hAge.trans hAle)
    have hd2 : (0:ℝ) ≤ ‖y - K k t‖ ^ 2 := sq_nonneg _
    have hstep : (1 / 2) * c * ‖y - K k t‖ ^ 2 / T ≤ (1 / 2) * c * ‖y - K k t‖ ^ 2 / t := by
      have hcoefnn : 0 ≤ (1 / 2) * c * ‖y - K k t‖ ^ 2 := by positivity
      rw [div_le_div_iff₀ hT ht.1]
      exact mul_le_mul_of_nonneg_left ht.2 hcoefnn
    have hkey : ‖y - K k t‖ ^ 2
        ≤ (2 * T / c) * Real.sqrt (α * ‖y - K k t‖ + h * β * ‖y - K k t‖ ^ 2) := by
      set Φ : ℝ := Real.sqrt (α * ‖y - K k t‖ + h * β * ‖y - K k t‖ ^ 2) with hΦdef
      have h4 : (1 / 2) * c * ‖y - K k t‖ ^ 2 / T ≤ Φ := by
        rw [hΦdef]
        linarith [hreal, hstep, mul_nonneg hh.le ht.1.le]
      have h5 : (1 / 2) * c * ‖y - K k t‖ ^ 2 ≤ Φ * T := by
        rw [div_le_iff₀ hT] at h4; exact h4
      have h6 : ‖y - K k t‖ ^ 2 ≤ (2 / c) * (Φ * T) := by
        have h7 := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ 2 / c)
        have heq : (2 / c) * ((1 / 2) * c * ‖y - K k t‖ ^ 2) = ‖y - K k t‖ ^ 2 := by
          rw [div_mul_eq_mul_div]
          rw [show (2 : ℝ) * ((1 / 2) * c * ‖y - K k t‖ ^ 2) = c * ‖y - K k t‖ ^ 2 by ring]
          exact mul_div_cancel_left₀ _ (ne_of_gt hc)
        rwa [heq] at h7
      calc ‖y - K k t‖ ^ 2 ≤ (2 / c) * (Φ * T) := h6
        _ = (2 * T / c) * Φ := by ring
    have := le_max_one_mul_sqrt hα.le (mul_nonneg hh.le hβ.le) (by positivity) (norm_nonneg _) hkey
    refine this.trans (le_of_eq ?_)
    rw [hRdef]
    congr 1
    ring
  -- the `L²` bound
  set Cb : ℝ := Real.sqrt (α * (2 * R) + h * β * (2 * R) ^ 2) with hCbdef
  have hCb0 : 0 ≤ Cb := Real.sqrt_nonneg _
  have hkin : ∀ k, (∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv (K k) t)))
      ≤ ENNReal.ofReal Cb := by
    intro k
    have hpt : ∀ t : ℝ, ENNReal.ofReal (kinetic m (deriv (K k) t))
        ≤ lagrangian m h (K k t) (deriv (K k) t) := by
      intro t
      have hreg := ofReal_kinetic_add_pairPot_add_h_le_lagrangian (m := m) (h := h)
        (fun i => (hm i).le) hh.le (K k t) (deriv (K k) t)
      have hgoal : ENNReal.ofReal (kinetic m (deriv (K k) t))
          ≤ ENNReal.ofReal (kinetic m (deriv (K k) t)) + pairPot m (K k t) + ENNReal.ofReal h := by
        calc ENNReal.ofReal (kinetic m (deriv (K k) t))
            ≤ ENNReal.ofReal (kinetic m (deriv (K k) t)) + pairPot m (K k t) :=
              le_add_right le_rfl
          _ ≤ (ENNReal.ofReal (kinetic m (deriv (K k) t)) + pairPot m (K k t))
                + ENNReal.ofReal h := le_add_right le_rfl
      exact hgoal.trans hreg
    calc (∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv (K k) t)))
        ≤ ∫⁻ t in Set.Ioc 0 T, lagrangian m h (K k t) (deriv (K k) t) :=
          setLIntegral_mono' measurableSet_Ioc (fun t _ => hpt t)
      _ = actionOn m h (K k) 0 T := rfl
      _ = actionPot m h y (K k T) := by
          have h1 := hminT k
          rw [IsHMinimizer] at h1
          rw [h1, hK0 k]
      _ ≤ ENNReal.ofReal Cb := by
          refine (hest y (K k T)).trans (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_))
          have h2 := hdisp k T ⟨hT, le_rfl⟩
          have h4 : ‖y - K k T‖ ≤ 2 * R := by linarith
          have h5 : ‖y - K k T‖ ^ 2 ≤ (2 * R) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h4 2
          have h6 : 0 ≤ h * β := mul_nonneg hh.le hβ.le
          have h7 : h * β * ‖y - K k T‖ ^ 2 ≤ h * β * (2 * R) ^ 2 :=
            mul_le_mul_of_nonneg_left h5 h6
          have h8 : α * ‖y - K k T‖ ≤ α * (2 * R) := mul_le_mul_of_nonneg_left h4 hα.le
          linarith
  set M : ℝ := Real.sqrt (Cb / ((1 / 2) * c)) with hMdef
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hMsq : M ^ 2 = Cb / ((1 / 2) * c) := Real.sq_sqrt (by positivity)
  have hL2 : ∀ k, (∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (‖deriv (K k) t‖ ^ 2))
      ≤ ENNReal.ofReal (M ^ 2) := by
    intro k
    have h1 := euclidean_energy_le_of_kinetic (M := Real.sqrt Cb) hc hmc
      (by simpa [Real.sq_sqrt hCb0] using hkin k)
    simpa [hMsq, Real.sq_sqrt hCb0] using h1
  -- extraction
  have hKcont : ∀ k, ContinuousOn (K k) (Set.Icc 0 T) := by
    intro k
    have h := (hKacT k).continuousOn
    rwa [uIcc_of_le hT.le] at h
  obtain ⟨φ, hφ, γlim, hγlimcont, hconv⟩ :=
    exists_uniform_subseq hM0 hT.le hKcont hKacT hL2 ⟨y, hK0⟩
  have hγlim0 : γlim 0 = y := by
    refine tendsto_nhds_unique (hconv.tendsto_at (Set.left_mem_Icc.mpr hT.le)) ?_
    simpa only [hK0] using tendsto_const_nhds (x := y) (f := atTop)
  -- uniform convergence on the ball containing the curves
  have huni_ball : TendstoUniformlyOn (fun k x => normPot m h (P k) x) u atTop
      (Metric.closedBall y (2 * R)) := hPuni _ (isCompact_closedBall y (2 * R))
  have hmem_ball : ∀ t ∈ Set.Ioc 0 T, ∀ k, K (φ k) t ∈ Metric.closedBall y (2 * R) := by
    intro t ht k
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    have := hdisp (φ k) t ht
    linarith [hRnn]
  have hγlim_mem : ∀ t ∈ Set.Ioc 0 T, γlim t ∈ Metric.closedBall y (2 * R) := by
    intro t ht
    exact isClosed_closedBall.mem_of_tendsto (hconv.tendsto_at ⟨ht.1.le, ht.2⟩)
      (Eventually.of_forall (hmem_ball t ht))
  have hy_ball : y ∈ Metric.closedBall y (2 * R) := by
    rw [Metric.mem_closedBall, dist_self]
    linarith [hRnn]
  have hconv1 : Tendsto (fun k => normPot m h (P (φ k)) y) atTop (𝓝 (u y)) :=
    (huni_ball.tendsto_at hy_ball).comp hφ.tendsto_atTop
  have hAlim : ∀ t ∈ Set.Ioc 0 T,
      Tendsto (fun k => actionOn m h (K (φ k)) 0 t) atTop
        (𝓝 (ENNReal.ofReal (u y - u (γlim t)))) := by
    intro t ht
    have hconv2 : Tendsto (fun k => normPot m h (P (φ k)) (K (φ k) t)) atTop (𝓝 (u (γlim t))) :=
      tendsto_normPot_comp (huni_ball.seq_tendstoUniformlyOn φ hφ.tendsto_atTop) hu_dist
        (hmem_ball t ht) (hγlim_mem t ht) (hconv.tendsto_at ⟨ht.1.le, ht.2⟩)
    have hev : (fun k => actionOn m h (K (φ k)) 0 t) =ᶠ[atTop]
        fun k => ENNReal.ofReal (normPot m h (P (φ k)) y
          - normPot m h (P (φ k)) (K (φ k) t)) :=
      Eventually.of_forall fun k =>
        actionOn_eq_ofReal_normPot_sub (hKac (φ k)) (hKmin (φ k)) (hfin y (P (φ k))) (hK0 (φ k))
          (hKTau (φ k)) ht.1 (lt_of_le_of_lt ht.2 (hTauT (φ k)))
    have hlim' : Tendsto (fun k => ENNReal.ofReal (normPot m h (P (φ k)) y
        - normPot m h (P (φ k)) (K (φ k) t))) atTop
        (𝓝 (ENNReal.ofReal (u y - u (γlim t)))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hconv1.sub hconv2)
    exact hlim'.congr' hev.symm
  -- the value identity `φ_h(y, γ t) = u y - u (γ t)`
  have hval : ∀ t ∈ Set.Ioc 0 T,
      actionPot m h y (γlim t) = ENNReal.ofReal (u y - u (γlim t)) := by
    intro t ht
    have hlim1 : Tendsto (fun k => actionPot m h y (K (φ k) t)) atTop
        (𝓝 (ENNReal.ofReal (u y - u (γlim t)))) :=
      (hAlim t ht).congr' (Eventually.of_forall fun k => by
        have hm := hmin_le (φ k) t ht.1 ht.2
        rw [IsHMinimizer] at hm
        rw [hm, hK0 (φ k)])
    have hlim2 : Tendsto (fun k => actionPot m h y (K (φ k) t)) atTop
        (𝓝 (actionPot m h y (γlim t))) := by
      have hz : Tendsto (fun k => ‖K (φ k) t - γlim t‖) atTop (𝓝 0) := by
        have h' : Tendsto (fun k => K (φ k) t - γlim t) atTop (𝓝 (γlim t - γlim t)) :=
          (hconv.tendsto_at ⟨ht.1.le, ht.2⟩).sub (tendsto_const_nhds (x := γlim t))
        simpa using h'.norm
      have hp : Tendsto (fun k => α * ‖K (φ k) t - γlim t‖
          + h * β * ‖K (φ k) t - γlim t‖ ^ 2) atTop (𝓝 (α * 0 + h * β * 0 ^ 2)) :=
        (tendsto_const_nhds.mul hz).add (tendsto_const_nhds.mul (hz.pow 2))
      have hs : Tendsto (fun k => Real.sqrt (α * ‖K (φ k) t - γlim t‖
          + h * β * ‖K (φ k) t - γlim t‖ ^ 2)) atTop (𝓝 0) := by
        have h3 := (Real.continuous_sqrt.tendsto (α * 0 + h * β * 0 ^ 2)).comp hp
        have h4 : Real.sqrt (α * 0 + h * β * 0 ^ 2) = 0 := by simp
        rw [h4] at h3
        exact h3
      have hseq : Tendsto (fun k => (actionPot m h y (K (φ k) t)).toReal) atTop
          (𝓝 ((actionPot m h y (γlim t)).toReal)) := by
        refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
        refine squeeze_zero (fun k => norm_nonneg _)
          (fun k => ?_) (by simpa [Real.norm_eq_abs] using hs)
        rw [Real.norm_eq_abs]
        exact actionPot_toReal_sub_le' hα.le hβ.le hfin hest y _ _
      have h2 : Tendsto (fun k => ENNReal.ofReal ((actionPot m h y (K (φ k) t)).toReal)) atTop
          (𝓝 (ENNReal.ofReal ((actionPot m h y (γlim t)).toReal))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp hseq
      have h3 : (fun k => ENNReal.ofReal ((actionPot m h y (K (φ k) t)).toReal))
          = fun k => actionPot m h y (K (φ k) t) := by
        funext k; exact ENNReal.ofReal_toReal (hfin y _).ne
      rw [h3, ENNReal.ofReal_toReal (hfin y (γlim t)).ne] at h2
      exact h2
    exact tendsto_nhds_unique hlim2 hlim1
  -- lower semicontinuity of the action on the limit curve
  have hMWT := Commons.MeasureTheory.Integral.massWeighted_kinetic_le_liminf (m := m) (c := c)
    hc hmc hT.le (Real.sqrt_nonneg Cb) hγlimcont hconv (fun k => hKacT (φ k))
    (fun k => by
      have h := hkin (φ k)
      rw [lintegral_ofReal_kinetic_eq] at h
      simpa [Real.sq_sqrt hCb0] using h)
  have hcal : ∀ t ∈ Set.Ioc 0 T,
      actionOn m h γlim 0 t = ENNReal.ofReal (u y - u (γlim t)) := by
    intro t ht
    refine le_antisymm ?_ ?_
    · have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
      have hsub' : Set.Ioc 0 t ⊆ Set.Ioc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
      have hki : (∫⁻ s in Set.Ioc 0 t, ENNReal.ofReal (kinetic m (deriv γlim s)))
          ≤ liminf (fun k => ∫⁻ s in Set.Ioc 0 t,
              ENNReal.ofReal (kinetic m (deriv (K (φ k)) s))) atTop := by
        have h1 := Commons.MeasureTheory.Integral.massWeighted_kinetic_le_liminf
          (m := m) (c := c) hc hmc ht.1.le (Real.sqrt_nonneg Cb)
          (hγlimcont.mono hsub)
          (hconv.mono hsub)
          (fun k => (hKacT (φ k)).mono (by
            rw [uIcc_of_le ht.1.le, uIcc_of_le hT.le]
            exact hsub))
          (fun k => by
            have h : (∫⁻ s in Set.Ioc 0 t,
                ENNReal.ofReal (kinetic m (deriv (K (φ k)) s))) ≤ ENNReal.ofReal Cb :=
              (lintegral_mono_set (μ := volume) (s := Set.Ioc 0 t) (t := Set.Ioc 0 T)
                (f := fun s => ENNReal.ofReal (kinetic m (deriv (K (φ k)) s)))
                (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)).trans (hkin (φ k))
            rw [lintegral_ofReal_kinetic_eq] at h
            simpa [Real.sq_sqrt hCb0] using h)
        simp only [lintegral_ofReal_kinetic_eq] at h1
        exact h1.2
      have hγcont : ContinuousOn γlim (Set.Ioc 0 t) :=
        hγlimcont.mono (fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩)
      have hKcont' : ∀ k, ContinuousOn (K (φ k)) (Set.Ioc 0 t) := fun k =>
        (hKcont (φ k)).mono (fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩)
      have hp : (∫⁻ s in Set.Ioc 0 t, pairPot m (γlim s))
          ≤ liminf (fun k => ∫⁻ s in Set.Ioc 0 t, pairPot m (K (φ k) s)) atTop :=
        lintegral_pairPot_le_liminf' (fun i => (hm i).le)
          (fun s hs => hconv.tendsto_at ⟨hs.1.le, hs.2.trans ht.2⟩) hKcont'
      have hmain := actionOn_le_liminf hm hh.le
        (aemeasurable_pairPot_comp hγcont measurableSet_Ioc) hki hp
      rw [(hAlim t ht).liminf_eq] at hmain
      exact hmain
    · rw [← hval t ht]
      exact actionPot_le_of_interval ht.1 (by rw [hγlim0]) rfl
        (hMWT.1.mono (by
          rw [uIcc_of_le ht.1.le, uIcc_of_le hT.le]
          exact Set.Icc_subset_Icc le_rfl ht.2))
  refine ⟨γlim, hγlim0, hMWT.1, ?_, hcal⟩
  rw [IsHMinimizer, hγlim0]
  exact (hcal T ⟨hT, le_rfl⟩).trans (hval T ⟨hT, le_rfl⟩).symm



/-- Translation invariance of the action in the form used for concatenations. -/
lemma actionOn_comp_sub_const {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a L : ℝ} :
    actionOn m h (fun t => γ (t - a)) a (a + L) = actionOn m h γ 0 L := by
  have h1 := actionOn_comp_add_const (m := m) (h := h) (γ := fun t => γ (t - a)) (a := a) (L := L)
  have h2 : (fun t : ℝ => (fun s => γ (s - a)) (t + a)) = γ := by
    funext t
    show γ (t + a - a) = γ t
    rw [add_sub_cancel_right]
  rw [h2] at h1
  exact h1.symm

/-- Along a calibrating minimiser of a dominated function, the function `u` decreases. -/
lemma le_of_isHMinimizer_of_calibrating {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ}
    (hdom : Dominated m h u) {γ : ℝ → EN E N} {a b : ℝ} (hmin : IsHMinimizer m h γ a b)
    (hcal : actionOn m h γ a b = ENNReal.ofReal (u (γ a) - u (γ b))) :
    u (γ b) ≤ u (γ a) := by
  have h1 : ENNReal.ofReal (u (γ b) - u (γ a)) ≤ ENNReal.ofReal (u (γ a) - u (γ b)) := by
    calc ENNReal.ofReal (u (γ b) - u (γ a)) ≤ actionPot m h (γ a) (γ b) := hdom (γ a) (γ b)
      _ = actionOn m h γ a b := hmin.symm
      _ = ENNReal.ofReal (u (γ a) - u (γ b)) := hcal
  by_contra hcont
  have hlt : 0 < u (γ b) - u (γ a) := by
    have := not_le.mp hcont
    linarith
  have h2 : ENNReal.ofReal (u (γ b) - u (γ a)) = 0 := by
    rw [ENNReal.ofReal_eq_zero.mpr (by linarith : u (γ a) - u (γ b) ≤ 0)] at h1
    exact le_antisymm h1 bot_le
  exact (ENNReal.ofReal_pos.mpr hlt).ne' h2


/-- Two action potentials with the same second argument differ by at most the action potential of
the pair. -/
lemma abs_actionPot_sub_le {m : Fin N → ℝ} {h : ℝ}
    (hfin : ∀ a b : EN E N, actionPot m h a b < ⊤) (p x z : EN E N) :
    |(actionPot m h x p).toReal - (actionPot m h z p).toReal| ≤ (actionPot m h x z).toReal := by
  have h1 : actionPot m h x p ≤ actionPot m h x z + actionPot m h z p :=
    actionPot_triangle m h x z p
  have h2 : actionPot m h z p ≤ actionPot m h z x + actionPot m h x p :=
    actionPot_triangle m h z x p
  have h3 : (actionPot m h x p).toReal
      ≤ (actionPot m h x z).toReal + (actionPot m h z p).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(hfin x z).ne, (hfin z p).ne⟩) h1
    rwa [ENNReal.toReal_add (hfin x z).ne (hfin z p).ne] at h
  have h4 : (actionPot m h z p).toReal
      ≤ (actionPot m h z x).toReal + (actionPot m h x p).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(hfin z x).ne, (hfin x p).ne⟩) h2
    rwa [ENNReal.toReal_add (hfin z x).ne (hfin x p).ne] at h
  have h5 : (actionPot m h z x).toReal = (actionPot m h x z).toReal := by
    rw [actionPot_comm m h z x]
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Horofunctions are Lipschitz for `φ_h` in both directions.** -/
lemma ofReal_abs_sub_le_actionPot {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ} {p : ℕ → EN E N}
    (hupt : ∀ x : EN E N, Tendsto (fun k => normPot m h (p k) x) atTop (𝓝 (u x)))
    (hfin : ∀ a b : EN E N, actionPot m h a b < ⊤) (x z : EN E N) :
    ENNReal.ofReal |u x - u z| ≤ actionPot m h x z := by
  have hpt : ∀ k, ENNReal.ofReal |(actionPot m h x (p k)).toReal - (actionPot m h z (p k)).toReal|
      ≤ actionPot m h x z := fun k => by
    rw [← ENNReal.ofReal_toReal (hfin x z).ne]
    exact ENNReal.ofReal_le_ofReal (abs_actionPot_sub_le hfin (p k) x z)
  have hnorm : ∀ k, |(actionPot m h x (p k)).toReal - (actionPot m h z (p k)).toReal|
      = |normPot m h (p k) x - normPot m h (p k) z| := by
    intro k
    congr 1
    simp only [normPot]
    ring
  have hlim : Tendsto (fun k => ENNReal.ofReal
      |(actionPot m h x (p k)).toReal - (actionPot m h z (p k)).toReal|) atTop
      (𝓝 (ENNReal.ofReal |u x - u z|)) := by
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    simpa only [hnorm] using (((hupt x).sub (hupt z)).abs)
  exact le_of_tendsto hlim (Eventually.of_forall hpt)

/-- **The calibrating curve of a horofunction.**  For any configuration `x` there is a curve
`γ : ℝ → Eᴺ` with `γ 0 = x` which is an `h`-minimiser on every `[0,t]` and calibrates the
horofunction: `A(γ|[0,t]) = 𝔲 x - 𝔲 (γ t)`. -/
theorem exists_calibrating_curve {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ} {p : ℕ → EN E N}
    (hN : 0 < N) (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hdom : Dominated m h u)
    (hpnc : ∀ k, WithoutCollisions (p k))
    (hpgrow : Tendsto (fun k => ‖p k‖) atTop atTop)
    (huni : ∀ K : Set (EN E N), IsCompact K →
      TendstoUniformlyOn (fun k x => normPot m h (p k) x) u atTop K)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hest : ∀ x z : EN E N, actionPot m h x z ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2)))
    (x : EN E N) :
    ∃ γ : ℝ → EN E N, γ 0 = x ∧ ∀ t : ℝ, 0 < t →
      AbsolutelyContinuousOnInterval γ 0 t ∧ IsHMinimizer m h γ 0 t ∧
        actionOn m h γ 0 t = ENNReal.ofReal (u x - u (γ t)) := by
  classical
  have hfin : ∀ a b : EN E N, actionPot m h a b < ⊤ :=
    fun a b => lt_of_le_of_lt (hest a b) ENNReal.ofReal_lt_top
  have hupt : ∀ y : EN E N, Tendsto (fun k => normPot m h (p k) y) atTop (𝓝 (u y)) :=
    fun y => (huni {y} isCompact_singleton).tendsto_at (Set.mem_singleton y)
  have hlip : ∀ y z : EN E N, ENNReal.ofReal |u y - u z| ≤ actionPot m h y z :=
    fun y z => ofReal_abs_sub_le_actionPot hupt hfin y z
  have hstep : ∀ y : EN E N, ∃ γ : ℝ → EN E N, γ 0 = y ∧
      AbsolutelyContinuousOnInterval γ 0 1 ∧ IsHMinimizer m h γ 0 1 ∧
      ∀ t ∈ Set.Ioc 0 1, actionOn m h γ 0 t = ENNReal.ofReal (u y - u (γ t)) :=
    fun y => exists_calibrating_interval (m := m) (h := h) (u := u) (p := p) hN hm hh hdom hpnc
      hpgrow huni hα hβ hest (y := y) (T := 1) one_pos
  -- the inductive invariant
  let P : ℕ → (ℝ → EN E N) → Prop := fun n γ =>
    γ 0 = x ∧ AbsolutelyContinuousOnInterval γ 0 ((n : ℝ) + 1) ∧
      IsHMinimizer m h γ 0 ((n : ℝ) + 1) ∧
      (∀ t ∈ Set.Ioc 0 ((n : ℝ) + 1), actionOn m h γ 0 t = ENNReal.ofReal (u x - u (γ t)))
  -- the curve extending `γ` beyond time `n + 1`
  let mkNext : (n : ℕ) → (ℝ → EN E N) → ℝ → EN E N := fun n γ t =>
    if t ≤ (n : ℝ) + 1 then γ t
    else (Classical.choose (hstep (γ ((n : ℝ) + 1)))) (t - ((n : ℝ) + 1))
  let seq : ℕ → ℝ → EN E N := fun n =>
    Nat.rec (Classical.choose (hstep x)) (fun n ih => mkNext n ih) n
  have hseq0 : seq 0 = Classical.choose (hstep x) := rfl
  have hseqS : ∀ n, seq (n + 1) = mkNext n (seq n) := fun n => rfl
  have hseq : ∀ n, P n (seq n) := by
    intro n
    induction n with
    | zero =>
      rw [hseq0]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (Classical.choose_spec (hstep x)).1
      · simpa using (Classical.choose_spec (hstep x)).2.1
      · simpa using (Classical.choose_spec (hstep x)).2.2.1
      · intro t ht
        exact (Classical.choose_spec (hstep x)).2.2.2 t (by simpa using ht)
    | succ n ih =>
      rw [hseqS n]
      obtain ⟨h0, hac, hmin, hcal⟩ := ih
      set c : ℝ := (n : ℝ) + 1 with hc
      have hcpos : 0 < c := by rw [hc]; positivity
      have hcalc : actionOn m h (seq n) 0 c = ENNReal.ofReal (u x - u (seq n c)) :=
        hcal c ⟨hcpos, le_rfl⟩
      obtain ⟨ht0, htac, htmin, htcal⟩ := Classical.choose_spec (hstep (seq n c))
      have hmk : ∀ t, mkNext n (seq n) t
          = if t ≤ c then seq n t else (Classical.choose (hstep (seq n c))) (t - c) := by
        intro t
        show (if t ≤ (n : ℝ) + 1 then seq n t
          else (Classical.choose (hstep (seq n ((n : ℝ) + 1)))) (t - ((n : ℝ) + 1))) = _
        rw [hc]
      have hagree : ∀ t, t ≤ c → mkNext n (seq n) t = seq n t := by
        intro t ht
        rw [hmk t, if_pos ht]
      have hshift : ∀ t, c < t → mkNext n (seq n) t = (Classical.choose (hstep (seq n c))) (t - c) := by
        intro t ht
        rw [hmk t, if_neg (not_le_of_gt ht)]
      -- absolute continuity
      have hac_shift : AbsolutelyContinuousOnInterval
          (fun t : ℝ => (Classical.choose (hstep (seq n c))) (t - c)) c (c + 1) := by
        have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
          (f := Classical.choose (hstep (seq n c))) (a := (0 : ℝ)) (b := 1) (c := 1) (d := -c)
          one_ne_zero htac
        have h2 : (0 - -c) / 1 = c := by ring
        have h3 : (1 - -c) / 1 = c + 1 := by ring
        rw [h2, h3] at h
        simpa [sub_eq_add_neg] using h
      have hjoin : seq n c = (fun t : ℝ => (Classical.choose (hstep (seq n c))) (t - c)) c := by
        simp only [sub_self]
        exact ht0.symm
      have hac' : AbsolutelyContinuousOnInterval (mkNext n (seq n)) 0 (c + 1) := by
        have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_concat
          (f := seq n) (g := fun t : ℝ => (Classical.choose (hstep (seq n c))) (t - c))
          (a := 0) (c := c) (b := c + 1) (by linarith) (by linarith) hjoin hac hac_shift
        simpa only [hmk] using h
      -- the action of the initial piece
      have hleft : ∀ t, 0 < t → t ≤ c →
          actionOn m h (mkNext n (seq n)) 0 t = actionOn m h (seq n) 0 t := by
        intro t _ htc
        unfold actionOn
        refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
        filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
          (MeasureTheory.measure_singleton t)] with s hs hsI
        have hst : s < t := lt_of_le_of_ne hsI.2 hs
        have hsc : s < c := lt_of_lt_of_le hst htc
        have hev : mkNext n (seq n) =ᶠ[𝓝 s] (seq n) := by
          refine Eventually.mono (IsOpen.mem_nhds isOpen_Iio hsc) ?_
          intro u hu
          exact hagree u (le_of_lt hu)
        rw [hev.deriv_eq, hagree s hsc.le]
      -- the action of the final piece
      have hpiece : ∀ t, c < t → actionOn m h (mkNext n (seq n)) c t
          = actionOn m h (Classical.choose (hstep (seq n c))) 0 (t - c) := by
        intro t hct
        have hshift_eq : actionOn m h (mkNext n (seq n)) c t
            = actionOn m h (fun s : ℝ => (Classical.choose (hstep (seq n c))) (s - c)) c t := by
          unfold actionOn
          refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
          filter_upwards with s hs
          have hcs : c < s := hs.1
          have hev : mkNext n (seq n) =ᶠ[𝓝 s]
              (fun u : ℝ => (Classical.choose (hstep (seq n c))) (u - c)) := by
            refine Eventually.mono (IsOpen.mem_nhds isOpen_Ioi hcs) ?_
            intro u hu
            exact hshift u hu
          rw [hev.deriv_eq, hshift s hcs]
          rfl
        rw [hshift_eq, ← actionOn_comp_sub_const
          (γ := Classical.choose (hstep (seq n c))) (a := c) (L := t - c)]
        congr 1
        ring
      -- the calibration
      have htfin : actionOn m h (Classical.choose (hstep (seq n c))) 0 1 < ⊤ := by
        rw [htcal 1 ⟨one_pos, le_rfl⟩]; exact ENNReal.ofReal_lt_top
      have hcal' : ∀ t ∈ Set.Ioc 0 (c + 1), actionOn m h (mkNext n (seq n)) 0 t
          = ENNReal.ofReal (u x - u (mkNext n (seq n) t)) := by
        intro t ht
        by_cases htc : t ≤ c
        · rw [hleft t ht.1 htc, hcal t ⟨ht.1, htc⟩, hagree t htc]
        · have hct : c < t := not_le.mp htc
          have h1 : actionOn m h (mkNext n (seq n)) 0 t
              = actionOn m h (mkNext n (seq n)) 0 c + actionOn m h (mkNext n (seq n)) c t :=
            actionOn_add (mkNext n (seq n)) hcpos.le hct.le
          have h4 : actionOn m h (seq n) 0 c = ENNReal.ofReal (u x - u (seq n c)) := hcalc
          have h5 : actionOn m h (Classical.choose (hstep (seq n c))) 0 (t - c)
              = ENNReal.ofReal (u (seq n c)
                - u ((Classical.choose (hstep (seq n c))) (t - c))) :=
            htcal (t - c) ⟨by linarith [ht.2], by linarith [ht.2]⟩
          have hmin' : IsHMinimizer m h (Classical.choose (hstep (seq n c))) 0 (t - c) := by
            rcases lt_or_eq_of_le (by linarith [ht.2] : t - c ≤ 1) with h1 | h1
            · exact IsHMinimizer.sub_left htac htmin htfin (by linarith [hct]) h1
            · rw [h1]; exact htmin
          have haz : 0 ≤ u x - u (seq n c) := by
            by_contra hneg
            push_neg at hneg
            have h2 : ENNReal.ofReal |u x - u (seq n c)|
                ≤ ENNReal.ofReal (u x - u (seq n c)) := by
              have h3a := hmin.symm
              rw [h0] at h3a
              have h3 : actionPot m h x (seq n c) = ENNReal.ofReal (u x - u (seq n c)) := by
                rw [h3a, hcalc]
              rw [← h3]
              exact hlip x (seq n c)
            rw [ENNReal.ofReal_eq_zero.mpr hneg.le] at h2
            exact (ENNReal.ofReal_pos.mpr (abs_pos.mpr (ne_of_lt hneg))).ne'
              (le_antisymm h2 bot_le)
          have hbz : 0 ≤ u (seq n c) - u ((Classical.choose (hstep (seq n c))) (t - c)) := by
            by_contra hneg
            push_neg at hneg
            have h2 : ENNReal.ofReal |u (seq n c)
                - u ((Classical.choose (hstep (seq n c))) (t - c))|
                ≤ ENNReal.ofReal (u (seq n c)
                  - u ((Classical.choose (hstep (seq n c))) (t - c))) := by
              have h3a := hmin'.symm
              rw [ht0] at h3a
              have h3 : actionPot m h (seq n c)
                  ((Classical.choose (hstep (seq n c))) (t - c))
                  = ENNReal.ofReal (u (seq n c)
                    - u ((Classical.choose (hstep (seq n c))) (t - c))) := by
                rw [h3a, h5]
              rw [← h3]
              exact hlip (seq n c) _
            rw [ENNReal.ofReal_eq_zero.mpr hneg.le] at h2
            exact (ENNReal.ofReal_pos.mpr (abs_pos.mpr (ne_of_lt hneg))).ne'
              (le_antisymm h2 bot_le)
          rw [h1, hleft c hcpos le_rfl, h4, hpiece t hct, h5, hshift t hct]
          rw [← ENNReal.ofReal_add haz hbz]
          ring_nf
      -- the minimiser property
      have hmin'' : IsHMinimizer m h (mkNext n (seq n)) 0 (c + 1) := by
        rw [IsHMinimizer]
        refine le_antisymm ?_ (actionPot_le_of_interval (by linarith) rfl rfl hac')
        calc actionOn m h (mkNext n (seq n)) 0 (c + 1)
            = ENNReal.ofReal (u x - u (mkNext n (seq n) (c + 1))) :=
              hcal' (c + 1) ⟨by linarith, le_rfl⟩
          _ = ENNReal.ofReal (u (mkNext n (seq n) 0) - u (mkNext n (seq n) (c + 1))) := by
              rw [hagree 0 (le_of_lt hcpos), h0]
          _ ≤ ENNReal.ofReal |u (mkNext n (seq n) 0) - u (mkNext n (seq n) (c + 1))| :=
              ENNReal.ofReal_le_ofReal (le_abs_self _)
          _ ≤ actionPot m h (mkNext n (seq n) 0) (mkNext n (seq n) (c + 1)) := hlip _ _
      have h0' : mkNext n (seq n) 0 = x := by
        rw [hagree 0 (le_of_lt hcpos), h0]
      refine ⟨h0', ?_, ?_, ?_⟩
      · simpa only [Nat.cast_add, Nat.cast_one, hc] using hac'
      · simpa only [Nat.cast_add, Nat.cast_one, hc] using hmin''
      · intro t ht
        exact hcal' t (by simpa only [Nat.cast_add, Nat.cast_one, hc] using ht)
  -- agreement of consecutive curves
  have hagreeG : ∀ (n : ℕ) (t : ℝ), t ≤ (n : ℝ) + 1 → seq (n + 1) t = seq n t := by
    intro n t ht
    rw [hseqS n]
    show (if t ≤ (n : ℝ) + 1 then seq n t
      else (Classical.choose (hstep (seq n ((n : ℝ) + 1)))) (t - ((n : ℝ) + 1))) = seq n t
    rw [if_pos ht]
  -- the nested family
  have hnest : ∀ (m n : ℕ), n ≤ m → ∀ t : ℝ, t ≤ (n : ℝ) + 1 → seq m t = seq n t := by
    intro m
    induction m with
    | zero =>
      intro n hn t _
      rw [Nat.le_zero.mp hn]
    | succ m ih =>
      intro n hn t ht
      rcases Nat.lt_or_eq_of_le hn with hlt | heq
      · have hnm : n ≤ m := Nat.lt_succ_iff.mp hlt
        have ht' : t ≤ (m : ℝ) + 1 := by
          have h2 : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
          linarith
        rw [hagreeG m t ht', ih n hnm t ht]
      · rw [heq]
  -- the global curve
  let g : ℝ → EN E N := fun t => seq (Nat.floor t) t
  have hg0 : g 0 = x := by
    have h1 : g 0 = seq (Nat.floor (0 : ℝ)) 0 := rfl
    rw [h1, Nat.floor_zero]
    exact (hseq 0).1
  refine ⟨g, hg0, ?_⟩
  intro t htp
  set N : ℕ := Nat.floor t with hN
  have htN : t < (N : ℝ) + 1 := by
    rw [hN]; exact Nat.lt_floor_add_one t
  have hgt : ∀ s, 0 ≤ s → s ≤ t → g s = seq N s := by
    intro s hs0 hst
    have hsN : Nat.floor s ≤ N := by
      rw [hN]; exact Nat.floor_mono hst
    have hs1 : s ≤ ((Nat.floor s : ℕ) : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one s)
    show seq (Nat.floor s) s = seq N s
    exact (hnest N (Nat.floor s) hsN s hs1).symm
  have hAg : actionOn m h g 0 t = actionOn m h (seq N) 0 t := by
    unfold actionOn
    refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
      (MeasureTheory.measure_singleton t)] with s hs hsI
    have hst : s < t := lt_of_le_of_ne hsI.2 hs
    have hev : g =ᶠ[𝓝 s] (seq N) := by
      have hmem : Set.Ioo 0 t ∈ 𝓝 s := IsOpen.mem_nhds isOpen_Ioo ⟨hsI.1, hst⟩
      refine Eventually.mono hmem ?_
      intro u hu
      exact hgt u hu.1.le hu.2.le
    rw [hev.deriv_eq, hgt s hsI.1.le hsI.2]
  have hacg : AbsolutelyContinuousOnInterval g 0 t := by
    have h1 : AbsolutelyContinuousOnInterval (seq N) 0 t :=
      ((hseq N).2.1).mono (by
        rw [uIcc_of_le htp.le, uIcc_of_le (by positivity : (0:ℝ) ≤ (N:ℝ) + 1)]
        exact Set.Icc_subset_Icc le_rfl (le_of_lt htN))
    rw [absolutelyContinuousOnInterval_iff] at h1 ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδprop⟩ := h1 ε hε
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    rw [show (∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2))
        = ∑ i ∈ Finset.range E.1, dist ((seq N) (E.2 i).1) ((seq N) (E.2 i).2) from
      Finset.sum_congr rfl (fun i hi => by
        have h := hE
        simp only [AbsolutelyContinuousOnInterval.disjWithin, Set.mem_setOf_eq] at h
        rw [uIcc_of_le htp.le] at h
        obtain ⟨h1i, h2i⟩ := h.1 i hi
        rw [hgt _ h1i.1 h1i.2, hgt _ h2i.1 h2i.2])]
    exact hδprop E hE hlen
  have hfinN : actionOn m h (seq N) 0 ((N : ℝ) + 1) < ⊤ := by
    rw [(hseq N).2.2.2 _ ⟨by positivity, le_rfl⟩]
    exact ENNReal.ofReal_lt_top
  have hminN : IsHMinimizer m h (seq N) 0 t :=
    IsHMinimizer.sub_left (hseq N).2.1 (hseq N).2.2.1 hfinN htp htN
  have hgt0 : g t = seq N t := hgt t htp.le le_rfl
  have hg0N : seq N 0 = x := by
    rw [hnest N 0 (Nat.zero_le N) 0 (by norm_num : (0:ℝ) ≤ ((0:ℕ):ℝ) + 1)]
    exact (hseq 0).1
  refine ⟨hacg, ?_, ?_⟩
  · rw [IsHMinimizer]
    calc actionOn m h g 0 t = actionOn m h (seq N) 0 t := hAg
      _ = actionPot m h (seq N 0) (seq N t) := hminN
      _ = actionPot m h (g 0) (g t) := by rw [hg0N, hg0, hgt0]
  · rw [hAg, (hseq N).2.2.2 t ⟨htp, htN.le⟩, hgt0]

end Submission.NBody
