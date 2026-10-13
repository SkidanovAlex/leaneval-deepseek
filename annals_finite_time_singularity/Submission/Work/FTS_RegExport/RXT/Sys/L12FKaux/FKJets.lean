import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Standing
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FtauSlot
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.FKJets` — the angular moments `Q = ∫_θ K(θ)·D_z^k F(τ)` and their `z`-derivatives

`FK F z = ∫_θ F z θ K(θ) dθ` is the `k = 0` member of the family

  `Q(k)(z) = ∫_θ K(θ) · D_z^k F(τ)(z,θ) dθ`,

and `D_z^{k+1}(L₁₂ F)(z) = -Q(k)(z)`.  The module provides

* `Qlim`, `Qapp` — the moments of the limit profile `F(τ) = F_* + slice g τ` and of the
  approximants `F(τ) = F_* + slice (gn n) τ`;
* `Qapp_hasDerivAt` — `∂_z Q(n,k) = Q(n,k+1)/z` (differentiation under the angular integral);
* `Qapp_tendsto` — `Q(n,k) → Q(k)` along the approximants (dominated convergence in `θ`);
* `Qapp_bound` — the uniform bound `|Q(n,k)| ≤ 3(π/2)C_B`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- `K ≥ 0` on the angular interval. -/
theorem K_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc
    ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  positivity

/-- The `k`-th angular moment of the limit profile `F(τ) = F_* + slice g τ`. -/
def Qlim (α : ℝ) (g : Fam) (τ : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
    (Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      + Work.Spaces.DzIter k (slice g τ) z θ)

/-- The `k`-th angular moment of the approximant `F_* + slice (gn n) τ`. -/
def Qapp (α : ℝ) (gn : ℕ → Fam) (τ : ℝ) (n k : ℕ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
    Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
      (gn n) τ) z θ

/-! ## §1 Differentiating in `z` -/

/-- `∂_z (D_z^k f) = D_z^{k+1} f / z`. -/
theorem pz_DzIter_eq {f : ℝ → ℝ → ℝ} (k : ℕ) {z θ : ℝ} (hz : z ≠ 0) :
    Work.Spaces.pz (Work.Spaces.DzIter k f) z θ
      = Work.Spaces.DzIter (k + 1) f z θ / z := by
  show Work.Spaces.pz (Work.Spaces.DzIter k f) z θ
    = (z * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ) / z
  rw [mul_div_cancel_left₀ _ hz]

/-- **Differentiation under the angular integral**: `∂_z Q(n,k) = Q(n,k+1)/z` for `k ≤ 1`. -/
theorem Qapp_hasDerivAt {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {τ : ℝ} {CB : ℝ} (hCB : 0 ≤ CB)
    (h3 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (n : ℕ) {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Qapp α gn τ n k) (Qapp α gn τ n (k + 1) z / z) z := by
  have h2 : ContDiffOn ℝ 2 (Function.uncurry
      (Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0 k 2
      ((h3 n).of_le (Nat.cast_le.mpr (by omega : 2 + k ≤ 4)))
  have hb0 : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) x θ| ≤ CB := by
    intro x hx θ hθ
    exact hsl n k (by omega) x θ (by linarith [hx.1, hz]) hθ.1 hθ.2
  have hb : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pz (Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ)) x θ| ≤ 2 * CB / z := by
    intro x hx θ hθ
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hbnd := hsl n (k + 1) (by omega) x θ hx0 hθ.1 hθ.2
    have hval : Work.Spaces.DzIter (k + 1) (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) x θ
        = x * deriv (fun z' => Work.Spaces.DzIter k (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (gn n) τ) z' θ) x := rfl
    rw [hval, abs_mul, abs_of_pos hx0] at hbnd
    rw [Work.Spaces.pz]
    have h1 : |deriv (fun z' => Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) z' θ) x| ≤ CB / x := by
      rw [le_div_iff₀ hx0]
      linarith [hbnd]
    have h2' : CB / x ≤ 2 * CB / z := by
      have hzx : z ≤ 2 * x := by linarith [hx.1]
      have h3' : 1 / x ≤ 2 / z := by
        rw [div_le_div_iff₀ hx0 hz]
        linarith
      calc CB / x = CB * (1 / x) := by ring
        _ ≤ CB * (2 / z) := mul_le_mul_of_nonneg_left h3' hCB
        _ = 2 * CB / z := by ring
    linarith [h1, h2']
  have hCmax : (0 : ℝ) ≤ max CB (2 * CB / z) := le_trans hCB (le_max_left _ _)
  have hb' : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pz (Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ)) x θ| ≤ max CB (2 * CB / z) :=
    fun x hx θ hθ => le_trans (hb x hx θ hθ) (le_max_right _ _)
  have hb0' : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) x θ| ≤ max CB (2 * CB / z) :=
    fun x hx θ hθ => le_trans (hb0 x hx θ hθ) (le_max_left _ _)
  have key := hasDerivAt_integral_Itheta_K (f := Work.Spaces.DzIter k
    (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
    h2 hz hCmax hb' hb0'
  have hval : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
      (Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ)) z θ)
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter (k + 1)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ) / z := by
    rw [← MeasureTheory.integral_div]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    show Work.Spaces.K θ * Work.Spaces.pz (Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ)) z θ
      = Work.Spaces.K θ * Work.Spaces.DzIter (k + 1) (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) z θ / z
    rw [pz_DzIter_eq k (ne_of_gt hz)]
    ring
  rw [hval] at key
  have hdef : Qapp α gn τ n k
      = fun x => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter k
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) x θ := rfl
  rw [hdef]
  exact key

/-! ## §2 Convergence along the approximants -/

/-- **Dominated convergence in `θ`**: `Q(n,k) z → Q(k) z` for `k ≤ 2`. -/
theorem Qapp_tendsto {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {g : Fam} {τ : ℝ} {Cw CB : ℝ} (hCw : 0 ≤ Cw) (hCB : 0 ≤ CB)
    (h4 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (h2 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (hjet : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)))
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun n => Qapp α gn τ n k z) Filter.atTop (𝓝 (Qlim α g τ k z)) := by
  have hKc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rw [Work.Spaces.K]
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  have hKcont : Continuous fun θ : ℝ => Work.Spaces.K θ * CB := by
    have hfun : Work.Spaces.K = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 := by
      funext θ; rw [Work.Spaces.K]
    rw [hfun]
    exact ((continuous_const.mul Real.continuous_sin).mul
      (Real.continuous_cos.pow 2)).mul continuous_const
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ
      * Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ) (volume.restrict Work.Spaces.Iθ) := by
    intro n
    have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0 k 0
        (by simpa using (h2 n).of_le (Nat.cast_le.mpr (by omega : 0 + k ≤ 4)))).continuousOn
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2
        * Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (gn n) τ) p.1 p.2) Work.FTS.EllipticEst.Q0 := hKc.mul hD
    exact Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0
      (g := fun x θ => Work.Spaces.K θ * Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) x θ) hcont hz
  have hint : Integrable (fun θ : ℝ => Work.Spaces.K θ * CB)
      (volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (3 * CB))
      (hKcont.continuousOn.aestronglyMeasurable measurableSet_Icc) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    show ‖Work.Spaces.K θ * CB‖ ≤ 3 * CB
    have hK3 : Work.Spaces.K θ ≤ 3 := by
      have h := abs_K_le_three θ
      rwa [abs_of_nonneg (K_nonneg_Iθ hθ)] at h
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K_nonneg_Iθ hθ), abs_of_nonneg hCB]
    exact mul_le_mul_of_nonneg_right hK3 hCB
  have hbound : ∀ n : ℕ, ∀ᵐ a ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K a * Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) z a‖ ≤ Work.Spaces.K a * CB := by
    intro n
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
      simp only [hK0, zero_mul, norm_zero, le_refl]
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      simp only [hK1, zero_mul, norm_zero, le_refl]
    show ‖Work.Spaces.K θ * Work.Spaces.DzIter k (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (gn n) τ) z θ‖ ≤ Work.Spaces.K θ * CB
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K_nonneg_Iθ ⟨h0.le, h1.le⟩)]
    exact mul_le_mul_of_nonneg_left (hsl n k (by omega) z θ hz h0 h1)
      (K_nonneg_Iθ ⟨h0.le, h1.le⟩)
  have hlim : ∀ᵐ a ∂(volume.restrict Work.Spaces.Iθ), Filter.Tendsto
      (fun n => Work.Spaces.K a * Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) z a) Filter.atTop
      (𝓝 (Work.Spaces.K a * (Work.Spaces.DzIter k
          (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z a
        + Work.Spaces.DzIter k (slice g τ) z a))) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
      simp only [hK0, zero_mul]
      exact tendsto_const_nhds
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      simp only [hK1, zero_mul]
      exact tendsto_const_nhds
    have hQ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, h0, h1⟩
    have hadd : ∀ n : ℕ, Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ
        = Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter k (slice (gn n) τ) z θ :=
      fun n => DzIter_Fstar_add (β := Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.pExp_pos hα) (Work.FTS.Regularity.pExp_le_one hα13)
        (h4 n) hk z θ hz h0 h1
    have h1' : Filter.Tendsto (fun n => Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ)
        Filter.atTop (𝓝 (Work.Spaces.DzIter k
          (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter k (slice g τ) z θ)) := by
      refine ((tendsto_const_nhds.add (hjet k hk z θ hQ))).congr' ?_
      filter_upwards with n
      exact (hadd n).symm
    show Filter.Tendsto (fun n => Work.Spaces.K θ * Work.Spaces.DzIter k
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ) Filter.atTop
      (𝓝 (Work.Spaces.K θ * (Work.Spaces.DzIter k
          (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice g τ) z θ)))
    exact tendsto_const_nhds.mul h1'
  have key := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iθ)
    (F := fun n θ => Work.Spaces.K θ * Work.Spaces.DzIter k
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ)
    (f := fun θ => Work.Spaces.K θ * (Work.Spaces.DzIter k
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      + Work.Spaces.DzIter k (slice g τ) z θ))
    (bound := fun θ => Work.Spaces.K θ * CB) hFmeas hint hbound hlim
  simpa only [Qapp, Qlim] using key

/-! ## §3 The uniform bound on the moments -/

/-- **`|Q(n,k) z| ≤ 3(π/2)C_B`** for `k ≤ 2`. -/
theorem Qapp_bound {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {τ : ℝ} {CB : ℝ} (hCB : 0 ≤ CB)
    (h2 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (n : ℕ) {k : ℕ} (hk : k ≤ 3) {z : ℝ} (hz : 0 < z) :
    |Qapp α gn τ n k z| ≤ 3 * (Real.pi / 2) * CB := by
  have hmem : AEStronglyMeasurable (fun θ : ℝ => |Work.Spaces.K θ * Work.Spaces.DzIter k
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    have hKc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
        Work.FTS.EllipticEst.Q0 := by
      have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
          = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
        funext p; rw [Work.Spaces.K]
      rw [hfun]
      exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
        ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
    have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0 k 0
        (by simpa using (h2 n).of_le (Nat.cast_le.mpr (by omega : 0 + k ≤ 4)))).continuousOn
    refine Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0
      (g := fun x θ => |Work.Spaces.K θ * Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) x θ|) ?_ hz
    have hfun : Function.uncurry (fun x θ => |Work.Spaces.K θ * Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) x θ|)
        = fun p : ℝ × ℝ => |Work.Spaces.K p.2
          * Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (gn n) τ) p.1 p.2| := rfl
    rw [hfun]
    exact (hKc.mul hD).abs
  have hint : Integrable (fun θ : ℝ => |Work.Spaces.K θ * Work.Spaces.DzIter k
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.mono' (integrable_const (3 * CB)) hmem ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    try dsimp only
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
      show ‖|Work.Spaces.K 0 * Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) z 0|‖ ≤ 3 * CB
      rw [hK0, zero_mul, abs_zero, norm_zero]
      linarith [hCB]
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      show ‖|Work.Spaces.K (Real.pi / 2) * Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) z (Real.pi / 2)|‖ ≤ 3 * CB
      rw [hK1, zero_mul, abs_zero, norm_zero]
      linarith [hCB]
    show ‖|Work.Spaces.K θ * Work.Spaces.DzIter k (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (gn n) τ) z θ|‖ ≤ 3 * CB
    rw [Real.norm_eq_abs, abs_abs, abs_mul]
    exact mul_le_mul (abs_K_le_three θ) (hsl n k (by omega) z θ hz h0 h1) (abs_nonneg _)
      (by norm_num)
  have h1 : ‖Qapp α gn τ n k z‖
      ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Spaces.K θ * Work.Spaces.DzIter k
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ‖ := by
    rw [Qapp]
    exact MeasureTheory.norm_integral_le_integral_norm _
  have h2' : (∫ θ in Work.Spaces.Iθ, ‖Work.Spaces.K θ * Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ‖)
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * CB := by
    refine MeasureTheory.integral_mono_ae hint (MeasureTheory.integrable_const _) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    try dsimp only
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
      rw [hK0, zero_mul, norm_zero]
      linarith [hCB]
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      rw [hK1, zero_mul, norm_zero]
      linarith [hCB]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_K_le_three θ) (hsl n k (by omega) z θ hz h0 h1) (abs_nonneg _)
      (by norm_num)
  have h3 : (∫ θ in Work.Spaces.Iθ, 3 * CB) = 3 * (Real.pi / 2) * CB := by
    rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [Real.norm_eq_abs] at h1
  linarith [h1, h2', le_of_eq h3]

end Work.FTS_RegExport.RXT.Sys.L12FKaux
