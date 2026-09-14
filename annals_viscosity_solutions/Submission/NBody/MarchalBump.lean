import Submission.NBody.MarchalStandardVariation
import Submission.NBody.MarchalDerivBound
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_add_lipschitzWith

/-!
# The symmetric bump: the competitor of Marchal's theorem

Ferrario--Terracini's standard variation `v^δ` (see `Submission.NBody.stdVar`) is applied **on both
sides** of the collision time `t₀`: the competitor of `γ` is

  `η(t₀ ± u) = γ(t₀ ± u) + λ^{2/3} • stdPert m k i₀ δ T u`   for `0 ≤ u ≤ λT`.

The point of the symmetry is that `η` is **continuous at `t₀`** (both one-sided limits equal
`γ(t₀) + λ^{2/3}·stdPertVec m k i₀ δ`), hence `η` is absolutely continuous on `[a,b]` with the
same endpoints as `γ` — so it is an admissible competitor for `IsHMinimizer`, and no `actionPot`
detour (which would cost `Θ(‖δ‖^{1/2})` and destroy the argument) is needed.  Moreover the
potential gain is obtained twice, once per side.

This file contains the definition of the bump, its Lipschitz bound (whence the absolute continuity
of `η`), and the abstract reduction: **any** absolutely continuous competitor with the same
endpoints and strictly smaller action contradicts minimality.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The centred perturbation vector is linear in the displacement. -/
lemma stdPertVec_smul_apply {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N}
    (c : ℝ) (v : E) : stdPertVec m k i₀ (c • v) = c • stdPertVec m k i₀ v := by
  refine PiLp.ext fun i => ?_
  rw [PiLp.smul_apply]
  by_cases hi : i ∈ k
  · rw [stdPertVec_apply_of_mem hi, stdPertVec_apply_of_mem hi, smul_smul, smul_smul, mul_comm]
  · rw [stdPertVec_apply_of_notMem hi, stdPertVec_apply_of_notMem hi, smul_zero]

/-- The standard perturbation at time `t` is the scalar coefficient of the standard variation times
the centred perturbation vector. -/
lemma stdPert_eq_smul_stdPertVec {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N}
    (δ : E) (T t : ℝ) :
    stdPert m k i₀ δ T t = stdCoef δ T t • stdPertVec m k i₀ δ := by
  unfold stdPert stdVar
  rw [stdPertVec_smul_apply]

/-- The scalar coefficient of the standard variation is Lipschitz with constant `‖δ‖⁻¹`. -/
lemma lipschitzWith_stdCoef {δ : E} (hδ : δ ≠ 0) (T : ℝ) :
    LipschitzWith ⟨(‖δ‖)⁻¹, inv_nonneg.mpr (norm_nonneg δ)⟩ (stdCoef δ T) := by
  have hd : (0:ℝ) < ‖δ‖ := norm_pos_iff.mpr hδ
  have hbase : ∀ x y : ℝ, |(T - x)/‖δ‖ - (T - y)/‖δ‖| ≤ (‖δ‖)⁻¹ * |x - y| := by
    intro x y
    have hkey : (T - x)/‖δ‖ - (T - y)/‖δ‖ = (y - x)/‖δ‖ := by ring
    rw [hkey, abs_div, abs_of_pos hd, abs_sub_comm, div_eq_mul_inv, mul_comm]
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq]
  simp only [stdCoef]
  have h1 := abs_min_sub_min_le_max (1:ℝ) (max 0 ((T-x)/‖δ‖)) 1 (max 0 ((T-y)/‖δ‖))
  have h2 := abs_max_sub_max_le_max (0:ℝ) ((T-x)/‖δ‖) 0 ((T-y)/‖δ‖)
  simp only [sub_self, abs_zero] at h1 h2
  have h2' : |max 0 ((T-x)/‖δ‖) - max 0 ((T-y)/‖δ‖)| ≤ |(T-x)/‖δ‖ - (T-y)/‖δ‖| :=
    h2.trans (le_of_eq (max_eq_right (abs_nonneg _)))
  have h1' : |min 1 (max 0 ((T-x)/‖δ‖)) - min 1 (max 0 ((T-y)/‖δ‖))|
      ≤ |(T-x)/‖δ‖ - (T-y)/‖δ‖| :=
    (h1.trans (le_of_eq (max_eq_right (abs_nonneg _)))).trans h2'
  exact h1'.trans (hbase x y)

lemma lipschitzWith_abs_sub_div {t₀ lam : ℝ} (hlam : 0 < lam) :
    LipschitzWith ⟨lam⁻¹, inv_nonneg.mpr hlam.le⟩ (fun s : ℝ => |s - t₀| / lam) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hkey : |x - t₀| / lam - |y - t₀| / lam = (|x - t₀| - |y - t₀|) / lam := by ring
  rw [Real.dist_eq, Real.dist_eq, hkey, abs_div, abs_of_pos hlam]
  have h3 : abs (abs (x - t₀) - abs (y - t₀)) ≤ abs (x - y) := by
    have h := abs_abs_sub_abs_le_abs_sub (x - t₀) (y - t₀)
    rwa [sub_sub_sub_cancel_right] at h
  show abs (abs (x - t₀) - abs (y - t₀)) / lam ≤ lam⁻¹ * abs (x - y)
  calc abs (abs (x - t₀) - abs (y - t₀)) / lam ≤ abs (x - y) / lam :=
        div_le_div_of_nonneg_right h3 hlam.le
    _ = lam⁻¹ * abs (x - y) := by rw [div_eq_mul_inv, mul_comm]

variable {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N}

/-- The **symmetric bump**: the standard variation, evaluated at `|s - t₀| / λ` and scaled by
`λ^{2/3}`, so that it is applied identically on both sides of the collision time `t₀`. -/
noncomputable def bumpPert (δ : E) (T lam t₀ : ℝ) (u₀ : EN E N) : ℝ → EN E N :=
  fun s => stdCoef δ T (|s - t₀| / lam) • (lam ^ ((2:ℝ)/3) • u₀)

/-- The symmetric bump is Lipschitz. -/
lemma lipschitzWith_bumpPert {δ : E} (hδ : δ ≠ 0) {lam T t₀ : ℝ} (hlam : 0 < lam)
    (u₀ : EN E N) :
    LipschitzWith (⟨‖lam ^ ((2:ℝ)/3) • u₀‖, norm_nonneg _⟩
        * (⟨(‖δ‖)⁻¹, inv_nonneg.mpr (norm_nonneg δ)⟩
          * ⟨lam⁻¹, inv_nonneg.mpr hlam.le⟩)) (bumpPert δ T lam t₀ u₀) := by
  have h1 : LipschitzWith ⟨(‖δ‖)⁻¹, inv_nonneg.mpr (norm_nonneg δ)⟩ (stdCoef δ T) :=
    lipschitzWith_stdCoef hδ T
  have h2 : LipschitzWith ⟨lam⁻¹, inv_nonneg.mpr hlam.le⟩ (fun s : ℝ => |s - t₀| / lam) :=
    lipschitzWith_abs_sub_div hlam
  have h4 : LipschitzWith ⟨‖lam ^ ((2:ℝ)/3) • u₀‖, norm_nonneg _⟩
      (fun c : ℝ => c • (lam ^ ((2:ℝ)/3) • u₀)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, mul_comm]
    rfl
  exact h4.comp (h1.comp h2)

/-- The symmetric bump vanishes outside the window `|s - t₀| ≤ λT`. -/
lemma bumpPert_eq_zero_of_le {δ : E} (hδ : δ ≠ 0) {lam T t₀ : ℝ} (hlam : 0 < lam)
    (u₀ : EN E N) {s : ℝ} (h : lam * T ≤ |s - t₀|) : bumpPert δ T lam t₀ u₀ s = 0 := by
  have h1 : T ≤ |s - t₀| / lam := by
    rw [le_div_iff₀ hlam, mul_comm T lam]
    exact h
  rw [bumpPert, stdCoef_of_ge hδ h1, zero_smul]

/-- **The competitor of the symmetric-bump argument.**  It equals `γ` outside the window
`|s - t₀| ≤ λT`, and `γ + λ^{2/3}·stdPertVec m k i₀ δ` at `s = t₀`. -/
noncomputable def bumpCurve (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (δ : E)
    (T lam t₀ : ℝ) (γ : ℝ → EN E N) : ℝ → EN E N :=
  fun s => γ s + bumpPert δ T lam t₀ (stdPertVec m k i₀ δ) s

lemma bumpCurve_eq_of_le {δ : E} (hδ : δ ≠ 0) {lam T t₀ : ℝ} (hlam : 0 < lam)
    {γ : ℝ → EN E N} {s : ℝ} (h : lam * T ≤ |s - t₀|) :
    bumpCurve m k i₀ δ T lam t₀ γ s = γ s := by
  rw [bumpCurve, bumpPert_eq_zero_of_le hδ hlam _ h, add_zero]

/-- **The bump competitor is absolutely continuous**, whenever `γ` is. -/
theorem absolutelyContinuousOnInterval_bumpCurve {δ : E} (hδ : δ ≠ 0) {lam T t₀ : ℝ}
    (hlam : 0 < lam) {γ : ℝ → EN E N} {a b : ℝ}
    (hac : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (bumpCurve m k i₀ δ T lam t₀ γ) a b := by
  have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_add_lipschitzWith
    (f := γ) (g := bumpPert δ T lam t₀ (stdPertVec m k i₀ δ)) (a := a) (b := b) hac
    (lipschitzWith_bumpPert (δ := δ) hδ hlam (stdPertVec m k i₀ δ))
  rw [show (fun t : ℝ => γ t + bumpPert δ T lam t₀ (stdPertVec m k i₀ δ) t)
      = bumpCurve m k i₀ δ T lam t₀ γ from rfl] at h
  exact h

/-- **The abstract contradiction.**  If an absolutely continuous curve `η` with the same endpoints
as `γ` has strictly smaller action, then `γ` is not an `h`-minimiser. -/
theorem not_isHMinimizer_of_action_lt {m : Fin N → ℝ} {h : ℝ} {γ η : ℝ → EN E N} {a b : ℝ}
    (hab : a < b) (hac : AbsolutelyContinuousOnInterval η a b)
    (h0 : η a = γ a) (h1 : η b = γ b)
    (hlt : actionOn m h η a b < actionOn m h γ a b)
    (hmin : IsHMinimizer m h γ a b) : False := by
  have hle : actionPot m h (γ a) (γ b) ≤ actionOn m h η a b :=
    actionPot_le_of_interval hab h0 h1 hac
  have hmin' : actionOn m h γ a b = actionPot m h (γ a) (γ b) := hmin
  rw [hmin'] at hlt
  exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)

end Submission.NBody
