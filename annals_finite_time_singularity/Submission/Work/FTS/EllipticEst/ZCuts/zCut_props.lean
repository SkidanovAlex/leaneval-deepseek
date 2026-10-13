/-
Copyright: work module for the Elgindi finite-time singularity project.

# Properties of the logarithmic cutoff `ψ_k(z) = φ(log z / log k)`

This module proves `Work.FTS.EllipticEst.ZCuts.zCut_props`, the collection of elementary
properties of the logarithmic cutoff `psiFun φ k z = φ (log z / log k)`
(`Submission/Work/FTS/EllipticEst/zHardyCutDefs.lean`) that the weighted Hardy inequality
`zHardy_sq_le` and the elliptic estimates need:

* `ψ_k` is `C^∞` on `(0,∞)` (composition of the `C^∞` bump with a smooth function);
* `ψ_k = 1` on `[1/k, k]` and `ψ_k = 0` on `(0, 1/k²] ∪ [k², ∞)`;
* `0 ≤ ψ_k ≤ 1` everywhere (`φ` takes values in `[0,1]` everywhere, not only on the
  cutoff region);
* `|z ψ_k'(z)| ≤ K / log k` on `(0,∞)`: the commutator of `ψ_k` with the vector field
  `z ∂_z` is of size `1 / log k`, which is what makes the logarithmic localisation cheap.

All the analytic content is the chain rule for `ψ_k = φ ∘ (log z / log k)` together with
the elementary inequalities for `Real.log` on the three regions defining `IsZCut`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.zHardyCutDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.ZCuts

/-- For `k ≥ 2` the real number `k` is `> 1` (so that `log k > 0`). -/
lemma one_lt_natCast_of_two_le {k : ℕ} (hk : 2 ≤ k) : (1 : ℝ) < (k : ℝ) := by
  exact_mod_cast (by omega : 1 < k)

/-- `y ↦ log y / log k` is `C^∞` on `(0,∞)` for `k ≥ 2`. -/
lemma contDiffOn_log_div {k : ℕ} (hk : 2 ≤ k) :
    ContDiffOn ℝ smoothOrder (fun y : ℝ => Real.log y / Real.log (k : ℝ)) (Set.Ioi 0) := by
  apply ContDiffOn.div
  · exact Real.contDiffOn_log.mono (fun x hx => hx.ne')
  · exact contDiffOn_const
  · intro y hy
    exact ne_of_gt (Real.log_pos (one_lt_natCast_of_two_le hk))

/-- `ψ_k = φ(log z / log k)` is `C^∞` on `(0,∞)`. -/
lemma psiFun_contDiffOn {φ : ℝ → ℝ} {k : ℕ} (hφ : ContDiff ℝ smoothOrder φ) (hk : 2 ≤ k) :
    ContDiffOn ℝ smoothOrder (Work.FTS.EllipticEst.psiFun φ k) (Set.Ioi 0) :=
  hφ.comp_contDiffOn (contDiffOn_log_div hk)

/-- For `k ≥ 2` and `0 < z ≤ 1/k²`, `log z / log k ≤ -2`. -/
lemma log_div_le_neg_two {k : ℕ} (hk : 2 ≤ k) {z : ℝ} (hz : 0 < z)
    (h : z ≤ 1 / (k : ℝ) ^ 2) : Real.log z / Real.log (k : ℝ) ≤ -2 := by
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (one_lt_natCast_of_two_le hk)
  have h1 : Real.log z ≤ Real.log (1 / (k : ℝ) ^ 2) := Real.log_le_log hz h
  have h2 : Real.log (1 / (k : ℝ) ^ 2) = -(2 * Real.log (k : ℝ)) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  rw [div_le_iff₀ hlogk]
  linarith [h1, h2.le]

/-- For `k ≥ 2` and `k² ≤ z`, `2 ≤ log z / log k`. -/
lemma two_le_log_div {k : ℕ} (hk : 2 ≤ k) {z : ℝ} (h : (k : ℝ) ^ 2 ≤ z) :
    (2 : ℝ) ≤ Real.log z / Real.log (k : ℝ) := by
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (one_lt_natCast_of_two_le hk)
  have h1 : Real.log ((k : ℝ) ^ 2) ≤ Real.log z :=
    Real.log_le_log (by positivity) h
  have h2 : Real.log ((k : ℝ) ^ 2) = 2 * Real.log (k : ℝ) := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [le_div_iff₀ hlogk]
  linarith [h1, h2.le]

/-- For `k ≥ 2` and `1/k ≤ z ≤ k`, `|log z / log k| ≤ 1`. -/
lemma abs_log_div_le_one {k : ℕ} (hk : 2 ≤ k) {z : ℝ} (hz : 0 < z)
    (h1 : 1 / (k : ℝ) ≤ z) (h2 : z ≤ (k : ℝ)) :
    |Real.log z / Real.log (k : ℝ)| ≤ 1 := by
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (one_lt_natCast_of_two_le hk)
  have h3 : Real.log (1 / (k : ℝ)) ≤ Real.log z :=
    Real.log_le_log (by positivity) h1
  have h4 : Real.log (1 / (k : ℝ)) = -Real.log (k : ℝ) := by
    rw [one_div, Real.log_inv]
  have h5 : Real.log z ≤ Real.log (k : ℝ) := Real.log_le_log hz h2
  refine abs_le.mpr ⟨?_, ?_⟩
  · rw [le_div_iff₀ hlogk]
    linarith [h3, h4.le]
  · rw [div_le_iff₀ hlogk]
    linarith

/-- On `(0,1/k²] ∪ [k²,∞)` the cutoff vanishes: there `|log z / log k| ≥ 2`. -/
lemma psiFun_eq_zero {φ : ℝ → ℝ} {k : ℕ} (hφ0 : ∀ t, 2 ≤ |t| → φ t = 0) (hk : 2 ≤ k)
    {z : ℝ} (hz : 0 < z) (h : z ≤ 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 ≤ z) :
    Work.FTS.EllipticEst.psiFun φ k z = 0 := by
  have key : 2 ≤ |Real.log z / Real.log (k : ℝ)| := by
    rcases h with h | h
    · have hq := log_div_le_neg_two hk hz h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hq := two_le_log_div hk h
      rw [abs_of_nonneg (by linarith)]
      linarith
  simp only [Work.FTS.EllipticEst.psiFun]
  exact hφ0 _ key

/-- On `[1/k, k]` the cutoff equals `1`: there `|log z / log k| ≤ 1`. -/
lemma psiFun_eq_one {φ : ℝ → ℝ} {k : ℕ} (hφ1 : ∀ t, |t| ≤ 1 → φ t = 1) (hk : 2 ≤ k)
    {z : ℝ} (hz : 0 < z) (h1 : 1 / (k : ℝ) ≤ z) (h2 : z ≤ (k : ℝ)) :
    Work.FTS.EllipticEst.psiFun φ k z = 1 := by
  simp only [Work.FTS.EllipticEst.psiFun]
  exact hφ1 _ (abs_log_div_le_one hk hz h1 h2)

/-- `ψ_k` takes values in `[0,1]` everywhere. -/
lemma psiFun_mem_Icc {φ : ℝ → ℝ} {k : ℕ} (hbdd : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (z : ℝ) :
    0 ≤ Work.FTS.EllipticEst.psiFun φ k z ∧ Work.FTS.EllipticEst.psiFun φ k z ≤ 1 := by
  simp only [Work.FTS.EllipticEst.psiFun]
  exact hbdd _

/-- The commutator bound `|z ψ_k'(z)| ≤ K / log k`: differentiating the composition
`ψ_k = φ ∘ (log z / log k)` gives `z ψ_k'(z) = φ'(log z / log k) / log k`, and
`|φ'| ≤ K`. -/
lemma abs_mul_deriv_psiFun_le {φ : ℝ → ℝ} {K : ℝ} {k : ℕ} (hφcd : ContDiff ℝ smoothOrder φ)
    (hφd : ∀ t, |deriv φ t| ≤ K) (hk : 2 ≤ k) {z : ℝ} (hz : 0 < z) :
    |z * deriv (Work.FTS.EllipticEst.psiFun φ k) z| ≤ K / Real.log (k : ℝ) := by
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (one_lt_natCast_of_two_le hk)
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hφdiff : DifferentiableAt ℝ φ (Real.log z / Real.log (k : ℝ)) :=
    (hφcd.differentiable (by simp)).differentiableAt
  -- the chain rule for `ψ_k = φ ∘ (log · / log k)`
  have hderiv : deriv (Work.FTS.EllipticEst.psiFun φ k) z
      = deriv φ (Real.log z / Real.log (k : ℝ)) * (z⁻¹ / Real.log (k : ℝ)) := by
    have h2 : HasDerivAt (fun y : ℝ => Real.log y / Real.log (k : ℝ))
        (z⁻¹ / Real.log (k : ℝ)) z := (Real.hasDerivAt_log hz0).div_const _
    have h1 : HasDerivAt φ (deriv φ (Real.log z / Real.log (k : ℝ)))
        (Real.log z / Real.log (k : ℝ)) := hφdiff.hasDerivAt
    have hcomp : HasDerivAt (fun y : ℝ => φ (Real.log y / Real.log (k : ℝ)))
        (deriv φ (Real.log z / Real.log (k : ℝ)) * (z⁻¹ / Real.log (k : ℝ))) z :=
      h1.comp z h2
    change deriv (fun y : ℝ => φ (Real.log y / Real.log (k : ℝ))) z = _
    exact hcomp.deriv
  have hzψ : z * deriv (Work.FTS.EllipticEst.psiFun φ k) z
      = deriv φ (Real.log z / Real.log (k : ℝ)) / Real.log (k : ℝ) := by
    rw [hderiv]
    field_simp
  calc |z * deriv (Work.FTS.EllipticEst.psiFun φ k) z|
      = |deriv φ (Real.log z / Real.log (k : ℝ))| / Real.log (k : ℝ) := by
        rw [hzψ, abs_div, abs_of_pos hlogk]
    _ ≤ K / Real.log (k : ℝ) := div_le_div_of_nonneg_right (hφd _) hlogk.le

theorem zCut_props {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) (k : ℕ) (hk : 2 ≤ k) :
    ContDiffOn ℝ smoothOrder (Work.FTS.EllipticEst.psiFun φ k) (Set.Ioi 0) ∧
      (∀ z, 0 < z → z ≤ 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 ≤ z →
        Work.FTS.EllipticEst.psiFun φ k z = 0) ∧
      (∀ z, 0 < z → 1 / (k : ℝ) ≤ z → z ≤ (k : ℝ) →
        Work.FTS.EllipticEst.psiFun φ k z = 1) ∧
      (∀ z, 0 ≤ Work.FTS.EllipticEst.psiFun φ k z ∧
        Work.FTS.EllipticEst.psiFun φ k z ≤ 1) ∧
      (∀ z, 0 < z →
        |z * deriv (Work.FTS.EllipticEst.psiFun φ k) z| ≤ K / Real.log (k : ℝ)) := by
  obtain ⟨hcd, hone, hzero, hbdd, _, hder⟩ := hφ
  exact ⟨psiFun_contDiffOn hcd hk,
    fun z hz h => psiFun_eq_zero hzero hk hz h,
    fun z hz h1 h2 => psiFun_eq_one hone hk hz h1 h2,
    fun z => psiFun_mem_Icc hbdd z,
    fun z hz => abs_mul_deriv_psiFun_le hcd hder hk hz⟩

end Work.FTS.EllipticEst.ZCuts
