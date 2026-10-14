import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.Cutoff
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.EllipticEst.Core.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Vocabulary for the mixed-derivative interpolation `interpMixedGen`

This module collects the small definitional layer shared by the analytic pieces of the
`alphaDz_pth_core_le` estimate:

* `MixInt`, `DDInt`, `TTInt`, `DInt` — the four weighted functionals
  `∫∫ (D_z∂_θu)² w² σ_η`, `∫∫ (D_z²u)² w² σ_η`, `∫∫ (∂_θ²u)² w² σ_η`, `∫∫ (D_zu)² w² σ_η`
  (written as iterated integrals, `θ` first, against `w z ^ 2 * thEta θ`);
* `SliceHonest u z` — the four corresponding `θ`-slice integrals at `z` are finite;
* `RHSInt u` — the three *right-hand side* functionals are integrable in `z`.

There are no `sorry`s here; the analytic statements live in the sibling modules.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

/-- The `θ`-slice integrand of `MixInt`. -/
def mixIntS (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)

/-- The `θ`-slice integrand of `∫∫ (D_z² u)² w² σ_η`. -/
def ddIntS (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.Dz u) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)

/-- The `θ`-slice integrand of `∫∫ (∂_θ² u)² w² σ_η`. -/
def ttIntS (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pth (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)

/-- The `θ`-slice integrand of `∫∫ (D_z u)² w² σ_η`. -/
def dIntS (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)


/-- The `θ`-slice integrand of the `D_θ`-summand `(D_z^{j+1}D_θ^i∂_θu)² w² σ_γ`, `i ≥ 1`. -/
def mixedIntS (α : ℝ) (i j : ℕ) (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth u) z θ) ^ 2
      * Work.FTS.EllipticEst.thGam α θ)



end Work.EllipticEst.Core
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.zLogCut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `zLogCut` — the two-sided logarithmic cut-off family in the radial variable `z`

We build, on `(0,∞)`, a family `χ k` (`k : ℕ`) of smooth cut-offs which are `0` outside the
multiplicative window `(1/((k:ℝ)+1)², ((k:ℝ)+1)²)`, increase pointwise in `k` to the constant
`1`, and whose logarithmic derivatives are bounded by `K / log ((k:ℝ)+2)`:

* the first order (`z χ'_k`), and
* the second order (`z (z χ'_k)'`).

The witness is the explicit smooth bump of `Work.ChiExplicit`,
`chi t = Real.smoothTransition (2 - ‖t‖)` (`= 1` for `|t| ≤ 1`, `= 0` for `|t| ≥ 2`,
`0 ≤ chi ≤ 1`, antitone on `[0,∞)`), composed with the *logarithmic* rescaling
`z ↦ log z / log ((k:ℝ)+1)`:

  `zLogChi k z = chi (log z / log ((k:ℝ)+1))`  for `k ≥ 1`,  and `zLogChi 0 = 0`.

(The index `k = 0` is degenerate: the window is the single point `{1}`, so `χ 0` must vanish
everywhere on `(0,∞)`.)
-/

namespace Work.EllipticEst.Core

open scoped Real Topology
open Set Filter

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Boundedness of the derivatives of the explicit bump `chi` -/

/-- A continuous function vanishing off the compact set `[-2,2]` is bounded in absolute value. -/
lemma exists_max_abs_of_continuous_zero_far (g : ℝ → ℝ) (hg : Continuous g)
    (hzero : ∀ t : ℝ, 2 < |t| → g t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |g t| ≤ C := by
  have hcont : Continuous fun t : ℝ => |g t| := hg.abs
  obtain ⟨x₀, -, hmax⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_isMaxOn
    (⟨(-2 : ℝ), by norm_num⟩ : (Set.Icc (-2 : ℝ) 2).Nonempty)
    (f := fun t : ℝ => |g t|) hcont.continuousOn
  refine ⟨|g x₀|, abs_nonneg _, fun t => ?_⟩
  by_cases ht : |t| ≤ 2
  · exact isMaxOn_iff.mp hmax t (Set.mem_Icc.mpr (abs_le.mp ht))
  · rw [hzero t (lt_of_not_ge ht), abs_zero]
    exact abs_nonneg _

/-- `deriv chi` vanishes strictly outside `[-2,2]` (`chi` is locally `0` there). -/
lemma chi_deriv_eq_zero_far (t : ℝ) (ht : 2 < |t|) : deriv Work.ChiExplicit.chi t = 0 := by
  have hopen : IsOpen {s : ℝ | (2 : ℝ) < |s|} := isOpen_lt continuous_const continuous_abs
  have hev : Work.ChiExplicit.chi =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact Work.ChiExplicit.chi_eq_zero hs.le
  rw [hev.deriv_eq, deriv_const]

/-- `deriv (deriv chi)` vanishes strictly outside `[-2,2]`. -/
lemma chi_deriv2_eq_zero_far (t : ℝ) (ht : 2 < |t|) :
    deriv (fun x : ℝ => deriv Work.ChiExplicit.chi x) t = 0 := by
  have hopen : IsOpen {s : ℝ | (2 : ℝ) < |s|} := isOpen_lt continuous_const continuous_abs
  have hev : (fun x : ℝ => deriv Work.ChiExplicit.chi x) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact chi_deriv_eq_zero_far s hs
  rw [hev.deriv_eq, deriv_const]

/-- **Both the first and the second derivative of the bump `chi` are globally bounded.** -/
lemma chi_deriv_bounds : ∃ C : ℝ, 0 ≤ C ∧
    (∀ t : ℝ, |deriv Work.ChiExplicit.chi t| ≤ C) ∧
    (∀ t : ℝ, |deriv (fun x : ℝ => deriv Work.ChiExplicit.chi x) t| ≤ C) := by
  have hcd : ContDiff ℝ Work.Stability.smoothOrder Work.ChiExplicit.chi :=
    Work.ChiExplicit.chi_contDiff (⊤ : ℕ∞)
  have hcont1 : Continuous (fun t : ℝ => deriv Work.ChiExplicit.chi t) :=
    hcd.continuous_deriv (by simp [Work.Stability.smoothOrder])
  have hcont2 :
      Continuous (fun t : ℝ => deriv (fun x : ℝ => deriv Work.ChiExplicit.chi x) t) := by
    have h2 : ContDiff ℝ Work.Stability.smoothOrder (deriv^[2] Work.ChiExplicit.chi) :=
      ContDiff.iterate_deriv 2 hcd
    simpa [Function.iterate_succ, Function.iterate_zero, Function.comp_def] using h2.continuous
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_max_abs_of_continuous_zero_far _ hcont1 chi_deriv_eq_zero_far
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_max_abs_of_continuous_zero_far _ hcont2 chi_deriv2_eq_zero_far
  exact ⟨max C₁ C₂, le_trans hC₁0 (le_max_left _ _),
    fun t => (hC₁ t).trans (le_max_left _ _), fun t => (hC₂ t).trans (le_max_right _ _)⟩

/-! ## Smoothness and derivatives of the log-rescaled bump -/

/-- The log-rescaled bump `z ↦ chi (log z / L)` is `C^∞` on `(0,∞)`. -/
lemma contDiffOn_chi_logDiv (L : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.ChiExplicit.chi (Real.log z / L)) (Set.Ioi (0 : ℝ)) := by
  have hlog : ContDiffOn ℝ Work.Stability.smoothOrder Real.log (Set.Ioi (0 : ℝ)) :=
    Real.contDiffOn_log.mono (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx)
  have hg : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Real.log z / L) (Set.Ioi (0 : ℝ)) := hlog.div_const L
  have hchi : ContDiffOn ℝ Work.Stability.smoothOrder Work.ChiExplicit.chi Set.univ :=
    (Work.ChiExplicit.chi_contDiff (⊤ : ℕ∞)).contDiffOn
  exact (hchi.comp hg (fun z _ => Set.mem_univ _)).congr (fun z _ => rfl)

/-! ### Elementary arithmetic of inverses -/

lemma inv_div_eq_one_div_mul (z L : ℝ) : z⁻¹ / L = 1 / (z * L) := by
  rw [one_div, div_eq_mul_inv, mul_inv_rev]
  ring

/-- **The chain rule for the log-rescaled bump**: for `z > 0` and `L ≠ 0`,
`(f (log · / L))'(z) = f'(log z / L) / (z * L)`. -/
lemma deriv_logDiv_gen {f : ℝ → ℝ} (hf : ContDiff ℝ Work.Stability.smoothOrder f)
    {L : ℝ} (hL : L ≠ 0) {z : ℝ} (hz : 0 < z) :
    deriv (fun y : ℝ => f (Real.log y / L)) z = deriv f (Real.log z / L) / (z * L) := by
  have hz' : z ≠ 0 := ne_of_gt hz
  have hg : HasDerivAt (fun y : ℝ => Real.log y / L) (1 / (z * L)) z := by
    have h := (Real.hasDerivAt_log hz').div_const L
    rwa [inv_div_eq_one_div_mul z L] at h
  have hdf : HasDerivAt f (deriv f (Real.log z / L)) (Real.log z / L) :=
    (hf.differentiable (by simp [Work.Stability.smoothOrder])).differentiableAt.hasDerivAt
  have hc : HasDerivAt (fun y : ℝ => f (Real.log y / L))
      (deriv f (Real.log z / L) / (z * L)) z := by
    simpa only [Function.comp_def, div_eq_mul_inv, one_mul] using hdf.comp z hg
  exact hc.deriv

/-- **The chain rule, second order**: for `z > 0` and `L ≠ 0`,
`(z ↦ z · (f (log · / L))'(z))'(z) = f''(log z / L) / (z * L²)`. -/
lemma deriv_mul_deriv_logDiv {f : ℝ → ℝ} (hf : ContDiff ℝ Work.Stability.smoothOrder f)
    {L : ℝ} (hL : L ≠ 0) {z : ℝ} (hz : 0 < z) :
    deriv (fun y : ℝ => y * deriv (fun w : ℝ => f (Real.log w / L)) y) z
      = deriv (deriv f) (Real.log z / L) / (z * L ^ 2) := by
  have hz' : z ≠ 0 := ne_of_gt hz
  -- On `(0,∞)` the derivative of the log-rescaled function is `y ↦ f'(log y / L)/(y L)`.
  have hdg : deriv (fun w : ℝ => f (Real.log w / L))
      =ᶠ[𝓝 z] (fun y : ℝ => deriv f (Real.log y / L) / (y * L)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    have hy' : y ≠ 0 := ne_of_gt hy
    have hgy : HasDerivAt (fun w : ℝ => Real.log w / L) (1 / (y * L)) y := by
      have h := (Real.hasDerivAt_log hy').div_const L
      rwa [inv_div_eq_one_div_mul y L] at h
    have hdfy : HasDerivAt f (deriv f (Real.log y / L)) (Real.log y / L) :=
      (hf.differentiable (by simp [Work.Stability.smoothOrder])).differentiableAt.hasDerivAt
    have hcy : HasDerivAt (fun w : ℝ => f (Real.log w / L))
        (deriv f (Real.log y / L) / (y * L)) y := by
      simpa only [Function.comp_def, div_eq_mul_inv, one_mul] using hdfy.comp y hgy
    exact hcy.deriv
  -- `y ↦ y · (f (log · / L))'(y)` agrees with `y ↦ f'(log y / L)/L` near `z`.
  have hev : (fun y : ℝ => y * deriv (fun w : ℝ => f (Real.log w / L)) y)
      =ᶠ[𝓝 z] (fun y : ℝ => deriv f (Real.log y / L) / L) := by
    filter_upwards [hdg, isOpen_Ioi.mem_nhds hz] with y hy hypos
    have hy' : y ≠ 0 := ne_of_gt hypos
    rw [hy]
    field_simp
    try ring
  -- Derivative of `y ↦ f'(log y / L) / L` at `z`.
  have hg : HasDerivAt (fun y : ℝ => Real.log y / L) (1 / (z * L)) z := by
    have h := (Real.hasDerivAt_log hz').div_const L
    rwa [inv_div_eq_one_div_mul z L] at h
  have hd2 : HasDerivAt (deriv f) (deriv (deriv f) (Real.log z / L)) (Real.log z / L) :=
    ((ContDiff.iterate_deriv 1 hf).differentiable
      (by simp [Work.Stability.smoothOrder])).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun y : ℝ => deriv f (Real.log y / L) / L)
      (deriv (deriv f) (Real.log z / L) / (z * L) / L) z := by
    simpa only [Function.comp_def, div_eq_mul_inv, one_mul] using (hd2.comp z hg).div_const L
  rw [hev.deriv_eq, hcomp.deriv]
  field_simp
  try ring

/-! ## The elementary properties of `chi (log z / log ((k:ℝ)+1))` -/

/-- **Vanishing outside the window**: for `k ≥ 1`, the log-rescaled bump vanishes for
`z ≤ 1/((k:ℝ)+1)²` and for `z ≥ ((k:ℝ)+1)²`. -/
lemma chi_logDiv_zero {k : ℕ} (hk : 1 ≤ k) {z : ℝ} (hz : 0 < z)
    (h : z ≤ 1 / ((k : ℝ) + 1) ^ 2 ∨ ((k : ℝ) + 1) ^ 2 ≤ z) :
    Work.ChiExplicit.chi (Real.log z / Real.log ((k : ℝ) + 1)) = 0 := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1k : (1 : ℝ) < (k : ℝ) + 1 := by linarith
  have hlog : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos h1k
  have hc : 0 < (k : ℝ) + 1 := by linarith
  refine Work.ChiExplicit.chi_eq_zero ?_
  rcases h with h | h
  · have hlog_le : Real.log z ≤ Real.log (1 / ((k : ℝ) + 1) ^ 2) := Real.log_le_log hz h
    have hval : Real.log (1 / ((k : ℝ) + 1) ^ 2) = -(2 * Real.log ((k : ℝ) + 1)) := by
      rw [one_div, Real.log_inv, Real.log_pow]
      push_cast
      ring
    have ht : Real.log z / Real.log ((k : ℝ) + 1) ≤ -2 := by
      rw [div_le_iff₀ hlog]
      linarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hlog_le : Real.log (((k : ℝ) + 1) ^ 2) ≤ Real.log z :=
      Real.log_le_log (pow_pos hc 2) h
    have hval : Real.log (((k : ℝ) + 1) ^ 2) = 2 * Real.log ((k : ℝ) + 1) := by
      rw [Real.log_pow]
      push_cast
      ring
    have ht : (2 : ℝ) ≤ Real.log z / Real.log ((k : ℝ) + 1) := by
      rw [le_div_iff₀ hlog]
      linarith
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- **Monotonicity of the log-rescaled bump in the rescaling parameter.** -/
lemma chi_logDiv_mono {L₁ L₂ : ℝ} (h1 : 0 < L₁) (h12 : L₁ ≤ L₂) (z : ℝ) :
    Work.ChiExplicit.chi (Real.log z / L₁) ≤ Work.ChiExplicit.chi (Real.log z / L₂) := by
  have h2 : 0 < L₂ := lt_of_lt_of_le h1 h12
  have e1 : |Real.log z / L₁| = |Real.log z| / L₁ := by rw [abs_div, abs_of_pos h1]
  have e2 : |Real.log z / L₂| = |Real.log z| / L₂ := by rw [abs_div, abs_of_pos h2]
  have hchiabs : ∀ t : ℝ, Work.ChiExplicit.chi t = Work.ChiExplicit.chi |t| := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg ht, Work.ChiExplicit.chi_neg t]
  have hden : |Real.log z| / L₂ ≤ |Real.log z| / L₁ :=
    div_le_div_of_nonneg_left (abs_nonneg _) h1 h12
  have hL : Work.ChiExplicit.chi (Real.log z / L₁)
      = Work.ChiExplicit.chi (|Real.log z| / L₁) := by
    rw [hchiabs (Real.log z / L₁), e1]
  have hR : Work.ChiExplicit.chi (Real.log z / L₂)
      = Work.ChiExplicit.chi (|Real.log z| / L₂) := by
    rw [hchiabs (Real.log z / L₂), e2]
  rw [hL, hR]
  exact Work.ChiExplicit.chi_antitoneOn (div_nonneg (abs_nonneg _) h2.le)
    (div_nonneg (abs_nonneg _) h1.le) hden

/-- **The family tends to `1` pointwise**: for every fixed `z > 0` and every `ε > 0` there is
`N` with `1 - chi (log z / log ((k:ℝ)+1)) < ε` for all `k ≥ N`. -/
lemma chi_logDiv_small {z : ℝ} (hz : 0 < z) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      1 - Work.ChiExplicit.chi (Real.log z / Real.log ((k : ℝ) + 1)) < ε := by
  intro ε hε
  set A : ℝ := |Real.log z| with hA
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp A)
  refine ⟨max N 1, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hkN : N ≤ k := le_trans (le_max_left _ _) hk
  have hkR : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkN
  have hexp : Real.exp A ≤ (k : ℝ) + 1 := by
    have := Real.exp_pos A
    linarith
  have hlog_ge : A ≤ Real.log ((k : ℝ) + 1) := by
    have h := Real.log_le_log (Real.exp_pos A) hexp
    rwa [Real.log_exp] at h
  have hkpos : (1 : ℝ) < (k : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hlog_pos : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos hkpos
  have habs : |Real.log z / Real.log ((k : ℝ) + 1)| ≤ 1 := by
    rw [abs_div, abs_of_pos hlog_pos, div_le_iff₀ hlog_pos, ← hA]
    simpa using hlog_ge
  have hchi1 : Work.ChiExplicit.chi (Real.log z / Real.log ((k : ℝ) + 1)) = 1 :=
    Work.ChiExplicit.chi_eq_one habs
  rw [hchi1]
  linarith

/-! ## Elementary logarithms and numerical comparisons -/

/-- `log ((k:ℝ)+2) ≤ 2 log ((k:ℝ)+1)` for `k ≥ 1`, i.e. `k + 2 ≤ (k+1)²`. -/
lemma log_add_two_le (k : ℕ) (hk : 1 ≤ k) :
    Real.log ((k : ℝ) + 2) ≤ 2 * Real.log ((k : ℝ) + 1) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsq : (k : ℝ) + 2 ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
  calc Real.log ((k : ℝ) + 2) ≤ Real.log (((k : ℝ) + 1) ^ 2) :=
        Real.log_le_log (by linarith) hsq
    _ = 2 * Real.log ((k : ℝ) + 1) := by rw [Real.log_pow]; norm_num

/-- The numerical comparison `A / L ≤ K / M` when `M ≤ 2L` and `2A ≤ K`. -/
lemma div_le_div_log_of_le (A K : ℝ) {L M : ℝ} (hA : 0 ≤ A) (hL : 0 < L) (hM : 0 < M)
    (hML : M ≤ 2 * L) (hK : 2 * A ≤ K) : A / L ≤ K / M := by
  rw [div_le_div_iff₀ hL hM]
  nlinarith

/-- The numerical comparison `A / L² ≤ K / M` when `M ≤ 2L`, `log 2 ≤ L` and
`2 (A / log 2) ≤ K`. -/
lemma div_sq_le_div_log_of_le (A K : ℝ) {L M : ℝ} (hA : 0 ≤ A) (hL : 0 < L) (hM : 0 < M)
    (hML : M ≤ 2 * L) (hLge : Real.log 2 ≤ L) (hK : 2 * (A / Real.log 2) ≤ K) :
    A / L ^ 2 ≤ K / M := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA' : 0 ≤ A / Real.log 2 := div_nonneg hA hlog2.le
  have h1 : A / L ^ 2 ≤ (A / Real.log 2) / L := by
    rw [show (A / Real.log 2) / L = A / (Real.log 2 * L) by field_simp]
    exact div_le_div_of_nonneg_left hA (by positivity) (by nlinarith)
  refine h1.trans ?_
  rw [div_le_div_iff₀ hL hM]
  nlinarith

/-! ## The cut-off family -/

/-- **THE LOGARITHMIC CUT-OFF FAMILY** in the radial variable: for `k ≥ 1`,
`zLogChi k z = chi (log z / log ((k:ℝ)+1))`, and `zLogChi 0 = 0`. -/
noncomputable def zLogChi (k : ℕ) : ℝ → ℝ :=
  fun z => if k = 0 then 0 else Work.ChiExplicit.chi (Real.log z / Real.log ((k : ℝ) + 1))

lemma zLogChi_zero : zLogChi 0 = fun _ : ℝ => (0 : ℝ) := by
  funext z
  simp [zLogChi]

lemma zLogChi_formula {k : ℕ} (hk : k ≠ 0) :
    zLogChi k = fun z : ℝ => Work.ChiExplicit.chi (Real.log z / Real.log ((k : ℝ) + 1)) := by
  funext z
  simp [zLogChi, hk]

theorem zLogCut : ∃ (χ : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K ∧
    (∀ k : ℕ, ContDiffOn ℝ Work.Stability.smoothOrder (χ k) (Set.Ioi (0 : ℝ))) ∧
    (∀ k : ℕ, ∀ z : ℝ, 0 < z → 0 ≤ χ k z ∧ χ k z ≤ 1) ∧
    (∀ k : ℕ, ∀ z : ℝ, 0 < z →
      (z ≤ 1 / ((k : ℝ) + 1) ^ 2 ∨ ((k : ℝ) + 1) ^ 2 ≤ z) → χ k z = 0) ∧
    (∀ k : ℕ, ∀ z : ℝ, 0 < z → χ k z ≤ χ (k + 1) z) ∧
    (∀ z : ℝ, 0 < z → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → 1 - χ k z < ε) ∧
    (∀ k : ℕ, ∀ z : ℝ, 0 < z → |z * deriv (χ k) z| ≤ K / Real.log ((k : ℝ) + 2)) ∧
    (∀ k : ℕ, ∀ z : ℝ, 0 < z →
      |z * deriv (fun y : ℝ => y * deriv (χ k) y) z| ≤ K / Real.log ((k : ℝ) + 2)) := by
  obtain ⟨C, hC0, hC1, hC2⟩ := chi_deriv_bounds
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hClog2 : 0 ≤ C / Real.log 2 := div_nonneg hC0 hlog2.le
  have hK0 : 0 ≤ 2 * C + 2 * (C / Real.log 2) + 1 := by linarith
  have hlog0 : 0 ≤ Real.log (((0 : ℕ) : ℝ) + 2) := by
    have h : (((0 : ℕ) : ℝ) + 2) = 2 := by norm_num
    rw [h]
    exact hlog2.le
  refine ⟨zLogChi, 2 * C + 2 * (C / Real.log 2) + 1, hK0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness on `(0,∞)`
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [zLogChi_zero]
      exact contDiffOn_const
    · rw [zLogChi_formula hk]
      exact contDiffOn_chi_logDiv _
  · -- values in `[0,1]`
    intro k z hz
    by_cases hk : k = 0
    · subst hk
      rw [zLogChi_zero]
      norm_num
    · rw [zLogChi_formula hk]
      exact ⟨Work.ChiExplicit.chi_nonneg _, Work.ChiExplicit.chi_le_one _⟩
  · -- vanishing outside the window
    intro k z hz h
    by_cases hk : k = 0
    · subst hk
      rw [zLogChi_zero]
    · rw [zLogChi_formula hk]
      exact chi_logDiv_zero (Nat.one_le_iff_ne_zero.mpr hk) hz h
  · -- monotone in `k`
    intro k z hz
    by_cases hk : k = 0
    · subst hk
      rw [zLogChi_zero, zLogChi_formula (by norm_num : (1 : ℕ) ≠ 0)]
      exact Work.ChiExplicit.chi_nonneg _
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have h1 : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos (by linarith)
      have h12 : Real.log ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [zLogChi_formula hk, zLogChi_formula (by omega : (k + 1 : ℕ) ≠ 0)]
      have hcast : (((k + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      exact chi_logDiv_mono h1 h12 z
  · -- convergence to `1`
    intro z hz ε hε
    obtain ⟨N, hN⟩ := chi_logDiv_small hz ε hε
    refine ⟨max N 1, fun k hk => ?_⟩
    have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
    have hkN : N ≤ k := le_trans (le_max_left _ _) hk
    have hk0 : k ≠ 0 := by omega
    rw [zLogChi_formula hk0]
    exact hN k hkN
  · -- first order logarithmic derivative bound
    intro k z hz
    by_cases hk : k = 0
    · subst hk
      rw [zLogChi_zero, deriv_const, mul_zero, abs_zero]
      exact div_nonneg hK0 hlog0
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have hL : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos (by linarith)
      have hLne : Real.log ((k : ℝ) + 1) ≠ 0 := ne_of_gt hL
      have hz' : z ≠ 0 := ne_of_gt hz
      rw [zLogChi_formula hk]
      rw [deriv_logDiv_gen (Work.ChiExplicit.chi_contDiff (⊤ : ℕ∞)) hLne hz]
      have harith : z * (deriv Work.ChiExplicit.chi (Real.log z / Real.log ((k : ℝ) + 1))
          / (z * Real.log ((k : ℝ) + 1)))
          = deriv Work.ChiExplicit.chi (Real.log z / Real.log ((k : ℝ) + 1))
            / Real.log ((k : ℝ) + 1) := by
        field_simp
        try ring
      rw [harith, abs_div, abs_of_pos hL]
      have hb1 : |deriv Work.ChiExplicit.chi (Real.log z / Real.log ((k : ℝ) + 1))|
            / Real.log ((k : ℝ) + 1) ≤ C / Real.log ((k : ℝ) + 1) :=
        div_le_div_of_nonneg_right (hC1 _) hL.le
      refine hb1.trans ?_
      have hlogk2 : 0 < Real.log ((k : ℝ) + 2) := Real.log_pos (by linarith)
      exact div_le_div_log_of_le C (2 * C + 2 * (C / Real.log 2) + 1) hC0 hL hlogk2
        (log_add_two_le k hk1) (by linarith)
  · -- second order logarithmic derivative bound
    intro k z hz
    by_cases hk : k = 0
    · subst hk
      rw [zLogChi_zero]
      have hfun : (fun y : ℝ => y * deriv (fun _ : ℝ => (0 : ℝ)) y)
          = fun _ : ℝ => (0 : ℝ) := by
        funext y
        rw [deriv_const]
        ring
      rw [hfun, deriv_const, mul_zero, abs_zero]
      exact div_nonneg hK0 hlog0
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have hL : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos (by linarith)
      have hLne : Real.log ((k : ℝ) + 1) ≠ 0 := ne_of_gt hL
      have hz' : z ≠ 0 := ne_of_gt hz
      rw [zLogChi_formula hk]
      rw [deriv_mul_deriv_logDiv (Work.ChiExplicit.chi_contDiff (⊤ : ℕ∞)) hLne hz]
      have hL2 : 0 < (Real.log ((k : ℝ) + 1)) ^ 2 := by positivity
      have harith : z * (deriv (deriv Work.ChiExplicit.chi)
            (Real.log z / Real.log ((k : ℝ) + 1))
          / (z * (Real.log ((k : ℝ) + 1)) ^ 2))
          = deriv (deriv Work.ChiExplicit.chi) (Real.log z / Real.log ((k : ℝ) + 1))
            / (Real.log ((k : ℝ) + 1)) ^ 2 := by
        field_simp
        try ring
      rw [harith, abs_div, abs_of_pos hL2]
      have hb1 : |deriv (deriv Work.ChiExplicit.chi) (Real.log z / Real.log ((k : ℝ) + 1))|
            / (Real.log ((k : ℝ) + 1)) ^ 2 ≤ C / (Real.log ((k : ℝ) + 1)) ^ 2 :=
        div_le_div_of_nonneg_right (hC2 _) hL2.le
      refine hb1.trans ?_
      have hlogk2 : 0 < Real.log ((k : ℝ) + 2) := Real.log_pos (by linarith)
      have hLge : Real.log 2 ≤ Real.log ((k : ℝ) + 1) :=
        Real.log_le_log (by norm_num) (by linarith)
      exact div_sq_le_div_log_of_le C (2 * C + 2 * (C / Real.log 2) + 1) hC0 hL hlogk2
        (log_add_two_le k hk1) hLge (by linarith)

end

end Work.EllipticEst.Core
end
-- ===== merged: Submission.Work.FTS.ClassCHon.CmodeDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.ClassCHon

/-- `Lop g k` is the `k`-fold iterate of the angular operator `Lzero1` applied to `g`
(`Lop g 0 = g`, `Lop g (k+1) = Lzero1 (Lop g k)`). -/
noncomputable def Lop (g : ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun k => Nat.rec g (fun _ acc => Work.FTS.EllipticEst.Lzero1 acc) k

@[simp] theorem Lop_zero (g : ℝ → ℝ) : Lop g 0 = g := rfl

@[simp] theorem Lop_succ (g : ℝ → ℝ) (k : ℕ) :
    Lop g (k + 1) = Work.FTS.EllipticEst.Lzero1 (Lop g k) := rfl

/-- A function `g` which is `C^∞` (`∞ = Work.Stability.smoothOrder`, *not* the analytic order
`⊤ = ω`) and vanishes outside the interval `[a,b]`. -/
def Good (a b : ℝ) (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ Work.Stability.smoothOrder g ∧ ∀ θ : ℝ, θ ∉ Set.Icc a b → g θ = 0

theorem Good.contDiff {a b : ℝ} {g : ℝ → ℝ} (h : Good a b g) :
    ContDiff ℝ Work.Stability.smoothOrder g := h.1

theorem Good.eq_zero {a b : ℝ} {g : ℝ → ℝ} (h : Good a b g) :
    ∀ θ : ℝ, θ ∉ Set.Icc a b → g θ = 0 := h.2

end Work.FTS.ClassCHon
end
end
