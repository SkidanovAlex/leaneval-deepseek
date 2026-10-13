/-
Work module for the Elgindi finite-time singularity project.

# The repaired `Work.FTS.EllipticEst.Mine.cutoffFamilyMono`

The requested lemma (`Submission/Work/FTS/EllipticEst/Mine/cutoffFamilyMono.lean`) is **false as
written**, because the smoothness clause is stated in the *analytic* order: in this pinned Mathlib
`ContDiff 𝕜 n f` has `n : ℕ∞ω = WithTop ℕ∞`, `⊤ = ω` is analyticity and `∞ = ((⊤ : ℕ∞) : ℕ∞ω)`
is `C^∞` (`contDiff_omega_iff_analyticOnNhd`).  A family which is `ContDiff ℝ ⊤` and vanishes on
`(-∞,0]` is identically zero, so it can never saturate at `χ N z = 1`.  See
`Submission/Work/FTS/EllipticEst/Mine/Refute/cutoffFamilyMonoFalse.lean` for the formal
refutation (`Work.FTS.EllipticEst.Mine.not_cutoffFamilyMono`).

This file proves the repaired statement `cutoffFamilyMono_smooth`: **`ContDiff ℝ ⊤` replaced by
`ContDiff ℝ ∞`, every other clause verbatim**.

## The witness

With `σ = Real.smoothTransition` (`σ = 0` on `(-∞,0]`, `σ = 1` on `[1,∞)`, `0 ≤ σ ≤ 1`, smooth,
not analytic),

```
χ N z  =  cutA N z * cutB N z,
  cutA N z = σ((N+1)·z - 1)      -- switches ON at  z = 1/(N+1)
  cutB N z = σ(2 - z/(N+1))      -- switches OFF at z = 2(N+1)
```

* smoothness: composition of `σ` with affine maps; `σ` is *not* analytic, which is why the
  family is compactly supported in `z`;
* `0 ≤ χ N ≤ 1`: `0 ≤ σ ≤ 1`;
* `z ≤ 0 ⟹ χ N z = 0`: `(N+1)z - 1 ≤ 0`, so `cutA N z = 0`;
* `z ≤ 1/(N+1) ⟹ χ N z = 0`: same;
* `2(N+1) ≤ z ⟹ χ N z = 0`: `2 - z/(N+1) ≤ 0`, so `cutB N z = 0`;
* monotone in `N` on `z ≥ 0`: both factors are pointwise nondecreasing in `N`
  (`(N+1)z - 1` and `2 - z/(N+1)` are monotone in `N` for `z ≥ 0`);
* saturation: for fixed `z > 0` and `N` large, `(N+1)z - 1 ≥ 1` and `2 - z/(N+1) ≥ 1`, so both
  factors are `1`;
* `|z · χ N z · (χ N)' z| ≤ C · χ N z` for `C = 4M + 1`: differentiating gives
  `z (χ N)' z = [((N+1)z) σ'((N+1)z-1)] cutB N z - [(z/(N+1)) σ'(2 - z/(N+1))] cutA N z`,
  and the profile derivative `σ'` *vanishes off* `[0,1]`, so each bracket is bounded by `2M`
  with `M` a bound for `|σ'|` (each factor of the pair `(t, σ'(t))` lies in `[0,2] × [-M,M]`
  when it is nonzero).  This last clause is *equivalent* to the on-support bound
  `χ N z > 0 → |z (χ N)' z| ≤ C` (on the zero set of `χ N` both sides of the clause vanish,
  and dividing by `χ N z > 0` is legitimate); the witness satisfies the global bound
  `|z (χ N)' z| ≤ 4M` on all of `ℝ`, which is what makes the clause hold with `C = 4M + 1`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.EllipticEst.Mine

/-! ## The witnesses -/

/-- The left shoulder `z ↦ σ((N+1)z - 1)`, switched on at `z = 1/(N+1)`. -/
def cutA (N : ℕ) (z : ℝ) : ℝ := Real.smoothTransition (((N : ℝ) + 1) * z - 1)

/-- The right shoulder `z ↦ σ(2 - z/(N+1))`, switched off at `z = 2(N+1)`. -/
def cutB (N : ℕ) (z : ℝ) : ℝ := Real.smoothTransition (2 - z / ((N : ℝ) + 1))

/-- The repair witness: `χ N z = cutA N z * cutB N z`. -/
def monoCut (N : ℕ) (z : ℝ) : ℝ := cutA N z * cutB N z

/-! ## The profile `σ` and its derivative -/

/-- `σ'` vanishes off `[0,1]`: `σ` is constant `0` left of `0` and constant `1` right of `1`. -/
theorem deriv_smoothTransition_eq_zero_of_not_mem_Icc {t : ℝ} (ht : t ∉ Set.Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition t = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · have hev : Real.smoothTransition =ᶠ[nhds t] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds ht] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [hev.deriv_eq]
    simp
  · have hev : Real.smoothTransition =ᶠ[nhds t] (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds ht] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [hev.deriv_eq]
    simp

/-- **`σ'` is globally bounded** (it is continuous with support in `[0,1]`). -/
theorem exists_bound_deriv_smoothTransition :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 1) (f := deriv Real.smoothTransition) hcont.continuousOn
  refine ⟨max M 0, le_max_right M 0, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · exact le_trans (by simpa [Real.norm_eq_abs] using hM t ht) (le_max_left M 0)
  · rw [deriv_smoothTransition_eq_zero_of_not_mem_Icc ht, abs_zero]
    exact le_max_right M 0

/-- The first bracket: `|u σ'(u-1)| ≤ 2M` (when `σ'(u-1) ≠ 0` one has `u ∈ [1,2]`). -/
theorem abs_mul_deriv_shift_le {M : ℝ} (hM : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M)
    (hM0 : 0 ≤ M) (u : ℝ) : |u * deriv Real.smoothTransition (u - 1)| ≤ 2 * M := by
  by_cases hu : u - 1 ∈ Set.Icc (0 : ℝ) 1
  · have hu2 : |u| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    calc |u * deriv Real.smoothTransition (u - 1)|
        = |u| * |deriv Real.smoothTransition (u - 1)| := abs_mul _ _
      _ ≤ 2 * M := mul_le_mul hu2 (hM _) (abs_nonneg _) (by linarith)
  · rw [deriv_smoothTransition_eq_zero_of_not_mem_Icc hu, mul_zero, abs_zero]
    linarith

/-- The second bracket: `|w σ'(2 - w)| ≤ 2M` (when `σ'(2-w) ≠ 0` one has `w ∈ [1,2]`). -/
theorem abs_mul_deriv_sub_le {M : ℝ} (hM : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M)
    (hM0 : 0 ≤ M) (w : ℝ) : |w * deriv Real.smoothTransition (2 - w)| ≤ 2 * M := by
  by_cases hw : 2 - w ∈ Set.Icc (0 : ℝ) 1
  · have hwpos : 0 < w := by linarith [hw.2]
    have hw2 : |w| ≤ 2 := by
      rw [abs_of_pos hwpos]
      linarith [hw.1]
    calc |w * deriv Real.smoothTransition (2 - w)|
        = |w| * |deriv Real.smoothTransition (2 - w)| := abs_mul _ _
      _ ≤ 2 * M := mul_le_mul hw2 (hM _) (abs_nonneg _) (by linarith)
  · rw [deriv_smoothTransition_eq_zero_of_not_mem_Icc hw, mul_zero, abs_zero]
    linarith

/-! ## The elementary clauses of the family -/

theorem cutA_nonneg (N : ℕ) (z : ℝ) : 0 ≤ cutA N z := Real.smoothTransition.nonneg _

theorem cutA_le_one (N : ℕ) (z : ℝ) : cutA N z ≤ 1 := Real.smoothTransition.le_one _

theorem cutA_abs_le_one (N : ℕ) (z : ℝ) : |cutA N z| ≤ 1 := by
  rw [abs_of_nonneg (cutA_nonneg N z)]
  exact cutA_le_one N z

theorem cutB_nonneg (N : ℕ) (z : ℝ) : 0 ≤ cutB N z := Real.smoothTransition.nonneg _

theorem cutB_le_one (N : ℕ) (z : ℝ) : cutB N z ≤ 1 := Real.smoothTransition.le_one _

theorem cutB_abs_le_one (N : ℕ) (z : ℝ) : |cutB N z| ≤ 1 := by
  rw [abs_of_nonneg (cutB_nonneg N z)]
  exact cutB_le_one N z

theorem contDiff_cutA (N : ℕ) : ContDiff ℝ ∞ (cutA N) := by
  have hσ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff (n := ⊤)
  have hg : ContDiff ℝ ∞ (fun z : ℝ => ((N : ℝ) + 1) * z - 1) := by fun_prop
  unfold cutA
  simpa [Function.comp_def] using hσ.comp hg

theorem contDiff_cutB (N : ℕ) : ContDiff ℝ ∞ (cutB N) := by
  have hσ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff (n := ⊤)
  have hg : ContDiff ℝ ∞ (fun z : ℝ => 2 - z / ((N : ℝ) + 1)) := by fun_prop
  unfold cutB
  simpa [Function.comp_def] using hσ.comp hg

theorem contDiff_monoCut (N : ℕ) : ContDiff ℝ ∞ (monoCut N) := by
  unfold monoCut
  exact (contDiff_cutA N).mul (contDiff_cutB N)

theorem monoCut_nonneg (N : ℕ) (z : ℝ) : 0 ≤ monoCut N z := by
  rw [monoCut]
  exact mul_nonneg (cutA_nonneg N z) (cutB_nonneg N z)

theorem monoCut_le_one (N : ℕ) (z : ℝ) : monoCut N z ≤ 1 := by
  rw [monoCut]
  calc cutA N z * cutB N z ≤ 1 * 1 :=
        mul_le_mul (cutA_le_one N z) (cutB_le_one N z) (cutB_nonneg N z) zero_le_one
    _ = 1 := by ring

theorem monoCut_eq_zero_of_nonpos (N : ℕ) {z : ℝ} (hz : z ≤ 0) : monoCut N z = 0 := by
  have h : ((N : ℝ) + 1) * z - 1 ≤ 0 := by
    have h' : ((N : ℝ) + 1) * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hz
    linarith
  rw [monoCut, cutA, Real.smoothTransition.zero_of_nonpos h, zero_mul]

theorem monoCut_eq_zero_of_le_inv (N : ℕ) {z : ℝ} (hz : z ≤ 1 / ((N : ℝ) + 1)) :
    monoCut N z = 0 := by
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmul : ((N : ℝ) + 1) * z ≤ 1 := by
    have h1 : ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1)) = 1 :=
      mul_one_div_cancel (ne_of_gt hpos)
    calc ((N : ℝ) + 1) * z ≤ ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hz (le_of_lt hpos)
      _ = 1 := h1
  rw [monoCut, cutA,
    Real.smoothTransition.zero_of_nonpos (by linarith : ((N : ℝ) + 1) * z - 1 ≤ 0), zero_mul]

theorem monoCut_eq_zero_of_two_mul_le (N : ℕ) {z : ℝ} (hz : 2 * ((N : ℝ) + 1) ≤ z) :
    monoCut N z = 0 := by
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h2 : 2 ≤ z / ((N : ℝ) + 1) := by
    rw [le_div_iff₀ hpos]
    linarith
  rw [monoCut, cutB,
    Real.smoothTransition.zero_of_nonpos (by linarith : 2 - z / ((N : ℝ) + 1) ≤ 0), mul_zero]

theorem monoCut_mono (N M : ℕ) (hNM : N ≤ M) {z : ℝ} (hz : 0 ≤ z) :
    monoCut N z ≤ monoCut M z := by
  have hNM' : ((N : ℝ) + 1) ≤ ((M : ℝ) + 1) := by
    have : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
    linarith
  have ha : cutA N z ≤ cutA M z := by
    refine Real.smoothTransition.monotone ?_
    have := mul_le_mul_of_nonneg_right hNM' hz
    linarith
  have hb : cutB N z ≤ cutB M z := by
    refine Real.smoothTransition.monotone ?_
    have hdiv : z / ((M : ℝ) + 1) ≤ z / ((N : ℝ) + 1) :=
      div_le_div_of_nonneg_left hz (by positivity) hNM'
    linarith
  rw [monoCut]
  exact mul_le_mul ha hb (cutB_nonneg N z) (cutA_nonneg M z)

theorem monoCut_eventually_one {z : ℝ} (hz : 0 < z) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → monoCut N z = 1 := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max (2 / z) z)
  refine ⟨n, fun N hN => ?_⟩
  have hN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlarge : 2 / z ≤ (N : ℝ) := le_trans (le_max_left (2 / z) z) (le_trans hn hN')
  have hsmall : z ≤ (N : ℝ) := le_trans (le_max_right (2 / z) z) (le_trans hn hN')
  have h1 : 1 ≤ ((N : ℝ) + 1) * z - 1 := by
    have h2 : 2 ≤ ((N : ℝ) + 1) * z := by
      rw [div_le_iff₀ hz] at hlarge
      nlinarith [hlarge, hz]
    linarith
  have h2 : 1 ≤ 2 - z / ((N : ℝ) + 1) := by
    have h3 : z / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      linarith
    linarith
  rw [monoCut, cutA, cutB, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.one_of_one_le h2, mul_one]

/-! ## The derivative -/

theorem hasDerivAt_cutA (N : ℕ) (z : ℝ) :
    HasDerivAt (cutA N)
      (deriv Real.smoothTransition (((N : ℝ) + 1) * z - 1) * ((N : ℝ) + 1)) z := by
  have hσ : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
  have h1 : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (((N : ℝ) + 1) * z - 1)) (((N : ℝ) + 1) * z - 1) :=
    (hσ _).hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ => ((N : ℝ) + 1) * y - 1) ((N : ℝ) + 1) z := by
    simpa using ((hasDerivAt_id z).const_mul ((N : ℝ) + 1)).sub_const 1
  unfold cutA
  exact h1.comp z h2

theorem hasDerivAt_cutB (N : ℕ) (z : ℝ) :
    HasDerivAt (cutB N)
      (deriv Real.smoothTransition (2 - z / ((N : ℝ) + 1)) * (-(1 / ((N : ℝ) + 1)))) z := by
  have hσ : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
  have h1 : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (2 - z / ((N : ℝ) + 1))) (2 - z / ((N : ℝ) + 1)) :=
    (hσ _).hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ => 2 - y / ((N : ℝ) + 1)) (-(1 / ((N : ℝ) + 1))) z := by
    have h : HasDerivAt (fun y : ℝ => y / ((N : ℝ) + 1)) (1 / ((N : ℝ) + 1)) z :=
      (hasDerivAt_id z).div_const ((N : ℝ) + 1)
    simpa using h.const_sub 2
  unfold cutB
  exact h1.comp z h2

theorem deriv_cutA (N : ℕ) (z : ℝ) :
    deriv (cutA N) z = deriv Real.smoothTransition (((N : ℝ) + 1) * z - 1) * ((N : ℝ) + 1) :=
  (hasDerivAt_cutA N z).deriv

theorem deriv_cutB (N : ℕ) (z : ℝ) :
    deriv (cutB N) z
      = deriv Real.smoothTransition (2 - z / ((N : ℝ) + 1)) * (-(1 / ((N : ℝ) + 1))) :=
  (hasDerivAt_cutB N z).deriv

theorem deriv_monoCut (N : ℕ) (z : ℝ) :
    deriv (monoCut N) z = deriv (cutA N) z * cutB N z + cutA N z * deriv (cutB N) z := by
  have h1 : DifferentiableAt ℝ (cutA N) z := (hasDerivAt_cutA N z).differentiableAt
  have h2 : DifferentiableAt ℝ (cutB N) z := (hasDerivAt_cutB N z).differentiableAt
  unfold monoCut
  exact deriv_mul h1 h2

/-- The exact form of the weighted derivative. -/
theorem z_mul_deriv_monoCut (N : ℕ) (z : ℝ) :
    z * deriv (monoCut N) z
      = (((N : ℝ) + 1) * z * deriv Real.smoothTransition (((N : ℝ) + 1) * z - 1)) * cutB N z
        - (z / ((N : ℝ) + 1)
            * deriv Real.smoothTransition (2 - z / ((N : ℝ) + 1))) * cutA N z := by
  rw [deriv_monoCut, deriv_cutA, deriv_cutB, cutA, cutB]
  ring

/-- **The weighted derivative bound** `|z (χ N)' z| ≤ 4M` for the witness, `M` bounding `|σ'|`.
(No hypothesis on `z` is needed: the bound holds on all of `ℝ`.) -/
theorem monoCut_z_deriv_le {M : ℝ} (hM : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M)
    (hM0 : 0 ≤ M) (N : ℕ) (z : ℝ) : |z * deriv (monoCut N) z| ≤ 4 * M := by
  rw [z_mul_deriv_monoCut]
  have hb : |(((N : ℝ) + 1) * z * deriv Real.smoothTransition (((N : ℝ) + 1) * z - 1))| ≤ 2 * M :=
    abs_mul_deriv_shift_le hM hM0 (((N : ℝ) + 1) * z)
  have ha : |(z / ((N : ℝ) + 1)
      * deriv Real.smoothTransition (2 - z / ((N : ℝ) + 1)))| ≤ 2 * M :=
    abs_mul_deriv_sub_le hM hM0 (z / ((N : ℝ) + 1))
  calc |(((N : ℝ) + 1) * z * deriv Real.smoothTransition (((N : ℝ) + 1) * z - 1)) * cutB N z
          - (z / ((N : ℝ) + 1)
              * deriv Real.smoothTransition (2 - z / ((N : ℝ) + 1))) * cutA N z|
      ≤ |(((N : ℝ) + 1) * z * deriv Real.smoothTransition (((N : ℝ) + 1) * z - 1)) * cutB N z|
        + |(z / ((N : ℝ) + 1)
            * deriv Real.smoothTransition (2 - z / ((N : ℝ) + 1))) * cutA N z| := by
        rw [sub_eq_add_neg]
        simpa using abs_add_le
          ((((N : ℝ) + 1) * z * deriv Real.smoothTransition (((N : ℝ) + 1) * z - 1)) * cutB N z)
          (-((z / ((N : ℝ) + 1)
              * deriv Real.smoothTransition (2 - z / ((N : ℝ) + 1))) * cutA N z))
    _ = |(((N : ℝ) + 1) * z * deriv Real.smoothTransition (((N : ℝ) + 1) * z - 1))| * |cutB N z|
        + |(z / ((N : ℝ) + 1)
            * deriv Real.smoothTransition (2 - z / ((N : ℝ) + 1)))| * |cutA N z| := by
        simp only [abs_mul]
    _ ≤ 2 * M * 1 + 2 * M * 1 := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul hb (cutB_abs_le_one N z) (abs_nonneg _) (by linarith)
        · exact mul_le_mul ha (cutA_abs_le_one N z) (abs_nonneg _) (by linarith)
    _ = 4 * M := by ring

/-! ## The repaired statement -/

/-- **The repaired `cutoffFamilyMono`**: the smoothness clause is stated in the smooth order `∞`
instead of the analytic order `⊤`; all the other clauses are verbatim.  Witness: the family
`monoCut N z = σ((N+1)z - 1) · σ(2 - z/(N+1))` with constant `4M + 1`, where `M` bounds `|σ'|`. -/
theorem cutoffFamilyMono_smooth :
    ∃ (χ : ℕ → ℝ → ℝ) (C : ℝ), 0 < C ∧
      (∀ N, ContDiff ℝ ∞ (χ N)) ∧
      (∀ N z, 0 ≤ χ N z) ∧ (∀ N z, χ N z ≤ 1) ∧
      (∀ (N : ℕ) (z : ℝ), z ≤ 0 → χ N z = 0) ∧
      (∀ (N : ℕ) (z : ℝ), z ≤ 1 / ((N : ℝ) + 1) → χ N z = 0) ∧
      (∀ (N : ℕ) (z : ℝ), 2 * ((N : ℝ) + 1) ≤ z → χ N z = 0) ∧
      (∀ (N M : ℕ), N ≤ M → ∀ z : ℝ, 0 ≤ z → χ N z ≤ χ M z) ∧
      (∀ z : ℝ, 0 < z → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → χ N z = 1) ∧
      (∀ (N : ℕ) (z : ℝ), |z * χ N z * deriv (χ N) z| ≤ C * χ N z) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_smoothTransition
  refine ⟨monoCut, 4 * M + 1, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun N => contDiff_monoCut N
  · exact fun N z => monoCut_nonneg N z
  · exact fun N z => monoCut_le_one N z
  · exact fun N z hz => monoCut_eq_zero_of_nonpos N hz
  · exact fun N z hz => monoCut_eq_zero_of_le_inv N hz
  · exact fun N z hz => monoCut_eq_zero_of_two_mul_le N hz
  · exact fun N M hNM z hz => monoCut_mono N M hNM hz
  · exact fun z hz => monoCut_eventually_one hz
  · intro N z
    have hχ : 0 ≤ monoCut N z := monoCut_nonneg N z
    have hbd : |z * deriv (monoCut N) z| ≤ 4 * M := monoCut_z_deriv_le hM hM0 N z
    calc |z * monoCut N z * deriv (monoCut N) z|
        = monoCut N z * |z * deriv (monoCut N) z| := by
          rw [show z * monoCut N z * deriv (monoCut N) z
                = monoCut N z * (z * deriv (monoCut N) z) from by ring,
            abs_mul, abs_of_nonneg hχ]
      _ ≤ monoCut N z * (4 * M + 1) := mul_le_mul_of_nonneg_left (by linarith) hχ
      _ = (4 * M + 1) * monoCut N z := by ring

/-- The repaired sibling `Work.FTS.EllipticEst.Mine.cutoffFamily`
(`Submission/Work/FTS/EllipticEst/Mine/cutoffFamily.lean`), which has the same `⊤` defect:
the statement above with `ContDiff ℝ ∞` and without the monotonicity clause.  Immediate from
`cutoffFamilyMono_smooth`, which is strictly stronger. -/
theorem cutoffFamily_smooth :
    ∃ (χ : ℕ → ℝ → ℝ) (C : ℝ), 0 < C ∧
      (∀ N, ContDiff ℝ ∞ (χ N)) ∧
      (∀ N z, 0 ≤ χ N z) ∧ (∀ N z, χ N z ≤ 1) ∧
      (∀ (N : ℕ) (z : ℝ), z ≤ 0 → χ N z = 0) ∧
      (∀ (N : ℕ) (z : ℝ), z ≤ 1 / ((N : ℝ) + 1) → χ N z = 0) ∧
      (∀ (N : ℕ) (z : ℝ), 2 * ((N : ℝ) + 1) ≤ z → χ N z = 0) ∧
      (∀ z : ℝ, 0 < z → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → χ N z = 1) ∧
      (∀ (N : ℕ) (z : ℝ), |z * χ N z * deriv (χ N) z| ≤ C * χ N z) := by
  obtain ⟨χ, C, hC, hsm, hnn, hle, hz0, hz1, hz2, _hmono, hsat, hder⟩ := cutoffFamilyMono_smooth
  exact ⟨χ, C, hC, hsm, hnn, hle, hz0, hz1, hz2, hsat, hder⟩

end Work.FTS.EllipticEst.Mine
