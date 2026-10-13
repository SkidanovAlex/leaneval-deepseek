import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `smoothCutoffIoo`: a smooth two-plateau cut-off on `[0, π/2]`

For every `ε > 0` we build an explicit `C²` function `χ` with

* `0 ≤ χ ≤ 1` everywhere,
* `χ θ = 0` for `θ ≤ ε/2` and for `π/2 - ε/2 ≤ θ`,
* `χ θ = 1` for `ε ≤ θ ≤ π/2 - ε`,
* `|χ' θ| ≤ M/ε` and `|χ'' θ| ≤ M/ε²` with a universal constant `M > 0`.

The construction uses the fixed `C^∞` profile

`Ψ s = Real.smoothTransition (2 s - 1)`,   which is `0` for `s ≤ 1/2` and `1` for `s ≥ 1`,

and the cut-off `χ θ = Ψ (θ/ε) * Ψ ((π/2 - θ)/ε)`.  The constant `M` is built from the two
sup-norms `S₁ = sup |Ψ'|`, `S₂ = sup |Ψ''|`, which exist because `Ψ` is `C^∞` and locally
constant off the compact interval `[1/2, 1]`.
-/

namespace Work.FTS.EllipticEst.SliceMixedAux

noncomputable section

open scoped Real Topology

/-! ## The fixed profile `Ψ` -/

/-- The fixed `C^∞` profile `Ψ s = smoothTransition (2 s - 1)`: it is `0` for `s ≤ 1/2`,
`1` for `s ≥ 1`, and everywhere in `[0,1]`. -/
def prof (s : ℝ) : ℝ := Real.smoothTransition (2 * s - 1)

theorem prof_contDiff (n : ℕ∞) : ContDiff ℝ n prof := by
  have h : ContDiff ℝ n (fun s : ℝ => 2 * s - 1) :=
    ((contDiff_const (c := (2 : ℝ))).mul contDiff_id).sub contDiff_const
  exact (Real.smoothTransition.contDiff (n := n)).comp h

theorem prof_nonneg (s : ℝ) : 0 ≤ prof s := Real.smoothTransition.nonneg _

theorem prof_le_one (s : ℝ) : prof s ≤ 1 := Real.smoothTransition.le_one _

theorem prof_abs_le_one (s : ℝ) : |prof s| ≤ 1 := by
  rw [abs_of_nonneg (prof_nonneg s)]
  exact prof_le_one s

theorem prof_eq_zero {s : ℝ} (h : s ≤ 1 / 2) : prof s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem prof_eq_one {s : ℝ} (h : 1 ≤ s) : prof s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem prof_differentiable : Differentiable ℝ prof :=
  (prof_contDiff (⊤ : ℕ∞)).differentiable (by simp)

theorem prof_deriv_differentiable : Differentiable ℝ (deriv prof) := by
  have h := (prof_contDiff (⊤ : ℕ∞)).differentiable_iteratedDeriv 1 (by norm_num)
  rwa [iteratedDeriv_one] at h

/-! ## Vanishing of the derivatives of `Ψ` off the compact interval `[1/2, 1]` -/

theorem prof_deriv_eq_zero_of_notMem {s : ℝ} (hs : s ∉ Set.Icc (1 / 2 : ℝ) 1) :
    deriv prof s = 0 := by
  rw [Set.mem_Icc, not_and_or] at hs
  rcases hs with hs | hs
  · have hs' : s < 1 / 2 := not_le.mp hs
    have hev : prof =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hs'] with y hy
      exact prof_eq_zero (le_of_lt hy)
    rw [hev.deriv_eq]
    simp
  · have hs' : 1 < s := not_le.mp hs
    have hev : prof =ᶠ[𝓝 s] (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hs'] with y hy
      exact prof_eq_one (le_of_lt hy)
    rw [hev.deriv_eq]
    simp

theorem prof_deriv2_eq_zero_of_notMem {s : ℝ} (hs : s ∉ Set.Icc (1 / 2 : ℝ) 1) :
    deriv (deriv prof) s = 0 := by
  have hev : deriv prof =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ)) := by
    rw [Set.mem_Icc, not_and_or] at hs
    rcases hs with hs | hs
    · have hs' : s < 1 / 2 := not_le.mp hs
      filter_upwards [isOpen_Iio.mem_nhds hs'] with y hy
      exact prof_deriv_eq_zero_of_notMem (fun h => absurd h.1 (not_le_of_gt hy))
    · have hs' : 1 < s := not_le.mp hs
      filter_upwards [isOpen_Ioi.mem_nhds hs'] with y hy
      exact prof_deriv_eq_zero_of_notMem (fun h => absurd h.2 (not_le_of_gt hy))
  rw [hev.deriv_eq]
  simp

/-! ## Sup-norm bounds for `Ψ'` and `Ψ''` -/

theorem exists_prof_deriv_bound : ∃ M : ℝ, ∀ s : ℝ, |deriv prof s| ≤ M := by
  have hcont : Continuous (deriv prof) := (prof_contDiff (⊤ : ℕ∞)).continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun s => ?_⟩
  by_cases hs : s ∈ Set.Icc (1 / 2 : ℝ) 1
  · have h := hC s hs
    rwa [Real.norm_eq_abs] at h
  · rw [prof_deriv_eq_zero_of_notMem hs, abs_zero]
    exact le_trans (abs_nonneg _) (hC (1 / 2) (by norm_num))

theorem exists_prof_deriv2_bound : ∃ M : ℝ, ∀ s : ℝ, |deriv (deriv prof) s| ≤ M := by
  have hcont : Continuous (deriv (deriv prof)) := by
    have h := (prof_contDiff (⊤ : ℕ∞)).continuous_iteratedDeriv 2 (by norm_num)
    rwa [iteratedDeriv_succ, iteratedDeriv_one] at h
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun s => ?_⟩
  by_cases hs : s ∈ Set.Icc (1 / 2 : ℝ) 1
  · have h := hC s hs
    rwa [Real.norm_eq_abs] at h
  · rw [prof_deriv2_eq_zero_of_notMem hs, abs_zero]
    exact le_trans (abs_nonneg _) (hC (1 / 2) (by norm_num))

/-! ## Chain rules with the affine substitutions `t ↦ t/c` and `t ↦ (p-t)/c` -/

theorem hasDerivAt_comp_div (g : ℝ → ℝ) (hg : Differentiable ℝ g) (c x : ℝ) :
    HasDerivAt (fun t : ℝ => g (t / c)) (deriv g (x / c) * (1 / c)) x := by
  have hin : HasDerivAt (fun t : ℝ => t / c) (1 / c) x := by
    simpa using (hasDerivAt_id x).div_const c
  exact (hg.differentiableAt (x := x / c)).hasDerivAt.comp x hin

theorem hasDerivAt_comp_sub_div (g : ℝ → ℝ) (hg : Differentiable ℝ g) (p c x : ℝ) :
    HasDerivAt (fun t : ℝ => g ((p - t) / c)) (deriv g ((p - x) / c) * (-(1 / c))) x := by
  have hin : HasDerivAt (fun t : ℝ => (p - t) / c) (-(1 / c)) x := by
    have h : HasDerivAt (fun t : ℝ => p - t) (-1) x := (hasDerivAt_id x).const_sub p
    have h2 : HasDerivAt (fun t : ℝ => (p - t) / c) ((-1 : ℝ) / c) x := h.div_const c
    have he : (-1 : ℝ) / c = -(1 / c) := by ring
    rwa [he] at h2
  exact (hg.differentiableAt (x := (p - x) / c)).hasDerivAt.comp x hin

theorem deriv_comp_div (g : ℝ → ℝ) (hg : Differentiable ℝ g) (c x : ℝ) :
    deriv (fun t : ℝ => g (t / c)) x = deriv g (x / c) * (1 / c) :=
  (hasDerivAt_comp_div g hg c x).deriv

theorem deriv_comp_sub_div (g : ℝ → ℝ) (hg : Differentiable ℝ g) (p c x : ℝ) :
    deriv (fun t : ℝ => g ((p - t) / c)) x = deriv g ((p - x) / c) * (-(1 / c)) :=
  (hasDerivAt_comp_sub_div g hg p c x).deriv

/-! ## The cut-off `χ_ε` -/

/-- The cut-off `χ_ε θ = Ψ (θ/ε) * Ψ ((π/2 - θ)/ε)`. -/
def cut (ε : ℝ) (θ : ℝ) : ℝ := prof (θ / ε) * prof ((Real.pi / 2 - θ) / ε)

theorem cut_contDiff (ε : ℝ) : ContDiff ℝ 2 (cut ε) := by
  have h1 : ContDiff ℝ 2 (fun θ : ℝ => prof (θ / ε)) :=
    (prof_contDiff (2 : ℕ∞)).comp (contDiff_id.div_const ε)
  have h2 : ContDiff ℝ 2 (fun θ : ℝ => prof ((Real.pi / 2 - θ) / ε)) :=
    (prof_contDiff (2 : ℕ∞)).comp
      (((contDiff_const (c := (Real.pi / 2 : ℝ))).sub contDiff_id).div_const ε)
  exact h1.mul h2

theorem cut_nonneg (ε θ : ℝ) : 0 ≤ cut ε θ :=
  mul_nonneg (prof_nonneg _) (prof_nonneg _)

theorem cut_le_one (ε θ : ℝ) : cut ε θ ≤ 1 := by
  rw [cut]
  calc prof (θ / ε) * prof ((Real.pi / 2 - θ) / ε)
      ≤ 1 * 1 := mul_le_mul (prof_le_one _) (prof_le_one _) (prof_nonneg _) (by norm_num)
    _ = 1 := by ring

theorem cut_eq_zero_low {ε θ : ℝ} (hε : 0 < ε) (h : θ ≤ ε / 2) : cut ε θ = 0 := by
  have h1 : θ / ε ≤ 1 / 2 := by rw [div_le_iff₀ hε]; linarith
  rw [cut, prof_eq_zero h1, zero_mul]

theorem cut_eq_zero_high {ε θ : ℝ} (hε : 0 < ε) (h : Real.pi / 2 - ε / 2 ≤ θ) :
    cut ε θ = 0 := by
  have h1 : (Real.pi / 2 - θ) / ε ≤ 1 / 2 := by rw [div_le_iff₀ hε]; linarith
  rw [cut, prof_eq_zero h1, mul_zero]

theorem cut_eq_one {ε θ : ℝ} (hε : 0 < ε) (h1 : ε ≤ θ) (h2 : θ ≤ Real.pi / 2 - ε) :
    cut ε θ = 1 := by
  have ha : 1 ≤ θ / ε := by rw [le_div_iff₀ hε]; linarith
  have hb : 1 ≤ (Real.pi / 2 - θ) / ε := by rw [le_div_iff₀ hε]; linarith
  rw [cut, prof_eq_one ha, prof_eq_one hb, one_mul]

/-! ## The two derivatives of `χ_ε` -/

theorem deriv_cut (ε θ : ℝ) :
    deriv (cut ε) θ = deriv prof (θ / ε) * (1 / ε) * prof ((Real.pi / 2 - θ) / ε)
      + prof (θ / ε) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε))) := by
  have hA := hasDerivAt_comp_div prof prof_differentiable ε θ
  have hB := hasDerivAt_comp_sub_div prof prof_differentiable (Real.pi / 2) ε θ
  have hcut : cut ε = (fun t : ℝ => prof (t / ε)) * fun t : ℝ => prof ((Real.pi / 2 - t) / ε) :=
    rfl
  rw [hcut]
  exact (hA.mul hB).deriv

theorem deriv2_cut (ε θ : ℝ) :
    deriv (deriv (cut ε)) θ =
      (deriv (deriv prof) (θ / ε) * (1 / ε) * (1 / ε)) * prof ((Real.pi / 2 - θ) / ε)
      + (deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε)))
      + ((deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε)))
          + prof (θ / ε) *
              (deriv (deriv prof) ((Real.pi / 2 - θ) / ε) * (-(1 / ε)) * (-(1 / ε)))) := by
  have hd1 : deriv (cut ε) = fun θ : ℝ =>
      deriv prof (θ / ε) * (1 / ε) * prof ((Real.pi / 2 - θ) / ε)
        + prof (θ / ε) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε))) :=
    funext (fun θ => deriv_cut ε θ)
  have hP : HasDerivAt (fun t : ℝ => deriv prof (t / ε) * (1 / ε))
      (deriv (deriv prof) (θ / ε) * (1 / ε) * (1 / ε)) θ :=
    (hasDerivAt_comp_div (deriv prof) prof_deriv_differentiable ε θ).mul_const (1 / ε)
  have hB : HasDerivAt (fun t : ℝ => prof ((Real.pi / 2 - t) / ε))
      (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε))) θ :=
    hasDerivAt_comp_sub_div prof prof_differentiable (Real.pi / 2) ε θ
  have hA : HasDerivAt (fun t : ℝ => prof (t / ε)) (deriv prof (θ / ε) * (1 / ε)) θ :=
    hasDerivAt_comp_div prof prof_differentiable ε θ
  have hQ : HasDerivAt (fun t : ℝ => deriv prof ((Real.pi / 2 - t) / ε) * (-(1 / ε)))
      (deriv (deriv prof) ((Real.pi / 2 - θ) / ε) * (-(1 / ε)) * (-(1 / ε))) θ :=
    (hasDerivAt_comp_sub_div (deriv prof) prof_deriv_differentiable (Real.pi / 2) ε θ).mul_const
      (-(1 / ε))
  have hF := hP.mul hB
  have hG := hA.mul hQ
  have hsum := hF.add hG
  have hsplit : (fun θ : ℝ =>
        deriv prof (θ / ε) * (1 / ε) * prof ((Real.pi / 2 - θ) / ε)
          + prof (θ / ε) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε))))
      = (fun θ : ℝ => deriv prof (θ / ε) * (1 / ε) * prof ((Real.pi / 2 - θ) / ε))
        + (fun θ : ℝ => prof (θ / ε) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε)))) := rfl
  rw [hd1, hsplit]
  exact hsum.deriv

/-! ## The derivative bounds -/

theorem abs_deriv_cut_le {ε : ℝ} (hε : 0 < ε) {S1 : ℝ}
    (hS1 : ∀ s : ℝ, |deriv prof s| ≤ S1) (θ : ℝ) :
    |deriv (cut ε) θ| ≤ 2 * S1 / ε := by
  have hS1nn : 0 ≤ S1 := le_trans (abs_nonneg _) (hS1 0)
  have hE : (0 : ℝ) < 1 / ε := by positivity
  have hEabs : |(1 / ε : ℝ)| = 1 / ε := abs_of_nonneg hE.le
  rw [deriv_cut ε θ]
  have e1 : |deriv prof (θ / ε) * (1 / ε) * prof ((Real.pi / 2 - θ) / ε)| ≤ S1 * (1 / ε) := by
    simp only [abs_mul, hEabs]
    calc |deriv prof (θ / ε)| * (1 / ε) * |prof ((Real.pi / 2 - θ) / ε)|
        ≤ S1 * (1 / ε) * 1 :=
          mul_le_mul (mul_le_mul (hS1 _) le_rfl hE.le hS1nn) (prof_abs_le_one _)
            (abs_nonneg _) (mul_nonneg hS1nn hE.le)
      _ = S1 * (1 / ε) := by ring
  have e2 : |prof (θ / ε) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε)))|
      ≤ S1 * (1 / ε) := by
    simp only [abs_mul, abs_neg, hEabs]
    calc |prof (θ / ε)| * (|deriv prof ((Real.pi / 2 - θ) / ε)| * (1 / ε))
        ≤ 1 * (S1 * (1 / ε)) :=
          mul_le_mul (prof_abs_le_one _)
            (mul_le_mul (hS1 _) le_rfl hE.le hS1nn)
            (mul_nonneg (abs_nonneg _) hE.le) (by norm_num)
      _ = S1 * (1 / ε) := by ring
  calc |deriv prof (θ / ε) * (1 / ε) * prof ((Real.pi / 2 - θ) / ε)
        + prof (θ / ε) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε)))|
      ≤ |deriv prof (θ / ε) * (1 / ε) * prof ((Real.pi / 2 - θ) / ε)|
        + |prof (θ / ε) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε)))| := abs_add_le _ _
    _ ≤ S1 * (1 / ε) + S1 * (1 / ε) := add_le_add e1 e2
    _ = 2 * S1 / ε := by ring

theorem abs_deriv2_cut_le {ε : ℝ} (hε : 0 < ε) {S1 S2 : ℝ}
    (hS1 : ∀ s : ℝ, |deriv prof s| ≤ S1) (hS2 : ∀ s : ℝ, |deriv (deriv prof) s| ≤ S2)
    (θ : ℝ) : |deriv (deriv (cut ε)) θ| ≤ (2 * S2 + 2 * S1 ^ 2) / ε ^ 2 := by
  have hS1nn : 0 ≤ S1 := le_trans (abs_nonneg _) (hS1 0)
  have hS2nn : 0 ≤ S2 := le_trans (abs_nonneg _) (hS2 0)
  have hE : (0 : ℝ) < 1 / ε := by positivity
  have hEabs : |(1 / ε : ℝ)| = 1 / ε := abs_of_nonneg hE.le
  rw [deriv2_cut ε θ]
  have t1 : |(deriv (deriv prof) (θ / ε) * (1 / ε) * (1 / ε)) * prof ((Real.pi / 2 - θ) / ε)|
      ≤ S2 * (1 / ε) * (1 / ε) := by
    simp only [abs_mul, hEabs]
    calc |deriv (deriv prof) (θ / ε)| * (1 / ε) * (1 / ε) * |prof ((Real.pi / 2 - θ) / ε)|
        ≤ S2 * (1 / ε) * (1 / ε) * 1 :=
          mul_le_mul
            (mul_le_mul (mul_le_mul (hS2 _) le_rfl hE.le hS2nn) le_rfl hE.le
              (mul_nonneg hS2nn hE.le))
            (prof_abs_le_one _) (abs_nonneg _) (mul_nonneg (mul_nonneg hS2nn hE.le) hE.le)
      _ = S2 * (1 / ε) * (1 / ε) := by ring
  have t2 : |(deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε)))|
      ≤ S1 * (1 / ε) * (S1 * (1 / ε)) := by
    simp only [abs_mul, abs_neg, hEabs]
    calc |deriv prof (θ / ε)| * (1 / ε) * (|deriv prof ((Real.pi / 2 - θ) / ε)| * (1 / ε))
        ≤ S1 * (1 / ε) * (S1 * (1 / ε)) :=
          mul_le_mul (mul_le_mul (hS1 _) le_rfl hE.le hS1nn)
            (mul_le_mul (hS1 _) le_rfl hE.le hS1nn)
            (mul_nonneg (abs_nonneg _) hE.le) (mul_nonneg hS1nn hE.le)
      _ = S1 * (1 / ε) * (S1 * (1 / ε)) := rfl
  have t4 : |prof (θ / ε) *
        (deriv (deriv prof) ((Real.pi / 2 - θ) / ε) * (-(1 / ε)) * (-(1 / ε)))|
      ≤ S2 * (1 / ε) * (1 / ε) := by
    simp only [abs_mul, abs_neg, hEabs]
    calc |prof (θ / ε)| * (|deriv (deriv prof) ((Real.pi / 2 - θ) / ε)| * (1 / ε) * (1 / ε))
        ≤ 1 * (S2 * (1 / ε) * (1 / ε)) :=
          mul_le_mul (prof_abs_le_one _)
            (mul_le_mul (mul_le_mul (hS2 _) le_rfl hE.le hS2nn) le_rfl hE.le
              (mul_nonneg hS2nn hE.le))
            (mul_nonneg (mul_nonneg (abs_nonneg _) hE.le) hE.le) (by norm_num)
      _ = S2 * (1 / ε) * (1 / ε) := by ring
  have htri : |((deriv (deriv prof) (θ / ε) * (1 / ε) * (1 / ε)) * prof ((Real.pi / 2 - θ) / ε)
        + (deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε))))
        + ((deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε)))
            + prof (θ / ε) *
                (deriv (deriv prof) ((Real.pi / 2 - θ) / ε) * (-(1 / ε)) * (-(1 / ε))))|
      ≤ |(deriv (deriv prof) (θ / ε) * (1 / ε) * (1 / ε)) * prof ((Real.pi / 2 - θ) / ε)|
        + |(deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε)))|
        + (|(deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε)))|
            + |prof (θ / ε) *
                (deriv (deriv prof) ((Real.pi / 2 - θ) / ε) * (-(1 / ε)) * (-(1 / ε)))|) := by
    have h1 := abs_add_le
      ((deriv (deriv prof) (θ / ε) * (1 / ε) * (1 / ε)) * prof ((Real.pi / 2 - θ) / ε)
        + (deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε))))
      ((deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε)))
        + prof (θ / ε) *
            (deriv (deriv prof) ((Real.pi / 2 - θ) / ε) * (-(1 / ε)) * (-(1 / ε))))
    have h2 := abs_add_le
      ((deriv (deriv prof) (θ / ε) * (1 / ε) * (1 / ε)) * prof ((Real.pi / 2 - θ) / ε))
      ((deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε))))
    have h3 := abs_add_le
      ((deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε))))
      (prof (θ / ε) *
        (deriv (deriv prof) ((Real.pi / 2 - θ) / ε) * (-(1 / ε)) * (-(1 / ε))))
    linarith
  calc |((deriv (deriv prof) (θ / ε) * (1 / ε) * (1 / ε)) * prof ((Real.pi / 2 - θ) / ε)
        + (deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε))))
        + ((deriv prof (θ / ε) * (1 / ε)) * (deriv prof ((Real.pi / 2 - θ) / ε) * (-(1 / ε)))
            + prof (θ / ε) *
                (deriv (deriv prof) ((Real.pi / 2 - θ) / ε) * (-(1 / ε)) * (-(1 / ε))))|
      ≤ _ := htri
    _ ≤ S2 * (1 / ε) * (1 / ε) + S1 * (1 / ε) * (S1 * (1 / ε))
        + (S1 * (1 / ε) * (S1 * (1 / ε)) + S2 * (1 / ε) * (1 / ε)) := by
          linarith [t1, t2, t4]
    _ = (2 * S2 + 2 * S1 ^ 2) / ε ^ 2 := by ring

/-! ## The main theorem -/

theorem smoothCutoffIoo : ∃ M : ℝ, 0 < M ∧ ∀ ε : ℝ, 0 < ε → ∃ χ : ℝ → ℝ,
    ContDiff ℝ 2 χ ∧ (∀ θ : ℝ, 0 ≤ χ θ) ∧ (∀ θ : ℝ, χ θ ≤ 1) ∧
    (∀ θ : ℝ, θ ≤ ε / 2 → χ θ = 0) ∧
    (∀ θ : ℝ, Real.pi / 2 - ε / 2 ≤ θ → χ θ = 0) ∧
    (∀ θ : ℝ, ε ≤ θ → θ ≤ Real.pi / 2 - ε → χ θ = 1) ∧
    (∀ θ : ℝ, |deriv χ θ| ≤ M / ε) ∧
    (∀ θ : ℝ, |deriv (deriv χ) θ| ≤ M / ε ^ 2) := by
  obtain ⟨S1, hS1⟩ := exists_prof_deriv_bound
  obtain ⟨S2, hS2⟩ := exists_prof_deriv2_bound
  have hS1nn : 0 ≤ S1 := le_trans (abs_nonneg _) (hS1 0)
  have hS2nn : 0 ≤ S2 := le_trans (abs_nonneg _) (hS2 0)
  refine ⟨2 * S1 + 2 * S2 + 2 * S1 ^ 2 + 1, ?_, fun ε hε => ?_⟩
  · nlinarith [sq_nonneg S1, sq_nonneg S2]
  refine ⟨cut ε, cut_contDiff ε, fun θ => cut_nonneg ε θ, fun θ => cut_le_one ε θ,
    fun θ h => cut_eq_zero_low hε h, fun θ h => cut_eq_zero_high hε h,
    fun θ h1 h2 => cut_eq_one hε h1 h2, fun θ => ?_, fun θ => ?_⟩
  · have h1 := abs_deriv_cut_le hε hS1 θ
    have h2 : 2 * S1 ≤ 2 * S1 + 2 * S2 + 2 * S1 ^ 2 + 1 := by nlinarith [sq_nonneg S1, hS2nn]
    exact le_trans h1 (div_le_div_of_nonneg_right h2 hε.le)
  · have h1 := abs_deriv2_cut_le hε hS1 hS2 θ
    have h2 : 2 * S2 + 2 * S1 ^ 2 ≤ 2 * S1 + 2 * S2 + 2 * S1 ^ 2 + 1 := by
      nlinarith [sq_nonneg S1, hS1nn]
    exact le_trans h1 (div_le_div_of_nonneg_right h2 (sq_nonneg ε))

end

end Work.FTS.EllipticEst.SliceMixedAux
