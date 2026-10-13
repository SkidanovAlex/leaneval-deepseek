import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.Reconstruct
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.le_zero_of_hasDerivAt_nonpos_of_tendsto_nhdsGT
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.le_zero_of_hasDerivAt_nonneg_of_tendsto_nhdsLT

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `vopRated` — the rated `Vop`-bound on the slice `(0, π/2)`

For a function `f : ℝ → ℝ` whose logarithmic derivative along `θ` is bounded,
`|f' θ - tan θ · f θ| ≤ K` on `(0, π/2)`, and which vanishes at `θ = 0⁺` and whose
product with `cos` vanishes at `θ → (π/2)⁻`, the function itself is dominated by
`K · tan θ` and by `K · (1 - sin θ)/cos θ`:

* `|f θ| ≤ K · tan θ` (the "rated" bound: the singularity at `0` is at worst that of the
  homogeneous solution `1/cos θ`, tested against the vanishing at `0⁺`);
* `|f θ| ≤ K · (1 - sin θ)/cos θ` (the boundary condition at `π/2`: there
  `1 - sin θ = cos²θ/(1 + sin θ)`, so the bound is `K · cos θ/(1 + sin θ)`).

The mechanism is the multiplicative integrating factor `g θ = cos θ · f θ`, for which
`g' θ = cos θ · (f' θ - tan θ · f θ)`, hence `|g'| ≤ K cos θ`.  The two conclusions are the
four comparisons

* `g ≤ K sin θ` and `-g ≤ K sin θ`, both from the limit `0` at `0⁺` (left-endpoint
  comparison, `le_zero_of_hasDerivAt_nonpos_of_tendsto_nhdsGT`),
* `g ≤ K (1 - sin θ)` and `-g ≤ K (1 - sin θ)`, both from the limit `0` at `(π/2)⁻`
  (right-endpoint comparison, `le_zero_of_hasDerivAt_nonneg_of_tendsto_nhdsLT`),

combined with `|g θ| = cos θ · |f θ|` (`cos θ > 0` on `(0, π/2)`).
-/

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open scoped Real Topology
open Filter Set

theorem vopRated {f f' : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt f (f' θ) θ)
    (hbound : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f' θ - Real.tan θ * f θ| ≤ K)
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (h1 : Filter.Tendsto (fun θ : ℝ => Real.cos θ * f θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ K * (Real.sin θ / Real.cos θ)) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |f θ| ≤ K * ((1 - Real.sin θ) / Real.cos θ)) := by
  have hπ2 : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcospos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
  -- ## the derivative of the integrating factor `g θ = cos θ · f θ`
  have hgd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ : ℝ => Real.cos θ * f θ) (Real.cos θ * (f' θ - Real.tan θ * f θ)) θ := by
    intro θ hθ
    have hc : Real.cos θ ≠ 0 := ne_of_gt (hcospos θ hθ)
    refine ((Real.hasDerivAt_cos θ).mul (hder θ hθ)).congr_deriv ?_
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have hgbd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.cos θ * (f' θ - Real.tan θ * f θ)| ≤ K * Real.cos θ := by
    intro θ hθ
    calc |Real.cos θ * (f' θ - Real.tan θ * f θ)|
        = Real.cos θ * |f' θ - Real.tan θ * f θ| := by
          rw [abs_mul, abs_of_pos (hcospos θ hθ)]
      _ ≤ Real.cos θ * K := mul_le_mul_of_nonneg_left (hbound θ hθ) (le_of_lt (hcospos θ hθ))
      _ = K * Real.cos θ := by ring
  -- ## the two endpoint limits, as limits of the integrating factor
  have hlim0 : Filter.Tendsto (fun θ : ℝ => Real.cos θ * f θ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Filter.Tendsto (fun θ : ℝ => Real.cos θ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa [Real.cos_zero] using
        (Real.continuous_cos.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using hc.mul h0
  have hlim0Ks : Filter.Tendsto (fun θ : ℝ => K * Real.sin θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Real.sin_zero] using
      ((Real.continuous_sin.tendsto 0).mono_left nhdsWithin_le_nhds).const_mul K
  have hlimKc : Filter.Tendsto (fun θ : ℝ => K * (1 - Real.sin θ)) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have hs : Filter.Tendsto (fun θ : ℝ => Real.sin θ) (𝓝[<] (Real.pi / 2)) (𝓝 1) := by
      simpa [Real.sin_pi_div_two] using
        (Real.continuous_sin.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds
    have h1' : Filter.Tendsto (fun θ : ℝ => 1 - Real.sin θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
      have hconst : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[<] (Real.pi / 2)) (𝓝 1) :=
        tendsto_const_nhds
      simpa using hconst.sub hs
    simpa using h1'.const_mul K
  -- ## the four comparison functions
  have hA : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Real.cos θ * f θ - K * Real.sin θ ≤ 0 := by
    refine le_zero_of_hasDerivAt_nonpos_of_tendsto_nhdsGT (a := 0) (b := Real.pi / 2) (c := 0) hπ2
      (h := fun θ : ℝ => Real.cos θ * f θ - K * Real.sin θ)
      (h' := fun θ : ℝ => Real.cos θ * (f' θ - Real.tan θ * f θ) - K * Real.cos θ)
      ?_ ?_ ?_ (le_refl 0)
    · intro x hx
      exact (hgd x hx).sub ((Real.hasDerivAt_sin x).const_mul K)
    · intro x hx
      have h1 := hgbd x hx
      have h2 := le_abs_self (Real.cos x * (f' x - Real.tan x * f x))
      linarith
    · simpa using hlim0.sub hlim0Ks
  have hB : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      -(Real.cos θ * f θ) - K * Real.sin θ ≤ 0 := by
    refine le_zero_of_hasDerivAt_nonpos_of_tendsto_nhdsGT (a := 0) (b := Real.pi / 2) (c := 0) hπ2
      (h := fun θ : ℝ => -(Real.cos θ * f θ) - K * Real.sin θ)
      (h' := fun θ : ℝ => -(Real.cos θ * (f' θ - Real.tan θ * f θ)) - K * Real.cos θ)
      ?_ ?_ ?_ (le_refl 0)
    · intro x hx
      exact (hgd x hx).neg.sub ((Real.hasDerivAt_sin x).const_mul K)
    · intro x hx
      have h1 := hgbd x hx
      have h2 := neg_le_abs (Real.cos x * (f' x - Real.tan x * f x))
      linarith
    · simpa using hlim0.neg.sub hlim0Ks
  have hC : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Real.cos θ * f θ - K * (1 - Real.sin θ) ≤ 0 := by
    refine le_zero_of_hasDerivAt_nonneg_of_tendsto_nhdsLT (a := 0) (b := Real.pi / 2) (c := 0) hπ2
      (h := fun θ : ℝ => Real.cos θ * f θ - K * (1 - Real.sin θ))
      (h' := fun θ : ℝ => Real.cos θ * (f' θ - Real.tan θ * f θ) + K * Real.cos θ)
      ?_ ?_ ?_ (le_refl 0)
    · intro x hx
      have h := (hgd x hx).sub (((Real.hasDerivAt_sin x).const_sub 1).const_mul K)
      refine h.congr_deriv ?_
      ring
    · intro x hx
      have h1 := (abs_le.mp (hgbd x hx)).1
      linarith
    · simpa using h1.sub hlimKc
  have hD : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      -(Real.cos θ * f θ) - K * (1 - Real.sin θ) ≤ 0 := by
    refine le_zero_of_hasDerivAt_nonneg_of_tendsto_nhdsLT (a := 0) (b := Real.pi / 2) (c := 0) hπ2
      (h := fun θ : ℝ => -(Real.cos θ * f θ) - K * (1 - Real.sin θ))
      (h' := fun θ : ℝ => -(Real.cos θ * (f' θ - Real.tan θ * f θ)) + K * Real.cos θ)
      ?_ ?_ ?_ (le_refl 0)
    · intro x hx
      have h := (hgd x hx).neg.sub (((Real.hasDerivAt_sin x).const_sub 1).const_mul K)
      refine h.congr_deriv ?_
      ring
    · intro x hx
      have h1 := (abs_le.mp (hgbd x hx)).2
      linarith
    · simpa using h1.neg.sub hlimKc
  -- ## assembly
  constructor
  · intro θ hθ
    have hc := hcospos θ hθ
    have hgabs : Real.cos θ * |f θ| ≤ K * Real.sin θ := by
      have habs : |Real.cos θ * f θ| ≤ K * Real.sin θ :=
        abs_le.mpr ⟨by linarith [hB θ hθ], by linarith [hA θ hθ]⟩
      rwa [abs_mul, abs_of_pos hc] at habs
    have hkey : |f θ| ≤ K * Real.sin θ / Real.cos θ := by
      rw [le_div_iff₀ hc]
      calc |f θ| * Real.cos θ = Real.cos θ * |f θ| := by ring
        _ ≤ K * Real.sin θ := hgabs
    calc |f θ| ≤ K * Real.sin θ / Real.cos θ := hkey
      _ = K * (Real.sin θ / Real.cos θ) := by ring
  · intro θ hθ
    have hc := hcospos θ hθ
    have hgabs : Real.cos θ * |f θ| ≤ K * (1 - Real.sin θ) := by
      have habs : |Real.cos θ * f θ| ≤ K * (1 - Real.sin θ) :=
        abs_le.mpr ⟨by linarith [hD θ hθ], by linarith [hC θ hθ]⟩
      rwa [abs_mul, abs_of_pos hc] at habs
    have hkey : |f θ| ≤ K * (1 - Real.sin θ) / Real.cos θ := by
      rw [le_div_iff₀ hc]
      calc |f θ| * Real.cos θ = Real.cos θ * |f θ| := by ring
        _ ≤ K * (1 - Real.sin θ) := hgabs
    calc |f θ| ≤ K * (1 - Real.sin θ) / Real.cos θ := hkey
      _ = K * ((1 - Real.sin θ) / Real.cos θ) := by ring

end Work.FTS_EllLimOK.ProducerH.BoxAux
