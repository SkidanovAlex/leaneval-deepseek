/-
# `Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds_from_aux`

The assembly of `Work.FTS_RegExport.RXR5L.aux.Tlim_bounds`: the uniform bound and the fake-time
modulus of the transport zero-mode `L₁₂(3·D_θ(slice g τ)/(1+z))(0)` of a strong solution family
`g`.

The two analytic inputs are taken here as hypotheses, so that this file builds independently of
them; the consumer instantiates them with

* `Work.FTS_RegExport.RXR5L.Auxiliary.Dth_slice_bounds` — the pointwise bound
  `|D_θ(slice g τ)| ≤ C₁·Rwt` and the pointwise `τ`-modulus
  `|D_θ(slice g τ) - D_θ(slice g τ')| ≤ C₁·Rwt·|τ-τ'|` on `[0,S]` and the closed angular
  interval, with `Rwt z = z^{3/2}/(1+z)²`;
* `Work.FTS_RegExport.RXR5L.Auxiliary.L12_sub_of_bdd` — the linearity
  `L₁₂ a(0) - L₁₂ b(0) = L₁₂(a-b)(0)` of `L₁₂` in its profile for continuous data dominated by a
  multiple of `Rwt·(1+·)⁻¹`.

The proof is then elementary: the pointwise majorant is pushed through the two integrals defining
`L₁₂` by the (hypothesis-free) mean inequality
`Work.FTS_RegExport.RXR5L.aux.abs_L12_zero_le_of_pointwise`
`|L₁₂ f (0)| ≤ 3·(π/2)·M·2` for `|f| ≤ M·Rwt`, which gives both claims with the *same* constant
`3π·(3C₁)`: the first by applying it to the datum of `slice g τ` itself, the second by applying
it to the *difference* of the two data (a legitimate function, whose `L₁₂` is the difference of
the two `L₁₂`'s by `hsub`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.abs_L12_zero_le_of_pointwise
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXR5L.Auxiliary

set_option autoImplicit false

local notation "Rwt" => Work.FTS_RegExport.RXT.L12Iter.Rwt
local notation "Dth" => Work.Spaces.Dth
local notation "L12" => Work.Construction.L12

/-- `(z,θ) ↦ 3·D_θ F(z,θ)/(1+z)` is continuous on the open quadrant as soon as `F` is `C⁴`
there: `D_θ F` is `C³` and the radial factor `3/(1+z)` is smooth and nonvanishing on `z > 0`. -/
theorem continuousOn_uncurry_three_div_Dth {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry (fun z θ => 3 * Dth F z θ / (1 + z)))
      Work.FTS.EllipticEst.Q0 := by
  have h3 : ContDiffOn ℝ 3 (Function.uncurry (Dth F)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dth_fin (n := 3) Work.FTS.EllipticEst.isOpen_Q0 hF
  have hfac : ContinuousOn (fun p : ℝ × ℝ => 3 / (1 + p.1)) Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.div continuousOn_const
      (continuousOn_const.add continuous_fst.continuousOn) ?_
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    positivity
  have hmul : ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (1 + p.1)) * Function.uncurry (Dth F) p) Work.FTS.EllipticEst.Q0 :=
    hfac.mul h3.continuousOn
  refine hmul.congr (fun p hp => ?_)
  simp only [Function.uncurry]
  ring

/-- **The assembly.**  Given the pointwise inputs `hsub` (linearity of `L₁₂` in the profile) and
`hbnd` (bound and `τ`-modulus of `D_θ(slice g ·)`), the transport zero-mode of the family `g` is
uniformly bounded and Lipschitz in the fake time on `[0,S]`. -/
theorem Tlim_bounds_from_aux {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ}
    (hsub : ∀ {a b : ℝ → ℝ → ℝ} {A B : ℝ}, 0 ≤ A → 0 ≤ B →
      ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0 →
      ContinuousOn (Function.uncurry b) Work.FTS.EllipticEst.Q0 →
      (∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |a s θ| ≤ A * (Rwt s / (1 + s))) →
      (∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |b s θ| ≤ B * (Rwt s / (1 + s))) →
      L12 a 0 - L12 b 0 = L12 (fun z θ => a z θ - b z θ) 0)
    (hbnd : ∃ C1 : ℝ, 0 ≤ C1 ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
        |Dth (Work.FTS.Galerkin.slice g τ) z θ| ≤ C1 * Rwt z) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S, ∀ z θ : ℝ, 0 < z →
        θ ∈ Work.Spaces.Iθ →
        |Dth (Work.FTS.Galerkin.slice g τ) z θ - Dth (Work.FTS.Galerkin.slice g τ') z θ|
          ≤ C1 * Rwt z * |τ - τ'|)) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ τ ∈ Set.Icc (0:ℝ) S,
        |L12 (fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0| ≤ M) ∧
      (∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |L12 (fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0
          - L12 (fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ') z θ / (1 + z)) 0|
          ≤ M * |τ - τ'|) := by
  obtain ⟨hDyn, _hLim⟩ := hOK
  obtain ⟨C1, hC1, hbd, hlip⟩ := hbnd
  -- the data `3·D_θ(slice g τ)/(1+z)` are continuous on the open quadrant
  have hcont : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      ContinuousOn (Function.uncurry
        (fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)))
        Work.FTS.EllipticEst.Q0 := fun τ hτ =>
    continuousOn_uncurry_three_div_Dth (hDyn.1.c4 τ hτ.1)
  -- ## the two pointwise bounds for the data
  -- (a) on the closed angular interval, in the form required by `abs_L12_zero_le_of_pointwise`
  have hbddI : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)| ≤ (3 * C1) * Rwt z := by
    intro τ hτ z θ hz hθ
    have h1 := hbd τ hτ z θ hz hθ
    have hR : 0 ≤ Rwt z := Work.FTS_RegExport.RXT.L12Iter.Rwt_nonneg hz.le
    have hz1 : (0 : ℝ) < 1 + z := by linarith
    have h2 : |3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)|
        = 3 * |Dth (Work.FTS.Galerkin.slice g τ) z θ| / (1 + z) := by
      rw [abs_div, abs_mul, abs_of_pos hz1, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    rw [h2]
    have hA : 0 ≤ 3 * (C1 * Rwt z) := mul_nonneg (by norm_num) (mul_nonneg hC1 hR)
    calc 3 * |Dth (Work.FTS.Galerkin.slice g τ) z θ| / (1 + z)
        ≤ 3 * (C1 * Rwt z) / (1 + z) := by gcongr
      _ ≤ 3 * (C1 * Rwt z) := by
          rw [div_le_iff₀ hz1]
          nlinarith [mul_nonneg hA hz.le]
      _ = (3 * C1) * Rwt z := by ring
  -- (b) on the open angular interval, in the form required by `hsub`
  have hbdd : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ s θ : ℝ, 0 < s →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |3 * Dth (Work.FTS.Galerkin.slice g τ) s θ / (1 + s)|
        ≤ (3 * C1) * (Rwt s / (1 + s)) := by
    intro τ hτ s θ hs hθ
    have h1 := hbd τ hτ s θ hs ⟨hθ.1.le, hθ.2.le⟩
    have hs1 : (0 : ℝ) < 1 + s := by linarith
    have h2 : |3 * Dth (Work.FTS.Galerkin.slice g τ) s θ / (1 + s)|
        = 3 * |Dth (Work.FTS.Galerkin.slice g τ) s θ| / (1 + s) := by
      rw [abs_div, abs_mul, abs_of_pos hs1, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    rw [h2]
    calc 3 * |Dth (Work.FTS.Galerkin.slice g τ) s θ| / (1 + s)
        ≤ 3 * (C1 * Rwt s) / (1 + s) := by gcongr
      _ = (3 * C1) * (Rwt s / (1 + s)) := by ring
  refine ⟨3 * Real.pi * (3 * C1), by positivity, ?_, ?_⟩
  · -- ## the uniform bound
    intro τ hτ
    have hM0 : (0 : ℝ) ≤ 3 * C1 := by linarith
    have hb := Work.FTS_RegExport.RXR5L.aux.abs_L12_zero_le_of_pointwise
      (f := fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z))
      (M := 3 * C1) hM0 (hbddI τ hτ)
    refine le_trans hb (le_of_eq ?_)
    ring
  · -- ## the `τ`-modulus
    intro τ hτ τ' hτ'
    have hM0 : (0 : ℝ) ≤ 3 * C1 := by linarith
    have hsub' := hsub
      (a := fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z))
      (b := fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ') z θ / (1 + z))
      (A := 3 * C1) (B := 3 * C1) hM0 hM0 (hcont τ hτ) (hcont τ' hτ')
      (hbdd τ hτ) (hbdd τ' hτ')
    rw [hsub']
    have hb := Work.FTS_RegExport.RXR5L.aux.abs_L12_zero_le_of_pointwise
      (f := fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)
        - 3 * Dth (Work.FTS.Galerkin.slice g τ') z θ / (1 + z))
      (M := 3 * C1 * |τ - τ'|) (by positivity) ?_
    · refine le_trans hb (le_of_eq ?_)
      ring
    · intro z θ hz hθ
      have hR : 0 ≤ Rwt z := Work.FTS_RegExport.RXT.L12Iter.Rwt_nonneg hz.le
      have hz1 : (0 : ℝ) < 1 + z := by linarith
      have h2 : |3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)
            - 3 * Dth (Work.FTS.Galerkin.slice g τ') z θ / (1 + z)|
          = 3 * |Dth (Work.FTS.Galerkin.slice g τ) z θ
              - Dth (Work.FTS.Galerkin.slice g τ') z θ| / (1 + z) := by
        rw [show 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)
              - 3 * Dth (Work.FTS.Galerkin.slice g τ') z θ / (1 + z)
            = 3 * (Dth (Work.FTS.Galerkin.slice g τ) z θ
              - Dth (Work.FTS.Galerkin.slice g τ') z θ) / (1 + z) from by ring]
        rw [abs_div, abs_mul, abs_of_pos hz1, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      rw [h2]
      have hd := hlip τ hτ τ' hτ' z θ hz hθ
      have hA : 0 ≤ C1 * Rwt z * |τ - τ'| :=
        mul_nonneg (mul_nonneg hC1 hR) (abs_nonneg _)
      have hB : 0 ≤ 3 * (C1 * Rwt z * |τ - τ'|) := mul_nonneg (by norm_num) hA
      rw [div_le_iff₀ hz1]
      calc 3 * |Dth (Work.FTS.Galerkin.slice g τ) z θ
              - Dth (Work.FTS.Galerkin.slice g τ') z θ|
          ≤ 3 * (C1 * Rwt z * |τ - τ'|) := by linarith
        _ ≤ 3 * (C1 * Rwt z * |τ - τ'|) * (1 + z) := by
            nlinarith [mul_nonneg hB hz.le]
        _ = (3 * C1 * |τ - τ'|) * Rwt z * (1 + z) := by ring

end Work.FTS_RegExport.RXR5L.Auxiliary
