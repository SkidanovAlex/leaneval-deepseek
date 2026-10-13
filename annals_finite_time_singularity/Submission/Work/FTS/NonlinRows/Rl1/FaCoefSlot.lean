/-
# `FaCoefSlot` — the `rl¹`-engine for an *energetic* coefficient

The primed `rl1`-rows whose coefficient is only an `HQo`-function of a package
(`Work.FTS.VocabO.EllPkgGo`'s `ℛ(Φ̃_g)`, `𝒰(Φ̃_g)/sin 2θ`, `𝒱(Φ̃_g)`) cannot be priced by a
pointwise bound (none is available in the primed interface).  The replacement is the
*angular Agmon bound* `angSupHk`: for `A ∈ HQo α 4` and `z > 0`, `θ ∈ (0,π/2)`

  `A z θ² ≤ C_A/(γ-1) · Ψ_A z`,   `Ψ_A z := ∫_θ HkIntegrand α 4 A z θ`,

i.e. a pointwise bound whose *majorant depends on the radius*.  This file performs the
resulting two-step estimate of the `L₁₂`-density functional

  `Fa N = ∫⁻_r r⁻¹ · ∫⁻_θ |K θ · N r θ|`

for a pointwise factorisation `|K θ · N r θ| ≤ |A r θ| · |B r θ|`, with

* `(A r θ)² ≤ C · Ψ r` almost everywhere in `θ` (`∫ Ψ ≤ Ys`), and
* `∫⁻_θ ofReal (B r θ²) ≤ ofReal (Φ r)`, with `∫ r⁻² Φ r ≤ Zs`,

namely `Fa N ≤ ofReal (√C · √(π/2) · √Ys · √Zs)`.

The two Cauchy–Schwarz steps are: in `θ`, `∫_θ |A||B| ≤ √(CΨ r)·√(π/2)·(∫_θ B²)^{1/2}`
(`lintegral_abs_le_sqrt`), and in `r`, `∫_r r⁻¹ √(Ψ r) √(Φ r) ≤ √(∫Ψ)·√(∫ r⁻²Φ)`
(`outer_gen`); the latter is the reason the hypothesis on `Φ` carries the weight
`r⁻² ≤ w(r)`, which is what makes the slot energies of `ℋ⁴` usable
(`Work.FTS.NonlinRows.Rl1.SlotData.lew`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.FaStep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.Rl1

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `rl¹`-engine with an energetic coefficient.**

Let `N` obey `|K θ · N r θ| ≤ |A r θ| · |B r θ|` on the open quadrant, let `A` be bounded in
`L²(θ)` by `√(C Ψ r)` at every radius and let `B` have angular energy at most `Φ r`
(`∫⁻_θ ofReal (B r θ²) ≤ ofReal (Φ r)`).  Then

  `Fa N ≤ ofReal (√C · √(π/2) · √(∫Ψ) · √(∫ r⁻²Φ))`.

The two square roots of the right-hand side are the `θ`- and `r`-Cauchy–Schwarz losses. -/
theorem Fa_le_coef_slot {N A B : Fn} {C Ys Zs : ℝ} {Ψ Φ : ℝ → ℝ}
    (hC : 0 ≤ C) (hYs : 0 ≤ Ys) (hZs : 0 ≤ Zs)
    (hΨnn : ∀ r, 0 ≤ Ψ r)
    (hΨmeas : AEMeasurable Ψ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΨint : MeasureTheory.IntegrableOn Ψ (Set.Ioi (0 : ℝ)))
    (hΨle : (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Ys)
    (hΦnn : ∀ r, 0 ≤ Φ r)
    (hΦmeas : AEMeasurable Φ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΦint : MeasureTheory.IntegrableOn (fun r => (r⁻¹) ^ 2 * Φ r) (Set.Ioi (0 : ℝ)))
    (hΦle : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹) ^ 2 * Φ r) ≤ Zs)
    (hAmeas : ∀ r, 0 < r → MeasureTheory.AEStronglyMeasurable (fun θ => A r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hBmeas : ∀ r, 0 < r → MeasureTheory.AEStronglyMeasurable (fun θ => B r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hBsq : ∀ r, 0 < r → MeasureTheory.IntegrableOn (fun θ => (B r θ) ^ 2)
      Work.Spaces.Iθ)
    (hAb : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (A r θ) ^ 2 ≤ C * Ψ r)
    (hB : ∀ r, 0 < r → (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2))
      ≤ ENNReal.ofReal (Φ r))
    (hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * N r θ| ≤ |A r θ| * |B r θ|) :
    Fa N ≤ ENNReal.ofReal (Real.sqrt C * Real.sqrt (Real.pi / 2) * Real.sqrt Ys
      * Real.sqrt Zs) := by
  -- ## Step 1: the `θ`-bound at a fixed radius `r > 0`
  have hinner : ∀ r, 0 < r →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (Real.sqrt (C * Ψ r) * Real.sqrt (Real.pi / 2) * Real.sqrt (Φ r)) := by
    intro r hr
    have hCΨ : 0 ≤ C * Ψ r := mul_nonneg hC (hΨnn r)
    have hsCΨ : 0 ≤ Real.sqrt (C * Ψ r) := Real.sqrt_nonneg _
    -- the pointwise a.e. domination by `√(CΨ r)·|B|`
    have hdom : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal |Work.Spaces.K θ * N r θ|
          ≤ ENNReal.ofReal (Real.sqrt (C * Ψ r)) * ENNReal.ofReal |B r θ| := by
      filter_upwards [hAb r hr,
        Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
          (p := fun θ => θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (fun θ hθ => hθ)] with θ hAθ hθ
      have hAabs : |A r θ| ≤ Real.sqrt (C * Ψ r) := Real.abs_le_sqrt hAθ
      have h1 : |Work.Spaces.K θ * N r θ| ≤ Real.sqrt (C * Ψ r) * |B r θ| :=
        (hpt r hr θ hθ).trans (mul_le_mul_of_nonneg_right hAabs (abs_nonneg _))
      rw [← ENNReal.ofReal_mul hsCΨ]
      exact ENNReal.ofReal_le_ofReal h1
    have hstep1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (Real.sqrt (C * Ψ r))
          * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ| :=
      (MeasureTheory.lintegral_mono_ae hdom).trans_eq
        (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
    -- the `B`-slot bound
    have hsqrtB : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ|)
        ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2)) * ENNReal.ofReal (Real.sqrt (Φ r)) := by
      have h1 := lintegral_abs_le_sqrt (B := B) (r := r) (hBmeas r hr) (hBsq r hr)
      have h2 : ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2)
          = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2) :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hBsq r hr)
          (Eventually.of_forall fun θ => sq_nonneg (B r θ))
      have h4 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2) ≤ Real.sqrt (Φ r) :=
        Real.sqrt_le_sqrt
          ((ENNReal.ofReal_le_ofReal_iff (hΦnn r)).mp (h2 ▸ hB r hr))
      calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ|)
          ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2) ^ (1 / 2 : ℝ) := h1
        _ = ENNReal.ofReal (Real.sqrt (Real.pi / 2))
              * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2)) := by
            rw [ofReal_rpow_half (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
        _ ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2)) * ENNReal.ofReal (Real.sqrt (Φ r)) :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal h4) _
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (Real.sqrt (C * Ψ r))
            * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ| := hstep1
      _ ≤ ENNReal.ofReal (Real.sqrt (C * Ψ r))
            * (ENNReal.ofReal (Real.sqrt (Real.pi / 2)) * ENNReal.ofReal (Real.sqrt (Φ r))) :=
          mul_le_mul_right hsqrtB _
      _ = ENNReal.ofReal (Real.sqrt (C * Ψ r) * Real.sqrt (Real.pi / 2)
            * Real.sqrt (Φ r)) := by
          rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg (Real.pi / 2)),
            ← ENNReal.ofReal_mul (Real.sqrt_nonneg (C * Ψ r))]
          ring_nf
  -- ## Step 2: the radial Cauchy–Schwarz
  set θw : ℝ → ℝ := fun r => |r⁻¹| * Real.sqrt (Φ r) with hθwdef
  set M : ℝ → ℝ := fun r => Real.sqrt (C * Ψ r) with hMdef
  have hθwnn : ∀ r, 0 ≤ θw r :=
    fun r => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hMnn : ∀ r, 0 ≤ M r := fun r => Real.sqrt_nonneg _
  have hθwmeas : AEMeasurable θw (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : AEMeasurable (fun r : ℝ => |r⁻¹|)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (measurable_inv.abs).aemeasurable
    have h2 : AEMeasurable (fun r : ℝ => Real.sqrt (Φ r))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Real.continuous_sqrt.measurable.comp_aemeasurable hΦmeas
    exact h1.mul h2
  have hθwint : MeasureTheory.IntegrableOn (fun r => (θw r) ^ 2) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.congr_fun hΦint
      (fun r _ => by
        rw [hθwdef, mul_pow, sq_abs, Real.sq_sqrt (hΦnn r)]) measurableSet_Ioi
  have hMle : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), (M r) ^ 2 ≤ C * Ψ r :=
    Eventually.of_forall fun r => le_of_eq (Real.sq_sqrt (mul_nonneg hC (hΨnn r)))
  have houter := outer_gen (C := C) hC hθwnn hMnn hΨnn hθwmeas hΨmeas hθwint hΨint hMle
  have hθwval : ∀ r, 0 < r → θw r = r⁻¹ * Real.sqrt (Φ r) := by
    intro r hr
    show |r⁻¹| * Real.sqrt (Φ r) = r⁻¹ * Real.sqrt (Φ r)
    rw [abs_of_pos (inv_pos.mpr hr)]
  have hθw2le : (∫ r in Set.Ioi (0 : ℝ), (θw r) ^ 2) ≤ Zs := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), (θw r) ^ 2)
        = ∫ r in Set.Ioi (0 : ℝ), (r⁻¹) ^ 2 * Φ r :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r hr => by
        rw [hθwval r hr, mul_pow, Real.sq_sqrt (hΦnn r)])
    rw [h1]
    exact hΦle
  have hΨY : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Real.sqrt Ys :=
    Real.sqrt_le_sqrt hΨle
  rw [Fa]
  have hBigA : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.sqrt (Real.pi / 2))
          * (ENNReal.ofReal (θw r) * ENNReal.ofReal (M r)) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
    have hkey : ENNReal.ofReal r⁻¹
        * ENNReal.ofReal (Real.sqrt (C * Ψ r) * Real.sqrt (Real.pi / 2) * Real.sqrt (Φ r))
        = ENNReal.ofReal (Real.sqrt (Real.pi / 2))
          * (ENNReal.ofReal (θw r) * ENNReal.ofReal (M r)) := by
      have hA : 0 ≤ Real.sqrt (C * Ψ r) := Real.sqrt_nonneg _
      have hB0 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
      have hC0 : 0 ≤ Real.sqrt (Φ r) := Real.sqrt_nonneg _
      rw [hθwval r hr0, hMdef]
      rw [show ENNReal.ofReal (Real.sqrt (C * Ψ r) * Real.sqrt (Real.pi / 2)
              * Real.sqrt (Φ r))
            = ENNReal.ofReal (Real.sqrt (C * Ψ r)) * ENNReal.ofReal (Real.sqrt (Real.pi / 2))
              * ENNReal.ofReal (Real.sqrt (Φ r)) from by
          rw [ENNReal.ofReal_mul (mul_nonneg hA hB0), ENNReal.ofReal_mul hA],
        show ENNReal.ofReal (r⁻¹ * Real.sqrt (Φ r))
            = ENNReal.ofReal r⁻¹ * ENNReal.ofReal (Real.sqrt (Φ r)) from
          ENNReal.ofReal_mul hinv]
      ring
    exact (mul_le_mul_right (hinner r hr0) _).trans_eq hkey
  have hBigB : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.sqrt (Real.pi / 2))
        * (ENNReal.ofReal (θw r) * ENNReal.ofReal (M r)))
      ≤ ENNReal.ofReal (Real.sqrt C * Real.sqrt (Real.pi / 2) * Real.sqrt Ys
          * Real.sqrt Zs) := by
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [show ENNReal.ofReal (Real.sqrt C * Real.sqrt (Real.pi / 2) * Real.sqrt Ys
          * Real.sqrt Zs)
        = ENNReal.ofReal (Real.sqrt (Real.pi / 2))
          * ENNReal.ofReal (Real.sqrt C * Real.sqrt Ys * Real.sqrt Zs) from by
      rw [show (Real.sqrt C * Real.sqrt (Real.pi / 2) * Real.sqrt Ys * Real.sqrt Zs : ℝ)
            = Real.sqrt (Real.pi / 2) * (Real.sqrt C * Real.sqrt Ys * Real.sqrt Zs) from by
          ring,
        ENNReal.ofReal_mul (Real.sqrt_nonneg (Real.pi / 2))]]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine houter.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hΨY (Real.sqrt_nonneg C))
      (Real.sqrt_le_sqrt hθw2le) (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg C) (Real.sqrt_nonneg _))
  exact hBigA.trans hBigB

end Work.FTS.NonlinRows.Rl1
