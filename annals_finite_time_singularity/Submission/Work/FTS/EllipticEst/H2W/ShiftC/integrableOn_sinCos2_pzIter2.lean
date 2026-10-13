import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W/ShiftC/integrableOn_sinCos2_pzIter2`

Box integrability of `sinθcos²θ·|∂_z²Ψ|` from the box integrability of the *difference*
`sinθcos²θ·|Lzero Ψ − F|` and of `sinθcos²θ·|∂_zΨ|`, granted the equation `bslOp α Ψ = F` on the
open quadrant.

The whole content is the *level identity* (`Lzero_eq_bslOp_add_radial_pz2`)

  `Lzero Ψ = F + α²z²∂_z²Ψ + α(5+α)z ∂_zΨ`   on `(0,∞) × (0,π/2)`,

which on a box `[a,b] × Iθ` with `0 < a < b` gives the pointwise bound

  `|∂_z²Ψ(s,θ)| ≤ (|Lzero Ψ − F| + α(5+α)·b·|∂_zΨ(s,θ)|) / (α²·a²)`,

so that after multiplication by the nonnegative weight `sinθcos²θ` the target integrand is
dominated by a constant multiple of the sum of the two integrable integrands.  The a.e. strong
measurability of the target comes from the `C^∞`-smoothness of `Ψ` on the open quadrant
(`SmoothOpen`), the level identity holding a.e. on the box (the exceptional set being contained in
the two null lines `θ = 0`, `θ = π/2`).

Every declaration in this file is fully proved and rests only on the axioms
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.EllipticEst.H2W.ShiftC

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## The elementary angular fact -/

/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
theorem sinCos2_nonneg_Iθ_pz2 {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [h1, Real.pi_pos]))
    (sq_nonneg _)

/-! ## The level identity on the open quadrant, and almost everywhere on a box -/

/-- **The level identity.**  On the open quadrant the equation `bslOp α Ψ = F` is exactly

  `Lzero Ψ = F + α²z²∂_z²Ψ + α(5+α)z ∂_zΨ`.

This is pure algebra from `bslOp_apply` (no derivative is taken). -/
theorem Lzero_eq_bslOp_add_radial_pz2 {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Elliptic.Lzero Ψ z θ
      = F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        + α * (5 + α) * z * Work.Spaces.pz Ψ z θ := by
  have h := hEq z hz θ hθ0 hθ1
  rw [Work.Elliptic.bslOp_apply] at h
  linarith [h]

/-- **The level identity almost everywhere on a box**: on `[a,b] ×ˢ Iθ` with `0 < a` the set where
`Lzero Ψ = F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ` can fail is contained in the two null lines
`θ = 0`, `θ = π/2`. -/
theorem ae_Lzero_eq_add_radial_pz2 {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {a b : ℝ} (ha : 0 < a) :
    ∀ᵐ q ∂(volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)),
      Work.Elliptic.Lzero Ψ q.1 q.2
        = F q.1 q.2
          + (α ^ 2 * q.1 ^ 2 * Work.Spaces.pzIter 2 Ψ q.1 q.2
              + α * (5 + α) * q.1 * Work.Spaces.pz Ψ q.1 q.2) := by
  have hθae : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  have hboxae : (Set.Icc a b ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[volume]
      (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) hθae
  rw [MeasureTheory.Measure.restrict_congr_set hboxae]
  rw [MeasureTheory.ae_restrict_iff' (measurableSet_Icc.prod isOpen_Ioo.measurableSet)]
  refine Filter.Eventually.of_forall fun q hq => ?_
  obtain ⟨hq1, hq2⟩ := hq
  have h := Lzero_eq_bslOp_add_radial_pz2 (α := α) (F := F) hEq
    (lt_of_lt_of_le ha hq1.1) hq2.1 hq2.2
  rw [h]
  ring

/-! ## A.e. strong measurability on a box of a function continuous on the open quadrant -/

/-- A.e. strong measurability on a fixed box of a function continuous on the open quadrant.
The product measure on the box is the restriction of the planar Lebesgue measure, and the box
differs from the open quadrant by sets contained in the coordinate hyperplanes and the two
boundary lines `θ = 0`, `θ = π/2`. -/
theorem aesm_of_continuousOn_Qd_box_pz2 {g : ℝ × ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (ha : 0 < a) :
    AEStronglyMeasurable g (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) := by
  have h : AEStronglyMeasurable g
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  rw [show volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ) from
    (MeasureTheory.Measure.prod_restrict (Set.Icc a b) Work.Spaces.Iθ).symm]
  exact h.mono_measure (Measure.prod_mono
    (Measure.restrict_mono (fun x hx => le_trans (le_of_lt ha) hx.1) le_rfl) le_rfl)

/-! ## The main theorem -/

theorem integrableOn_sinCos2_pzIter2 {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hG : MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        Work.Elliptic.sinCos2 θ * |Work.Elliptic.Lzero Ψ s θ - F s θ|))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hPz : MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        Work.Elliptic.sinCos2 θ * |Work.Spaces.pz Ψ s θ|)) (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter 2 Ψ s θ|))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  have hα2 : (0 : ℝ) < α ^ 2 := pow_pos hα 2
  have h55 : (0 : ℝ) < α * (5 + α) := by nlinarith [hα]
  -- Continuity of the target integrand on the open quadrant.
  have hcont : ContinuousOn (Function.uncurry (fun s θ : ℝ =>
      Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter 2 Ψ s θ|))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_sin.comp continuous_snd).mul
        ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
    have hinner : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 Ψ p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hsm.pzIter 2).continuousOn
    have hfun : Function.uncurry (fun s θ : ℝ =>
        Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter 2 Ψ s θ|)
        = (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
          * (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2|) := by
      funext p
      rcases p with ⟨z, θ⟩
      simp only [Function.uncurry_apply_pair, Work.Elliptic.sinCos2, Pi.mul_apply]
    rw [hfun]
    exact hsin.mul hinner.abs
  rw [MeasureTheory.IntegrableOn] at hG hPz ⊢
  -- The integrable majorant: a constant multiple of the sum of the two integrable integrands.
  have hconst : (0 : ℝ) < α ^ 2 * a ^ 2 := mul_pos hα2 (pow_pos ha 2)
  have hmaj : Integrable (fun p : ℝ × ℝ => (1 / (α ^ 2 * a ^ 2)) *
      (Function.uncurry (fun s θ : ℝ => Work.Elliptic.sinCos2 θ *
          |Work.Elliptic.Lzero Ψ s θ - F s θ|) p
       + (α * (5 + α) * b) * Function.uncurry (fun s θ : ℝ => Work.Elliptic.sinCos2 θ *
          |Work.Spaces.pz Ψ s θ|) p))
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    (hG.add (hPz.const_mul (α * (5 + α) * b))).const_mul (1 / (α ^ 2 * a ^ 2))
  refine Integrable.mono' hmaj (aesm_of_continuousOn_Qd_box_pz2 hcont ha) ?_
  filter_upwards [ae_Lzero_eq_add_radial_pz2 (α := α) (F := F) hEq ha,
    ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hid hp
  obtain ⟨hp1, hp2⟩ := hp
  have hp1pos : 0 < p.1 := lt_of_lt_of_le ha hp1.1
  have hWnn : 0 ≤ Work.Elliptic.sinCos2 p.2 := sinCos2_nonneg_Iθ_pz2 hp2
  have hcoef_nn : 0 ≤ α * (5 + α) * p.1 := le_of_lt (mul_pos h55 hp1pos)
  -- The pointwise bound coming from the level identity.
  have hkey : |Work.Spaces.pzIter 2 Ψ p.1 p.2| * (α ^ 2 * a ^ 2)
      ≤ |Work.Elliptic.Lzero Ψ p.1 p.2 - F p.1 p.2|
        + (α * (5 + α) * b) * |Work.Spaces.pz Ψ p.1 p.2| := by
    have hs2 : a ^ 2 ≤ p.1 ^ 2 := pow_le_pow_left₀ (le_of_lt ha) hp1.1 2
    have h1 : |Work.Spaces.pzIter 2 Ψ p.1 p.2| * (α ^ 2 * a ^ 2)
        ≤ |Work.Spaces.pzIter 2 Ψ p.1 p.2| * (α ^ 2 * p.1 ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs2 (pow_nonneg hα.le 2))
        (abs_nonneg _)
    have h2 : |Work.Spaces.pzIter 2 Ψ p.1 p.2| * (α ^ 2 * p.1 ^ 2)
        = |α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (pow_nonneg hα.le 2) (sq_nonneg p.1))]
      ring
    have heq : α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2
        = (Work.Elliptic.Lzero Ψ p.1 p.2 - F p.1 p.2)
          - α * (5 + α) * p.1 * Work.Spaces.pz Ψ p.1 p.2 := by
      rw [hid]
      ring
    have h3 : |α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2|
        ≤ |Work.Elliptic.Lzero Ψ p.1 p.2 - F p.1 p.2|
          + (α * (5 + α) * b) * |Work.Spaces.pz Ψ p.1 p.2| := by
      have hle : α * (5 + α) * p.1 ≤ α * (5 + α) * b :=
        mul_le_mul_of_nonneg_left hp1.2 (le_of_lt h55)
      calc |α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2|
          = |(Work.Elliptic.Lzero Ψ p.1 p.2 - F p.1 p.2)
              - α * (5 + α) * p.1 * Work.Spaces.pz Ψ p.1 p.2| := by rw [heq]
        _ ≤ |Work.Elliptic.Lzero Ψ p.1 p.2 - F p.1 p.2|
              + |α * (5 + α) * p.1 * Work.Spaces.pz Ψ p.1 p.2| := abs_sub _ _
        _ = |Work.Elliptic.Lzero Ψ p.1 p.2 - F p.1 p.2|
              + (α * (5 + α) * p.1) * |Work.Spaces.pz Ψ p.1 p.2| := by
            rw [abs_mul, abs_of_nonneg hcoef_nn]
        _ ≤ |Work.Elliptic.Lzero Ψ p.1 p.2 - F p.1 p.2|
              + (α * (5 + α) * b) * |Work.Spaces.pz Ψ p.1 p.2| :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hle (abs_nonneg _))
    exact le_trans h1 (le_trans (le_of_eq h2) h3)
  have hmain : |Work.Spaces.pzIter 2 Ψ p.1 p.2|
      ≤ (|Work.Elliptic.Lzero Ψ p.1 p.2 - F p.1 p.2|
          + (α * (5 + α) * b) * |Work.Spaces.pz Ψ p.1 p.2|) / (α ^ 2 * a ^ 2) := by
    rw [le_div_iff₀ hconst]
    exact hkey
  rw [Real.norm_eq_abs]
  change abs (Work.Elliptic.sinCos2 p.2 * abs (Work.Spaces.pzIter 2 Ψ p.1 p.2))
      ≤ (1 / (α ^ 2 * a ^ 2)) *
        (Work.Elliptic.sinCos2 p.2 * abs (Work.Elliptic.Lzero Ψ p.1 p.2 - F p.1 p.2)
          + (α * (5 + α) * b) * (Work.Elliptic.sinCos2 p.2 * abs (Work.Spaces.pz Ψ p.1 p.2)))
  rw [abs_of_nonneg (mul_nonneg hWnn (abs_nonneg _))]
  calc Work.Elliptic.sinCos2 p.2 * |Work.Spaces.pzIter 2 Ψ p.1 p.2|
      ≤ Work.Elliptic.sinCos2 p.2 *
          ((|Work.Elliptic.Lzero Ψ p.1 p.2 - F p.1 p.2|
            + (α * (5 + α) * b) * |Work.Spaces.pz Ψ p.1 p.2|) / (α ^ 2 * a ^ 2)) :=
        mul_le_mul_of_nonneg_left hmain hWnn
    _ = (1 / (α ^ 2 * a ^ 2)) *
          (Work.Elliptic.sinCos2 p.2 * |Work.Elliptic.Lzero Ψ p.1 p.2 - F p.1 p.2|
            + (α * (5 + α) * b) * (Work.Elliptic.sinCos2 p.2 * |Work.Spaces.pz Ψ p.1 p.2|)) := by
        ring

end

end Work.FTS.EllipticEst.H2W.ShiftC
