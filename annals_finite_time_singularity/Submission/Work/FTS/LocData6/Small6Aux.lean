/-
# `Work.FTS.LocData6.Small6Aux` — the order-`6` smallness chain, conditional on the two `ℋ⁶`
inputs of the far part

This module contains, in the *generic* bump form of `Work.FTS.LocData.locData_small_general`
(general `h` rather than `hLoc α`), the order-`6` analogue of the numerical smallness of the
localised datum:

* `HkMem_h_of_majorant6` — membership in `ℋ⁶` by domination (the order-`6` instance of
  `LocData.HkMem_h_of_majorant`);
* `HkNorm_locG_le_gen6` — `HkNorm α 6 (locG α L β h) ≤ √(2C₀α/L) + √2·|β|·√C₁` (the order-`6`
  instance of `LocData.HkNorm_locG_le_gen`, with `C₀` bounding `L·HkSq α 6 (zfar L F_*)` and
  `C₁` bounding `HkSq α 6 h`);
* `locData6_small_aux` — **for every `ε > 0` there is `L₀` such that for every `L ≥ L₀` there is
  `β` with `|β| ≤ ε`, `L₁₂(locG α L β h)(0) = 0` and `HkNorm α 6 (locG α L β h) ≤ ε`.

The two facts about the far part `zfar L F_*` that the argument needs are carried as explicit
hypotheses (`hZT` = `ℋ⁶`-membership, `hC₀` = the `α/L`-decay of `HkSq α 6`); they are discharged
in the assembly of this chapter from the order-`6` radial jet bounds of the profile (orders `4`,
`5`) and of the cut-off.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData6.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Membership in `ℋ⁶` by domination -/

/-- **Membership in `ℋ⁶` by domination**: if the `ℋ⁶`-integrand of `h` is continuous on the open
quadrant and dominated by the integrable majorant `K·angMaj α θ/(1+z)²`, then `h ∈ ℋ⁶`. -/
theorem HkMem_h_of_majorant6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ} {K : ℝ}
    (hsh : Work.FTS.LocData.SmoothQuad h)
    (hK : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 h z θ ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) :
    Work.Spaces.HkMem α 6 h := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 h p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 6 _ hsh
  refine Work.FTS.LocData.HkMem_of_majorant (f := h)
    (M := fun z θ => K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) α 6 hcont ?_ ?_ ?_
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).1
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).2
  · intro z hz θ hθ
    exact hK z hz θ hθ

/-! ## The `ℋ⁶`-norm of `locG α L β h` -/

/-- **The order-`6` `ℋ⁶`-bound on the localised perturbation**, for an arbitrary bump `h`: if
`C₀` bounds `L·HkSq α 6 (zfar L F_*)` and `C₁` bounds `HkSq α 6 h`, then

  `HkNorm α 6 (locG α L β h) ≤ √(2C₀α/L) + √2·|β|·√C₁`.

This is the order-`6` instance of `Work.FTS.LocData.HkNorm_locG_le_gen`. -/
theorem HkNorm_locG_le_gen6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ}
    {L β C₀ C₁ : ℝ} (hL : 1 ≤ L) (hsh : Work.FTS.LocData.SmoothQuad h)
    (hC₀nn : 0 ≤ C₀) (hC₁nn : 0 ≤ C₁)
    (hmemT : Work.Spaces.HkMem α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)))
    (hmemH : Work.Spaces.HkMem α 6 h)
    (hC₀ : Work.Spaces.HkSq α 6 (Work.Stability.zfar L (Work.Construction.Fstar α))
      ≤ C₀ * α / L)
    (hC₁ : Work.Spaces.HkSq α 6 h ≤ C₁) :
    Work.Spaces.HkNorm α 6 (Work.FTS.LocData.locG α L β h)
      ≤ Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt 2 * |β| * Real.sqrt C₁ := by
  have hmeqb : Work.Spaces.HkMem α 6 (fun z θ => β * h z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 β hmemH
  have hsq : Work.Spaces.HkSq α 6 (Work.FTS.LocData.locG α L β h)
      ≤ 2 * (C₀ * α / L) + 2 * β ^ 2 * C₁ := by
    have hxy : Work.FTS.LocData.locG α L β h
        = fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ + β * h z θ := by
      funext z θ
      exact Work.FTS.LocData.locG_eq_zfar α L β h z θ
    rw [hxy]
    have hAB := Work.FTS.LocData.HkSq_add_le (α := α) (k := 6)
      (a := fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
      (b := fun z θ => β * h z θ)
      (Work.FTS.LocData.smoothQuad_neg (Work.FTS.LocData.SmoothQuad_zfar_Fstar α L))
      (Work.FTS.LocData.smoothQuad_const_mul β hsh)
      (Work.FTS.LocData.HkMem_neg α 6 hmemT) hmeqb
    have h1 : Work.Spaces.HkSq α 6
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
        = Work.Spaces.HkSq α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) :=
      Work.FTS.LocData.HkSq_neg α 6 _
    have h2 : Work.Spaces.HkSq α 6 (fun z θ => β * h z θ) = β ^ 2 * Work.Spaces.HkSq α 6 h :=
      Work.FTS.LocData.HkSq_const_mul α 6 β hmemH
    have hb : 2 * (β ^ 2 * Work.Spaces.HkSq α 6 h) ≤ 2 * β ^ 2 * C₁ := by
      nlinarith [sq_nonneg β, hC₁]
    linarith [hAB, h1.le, h1.ge, h2.le, h2.ge, hC₀, hb]
  have hmono : Real.sqrt (Work.Spaces.HkSq α 6 (Work.FTS.LocData.locG α L β h))
      ≤ Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁) := Real.sqrt_le_sqrt hsq
  have hLpos : 0 < L := by linarith
  have h2C₀ : (0 : ℝ) ≤ 2 * (C₀ * α / L) := by
    have : 0 ≤ C₀ * α / L := div_nonneg (mul_nonneg hC₀nn hα.le) hLpos.le
    linarith
  have h2C₁ : (0 : ℝ) ≤ 2 * β ^ 2 * C₁ := by
    have : 0 ≤ β ^ 2 * C₁ := mul_nonneg (sq_nonneg β) hC₁nn
    linarith
  have hsplit : Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁)
      ≤ Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁) := by
    have h1 : 2 * (C₀ * α / L) + 2 * β ^ 2 * C₁
        ≤ (Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁)) ^ 2 := by
      have ha := Real.sq_sqrt h2C₀
      have hb := Real.sq_sqrt h2C₁
      have ha' := Real.sqrt_nonneg (2 * (C₀ * α / L))
      have hb' := Real.sqrt_nonneg (2 * β ^ 2 * C₁)
      nlinarith [ha, hb, ha', hb']
    calc Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁)
        ≤ Real.sqrt ((Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁)) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁) :=
          Real.sqrt_sq (by positivity)
  have hscal : Real.sqrt (2 * β ^ 2 * C₁) = Real.sqrt 2 * |β| * Real.sqrt C₁ := by
    rw [show (2 : ℝ) * β ^ 2 * C₁ = 2 * β ^ 2 * C₁ by ring,
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * β ^ 2) C₁,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (β ^ 2), Real.sqrt_sq_eq_abs]
  calc Work.Spaces.HkNorm α 6 (Work.FTS.LocData.locG α L β h)
      = Real.sqrt (Work.Spaces.HkSq α 6 (Work.FTS.LocData.locG α L β h)) := rfl
    _ ≤ Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁) := hmono
    _ ≤ Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁) := hsplit
    _ = Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt 2 * |β| * Real.sqrt C₁ := by rw [hscal]

/-! ## The `ε`-smallness at order `6` -/

/-- **THE ORDER-`6` SMALLNESS (generic bump).**  For every `ε > 0` there is `L₀` such that for
every `L ≥ L₀` there is a scalar `β` with `|β| ≤ ε`, `L₁₂(locG α L β h)(0) = 0` and
`HkNorm α 6 (locG α L β h) ≤ ε`.  This is `Work.FTS.LocData.locData_small_general` at order `6`;
the two facts about the far part are the hypotheses `hC₀` (`α/L`-decay of `HkSq α 6`) and `hZT`
(membership in `ℋ⁶`). -/
theorem locData6_small_aux (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ} {K : ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad h)
    (hmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 h z θ ≤ K ^ 2 * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
    (hD : 0 < Work.Construction.L12 h 0)
    (hlin : ∀ L β : ℝ, 1 ≤ L → Work.Construction.L12 (Work.FTS.LocData.locG α L β h) 0
      = -(Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0)
        + β * Work.Construction.L12 h 0)
    (hC₀ : ∃ C₀ : ℝ, ∀ L : ℝ, 1 ≤ L →
      Work.Spaces.HkSq α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) ≤ C₀ * α / L)
    (hZT : ∀ L : ℝ, 1 ≤ L →
      Work.Spaces.HkMem α 6 (Work.Stability.zfar L (Work.Construction.Fstar α))) :
    ∀ ε > 0, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∃ β : ℝ,
      |β| ≤ ε ∧
        Work.Construction.L12 (Work.FTS.LocData.locG α L β h) 0 = 0 ∧
        Work.Spaces.HkNorm α 6 (Work.FTS.LocData.locG α L β h) ≤ ε := by
  intro ε hε
  obtain ⟨C₀, hC₀'⟩ := hC₀
  have hmemH : Work.Spaces.HkMem α 6 h := HkMem_h_of_majorant6 α hα hα1 hsm hmaj
  set C₁ : ℝ := Work.Spaces.HkSq α 6 h with hC₁def
  have hC₁ : Work.Spaces.HkSq α 6 h ≤ C₁ := le_of_eq hC₁def.symm
  have hC₁nn : (0 : ℝ) ≤ C₁ := by rw [hC₁def]; exact Work.Spaces.HkSq_nonneg α 6 h
  obtain ⟨D, hDdef, hDpos⟩ : ∃ D : ℝ, D = Work.Construction.L12 h 0 ∧ 0 < D :=
    ⟨_, rfl, hD⟩
  have hC₀nn : 0 ≤ C₀ := by
    have h : 0 ≤ C₀ * α / 1 :=
      le_trans (Work.Spaces.HkSq_nonneg α 6 _) (by simpa using hC₀' 1 le_rfl)
    nlinarith [hα]
  have hεpos : 0 < ε := hε
  set L₀ : ℝ := max 1 (max (8 * C₀ * α / ε ^ 2)
    (max (4 * α / (ε * D)) (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)))) with hL₀
  refine ⟨L₀, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : 8 * C₀ * α / ε ^ 2 ≤ L := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
    exact this
  have hL3 : 4 * α / (ε * D) ≤ L := by
    have h1 : max (4 * α / (ε * D)) (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)) ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    exact le_trans (le_max_left _ _) h1
  have hL4 : 8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D) ≤ L := by
    have h1 : max (4 * α / (ε * D)) (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)) ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    exact le_trans (le_max_right _ _) h1
  have hLpos : 0 < L := by linarith
  refine ⟨Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0 / D,
    ?_, ?_, ?_⟩
  · -- `|β| ≤ ε`
    have hN : |Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0|
        ≤ 4 * α / L := Work.FTS.LocData.L12_zfar_Fstar_abs_le α hα hα1 hL1
    have hden : 0 < ε * D := mul_pos hεpos hDpos
    have h3 : 4 * α / L ≤ ε * D := by
      rw [div_le_iff₀ hLpos]
      have h3' : 4 * α ≤ ε * D * L := by
        rw [div_le_iff₀ hden] at hL3
        linarith [hL3]
      linarith [h3']
    rw [abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    linarith [hN, h3]
  · -- the `L₁₂`-orthogonality at `z = 0`
    rw [hlin L _ hL1]
    rw [show Work.Construction.L12 h 0 = D from hDdef.symm]
    rw [div_mul_cancel₀ _ (ne_of_gt hDpos)]
    ring
  · -- the `ℋ⁶`-bound
    refine le_trans (HkNorm_locG_le_gen6 α hα hα1 hL1 hsm hC₀nn hC₁nn (hZT L hL1) hmemH
      (hC₀' L hL1) hC₁) ?_
    have hN : |Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0|
        ≤ 4 * α / L := Work.FTS.LocData.L12_zfar_Fstar_abs_le α hα hα1 hL1
    have hβb : |Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0 / D|
        ≤ 4 * α / (L * D) := by
      rw [abs_div, abs_of_pos hDpos]
      rw [show 4 * α / (L * D) = (4 * α / L) / D by field_simp]
      rw [div_le_iff₀ hDpos, div_mul_cancel₀ _ (ne_of_gt hDpos)]
      exact hN
    have harg1 : 2 * (C₀ * α / L) ≤ (ε / 2) ^ 2 := by
      have h2 : 8 * C₀ * α ≤ ε ^ 2 * L := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < ε ^ 2)] at hL2
        linarith [hL2]
      rw [show (2 : ℝ) * (C₀ * α / L) = 2 * C₀ * α / L by ring]
      rw [div_le_iff₀ hLpos]
      nlinarith [h2]
    have hsqrt1 : Real.sqrt (2 * (C₀ * α / L)) ≤ ε / 2 := by
      calc Real.sqrt (2 * (C₀ * α / L)) ≤ Real.sqrt ((ε / 2) ^ 2) := Real.sqrt_le_sqrt harg1
        _ = ε / 2 := Real.sqrt_sq (by linarith)
    have hβterm : Real.sqrt 2 * |Work.Construction.L12 (Work.Stability.zfar L
        (Work.Construction.Fstar α)) 0 / D| * Real.sqrt C₁ ≤ ε / 2 := by
      have h2 : 0 ≤ Real.sqrt 2 * Real.sqrt C₁ :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      calc Real.sqrt 2 * |Work.Construction.L12 (Work.Stability.zfar L
            (Work.Construction.Fstar α)) 0 / D| * Real.sqrt C₁
          = (Real.sqrt 2 * Real.sqrt C₁) * |Work.Construction.L12 (Work.Stability.zfar L
              (Work.Construction.Fstar α)) 0 / D| := by ring
        _ ≤ (Real.sqrt 2 * Real.sqrt C₁) * (4 * α / (L * D)) :=
            mul_le_mul_of_nonneg_left hβb h2
        _ = (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)) * (ε / (2 * L)) := by
            field_simp
            ring
        _ ≤ L * (ε / (2 * L)) := mul_le_mul_of_nonneg_right hL4 (by positivity)
        _ = ε / 2 := by field_simp
    linarith [hsqrt1, hβterm]

end Work.FTS.LocData6
