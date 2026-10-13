import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ThShiftSubst`

The angular substitution bound used in the smoothness of `Fstar (Jeps ρ ε W)`: the critical
weight `sinCos2 θ = sin θ cos²θ` is bounded by `1`, and the log-coordinate shift
`θ ↦ thShift θ q = arctan (tan θ · e^{-q})` changes the angular measure by at most `e^{3|q|}`
(`JepsHkMem.lintegral_thShift_le`).  Hence

  `∫_{θ ∈ (0,π/2)} sinCos2 θ · H (thShift θ q) ≤ e^{3|q|} ∫_{θ ∈ (0,π/2)} H θ`
  `  ≤ e^{3ε} ∫_{θ ∈ (0,π/2)} H θ`   for `|q| ≤ ε`,

for every nonnegative `H` which is integrable on `(0, π/2)`.

Everything is first done for `lintegral`s (`ofReal` of the integrand), where no measurability of
`H ∘ thShift` is ever needed, and only at the very end is the Bochner integral compared with the
`toReal` of the corresponding `lintegral` (`integral_le_toReal_lintegral_of_nonneg_ae`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

/-- A Bochner integral which is nonnegative a.e. on `s` is bounded by the `toReal` of the
`lintegral` of the `ofReal` of the integrand.  (The general-measure statement, in the form
needed below: the integrand must be nonnegative on `s`, not everywhere.) -/
theorem integral_le_toReal_lintegral_of_nonneg_ae {g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hg : ∀ θ ∈ s, 0 ≤ g θ) :
    ∫ θ in s, g θ ≤ ENNReal.toReal (∫⁻ θ in s, ENNReal.ofReal (g θ)) := by
  have hae : 0 ≤ᵐ[volume.restrict s] g := by
    filter_upwards [MeasureTheory.ae_restrict_mem hs] with θ hθ
    exact hg θ hθ
  by_cases hint : IntegrableOn g s
  · rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hae hint.aestronglyMeasurable]
  · rw [MeasureTheory.integral_undef hint]
    exact ENNReal.toReal_nonneg

/-- `sin θ cos²θ ≥ 0` on `(0, π/2)`. -/
theorem sinCos2_nonneg_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg hsin0 (sq_nonneg _)

/-- `sin θ cos²θ ≤ 1` on `(0, π/2)`. -/
theorem sinCos2_le_one_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Elliptic.sinCos2 θ ≤ 1 := by
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  calc Work.Elliptic.sinCos2 θ = Real.sin θ * Real.cos θ ^ 2 := rfl
    _ ≤ Real.sin θ * 1 := mul_le_mul_of_nonneg_left (Real.cos_sq_le_one θ) hsin0
    _ = Real.sin θ := mul_one _
    _ ≤ 1 := Real.sin_le_one θ

/-- The closed angular interval `Iθ = [0, π/2]` and the open one `(0, π/2)` differ by a null
set, so their `lintegral`s agree. -/
theorem lintegral_Iθ_eq_Ioo (U : ℝ → ENNReal) :
    (∫⁻ θ in Work.Spaces.Iθ, U θ) = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), U θ :=
  MeasureTheory.setLIntegral_congr
    (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := (Real.pi / 2))).symm

theorem ThShiftSubst {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {q : ℝ}, |q| ≤ ε → ∀ {H : ℝ → ℝ},
      MeasureTheory.IntegrableOn H (Set.Ioo 0 (Real.pi / 2)) → (∀ θ, 0 ≤ H θ) →
      ∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.Elliptic.sinCos2 θ * H (Work.FTS.StrongEps.thShift θ q)
        ≤ C * ∫ θ in Set.Ioo 0 (Real.pi / 2), H θ := by
  have hε0 : (0 : ℝ) ≤ ε := le_of_lt hε
  refine ⟨Real.exp (3 * ε), Real.exp_nonneg _, ?_⟩
  intro q hq H hint hH
  -- the `lintegral` of `ofReal` of the integrand
  set A : ENNReal :=
    ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
      ENNReal.ofReal (Work.Elliptic.sinCos2 θ * H (Work.FTS.StrongEps.thShift θ q)) with hAdef
  -- step 1: Bochner integral ≤ `toReal` of the `lintegral`
  have hLHS : ∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.Elliptic.sinCos2 θ * H (Work.FTS.StrongEps.thShift θ q) ≤ A.toReal :=
    integral_le_toReal_lintegral_of_nonneg_ae measurableSet_Ioo
      fun θ hθ => mul_nonneg (sinCos2_nonneg_of_mem_Ioo hθ) (hH _)
  -- step 2: split the `ofReal` of the product
  have hprod : A = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
      ENNReal.ofReal (Work.Elliptic.sinCos2 θ)
        * ENNReal.ofReal (H (Work.FTS.StrongEps.thShift θ q)) := by
    rw [hAdef]
    exact MeasureTheory.lintegral_congr fun θ => ENNReal.ofReal_mul' (hH _)
  -- step 3: `sinCos2 θ ≤ 1`, so the weight can be dropped
  have hdrop : (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ENNReal.ofReal (Work.Elliptic.sinCos2 θ)
          * ENNReal.ofReal (H (Work.FTS.StrongEps.thShift θ q)))
      ≤ ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
          ENNReal.ofReal (H (Work.FTS.StrongEps.thShift θ q)) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have h1 : ENNReal.ofReal (Work.Elliptic.sinCos2 θ) ≤ 1 :=
      ENNReal.ofReal_le_one.2 (sinCos2_le_one_of_mem_Ioo hθ)
    calc ENNReal.ofReal (Work.Elliptic.sinCos2 θ)
            * ENNReal.ofReal (H (Work.FTS.StrongEps.thShift θ q))
        ≤ 1 * ENNReal.ofReal (H (Work.FTS.StrongEps.thShift θ q)) :=
          mul_le_mul_of_nonneg_right h1 zero_le
      _ = ENNReal.ofReal (H (Work.FTS.StrongEps.thShift θ q)) := one_mul _
  -- step 4: the log-coordinate shift bound over `Iθ`
  have hIθIoo : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (H (Work.FTS.StrongEps.thShift θ q)))
      = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ENNReal.ofReal (H (Work.FTS.StrongEps.thShift θ q)) := lintegral_Iθ_eq_Ioo _
  have hIθIooH : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (H θ))
      = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (H θ) := lintegral_Iθ_eq_Ioo _
  have hshift : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (H (Work.FTS.StrongEps.thShift θ q)))
      ≤ ENNReal.ofReal (Real.exp (3 * |q|))
        * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (H θ) :=
    Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le (fun θ => ENNReal.ofReal (H θ)) q
  have hB : (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ENNReal.ofReal (H (Work.FTS.StrongEps.thShift θ q)))
      ≤ ENNReal.ofReal (Real.exp (3 * |q|))
        * ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (H θ) := by
    rw [← hIθIoo, ← hIθIooH]
    exact hshift
  -- step 5: identify the `lintegral` of `ofReal ∘ H` with `ofReal` of the Bochner integral
  have hC : ENNReal.ofReal (∫ θ in Set.Ioo 0 (Real.pi / 2), H θ)
      = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (H θ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hH)
  have hRHSnn : 0 ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), H θ := MeasureTheory.integral_nonneg hH
  -- the `lintegral` bound, with the constant pulled inside the `ofReal`
  have hmain : A ≤ ENNReal.ofReal (Real.exp (3 * |q|) * ∫ θ in Set.Ioo 0 (Real.pi / 2), H θ) := by
    rw [hprod]
    refine (hdrop.trans hB).trans (le_of_eq ?_)
    rw [← hC, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  -- take `toReal`
  have hto : A.toReal ≤ Real.exp (3 * |q|) * ∫ θ in Set.Ioo 0 (Real.pi / 2), H θ := by
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain).trans_eq ?_
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) hRHSnn)]
  calc ∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.Elliptic.sinCos2 θ * H (Work.FTS.StrongEps.thShift θ q)
      ≤ A.toReal := hLHS
    _ ≤ Real.exp (3 * |q|) * ∫ θ in Set.Ioo 0 (Real.pi / 2), H θ := hto
    _ ≤ Real.exp (3 * ε) * ∫ θ in Set.Ioo 0 (Real.pi / 2), H θ := by
        refine mul_le_mul_of_nonneg_right ?_ hRHSnn
        rw [Real.exp_le_exp]
        nlinarith [hq, abs_nonneg q]

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
