/-
# `FTS_MuLamOK/Rows/Rl2Open` — the transport zero-mode, open-quadrant form

`|L₁₂(3 D_θf/(1+z))(0)| ≤ 9 · |f|_{ℋ⁴}` for every `f` which is `C^∞` on the open quadrant
`(0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen`) and whose `ℋ⁴`-integrand is honest
(`Work.Spaces.HkMem α 4 f`).

This is the honest form of the third zero-mode estimate of Elgindi's Proposition `muestimate`
(the transport term of `2αμ`), needed by the μ/λ clause `Work.FTS.StrongEps.MuLamOK`; it is the
open-quadrant restatement of `Work.FTS.Nonlinear.Pieces.rl2_bound` (whose hypothesis is the
stronger `SmoothQuad g`, i.e. `C^∞` on `z > -1`).  The hypothesis set is exactly the fragment of
`Work.FTS.ClassC.ClassC α f` that the μ/λ clause uses (`ClassC.reg` and `ClassC.mem`, via
`HkMem`-monotonicity).

Route (verbatim from `rl2_bound`): `3D_θg/(1+z)` is continuous on the open quadrant
(`SmoothOpen.Dth`), hence its slices are a.e. strongly measurable
(`Spaces.aesm_slice_of_continuousOn_Qd`) and its weighted angular energy is dominated by
`9 ∫_θ HkIntegrand α 4 g` (`dth_sq_le_HkIntegrand`, `slice_energy_le_HkIntegrand`, which need
only `HkMem`); `L12_zero_le_of_weight_bound` then gives
`|L₁₂ f 0| ≤ 3√(9 HkSq α 4 g) = 9 |g|_{ℋ⁴}`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLamOK.Rows

set_option autoImplicit false

theorem Rl2Open : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {f : ℝ → ℝ → ℝ},
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
      ≤ K * Work.FTS.Nonlin.Xn α f := by
  refine ⟨9, by norm_num, ?_⟩
  intro α g hα hα1 hso hmem
  set f : ℝ → ℝ → ℝ := fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z) with hf
  have hc : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (Function.uncurry (Work.Spaces.Dth g))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hso.Dth.continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => 3 / (1 + p.1))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      refine ContinuousOn.div continuousOn_const
        (continuousOn_const.add continuous_fst.continuousOn) ?_
      intro p hp
      have hp1 : 0 < p.1 := hp.1
      exact ne_of_gt (by positivity)
    have h3 : ContinuousOn (fun p : ℝ × ℝ =>
        (3 / (1 + p.1)) * Function.uncurry (Work.Spaces.Dth g) p)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := h2.mul h1
    refine h3.congr (fun p hp => ?_)
    simp only [Function.uncurry, hf]
    ring
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => f r θ ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => ?_)
    have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => f r θ ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => f p.1 p.2 ^ 2)
        (by change ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2) _
            exact hc.pow 2) hr
    refine MeasureTheory.Integrable.mono'
      ((hmem.1 r (Set.mem_Ici.mpr (le_of_lt hr))).const_mul 9) haesm ?_
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    rw [hIoo2]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsqle : (Work.Spaces.Dth g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
      Work.FTS.Nonlinear.Pieces.dth_sq_le_HkIntegrand α g hα hr hθ
    have hfe : f r θ = (3 / (1 + r)) * Work.Spaces.Dth g r θ := by rw [hf]; ring
    have h3 : (3 / (1 + r)) ^ 2 ≤ 9 := by
      have hr' : (0 : ℝ) < 1 + r := by linarith [Set.mem_Ioi.mp hr]
      rw [div_pow, div_le_iff₀ (pow_pos hr' 2)]
      nlinarith [sq_nonneg r, le_of_lt (Set.mem_Ioi.mp hr)]
    rw [Real.norm_of_nonneg (sq_nonneg _), hfe, mul_pow]
    exact mul_le_mul h3 hsqle (sq_nonneg _) (by norm_num)
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2
        ≤ 9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => ?_)
    have hslice := (Work.FTS.Nonlinear.Pieces.slice_energy_le_HkIntegrand α g hα hα1 hmem).1 r hr
    have hint : (∫ θ in Work.Spaces.Iθ, f r θ ^ 2)
        = (3 / (1 + r)) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      rw [hf]; ring
    have h3 : (3 / (1 + r)) ^ 2 ≤ 9 := by
      have hr' : (0 : ℝ) < 1 + r := by linarith [Set.mem_Ioi.mp hr]
      rw [div_pow, div_le_iff₀ (pow_pos hr' 2)]
      nlinarith [sq_nonneg r, le_of_lt (Set.mem_Ioi.mp hr)]
    have hnn : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g r θ
    calc (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2
        = (3 / (1 + r)) ^ 2 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2)
            * ((1 + r) / r) ^ 2) := by rw [hint]; ring
      _ ≤ (3 / (1 + r)) ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
          mul_le_mul_of_nonneg_left hslice (sq_nonneg _)
      _ ≤ 9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
          mul_le_mul_of_nonneg_right h3 hnn
  have hΦint : MeasureTheory.IntegrableOn
      (fun z => 9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      (Set.Ioi (0 : ℝ)) :=
    (hmem.2.mono_set Set.Ioi_subset_Ici_self).const_mul 9
  have hmain := Work.FTS.Nonlinear.Pieces.L12_zero_le_of_weight_bound hsl
    (Work.FTS.Nonlinear.Pieces.aesm_weighted_energy_of_continuousOn hc) hΦint hbd
  have hsqeval : (∫ r in Set.Ioi (0 : ℝ),
        9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      = 9 * Work.Spaces.HkSq α 4 g := by
    rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]
    congr 1
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
  have hsqrt : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      = 3 * Work.FTS.Nonlin.Xn α g := by
    rw [hsqeval, Work.FTS.Nonlin.Xn]
    congr 1
    have h1 : (3 * Work.Spaces.HkNorm α 4 g) ^ 2 = 9 * Work.Spaces.HkSq α 4 g := by
      rw [Work.Spaces.HkNorm, mul_pow, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 g)]
      norm_num
    rw [← h1]
    exact Real.sqrt_sq (mul_nonneg (by norm_num) (Work.Spaces.HkNorm_nonneg α 4 g))
  calc |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0|
      = |Work.Construction.L12 f 0| := by rw [hf]
    _ ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) := hmain
    _ = 3 * (3 * Work.FTS.Nonlin.Xn α g) := by rw [hsqrt]
    _ = 9 * Work.FTS.Nonlin.Xn α g := by ring

end Work.FTS_MuLamOK.Rows
