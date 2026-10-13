import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcIBP
import Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcIntShift
import Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcIntTailZero
import Submission.Work.FTS.EllSol.ShiftFT.Aux2.sqIntegralAbsLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The tail behaviour of the backward particular solution `Gc`

`Gc N b u` is the backward particular solution of the shifted equation
`L_b G = chi N · (L_b u)`, written in `ShiftPrimDefs` as

`Gc N b u t θ = chi N t · u t θ + e^{bt} ∫_t^{2N} e^{-bs} (chi N)'(s) u s θ ds`.

This file proves the three assertions needed about its behaviour *off* the truncation window:

* for `t ≤ -2N` it agrees with the *improper integral* form
  `Gc N b u t θ = -∫_{-2N}^{2N} e^{b(t-s)} chi N s (∂_t u - b u)(s,θ) ds`
  (the two right-tail pieces of the primitive identity are recombined by an integration by
  parts, the boundary terms vanishing because `chi N (±2N) = 0`);
* consequently `(Gc N b u t θ)^2 ≤ 4N ∫_{-2N}^{2N} (∂_t u - b u)(s,θ)^2 ds` for `t ≤ -2N`
  (Cauchy–Schwarz, using `0 ≤ b` to bound `e^{b(t-s)} ≤ 1` on the window);
* for `2N ≤ t` it vanishes identically (`(chi N)' = 0` on `[2N,∞)`).

The analytic pieces of this (the integration by parts and the Cauchy–Schwarz inequality for
interval integrals) are proved in the sibling modules `gcIBP`, `gcIntShift`, `gcIntTailZero`
and `sqIntegralAbsLe`.
-/

namespace Work.FTS.EllSol.ShiftFT.Aux2

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## Elementary support facts for the cutoff -/

/-- Off the strict window `|s| > 2N` the derivative of the cutoff vanishes (the cutoff is
locally constant there). -/
theorem deriv_chi_eq_zero_of_lt_abs {N t : ℝ} (hN : 0 < N) (ht : 2 * N < |t|) :
    deriv (Work.FTS.EllSol.Trunc.chi N) t = 0 := by
  have hev : Work.FTS.EllSol.Trunc.chi N =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
    have hopen : IsOpen {s : ℝ | 2 * N < |s|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact Work.FTS.EllSol.Trunc.chi_eq_zero hN (le_of_lt hs)
  rw [hev.deriv_eq, deriv_const]

theorem chi_eq_zero_at_two_mul_N {N : ℝ} (hN : 0 < N) :
    Work.FTS.EllSol.Trunc.chi N (2 * N) = 0 :=
  Work.FTS.EllSol.Trunc.chi_eq_zero hN (by rw [abs_of_nonneg (by linarith)])

theorem chi_eq_zero_at_neg_two_mul_N {N : ℝ} (hN : 0 < N) :
    Work.FTS.EllSol.Trunc.chi N (-(2 * N)) = 0 :=
  Work.FTS.EllSol.Trunc.chi_eq_zero hN (by rw [abs_neg, abs_of_nonneg (by linarith)])

/-! ## Slice regularity from the joint `C²` hypothesis -/

/-- The `θ`-slice of `u` is `C²` on all of `ℝ` for `θ` in the open angular interval. -/
theorem contDiff_slice_of_uncurry {u : ℝ → ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiff ℝ 2 (fun s : ℝ => u s θ) := by
  have hmap : Set.MapsTo (fun s : ℝ => ((s, θ) : ℝ × ℝ)) Set.univ
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun s _ => ⟨trivial, hθ⟩
  have hpair : ContDiffOn ℝ 2 (fun s : ℝ => ((s, θ) : ℝ × ℝ)) Set.univ :=
    ContDiffOn.prodMk contDiffOn_id contDiffOn_const
  have hslice : ContDiffOn ℝ 2 (fun s : ℝ => u s θ) Set.univ := by
    have h := hu.comp hpair hmap
    simpa [Function.comp_def, Function.uncurry] using h
  exact contDiffOn_univ.mp hslice

/-- The `t`-derivative of the `θ`-slice of `u` is continuous. -/
theorem continuous_pz_slice_of_uncurry {u : ℝ → ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    Continuous (fun s : ℝ => Work.Spaces.pz u s θ) :=
  (contDiff_slice_of_uncurry hθ hu).continuous_deriv (by norm_num)

/-! ## The target -/

theorem gcTail (N b : ℝ) (u : ℝ → ℝ → ℝ) (hb : 0 ≤ b) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → t ≤ -(2 * N) →
      Work.FTS.EllSol.ShiftFT.Gc N b u t θ
        = -(∫ s in (-(2 * N))..(2 * N),
            Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
              * (Work.Spaces.pz u s θ - b * u s θ)))
    ∧ (∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → t ≤ -(2 * N) →
      (Work.FTS.EllSol.ShiftFT.Gc N b u t θ) ^ 2
        ≤ 4 * N * ∫ s in (-(2 * N))..(2 * N), (Work.Spaces.pz u s θ - b * u s θ) ^ 2)
    ∧ (∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 2 * N ≤ t →
      Work.FTS.EllSol.ShiftFT.Gc N b u t θ = 0) := by
  have hchi_cont : Continuous (Work.FTS.EllSol.Trunc.chi N) :=
    (Work.FTS.EllSol.Trunc.chi_contDiff 2 N).continuous
  have htail : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → t ≤ -(2 * N) →
      Work.FTS.EllSol.ShiftFT.Gc N b u t θ
        = -(∫ s in (-(2 * N))..(2 * N),
            Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
              * (Work.Spaces.pz u s θ - b * u s θ)) := by
    intro t θ hθ ht
    have hχt : Work.FTS.EllSol.Trunc.chi N t = 0 := by
      refine Work.FTS.EllSol.Trunc.chi_eq_zero hN ?_
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hunfold : Work.FTS.EllSol.ShiftFT.Gc N b u t θ
        = Work.FTS.EllSol.Trunc.chi N t * u t θ
          + Real.exp (b * t) * ∫ s in t..(2 * N),
              Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := rfl
    rw [hunfold, hχt, zero_mul, zero_add, gcIntShift N b u hN hu θ hθ t ht]
    rw [gcIBP N b u hN hu θ hθ t]
    ring
  have hzero : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 2 * N ≤ t →
      Work.FTS.EllSol.ShiftFT.Gc N b u t θ = 0 := by
    intro t θ hθ ht
    have hχt : Work.FTS.EllSol.Trunc.chi N t = 0 := by
      refine Work.FTS.EllSol.Trunc.chi_eq_zero hN ?_
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hunfold : Work.FTS.EllSol.ShiftFT.Gc N b u t θ
        = Work.FTS.EllSol.Trunc.chi N t * u t θ
          + Real.exp (b * t) * ∫ s in t..(2 * N),
              Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := rfl
    rw [hunfold, hχt, zero_mul, zero_add, gcIntTailZero N b u hN hu θ hθ t ht, mul_zero]
  refine ⟨htail, ?_, hzero⟩
  intro t θ hθ ht
  have hu_cont : Continuous (fun s : ℝ => u s θ) := (contDiff_slice_of_uncurry hθ hu).continuous
  have hpz_cont : Continuous (fun s : ℝ => Work.Spaces.pz u s θ) :=
    continuous_pz_slice_of_uncurry hθ hu
  have hv_cont : Continuous (fun s : ℝ => Work.Spaces.pz u s θ - b * u s θ) :=
    hpz_cont.sub (hu_cont.const_mul b)
  have hexp_cont : Continuous (fun s : ℝ => Real.exp (b * (t - s))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hJabs_le : ∀ s : ℝ,
      |Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
          * (Work.Spaces.pz u s θ - b * u s θ)|
        ≤ |Work.Spaces.pz u s θ - b * u s θ| := by
    intro s
    by_cases hχ : Work.FTS.EllSol.Trunc.chi N s = 0
    · rw [hχ, mul_zero, zero_mul, abs_zero]
      exact abs_nonneg _
    · have hts : t ≤ s := by
        by_contra hcon
        have hcon' : s < t := lt_of_not_ge hcon
        have hst : s < -(2 * N) := lt_of_lt_of_le hcon' ht
        have habs : |s| = -s := abs_of_neg (by linarith)
        exact hχ (Work.FTS.EllSol.Trunc.chi_eq_zero hN (by rw [habs]; linarith))
      have hexp1 : Real.exp (b * (t - s)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonneg_of_nonpos hb (by linarith)
      have hexp0 : 0 ≤ Real.exp (b * (t - s)) := Real.exp_nonneg _
      have hχ0 : 0 ≤ Work.FTS.EllSol.Trunc.chi N s := Work.FTS.EllSol.Trunc.chi_nonneg _ _
      have hχ1 : Work.FTS.EllSol.Trunc.chi N s ≤ 1 := Work.FTS.EllSol.Trunc.chi_le_one _ _
      calc |Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
              * (Work.Spaces.pz u s θ - b * u s θ)|
          = Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
              * |Work.Spaces.pz u s θ - b * u s θ| := by
            rw [abs_mul, abs_of_nonneg (mul_nonneg hexp0 hχ0)]
        _ ≤ 1 * |Work.Spaces.pz u s θ - b * u s θ| :=
            mul_le_mul_of_nonneg_right (mul_le_one₀ hexp1 hχ0 hχ1) (abs_nonneg _)
        _ = |Work.Spaces.pz u s θ - b * u s θ| := one_mul _
  have hstep1 : |Work.FTS.EllSol.ShiftFT.Gc N b u t θ|
      ≤ ∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ| := by
    rw [htail t θ hθ ht, abs_neg]
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs
      (f := fun s => Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
        * (Work.Spaces.pz u s θ - b * u s θ)) (by linarith)) ?_
    refine intervalIntegral.integral_mono (by linarith) ?_ ?_ (fun s => hJabs_le s)
    · exact ((hexp_cont.mul hchi_cont).mul hv_cont).abs.intervalIntegrable _ _
    · exact hv_cont.abs.intervalIntegrable _ _
  have hCS : (∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|) ^ 2
      ≤ 4 * N * ∫ s in (-(2 * N))..(2 * N), (Work.Spaces.pz u s θ - b * u s θ) ^ 2 := by
    have h := sqIntegralAbsLe (-(2 * N)) (2 * N) (by linarith)
      (fun s : ℝ => Work.Spaces.pz u s θ - b * u s θ) hv_cont
    convert h using 1
    ring
  have hsq : |Work.FTS.EllSol.ShiftFT.Gc N b u t θ| ^ 2
      ≤ (∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (Work.FTS.EllSol.ShiftFT.Gc N b u t θ)) hstep1
    simpa [sq] using h
  calc (Work.FTS.EllSol.ShiftFT.Gc N b u t θ) ^ 2
      = |Work.FTS.EllSol.ShiftFT.Gc N b u t θ| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|) ^ 2 := hsq
    _ ≤ 4 * N * ∫ s in (-(2 * N))..(2 * N), (Work.Spaces.pz u s θ - b * u s θ) ^ 2 := hCS

end

end Work.FTS.EllSol.ShiftFT.Aux2
