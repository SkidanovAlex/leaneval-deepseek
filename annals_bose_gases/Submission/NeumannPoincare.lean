import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# One-dimensional Neumann (mean-subtracted) Poincaré inequality

Any "gap above the condensate" argument for a Neumann-type box (the Fournais--
Solovej small/large box analysis, Section 5 onward; and the corpus's per-cell
a priori bounds) needs the classical one-dimensional inequality

    ∫₀^L (f(x) − m)² dx ≤ L² · ∫₀^L (f′(x))² dx,
    m := (1/L)·∫₀^L f,

for `f : ℝ → ℝ` of class C¹ and `L > 0`.  (The sharp constant is `1/π²`;
the crude constant `1` here — proved by the mean-value argument: `f − m`
has integral `0`, so it vanishes somewhere in `[0,L]`, and the FTC +
Cauchy--Schwarz give the bound.)  This is the 1D atom; N-particle /
multi-coordinate versions follow by applying it slicewise.

Only the atom is proved here.  Constants deliberately crude.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real

namespace Submission.BoseGases

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- Interval Cauchy–Schwarz: for `a ≤ b` and a nonnegative function
`h` continuous on `[a,b]`,  `(∫_a^b h)² ≤ (b-a)·∫_a^b h²`. -/
lemma cs_interval {a b : ℝ} (hab : a ≤ b) {h : ℝ → ℝ}
    (hh : ContinuousOn h (Set.Icc a b)) (h0 : ∀ x, 0 ≤ h x) :
    (∫ x in a..b, h x) ^ 2 ≤ (b - a) * ∫ x in a..b, (h x) ^ 2 := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hfin : IsFiniteMeasure ν := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure ν := hfin
  have hmh : AEStronglyMeasurable h ν := by
    refine ContinuousOn.aestronglyMeasurable (s := Set.Ioc a b) (μ := volume) ?_ (by simp)
    exact hh.mono (by intro x hx; exact Set.Ioc_subset_Icc_self hx)
  have h0ae : 0 ≤ᵐ[ν] h := ae_of_all _ h0
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
  have hbnd : ∀ᵐ x ∂ν, ‖h x‖ ≤ C := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact (ae_of_all volume (fun x hx => hC x (Set.Ioc_subset_Icc_self hx)))
  have hmem : MemLp h (ENNReal.ofReal 2) ν := MemLp.of_bound hmh C hbnd
  have hmem1 : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) ν := memLp_const (1 : ℝ)
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (μ := ν)
    Real.HolderConjugate.two_two h0ae (ae_of_all _ (fun _ => by norm_num)) hmem hmem1
  have hA : (∫ x, h x * (1 : ℝ) ∂ν) = ∫ x, h x ∂ν := by simp
  have h2r : (fun x : ℝ => (h x) ^ (2 : ℝ)) = fun x : ℝ => (h x) ^ 2 := by
    funext x; rw [Real.rpow_two]
  have h1r : (fun x : ℝ => (1 : ℝ) ^ (2 : ℝ)) = fun x : ℝ => (1 : ℝ) := by
    funext x; rw [Real.rpow_two]; norm_num
  rw [hA, h2r, h1r] at hmain
  let A := ∫ x, h x ∂ν
  let B := ∫ x, (h x) ^ 2 ∂ν
  let C := ν.real Set.univ
  have hB0 : 0 ≤ B := by dsimp [B]; exact integral_nonneg (fun x => sq_nonneg (h x))
  have hC0 : 0 ≤ C := by simp [C]
  have hA0 : 0 ≤ A := by dsimp [A]; exact integral_nonneg h0
  have hR : A ≤ √B * √C := by
    dsimp [A, B, C]
    simpa [Real.sqrt_eq_rpow] using hmain
  have hsquared : A ^ 2 ≤ B * C := by
    have h1 : |A| ≤ |√B * √C| := by
      calc
        |A| = A := abs_of_nonneg hA0
        _ ≤ √B * √C := hR
        _ = |√B * √C| :=
          (abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).symm
    calc
      A ^ 2 ≤ (√B * √C) ^ 2 := (sq_le_sq.mpr h1)
      _ = B * C := by
        rw [mul_pow, Real.sq_sqrt hB0, Real.sq_sqrt hC0]
  have hCeq : ν.real Set.univ = b - a := by
    dsimp [ν]
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  dsimp [A, B, C] at hsquared
  rw [hCeq] at hsquared
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  simpa [mul_comm] using hsquared

/-- The Lebesgue integral over `[a,b]` equals the interval integral `∫_a^b`
when `a ≤ b`. -/
lemma integral_Icc_eq_interval {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x in Set.Icc a b, f x) = ∫ x in a..b, f x := by
  calc
    (∫ x in Set.Icc a b, f x) = ∫ x in Set.Ioc a b, f x :=
      MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ x in a..b, f x := (intervalIntegral.integral_of_le hab).symm

/-- One-dimensional Neumann (mean-subtracted) Poincaré inequality, in
interval-integral form: if `∫₀^L (f − m) = 0` (i.e. `m` is the mean of `f`
on `[0,L]`), then `∫₀^L (f−m)² ≤ L²·∫₀^L (f′)²`. -/
lemma mean_zero_poincare_interval {L m : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hm : (∫ x in (0 : ℝ)..L, (f x - m)) = 0) :
    (∫ x in (0 : ℝ)..L, (f x - m) ^ 2) ≤
      L ^ 2 * (∫ x in (0 : ℝ)..L, (deriv f x) ^ 2) := by
  let g : ℝ → ℝ := fun x => f x - m
  let B : ℝ := ∫ x in (0 : ℝ)..L, (deriv f x) ^ 2
  -- `g = f − m` is C¹ and has the same derivative as `f`
  have hg : ContDiff ℝ 1 g := by
    dsimp [g]
    exact ContDiff.sub hf (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => m))
  have hgC : Continuous g := hg.continuous
  have hdf : Continuous (deriv f) := hf.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
  -- the antiderivative `F u = ∫₀^u g` vanishes at both endpoints; Rolle gives
  -- a point `c0 ∈ (0,L)` with `g c0 = 0`
  let F : ℝ → ℝ := fun u => ∫ x in (0 : ℝ)..u, g x
  have hF0 : F 0 = 0 := by simp [F]
  have hFL : F L = 0 := by simpa [F, g] using hm
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) L) := by
    intro x hx
    exact ((Continuous.integral_hasStrictDerivAt hgC 0 x).hasDerivAt.continuousAt).continuousWithinAt
  obtain ⟨c0, hc0Ioo, hc0deriv⟩ :=
    exists_deriv_eq_zero (f := F) (a := (0 : ℝ)) (b := L) hL hFcont (hF0.trans hFL.symm)
  have hc0 : g c0 = 0 := by
    have hdc : deriv F c0 = g c0 := by
      simpa [F] using (Continuous.deriv_integral g hgC 0 c0)
    rw [hdc] at hc0deriv
    exact hc0deriv
  have hc0ge : (0 : ℝ) ≤ c0 := le_of_lt hc0Ioo.1
  have hc0le : c0 ≤ L := le_of_lt hc0Ioo.2
  have hfc0 : f c0 = m := by simpa [g, sub_eq_zero] using hc0
  -- the fundamental theorem of calculus, anchored at `c0`
  have hftc {x : ℝ} (hx0 : 0 ≤ x) (hxL : x ≤ L) : g x = ∫ y in c0..x, deriv f y := by
    have hft : ∫ y in c0..x, deriv f y = f x - f c0 :=
      intervalIntegral.integral_deriv_of_contDiffOn_uIcc (f := f) (a := c0) (b := x)
        (ContDiff.contDiffOn hf)
    rw [hfc0] at hft
    dsimp [g]
    exact hft.symm
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact intervalIntegral.integral_nonneg hL.le (fun x hx => sq_nonneg (deriv f x))
  -- pointwise bound: for `x ∈ [0,L]`, `(g x)² ≤ L·B`
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) L, (g x) ^ 2 ≤ L * B := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxL : x ≤ L := hx.2
    by_cases hcx : c0 ≤ x
    · -- case `c0 ≤ x`
      have h1 : |g x| ≤ ∫ y in c0..x, |deriv f y| := by
        have hgx' : g x = ∫ y in c0..x, deriv f y := hftc hx0 hxL
        calc
          |g x| = |∫ y in c0..x, deriv f y| := by rw [hgx']
          _ ≤ ∫ y in c0..x, |deriv f y| := intervalIntegral.abs_integral_le_integral_abs hcx
      have hcs := cs_interval hcx (h := fun y : ℝ => |deriv f y|)
        (by simpa using hdf.continuousOn.abs) (fun _ => abs_nonneg _)
      have hcs' : (∫ y in c0..x, |deriv f y|) ^ 2 ≤
          (x - c0) * (∫ y in c0..x, (deriv f y) ^ 2) := by
        simpa [sq_abs] using hcs
      have h2 : (g x) ^ 2 ≤ (x - c0) * (∫ y in c0..x, (deriv f y) ^ 2) := by
        calc
          (g x) ^ 2 = |g x| ^ 2 := by rw [sq_abs]
          _ ≤ (∫ y in c0..x, |deriv f y|) ^ 2 :=
            (pow_le_pow_left₀ (abs_nonneg (g x)) h1 2)
          _ ≤ (x - c0) * (∫ y in c0..x, (deriv f y) ^ 2) := hcs'
      have hmono : (∫ y in c0..x, (deriv f y) ^ 2) ≤ B := by
        dsimp [B]
        have hn0 : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) L)]
            (fun y : ℝ => (deriv f y) ^ 2) := by
          apply ae_of_all
          intro y
          exact sq_nonneg (deriv f y)
        have hfi : IntervalIntegrable (fun y : ℝ => (deriv f y) ^ 2) volume (0 : ℝ) L :=
          (hdf.pow 2).intervalIntegrable 0 L
        simpa using
          (intervalIntegral.integral_mono_interval (f := fun y : ℝ => (deriv f y) ^ 2)
            (c := (0 : ℝ)) (d := L) (a := c0) (b := x) hc0ge hcx hxL hn0 hfi)
      have hxmc : 0 ≤ x - c0 := sub_nonneg.mpr hcx
      have h3 : (g x) ^ 2 ≤ (x - c0) * B :=
        le_trans h2 (mul_le_mul_of_nonneg_left hmono hxmc)
      have hxmcL : x - c0 ≤ L := by nlinarith [hc0ge, hxL]
      exact le_trans h3 (mul_le_mul_of_nonneg_right hxmcL hB0)
    · -- case `x < c0` (symmetrically, on `[x, c0]`)
      have hxc : x ≤ c0 := le_of_not_ge hcx
      have h1 : |g x| ≤ ∫ y in x..c0, |deriv f y| := by
        have hgx' : g x = ∫ y in c0..x, deriv f y := hftc hx0 hxL
        calc
          |g x| = |∫ y in c0..x, deriv f y| := by rw [hgx']
          _ = |∫ y in x..c0, deriv f y| := by
            rw [intervalIntegral.integral_symm]
            simp
          _ ≤ ∫ y in x..c0, |deriv f y| := intervalIntegral.abs_integral_le_integral_abs hxc
      have hcs := cs_interval hxc (h := fun y : ℝ => |deriv f y|)
        (by simpa using hdf.continuousOn.abs) (fun _ => abs_nonneg _)
      have hcs' : (∫ y in x..c0, |deriv f y|) ^ 2 ≤
          (c0 - x) * (∫ y in x..c0, (deriv f y) ^ 2) := by
        simpa [sq_abs] using hcs
      have h2 : (g x) ^ 2 ≤ (c0 - x) * (∫ y in x..c0, (deriv f y) ^ 2) := by
        calc
          (g x) ^ 2 = |g x| ^ 2 := by rw [sq_abs]
          _ ≤ (∫ y in x..c0, |deriv f y|) ^ 2 :=
            (pow_le_pow_left₀ (abs_nonneg (g x)) h1 2)
          _ ≤ (c0 - x) * (∫ y in x..c0, (deriv f y) ^ 2) := hcs'
      have hmono : (∫ y in x..c0, (deriv f y) ^ 2) ≤ B := by
        dsimp [B]
        have hn0 : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) L)]
            (fun y : ℝ => (deriv f y) ^ 2) := by
          apply ae_of_all
          intro y
          exact sq_nonneg (deriv f y)
        have hfi : IntervalIntegrable (fun y : ℝ => (deriv f y) ^ 2) volume (0 : ℝ) L :=
          (hdf.pow 2).intervalIntegrable 0 L
        simpa using
          (intervalIntegral.integral_mono_interval (f := fun y : ℝ => (deriv f y) ^ 2)
            (c := (0 : ℝ)) (d := L) (a := x) (b := c0) hx0 hxc hc0le hn0 hfi)
      have hcxm : 0 ≤ c0 - x := sub_nonneg.mpr hxc
      have h3 : (g x) ^ 2 ≤ (c0 - x) * B :=
        le_trans h2 (mul_le_mul_of_nonneg_left hmono hcxm)
      have hcxmL : c0 - x ≤ L := by nlinarith [hx0, hc0le]
      exact le_trans h3 (mul_le_mul_of_nonneg_right hcxmL hB0)
  -- integrate the pointwise bound over `x ∈ [0,L]`
  have hmono2 : (∫ x in (0 : ℝ)..L, (g x) ^ 2) ≤ (∫ x in (0 : ℝ)..L, L * B) := by
    apply intervalIntegral.integral_mono_on hL.le
    · exact (hgC.pow 2).intervalIntegrable 0 L
    · exact intervalIntegrable_const
    · exact hpt
  have hLB : (∫ x in (0 : ℝ)..L, L * B) = L * (L * B) := by
    rw [intervalIntegral.integral_const]
    simp
  have hmain : (∫ x in (0 : ℝ)..L, (g x) ^ 2) ≤ L ^ 2 * B := by
    calc
      (∫ x in (0 : ℝ)..L, (g x) ^ 2) ≤ (∫ x in (0 : ℝ)..L, L * B) := hmono2
      _ = L * (L * B) := hLB
      _ = L ^ 2 * B := by ring
  simpa [g, B] using hmain

/-- The same inequality with the mean written as `m` (both sides shifted):
useful when the mean is already named. -/
lemma neumann_poincare_one_mean {L m : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hm : m = (1 / L) * (∫ y in Set.Icc (0 : ℝ) L, f y)) :
    (∫ x in Set.Icc (0 : ℝ) L, (f x - m) ^ 2) ≤
      L ^ 2 * (∫ x in Set.Icc (0 : ℝ) L, (deriv f x) ^ 2) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hLle : (0 : ℝ) ≤ L := le_of_lt hL
  have hIntI : (∫ y in Set.Icc (0 : ℝ) L, f y) = ∫ y in (0 : ℝ)..L, f y :=
    integral_Icc_eq_interval hLle f
  -- `m·L = ∫₀^L f`, hence `∫₀^L (f − m) = 0`
  have hmL : m * L = (∫ y in (0 : ℝ)..L, f y) := by
    rw [hm]
    rw [hIntI]
    field_simp [hLne]
  have hmean0 : (∫ x in (0 : ℝ)..L, (f x - m)) = 0 := by
    have hsub := intervalIntegral.integral_sub (μ := volume) (f := f) (g := fun _ : ℝ => m)
      ((hf.continuous).intervalIntegrable (μ := volume) 0 L) (intervalIntegrable_const (μ := volume))
    calc
      (∫ x in (0 : ℝ)..L, (f x - m)) =
          (∫ x in (0 : ℝ)..L, f x) - (∫ x in (0 : ℝ)..L, m) := hsub
      _ = (∫ x in (0 : ℝ)..L, f x) - (L - 0) • m := by
        rw [intervalIntegral.integral_const]
      _ = (∫ x in (0 : ℝ)..L, f x) - m * L := by
        simp [mul_comm]
      _ = 0 := by
        rw [hmL]
        ring
  calc
    (∫ x in Set.Icc (0 : ℝ) L, (f x - m) ^ 2)
        = ∫ x in (0 : ℝ)..L, (f x - m) ^ 2 :=
          integral_Icc_eq_interval hLle (fun x => (f x - m) ^ 2)
    _ ≤ L ^ 2 * (∫ x in (0 : ℝ)..L, (deriv f x) ^ 2) :=
          mean_zero_poincare_interval hL hf hmean0
    _ = L ^ 2 * (∫ x in Set.Icc (0 : ℝ) L, (deriv f x) ^ 2) := by
          rw [← integral_Icc_eq_interval hLle (fun x => (deriv f x) ^ 2)]

/-- One-dimensional Neumann (mean-subtracted) Poincaré: for `f` C¹ and
`L > 0`, `∫₀^L (f − mean)² ≤ L² · ∫₀^L (f′)²`, `mean := (1/L)·∫₀^L f`
(integrals over `[0,L]`). -/
lemma neumann_poincare_one {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    (∫ x in Set.Icc (0 : ℝ) L, (f x - (1 / L) * (∫ y in Set.Icc (0 : ℝ) L, f y)) ^ 2) ≤
      L ^ 2 * (∫ x in Set.Icc (0 : ℝ) L, (deriv f x) ^ 2) := by
  exact neumann_poincare_one_mean hL hf rfl

end Submission.BoseGases
