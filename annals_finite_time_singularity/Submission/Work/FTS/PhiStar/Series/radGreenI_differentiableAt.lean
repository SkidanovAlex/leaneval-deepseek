/-
# `radGreenI_differentiableAt`

`Work.FTS.PhiStar.Radial.radGreenI α m c` is the explicit decaying solution of the mode-`m` Euler
equation

  `-α²z² a'' - α(5+α) z a' + λ_m a = c`,

written as a Green's function

  `radGreenI α m c z = K·( z^{s⁻}·∫₀^z c(t) t^{(2m+5)/α-1} dt
                           + z^{s⁺}·∫_{Ioi z} c(t) t^{-2m/α-1} dt )`

with `s⁻ = -(2m+5)/α`, `s⁺ = 2m/α`, `K = 1/(α(4m+5))`.

Here we prove that it (and its first derivative) is differentiable at every `z > 0`, under the same
integrability hypotheses as `radGreenI_solves` (`Radial/radGreenIntended.lean`).

The proof is the differentiability half of the argument of `radGreenI_solves`, which is carried out
there with `private` scaffolding; the scaffolding is rebuilt here (publicly, under the `rgi*` names)
so that the two differentiability statements can be extracted:

* `rgiA` is differentiable on `(0,∞)` with `HasDerivAt (rgiA) (rgiF1 z) z` (the fundamental theorem
  of calculus for a named interval integral), and `rgiB` with `HasDerivAt (rgiB) (-(rgiF2 z)) z`
  (the tail-integral version of the FTC);
* hence `radGreenI α m c` has derivative `rgiD1 α m c z` at every `z > 0` — the sum of the two
  `c`-terms of the product rule cancels because `z^{s⁻}·z^{(2m+5)/α-1} = 1/z = z^{s⁺}·z^{-2m/α-1}`;
* `rgiD1 α m c` is itself differentiable on `(0,∞)`, since it is built from `z^{s⁻-1}`, `z^{s⁺-1}`
  (differentiable at `z ≠ 0`) and the differentiable functions `rgiA`, `rgiB`;
* finally `deriv (radGreenI α m c) =ᶠ[𝓝 z] rgiD1 α m c`, so `deriv (radGreenI α m c)` is
  differentiable at `z`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.Radial.radGreenIntended
import Submission.Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi
import Submission.Work.FTS.PhiStar.Radial.intervalIntegrable_of_Ioi_Ioo
import Submission.Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

open Work.FTS.PhiStar.Radial (hasDerivAt_integral_Ioi intervalIntegrable_of_Ioi_Ioo
  integrableOn_Ioi_of_Ioi_Ioo)

/-! ### Scaffolding: the two integrals whose combination is `radGreenI` -/

/-- The decaying indicial exponent `s⁻ = -(2m+5)/α`. -/
def rgiSn (α : ℝ) (m : ℕ) : ℝ := -(2 * (m : ℝ) + 5) / α

/-- The growing indicial exponent `s⁺ = 2m/α`. -/
def rgiSp (α : ℝ) (m : ℕ) : ℝ := 2 * (m : ℝ) / α

/-- The normalising constant `1/(α(4m+5))`. -/
def rgiK (α : ℝ) (m : ℕ) : ℝ := 1 / (α * (4 * (m : ℝ) + 5))

/-- The integrand of the `0..z` integral. -/
def rgiF1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)

/-- The integrand of the `Ioi z` integral. -/
def rgiF2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * t ^ (-(2 * (m : ℝ) / α) - 1)

/-- The interval integral `∫₀^z c t t^{(2m+5)/α-1} dt`. -/
def rgiA (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in (0 : ℝ)..z, rgiF1 α m c t

/-- The tail integral `∫_{Ioi z} c t t^{-2m/α-1} dt`. -/
def rgiB (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in Set.Ioi z, rgiF2 α m c t

/-- The formula for the derivative of `radGreenI`. -/
def rgiD1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  rgiK α m * ((rgiSn α m * y ^ (rgiSn α m - 1)) * rgiA α m c y
    + (rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y)

/-- `radGreenI` written with the scaffolding names of this file (definitional). -/
lemma radGreenI_eq_rgi (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    Work.FTS.PhiStar.Radial.radGreenI α m c
      = fun z => rgiK α m * (z ^ (rgiSn α m) * rgiA α m c z
        + z ^ (rgiSp α m) * rgiB α m c z) := by
  funext z
  rfl

/-! ### Continuity and differentiability of the two integrals -/

lemma rgiF1_continuousOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0)) :
    ContinuousOn (rgiF1 α m c) (Set.Ioi 0) :=
  hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))

lemma rgiF2_continuousOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0)) :
    ContinuousOn (rgiF2 α m c) (Set.Ioi 0) :=
  hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))

/-- Fundamental theorem of calculus: `rgiA` is differentiable on `(0,∞)` with derivative `rgiF1`. -/
lemma rgiA_hasDerivAt {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rgiA α m c) (rgiF1 α m c z) z := by
  intro z hz
  have hF : ContinuousOn (rgiF1 α m c) (Set.Ioi 0) := rgiF1_continuousOn hc
  have hsm : StronglyMeasurableAtFilter (rgiF1 α m c) (𝓝 z) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hF z hz
  exact intervalIntegral.integral_hasDerivAt_right (a := 0) (b := z)
    (intervalIntegrable_of_Ioi_Ioo hz hF h0) hsm (hF.continuousAt (Ioi_mem_nhds hz))

/-- Fundamental theorem of calculus for the tail integral: `rgiB` is differentiable on `(0,∞)`
with derivative `-(rgiF2 ·)`. -/
lemma rgiB_hasDerivAt {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rgiB α m c) (-(rgiF2 α m c z)) z := by
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  have hF : ContinuousOn (rgiF2 α m c) (Set.Ioi 0) := rgiF2_continuousOn hc
  have hz2 : 0 < z / 2 := by linarith
  exact hasDerivAt_integral_Ioi (f := rgiF2 α m c) (a := z / 2) (z := z) (by linarith)
    (hF.mono (fun t ht => by simp only [Set.mem_Ioi] at ht ⊢; linarith))
    (integrableOn_Ioi_of_Ioi_Ioo hz2 hF hinf)

/-! ### The derivative of `radGreenI` -/

/-- **`radGreenI` is differentiable on `(0,∞)`**, with the explicit derivative `rgiD1`. -/
lemma hasDerivAt_radGreenI {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.FTS.PhiStar.Radial.radGreenI α m c) (rgiD1 α m c z) z := by
  intro z hz
  have hy0 : (0 : ℝ) < z := hz
  have hyne : z ≠ 0 := ne_of_gt hy0
  have hA := rgiA_hasDerivAt (α := α) (m := m) (c := c) hc h0 z hz
  have hB := rgiB_hasDerivAt (α := α) (m := m) (c := c) hc hinf z hz
  have hp1 : HasDerivAt (fun t : ℝ => t ^ (rgiSn α m))
      (rgiSn α m * z ^ (rgiSn α m - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hyne)
  have hp2 : HasDerivAt (fun t : ℝ => t ^ (rgiSp α m))
      (rgiSp α m * z ^ (rgiSp α m - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hyne)
  have hm1 : HasDerivAt (fun t : ℝ => t ^ (rgiSn α m) * rgiA α m c t)
      ((rgiSn α m * z ^ (rgiSn α m - 1)) * rgiA α m c z
        + z ^ (rgiSn α m) * rgiF1 α m c z) z := hp1.mul hA
  have hm2 : HasDerivAt (fun t : ℝ => t ^ (rgiSp α m) * rgiB α m c t)
      ((rgiSp α m * z ^ (rgiSp α m - 1)) * rgiB α m c z
        + z ^ (rgiSp α m) * (-(rgiF2 α m c z))) z := hp2.mul hB
  have h3 : HasDerivAt (fun t : ℝ => rgiK α m *
        (t ^ (rgiSn α m) * rgiA α m c t + t ^ (rgiSp α m) * rgiB α m c t))
      (rgiK α m * (((rgiSn α m * z ^ (rgiSn α m - 1)) * rgiA α m c z
            + z ^ (rgiSn α m) * rgiF1 α m c z)
          + ((rgiSp α m * z ^ (rgiSp α m - 1)) * rgiB α m c z
            + z ^ (rgiSp α m) * (-(rgiF2 α m c z))))) z :=
    (hm1.add hm2).const_mul (rgiK α m)
  -- the two `c`-terms of the product rule cancel
  have hcs1 : z ^ (rgiSn α m) * rgiF1 α m c z = c z / z := by
    have he : (2 * (m : ℝ) + 5) / α - 1 = -1 - (-(2 * (m : ℝ) + 5) / α) := by ring
    have hf : rgiF1 α m c z = c z * z ^ (-1 - rgiSn α m) := by
      simp only [rgiF1, rgiSn]; rw [he]
    calc z ^ (rgiSn α m) * rgiF1 α m c z
        = z ^ (rgiSn α m) * (c z * z ^ (-1 - rgiSn α m)) := by rw [hf]
      _ = c z * (z ^ (rgiSn α m) * z ^ (-1 - rgiSn α m)) := by ring
      _ = c z * z ^ (-(1 : ℝ)) := by
            have hExp : rgiSn α m + (-1 - rgiSn α m) = -(1 : ℝ) := by ring
            rw [← Real.rpow_add hy0, hExp]
      _ = c z / z := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hcs2 : z ^ (rgiSp α m) * rgiF2 α m c z = c z / z := by
    have he : -(2 * (m : ℝ) / α) - 1 = -1 - (2 * (m : ℝ) / α) := by ring
    have hf : rgiF2 α m c z = c z * z ^ (-1 - rgiSp α m) := by
      simp only [rgiF2, rgiSp]; rw [he]
    calc z ^ (rgiSp α m) * rgiF2 α m c z
        = z ^ (rgiSp α m) * (c z * z ^ (-1 - rgiSp α m)) := by rw [hf]
      _ = c z * (z ^ (rgiSp α m) * z ^ (-1 - rgiSp α m)) := by ring
      _ = c z * z ^ (-(1 : ℝ)) := by
            have hExp : rgiSp α m + (-1 - rgiSp α m) = -(1 : ℝ) := by ring
            rw [← Real.rpow_add hy0, hExp]
      _ = c z / z := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hval : rgiK α m * (((rgiSn α m * z ^ (rgiSn α m - 1)) * rgiA α m c z
            + z ^ (rgiSn α m) * rgiF1 α m c z)
          + ((rgiSp α m * z ^ (rgiSp α m - 1)) * rgiB α m c z
            + z ^ (rgiSp α m) * (-(rgiF2 α m c z)))) = rgiD1 α m c z := by
    simp only [rgiD1]
    rw [mul_neg, hcs1, hcs2]
    ring
  rw [radGreenI_eq_rgi]
  exact h3.congr_deriv hval

/-- **The derivative `rgiD1` of `radGreenI` is itself differentiable on `(0,∞)`.** -/
lemma rgiD1_differentiableAt {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (rgiD1 α m c) z := by
  intro z hz
  have hzne : z ≠ 0 := ne_of_gt hz
  have hA : DifferentiableAt ℝ (rgiA α m c) z :=
    (rgiA_hasDerivAt (α := α) (m := m) (c := c) hc h0 z hz).differentiableAt
  have hB : DifferentiableAt ℝ (rgiB α m c) z :=
    (rgiB_hasDerivAt (α := α) (m := m) (c := c) hc hinf z hz).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y : ℝ => rgiSn α m * y ^ (rgiSn α m - 1)) z :=
    ((Real.hasDerivAt_rpow_const (x := z) (p := rgiSn α m - 1) (Or.inl hzne)).const_mul
      (rgiSn α m)).differentiableAt
  have h2 : DifferentiableAt ℝ (fun y : ℝ => rgiSp α m * y ^ (rgiSp α m - 1)) z :=
    ((Real.hasDerivAt_rpow_const (x := z) (p := rgiSp α m - 1) (Or.inl hzne)).const_mul
      (rgiSp α m)).differentiableAt
  exact ((h1.mul hA).add (h2.mul hB)).const_mul (rgiK α m)

/-! ### The target -/

theorem radGreenI_differentiableAt {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (Work.FTS.PhiStar.Radial.radGreenI α m c) z ∧
        DifferentiableAt ℝ (deriv (Work.FTS.PhiStar.Radial.radGreenI α m c)) z := by
  have _hαne : α ≠ 0 := ne_of_gt hα
  intro z hz
  refine ⟨(hasDerivAt_radGreenI (α := α) (m := m) (c := c) hc h0 hinf z hz).differentiableAt,
    ?_⟩
  have heq : deriv (Work.FTS.PhiStar.Radial.radGreenI α m c) =ᶠ[𝓝 z] rgiD1 α m c :=
    eventually_of_mem (Ioi_mem_nhds hz)
      (fun y hy => (hasDerivAt_radGreenI (α := α) (m := m) (c := c) hc h0 hinf y hy).deriv)
  exact (heq.differentiableAt_iff).mpr
    (rgiD1_differentiableAt (α := α) (m := m) (c := c) hc h0 hinf z hz)

end Work.FTS.PhiStar.Series
