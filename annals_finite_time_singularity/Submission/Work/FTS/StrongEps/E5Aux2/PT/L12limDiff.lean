/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PT.L12limDiff` — the `z`-differentiability of `L₁₂` of the *limit* profile

The pointwise convergence `prof_pt_tendsto` needs `DifferentiableAt ℝ (fun z' => L₁₂(F)(z')) z`
for the **limit** profile `F = F_* + slice g s`: the identity

  `pz (PhiTil α F Φ) z θ = pz Φ z θ − (1/(4α))·sin(2θ)·∂_z L₁₂(F)(z)`

is an instance of `deriv_sub`, which needs differentiability of *both* summands.

The hypotheses of the target do **not** give smoothness of the limit slice (it is only `C⁴` on
the open quadrant, with an `ℋ⁶`-bound that need not be honest), so `Work.FTS.StrongPersist…L12add`
(which needs `SmoothOpen` + `HkMem α 4`) is *not* applicable.  What *is* available is the
approximating family: the projected slices `w n` are class-`C`, so `L₁₂(F_* + w n)` is
differentiable with derivative `−L₁₂dens (F_* + w n)`, and the densities are uniformly bounded and
uniformly Lipschitz (the `θ`-integral of a class-`C` profile).  Hence
`RXR1.hasDerivAt_of_tendsto_deriv` applies: *pointwise* convergence of `L₁₂(F_* + w n)` (a
hypothesis of the target, `hL12F`) plus locally uniform convergence of the derivatives (from the
uniform Lipschitz bounds) gives differentiability of the limit.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E5Aux2.PT.Basic
import Submission.Work.FTS.StrongEps.E5Aux2.PT.L12densFstar_deriv
import Submission.Work.FTS.StrongEps.E5Aux2.PT.L12densFstar_fam_bounds
import Submission.Work.FTS.StrongEps.E5Aux2.PT.L12densFstar_tendsto
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed
import Submission.Work.FTS_RegExport.RXR1.hasDerivAt_of_tendsto_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2.PT

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The perturbed full profile `F_* + w` of the modulation. -/
def Fadd (α : ℝ) (w : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Fstar α z θ + w z θ

/-- The `L₁₂`-marginal of `F_* + w`. -/
def L12F (α : ℝ) (w : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun x => Work.Construction.L12 (Fadd α w) x

/-- The `L₁₂`-density of `F_* + w`. -/
def densF (α : ℝ) (w : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun x => Work.Construction.L12dens (Fadd α w) x

/-- The θ-slice of a function which is `C¹` on the open quadrant is a.e. strongly measurable for
`volume.restrict Iθ`. -/
theorem aestronglyMeasurable_slice_of_contDiffOn_one {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w) {x : ℝ} (hx : 0 < x) :
    MeasureTheory.AEStronglyMeasurable (fun θ => w x θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hcontQ : ContinuousOn (Function.uncurry w) Work.FTS.EllipticEst.Q0 :=
    (hsm.forall 1).continuousOn
  have h2 : ContinuousOn (fun θ : ℝ => (x, θ)) (Set.Ioo 0 (π / 2)) :=
    (Continuous.prodMk_right x).continuousOn
  have hcomp : ContinuousOn (fun θ : ℝ => Function.uncurry w (x, θ)) (Set.Ioo 0 (π / 2)) :=
    hcontQ.comp h2 fun θ hθ => ⟨hx, hθ.1, hθ.2⟩
  have hslice : ContinuousOn (fun θ => w x θ) (Set.Ioo 0 (π / 2)) := hcomp
  have hae : AEMeasurable (fun θ => w x θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
    hslice.aemeasurable measurableSet_Ioo
  have hEq : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc)).symm
  rw [hEq]
  exact hae.aestronglyMeasurable

/-- **The `z`-differentiability of `L₁₂` of the limit profile.**

If the projected slices `w n` are class-`C` with a uniform `ℋ⁶`-bound `B`, converge pointwise on
the open quadrant to `W`, and if the `L₁₂`-marginals of `F_* + w n` converge pointwise to that of
`F_* + W` (the hypothesis `hL12F` of `prof_pt_tendsto`), then `L₁₂(F_* + W)` is differentiable at
`z > 0` with derivative `−L₁₂dens (F_* + W)(z)`. -/
theorem L12_add_lim_hasDerivAt {α B : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {w : ℕ → ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ}
    (hwC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α (w n))
    (hwB : ∀ n : ℕ, Work.FTS.StrongGlobal.Xn6 α (w n) ≤ B)
    (hwconv : ∀ (z θ : ℝ), (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => w n z θ) Filter.atTop (nhds (W z θ)))
    (hL12F : ∀ x ∈ Set.Ioi (0 : ℝ),
      Filter.Tendsto (fun n : ℕ => Work.Construction.L12
          (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x) Filter.atTop
        (nhds (Work.Construction.L12
          (fun z θ => Work.Construction.Fstar α z θ + W z θ) x)))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x => Work.Construction.L12
        (fun z θ => Work.Construction.Fstar α z θ + W z θ) x)
      (-(Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + W z θ) z)) z := by
  -- the uniform pointwise bound on the low slots of the approximants
  have hbd0 : ∀ (n : ℕ) (x θ : ℝ), (x, θ) ∈ Work.Construction.Qd → |w n x θ| ≤
      10 / Real.sqrt (Work.Spaces.gam α - 1) * B := by
    intro n x θ hxθ
    simpa using classC_mixed_sup_le_of_Xn6 hα (hwC n) (hwB n) (b := 0) (a := 0) (by norm_num) hxθ
  have hbd1 : ∀ (n : ℕ) (x θ : ℝ), (x, θ) ∈ Work.Construction.Qd → |Work.Spaces.Dz (w n) x θ| ≤
      10 / Real.sqrt (Work.Spaces.gam α - 1) * B := by
    intro n x θ hxθ
    simpa [Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_succ,
      Work.Spaces.DzIter_zero] using
      classC_mixed_sup_le_of_Xn6 hα (hwC n) (hwB n) (b := 1) (a := 0) (by norm_num) hxθ
  -- the two families
  have hder : ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun y => Work.Construction.L12
          (fun z θ => Work.Construction.Fstar α z θ + w n z θ) y)
        (-(Work.Construction.L12dens
          (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x)) x := by
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hmem : Work.Spaces.HkMem α 4 (w n) :=
      Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) (hwC n).reg (hwC n).mem
    have hint : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ)) (Set.Ioi 0) :=
      Work.FTS.MeridianDyn.Bridge.integrableOn_L12dens_Fstar_add hα.1 hα.2 (hwC n).reg hmem
    have hcont : ContinuousAt (Work.FM.L12dens Work.Spaces.K
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ)) x :=
      Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_Fstar_add hα.1 hα.2 (hwC n).reg hmem hx0
    have h := Work.FM.hasDerivAt_L12 (K := Work.Spaces.K)
      (f := fun z θ => Work.Construction.Fstar α z θ + w n z θ) (a := 0) (ρ := x)
      hint hcont hx0
    simpa only [Work.Construction.L12, Work.Construction.L12dens] using h
  -- differentiability of the densities (from the derivative formula)
  have hvdiff : ∀ n : ℕ, DifferentiableOn ℝ
      (fun x => -(Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x))
      (Set.Ioo (z / 2) (2 * z)) := by
    intro n
    refine DifferentiableOn.neg fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have h := (L12densFstar_deriv (α := α) (C₁ := 10 / Real.sqrt (Work.Spaces.gam α - 1) * B)
      (C₂ := 10 / Real.sqrt (Work.Spaces.gam α - 1) * B) hα.1 (hwC n).reg (hbd0 n) (hbd1 n)).1 x hx0
    exact h.differentiableAt.differentiableWithinAt
  -- the uniform bounds
  have hfam := L12densFstar_fam_bounds (α := α)
    (C₁ := 10 / Real.sqrt (Work.Spaces.gam α - 1) * B)
    (C₂ := 10 / Real.sqrt (Work.Spaces.gam α - 1) * B) hα
    (fun n => (hwC n).reg) hbd0 hbd1
  obtain ⟨M, hM0, hM⟩ := hfam.1
  obtain ⟨Lv, hL0, hLv⟩ := hfam.2
  have hMz : (0 : ℝ) < z / 2 := by linarith
  have hM' : ∃ M' : ℝ, 0 ≤ M' ∧ ∀ (n : ℕ), ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |-(Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x)| ≤ M' := by
    refine ⟨M * (1 + 1 / (z / 2)), by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have h1 : |Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x| ≤ M * (1 + 1 / x) := hM n x hx0
    have h2 : (1 : ℝ) + 1 / x ≤ 1 + 1 / (z / 2) := by
      have h3 : 1 / (z / 2) ≥ 1 / x := one_div_le_one_div_of_le hMz (by linarith [hx.1])
      linarith
    calc |-(Work.Construction.L12dens
          (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x)|
        = |Work.Construction.L12dens
            (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x| := abs_neg _
      _ ≤ M * (1 + 1 / x) := h1
      _ ≤ M * (1 + 1 / (z / 2)) := mul_le_mul_of_nonneg_left h2 hM0.le
  have hL' : ∃ L' : ℝ, 0 ≤ L' ∧ ∀ (n : ℕ), ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |deriv (fun x => -(Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x)) x| ≤ L' := by
    refine ⟨Lv * (1 + 1 / (z / 2) ^ 2), by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hdv : deriv (fun x => -(Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x)) x
        = -(deriv (fun x => Work.Construction.L12dens
            (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x) x) := by
      have h := (L12densFstar_deriv (α := α) (C₁ := 10 / Real.sqrt (Work.Spaces.gam α - 1) * B)
        (C₂ := 10 / Real.sqrt (Work.Spaces.gam α - 1) * B) hα.1 (hwC n).reg (hbd0 n)
        (hbd1 n)).1 x hx0
      rw [h.deriv]
      exact h.neg.deriv
    have h1 : |deriv (fun x => Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x) x| ≤ Lv * (1 + 1 / x ^ 2) :=
      hLv n x hx0
    have h2 : (1 : ℝ) + 1 / x ^ 2 ≤ 1 + 1 / (z / 2) ^ 2 := by
      have h3 : 1 / x ^ 2 ≤ 1 / (z / 2) ^ 2 := by
        apply one_div_le_one_div_of_le (pow_pos hMz 2)
        exact pow_le_pow_left₀ (by linarith [hx.1]) (by linarith [hx.1]) 2
      linarith
    rw [hdv, abs_neg]
    calc |deriv (fun x => Work.Construction.L12dens
          (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x) x|
        ≤ Lv * (1 + 1 / x ^ 2) := h1
      _ ≤ Lv * (1 + 1 / (z / 2) ^ 2) := mul_le_mul_of_nonneg_left h2 hL0.le
  -- convergence of the densities
  have hv : ∀ x ∈ Set.Ioo (z / 2) (2 * z), Filter.Tendsto
      (fun n : ℕ => -(Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x)) Filter.atTop
      (nhds (-(Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + W z θ) x))) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (fun θ => w n x θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      fun n => aestronglyMeasurable_slice_of_contDiffOn_one (hwC n).reg hx0
    exact (L12densFstar_tendsto (α := α) (C := 10 / Real.sqrt (Work.Spaces.gam α - 1) * B)
      hα hbd0 hwconv hx0 hmeas).neg
  -- convergence of the marginals (the hypothesis `hL12F`)
  have hu : ∀ x ∈ Set.Ioo (z / 2) (2 * z), Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x) Filter.atTop
      (nhds (Work.Construction.L12
        (fun z θ => Work.Construction.Fstar α z θ + W z θ) x)) :=
    fun x hx => hL12F x (Set.mem_Ioi.mpr (by linarith [hx.1, hz]))
  have hmain := Work.FTS_RegExport.RXR1.hasDerivAt_of_tendsto_deriv
    (a := z / 2) (b := 2 * z)
    (u := fun n x => Work.Construction.L12
      (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x)
    (v := fun n x => -(Work.Construction.L12dens
      (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x))
    (φ := fun x => Work.Construction.L12
      (fun z θ => Work.Construction.Fstar α z θ + W z θ) x)
    (γ := fun x => -(Work.Construction.L12dens
      (fun z θ => Work.Construction.Fstar α z θ + W z θ) x))
    (by linarith) hder hvdiff hM' hL' hu hv z ⟨by linarith, by linarith⟩
  exact hmain

end Work.FTS.StrongEps.E5Aux2.PT
