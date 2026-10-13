/-
# `Work.FTS.StrongPersist.L3Rhs.N0gL12Sup` — `|L₁₂(f)(z)| ≤ C · |f|_{ℋ⁶}`, uniformly in `z ≥ 0`

`L₁₂(f)(z) = ∫_{s>z} ∫_θ K(θ)·f(s,θ)/s dθ ds` is the radial tail integral of the fundamental
model (`Work.Construction.L12 = Work.FM.L12 Work.Spaces.K`).  This module proves that it is
dominated, *uniformly in `z ≥ 0`*, by the `ℋ⁶`-norm of `f`:

  `∃ C > 0, ∀ α, ∀ f ∈ ℋ⁶_α, ∀ z ≥ 0, |L₁₂(f)(z)| ≤ C · |f|_{ℋ⁶_α}`

with an `α`-free constant `C = BK·√W2 + 1` (the same constant as the `z = 0` sibling
`Work.FTS.StrongPersist.L3Rhs.L3RhsL12zero` and the `k = 4` sibling
`Work.FTS.GalBasis.cc.abs_L12_le_HkNorm`).  The target `N0gL12Sup` is the instance
`k = 6`, `H6Adm α f`, in the vocabulary of this chapter (`Xn6 α f = HkNorm α 6 f`).

## The argument (Cauchy–Schwarz twice; the `z`-dependence is free)

Writing `Sw θ = sin(2θ)^{η/2}`, `Wlam s = s/(1+s)² = 1/(s·w s)` and
`Gaz f s θ = f s θ · w s / Sw θ`, the density integrand factorises as

  `K(θ)·f s θ/s = Wlam s · (K(θ)·Sw θ·Gaz f s θ)`   (`L12dens_eq_weighted`),

and `(Gaz f s θ)² = (D_z^0 f · w/sin(2θ)^{η/2})²` is the `i = 0` summand of `HkIntegrand α k f`.
Hence, with `BK = √(∫_θ (K·Sw)²)` and `A s = √(∫_θ HkIntegrand α k f s θ)`,

* **angular Cauchy–Schwarz**: `|∫_θ K·Sw·Gaz| ≤ BK · A s` for every `s > 0`, from
  `|Gaz| ≤ √(HkIntegrand)` (`Work.FTS.GalBasis.cc.abs_Gaz_le_sqrt_HkIntegrand_gen`) and the
  honest Cauchy–Schwarz inequality for the *measurable* functions `|K·Sw|` and
  `√(HkIntegrand)`;
* **radial Cauchy–Schwarz**: `∫_{s>z} Wlam·A ≤ √(∫_{s>z}Wlam²)·√(∫_{s>z}A²)`, and since
  `Ioi z ⊆ (0,∞)` and `Ioi z ⊆ Iz` (for `z ≥ 0`) the two factors are dominated by
  `√W2` and `√(HkSq α k f)` by the monotonicity of the set integral.

Both constants are finite, positive and independent of `α` (and of `f`): the `α`-quantifier of
the statement is inert except for the `H6Adm` hypothesis.

## Layout

* `Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen` — the angular step at arbitrary order `k`
  (colleague lemma; the `k = 4` sibling is `Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le`);
* `Work.FTS.GalBasis.cc.integral_abs_L12dens_le_Ioi` — the radial step on `Ioi z` for arbitrary
  `z ≥ 0` (colleague lemma; the `z = 0` siblings are
  `Work.FTS.GalBasis.cc.integral_abs_L12dens_le` and `L3Rhs.integral_abs_L12dens_le_zero`);
* `abs_L12dens_le_gen`, `abs_L12_le_HkNorm_at` — the pointwise and integrated bounds;
* `N0gL12Sup` — the target.

Every integrability issue is handled by `MeasureTheory.integral_undef` (a non-integrable
integral is `0`, which satisfies the bound, the right-hand side being nonnegative), so the only
hypothesis needed on `f` is `HkMem α k f` — no smoothness, no measurability of the slices.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gDecomp
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen
import Submission.Work.FTS.GalBasis.cc.integral_abs_L12dens_le_Ioi
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
import Submission.Work.Elliptic.L12densFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.GalBasis.cc (Gaz Sw Wlam BK W2 BK_nonneg Wlam_nonneg continuous_sw)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000


/-! ## The pointwise bound on the `L₁₂`-density -/

/-- The `L₁₂`-density is dominated by the radial weight times `BK` times the square root of the
angular marginal of the `ℋᵏ`-integrand. -/
private lemma abs_L12dens_le_gen (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k h) {s : ℝ} (hs : 0 < s) :
    |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h s θ)) := by
  rw [Work.FTS.GalBasis.cc.L12dens_eq_weighted h hs, abs_mul,
    abs_of_nonneg (Wlam_nonneg hs.le)]
  exact mul_le_mul_of_nonneg_left
    (Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen α k h (hmem.1 s hs.le)) (Wlam_nonneg hs.le)

/-! ## The main bound -/

/-- **`|L₁₂(h)(z)| ≤ (BK·√W2 + 1)·|h|_{ℋᵏ}`, uniformly in `z ≥ 0`.**  The constant is the one of
the siblings `L3RhsL12zero` (`z = 0`, `k = 0`) and `abs_L12_le_HkNorm` (`z = 0`, `k = 4`); the
proof is the same two Cauchy–Schwarz steps, with the radial integration restricted to `Ioi z`
(and `Wlam`, `A` made square-integrable there by restriction). -/
private theorem abs_L12_le_HkNorm_at {α : ℝ} {k : ℕ} {h : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k h) {z : ℝ} (hz : 0 ≤ z) :
    |Work.Construction.L12 h z| ≤ (BK * Real.sqrt W2 + 1) * Work.Spaces.HkNorm α k h := by
  have hL12 : Work.Construction.L12 h z
      = ∫ s in Set.Ioi z, Work.Construction.L12dens h s := rfl
  calc |Work.Construction.L12 h z|
      = |∫ s in Set.Ioi z, Work.Construction.L12dens h s| := by rw [hL12]
    _ ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens h s| := by
        simpa only [Real.norm_eq_abs] using
          (MeasureTheory.norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Ioi z))
            (f := fun s => Work.Construction.L12dens h s))
    _ ≤ BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α k h) :=
        Work.FTS.GalBasis.cc.integral_abs_L12dens_le_Ioi α k h hmem hz
          (fun s hs => abs_L12dens_le_gen α k h hmem (lt_of_le_of_lt hz (Set.mem_Ioi.mp hs)))
    _ = (BK * Real.sqrt W2) * Work.Spaces.HkNorm α k h := by rw [Work.Spaces.HkNorm]
    _ ≤ (BK * Real.sqrt W2 + 1) * Work.Spaces.HkNorm α k h := by
        have hx := Work.Spaces.HkNorm_nonneg α k h
        nlinarith [Real.sqrt_nonneg W2, BK_nonneg]

/-! ## The target -/

theorem N0gL12Sup : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.StrongPersist.H6Adm α f →
    ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.L12 f z| ≤ C * Work.FTS.StrongPersist.Xn6 α f := by
  refine ⟨BK * Real.sqrt W2 + 1, by nlinarith [BK_nonneg, Real.sqrt_nonneg W2], ?_⟩
  intro α _hα f haf z hz
  have hmem : Work.Spaces.HkMem α 6 f := haf.reg.2
  exact abs_L12_le_HkNorm_at (h := f) hmem (le_of_lt hz)

end Work.FTS.StrongPersist.L3Rhs
