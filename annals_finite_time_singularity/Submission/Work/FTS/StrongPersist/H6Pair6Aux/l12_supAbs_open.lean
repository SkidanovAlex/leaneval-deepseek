/-
# `l12_supAbs_open` — the *uniform* (in `z ≥ 0`) bound `|L₁₂(g)(z)| ≤ 3 |g|_{ℋ⁴}`

`Work.Construction.L12 g z = ∫_{r > z} L₁₂dens(g)(r) dr` is the tail integral of the angular
density `L₁₂dens(g)(r) = ∫_θ K(θ) g(r,θ)/r dθ`.  The companion field
`Work.FTS.OpenPkg.l12zero_field` bounds the *zero mode* `|L₁₂(g)(0)| ≤ 3|g|_{ℋ⁴}`; here we need
the same constant `3` for **every** `z ≥ 0`, in the same open-quadrant class
(`SmoothOpen g` ⟹ `g` continuous on the open quadrant, no regularity through `z = 0`) with only
`HkMem α 4 g`.

The estimate is Cauchy–Schwarz on the tail `(z,∞)`, and — this is the point — the numeric
constant does not deteriorate as `z` grows, because the tail weight `r ↦ 1/(1+r)` only gets
*smaller*:

* slicewise (`∀ r > 0`), `|L₁₂dens(g)(r)|² ≤ 3 (∫_θ g(r,θ)²)/r²`
  (`Work.Coercivity.L12dens_sq_slice`, Cauchy–Schwarz against `K ∈ L²(Iθ)`, `∫_θ K = 1`);
* the Hardy weighted angular energy is dominated by the `ℋ⁴`-majorant,
  `(∫_θ g(r,θ)²)·((1+r)/r)² ≤ ∫_θ HkIntegrand α 4 g r θ` (`phiWeight_slice_le`), which turns the
  slicewise bound into `|L₁₂dens(g)(r)| ≤ √(3 Φ r)/(1+r)`, `Φ r = ∫_θ HkIntegrand α 4 g r θ`;
* `CS1D` on `(z,∞)` against `A r = √(3 Φ r)`, `B r = 1/(1+r)`, with
  `∫_{(z,∞)} A² ≤ 3 HkSq α 4 g` (monotone set integral, `HkIntegrand ≥ 0`) and
  `∫_{(z,∞)} B² ≤ ∫_{(0,∞)} B² ≤ 2` (`InvOneAddSq`) gives
  `|L₁₂(g)(z)| ≤ √6 · |g|_{ℋ⁴} ≤ 3 |g|_{ℋ⁴}`.

The two integrability/measurability hypotheses of `CS1D` come from `HkMem α 4 g` (for `A`) and
from `InvOneAddSq` (for `B`); no measurability of the angular energy itself is needed, because
`A` is built from the *integrable* majorant `Φ`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.OpenPkg.l12zero_field

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

/-- The `ℋ^k`-integrand is a sum of squares, hence nonnegative. -/
lemma l12sup_hkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand]
  refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split
  · exact sq_nonneg _
  · exact le_refl 0

/-- The squared `ℋ^k`-norm is nonnegative. -/
lemma l12sup_hkSq_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq]
  exact integral_nonneg fun z => integral_nonneg fun θ => l12sup_hkIntegrand_nonneg α k f z θ

/-- **The pointwise slice bound.**  For `r > 0`, an integrable angular slice `θ ↦ f(r,θ)²` on
`Iθ`, and any `Φ` dominating the Hardy weighted angular energy
`(∫_θ f(r,θ)²)·((1+r)/r)² ≤ Φ` (which is the statement of `phiWeight_slice_le` for `Φ` the
`HkIntegrand`-slice), the `L₁₂`-density at `r` satisfies

`|L₁₂dens(f)(r)| ≤ √(3Φ)/(1+r)`.

The two Cauchy–Schwarz steps are `L12dens_sq_slice` (in `θ`) and the relation
`√(φ·((1+r)/r)²) ≤ √Φ` (which is exactly `Φ ≥ φ(1+r)²/r²`, i.e. the comparison of the Hardy
weight with the `ρ²`-weight of the `ℋ⁴`-norm). -/
lemma l12sup_dens_le {f : ℝ → ℝ → ℝ} {r Φ : ℝ} (hr : 0 < r)
    (hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f r θ) ^ 2) Work.Spaces.Iθ)
    (hW : (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤ Φ) :
    |Work.FM.L12dens Work.Spaces.K f r| ≤ Real.sqrt (3 * Φ) * (1 / (1 + r)) := by
  have hφ0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2 := integral_nonneg fun θ => sq_nonneg _
  have hΦ0 : 0 ≤ Φ := le_trans (mul_nonneg hφ0 (sq_nonneg _)) hW
  have hsq : (Work.FM.L12dens Work.Spaces.K f r) ^ 2
      ≤ 3 * (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) / r ^ 2 :=
    Work.Coercivity.L12dens_sq_slice f Work.Coercivity.integral_Itheta_K hr hsl
  have hb : |Work.FM.L12dens Work.Spaces.K f r|
      ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) / r :=
    Work.FTS.H2.abs_le_sqrt_three_mul_sqrt_div hr hφ0 hsq
  refine hb.trans ?_
  have hkey1 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r)
      ≤ Real.sqrt Φ := by
    have hsqφ : (Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r)) ^ 2
        = (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hφ0]
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r)
        = Real.sqrt ((Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r)) ^ 2) :=
          (Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg (by linarith) hr.le))).symm
      _ = Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) := by rw [hsqφ]
      _ ≤ Real.sqrt Φ := Real.sqrt_le_sqrt hW
  have hkey2 : Real.sqrt 3 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r))
      ≤ Real.sqrt (3 * Φ) := by
    have h := mul_le_mul_of_nonneg_left hkey1 (Real.sqrt_nonneg 3)
    rwa [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) Φ] at h
  calc Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) / r
      = Real.sqrt 3 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r))
          * (1 / (1 + r)) := by
        have hr0 : r ≠ 0 := ne_of_gt hr
        have h1r : (1 : ℝ) + r ≠ 0 := by positivity
        field_simp
    _ ≤ Real.sqrt (3 * Φ) * (1 / (1 + r)) :=
        mul_le_mul_of_nonneg_right hkey2 (by positivity)

/-- **The uniform `L₁₂` bound in the open-quadrant class.**  For `SmoothOpen g` (interior
smoothness on the open quadrant) and `HkMem α 4 g`, the tail integral of the `L₁₂` density is
bounded by `3|g|_{ℋ⁴}` for every `z ≥ 0` — the zero-mode constant of
`Work.FTS.OpenPkg.l12zero_field`, valid uniformly in the radial variable.

See the module docstring for the proof: Cauchy–Schwarz on the tail `(z,∞)` against the
`ℋ⁴`-majorant `Φ` and the *decreasing* tail weight `1/(1+r)`, for which
`∫_{(z,∞)} 1/(1+r)² ≤ 2` requires `z ≥ 0`. -/
theorem l12_supAbs_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g := by
  intro z hz
  -- the tail `(z,∞)` sits inside the domain `Iz = [0,∞)` because `z ≥ 0`
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := by
    intro r hr
    rw [Work.Spaces.Iz]
    exact le_trans hz (le_of_lt (Set.mem_Ioi.mp hr))
  have hΦnn : ∀ r : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r => integral_nonneg fun θ => l12sup_hkIntegrand_nonneg α 4 g r θ
  -- the `ℋ⁴`-majorant is integrable on the tail
  have hΦint : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) (Set.Ioi z) :=
    hmem.2.mono_set hsub
  -- `A = √(3Φ)` is a.e. strongly measurable (it is the composition of the integrable `3Φ`
  -- with the continuous `√`) …
  have hAmeas : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ))
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable (hΦint.aestronglyMeasurable.const_mul 3)
  have hAcongr : (fun r : ℝ => 3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)]
      (fun r : ℝ =>
        Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) ^ 2) :=
    Filter.Eventually.of_forall fun r => (Real.sq_sqrt (mul_nonneg (by norm_num) (hΦnn r))).symm
  -- … and `A² = 3Φ` is integrable
  have hA2int : MeasureTheory.Integrable
      (fun r : ℝ =>
        Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi z)) := (hΦint.const_mul 3).congr hAcongr
  have hAmem : MeasureTheory.MemLp
      (fun r : ℝ => Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)) 2
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAmeas).mpr hA2int
  -- the tail weight `B = 1/(1+r)` is in `L²(z,∞)` (by monotonicity from `InvOneAddSq`)
  have hBint : MeasureTheory.IntegrableOn (fun r : ℝ => (1 / (1 + r)) ^ 2) (Set.Ioi z) :=
    (Work.FTS.H2.InvOneAddSq).1.mono_set (Set.Ioi_subset_Ioi hz)
  have hBmeas : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => 1 / (1 + r))
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    (by fun_prop : Measurable fun r : ℝ => 1 / (1 + r)).aestronglyMeasurable
  have hBmem : MeasureTheory.MemLp (fun r : ℝ => 1 / (1 + r)) 2
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBmeas).mpr hBint
  have hr_mem : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi z)), r ∈ Set.Ioi z :=
    MeasureTheory.ae_restrict_mem measurableSet_Ioi
  -- the two slicewise inputs, a.e. on the tail
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi z)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => (g r θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun r hr =>
      Work.FTS.OpenPkg.l12zero_slice_sq_integrableOn α hso hmem
        (lt_of_le_of_lt hz (Set.mem_Ioi.mp hr))
  have hWmem : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi z)),
      (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) * ((1 + r) / r) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun r hr =>
      Work.FTS.H2.L12Q.phiWeight_slice_le α g hmem r (lt_of_le_of_lt hz (Set.mem_Ioi.mp hr))
  -- the pointwise bound `|L₁₂dens(g)(r)| ≤ A(r)·B(r)`
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi z)),
      |Work.FM.L12dens Work.Spaces.K g r|
        ≤ Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
          * (1 / (1 + r)) := by
    filter_upwards [hr_mem, hsl, hWmem] with r hr hslr hWr
    exact l12sup_dens_le (lt_of_le_of_lt hz (Set.mem_Ioi.mp hr)) hslr hWr
  -- Cauchy–Schwarz on the tail
  have hcs := Work.FTS.H2.CS1D hAmem hBmem
    (Filter.Eventually.of_forall fun r => Real.sqrt_nonneg _)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun r hr =>
      div_nonneg zero_le_one (by have h := Set.mem_Ioi.mp hr; linarith))
    hbd
  -- the two `L²`-norms: `∫_{(z,∞)} 3Φ ≤ 3 HkSq α 4 g` and `∫_{(z,∞)} B² ≤ 2`
  have hIntΦ : ∫ r in Set.Ioi z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      ≤ Work.Spaces.HkSq α 4 g := by
    have hmono := MeasureTheory.setIntegral_mono_set hmem.2
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun r _ => hΦnn r)
      (Filter.Eventually.of_forall fun x hx => hsub hx)
    exact hmono
  have hA2le : ∫ r, Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) ^ 2
        ∂(MeasureTheory.volume.restrict (Set.Ioi z)) ≤ 3 * Work.Spaces.HkSq α 4 g := by
    have h1 : ∫ r, Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) ^ 2
          ∂(MeasureTheory.volume.restrict (Set.Ioi z))
        = ∫ r, 3 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
          ∂(MeasureTheory.volume.restrict (Set.Ioi z)) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r =>
        Real.sq_sqrt (mul_nonneg (by norm_num) (hΦnn r)))
    rw [h1, MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hIntΦ (by norm_num)
  have hB2le : ∫ r, (1 / (1 + r)) ^ 2 ∂(MeasureTheory.volume.restrict (Set.Ioi z)) ≤ 2 := by
    have hmono := MeasureTheory.setIntegral_mono_set (Work.FTS.H2.InvOneAddSq).1
      (Filter.Eventually.of_forall fun r => sq_nonneg (1 / (1 + r)))
      (Filter.Eventually.of_forall fun x hx => Set.Ioi_subset_Ioi hz hx)
    exact hmono.trans (Work.FTS.H2.InvOneAddSq).2
  have hLHS : (∫ r, Work.FM.L12dens Work.Spaces.K g r
      ∂(MeasureTheory.volume.restrict (Set.Ioi z))) = Work.Construction.L12 g z := rfl
  have hstep1 : |Work.Construction.L12 g z|
      ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 g) * Real.sqrt 2 := by
    rw [← hLHS]
    exact hcs.trans (mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hB2le)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  -- `√(3 HkSq)·√2 = √6·|g|_{ℋ⁴} ≤ 3|g|_{ℋ⁴}`
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hsqXn : Work.Spaces.HkSq α 4 g = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Real.sq_sqrt (l12sup_hkSq_nonneg α 4 g)).symm
  calc |Work.Construction.L12 g z|
      ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 g) * Real.sqrt 2 := hstep1
    _ = Real.sqrt 6 * Work.FTS.Nonlin.Xn α g := by
        have h6 : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
          rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (2 : ℝ)]
          norm_num
        rw [hsqXn, Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num)
          ((Work.FTS.Nonlin.Xn α g) ^ 2), Real.sqrt_sq hXn0, h6]
        ring
    _ ≤ 3 * Work.FTS.Nonlin.Xn α g := by
        refine mul_le_mul_of_nonneg_right ?_ hXn0
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]

end Work.FTS.StrongPersist.H6Pair6Aux
