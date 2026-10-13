import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of `(x, t) ↦ ρ t * a x * b (x - t)`

The product `ρ t * a x * b (x - t)` is integrable for the product of Lebesgue measures on
`ℝ³ × ℝ³` as soon as `ρ` and `b` are continuous with compact support (and `a` is merely
continuous).  The point is that the integrand *vanishes outside the compact set*

`K := (tsupport ρ + tsupport b) ×ˢ tsupport ρ`

(indeed `ρ t * a x * b (x - t) ≠ 0` forces `t ∈ tsupport ρ` and `x - t ∈ tsupport b`, whence
`x = t + (x - t) ∈ tsupport ρ + tsupport b`), so the integrand is a continuous function with
compact support and Mathlib's `Continuous.integrable_of_hasCompactSupport` applies.  No
boundedness assumption on `a` is needed: its argument is confined to `tsupport ρ + tsupport b`.

This is the lemma consumed by the pressure reconstruction: after the change of variables that
turns a convolution against the Newtonian kernel into an integral over `(x, t)`, the resulting
double integral has this exact shape.
-/

open MeasureTheory Function
open scoped Pointwise

namespace Work.FTS.PressureOn.Auxiliary

theorem integrable_uncurry_mul_sub (a b ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hρ : Continuous ρ)
    (hbc : HasCompactSupport b) (hρc : HasCompactSupport ρ) :
    MeasureTheory.Integrable
      (Function.uncurry fun (x t : EuclideanSpace ℝ (Fin 3)) => ρ t * a x * b (x - t))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  -- the integrand, packaged as a function of the pair `(x, t)`
  set K : Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
    (tsupport ρ + tsupport b) ×ˢ tsupport ρ with hKdef
  -- it is continuous
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ρ p.2 * a p.1 * b (p.1 - p.2)) :=
    ((hρ.comp continuous_snd).mul (ha.comp continuous_fst)).mul
      (hb.comp (continuous_fst.sub continuous_snd))
  -- and its support is contained in the compact set `K`
  have hsupp : Function.support (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ρ p.2 * a p.1 * b (p.1 - p.2)) ⊆ K := by
    intro p hp
    rw [Function.mem_support] at hp
    have hρne : ρ p.2 ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).1
    have hbne : b (p.1 - p.2) ≠ 0 := (mul_ne_zero_iff.mp hp).2
    have h2 : p.2 ∈ tsupport ρ := subset_tsupport ρ (Function.mem_support.mpr hρne)
    have h1 : p.1 - p.2 ∈ tsupport b := subset_tsupport b (Function.mem_support.mpr hbne)
    rw [hKdef]
    refine Set.mem_prod.mpr ⟨?_, h2⟩
    rw [Set.mem_add]
    exact ⟨p.2, h2, p.1 - p.2, h1, by abel⟩
  have hK : IsCompact K := by rw [hKdef]; exact IsCompact.add hρc hbc |>.prod hρc
  have hcs : HasCompactSupport (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ρ p.2 * a p.1 * b (p.1 - p.2)) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal hsupp hK.isClosed)
  exact hcont.integrable_of_hasCompactSupport hcs

end Work.FTS.PressureOn.Auxiliary
