import Mathlib
import Submission.Work.BoseBox.potAmbAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Measurability of the `potAmb` integrand

This file proves `Work.BoseBox.stronglyMeasurable_potIntegrandG`: the `(u,x)`-integrand
`(Ψ x)^2 · potBracketG N ℓ μ vK gK u x` of the potential half of the `C` node is strongly
measurable as soon as the two kernel *numerators* `vK`, `gK` are measurable and the state
`Ψ` is continuous.

The bracket is a finite sum of the one-body fibre integrals
`potBr ℓ gK u (x i) = ∫_y wLoc ℓ gK u (x i) y` and of the pair terms
`wLoc ℓ vK u (x p.1) (x p.2)`; both are handled by the corresponding measurability
closure properties.  The fibre integral is a parameter integral, so strong measurability
is `MeasureTheory.StronglyMeasurable.integral_prod_right'` applied to the (measurable)
uncurried integrand `((u,x),y) ↦ χ_u(x_i)·(gK(x_i−y)/(χ⋆χ)_ℓ(x_i−y))·χ_u(y)`.

## Implementation notes

The only non-formal input is that `wScaled ℓ h = h / (χ⋆χ)_ℓ` is measurable for
measurable `h` (division by the continuous `convScale`), and that `χ_u(x)` is continuous
in `(u,x)`.  These two facts are registered as `fun_prop` lemmas (locally, in this file)
so that Mathlib's `fun_prop` can assemble the compositions
`(u,a,b) ↦ wLoc ℓ h u a b`.  Pairing the whole argument into a single triple
`(u, a, b) ↦ wLoc ℓ h u a b = χ_u(a)·W(a−b)·χ_u(b)` and then composing with the
measurable map `(u,x) ↦ (u, x_{p.1}, x_{p.2})` avoids the repeated
`Measurable`-instance search that a per-argument composition would trigger.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace Work.BoseBox


open Submission.BoseGases

/-- `(u,x) ↦ χ_u(x)` is continuous (χ is continuous and `χ_u(x) = χ((ℓ⁻¹)•x − u)`). -/
lemma continuous_chiU_pair (ℓ : ℝ) : Continuous (fun q : ℝ³ × ℝ³ => chiU ℓ q.1 q.2) := by
  unfold chiU
  exact chi_continuous.comp ((continuous_snd.const_smul (ℓ⁻¹)).sub continuous_fst)

/-- The renormalized kernel `wScaled ℓ h = h / (χ⋆χ)_ℓ` is measurable as soon as the
numerator `h` is measurable (the denominator is continuous). -/
lemma measurable_wScaled' (ℓ : ℝ) {h : ℝ³ → ℝ} (hh : Measurable h) :
    Measurable (wScaled ℓ h) :=
  hh.div (convScale_continuous ℓ).measurable

attribute [local fun_prop] continuous_chiU_pair measurable_wScaled'

/-- The uncurried localized kernel `(u,a,b) ↦ wLoc ℓ h u a b` is measurable as soon as the
numerator `h` is: it is `χ_u(a)·W(a−b)·χ_u(b)`. -/
lemma measurable_wLoc_three (ℓ : ℝ) {h : ℝ³ → ℝ} (hh : Measurable h) :
    Measurable (fun q : ℝ³ × ℝ³ × ℝ³ => wLoc ℓ h q.1 q.2.1 q.2.2) := by
  unfold wLoc
  fun_prop

attribute [local fun_prop] measurable_wLoc_three

/-- **Measurability of the `potAmb` integrand for measurable kernels.** For measurable kernel numerators `vK` (pair term) and `gK` (one-body term) and a continuous state `Ψ`, the `(u,x)`-integrand of the potential word is strongly measurable.

Route: each fibre integral `potBr ℓ gK u (x i) = ∫_y wLoc ℓ gK u (x i) y` of `potBracketG` is a parameter integral whose uncurried integrand `((u,x),y) ↦ χ_u(x_i)·(gK(x_i−y)/(χ⋆χ)_ℓ(x_i−y))·χ_u(y)` is measurable (a product of continuous functions composed with the measurable `gK`, and a measurable division); `MeasureTheory.StronglyMeasurable.integral_prod_right'` then gives strong measurability of the parameter integral, and the pair terms `(u,x) ↦ wLoc ℓ vK u (x_{p.1}) (x_{p.2})` are directly measurable. -/
theorem stronglyMeasurable_potIntegrandG {N : ℕ} {ℓ μ : ℝ}
    {vK gK : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hvm : Measurable vK) (hgm : Measurable gK)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Continuous Ψ) :
    MeasureTheory.StronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        (Ψ p.2) ^ 2 * Work.BoseBox.potBracketG N ℓ μ vK gK p.1 p.2) := by
  -- the one-body fibre integrals, as parameter integrals
  have hone : ∀ i : Fin N,
      StronglyMeasurable (fun q : ℝ³ × Submission.BoseGases.X N => potBr ℓ gK q.1 (q.2 i)) := by
    intro i
    have hmap : Measurable
        (fun r : (ℝ³ × Submission.BoseGases.X N) × ℝ³ => (r.1.1, (r.1.2 i, r.2))) := by
      fun_prop
    have hf : StronglyMeasurable
        (fun r : (ℝ³ × Submission.BoseGases.X N) × ℝ³ => wLoc ℓ gK r.1.1 (r.1.2 i) r.2) := by
      have h2 := (measurable_wLoc_three ℓ hgm).comp hmap
      simpa only [Function.comp_def] using h2.stronglyMeasurable
    have h3 := hf.integral_prod_right' (ν := (volume : Measure ℝ³))
    rw [show (fun q : ℝ³ × Submission.BoseGases.X N => potBr ℓ gK q.1 (q.2 i)) =
        (fun x : ℝ³ × Submission.BoseGases.X N =>
          ∫ y : ℝ³, wLoc ℓ gK x.1 (x.2 i) y) from by
      funext q; rfl]
    exact h3
  -- the pair terms
  have hpair : ∀ p : Fin N × Fin N,
      StronglyMeasurable
        (fun q : ℝ³ × Submission.BoseGases.X N => wLoc ℓ vK q.1 (q.2 p.1) (q.2 p.2)) := by
    intro p
    fun_prop
  -- the two finite sums
  have hsum1 : StronglyMeasurable
      (fun q : ℝ³ × Submission.BoseGases.X N => ∑ i : Fin N, potBr ℓ gK q.1 (q.2 i)) := by
    have h := Finset.stronglyMeasurable_sum (Finset.univ : Finset (Fin N)) (fun i _ => hone i)
    convert h using 1
    ext q
    simp only [Finset.sum_apply]
  have hsum2 : StronglyMeasurable
      (fun q : ℝ³ × Submission.BoseGases.X N =>
        ∑ p ∈ pairSet N, wLoc ℓ vK q.1 (q.2 p.1) (q.2 p.2)) := by
    have h := Finset.stronglyMeasurable_sum (pairSet N) (fun p _ => hpair p)
    convert h using 1
    ext q
    simp only [Finset.sum_apply]
  -- the bracket
  have hbracket : StronglyMeasurable
      (fun q : ℝ³ × Submission.BoseGases.X N => potBracketG N ℓ μ vK gK q.1 q.2) := by
    have h := (hsum1.const_mul (-μ)).add (hsum2.const_mul (1 / 2))
    convert h using 1
    ext q
    simp only [Pi.add_apply]
    rfl
  -- assemble with the (continuous, hence measurable) weight `(Ψ ·)^2`
  have hPsi2 : StronglyMeasurable
      (fun q : ℝ³ × Submission.BoseGases.X N => (Ψ q.2) ^ 2) :=
    ((hΨ.comp continuous_snd).pow 2).stronglyMeasurable
  convert hPsi2.mul hbracket using 1
  all_goals
    ext p
    simp only [Pi.mul_apply]

end Work.BoseBox
