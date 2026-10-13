/-
# `f²w²` is integrable on the quadrant under the coercivity hypotheses

This file proves

`IntegrableOn (fun (z,θ) => f z θ * f z θ * w z ^ 2) (Iz ×ˢ Iθ)`

for every `f` satisfying `CoerciveData α f`.  This is the "unweighted" member of the
family of integrability conditions collected in `CoerciveData`: the coercivity chain
of §"Linearization with angular transport" of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), 1--70

never assumes it directly (the hypothesis package contains the `sin(2θ)^{-η}`-weighted
version `intFeta` instead), but the paper's `L²` bookkeeping repeatedly uses `|f w|²`
as an honest finite number.

## The argument

`CoerciveData` contains `intFeta`, the joint integrability of
`f² w² sin(2θ)^{-η}` with `η = 99/100`.  On the quadrant `θ ∈ [0, π/2]` one has
`sin(2θ) ∈ [0,1]`, so off the null set `{sin(2θ) = 0}` (which is contained in
`Iz ×ˢ {0, π/2}`) the factor `sin(2θ)^{-η}` is `≥ 1` and therefore

`‖f²w²‖ ≤ ‖f²w² sin(2θ)^{-η}‖`.

Moreover, off the same null set, `sin(2θ)^{-η} · sin(2θ)^{η} = 1`, so the target
function agrees a.e. with a bounded (by `1`) measurable multiple of the integrable
`f²w²sin(2θ)^{-η}`; this gives its a.e. strong measurability.  Integrability then
follows from `Integrable.mono'`.
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The null set `{sin(2θ) = 0}` -/

/-- The set of points of `ℝ × ℝ` whose second coordinate annihilates `sin(2·)` is
null.  (In the second coordinate these are the points of `(π/2)ℤ`, a countable set;
the set is `univ ×ˢ ((π/2)ℤ)`, a product of a measurable set with a null set.) -/
theorem volume_sin_two_zero :
    (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | Real.sin (2 * p.2) = 0} = 0 := by
  have hZ : (volume : Measure ℝ) {θ : ℝ | Real.sin (2 * θ) = 0} = 0 := by
    -- `sin(2θ) = 0` forces `θ = n π / 2`, so the set is countable.
    have hsub : {θ : ℝ | Real.sin (2 * θ) = 0} ⊆
        Set.range (fun n : ℤ => (n : ℝ) * Real.pi / 2) := by
      intro θ hθ
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hθ
      exact ⟨n, by linarith⟩
    exact Set.Countable.measure_zero ((Set.countable_range _).mono hsub) volume
  have hset : {p : ℝ × ℝ | Real.sin (2 * p.2) = 0}
      = Set.univ ×ˢ {θ : ℝ | Real.sin (2 * θ) = 0} := by
    ext p; simp
  rw [hset, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, hZ, mul_zero]

/-- Almost every point of `ℝ × ℝ` has `sin(2 ·) ≠ 0` in its second coordinate. -/
theorem ae_sin_two_ne_zero :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), Real.sin (2 * p.2) ≠ 0 := by
  rw [ae_iff]
  simpa only [ne_eq, not_not] using volume_sin_two_zero

/-! ## The pointwise facts at `θ ∈ Iθ` -/

/-- For `θ ∈ Iθ` with `sin(2θ) ≠ 0` (so that `sin(2θ) ∈ (0,1]`) and any real `a`, the
weight `sin(2θ)^{-η}` is `≥ 1`, it is the inverse of `sin(2θ)^{η}`, multiplying by it
does not decrease the norm of `a`, and it is cancelled by `sin(2θ)^{η}`. -/
theorem sin_two_eta_facts (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ)
    (hne : Real.sin (2 * θ) ≠ 0) :
    1 ≤ (Real.sin (2 * θ)) ^ (-(Spaces.eta)) ∧
      (Real.sin (2 * θ)) ^ (-(Spaces.eta)) * (Real.sin (2 * θ)) ^ (Spaces.eta) = 1 ∧
      ‖f z θ * f z θ * Spaces.w z ^ 2‖
        ≤ ‖f z θ * f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.eta))‖ ∧
      f z θ * f z θ * Spaces.w z ^ 2
        = f z θ * f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.eta))
            * (Real.sin (2 * θ)) ^ (Spaces.eta) := by
  have h0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hpos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne h0 (Ne.symm hne)
  -- `sin(2θ)^{η} ≤ 1` since `sin(2θ) ≤ 1` and `η ≥ 0`.
  have hle1 : (Real.sin (2 * θ)) ^ (Spaces.eta) ≤ 1 :=
    Real.rpow_le_one h0 (Real.sin_le_one _) (by norm_num [Spaces.eta])
  have hlt : 1 ≤ (Real.sin (2 * θ)) ^ (-(Spaces.eta)) := by
    rw [Real.rpow_neg (le_of_lt hpos)]
    exact (one_le_inv₀ (Real.rpow_pos_of_pos hpos Spaces.eta)).mpr hle1
  have hmul : (Real.sin (2 * θ)) ^ (-(Spaces.eta)) * (Real.sin (2 * θ)) ^ (Spaces.eta) = 1 := by
    rw [← Real.rpow_add hpos, neg_add_cancel, Real.rpow_zero]
  refine ⟨hlt, hmul, ?_, ?_⟩
  · calc ‖f z θ * f z θ * Spaces.w z ^ 2‖
        = ‖f z θ * f z θ * Spaces.w z ^ 2‖ * 1 := (mul_one _).symm
      _ ≤ ‖f z θ * f z θ * Spaces.w z ^ 2‖
            * ‖(Real.sin (2 * θ)) ^ (-(Spaces.eta))‖ :=
            mul_le_mul_of_nonneg_left
              (by rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 _)]; exact hlt) (norm_nonneg _)
      _ = ‖f z θ * f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.eta))‖ :=
            (norm_mul _ _).symm
  · calc f z θ * f z θ * Spaces.w z ^ 2
        = f z θ * f z θ * Spaces.w z ^ 2
            * ((Real.sin (2 * θ)) ^ (-(Spaces.eta))
                * (Real.sin (2 * θ)) ^ (Spaces.eta)) := by
            rw [hmul, mul_one]
      _ = f z θ * f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.eta))
            * (Real.sin (2 * θ)) ^ (Spaces.eta) := by ring

/-! ## The a.e. statements on the quadrant -/

/-- Almost everywhere on the quadrant, `f²w²` agrees with
`f²w² sin(2θ)^{-η} sin(2θ)^{η}` and is dominated in norm by `f²w² sin(2θ)^{-η}`. -/
theorem ae_f_sq_w_sq_facts (f : ℝ → ℝ → ℝ) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ Spaces.Iz ×ˢ Spaces.Iθ →
      ((f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
          = f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
              * (Real.sin (2 * p.2)) ^ (-Spaces.eta) * (Real.sin (2 * p.2)) ^ Spaces.eta) ∧
        ‖f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2‖
          ≤ ‖f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
              * (Real.sin (2 * p.2)) ^ (-Spaces.eta)‖) := by
  filter_upwards [ae_sin_two_ne_zero] with p hpne hp
  obtain ⟨-, -, h3, h4⟩ := sin_two_eta_facts (z := p.1) f hp.2 hpne
  exact ⟨h4, h3⟩

/-! ## The main statement -/

/-- Under the coercivity hypotheses the unweighted square `f² w²` is jointly integrable
on the quadrant.  (The hypotheses only provide the `sin(2θ)^{-η}`-weighted version
`intFeta`; the angular factor is `≥ 1` off the null set `{sin(2θ) = 0}` and is
cancelled there by `sin(2θ)^{η}`.) -/
theorem f_sq_w_sq_integrable (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Spaces.w z ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
  change Integrable
    (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2)
    (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ))
  have hs : MeasurableSet (Spaces.Iz ×ˢ Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  -- The dominating function: the `intFeta` integrand.
  have hG : Integrable
      (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
        * (Real.sin (2 * p.2)) ^ (-Spaces.eta))
      (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) := hi.intFeta
  have hkey := ae_f_sq_w_sq_facts f
  -- a.e. measurability: the target is a bounded measurable multiple of the integrand.
  have hEq : ∀ᵐ p ∂(volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)),
      f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta) * (Real.sin (2 * p.2)) ^ Spaces.eta
        = f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 :=
    (ae_restrict_iff' hs).mpr (hkey.mono fun p hp hps => (hp hps).1.symm)
  have hφmeas : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ Spaces.eta) :=
    (Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow_const Spaces.eta
  have hHmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2)
      (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) :=
    (hG.aestronglyMeasurable.mul hφmeas.aestronglyMeasurable).congr hEq
  -- a.e. domination of the norms.
  have hle : ∀ᵐ p ∂(volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)),
      ‖f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2‖
        ≤ ‖f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
            * (Real.sin (2 * p.2)) ^ (-Spaces.eta)‖ :=
    (ae_restrict_iff' hs).mpr (hkey.mono fun p hp hps => (hp hps).2)
  exact hG.norm.mono' hHmeas hle

end Work.Coercivity
