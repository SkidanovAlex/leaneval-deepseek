import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Sector.fsT_box_invariant
import Submission.Work.BoseKinLoc.Word.boxFormB_eq_boxForm_of_supp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.boxFormB_eq_zero_of_eq_zero_on_abox`

The box-restricted localised form `boxFormB m v g ℓ μ d s εT b` (FS `eq:Def_HB` seen through the
centred configuration box `abox m ℓ`, cf. `Defs.boxFormB`) **vanishes on every state that vanishes
on the box**:

    `ψ = 0` on `abox m ℓ`  ⟹  `boxFormB m v g ℓ μ d s εT b ψ = 0`.

This is the well-definedness statement that makes the quotient
`boxFormB … Φ / sqNormB m ℓ Φ` of `Defs.EΛ` a genuine *box* Rayleigh quotient: the form only sees
the restriction of the state to the box, so a state that is `0` there contributes `0` (and the
quotient is the indeterminate `0/0`, never a negative value produced by irrelevant values off the
box).

Both additive pieces vanish:

* the potential piece `∫_{abox}(ψ x)²·potWordU … 0 x` because `ψ x = 0` pointwise on the box;
* the `i`-th kinetic piece `∫_{abox} indU ℓ 0 (xᵢ)·fsT … 0 (fibre m i ψ x)`: for `x ∈ abox m ℓ` the
  fibre `z ↦ ψ(x_{i←z})` vanishes on the anchored box `lamBox ℓ 0 = acube ℓ` (replacing the `i`-th
  slot of a box configuration by a point of `acube ℓ` keeps it inside `abox m ℓ`, where `ψ = 0`),
  so `fsT` of the fibre equals `fsT` of the zero function by the box-locality
  `fsT_box_invariant`, and `fsT … 0 0 = 0` (`Word.fsT_zero`).
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseKinLoc.Sector

open Work.BoseKinLoc Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false

theorem boxFormB_eq_zero_of_eq_zero_on_abox {m : ℕ} {v g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {ℓ μ d s εT b : ℝ} (hℓ : 0 < ℓ) {ψ : Submission.BoseGases.X m → ℝ}
    (h0 : ∀ x ∈ Submission.BoseGases.abox m ℓ, ψ x = 0) :
    Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b ψ = 0 := by
  -- The `i`-th fibre of a box configuration vanishes on the anchored box `Λ(0) = acube ℓ`.
  have hfib : ∀ (i : Fin m) (x : Submission.BoseGases.X m),
      x ∈ Submission.BoseGases.abox m ℓ →
      ∀ z ∈ Work.BoseKinLoc.lamBox ℓ 0, Work.BoseKinLoc.fibre m i ψ x z = 0 := by
    intro i x hx z hz
    have hz' : z ∈ Submission.BoseGases.acube ℓ := by
      simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hz
    show ψ (Function.update x i z) = 0
    refine h0 (Function.update x i z) fun j => ?_
    by_cases hji : j = i
    · subst hji; rw [Function.update_self]; exact hz'
    · rw [Function.update_of_ne hji]; exact hx j
  -- Box locality of `fsT` reduces the fibre to the zero function.
  have hfsT : ∀ (i : Fin m) (x : Submission.BoseGases.X m),
      x ∈ Submission.BoseGases.abox m ℓ →
      Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre m i ψ x) = 0 := by
    intro i x hx
    rw [fsT_box_invariant (u := 0) hℓ fun z hz => hfib i x hx z hz]
    exact Word.fsT_zero hℓ
  -- Each slot integral vanishes pointwise on the box.
  have hkin : ∀ i : Fin m,
      (∫ x in Submission.BoseGases.abox m ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i) *
            Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre m i ψ x)) = 0 := by
    intro i
    have hcongr :
        (∫ x in Submission.BoseGases.abox m ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre m i ψ x))
          = ∫ x in Submission.BoseGases.abox m ℓ, (0 : ℝ) :=
      MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable m ℓ)
        (fun x hx => by rw [hfsT i x hx, mul_zero])
    rw [hcongr]
    simp
  -- The potential piece vanishes because `ψ` does.
  have hpot :
      (∫ x in Submission.BoseGases.abox m ℓ,
          (ψ x) ^ 2 * Work.BoseKinLoc.potWordU m v g ℓ μ 0 x)
        = ∫ x in Submission.BoseGases.abox m ℓ, (0 : ℝ) :=
    MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable m ℓ)
      (fun x hx => by rw [h0 x hx]; ring)
  unfold Work.BoseKinLoc.boxFormB Work.BoseKinLoc.kinFormB
  simp [hpot, hkin]

end Work.BoseKinLoc.Sector
