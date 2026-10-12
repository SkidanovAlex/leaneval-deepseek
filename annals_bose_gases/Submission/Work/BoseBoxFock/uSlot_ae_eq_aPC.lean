import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.uSlot_int_eq_aPC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.uSlot_ae_eq_aPC`

The condensate row of the box ↔ model dictionary needs the *pointwise* identification of the
slot operator of the pinned one-particle vector `u` (FS's condensate orbital, `u = c·θ_Λ`
with `conj c * c = ℓ⁻³`) with the box's slot mean `aPC`:

    `uSlot u j Θ x = u (x j) · conj c · ∫_{Λ} Θ (x[j ↦ z]) dz = ℓ⁻³ ∫_{Λ} Θ (x[j ↦ z]) dz
      = aPC ℓ j Θ x`,

valid for every `x` whose `j`-coordinate lies in the cube `Λ = acube ℓ` *and* where the a.e.
pinning `u = c·θ_Λ` is realised.  On the box `abox d ℓ = (Λ)^d` the first condition holds
*everywhere* by definition, and the second one holds almost everywhere, because the `j`-th
coordinate of a point of `abox d ℓ` is distributed according to `volume ↾ acube ℓ`
(`Measure.quasiMeasurePreserving_eval` for the product measure
`volume ↾ abox d ℓ = Measure.pi (fun _ => volume ↾ acube ℓ)`, `restrict_abox_eq_pi`).

The off-support/null-set junk values of the Bochner integral cause no difficulty: the identity
`uSlot_eq_mul_setIntegral` (from `uSlot_int_eq_aPC`) is *unconditional* in `Θ`, and the
a.e. statement `u (x j) = c` is exactly the missing factor.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Sp" => Work.BoseDict.Sp

/-- **Almost everywhere on the box, the pinned one-particle vector takes the value `c` at the
`j`-th coordinate.**  This is the only measure-theoretic input of `uSlot_ae_eq_aPC`: the
`j`-th coordinate of `abox d ℓ` is distributed by `volume ↾ acube ℓ`, so the a.e. pinning
`u = c · θ_Λ`, read on the cube, gives `u (x j) = c` for a.e. `x`. -/
theorem ae_u_eq_c_of_ae_eq_theta {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin d) {u : Sp → ℂ} {c : ℂ}
    (huc : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
        u z = c * Work.BoseK15.corpusBox.thetaFun ℓ z) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)), u (x j) = c := by
  -- On the cube itself, the pinning `u = c·θ_Λ` and `θ_Λ = 1` give `u = c` a.e.
  have hcu : ∀ᵐ z ∂((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
      (Submission.BoseGases.acube ℓ)), u z = c := by
    have h2 : ∀ᵐ z ∂((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
        (Submission.BoseGases.acube ℓ)),
        u z = c * Work.BoseK15.corpusBox.thetaFun ℓ z :=
      ae_mono MeasureTheory.Measure.restrict_le_self huc
    filter_upwards [h2, self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)]
      with z hz hzc
    rw [hz, thetaFun_eq_indicator hℓ, Set.indicator_of_mem hzc, mul_one]
  -- The `j`-th coordinate of `volume ↾ abox d ℓ = Measure.pi (volume ↾ acube ℓ)` is
  -- quasi-measure-preserving onto `volume ↾ acube ℓ`.
  rw [Submission.BoseGases.restrict_abox_eq_pi]
  exact (Measure.quasiMeasurePreserving_eval
    (μ := fun _ : Fin d => (MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
      (Submission.BoseGases.acube ℓ)) j).ae hcu

/-- **The slot operator of the pinned condensate vector is the box slot mean, a.e. on the box.**

`uSlot u j Θ x = u (x j)·conj c·∫_Λ Θ(x[j↦z])` for every `x`, and `u (x j) = c` for a.e. `x`
in `abox d ℓ` (`ae_u_eq_c_of_ae_eq_theta`); with `conj c · c = ℓ⁻³` this is `aPC ℓ j Θ x`. -/
theorem uSlot_ae_eq_aPC {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin d)
    {u : Work.BoseDict.Sp → ℂ} {c : ℂ} {Θ : Work.BoseDict.Xn d → ℂ}
    (huc : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp),
        u z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹) :
    (fun x => Work.BoseBoxFock.uSlot u j Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
      (fun x => Work.BoseBoxFock.aPC ℓ j Θ x) := by
  -- `c · conj c = ℓ⁻³`, in the normal form `1 / ℓ³` appearing in `aPC`.
  have hcc' : c * (starRingEnd ℂ) c = ((1 / ℓ ^ 3 : ℝ) : ℂ) := by
    have h' : (starRingEnd ℂ) c * c = ((↑((ℓ : ℝ) ^ 3)) : ℂ)⁻¹ := by simpa using hcc
    have h : ((1 / ℓ ^ 3 : ℝ) : ℂ) = ((↑((ℓ : ℝ) ^ 3)) : ℂ)⁻¹ := by
      rw [show (1 / ℓ ^ 3 : ℝ) = (ℓ ^ 3 : ℝ)⁻¹ from (inv_eq_one_div (ℓ ^ 3)).symm,
        Complex.ofReal_inv]
    rw [h, mul_comm]
    exact h'
  filter_upwards [ae_u_eq_c_of_ae_eq_theta hℓ j huc] with x hx
  rw [uSlot_eq_mul_setIntegral hℓ huc j Θ x, hx, aPC, hcc']

end Work.BoseBoxFock
