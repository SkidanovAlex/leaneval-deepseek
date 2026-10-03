import Mathlib
import Submission.Work.KMTAreas.A7.liftCollapse
import Submission.Work.KMTAreas.A7.symbolDefs
import Submission.Work.KMTAreas.A7.SmallModDefs

set_option maxHeartbeats 4000000

/-
# `avgSymb = weylAvg` at the shifted continuous frequencies

The discrete average symbol `avgSymb P N θ₁ θ₂` of (K1) and the discrete average `weylAvg`
of Proposition `mod-approx` are the same sum over the halved window `Ioc (N/2) N`, the first
written as a product of the two characters `n ↦ e(n θ₁)`, `n ↦ e(P(n) θ₂)` and the second as the
same product *twisted* by the continuous phase
`n ↦ e(ξ₁ n + ξ₂ P(n))` at the frequencies `ξᵢ = lift (θᵢ - βᵢ)`.

Because every `fourier` is a character of the circle group, the twist is *exactly* absorbed:

`fourier n θ = fourier n β · e(n · lift (θ - β))`,

so summing over the window gives

`avgSymb P N θ₁ θ₂ = weylAvg P N β₁ β₂ (lift (θ₁ - β₁)) (lift (θ₂ - β₂))`.

This is the identity that lets the §6 model approximation replace the concrete average symbol by
the Weyl sum `weylAvg` at shifted frequencies, and it is used by
`A7/concSymb_sub_modSymb_algebra.lean` / `A7/M0Aux.lean`.

The proof is pointwise in the summation index, hence uses no arithmetic at all.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## The two elementary identities for the Fourier characters -/

/-- `e` is a character of `ℝ`: `e (a + b) = e a · e b`. -/
private lemma ee_add_aux (a b : ℝ) : ee (a + b) = ee a * ee b := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The character `fourier n` at a point of the circle written as a real number. -/
private lemma fourier_coe_ee (n : ℤ) (x : ℝ) :
    fourier (T := 1) n ((x : ℝ) : AddCircle (1 : ℝ)) = ee ((n : ℝ) * x) := by
  rw [fourier_coe_apply]
  simp only [ee]
  congr 1
  push_cast
  ring

/-- The character `fourier n` evaluated through the canonical lift. -/
private lemma fourier_lift_ee (n : ℤ) (γ : AddCircle (1 : ℝ)) :
    fourier (T := 1) n γ = ee ((n : ℝ) * lift γ) := by
  conv_lhs => rw [← lift_coe γ]
  rw [fourier_coe_apply]
  simp only [ee]
  congr 1
  push_cast
  ring

/-- **Absorption of the shift.**  The character `fourier n` at `θ` factorises through its value at
`β` times the continuous frequency `lift (θ - β)`. -/
private lemma fourier_mul_lift (n : ℤ) (β θ : AddCircle (1 : ℝ)) :
    fourier (T := 1) n θ = fourier (T := 1) n β * ee (lift (θ - β) * (n : ℝ)) := by
  have hz : (n • θ : AddCircle (1 : ℝ)) = n • β + n • (θ - β) := by
    rw [← zsmul_add]
    congr 1
    abel
  have hb : fourier (T := 1) n θ = fourier (T := 1) n β * fourier (T := 1) n (θ - β) := by
    simp_rw [fourier_apply]
    rw [hz, AddCircle.toCircle_add, Circle.coe_mul]
  rw [hb, fourier_lift_ee n (θ - β)]
  congr 1
  ring

/-- The real evaluation of an integer polynomial at an integer is the coercion of the integer
evaluation. -/
private lemma pevalR_intCast (P : Polynomial ℤ) (n : ℤ) :
    PevalR P ((n : ℝ)) = ((P.eval n : ℤ) : ℝ) := by
  simp [PevalR]

/-- **The discrete average symbol equals the Weyl average at shifted continuous frequencies.** -/
theorem avgSymb_eq_weylAvg (P : Polynomial ℤ) (N : ℕ)
    (β₁ β₂ θ₁ θ₂ : Work.Analysis.IonescuWainger.Circle) :
    Work.KMTAreas.A7.avgSymb P N θ₁ θ₂
      = Work.KMTAreas.A7.weylAvg P N β₁ β₂
          (Work.KMTAreas.A7.lift (θ₁ - β₁)) (Work.KMTAreas.A7.lift (θ₂ - β₂)) := by
  simp only [avgSymb, weylAvg, momPhase]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [fourier_mul_lift (n : ℤ) β₁ θ₁, fourier_mul_lift (P.eval (n : ℤ)) β₂ θ₂]
  rw [pevalR_intCast P (n : ℤ)]
  rw [ee_add_aux]
  ring

end

end Work.KMTAreas.A7.Cpy

