/-
# The independence of `M₀` and of its derivatives from the choice of modulus

`M0 P N q α₁ α₂ ξ₁ ξ₂` and `M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂` are the symbol difference of
Proposition `mod-approx` and its `(ξ₁,ξ₂)`-derivatives; the modulus `q` enters *only* through the
arithmetic symbol `mZ P q α₁ α₂`.  The arithmetic character `n ↦ e(α₁ n + α₂ P(n))` is `q`-periodic
whenever `q • α₁ = q • α₂ = 0`, so `mZ` is unchanged when `q` is replaced by any other modulus
killing `α₁` and `α₂` (`Work.KMTPlan.A6.mZ_period_eq`), and then so are `M0` and `M0deriv`.

The point of the lemmas is to allow the modulus `arithQ ρ L` of the exact-height kernels to be
replaced by the *fibre period* `perQ α₁ α₂ = lcm (addOrderOf α₁) (addOrderOf α₂)`, whose square is
`2^{O(2^{ρl})}` (absorbable by `modelWeight`), whereas `arithQ²` is `2^{O(2^L)}` and is not.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.mZ_period_eq
import Submission.Work.KMTAreas.A7.spikeToolbox

set_option autoImplicit false

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-- **`M0` is unchanged when the modulus is replaced by another one killing `α₁, α₂`.** -/
theorem M0_eq_of_period (P : Polynomial ℤ) (N : ℕ) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    {α₁ α₂ : Work.Analysis.IonescuWainger.Circle} (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0) (h₁' : q' • α₁ = 0) (h₂' : q' • α₂ = 0)
    (ξ₁ ξ₂ : ℝ) :
    M0 P N q α₁ α₂ ξ₁ ξ₂ = M0 P N q' α₁ α₂ ξ₁ ξ₂ := by
  rw [M0, M0, Work.KMTPlan.A6.mZ_period_eq P hq hq' h₁ h₂ h₁' h₂']

/-- **`M0deriv` is unchanged when the modulus is replaced by another one killing `α₁, α₂`.** -/
theorem M0deriv_eq_of_period (P : Polynomial ℤ) (N : ℕ) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    {α₁ α₂ : Work.Analysis.IonescuWainger.Circle} (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0) (h₁' : q' • α₁ = 0) (h₂' : q' • α₂ = 0)
    (ξ₁ ξ₂ : ℝ) (j₁ j₂ : ℕ) :
    M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂ = M0deriv P N q' α₁ α₂ ξ₁ ξ₂ j₁ j₂ := by
  rw [M0deriv, M0deriv, Work.KMTPlan.A6.mZ_period_eq P hq hq' h₁ h₂ h₁' h₂']

/-- **`mZ` may be computed with the fibre period `perQ α₁ α₂`** (for any modulus `q` killing both
frequencies). -/
theorem mZ_eq_perQ (P : Polynomial ℤ) {q : ℕ} (hq : 0 < q) {α₁ α₂ : Work.Analysis.IonescuWainger.Circle}
    (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0) (ho₁ : IsOfFinAddOrder α₁)
    (ho₂ : IsOfFinAddOrder α₂) :
    mZ P q α₁ α₂ = mZ P (Work.KMTPlan.A6.perQ α₁ α₂) α₁ α₂ :=
  Work.KMTPlan.A6.mZ_period_eq P hq (Work.KMTPlan.A6.SpikeToolbox.perQ_pos ho₁ ho₂) h₁ h₂
    (Work.KMTPlan.A6.SpikeToolbox.perQ_smul_left α₁ α₂)
    (Work.KMTPlan.A6.SpikeToolbox.perQ_smul_right α₁ α₂)

/-- **`M0` may be computed with the fibre period `perQ α₁ α₂`.** -/
theorem M0_eq_perQ (P : Polynomial ℤ) (N : ℕ) {q : ℕ} (hq : 0 < q) {α₁ α₂ : Work.Analysis.IonescuWainger.Circle}
    (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0) (ho₁ : IsOfFinAddOrder α₁)
    (ho₂ : IsOfFinAddOrder α₂) (ξ₁ ξ₂ : ℝ) :
    M0 P N q α₁ α₂ ξ₁ ξ₂ = M0 P N (Work.KMTPlan.A6.perQ α₁ α₂) α₁ α₂ ξ₁ ξ₂ :=
  M0_eq_of_period P N hq (Work.KMTPlan.A6.SpikeToolbox.perQ_pos ho₁ ho₂) h₁ h₂
    (Work.KMTPlan.A6.SpikeToolbox.perQ_smul_left α₁ α₂)
    (Work.KMTPlan.A6.SpikeToolbox.perQ_smul_right α₁ α₂) ξ₁ ξ₂

/-- **`M0deriv` may be computed with the fibre period `perQ α₁ α₂`.** -/
theorem M0deriv_eq_perQ (P : Polynomial ℤ) (N : ℕ) {q : ℕ} (hq : 0 < q) {α₁ α₂ : Work.Analysis.IonescuWainger.Circle}
    (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0) (ho₁ : IsOfFinAddOrder α₁)
    (ho₂ : IsOfFinAddOrder α₂) (ξ₁ ξ₂ : ℝ) (j₁ j₂ : ℕ) :
    M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂
      = M0deriv P N (Work.KMTPlan.A6.perQ α₁ α₂) α₁ α₂ ξ₁ ξ₂ j₁ j₂ :=
  M0deriv_eq_of_period P N hq (Work.KMTPlan.A6.SpikeToolbox.perQ_pos ho₁ ho₂) h₁ h₂
    (Work.KMTPlan.A6.SpikeToolbox.perQ_smul_left α₁ α₂)
    (Work.KMTPlan.A6.SpikeToolbox.perQ_smul_right α₁ α₂) ξ₁ ξ₂ j₁ j₂

end

end Work.KMTAreas.A7
