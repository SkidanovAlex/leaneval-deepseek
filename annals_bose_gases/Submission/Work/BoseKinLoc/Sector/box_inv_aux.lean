import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_add_const_L2
import Submission.Work.BoseKinLoc.Word.fsT_eq_zero_of_lamBox_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.box_inv_aux` — the box-locality lemmas for `fsT`

FS's localised kinetic word `fsT ℓ d s εT b u` (`Work.BoseKinLoc.Defs`, FS `eq:DefT`) is a
one-body quadratic form that **only sees the state on the moving box** `Λ(u) = lamBox ℓ u`:

    `ψ = ψ'` on `Λ(u)`  ⟹  `fsT ℓ d s εT b u ψ = fsT ℓ d s εT b u ψ'`
    (`Work.BoseKinLoc.Sector.fsT_box_invariant`).

This module proves the *state-level* half of that statement, i.e. the invariance of the four
ingredients that are functionals of the state alone:

* `bsMean_eq_of_lamBox_eq` — the box mean `|Λ|⁻¹∫_{Λ(u)}ψ` only sees `ψ` on `Λ(u)` (the
  integrand is `ψ(ℓu + z)` with `ℓu + z ∈ Λ(u)`);
* `Qfree_eq_of_lamBox_eq` — hence the mean-free state `Q_uψ = ψ − m_u(ψ)` agrees on `Λ(u)`;
* `gapBare_eq_of_lamBox_eq` — the mean-free `L²`-mass `∫_{Λ(u)}(Q_uψ)²`;
* `neuFrac_eq_of_lamBox_eq` — the Neumann-resolvent fraction `neuFrac`, whose defining `sInf`
  is over trial values that are integrals over `Λ(u)` only.

The two *windowed* pieces (`momForm`, whose integrand is `θ_u·Q_uψ`, and `bsOneBody`, whose
integrand is `χ_u·Q_uψ`) are proved in the sibling modules
`Work.BoseKinLoc.Sector.momForm_eq_of_lamBox_eq` and
`Work.BoseKinLoc.Sector.bsOneBody_eq_of_lamBox_eq`; the main file assembles all six.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseKinLoc.Sector

open Work.BoseKinLoc Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The box mean and the mean-free state -/

/-- The moving-box mean `bsMean ℓ u ψ` only depends on the restriction of `ψ` to `Λ(u)`. -/
lemma bsMean_eq_of_lamBox_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ ψ' : ℝ³ → ℝ}
    (h : ∀ z : ℝ³, z ∈ lamBox ℓ u → ψ z = ψ' z) : bsMean ℓ u ψ = bsMean ℓ u ψ' := by
  unfold bsMean
  rw [show (∫ z in Submission.BoseGases.acube ℓ, ψ (ℓ • u + z))
      = ∫ z in Submission.BoseGases.acube ℓ, ψ' (ℓ • u + z) from
    setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) (fun z hz => by
      apply h
      show (ℓ • u + z - ℓ • u) ∈ Submission.BoseGases.acube ℓ
      rwa [add_sub_cancel_left])]

/-- The mean-free state `Q_uψ = ψ − m_u(ψ)` agrees on `Λ(u)` when `ψ` does. -/
lemma Qfree_eq_of_lamBox_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ ψ' : ℝ³ → ℝ}
    (h : ∀ z : ℝ³, z ∈ lamBox ℓ u → ψ z = ψ' z) :
    ∀ z : ℝ³, z ∈ lamBox ℓ u → Qfree ℓ u ψ z = Qfree ℓ u ψ' z := by
  intro z hz
  have hm := bsMean_eq_of_lamBox_eq hℓ u h
  simp only [Qfree, bsQ]
  rw [hm, h z hz]

/-! ## 2. The gap word's bare mass -/

/-- The mean-free mass `∫_{Λ(u)}(Q_uψ)²` is a box integral, hence only sees `ψ` on `Λ(u)`. -/
lemma gapBare_eq_of_lamBox_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ ψ' : ℝ³ → ℝ}
    (h : ∀ z : ℝ³, z ∈ lamBox ℓ u → ψ z = ψ' z) :
    gapBare ℓ u ψ = gapBare ℓ u ψ' := by
  unfold gapBare
  exact setIntegral_congr_fun (Word.measurableSet_lamBox ℓ u)
    (fun z hz => by rw [Qfree_eq_of_lamBox_eq hℓ u h z hz])

/-! ## 3. The Neumann-resolvent fraction -/

/-- The trial functional of `neuFrac` only sees the state on the box: all three of its
integrals are over `Λ(u)`. -/
lemma neuFracTrialVal_eq_of_lamBox_eq {ℓ a2 : ℝ} (u : ℝ³) {φ φ' : ℝ³ → ℝ}
    (h : ∀ z : ℝ³, z ∈ lamBox ℓ u → φ z = φ' z) (g : ℝ³ → ℝ) :
    NeuFrac.neuFracTrialVal ℓ a2 u φ g = NeuFrac.neuFracTrialVal ℓ a2 u φ' g := by
  have hmeas := Word.measurableSet_lamBox ℓ u
  unfold NeuFrac.neuFracTrialVal
  rw [show (∫ z in lamBox ℓ u, (φ z) ^ 2) = ∫ z in lamBox ℓ u, (φ' z) ^ 2 from
        setIntegral_congr_fun hmeas (fun z hz => by rw [h z hz]),
      show (∫ z in lamBox ℓ u, φ z * g z) = ∫ z in lamBox ℓ u, φ' z * g z from
        setIntegral_congr_fun hmeas (fun z hz => by rw [h z hz])]

/-- `neuFrac` is blind to changes of the state off the box: its defining `sInf` is over trial
sets that coincide. -/
lemma neuFrac_eq_of_lamBox_eq {ℓ a2 : ℝ} (u : ℝ³) {φ φ' : ℝ³ → ℝ}
    (h : ∀ z : ℝ³, z ∈ lamBox ℓ u → φ z = φ' z) :
    neuFrac ℓ a2 u φ = neuFrac ℓ a2 u φ' := by
  rw [NeuFrac.neuFrac_eq_sInf, NeuFrac.neuFrac_eq_sInf]
  congr 1
  ext y
  constructor
  · rintro ⟨g, hg, hgs, rfl⟩
    exact ⟨g, hg, hgs, neuFracTrialVal_eq_of_lamBox_eq u h g⟩
  · rintro ⟨g, hg, hgs, rfl⟩
    exact ⟨g, hg, hgs, (neuFracTrialVal_eq_of_lamBox_eq u h g).symm⟩

end Work.BoseKinLoc.Sector
