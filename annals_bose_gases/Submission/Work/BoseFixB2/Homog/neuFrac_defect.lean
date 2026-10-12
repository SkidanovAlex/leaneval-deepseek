import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Polar.neuFrac_parallelogram
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Homog.neuFrac_defect` — the `t`-defect of the box Neumann fraction

The box Neumann-resolvent fraction `neuFrac ℓ a² u` (FS `eq:DefT`'s first term) is a **quadratic
form** in the state.  This module records the two elementary properties of the `t`-defect

`D(t) = neuFrac(tψ₁ + ψ₂) − neuFrac(tψ₁ − ψ₂)`

along a line of states that together force it to be linear, `D(t) = t·D(1)`:

* **`neuFrac_defect_add`**: `D` is additive in `t`.  This is a rearrangement of the
  parallelogram law `neuFrac(f+g) + neuFrac(f−g) = 2 neuFrac(f) + 2 neuFrac(g)`
  (`Polar.neuFrac_parallelogram`), evaluated at the pairs `(a±c, b)` and `(a, b±c)` — note
  `D(t) = 4·B(tψ₁, ψ₂)` for the polar form `B` of the quadratic form, and `B` is additive in
  its first slot by the parallelogram law alone.
* **`neuFrac_defect_bddAbove`**: `D` is bounded above on a neighbourhood of `0`.  This uses
  the two one-sided variational bounds for `neuFrac`: `0 ≤ neuFrac φ`
  (`NeuFrac.neuFrac_nonneg_l2`) and `neuFrac φ ≤ ∫_Λ φ²` (the trial `g = 0`, here
  `neuFrac_le_sqBox`), so that for `|t| ≤ 1`

  `D(t) ≤ neuFrac(tψ₁+ψ₂) ≤ ∫_Λ (tψ₁+ψ₂)² ≤ 2∫_Λ ψ₁² + 2∫_Λ ψ₂²`,

  a finite constant because `ψ₁, ψ₂` are smooth and `Λ = lamBox ℓ u` is compact.

The point of splitting the two properties is that an additive function `ℝ → ℝ` which is
bounded above near `0` is *linear* (`Work.BoseFixB2.Homog.additive_bddAbove_eq_smul`), with no
measurability or topological hypothesis beyond the boundedness: this is exactly the step that
fails if one only knows the parallelogram law and `2`-homogeneity (the defect of those two
alone is a derivation of `ℝ`, see `Polar/par_polarisation.lean`).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB2.Homog

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.BoseKinLoc (neuFrac lamBox)

/-- **Nonnegativity of the box Neumann fraction for continuous states**: every value of the
defining trial functional is `≥ 0`, so the infimum is. -/
lemma neuFrac_nonneg_of_continuous {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 ≤ a2)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) :
    0 ≤ neuFrac ℓ a2 u ψ :=
  Work.BoseKinLoc.NeuFrac.neuFrac_nonneg_l2 ℓ a2 ha2 u ψ
    ((hψ.pow 2).continuousOn.integrableOn_compact (Work.BoseKinLoc.Gap.isCompact_lamBox hℓ u))

/-- **The variational upper bound `neuFrac ℓ a² u ψ ≤ ∫_Λ ψ²`**, from the trial `g = 0`.
This is `csInf_le` for the trial set of `neuFrac`, whose boundedness below is supplied by
square integrability of `ψ` on the box. -/
lemma neuFrac_le_sqBox {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : EuclideanSpace ℝ (Fin 3))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : MeasureTheory.Integrable (fun z => (ψ z) ^ 2)
      (MeasureTheory.volume.restrict (lamBox ℓ u))) :
    neuFrac ℓ a2 u ψ ≤ ∫ z in lamBox ℓ u, (ψ z) ^ 2 := by
  rw [Work.BoseKinLoc.Kinetic.neuFrac_eq_sInf_trialSet]
  refine csInf_le (Work.BoseKinLoc.Kinetic.bddBelow_trialSet_of_integrableOn' ha2 u hψ) ?_
  exact ⟨fun _ => (0 : ℝ), contDiff_const, HasCompactSupport.zero,
    (Work.BoseKinLoc.Kinetic.trialVal_zero ℓ a2 u ψ).symm⟩

/-- **The `t`-defect of `neuFrac`** along the line `t ↦ t·ψ₁ + ψ₂`:
`D(t) = neuFrac(tψ₁ + ψ₂) − neuFrac(tψ₁ − ψ₂)`.  For a quadratic form this is `4·B(tψ₁,ψ₂)`
for the associated bilinear form `B`. -/
def neuFracDefect (ℓ a2 : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (ψ₁ ψ₂ : EuclideanSpace ℝ (Fin 3) → ℝ) (t : ℝ) : ℝ :=
  neuFrac ℓ a2 u (fun z => t * ψ₁ z + ψ₂ z) - neuFrac ℓ a2 u (fun z => t * ψ₁ z - ψ₂ z)

/-- **The three-term identity for the polar form of `neuFrac`**: for smooth `a, b, c`,

`(V(a+b+c) − V(a+b−c)) = (V(a+c) − V(a−c)) + (V(b+c) − V(b−c))`.

This is the parallelogram law at the four pairs `(a±c, b)` and `(a, b±c)`, combined by `abel`
and `linarith`; it says that `B(x,y) = (V(x+y) − V(x−y))/4` is additive in its first slot. -/
lemma neuFrac_polar_add3 {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2)
    (u : EuclideanSpace ℝ (Fin 3)) {a b c : EuclideanSpace ℝ (Fin 3) → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    (neuFrac ℓ a2 u (a + b + c) - neuFrac ℓ a2 u (a + b - c))
      = (neuFrac ℓ a2 u (a + c) - neuFrac ℓ a2 u (a - c))
        + (neuFrac ℓ a2 u (b + c) - neuFrac ℓ a2 u (b - c)) := by
  have hpar : ∀ x y : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) x →
      ContDiff ℝ (⊤ : ℕ∞) y → neuFrac ℓ a2 u (x + y) + neuFrac ℓ a2 u (x - y)
        = 2 * neuFrac ℓ a2 u x + 2 * neuFrac ℓ a2 u y :=
    fun x y hx hy => Work.BoseFixB2.Polar.neuFrac_parallelogram hℓ ha2 u hx hy
  have p1 := hpar (a + c) b (ha.add hc) hb
  have p2 := hpar (a - c) b (ha.sub hc) hb
  have p3 := hpar a (b + c) ha (hb.add hc)
  have p4 := hpar a (b - c) ha (hb.sub hc)
  rw [show (a + c) + b = a + b + c by abel, show (a + c) - b = a - b + c by abel] at p1
  rw [show (a - c) + b = a + b - c by abel, show (a - c) - b = a - b - c by abel] at p2
  rw [show a + (b + c) = a + b + c by abel, show a - (b + c) = a - b - c by abel] at p3
  rw [show a + (b - c) = a + b - c by abel, show a - (b - c) = a - b + c by abel] at p4
  linarith

/-- **The `t`-defect of `neuFrac` is additive in `t`.** -/
lemma neuFrac_defect_add {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h₁ : ContDiff ℝ (⊤ : ℕ∞) ψ₁) (h₂ : ContDiff ℝ (⊤ : ℕ∞) ψ₂) (s t : ℝ) :
    neuFracDefect ℓ a2 u ψ₁ ψ₂ (s + t)
      = neuFracDefect ℓ a2 u ψ₁ ψ₂ s + neuFracDefect ℓ a2 u ψ₁ ψ₂ t := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun z => s * ψ₁ z) := contDiff_const.mul h₁
  have hB : ContDiff ℝ (⊤ : ℕ∞) (fun z => t * ψ₁ z) := contDiff_const.mul h₁
  have hk := neuFrac_polar_add3 (ℓ := ℓ) (a2 := a2) hℓ ha2 u hA hB h₂
  have e1 : (fun z => s * ψ₁ z) + (fun z => t * ψ₁ z) = fun z => (s + t) * ψ₁ z := by
    funext z
    simp only [Pi.add_apply]
    ring
  rw [e1] at hk
  exact hk

/-- **The `t`-defect of `neuFrac` is bounded above near `0`.** -/
lemma neuFrac_defect_bddAbove {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 ≤ a2)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h₁ : ContDiff ℝ (⊤ : ℕ∞) ψ₁) (h₂ : ContDiff ℝ (⊤ : ℕ∞) ψ₂) :
    ∃ M ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → neuFracDefect ℓ a2 u ψ₁ ψ₂ t ≤ M := by
  refine ⟨2 * (∫ z in lamBox ℓ u, (ψ₁ z) ^ 2) + 2 * (∫ z in lamBox ℓ u, (ψ₂ z) ^ 2),
    1, one_pos, ?_⟩
  intro t ht
  have ht1 : |t| ≤ 1 := le_of_lt ht
  have hK : IsCompact (lamBox ℓ u) := Work.BoseKinLoc.Gap.isCompact_lamBox hℓ u
  have hψ₁ : MeasureTheory.Integrable (fun z => (ψ₁ z) ^ 2)
      (MeasureTheory.volume.restrict (lamBox ℓ u)) :=
    (h₁.continuous.pow 2).continuousOn.integrableOn_compact hK
  have hψ₂ : MeasureTheory.Integrable (fun z => (ψ₂ z) ^ 2)
      (MeasureTheory.volume.restrict (lamBox ℓ u)) :=
    (h₂.continuous.pow 2).continuousOn.integrableOn_compact hK
  have hplus : MeasureTheory.Integrable (fun z => (t * ψ₁ z + ψ₂ z) ^ 2)
      (MeasureTheory.volume.restrict (lamBox ℓ u)) :=
    (((h₁.continuous.const_mul t).add h₂.continuous).pow 2).continuousOn.integrableOn_compact hK
  have hmono : (∫ z in lamBox ℓ u, (t * ψ₁ z + ψ₂ z) ^ 2)
      ≤ 2 * (∫ z in lamBox ℓ u, (ψ₁ z) ^ 2) + 2 * (∫ z in lamBox ℓ u, (ψ₂ z) ^ 2) := by
    have hR : MeasureTheory.Integrable
        (fun z => 2 * (ψ₁ z) ^ 2 + 2 * (ψ₂ z) ^ 2)
        (MeasureTheory.volume.restrict (lamBox ℓ u)) :=
      (hψ₁.const_mul 2).add (hψ₂.const_mul 2)
    have hpt : ∀ z ∈ lamBox ℓ u, (t * ψ₁ z + ψ₂ z) ^ 2 ≤ 2 * (ψ₁ z) ^ 2 + 2 * (ψ₂ z) ^ 2 := by
      intro z _
      have ht2 : t ^ 2 ≤ 1 := by
        have h := abs_le.mp ht1
        nlinarith [h.1, h.2]
      have h1 : t ^ 2 * (ψ₁ z) ^ 2 ≤ (ψ₁ z) ^ 2 :=
        mul_le_of_le_one_left (sq_nonneg _) ht2
      have h2 : 0 ≤ (t * ψ₁ z - ψ₂ z) ^ 2 := sq_nonneg _
      nlinarith [h1, h2]
    have hboth := setIntegral_mono_on hplus hR hK.measurableSet hpt
    rw [integral_add (hψ₁.const_mul 2) (hψ₂.const_mul 2), integral_const_mul,
      integral_const_mul] at hboth
    exact hboth
  have hup : neuFrac ℓ a2 u (fun z => t * ψ₁ z + ψ₂ z)
      ≤ ∫ z in lamBox ℓ u, (t * ψ₁ z + ψ₂ z) ^ 2 :=
    neuFrac_le_sqBox ha2 u hplus
  have hnn : 0 ≤ neuFrac ℓ a2 u (fun z => t * ψ₁ z - ψ₂ z) :=
    neuFrac_nonneg_of_continuous hℓ ha2 u ((h₁.continuous.const_mul t).sub h₂.continuous)
  unfold neuFracDefect
  linarith

end Work.BoseFixB2.Homog
