import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.boxMassGates
import Submission.Work.BoseFixB1S.perBoxGapBranchB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxM1_le_aV` — the localised one-body mass is `≤ C·(a v)·|B(u)|`

The localised fibre mass of the sliding box,

`boxM1 ℓ (dlBox ℓ d u) (wSmall1Pair h M ℓ d u) = ∫_{B(u)} ∫ w_{1,B(u)}`,

is bounded by a constant times `(a v)` times the *indicator* box volume
`boxMass ℓ d u = ∫ 1_{B(u)}`.  This is FS `eq:appw1sliding`
(`w_{1,B(u)} ≈ 8πa·|B(u)|`) in the form consumed by the per-box density
`n(u)/|B(u)|`.

The proof is the three-step chain

* `boxM1 = w1MassB` (`Work.BoseFixB1.boxMassGates`, gate 1);
* `w1MassB ≤ C₁·(a v)·chiMass M ℓ d u` (`Work.BoseFixB1.WB.mass_upper`, the
  *smooth* `χ_{B(u)}²`-mass law);
* `chiMass M ℓ d u ≤ (chiSupAbs·chiSmallDecay M)²·boxMass ℓ d u`
  (`Work.BoseFixB1S.perBoxGapBranchB1.chiMass_le_const_mul_boxMass`: the cutoff
  is bounded by the constant `chiSupAbs·chiSmallDecay M` and supported in the
  box),

with `a v ≥ 0` (`8π a v = ∫|g₀| ≥ 0`) to move the `chiMass`-comparison through
the factor `(a v)`.  The resulting constant is
`C = 16π·(smallConvLower M)⁻¹·(chiSupAbs·chiSmallDecay M)²`, depending on `M`
only.
-/

namespace Work.BoseFixB1

open MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

theorem boxM1_le_aV {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
        (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
        (u : EuclideanSpace ℝ (Fin 3)),
        Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u)
          ≤ C * (_root_.BoseGases.a v) * Work.SmallBoxSliding.boxMass ℓ d u := by
  -- the smooth mass law `∬w_{1,B} ≤ C₁ (a v) χ-mass`
  obtain ⟨C₁, hC₁, hUp⟩ :=
    WB.mass_upper (v := v) (h := h) (R0 := R0) hv hvrad hv_supp hR0 hM
  -- the `M`-dependent constant of the cutoff: `|χ_{B(u)}| ≤ D`
  set D : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M with hD
  refine ⟨C₁ * D ^ 2, mul_nonneg hC₁ (sq_nonneg D), ?_⟩
  intro ℓ d hℓ hd hR hRχ u
  -- step 1: the localised mass is the global nested integral
  have hgate : Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Submission.BoseGases.wSmall1Pair h M ℓ d u) = w1MassB h M ℓ d u :=
    (boxMassGates hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u).1
  rw [hgate]
  -- step 2: the smooth mass law
  have hmass : w1MassB h M ℓ d u
      ≤ C₁ * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass M ℓ d u :=
    hUp (ℓ := ℓ) (d := d) hℓ hd hR hRχ u
  -- step 3: `chiMass ≤ D²·boxMass`
  have hchi : Work.SmallBoxSliding.chiMass M ℓ d u
      ≤ D ^ 2 * Work.SmallBoxSliding.boxMass ℓ d u := by
    simpa only [hD] using
      Work.BoseFixB1S.chiMass_le_const_mul_boxMass (M := M) hM hℓ hd u
  -- the scattering length is nonnegative: `8π a v = ∫|g₀| ≥ 0`
  have ha : 0 ≤ _root_.BoseGases.a v := by
    have h1 : 0 ≤ ∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z| :=
      integral_nonneg (fun z => abs_nonneg _)
    have h2 : (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z|)
        = 8 * Real.pi * _root_.BoseGases.a v :=
      Submission.BoseGases.g0_abs_integral hR0 hv hvrad hv_supp h
    have h3 : 0 ≤ 8 * Real.pi * _root_.BoseGases.a v := by rw [← h2]; exact h1
    exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 8 * Real.pi)).mp h3
  calc w1MassB h M ℓ d u
      ≤ C₁ * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass M ℓ d u := hmass
    _ ≤ C₁ * (_root_.BoseGases.a v)
          * (D ^ 2 * Work.SmallBoxSliding.boxMass ℓ d u) :=
        mul_le_mul_of_nonneg_left hchi (mul_nonneg hC₁ ha)
    _ = (C₁ * D ^ 2) * (_root_.BoseGases.a v) * Work.SmallBoxSliding.boxMass ℓ d u := by ring

end Work.BoseFixB1
