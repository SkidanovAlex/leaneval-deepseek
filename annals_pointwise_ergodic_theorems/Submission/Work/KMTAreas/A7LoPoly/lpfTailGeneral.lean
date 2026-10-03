import Mathlib
import Submission.Work.KMTAreas.A7LoPoly.lpfTailFinsupp
import Submission.Work.KMTAreas.A7LoPoly.varRhoFromGeneralK

/-!
# The `ρ`-variation tail bound for the low-pass walk, for **all** inputs

`Work.KMTAreas.A7LoPoly.lpfTailFinsupp` proves the tail estimate

`‖ V^r_{n ≥ 2^κ} (n ↦ Π_{≤l₁,≤−(m₀+n)} f) ‖_{ℓᵖ} ≤ B ‖f‖_{ℓᵖ}`

for **finitely supported** `f` (with `B` independent of `l₁` and `κ + 1 ≤ Cκ (1+l₁)²`), by the
single-decimation factorisation and the decimated dilation variational estimate.

Here the restriction to finitely supported inputs is removed: the same estimate holds for every
`f : ℤ → ℂ`.  The extension is `Work.KMTAreas.A7LoPoly.varRhoFromGeneralK`, a density/Fatou
argument along the truncations `truncZ K f`; it is applied to the family

`K l₁ m₀ = 2 ^ (κ l₁ m₀)`,

where `κ l₁ m₀` is a *fixed* choice of the threshold supplied by `lpfTailFinsupp` on the good major
arcs (empty choices elsewhere, where the estimate is vacuous).  The constant `B` of
`lpfTailFinsupp` is replaced by `max B 1`, since `varRhoFromGeneralK` needs a strictly positive
constant.
-/

namespace Work.KMTAreas.A7LoPoly

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **A threshold choice that is uniform in the `GoodMajorArcs` hypothesis.**  Given `hT` which, on
the good major arcs, produces an exponent `κ` with its budget and the finitely supported bound at
cap `2^κ`, this produces – for each `(l₁, m₀)` and *without* assuming the major arc hypothesis – an
exponent whose budget and bound are implied by that hypothesis.  (Off the good arcs any exponent
works; the implications are vacuous.) -/
private lemma tailK_exists (ρ r p CρT Cκ B : ℝ)
    (hT : ∀ (l₁ m₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρT l₁ (-(m₀ : ℤ)) →
      ∃ κ : ℕ, (κ : ℝ) + 1 ≤ Cκ * (1 + (l₁ : ℝ)) ^ 2 ∧
        ∀ f : ℤ →₀ ℂ,
          MeasureTheory.eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom r (2 ^ κ)
              (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n (⇑f) y))
            (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal B *
              MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count)
    (l₁ m₀ : ℕ) :
    ∃ κ : ℕ,
      (Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρT l₁ (-(m₀ : ℤ)) →
        (κ : ℝ) + 1 ≤ Cκ * (1 + (l₁ : ℝ)) ^ 2) ∧
      (Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρT l₁ (-(m₀ : ℤ)) →
        ∀ f : ℤ →₀ ℂ,
          MeasureTheory.eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom r (2 ^ κ)
              (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n (⇑f) y))
            (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal B *
              MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count) := by
  classical
  by_cases h : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρT l₁ (-(m₀ : ℤ))
  · obtain ⟨κ, hb, hbd⟩ := hT l₁ m₀ h
    exact ⟨κ, fun _ => hb, fun _ => hbd⟩
  · exact ⟨0, fun hh => absurd hh h, fun hh => absurd hh h⟩

theorem lpfTailGeneral (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : ℝ) (hr : 2 < r)
    (p : ℝ) (hp : 1 < p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ Cκ : ℝ, 0 < Cκ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (l₁ m₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) →
        ∃ κ : ℕ, (κ : ℝ) + 1 ≤ Cκ * (1 + (l₁ : ℝ)) ^ 2 ∧
          ∀ f : ℤ → ℂ,
            MeasureTheory.eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom r (2 ^ κ)
                (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f y))
              (ENNReal.ofReal p) MeasureTheory.Measure.count
            ≤ ENNReal.ofReal B *
                MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  classical
  -- the finitely supported estimate, with the good-arc budget
  obtain ⟨Cρ, hCρ, Cκ, hCκ, B, hB, hT⟩ := lpfTailFinsupp ρ hρ hρ1 r hr p hp
  -- `varRhoFromGeneralK` needs a strictly positive constant
  refine ⟨Cρ, hCρ, Cκ, hCκ, max B 1, le_trans hB (le_max_left B 1), ?_⟩
  intro l₁ m₀ hgood
  -- the exponent family: `2 ^ (chosen threshold)`
  let K : ℕ → ℕ → ℕ :=
    fun l₁ m₀ => 2 ^ (Classical.choose (tailK_exists ρ r p Cρ Cκ B hT l₁ m₀))
  have hKspec : ∀ (l₁ m₀ : ℕ),
      (Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) →
        ((Classical.choose (tailK_exists ρ r p Cρ Cκ B hT l₁ m₀) : ℕ) : ℝ) + 1
          ≤ Cκ * (1 + (l₁ : ℝ)) ^ 2) ∧
      (Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) →
        ∀ f : ℤ →₀ ℂ,
          MeasureTheory.eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom r
              (2 ^ Classical.choose (tailK_exists ρ r p Cρ Cκ B hT l₁ m₀))
              (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n (⇑f) y))
            (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal B *
              MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count) :=
    fun l₁ m₀ => Classical.choose_spec (tailK_exists ρ r p Cρ Cκ B hT l₁ m₀)
  -- the finitely supported estimate at the cap `K l₁ m₀`, with the constant `max B 1`
  have hfin : ∀ (l₁ m₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) →
      ∀ g : ℤ →₀ ℂ,
        MeasureTheory.eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom r (K l₁ m₀)
            (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n (⇑g) y))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (max B 1) *
            MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    intro l₁ m₀ hg g
    refine ((hKspec l₁ m₀).2 hg g).trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left B 1)) bot_le
  refine ⟨Classical.choose (tailK_exists ρ r p Cρ Cκ B hT l₁ m₀), (hKspec l₁ m₀).1 hgood, ?_⟩
  intro f
  exact varRhoFromGeneralK ρ hρ r (by linarith) p (by linarith) Cρ (max B 1)
    (lt_of_lt_of_le zero_lt_one (le_max_right B 1)) K hfin l₁ m₀ hgood f

end Work.KMTAreas.A7LoPoly
