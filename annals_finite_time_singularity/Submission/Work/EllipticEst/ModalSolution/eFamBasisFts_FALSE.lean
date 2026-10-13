/-
# `eFamBasisFts` is FALSE as stated — the third conjunct is missing a measurability hypothesis

**Verdict.**  `Work.EllipticEst.ModalSolution.eFamBasisFts` is *not* a true statement: its third
conjunct

```
∀ g : ℝ → ℝ,
  MeasureTheory.IntegrableOn (fun θ => g θ ^ 2 * Real.cos θ) Work.Spaces.Iθ →
  (∀ m : ℕ, ∫ θ in Work.Spaces.Iθ, g θ * eFam m θ * Real.cos θ = 0) →
  ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), g θ = 0
```

is missing the (a.e.) measurability of `g`.  The first hypothesis constrains only `g ^ 2 * cos θ`
(`MeasureTheory.IntegrableOn` is `AEStronglyMeasurable ∧ HasFiniteIntegral`), hence forces only
`|g|` — and not `g` — to be a.e. strongly measurable; and the Bochner integral of a function which
is *not* a.e. strongly measurable is `0` *by convention*
(`MeasureTheory.integral_non_aestronglyMeasurable`: `¬ AEStronglyMeasurable f μ → ∫ a, f a ∂μ = 0`),
so the orthogonality hypothesis can hold *vacuously*.

**The counterexample.**  Let `A ⊆ ℝ` be non-Lebesgue-measurable (Vitali; equivalently `A` is not
`NullMeasurableSet` for `volume`) and set `g := 1_A - 1_{Aᶜ}`, so that `g = ±1` everywhere and `g`
is not a.e. strongly measurable.  Then

* `∫ θ in Iθ, g θ ^ 2 * cos θ = ∫ θ in Iθ, cos θ`, which is finite;
* for every `m`, the integrand `θ ↦ g θ · eFam m θ · cos θ` is *not* a.e. strongly measurable:
  dividing it by the a.e. nonvanishing factor `θ ↦ eFam m θ · cos θ` would express `g` as an a.e.
  strongly measurable function.  Note `eFam m θ · cos θ = cos²θ · C^{(3/2)}_{2m+1}(sin θ)` and
  `C^{(3/2)}_{2m+1} = gC (2m+1)` is a nonzero polynomial of degree `2m+1` (leading coefficient
  `c m ≠ 0` in the notation of `gCSpanDefs`/`gC_span_eq`), so each mode vanishes only on the
  finite set `{0, π/2} ∪ sin⁻¹{gC (2m+1) = 0} ∩ Iθ`.  Hence every integral in the second
  hypothesis is `0` by convention;
* `g ≠ 0` everywhere, so `g =ᵐ 0` is false.

So both hypotheses hold while the conclusion fails.  The same defect was found (and fixed) in this
workspace for `Work.FTS.PhiStar.Gegenbauer.odd_powers_complete`, which was refuted for exactly this
reason and replaced by `odd_powers_complete_of_aestronglyMeasurable` (adding
`AEStronglyMeasurable g (volume.restrict (Icc 0 1))`).  The corrected third conjunct (with that
hypothesis added) is the statement reviewed as `FTS/PhiStar/Gegenbauer/eFam_complete`.  See
`NOTES_eFamBasisFts.md` next to this file.

**What this file machine-checks.**  Mathlib cannot *construct* a non-measurable set (it has no
Vitali set), so the existence of the `±1`-valued function is an explicit hypothesis, exactly as in
`odd_powers_complete_counterexample.lean`.  The only other hypothesis is the elementary fact that
the modes vanish only on a null set.  Given those two hypotheses, this file proves that the third
conjunct fails, and hence that the whole requested conjunction (`eFamBasisFtsProp`, a verbatim copy
of the target's type) fails.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory

namespace Work.EllipticEst.ModalSolution

/-- The proposition asserted by `Work.EllipticEst.ModalSolution.eFamBasisFts`, copied
verbatim (so that its negation can be phrased without any risk of a parenthesisation slip;
`∧` is right associative, exactly as in the original). -/
def eFamBasisFtsProp : Prop :=
  (∀ m n : ℕ, m ≠ n → ∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ
        * Real.cos θ = 0) ∧
  (∀ m : ℕ, ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2
        * Real.cos θ
      = ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5)) ∧
  (∀ g : ℝ → ℝ,
    MeasureTheory.IntegrableOn (fun θ => g θ ^ 2 * Real.cos θ) Work.Spaces.Iθ →
    (∀ m : ℕ, ∫ θ in Work.Spaces.Iθ, g θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Real.cos θ = 0) →
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), g θ = 0)

/-- **The first conjunct is true, in the set-integral form used in `eFamBasisFts`.**  This is the
three-line conversion of `Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal` (interval-integral form):
the set integral over `Iθ = Icc 0 (π/2)` equals the interval integral `∫ θ in (0)..(π/2)` because
`Icc` and `Ioc` differ by the single point `0`. -/
theorem eFam_orthogonal_Iθ (m n : ℕ) (hmn : m ≠ n) :
    (∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ
        * Real.cos θ) = 0 := by
  have h := Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn
  simp only [Work.Spaces.Iθ]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
  exact h

/-- The `m`-th mode weight `θ ↦ eFam m θ · cos θ` is continuous. -/
lemma continuous_eFam_mul_cos (m : ℕ) :
    Continuous (fun θ : ℝ =>
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) := by
  have hFam : Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
    simp only [Work.FTS.PhiStar.Gegenbauer.eFam]
    exact Real.continuous_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
        Real.continuous_sin)
  exact hFam.mul Real.continuous_cos

/-- **Non-measurability is inherited by the products with the modes.**  If `g` is not a.e. strongly
measurable for `volume.restrict Iθ` and the mode weights vanish only on a null set, then for every
`m` the integrand `θ ↦ g θ · eFam m θ · cos θ` is not a.e. strongly measurable either. -/
lemma not_aestronglyMeasurable_mul_eFam
    {g : ℝ → ℝ} (hg : ¬ MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hφ : ∀ m : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ ≠ 0)
    (m : ℕ) :
    ¬ MeasureTheory.AEStronglyMeasurable
      (fun θ => g θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  set φ : ℝ → ℝ := fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ with hφdef
  intro hprod
  obtain ⟨v, hv_sm, hv_eq⟩ := hprod
  have hφ_sm : StronglyMeasurable φ := (continuous_eFam_mul_cos m).stronglyMeasurable
  have hdiv : StronglyMeasurable (fun θ : ℝ => v θ / φ θ) := hv_sm.div hφ_sm
  have hae : g =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ : ℝ => v θ / φ θ := by
    filter_upwards [hv_eq, hφ m] with θ hv hne
    rw [mul_assoc] at hv
    exact (eq_div_iff hne).mpr hv
  exact hg (hdiv.aestronglyMeasurable.congr hae.symm)

/-- **The third conjunct of `eFamBasisFts` fails.**  A `±1`-valued `g` which is not a.e. strongly
measurable satisfies the two hypotheses of the third conjunct *vacuously* (the first because
`g ^ 2 = 1`, the second because every integrand is a non-a.e.-strongly-measurable function, whose
Bochner integral is `0` by convention) while its conclusion `g =ᵐ 0` is false (`g` never
vanishes). -/
theorem third_conjunct_false_of_nonmeasurable
    (hg : ∃ g : ℝ → ℝ, (∀ θ, g θ = 1 ∨ g θ = -1) ∧
      ¬ MeasureTheory.AEStronglyMeasurable g
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hφ : ∀ m : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ ≠ 0) :
    ¬ (∀ g : ℝ → ℝ,
      MeasureTheory.IntegrableOn (fun θ => g θ ^ 2 * Real.cos θ) Work.Spaces.Iθ →
      (∀ m : ℕ, ∫ θ in Work.Spaces.Iθ, g θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Real.cos θ = 0) →
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), g θ = 0) := by
  intro hconj
  obtain ⟨g, hgv, hgnm⟩ := hg
  -- `g ^ 2 = 1`, so the integrability hypothesis is satisfied
  have hsq : (fun θ : ℝ => g θ ^ 2 * Real.cos θ) = fun θ : ℝ => Real.cos θ := by
    funext θ
    rcases hgv θ with hθ | hθ <;> simp [hθ]
  have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ => g θ ^ 2 * Real.cos θ)
      Work.Spaces.Iθ := by
    rw [hsq]
    exact Real.continuous_cos.continuousOn.integrableOn_compact isCompact_Icc
  -- every integral is `0` by convention, since no integrand is a.e. strongly measurable
  have hzero : ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ, g θ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) = 0 :=
    fun m => MeasureTheory.integral_non_aestronglyMeasurable
      (not_aestronglyMeasurable_mul_eFam hgnm hφ m)
  have hone := hconj g hInt hzero
  -- but `g` never vanishes
  have hne : ∀ θ : ℝ, g θ ≠ 0 := by
    intro θ
    rcases hgv θ with hθ | hθ <;> simp [hθ]
  have hset : {θ : ℝ | g θ ≠ 0} = Set.univ := by
    ext θ
    simp [hne θ]
  have hnull := MeasureTheory.ae_iff.mp hone
  rw [hset] at hnull
  simp only [Work.Spaces.Iθ] at hnull
  rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, sub_zero] at hnull
  exact absurd hnull (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))

/-- **`eFamBasisFts` is false as stated** (same hypotheses as
`third_conjunct_false_of_nonmeasurable`): the requested conjunction fails because its third
conjunct does. -/
theorem not_eFamBasisFts
    (hg : ∃ g : ℝ → ℝ, (∀ θ, g θ = 1 ∨ g θ = -1) ∧
      ¬ MeasureTheory.AEStronglyMeasurable g
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hφ : ∀ m : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ ≠ 0) :
    ¬ eFamBasisFtsProp :=
  fun hP => third_conjunct_false_of_nonmeasurable hg hφ hP.2.2

end Work.EllipticEst.ModalSolution
