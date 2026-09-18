import Submission.DS.Truncate
import Submission.DS.CircCorr
import Submission.DS.CircBound
import Mathlib.NumberTheory.WellApproximable

open scoped Nat ENNReal NNReal
open Set Filter MeasureTheory
open DuffinSchaefferConjecture

/-!
# Bridge from `[0,1]` to the circle (Gallagher zero-one law)

`W ψ ⊆ [0,1]` is the set of points lying in infinitely many coprime
rational-approximation sets `Acopr ψ q`.  On the circle `𝕊 = AddCircle 1`, Mathlib's
Gallagher theorem (`AddCircle.addWellApproximable_ae_empty_or_univ`) says the analogous
set is almost empty or almost everything.  This file transfers the two sets:

1. `W ψ` only depends on the values of `ψ` at a cofinite set of denominators;
2. the radius function `radSeq ψ n = ψ(n)/n` (zero for `n = 0`) realises the circle
   approximation radii;
3. (further) the per-denominator sets correspond through the measure-preserving quotient
   `[0,1) → 𝕊`, so that `volume (W ψ)` agrees with the circle volume of the
   `addWellApproximable` set when the radii tend to zero.
-/

namespace Submission.DS

/-- The radius sequence on `ℕ`: `radSeq ψ n = ψ(n)/n` for `n ≥ 1`, and `0` for `n = 0`. -/
noncomputable def radSeq (ψ : ℕ+ → ℝ≥0) : ℕ → ℝ :=
  fun n => if h : 0 < n then (ψ ⟨n, h⟩ : ℝ) / (n : ℝ) else 0

/-- `Acopr ψ q` depends only on `ψ q`. -/
lemma Acopr_eq_of_apply_eq {ψ χ : ℕ+ → ℝ≥0} {q : ℕ+} (h : ψ q = χ q) :
    Acopr ψ q = Acopr χ q := by
  ext x
  simp [Acopr]
  -- both sides: ∃ a, Coprime a q ∧ inequality: only ψ q differs
  constructor <;> rintro ⟨a, hc, hi⟩ <;> refine ⟨a, hc, ?_⟩
  · unfold inequality_1_7 at hi ⊢
    simpa [h] using hi
  · unfold inequality_1_7 at hi ⊢
    simpa [← h] using hi

/-- `W ψ` is unchanged if `ψ` agrees with another function on a cofinite set. -/
lemma W_of_eventually_eq {ψ χ : ℕ+ → ℝ≥0} (h : ∀ᶠ q : ℕ+ in Filter.cofinite, ψ q = χ q) :
    W ψ = W χ := by
  classical
  ext x
  unfold W
  have hlim : x ∈ limsupDenoms (Acopr ψ) ↔ x ∈ limsupDenoms (Acopr χ) := by
    unfold limsupDenoms
    change {q : ℕ+ | x ∈ Acopr ψ q}.Infinite ↔ {q : ℕ+ | x ∈ Acopr χ q}.Infinite
    apply infinite_iff_of_eventually_mem_iff
    rw [Filter.eventually_cofinite]
    have hF : {q : ℕ+ | ¬ ψ q = χ q}.Finite := Filter.eventually_cofinite.mp h
    apply Set.Finite.subset hF
    intro q hq
    by_contra hneq
    have hqeq : ψ q = χ q := not_not.mp hneq
    apply hq
    simpa using (show x ∈ Acopr ψ q ↔ x ∈ Acopr χ q from by rw [Acopr_eq_of_apply_eq hqeq])
  constructor <;> intro hx
  · rcases hx with ⟨h01, hl⟩
    exact ⟨h01, hlim.mp hl⟩
  · rcases hx with ⟨h01, hl⟩
    exact ⟨h01, hlim.mpr hl⟩



/-- The circle volume of a measurable set equals the Lebesgue measure of its lift to
`(0,1)` (the quotient map is measure-preserving on a fundamental domain). -/
lemma volume_circle_eq_lift {E : Set (AddCircle (1 : ℝ))} (hE : MeasurableSet E) :
    volume E = volume ((QuotientAddGroup.mk ⁻¹' E : Set ℝ) ∩ Set.Ioc (0 : ℝ) 1) := by
  have hA : Set.Ioc (0 : ℝ) (0 + 1) = Set.Ioc (0 : ℝ) (1 : ℝ) := by
    ext x
    simp
  have hMP : MeasurePreserving (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) volume := by
    simpa [hA] using (AddCircle.measurePreserving_mk (1 : ℝ) (0 : ℝ))
  have hEq : Measure.map (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) = volume := hMP.map_eq
  rw [← hEq]
  rw [Measure.map_apply hMP.measurable hE]
  rw [Measure.restrict_apply (hMP.measurable hE)]

/-- `W ψ ⊆ [0,1]` differs from `W ψ ∩ (0,1)` only by the null endpoints. -/
lemma W_measure_eq_inter_Ioo (ψ : ℕ+ → ℝ≥0) :
    volume (W ψ) = volume (W ψ ∩ Set.Ioo (0 : ℝ) 1) := by
  classical
  have hW01 : W ψ ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hx.1
  have hrem : W ψ ∩ (Set.Icc (0 : ℝ) 1 \ Set.Ioo (0 : ℝ) 1) ⊆ ({0} ∪ {1} : Set ℝ) := by
    intro x hx
    have hxi : x ∈ Set.Icc (0 : ℝ) 1 := hW01 hx.1
    have hxn : x ∉ Set.Ioo (0 : ℝ) 1 := hx.2.2
    have hnot : ¬ (0 < x ∧ x < 1) := by
      intro h
      exact hxn ⟨h.1, h.2⟩
    by_cases hx0 : x = 0
    · simp [hx0]
    · by_cases hx1 : x = 1
      · simp [hx1]
      · exfalso
        apply hnot
        constructor
        · exact lt_of_le_of_ne hxi.1 (by intro h; exact hx0 h.symm)
        · exact lt_of_le_of_ne hxi.2 hx1
  have hdecomp : W ψ = (W ψ ∩ Set.Ioo (0 : ℝ) 1) ∪
      (W ψ ∩ (Set.Icc (0 : ℝ) 1 \ Set.Ioo (0 : ℝ) 1)) := by
    ext x
    constructor
    · intro hx
      by_cases hxi : x ∈ Set.Ioo (0 : ℝ) 1
      · exact Or.inl ⟨hx, hxi⟩
      · exact Or.inr ⟨hx, ⟨hW01 hx, hxi⟩⟩
    · intro hx
      rcases hx with ⟨hx, _⟩ | ⟨hx, _⟩
      · exact hx
      · exact hx
  have hrem0 : volume (W ψ ∩ (Set.Icc (0 : ℝ) 1 \ Set.Ioo (0 : ℝ) 1)) = 0 := by
    apply le_antisymm _ bot_le
    exact (measure_mono hrem).trans_eq (by
      have hfin : ({0} ∪ {1} : Set ℝ).Finite := by simp
      exact hfin.measure_zero volume)
  have hmono : volume (W ψ ∩ Set.Ioo (0 : ℝ) 1) ≤ volume (W ψ) := measure_mono inter_subset_left
  apply le_antisymm ?_ hmono
  calc
    volume (W ψ) = volume ((W ψ ∩ Set.Ioo (0 : ℝ) 1) ∪
        (W ψ ∩ (Set.Icc (0 : ℝ) 1 \ Set.Ioo (0 : ℝ) 1))) :=
      congrArg volume hdecomp
    _ ≤ volume (W ψ ∩ Set.Ioo (0 : ℝ) 1) + volume (W ψ ∩ (Set.Icc (0 : ℝ) 1 \ Set.Ioo (0 : ℝ) 1)) :=
      measure_union_le _ _
    _ = volume (W ψ ∩ Set.Ioo (0 : ℝ) 1) := by rw [hrem0]; simp

end Submission.DS
