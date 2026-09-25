import Mathlib
import Submission.Work.BourgainPlan.Maximal.eLpNorm_varRhoAll_le_geometric

/-!
# Elementary `ℓʳ`-tools for the glue of the large-scale level estimate

* `iSup_tail_eq_lat`: the supremum over `k ≥ K₀` as a supremum over the shifted index.
* `eLpNorm_mono_enorm_lat`: monotonicity of `eLpNorm` for `ℝ≥0∞`-valued functions.
* `eLpNorm_add_le_enorm_lat`: the two-term triangle inequality for `ℝ≥0∞`-valued functions.
* `tail_sup_le_of_per_k_lat`: if the family `T (K₀ + j)` has `ℓʳ`-bounds `Mexp j`, then the
  pointwise supremum over the tail has `ℓʳ`-norm at most `∑' j, Mexp j` times `‖v‖`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.Maximal

noncomputable section

open Work.BourgainPlan.Maximal

/-- **The tail supremum of a family over `k ≥ K₀` as a supremum over the shifted family.** -/
lemma iSup_tail_eq_lat (K₀ : ℕ) (T : ℕ → ℤ → ℂ) (m : ℤ) :
    (⨆ k : ℕ, ⨆ (_ : K₀ ≤ k), ‖T k m‖ₑ) = ⨆ j : ℕ, ‖T (K₀ + j) m‖ₑ := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun k => iSup_le fun hk => ?_
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact le_iSup (fun j : ℕ => ‖T (K₀ + j) m‖ₑ) j
  · refine iSup_le fun j => ?_
    exact (le_iSup (fun _ : K₀ ≤ K₀ + j => ‖T (K₀ + j) m‖ₑ) (Nat.le_add_right K₀ j)).trans
      (le_iSup (fun k : ℕ => ⨆ (_ : K₀ ≤ k), ‖T k m‖ₑ) (K₀ + j))

/-- Monotonicity of `eLpNorm` for `ℝ≥0∞`-valued functions (the general `eLpNorm_mono` needs a
`NormedAddCommGroup`, which `ℝ≥0∞` is not). -/
lemma eLpNorm_mono_enorm_lat {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ}
    (hp : 0 < p) {f g : α → ℝ≥0∞} (h : f ≤ g)
    (hf : AEStronglyMeasurable f μ := by exact AEStronglyMeasurable.of_discrete) :
    MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ ≤ MeasureTheory.eLpNorm g (ENNReal.ofReal p) μ :=
  MeasureTheory.eLpNorm_mono_enorm hf fun x => by simp only [enorm_eq_self]; exact h x

/-- **The two-term triangle inequality for `eLpNorm` of `ℝ≥0∞`-valued functions.** -/
lemma eLpNorm_add_le_enorm_lat {r : ℝ} (hr : 1 < r) (F G : ℤ → ℝ≥0∞) :
    MeasureTheory.eLpNorm (F + G) (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm F (ENNReal.ofReal r) MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm G (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  exact MeasureTheory.eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hr.le)

/-- **The summation step with an arbitrary constant.**  If the individual operators of a family
`T k`, `k ≥ K₀`, satisfy the `ℓʳ` bound `‖T (K₀ + j) v‖_{ℓʳ} ≤ Mexp j ‖v‖_{ℓʳ}`, then the
`ℓʳ`-norm of the pointwise supremum over the tail is bounded by `(∑' j, Mexp j) ‖v‖_{ℓʳ}`. -/
lemma tail_sup_le_of_per_k_lat (K₀ : ℕ) (T : ℕ → ℤ → ℂ) (v : ℤ → ℂ) (Mexp : ℕ → ℝ)
    {r : ℝ} (hr : 1 ≤ r)
    (hperj : ∀ j : ℕ, MeasureTheory.eLpNorm (T (K₀ + j)) (ENNReal.ofReal r) Measure.count
      ≤ ENNReal.ofReal (Mexp j) * MeasureTheory.eLpNorm v (ENNReal.ofReal r) Measure.count)
    (hMnn : ∀ j : ℕ, 0 ≤ Mexp j) (hsumm : Summable Mexp) :
    MeasureTheory.eLpNorm (fun m : ℤ => ⨆ k : ℕ, ⨆ (_ : K₀ ≤ k), ‖T k m‖ₑ)
        (ENNReal.ofReal r) Measure.count
      ≤ ENNReal.ofReal (∑' j : ℕ, Mexp j)
        * MeasureTheory.eLpNorm v (ENNReal.ofReal r) Measure.count := by
  set N : ℝ≥0∞ := MeasureTheory.eLpNorm v (ENNReal.ofReal r) Measure.count with hNdef
  have hfun : (fun m : ℤ => ⨆ k : ℕ, ⨆ (_ : K₀ ≤ k), ‖T k m‖ₑ)
      = fun m : ℤ => ⨆ j : ℕ, ‖T (K₀ + j) m‖ₑ := funext fun m => iSup_tail_eq_lat K₀ T m
  have h1 : MeasureTheory.eLpNorm (fun m : ℤ => ⨆ j : ℕ, ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count
      ≤ MeasureTheory.eLpNorm (fun m : ℤ => ∑' j : ℕ, ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count :=
    eLpNorm_mono_enorm_lat (lt_of_lt_of_le zero_lt_one hr)
      (fun m => iSup_le (fun j => ENNReal.le_tsum (f := fun j => ‖T (K₀ + j) m‖ₑ) j))
  have h2 : MeasureTheory.eLpNorm (fun m : ℤ => ∑' j : ℕ, ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count
      ≤ ∑' j : ℕ, MeasureTheory.eLpNorm (fun m : ℤ => ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count :=
    eLpNorm_tsum_le_tsum_eLpNorm (ENNReal.one_le_ofReal.mpr hr) ENNReal.ofReal_ne_top
      (fun j => measurable_of_int _)
  have h3 : ∑' j : ℕ, MeasureTheory.eLpNorm (fun m : ℤ => ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count
      ≤ ∑' j : ℕ, ENNReal.ofReal (Mexp j) * N := by
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [eLpNorm_enorm _ AEStronglyMeasurable.of_discrete, hNdef]
    exact hperj j
  have h4 : ∑' j : ℕ, ENNReal.ofReal (Mexp j) * N
      = (∑' j : ℕ, ENNReal.ofReal (Mexp j)) * N := ENNReal.tsum_mul_right
  have h5 : (∑' j : ℕ, ENNReal.ofReal (Mexp j)) = ENNReal.ofReal (∑' j : ℕ, Mexp j) :=
    (ENNReal.ofReal_tsum_of_nonneg hMnn hsumm).symm
  calc MeasureTheory.eLpNorm (fun m : ℤ => ⨆ k : ℕ, ⨆ (_ : K₀ ≤ k), ‖T k m‖ₑ)
        (ENNReal.ofReal r) Measure.count
      = MeasureTheory.eLpNorm (fun m : ℤ => ⨆ j : ℕ, ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count := by rw [hfun]
    _ ≤ MeasureTheory.eLpNorm (fun m : ℤ => ∑' j : ℕ, ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count := h1
    _ ≤ ∑' j : ℕ, MeasureTheory.eLpNorm (fun m : ℤ => ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count := h2
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (Mexp j) * N := h3
    _ = (∑' j : ℕ, ENNReal.ofReal (Mexp j)) * N := h4
    _ = ENNReal.ofReal (∑' j : ℕ, Mexp j) * N := by rw [h5]
    _ = ENNReal.ofReal (∑' j : ℕ, Mexp j)
        * MeasureTheory.eLpNorm v (ENNReal.ofReal r) Measure.count := by rw [hNdef]

end

end Work.Maximal
