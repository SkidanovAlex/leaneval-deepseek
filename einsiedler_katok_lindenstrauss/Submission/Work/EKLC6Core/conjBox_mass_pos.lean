import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLProd.sl3EntryBox_compact

/-!
# `EKLC6Core.conjBox_mass_pos`

The contracted box `conjBox U t = aDiag t · B₁^U · (aDiag t)⁻¹` has **positive and finite**
`ν x`-mass at every point `x` of the leaf-wise domain, for `U` a horospherical subgroup.

Both halves are elementary geometry of the boxes:

* **Positivity.**  `conjBox_nhds` (`EKLC6Core.conjBox_nhds`) says that `conjBox U t` contains
  `V δ ∩ U` for some `δ > 0`.  The leaf-wise measure `ν x` is carried by `U`
  (`IsLeafwise.carried`), so `ν x (V δ ∩ U) = ν x (V δ)`, and the latter is positive by
  `IsLeafwise.pos`.
* **Finiteness.**  Conjugating by `aDiag t` scales the entry `(i,j)` by `exp (tᵢ - tⱼ)`
  (`aDiag_conj_entry`), while `B₁^U` has entries bounded by `2`; hence `conjBox U t` sits inside
  an entrywise box, which is compact (`EKLProd.sl3EntryBox_compact`).  A measure finite on
  compacta (`IsLeafwise.radon`) gives a finite value there.

This is the "non-degeneracy" of the contracted box that makes the pointwise information
`growthFun U ν t = -log (ν x (conjBox U t))` a well-defined real number, and hence the entropy
contribution `D_μ(a,U)` of Pisa 7.6 an honest Birkhoff average.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Entrywise conjugation by the diagonal flow -/

/-- The diagonal flow scales the entry `(i,j)` of a matrix by `exp (tᵢ - tⱼ)`, in the form
needed for the *image* `aDiag t · g · (aDiag t)⁻¹` defining `conjBox`. -/
theorem aDiag_conj_entry_right (s : Fin 3 → ℝ) (g : SL3) (i j : Fin 3) :
    ((aDiag s * g * (aDiag s)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
      = Real.exp (s i - s j) * (g : Matrix (Fin 3) (Fin 3) ℝ) i j := by
  have hinv : (aDiag s)⁻¹ = aDiag (-s) := inv_eq_of_mul_eq_one_left (aDiag_neg_mul s)
  rw [hinv]
  have h := aDiag_conj_entry (-s) g i j
  rw [show -(-s) = s from neg_neg s] at h
  rw [h]
  congr 1
  simp only [Pi.neg_apply]
  ring_nf

/-! ## The contracted box sits in a compact entrywise box -/

/-- Every element of `conjBox U t` has entries bounded by `2 · exp (tᵢ - tⱼ)`: an element of the
conjugated box is `aDiag t · h · (aDiag t)⁻¹` with `h ∈ B₁^U`, so `|hᵢⱼ| ≤ 2`. -/
theorem conjBox_subset_entryBox {U : Subgroup SL3} (t : Fin 3 → ℝ) :
    conjBox U t ⊆ {g : SL3 | ∀ i j,
      -(2 * Real.exp (t i - t j)) ≤ (g : Matrix (Fin 3) (Fin 3) ℝ) i j ∧
      (g : Matrix (Fin 3) (Fin 3) ℝ) i j ≤ 2 * Real.exp (t i - t j)} := by
  rintro g ⟨h, hh, rfl⟩ i j
  rw [aDiag_conj_entry_right]
  have hb : |(h : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 2 := by
    have h1 : |(h : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := hh.2 i j
    rcases eq_or_ne i j with hij | hij
    · subst hij
      rw [Matrix.one_apply_eq] at h1
      have h1' := abs_le.mp h1
      rw [abs_le]
      constructor <;> linarith [h1'.1, h1'.2]
    · rw [Matrix.one_apply_ne hij, sub_zero] at h1
      have h1' := abs_le.mp h1
      rw [abs_le]
      constructor <;> linarith [h1'.1, h1'.2]
  have hb' := abs_le.mp hb
  have hE : 0 < Real.exp (t i - t j) := Real.exp_pos _
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hb'.1 (le_of_lt hE)
    nlinarith [hmul]
  · have hmul := mul_le_mul_of_nonneg_left hb'.2 (le_of_lt hE)
    nlinarith [hmul]

/-! ## The main statement -/

theorem conjBox_mass_pos {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3} {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hU : Work.EKLContract.IsHoro U) (t : Fin 3 → ℝ) {x : Work.EKLContract.X3} (hxX : x ∈ X') :
    0 < ν x (Work.EKLC6Core.conjBox U t) ∧ ν x (Work.EKLC6Core.conjBox U t) < ⊤ := by
  constructor
  · -- positivity: `conjBox U t ⊇ V δ ∩ U`, and `ν x` is carried by `U`
    obtain ⟨δ, hδpos, hδ⟩ := conjBox_nhds hU t
    have hdiff : ν x (V δ \ (V δ ∩ (U : Set SL3))) = 0 :=
      measure_mono_null (fun g hg => fun hgU => hg.2 ⟨hg.1, hgU⟩) (hL.carried x hxX)
    have hVe : ν x (V δ ∩ (U : Set SL3)) = ν x (V δ) :=
      measure_eq_measure_of_null_sdiff Set.inter_subset_left hdiff
    have hpos := hL.pos x hxX δ hδpos
    rw [← hVe] at hpos
    exact lt_of_lt_of_le hpos (measure_mono (fun g hg => hδ g hg.1 hg.2))
  · -- finiteness: `conjBox U t` is contained in a compact entrywise box
    refine lt_of_le_of_lt (measure_mono (conjBox_subset_entryBox (U := U) t)) ?_
    exact (hL.radon x hxX).lt_top_of_isCompact
      (Work.EKLProd.sl3EntryBox_compact (fun i j => -(2 * Real.exp (t i - t j)))
        (fun i j => 2 * Real.exp (t i - t j)))

end Work.EKLC6Core

end
