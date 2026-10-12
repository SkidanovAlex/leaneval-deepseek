import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Submission.Work.BoseB6Est.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open MeasureTheory

/-- The affine profile `β r = 8π + η r` on `[0,T]`, zero beyond: an `FsKernel`.

This is the model kernel of the FS regime: `β(t) = 8π + η t` on the mode range
`0 ≤ t ≤ T` (the χ-Taylor bound `|β − 8π| ≤ η t` being an equality), and `β`
vanishing beyond the momentum cutoff `T`.  All the structural fields
(measurability, nonnegativity, the bound `B = 8π + ηT`, the closeness and the
support) hold for it. -/
theorem exists_fsKernel_affine {η T : ℝ} (hη : 0 ≤ η) (hT : 0 ≤ T) :
    ∃ K : Work.BoseB6Est.FsKernel, K.η = η ∧ K.T = T
      ∧ (∀ r : ℝ, 0 ≤ r → r ≤ T → K.β r = 8 * Real.pi + η * r)
      ∧ (∀ r : ℝ, T < r → K.β r = 0) := by
  have hpi : (0 : ℝ) ≤ 8 * Real.pi := by positivity
  have hBnn : 0 ≤ 8 * Real.pi + η * T := by
    have := mul_nonneg hη hT
    linarith
  refine ⟨{ β := fun r : ℝ => if r ∈ Set.Icc (0 : ℝ) T then 8 * Real.pi + η * r else 0
            B := 8 * Real.pi + η * T
            η := η
            T := T
            Bnn := hBnn
            ηnn := hη
            Tnn := hT
            meas := Measurable.ite measurableSet_Icc
              (measurable_const.add (measurable_const.mul measurable_id))
              measurable_const
            nonneg := ?_
            bound := ?_
            close := ?_
            support := ?_ }, rfl, rfl, ?_, ?_⟩
  · -- nonnegativity: `8π + ηr ≥ 0` on `[0,T]`, `0` off it
    intro r
    by_cases h : r ∈ Set.Icc (0 : ℝ) T
    · obtain ⟨h1, h2⟩ := Set.mem_Icc.mp h
      rw [if_pos h]
      have := mul_nonneg hη h1
      linarith
    · rw [if_neg h]
  · -- the bound `β ≤ 8π + ηT`
    intro r
    by_cases h : r ∈ Set.Icc (0 : ℝ) T
    · obtain ⟨h1, h2⟩ := Set.mem_Icc.mp h
      rw [if_pos h]
      have := mul_le_mul_of_nonneg_left h2 hη
      linarith
    · rw [if_neg h]
      exact hBnn
  · -- closeness on the support: `|β r − 8π| = η r`
    intro r h0 hrT
    rw [if_pos (show r ∈ Set.Icc (0 : ℝ) T from Set.mem_Icc.mpr ⟨h0, hrT⟩),
      show 8 * Real.pi + η * r - 8 * Real.pi = η * r from by ring,
      abs_of_nonneg (mul_nonneg hη h0)]
  · -- the cutoff
    intro r hr
    rw [if_neg (fun h : r ∈ Set.Icc (0 : ℝ) T => absurd (Set.mem_Icc.mp h).2 (not_le.mpr hr))]
  · -- `K.β = 8π + η·` on `[0,T]`
    intro r h0 hrT
    change (if r ∈ Set.Icc (0 : ℝ) T then 8 * Real.pi + η * r else 0)
      = 8 * Real.pi + η * r
    rw [if_pos (show r ∈ Set.Icc (0 : ℝ) T from Set.mem_Icc.mpr ⟨h0, hrT⟩)]
  · -- `K.β = 0` beyond `T`
    intro r hr
    change (if r ∈ Set.Icc (0 : ℝ) T then 8 * Real.pi + η * r else 0) = 0
    rw [if_neg (fun h : r ∈ Set.Icc (0 : ℝ) T => absurd (Set.mem_Icc.mp h).2 (not_le.mpr hr))]

end Work.BoseBogFS
