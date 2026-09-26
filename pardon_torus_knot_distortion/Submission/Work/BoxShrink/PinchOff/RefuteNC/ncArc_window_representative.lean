import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteNC.ArcSetup

namespace Work.BoxShrink.PinchOff.RefuteNC

/-- **A window representative on one of the two slice arcs.**

If the `y`-coordinate `ncY1 φ` of the trace point `ncArc φ` lies in the closed window
`[9/10, 29/10]`, then `ncArc φ` is already the image of a parameter on one of the two closed
arcs of the slice: either `φ` reduced modulo `2π` lands in `[ncPhiA, ncPhiB]`, or it lands in the
mirror arc `[2π - ncPhiB, 2π - ncPhiA]`.  The proof reduces `φ` modulo `2π` via the floor, uses
`ncY1_mem_Icc_iff` to translate the window into a condition on `cos φ`, and then
`cos_mem_Icc_iff` to place the reduced parameter on one of the two arcs; periodicity of `ncArc`
gives the equality of the traced points. -/
theorem ncArc_window_representative {φ : ℝ}
    (h : 9 / 10 ≤ ncY1 φ ∧ ncY1 φ ≤ 29 / 10) :
    (∃ ψ ∈ Set.Icc ncPhiA ncPhiB, ncArc ψ = ncArc φ) ∨
    (∃ ψ ∈ Set.Icc (2 * Real.pi - ncPhiB) (2 * Real.pi - ncPhiA),
        ncArc ψ = ncArc φ) := by
  set k : ℤ := ⌊φ / (2 * Real.pi)⌋ with hk
  set φ₀ : ℝ := φ - 2 * Real.pi * k with hφ₀
  have htwo_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfloor : (k : ℝ) ≤ φ / (2 * Real.pi) := by rw [hk]; exact Int.floor_le _
  have hfloor' : φ / (2 * Real.pi) < (k : ℝ) + 1 := by
    rw [hk]; exact Int.lt_floor_add_one _
  have hφ₀_nonneg : 0 ≤ φ₀ := by
    have h1 : (k : ℝ) * (2 * Real.pi) ≤ φ := (le_div_iff₀ htwo_pi_pos).mp hfloor
    rw [hφ₀]; nlinarith
  have hφ₀_lt : φ₀ < 2 * Real.pi := by
    have h1 : φ < ((k : ℝ) + 1) * (2 * Real.pi) := (div_lt_iff₀ htwo_pi_pos).mp hfloor'
    rw [hφ₀]; nlinarith
  have hφ₀_le : φ₀ ≤ 2 * Real.pi := le_of_lt hφ₀_lt
  have hφeq : φ = φ₀ + (k : ℝ) * (2 * Real.pi) := by rw [hφ₀]; ring
  have hcos : Real.cos φ₀ = Real.cos φ := by
    rw [hφeq, (Real.cos_periodic.int_mul k) φ₀]
  have harc : ncArc φ₀ = ncArc φ := by
    rw [hφeq, (ncArc_periodic.int_mul k) φ₀]
  have hc : Real.cos φ ∈ Set.Icc ncCosLo ncCosHi := (ncY1_mem_Icc_iff φ).mp h
  have hc₀ : Real.cos φ₀ ∈ Set.Icc ncCosLo ncCosHi := by rw [hcos]; exact hc
  have hmem := (cos_mem_Icc_iff φ₀ hφ₀_nonneg hφ₀_le).mp hc₀
  rcases hmem with hm | hm
  · exact Or.inl ⟨φ₀, hm, harc⟩
  · exact Or.inr ⟨φ₀, hm, harc⟩

end Work.BoxShrink.PinchOff.RefuteNC
