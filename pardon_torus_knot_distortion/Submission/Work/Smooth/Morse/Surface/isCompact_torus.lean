import Mathlib
import Submission.Work.Smooth.Morse.Defs

namespace Work.Smooth.Morse.Surface

open Set

/-- **Reduction of a `2π`-periodic function of one real variable to the interval `[0, 2π]`.**

If `f : ℝ → α` is periodic with period `2π` then every value of `f` is attained at a point of
`[0, 2π]`: the fractional part `2π * fract (x / 2π)` of `x` lies in `[0, 2π]` and differs from `x`
by an integral multiple of `2π`. -/
lemma exists_mem_Icc_periodic {α : Type*} (f : ℝ → α) (h : Function.Periodic f (2 * Real.pi))
    (x : ℝ) : ∃ y ∈ Set.Icc (0 : ℝ) (2 * Real.pi), f y = f x := by
  set y : ℝ := (2 * Real.pi) * Int.fract (x / (2 * Real.pi)) with hy
  have hy0 : 0 ≤ y := by
    rw [hy]
    have := Int.fract_nonneg (x / (2 * Real.pi))
    nlinarith [Real.pi_pos]
  have hy1 : y < 2 * Real.pi := by
    rw [hy]
    have := Int.fract_lt_one (x / (2 * Real.pi))
    nlinarith [Real.pi_pos]
  refine ⟨y, ⟨hy0, le_of_lt hy1⟩, ?_⟩
  have h2 := h.int_mul ⌊x / (2 * Real.pi)⌋
  have hx : x = y + ⌊x / (2 * Real.pi)⌋ * (2 * Real.pi) := by
    have h' := Int.fract_add_floor (x / (2 * Real.pi))
    have hx2 : (2 * Real.pi) * (x / (2 * Real.pi)) = x := by field_simp
    calc x = (2 * Real.pi) * (x / (2 * Real.pi)) := hx2.symm
      _ = (2 * Real.pi) * (Int.fract (x / (2 * Real.pi)) + ↑⌊x / (2 * Real.pi)⌋) := by rw [h']
      _ = y + ⌊x / (2 * Real.pi)⌋ * (2 * Real.pi) := by rw [hy]; ring
  rw [hx]
  exact (h2 y).symm

/-- The standard torus of revolution is compact: it is the continuous image of the compact square
`[0, 2π] × [0, 2π]`, since the parametrisation `Work.Core.torusMap` is `2π`-periodic in each
variable. -/
lemma isCompact_standard_carrier : IsCompact (Work.CoreTopology.standard).carrier := by
  have hf : Continuous (fun p : ℝ × ℝ => Work.Core.torusMap p.1 p.2) :=
    Work.CoreTopology.torusMap_continuous
  have hbox : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have hrange : Set.range (fun p : ℝ × ℝ => Work.Core.torusMap p.1 p.2) =
      (fun p : ℝ × ℝ => Work.Core.torusMap p.1 p.2) ''
        (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨p, rfl⟩
      obtain ⟨y1, hy1, h1⟩ := exists_mem_Icc_periodic (fun θ : ℝ => Work.Core.torusMap θ p.2)
        (fun θ => Work.Core.torusMap_add_two_pi_left θ p.2) p.1
      obtain ⟨y2, hy2, h2⟩ := exists_mem_Icc_periodic (fun φ : ℝ => Work.Core.torusMap y1 φ)
        (fun φ => Work.Core.torusMap_add_two_pi_right y1 φ) p.2
      exact ⟨(y1, y2), ⟨hy1, hy2⟩, by simp only [h2, h1]⟩
    · rintro _ ⟨p, -, rfl⟩
      exact ⟨p, rfl⟩
  show IsCompact (Set.range (fun p : ℝ × ℝ => Work.Core.torusMap p.1 p.2))
  rw [hrange]
  exact hbox.image hf

/-- **The torus `F = ψ(F_standard)` is compact.**  It is the image of the compact standard torus
under the homeomorphism `ψ.toHomeomorph`, hence compact. -/
theorem isCompact_torus (ψ : Submission.Diffeo) :
    IsCompact (Work.Smooth.Morse.torus ψ).carrier := by
  have h : (Work.Smooth.Morse.torus ψ).carrier =
      ψ.toHomeomorph '' (Work.CoreTopology.standard).carrier :=
    Work.CoreTopology.carrier_mapHomeomorph ψ.toHomeomorph
  rw [h]
  exact isCompact_standard_carrier.image ψ.toHomeomorph.continuous

end Work.Smooth.Morse.Surface
