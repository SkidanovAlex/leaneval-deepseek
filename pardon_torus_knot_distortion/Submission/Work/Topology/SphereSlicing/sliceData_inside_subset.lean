import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

namespace Work.Topology.SphereSlicing

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- A point of the closed unit disc of `ℂ` lying on the unit circle is `circlePoint θ` for
some real `θ`. -/
theorem exists_circlePoint_eq (z : Work.InnermostDisk.Disc) (hz : ‖(z : ℂ)‖ = 1) :
    ∃ θ : ℝ, Work.CoreTopology.circlePoint θ = z := by
  refine ⟨Complex.arg (z : ℂ), Subtype.ext ?_⟩
  rw [Work.CoreTopology.circlePoint_coe]
  have h := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [hz] at h
  simpa using h

theorem sliceData_inside_subset {P : Work.CoreTopology.ParamTorus}
    {S : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.Topology.SphereSlicing.SliceData P S) (i j : h.ι)
    (hij : ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧ h.disc i z ∈ Set.range (h.c j).γ) :
    Set.range (h.c j).γ ⊆ Set.range (h.disc i) := by
  by_cases hji : j = i
  · rw [hji]
    rintro x ⟨t, rfl⟩
    exact ⟨Work.CoreTopology.circlePoint t, h.disc_boundary i t⟩
  · have hdisj : Disjoint (Set.range (h.c i).γ) (Set.range (h.c j).γ) :=
      h.disjoint (Ne.symm hji)
    -- the interior of the disc of `i`, which is open in `S`
    have hUopen : IsOpen {x : S | ∃ z : Work.InnermostDisk.Disc,
        ‖(z : ℂ)‖ < 1 ∧ h.disc i z = (x : R3)} := h.open_interior i
    -- the disc of `i` is compact, hence closed, hence so is its trace on `S`
    have hBclosed : IsClosed (Set.range (h.disc i)) :=
      (isCompact_range (h.disc i).continuous).isClosed
    have hBcclosed : IsClosed {x : S | (x : R3) ∈ Set.range (h.disc i)} :=
      hBclosed.preimage continuous_subtype_val
    -- the closure of the interior is contained in the disc
    have hclU : closure {x : S | ∃ z : Work.InnermostDisk.Disc,
        ‖(z : ℂ)‖ < 1 ∧ h.disc i z = (x : R3)} ⊆
        {x : S | (x : R3) ∈ Set.range (h.disc i)} :=
      closure_minimal (by rintro x ⟨z, _, hz⟩; exact ⟨z, hz⟩) hBcclosed
    -- the curve of `j` starts inside the disc of `i`, so meets its interior
    have hCU : ({x : S | (x : R3) ∈ Set.range (h.c j).γ} ∩
        {x : S | ∃ z : Work.InnermostDisk.Disc,
          ‖(z : ℂ)‖ < 1 ∧ h.disc i z = (x : R3)}).Nonempty := by
      obtain ⟨z, hzlt, hzr⟩ := hij
      obtain ⟨t, ht⟩ := hzr
      exact ⟨⟨h.disc i z, h.disc_mem i z⟩, ⟨⟨t, ht⟩, ⟨z, hzlt, rfl⟩⟩⟩
    -- the curve of `j` is preconnected (as the range of a continuous map)
    have hCpre : IsPreconnected {x : S | (x : R3) ∈ Set.range (h.c j).γ} := by
      apply (Topology.IsInducing.subtypeVal.isPreconnected_image).mp
      have himg : (Subtype.val : S → R3) '' {x : S | (x : R3) ∈ Set.range (h.c j).γ}
          = Set.range (h.c j).γ := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩; exact hy
        · rintro ⟨t, rfl⟩
          exact ⟨⟨(h.c j).γ t, h.mem j t⟩, ⟨t, rfl⟩, rfl⟩
      rw [himg]
      exact isPreconnected_range (h.c j).cont
    -- a point of the disc of `i` that also lies on the curve of `j` lies in the interior
    have hcover : {x : S | (x : R3) ∈ Set.range (h.c j).γ} ⊆
        {x : S | ∃ z : Work.InnermostDisk.Disc,
          ‖(z : ℂ)‖ < 1 ∧ h.disc i z = (x : R3)}
          ∪ (closure {x : S | ∃ z : Work.InnermostDisk.Disc,
              ‖(z : ℂ)‖ < 1 ∧ h.disc i z = (x : R3)})ᶜ := by
      intro x hx
      by_cases hxB : (x : R3) ∈ Set.range (h.disc i)
      · left
        obtain ⟨z, hz⟩ := hxB
        refine ⟨z, ?_, hz⟩
        by_contra hlt
        have hge : (1 : ℝ) ≤ ‖(z : ℂ)‖ := not_lt.mp hlt
        have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa using Metric.mem_closedBall.mp z.2
        have hzn : ‖(z : ℂ)‖ = 1 := le_antisymm hle hge
        obtain ⟨θ, hθ⟩ := exists_circlePoint_eq z hzn
        have hxci : (x : R3) ∈ Set.range (h.c i).γ :=
          ⟨θ, by rw [← hz, ← hθ, h.disc_boundary i θ]⟩
        exact Set.disjoint_left.1 hdisj hxci hx
      · right
        exact fun hmem => hxB (hclU hmem)
    have hCUsub : {x : S | (x : R3) ∈ Set.range (h.c j).γ} ⊆
        {x : S | ∃ z : Work.InnermostDisk.Disc,
          ‖(z : ℂ)‖ < 1 ∧ h.disc i z = (x : R3)} :=
      hCpre.subset_left_of_subset_union hUopen isClosed_closure.isOpen_compl
        (disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure))
        hcover hCU
    rintro x ⟨t, rfl⟩
    have hx : (⟨(h.c j).γ t, h.mem j t⟩ : S) ∈
        {x : S | (x : R3) ∈ Set.range (h.c j).γ} := ⟨t, rfl⟩
    obtain ⟨z, _, hz⟩ := hCUsub hx
    exact ⟨z, hz⟩

end Work.Topology.SphereSlicing
