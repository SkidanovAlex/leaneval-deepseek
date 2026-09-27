import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.EKLComp.V_hasBasis_nhds_one

namespace Work.EKLC6Core

open MeasureTheory
open Work.EKLContract

theorem shape_mass_pos {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3} {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A) {x : Work.EKLContract.X3}
    (hxX : x ∈ X') (hxZ : x ∈ Z) :
    0 < ν x (Work.EKLContract.shape A U x) ∧ ν x (Work.EKLContract.shape A U x) < ⊤ := by
  obtain ⟨-, -, -, hplaqx⟩ := hplaq
  obtain ⟨-, -, ⟨O, hOopen, hOshape⟩, ⟨C, hC⟩⟩ := hplaqx x hxZ
  -- the identity lies in the atom `[x]_A`, hence in the shape and in the open set `O`
  have hxatom : x ∈ atom A x := by
    rw [atom, Set.mem_sInter]
    rintro s ⟨-, hs⟩
    exact hs
  have h1shape : (1 : SL3) ∈ shape A U x := ⟨U.one_mem, by simpa using hxatom⟩
  have h1O : (1 : SL3) ∈ O := by
    have h : (1 : SL3) ∈ O ∩ (U : Set SL3) := by rwa [← hOshape]
    exact h.1
  -- a displacement neighbourhood of the identity inside `O`
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (Work.EKLComp.V_hasBasis_nhds_one.mem_iff).mp (hOopen.mem_nhds h1O)
  -- positivity
  have hsub : V δ ∩ (U : Set SL3) ⊆ shape A U x := by
    intro u hu
    rw [hOshape]
    exact ⟨hδsub hu.1, hu.2⟩
  have hsplit : V δ = (V δ ∩ (U : Set SL3)) ∪ (V δ ∩ (U : Set SL3)ᶜ) := by
    ext g; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]; tauto
  have hnull : ν x (V δ ∩ (U : Set SL3)ᶜ) = 0 :=
    measure_mono_null Set.inter_subset_right (hL.carried x hxX)
  have hle : ν x (V δ) ≤ ν x (V δ ∩ (U : Set SL3)) := by
    calc ν x (V δ) = ν x ((V δ ∩ (U : Set SL3)) ∪ (V δ ∩ (U : Set SL3)ᶜ)) :=
          congrArg (ν x) hsplit
      _ ≤ ν x (V δ ∩ (U : Set SL3)) + ν x (V δ ∩ (U : Set SL3)ᶜ) := measure_union_le _ _
      _ = ν x (V δ ∩ (U : Set SL3)) := by rw [hnull, add_zero]
  refine ⟨lt_of_lt_of_le (hL.pos x hxX δ hδpos) (le_trans hle (measure_mono hsub)), ?_⟩
  -- finiteness: the shape has bounded entries, hence is relatively compact
  have hbox : shape A U x ⊆ {g : SL3 | ∀ i j, -C ≤ g i j ∧ g i j ≤ C} := by
    intro u hu i j
    exact abs_le.mp (hC u hu i j)
  exact lt_of_le_of_lt (measure_mono hbox)
    ((hL.radon x hxX).lt_top_of_isCompact
      (Work.EKLProd.sl3EntryBox_compact (fun _ _ => -C) (fun _ _ => C)))

end Work.EKLC6Core
