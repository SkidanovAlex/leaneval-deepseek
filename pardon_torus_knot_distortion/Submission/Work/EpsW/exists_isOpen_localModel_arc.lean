import Mathlib
import Submission.Work.Smooth.OneManifold.Defs
import Submission.Work.Smooth.OneManifold.Basic
import Submission.Work.Smooth.OneManifold.Plane.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.Plane.Slicing

namespace Work.EpsW

open LeanEval.KnotTheory.PardonDistortion

open Set

noncomputable section

open LeanEval.KnotTheory.PardonDistortion in
/-- **The local model of an injective arc.**  If `F : [0,1] → ℝ³` is continuous and injective, then at every parameter `s` there is an open set `O ∋ F s` whose trace on `Set.range F` is exactly the image of a parameter interval `(a,b)` containing `s`.  Suggested witness: take `c < (s:ℝ) < d` and `O := (F '' {x | (x:ℝ) ≤ c ∨ d ≤ (x:ℝ)})ᶜ`.  (The arc counterpart of `Work.EpsW.exists_isOpen_localModel_periodic`.) -/
theorem exists_isOpen_localModel_arc {F : C(Work.Smooth.Plane.ArcInterval, R3)}
    (hF : Function.Injective F) (s : Work.Smooth.Plane.ArcInterval) :
    ∃ (a b : ℝ) (O : Set R3), a < (s : ℝ) ∧ (s : ℝ) < b ∧ IsOpen O ∧ F s ∈ O ∧
      O ∩ Set.range F = F '' {x : Work.Smooth.Plane.ArcInterval | (x : ℝ) ∈ Set.Ioo a b} := by
  classical
  refine ⟨(s : ℝ) - 1, (s : ℝ) + 1,
    (F '' {x : Work.Smooth.Plane.ArcInterval | ¬ ((x : ℝ) ∈ Set.Ioo ((s : ℝ) - 1) ((s : ℝ) + 1))})ᶜ,
    by linarith, by linarith, ?_, ?_, ?_⟩
  · -- openness: the complement of the image of the closed (compact) parameter set
    have hclosed : IsClosed
        (F '' {x : Work.Smooth.Plane.ArcInterval |
          ¬ ((x : ℝ) ∈ Set.Ioo ((s : ℝ) - 1) ((s : ℝ) + 1))}) := by
      have : CompactSpace Work.Smooth.Plane.ArcInterval :=
        isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
      refine IsCompact.isClosed (IsCompact.image ?_ F.continuous)
      refine IsCompact.of_isClosed_subset isCompact_univ ?_ (Set.subset_univ _)
      rw [show {x : Work.Smooth.Plane.ArcInterval |
            ¬ ((x : ℝ) ∈ Set.Ioo ((s : ℝ) - 1) ((s : ℝ) + 1))}
          = (Subtype.val ⁻¹' (Set.Ioo ((s : ℝ) - 1) ((s : ℝ) + 1)))ᶜ from rfl]
      exact (isOpen_Ioo.isClosed_compl).preimage continuous_subtype_val
    exact hclosed.isOpen_compl
  · -- the point itself is not in the image of the closed parameter set
    rintro ⟨x, hx, hxs⟩
    have hxs' : x = s := hF hxs
    exact hx (by rw [hxs']; exact ⟨by linarith, by linarith⟩)
  · -- the trace of the open parameter interval
    ext y
    constructor
    · rintro ⟨hyO, hyR⟩
      rw [Set.mem_range] at hyR
      obtain ⟨x, rfl⟩ := hyR
      by_cases hx : (x : ℝ) ∈ Set.Ioo ((s : ℝ) - 1) ((s : ℝ) + 1)
      · exact ⟨x, hx, rfl⟩
      · exact absurd ⟨x, hx, rfl⟩ hyO
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ⟨x, rfl⟩⟩
      rintro ⟨z, hz, hzx⟩
      have hzx' : z = x := hF hzx
      rw [hzx'] at hz
      exact hz hx

end

end Work.EpsW
