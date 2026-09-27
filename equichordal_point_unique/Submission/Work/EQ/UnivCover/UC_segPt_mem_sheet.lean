import Submission.Work.EQ.UnivCover.Defs

/-!
# The initial-segment point of a path lies in the sheet of the earlier segment

For a path `γ : Path x₀ x` and `s t : unitInterval`, the point `UC.segPt γ t` of the universal
cover lies in the sheet of `UC.segPt γ s` over any set `V` that contains the piece of `γ` between
`s` and `t`.
-/

set_option autoImplicit false
open _root_.Topology
open scoped Topology
open Work.EQ.UnivCover

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X]

/-- Casting the left endpoint of a path homotopy class commutes with concatenation. -/
theorem quot_cast_trans {x y z x' : X} (A : Path.Homotopic.Quotient x y)
    (B : Path.Homotopic.Quotient y z) (h : x' = x) :
    (A.cast h rfl).trans B = (A.trans B).cast h rfl := by
  rcases A with ⟨p⟩
  rcases B with ⟨q⟩
  rfl

/-- The initial segment `segTo γ u` agrees with the subpath of `γ` from `0` to `u`. -/
theorem segTo_eq_subpath_cast {x₀ x : X} (γ : Path x₀ x) (u : unitInterval) :
    segTo γ u = (γ.subpath 0 u).cast γ.source.symm rfl := by
  ext a
  simp only [segTo, Path.subpath, Path.cast, Path.coe_mk_mk, Function.comp_apply]
  congr 1
  show a * u = Set.Icc.convexComb (0 : Set.Icc (0 : ℝ) 1) u a
  ext
  simp [Set.Icc.coe_convexComb]

/-- **The initial segments of a path form a chain of sheets.**  If `V` contains the piece of `γ`
between `s` and `t`, then `UC.segPt γ t` lies in the sheet of `UC.segPt γ s` over `V`. -/
theorem UC_segPt_mem_sheet {x₀ x : X} (γ : Path x₀ x) {V : Set X} (s t : unitInterval)
    (hγ : ∀ u : unitInterval, u ∈ Set.uIcc s t → γ u ∈ V) :
    UC.segPt γ t ∈ UC.sheet (UC.segPt γ s) V := by
  rw [UC.mem_sheet_iff]
  change γ t ∈ V ∧ ∃ δ : Path (γ s) (γ t), (∀ a, δ a ∈ V) ∧
    Path.Homotopic.Quotient.mk (segTo γ t)
      = (Path.Homotopic.Quotient.mk (segTo γ s)).trans (Path.Homotopic.Quotient.mk δ)
  refine ⟨hγ t Set.right_mem_uIcc, γ.subpath s t, ?_, ?_⟩
  · intro a
    have hmem : (γ.subpath s t) a ∈ Set.range (γ.subpath s t) := ⟨a, rfl⟩
    rw [Path.range_subpath] at hmem
    obtain ⟨v, hv, hv'⟩ := hmem
    rw [← hv']
    exact hγ v hv
  · rw [segTo_eq_subpath_cast γ t, segTo_eq_subpath_cast γ s,
      Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_cast]
    rw [quot_cast_trans, Path.Homotopic.mk_subpath_trans_mk_subpath γ 0 s t]

end Work.EQ.UnivCover
