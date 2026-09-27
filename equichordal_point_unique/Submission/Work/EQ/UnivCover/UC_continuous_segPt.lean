import Mathlib
import Submission.Work.EQ.UnivCover.Defs
import Submission.Work.EQ.UnivCover.Sheet
import Submission.Work.EQ.UnivCover.Topology
import Submission.Work.EQ.UnivCover.UC_segPt_mem_sheet

/-!
# The initial-segment map of a path is continuous

For a path `γ : Path x₀ x`, the map `t ↦ UC.segPt γ t` from `unitInterval` to the universal cover
`UC x₀` (topologised by its sheets) is continuous.  This is the standard statement that a path
lifts to the universal cover.

The proof uses that the sheets over disc-like sets form a topological basis of `UC x₀`.  Given a
sheet `UC.sheet e V` containing `UC.segPt γ t₀` and a disc-like `W` with `γ t₀ ∈ W ⊆ V`, continuity
of `γ` at `t₀` supplies a neighbourhood of `t₀` which `γ` maps into `W`; the initial segments
starting at `t₀` of times in that neighbourhood stay inside the sheet `UC.sheet (UC.segPt γ t₀) W`
(`UC_segPt_mem_sheet`), and that sheet is absorbed into `UC.sheet e V` (`UC_sheet_trans`).
-/

set_option autoImplicit false
open _root_.Topology
open scoped Topology
open Work.EQ.UnivCover

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

/-- **Betweenness in `unitInterval` bounds distances**: a point of the unordered interval with
endpoints `b` and `c` is no further from `b` than `c` is. -/
theorem dist_le_dist_of_mem_uIcc {a b c : unitInterval} (h : a ∈ Set.uIcc b c) :
    dist a b ≤ dist c b := by
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
  rcases Set.mem_uIcc.mp h with ⟨hba, hac⟩ | ⟨hca, hab⟩
  · have hba' : (b : ℝ) ≤ (a : ℝ) := hba
    have hac' : (a : ℝ) ≤ (c : ℝ) := hac
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have hca' : (c : ℝ) ≤ (a : ℝ) := hca
    have hab' : (a : ℝ) ≤ (b : ℝ) := hab
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- **Nearby initial segments stay in the same sheet.**  If the piece of `γ` between `t₀` and `t`
lies in `W ⊆ V`, then `UC.segPt γ t` lies in every sheet over `V` through `UC.segPt γ t₀`. -/
theorem UC_segPt_mem_sheet_near {x : X} (γ : Path x₀ x) {V W : Set X} {e : UC x₀}
    {t₀ t : unitInterval} (he : UC.segPt γ t₀ ∈ UC.sheet e V) (hWV : W ⊆ V)
    (ht : ∀ u : unitInterval, u ∈ Set.uIcc t₀ t → γ u ∈ W) :
    UC.segPt γ t ∈ UC.sheet e V :=
  UC_sheet_trans he (UC_segPt_mem_sheet γ t₀ t ht) hWV

/-- **The initial-segment map of a path is continuous.** -/
theorem UC_continuous_segPt {X : Type*} [TopologicalSpace X] {x₀ x : X} (γ : Path x₀ x)
    (hB : HasDiscBasis X) : Continuous (UC.segPt γ) := by
  rw [(UC_isTopologicalBasis_basis hB).continuous_iff]
  rintro S ⟨e, V, hV, heV, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro t₀ ht₀
  -- a disc-like neighbourhood `W` of `γ t₀` inside `V`
  obtain ⟨W, hW, hγt₀W, hWV⟩ := hB (γ t₀) V hV.isOpen ht₀.1
  -- continuity of `γ` turns it into a neighbourhood of `t₀` in `unitInterval`
  have hnhds : γ ⁻¹' W ∈ 𝓝 t₀ := (hW.isOpen.preimage γ.continuous).mem_nhds hγt₀W
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine Filter.mem_of_superset (Metric.ball_mem_nhds t₀ (half_pos hε)) ?_
  intro t ht
  have htε : dist t t₀ < ε / 2 := ht
  refine UC_segPt_mem_sheet_near γ ht₀ hWV fun u hu => hball ?_
  have := dist_le_dist_of_mem_uIcc hu
  show dist u t₀ < ε
  linarith

end Work.EQ.UnivCover
