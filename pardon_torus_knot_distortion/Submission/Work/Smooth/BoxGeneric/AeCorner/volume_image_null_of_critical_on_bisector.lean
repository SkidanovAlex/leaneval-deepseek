import Mathlib
import Submission.Work.Smooth.BoxGeneric.Sard.exists_isOpen_volume_image_restrictedCritical_null

namespace Work.Smooth.BoxGeneric.AeCorner

open MeasureTheory Set

/-- If two `C¹` functions `G`, `H` agree on a set `B`, the gradient of `G - H` is nonzero on
`B`, and the gradient of `G` is everywhere on `B` parallel to that of `G - H`, then `G '' B`
is Lebesgue null.

The point is that locally `B` lies on the level curve `{G - H = 0}`, and the condition
`fderiv G = A • fderiv (G - H)` says precisely that `G` is critical when restricted to that
level curve.  The local Sard theorem for the restricted critical set on a level curve
(`Work.Smooth.BoxGeneric.Sard.exists_isOpen_volume_image_restrictedCritical_null`) gives a
null image on a neighbourhood of every point of `B`; a Lindelöf (countable subcover)
argument then globalises. -/
theorem volume_image_null_of_critical_on_bisector {G H : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    (hH : ContDiff ℝ 1 H) (B : Set (ℝ × ℝ)) (hBound : ∀ q ∈ B, G q = H q)
    (hreg : ∀ q ∈ B, fderiv ℝ (fun p => G p - H p) q ≠ 0)
    (hcrit : ∀ q ∈ B, ∃ A : ℝ, fderiv ℝ G q = A • fderiv ℝ (fun p => G p - H p) q) :
    MeasureTheory.volume (G '' B) = 0 := by
  classical
  have hf : ContDiff ℝ 1 (fun p : ℝ × ℝ => G p - H p) := hG.sub hH
  -- Locally, `B` is contained in the restricted critical set of `G` on the level curve
  -- `{G - H = 0}`, whose image is null by Sard.
  have key : ∀ q ∈ B, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ q ∈ U ∧
      MeasureTheory.volume (G '' (B ∩ U)) = 0 := by
    intro q hq
    have hfq : (fun p : ℝ × ℝ => G p - H p) q = 0 := by
      simp [hBound q hq]
    obtain ⟨U, hUo, hqU, hvol⟩ :=
      Work.Smooth.BoxGeneric.Sard.exists_isOpen_volume_image_restrictedCritical_null
        (G := G) (h := fun p : ℝ × ℝ => G p - H p) (p := q) hG hf hfq (hreg q hq)
    refine ⟨U, hUo, hqU, ?_⟩
    refine MeasureTheory.measure_mono_null ?_ hvol
    exact image_mono (fun x hx => ⟨⟨sub_eq_zero.mpr (hBound x hx.1), hcrit x hx.1⟩, hx.2⟩)
  -- Extract a countable subcover.
  have hLind : IsLindelof B := HereditarilyLindelofSpace.isLindelof B
  let V : B → Set (ℝ × ℝ) := fun q => Classical.choose (key q.1 q.2)
  have hVo : ∀ q : B, IsOpen (V q) := fun q => (Classical.choose_spec (key q.1 q.2)).1
  have hqV : ∀ q : B, (q : ℝ × ℝ) ∈ V q := fun q => (Classical.choose_spec (key q.1 q.2)).2.1
  have hVvol : ∀ q : B, MeasureTheory.volume (G '' (B ∩ V q)) = 0 :=
    fun q => (Classical.choose_spec (key q.1 q.2)).2.2
  have hsub : B ⊆ ⋃ q : B, V q := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hqV ⟨x, hx⟩⟩
  obtain ⟨r, hrc, hrcov⟩ := hLind.elim_countable_subcover V hVo hsub
  have hcov2 : G '' B ⊆ ⋃ q ∈ r, G '' (B ∩ V q) := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨q, hqr, hxq⟩ := Set.mem_iUnion₂.mp (hrcov hx)
    exact Set.mem_iUnion₂.mpr ⟨q, hqr, Set.mem_image_of_mem G ⟨hx, hxq⟩⟩
  have hfinal : MeasureTheory.volume (G '' B) ≤ 0 := by
    calc MeasureTheory.volume (G '' B)
        ≤ MeasureTheory.volume (⋃ q ∈ r, G '' (B ∩ V q)) := MeasureTheory.measure_mono hcov2
      _ = 0 := by
          rw [MeasureTheory.measure_biUnion_null_iff hrc]
          exact fun q _ => hVvol q
  exact le_antisymm hfinal zero_le

end Work.Smooth.BoxGeneric.AeCorner
