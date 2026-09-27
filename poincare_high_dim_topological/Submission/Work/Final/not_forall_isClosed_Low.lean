import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.PL.Defs

namespace Work.Final

open Set Metric
open scoped Classical

/-- The vertex `1/(k+1) · e₀` of `EuclideanSpace ℝ (Fin 1)`, the `k`-th vertex of the witness
complex below. -/
private noncomputable def witPt (k : ℕ) : PL.E 1 := EuclideanSpace.single 0 (((k : ℝ) + 1)⁻¹)

private theorem witPt_injective : Function.Injective witPt := by
  intro k l h
  have h2 : ((k : ℝ) + 1)⁻¹ = ((l : ℝ) + 1)⁻¹ := by
    have hh := congrArg (fun x : PL.E 1 => x 0) h
    simpa [witPt] using hh
  rw [inv_inj] at h2
  have : (k : ℝ) = (l : ℝ) := by linarith
  exact_mod_cast this

private theorem witPt_ne_zero (k : ℕ) : witPt k ≠ 0 := by
  have h : ((k : ℝ) + 1)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  intro hk
  exact h (by simpa [witPt] using congrArg (fun x : PL.E 1 => x 0) hk)

/-- The faces of the witness complex: all the singletons `{1/(k+1) · e₀}`, `k : ℕ`. -/
private def witFaces : Set (Finset (PL.E 1)) := Set.range (fun k => {witPt k})

private theorem witFaces_isRelLowerSet :
    IsRelLowerSet witFaces Finset.Nonempty := by
  intro s hs
  simp only [witFaces, Set.mem_range] at hs
  obtain ⟨k, rfl⟩ := hs
  refine ⟨by simp, ?_⟩
  intro b hbs hb
  simp only [witFaces, Set.mem_range]
  exact ⟨k, ((Finset.eq_singleton_iff_nonempty_unique_mem).mpr
    ⟨hb, fun x hx => by simpa using hbs hx⟩).symm⟩

private theorem witFaces_indep :
    ∀ s ∈ witFaces, AffineIndependent ℝ ((↑) : s → PL.E 1) := by
  intro s hs
  simp only [witFaces, Set.mem_range] at hs
  obtain ⟨k, rfl⟩ := hs
  exact affineIndependent_of_subsingleton ℝ _

private theorem witFaces_inter :
    ∀ {s t}, s ∈ witFaces → t ∈ witFaces →
      convexHull ℝ ↑s ∩ convexHull ℝ ↑t ⊆ convexHull ℝ (s ∩ t : Set (PL.E 1)) := by
  intro s t hs ht
  simp only [witFaces, Set.mem_range] at hs ht
  obtain ⟨k, rfl⟩ := hs
  obtain ⟨l, rfl⟩ := ht
  by_cases hkl : k = l
  · subst hkl
    simp [Set.inter_self]
  · rw [Finset.coe_singleton, Finset.coe_singleton, convexHull_singleton, convexHull_singleton]
    exact subset_convexHull ℝ _

/-- The witness complex: the geometric simplicial complex whose faces are all the singletons
`{1/(k+1) · e₀}`, `k : ℕ`, in `PL.E 1`. -/
private noncomputable def witCx : PL.Cx 1 where
  faces := witFaces
  isRelLowerSet_faces := witFaces_isRelLowerSet
  indep := fun {s} hs => witFaces_indep s hs
  inter_subset_convexHull := witFaces_inter

/-- The `0`-skeleton of the witness complex is exactly the range of `k ↦ 1/(k+1) · e₀`. -/
private theorem wit_low : Work.Geo.DualStretch.Low witCx 0 = Set.range witPt := by
  ext x
  simp only [Work.Geo.DualStretch.Low, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨s, hs, _hcard, hx⟩
    rw [show s ∈ witCx.faces ↔ ∃ k, ({witPt k} : Finset (PL.E 1)) = s from Iff.rfl] at hs
    obtain ⟨k, rfl⟩ := hs
    rw [PL.simp, Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at hx
    exact ⟨k, hx.symm⟩
  · rintro ⟨k, hk⟩
    rw [← hk]
    refine ⟨{witPt k}, ?_, by simp, ?_⟩
    · rw [show ({witPt k} : Finset (PL.E 1)) ∈ witCx.faces ↔
          ∃ j, ({witPt j} : Finset (PL.E 1)) = ({witPt k} : Finset (PL.E 1)) from Iff.rfl]
      exact ⟨k, rfl⟩
    · simp [PL.simp]

/-- **The `low_closed` field of `Work.Cells.Connell.SkeletonData` is false as stated**: the
`p`-skeleton of a general (infinite) geometric simplicial complex need not be closed.  (This is why
the final assembly uses `Work.Final.skelLow`, see `Submission/Work/Final/Defs.lean`.)

Witness: in `PL.E 1 = EuclideanSpace ℝ (Fin 1)`, let
`faces : Set (Finset (PL.E 1)) := Set.range (fun k : ℕ => {EuclideanSpace.single 0 ((k : ℝ) + 1)⁻¹})`
(all faces are the singletons `{1/(k+1)}`), and build `P : PL.Cx 1` directly as
`⟨faces, isRelLowerSet_faces, indep, inter_subset_convexHull⟩`: `isRelLowerSet_faces` holds because a
nonempty subset of a singleton is that singleton (`IsRelLowerSet faces Finset.Nonempty`), each face is
affinely independent (a singleton is), and the intersection condition holds because distinct
singletons have `convexHull ℝ {a} ∩ convexHull ℝ {b} = ∅ = convexHull ℝ (∅ : Set _)`.  Then
`Work.Geo.DualStretch.Low P 0 = Set.range (fun k => EuclideanSpace.single 0 ((k:ℝ)+1)⁻¹)`, which is
not closed: `0` is a limit point of the range (`(k+1)⁻¹ → 0` along `atTop` and
`EuclideanSpace.single 0` is continuous, with `EuclideanSpace.single 0 x = 0 ↔ x = 0`), while
`0 ∉ Low P 0` since every face spans a single nonzero point. -/
theorem not_forall_isClosed_Low :
    ¬ (∀ (P : PL.Cx 1) (p : ℕ), IsClosed (Work.Geo.DualStretch.Low P p)) := by
  intro H
  have hc : IsClosed (Set.range witPt) := by
    rw [← wit_low]
    exact H witCx 0
  have hcl : (0 : PL.E 1) ∈ closure (Set.range witPt) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹
    refine ⟨witPt k, ⟨k, rfl⟩, ?_⟩
    have hpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    rw [dist_zero_left, witPt, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos hpos]
    have hk1 : ε⁻¹ < (k : ℝ) + 1 := by linarith
    exact (inv_lt_comm₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1) hε).mpr hk1
  have h0 : (0 : PL.E 1) ∈ Set.range witPt := by
    rw [← hc.closure_eq]
    exact hcl
  obtain ⟨k, hk⟩ := h0
  exact witPt_ne_zero k hk

end Work.Final
