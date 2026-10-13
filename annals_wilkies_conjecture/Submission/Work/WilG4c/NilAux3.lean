/-
  WilG4c / `NilAux3` — the assembly layer for `AlDgListSliceNil`.

  * `PtContLocus p n f` is the *pointwise* fibre-continuity locus: the set of `(l,u)` at which
    the slice `y ↦ f l y` is continuous at `u`.
  * `ContLocus p n f` is the fibre `C⁰`-locus (which by `contDiffAt_zero_local` and
    `Infl.tgt` is the inflation of `PtContLocus`, `contDiffAt_zero_eq_infl`).
  * `AlDgListSlice_nil_eq` identifies `AlDgListSlice p n f []` with the graph of `f` over the
    fibre `C⁰`-locus.
  * `ZpSet_eq` rewrites `ZpSet p n f` (the graph over `PtContLocus`) in terms of `PtContLocus`
    using `continuousAt_iff_sumSq`, and `projLast_ZpSet` identifies its projection with
    `PtContLocus`.
-/
import Mathlib
import Submission.Work.WilG4c.SliceNilDefs
import Submission.Work.WilG4c.NilAux1
import Submission.Work.WilG4c.NilAux2
import Submission.Work.WilG4c.continuousAt_iff_sumSq
import Submission.Work.WilG4c.contDiffAt_zero_local

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## The two loci -/

/-- The pointwise fibre-continuity locus: the set of `(l,u)` at which the slice is continuous
*at* the point. -/
def PtContLocus (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (Nc p n) → ℝ) :=
  {w | ContinuousAt (fun y : Fin (n + 1) → ℝ => f (parPt w) y) (cubePt w)}

/-- The fibre `C⁰`-locus. -/
def ContLocus (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (Nc p n) → ℝ) :=
  {w | ContDiffAt ℝ 0 (fun y : Fin (n + 1) → ℝ => f (parPt w) y) (cubePt w)}

/-! ## Reassembling `(l, u)` from `Fin.append l u` -/

theorem parPt_append {p n : ℕ} (l : Fin p → ℝ) (y : Fin (n + 1) → ℝ) :
    parPt (n := n) (Fin.append l y) = l := by
  funext i
  simp [parPt, Fin.append_left]

theorem cubePt_append {p n : ℕ} (l : Fin p → ℝ) (y : Fin (n + 1) → ℝ) :
    cubePt (p := p) (Fin.append l y) = y := by
  funext j
  simp [cubePt, Fin.append_right]

/-- Graph membership as an equation. -/
theorem mem_famGraph_iff {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (z : Fin (p + (n + 1) + 1) → ℝ) :
    z ∈ famGraph f ↔
      z (Fin.last (p + (n + 1))) = f (parPt (Fin.init z)) (cubePt (Fin.init z)) := by
  rw [famGraph_eq_graphOf_famFunHat, graphOf]
  rfl

/-- `AlDgListSlice p n f []` is the graph of `f` over the fibre `C⁰`-locus. -/
theorem AlDgListSlice_nil_eq (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    AlDgListSlice p n f [] =
      famGraph f ∩ {z : Fin (Nc p n + 1) → ℝ | Fin.init z ∈ ContLocus p n f} := by
  ext z
  rw [mem_AlDgListSlice]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.length_nil, ContLocus]
  constructor
  · rintro ⟨hc, hv⟩
    refine ⟨?_, hc⟩
    rw [iteratedFDeriv_zero_apply] at hv
    rw [mem_famGraph_iff]
    exact hv
  · rintro ⟨hg, hc⟩
    refine ⟨hc, ?_⟩
    rw [iteratedFDeriv_zero_apply]
    rw [mem_famGraph_iff] at hg
    exact hg

/-- `ZpSet p n f` is the graph over the pointwise fibre-continuity locus. -/
theorem ZpSet_eq (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    ZpSet p n f =
      famGraph f ∩ {z : Fin (Nc p n + 1) → ℝ | Fin.init z ∈ PtContLocus p n f} := by
  ext z
  rw [ZpSet]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, PtContLocus]
  constructor
  · rintro ⟨hg, hε⟩
    refine ⟨hg, ?_⟩
    rw [_root_.Work.WilG4c.continuousAt_iff_sumSq]
    intro ε hεpos
    obtain ⟨δ, hδ, h⟩ := hε ε hεpos
    refine ⟨δ, hδ, fun y' hy' => ?_⟩
    have h2 : z (Fin.last (Nc p n)) = f (parPt (Fin.init z)) (cubePt (Fin.init z)) := by
      rw [← mem_famGraph_iff]
      exact hg
    simpa [h2] using h y' hy'
  · rintro ⟨hg, hc⟩
    refine ⟨hg, ?_⟩
    rw [_root_.Work.WilG4c.continuousAt_iff_sumSq] at hc
    intro ε hεpos
    obtain ⟨δ, hδ, h⟩ := hc ε hεpos
    refine ⟨δ, hδ, fun y' hy' => ?_⟩
    have h2 : z (Fin.last (Nc p n)) = f (parPt (Fin.init z)) (cubePt (Fin.init z)) := by
      rw [← mem_famGraph_iff]
      exact hg
    rw [h2]
    exact h y' hy'

/-- Dropping the value coordinate of `ZpSet` gives the pointwise fibre-continuity locus. -/
theorem projLast_ZpSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    projLast (ZpSet p n f) = PtContLocus p n f := by
  ext w
  rw [projLast, Set.mem_ofPred_eq, ZpSet_eq]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, PtContLocus]
  constructor
  · rintro ⟨s, hg, hc⟩
    rw [init_snoc'] at hc
    exact hc
  · intro hc
    refine ⟨famFunHat f w, ?_, ?_⟩
    · show Fin.snoc w (famFunHat f w) ∈ famGraph f
      rw [famGraph_eq_graphOf_famFunHat, graphOf]
      show (Fin.snoc w (famFunHat f w) : Fin (Nc p n + 1) → ℝ) (Fin.last (Nc p n))
        = famFunHat f (Fin.init (Fin.snoc w (famFunHat f w) : Fin (Nc p n + 1) → ℝ))
      rw [snoc_last', init_snoc']
    · rw [init_snoc']
      exact hc

/-- `ContDiffAt ℝ 0` of a slice is continuity on a box around the point, i.e. the fibre
`C⁰`-locus is the inflation of the pointwise continuity locus. -/
theorem contDiffAt_zero_eq_infl (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    ContLocus p n f = Infl.tgt p n (PtContLocus p n f) := by
  ext w
  simp only [Set.mem_ofPred_eq, ContLocus, Infl.tgt, PtContLocus]
  rw [_root_.Work.WilG4c.contDiffAt_zero_local]
  constructor
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have h' := h y hy
    rw [parPt_append, cubePt_append]
    exact h'
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have h' := h y hy
    rw [parPt_append, cubePt_append] at h'
    exact h'

end Work.WilkG4c
