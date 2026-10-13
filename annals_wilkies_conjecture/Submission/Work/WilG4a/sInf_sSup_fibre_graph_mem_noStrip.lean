/-
  WilG4a : `Work.WilG4a.sInf_sSup_fibre_graph_mem_noStrip`.

  The pointwise infimum and supremum of the fibre `Z_l = {x | (l,x) ∈ Z}` of an `Ω`-definable
  set `Z ⊆ ℝ^{p+1}` are graphs of functions whose graphs are again `Ω`-definable, with a
  format independent of the degree `D` and a degree bound affine in `D`.

  *No strip hypothesis is used here*: `Z` is an arbitrary `Ω`-set, so the fibres may be empty
  or unbounded.  On `ℝ` the conventions are `sInf ∅ = 0`, `sSup ∅ = 0`, and `sInf s = 0`
  (resp. `sSup s = 0`) whenever `s` is not bounded below (resp. above); the corresponding
  descriptions of the two graphs are

    `A_lo_ns p Z = (LB1 ∩ GLB1) ∪ ((NE1ᶜ ∪ unbBelow1) ∩ yZero1)`,
    `A_hi_ns p Z = (UB1 ∩ LUB1) ∪ ((NE1ᶜ ∪ unbAbove1) ∩ yZero1)`

  (`Submission.Work.WilG4a.NoStripDefs`), and the semantic identification
  `graphOf (l ↦ sInf Z_l) = A_lo_ns p Z` (resp. `sSup`) is proved in the sibling modules
  `Work.WilG4a.graphOf_sInf_fibre_eq_A_lo_ns` / `Work.WilG4a.graphOf_sSup_fibre_eq_A_hi_ns`.

  The bookkeeping is then the `Ω`-calculus alone: `NE1`, `LB1`, `GLB1`, `UB1`, `LUB1`
  and `yZero1` are `Ω`-sets with format/degree bounds affine in `D` (`NE1_mem`, `LB1_mem`,
  `GLB1_mem`, `UB1_mem`, `LUB1_mem`, `yZero1_mem`), the sets `unbBelow1`/`unbAbove1` are one
  projection and one complement away from `LB1`/`UB1` (`unbBelow1_mem`, `unbAbove1_mem`), and
  a fixed number of complement/intersection/union steps turns these into `A_lo_ns` and
  `A_hi_ns`; both consume at most `6` copies of the degree bound `cmax * D + dmax`.
-/
import Mathlib
import Submission.Work.WilG4a.NoStripDefs
import Submission.Work.WilG4a.fiber_endpoints
import Submission.Work.WilG4a.NE1_mem
import Submission.Work.WilG4a.LB1_mem
import Submission.Work.WilG4a.UB1_mem
import Submission.Work.WilG4a.GLB1_mem
import Submission.Work.WilG4a.LUB1_mem
import Submission.Work.WilG4a.unbBelow1_mem
import Submission.Work.WilG4a.unbAbove1_mem
import Submission.Work.WilG4a.graphOf_sInf_fibre_eq_A_lo_ns
import Submission.Work.WilG4a.graphOf_sSup_fibre_eq_A_hi_ns
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.API

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesDesign WilkiesConjecture

theorem sInf_sSup_fibre_graph_mem_noStrip (S : WilkiesDesign.SOMin) (p F : ℕ) :
    ∃ (a c c' : ℕ),
      ∀ (D : ℕ) (Z : Set (Fin (p + 1) → ℝ)), Z ∈ S.Ω F D (p + 1) →
        WilkiesDesign.graphOf (fun l : Fin p → ℝ => sInf {x : ℝ | Fin.snoc l x ∈ Z}) ∈
            S.Ω a (c * D + c') (p + 1) ∧
        WilkiesDesign.graphOf (fun l : Fin p → ℝ => sSup {x : ℝ | Fin.snoc l x ∈ Z}) ∈
            S.Ω a (c * D + c') (p + 1) := by
  -- the uniform constants supplied by the sibling membership lemmas
  obtain ⟨A₁, c₁, d₁, hNE⟩ := NE1_mem S p F
  obtain ⟨A₂, c₂, d₂, hLB⟩ := LB1_mem S p F
  obtain ⟨A₃, c₃, d₃, hUB⟩ := UB1_mem S p F
  obtain ⟨A₄, c₄, d₄, hGLB⟩ := GLB1_mem S p F
  obtain ⟨A₅, c₅, d₅, hLUB⟩ := LUB1_mem S p F
  obtain ⟨A₆, c₆, d₆, hUnbLo⟩ := unbBelow1_mem S p F
  obtain ⟨A₇, c₇, d₇, hUnbHi⟩ := unbAbove1_mem S p F
  -- a common (crude) format and degree bound
  set A : ℕ := (A₁ + F) + (A₂ + F) + (A₃ + F) + (A₄ + F) + (A₅ + F) + (A₆ + F) + (A₇ + F)
    + p + 1 + 10 with hA
  set cmax : ℕ := c₁ + c₂ + c₃ + c₄ + c₅ + c₆ + c₇ + 1 with hcmax
  set dmax : ℕ := d₁ + d₂ + d₃ + d₄ + d₅ + d₆ + d₇ + 2 with hdmax
  refine ⟨A + 2, 6 * cmax, 6 * dmax, ?_⟩
  intro D Z hZ
  -- the seven base pieces, all at format `A` and degree `cmax * D + dmax`
  have hNE1 : NE1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hNE D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hLB1 : LB1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hLB D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hUB1 : UB1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hUB D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hGLB1 : GLB1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hGLB D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hLUB1 : LUB1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hLUB D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hUnbLo1 : unbBelow1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hUnbLo D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hUnbHi1 : unbAbove1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hUnbHi D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hyZero : yZero1 p ∈ S.Ω A (cmax * D + dmax) (p + 1) := by
    refine Work.WilG5.mem_mono (yZero1_mem S p) A (cmax * D + dmax) (by omega) ?_
    have h2 : dmax ≤ cmax * D + dmax := Nat.le_add_left dmax (cmax * D)
    omega
  -- the lower graph `A_lo_ns`
  have hX1 : LB1 p Z ∩ GLB1 p Z ∈ S.Ω (A + 1)
      ((cmax * D + dmax) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S) hLB1 hGLB1
  have hNE1c : (NE1 p Z)ᶜ ∈ S.Ω (A + 1) (cmax * D + dmax) (p + 1) := S.compl hNE1
  have hUnbLo' : unbBelow1 p Z ∈ S.Ω (A + 1) (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono hUnbLo1 (A + 1) (cmax * D + dmax) (by omega) le_rfl
  have hU : (NE1 p Z)ᶜ ∪ unbBelow1 p Z ∈ S.Ω (A + 1)
      ((cmax * D + dmax) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG0.Omega_union2 (S := S) hNE1c hUnbLo'
  have hyZero' : yZero1 p ∈ S.Ω (A + 1) (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono hyZero (A + 1) (cmax * D + dmax) (by omega) le_rfl
  have hX4 : ((NE1 p Z)ᶜ ∪ unbBelow1 p Z) ∩ yZero1 p ∈ S.Ω (A + 2)
      (((cmax * D + dmax) + (cmax * D + dmax)) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S) hU hyZero'
  have hX1' : LB1 p Z ∩ GLB1 p Z ∈ S.Ω (A + 2)
      (((cmax * D + dmax) + (cmax * D + dmax)) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG5.mem_mono hX1 (A + 2) _ (by omega) (by omega)
  have hA_lo : A_lo_ns p Z ∈ S.Ω (A + 2)
      ((((cmax * D + dmax) + (cmax * D + dmax)) + (cmax * D + dmax)) +
        (((cmax * D + dmax) + (cmax * D + dmax)) + (cmax * D + dmax))) (p + 1) := by
    unfold A_lo_ns
    exact Work.WilG0.Omega_union2 (S := S) hX1' hX4
  -- the upper graph `A_hi_ns`
  have hY1 : UB1 p Z ∩ LUB1 p Z ∈ S.Ω (A + 1)
      ((cmax * D + dmax) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S) hUB1 hLUB1
  have hUnbHi' : unbAbove1 p Z ∈ S.Ω (A + 1) (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono hUnbHi1 (A + 1) (cmax * D + dmax) (by omega) le_rfl
  have hV : (NE1 p Z)ᶜ ∪ unbAbove1 p Z ∈ S.Ω (A + 1)
      ((cmax * D + dmax) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG0.Omega_union2 (S := S) hNE1c hUnbHi'
  have hY4 : ((NE1 p Z)ᶜ ∪ unbAbove1 p Z) ∩ yZero1 p ∈ S.Ω (A + 2)
      (((cmax * D + dmax) + (cmax * D + dmax)) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S) hV hyZero'
  have hY1' : UB1 p Z ∩ LUB1 p Z ∈ S.Ω (A + 2)
      (((cmax * D + dmax) + (cmax * D + dmax)) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG5.mem_mono hY1 (A + 2) _ (by omega) (by omega)
  have hA_hi : A_hi_ns p Z ∈ S.Ω (A + 2)
      ((((cmax * D + dmax) + (cmax * D + dmax)) + (cmax * D + dmax)) +
        (((cmax * D + dmax) + (cmax * D + dmax)) + (cmax * D + dmax))) (p + 1) := by
    unfold A_hi_ns
    exact Work.WilG0.Omega_union2 (S := S) hY1' hY4
  -- the accumulated degree is `6 * (cmax * D + dmax) = 6 * cmax * D + 6 * dmax`
  have hdeg : ((((cmax * D + dmax) + (cmax * D + dmax)) + (cmax * D + dmax)) +
      (((cmax * D + dmax) + (cmax * D + dmax)) + (cmax * D + dmax))) ≤
        6 * cmax * D + 6 * dmax := by
    have e1 : ((((cmax * D + dmax) + (cmax * D + dmax)) + (cmax * D + dmax)) +
        (((cmax * D + dmax) + (cmax * D + dmax)) + (cmax * D + dmax))) =
          6 * (cmax * D + dmax) := by ring
    rw [e1]
    have e2 : 6 * (cmax * D + dmax) = 6 * cmax * D + 6 * dmax := by ring
    rw [e2]
  have hA_lo' : A_lo_ns p Z ∈ S.Ω (A + 2) (6 * cmax * D + 6 * dmax) (p + 1) :=
    Work.WilG5.mem_mono hA_lo (A + 2) (6 * cmax * D + 6 * dmax) le_rfl hdeg
  have hA_hi' : A_hi_ns p Z ∈ S.Ω (A + 2) (6 * cmax * D + 6 * dmax) (p + 1) :=
    Work.WilG5.mem_mono hA_hi (A + 2) (6 * cmax * D + 6 * dmax) le_rfl hdeg
  refine ⟨?_, ?_⟩
  · rw [graphOf_sInf_fibre_eq_A_lo_ns p Z]
    exact hA_lo'
  · rw [graphOf_sSup_fibre_eq_A_hi_ns p Z]
    exact hA_hi'

end Work.WilG4a
