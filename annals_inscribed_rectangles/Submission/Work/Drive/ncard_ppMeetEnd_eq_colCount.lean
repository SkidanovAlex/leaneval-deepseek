import Mathlib
import Submission.Work.Drive.ppParity.Bdry
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.even_ncard_pairMeetBdry

/-!
# The bridge `#ppMeetEnd = K s`: the pair-meet count is the collapsed triple count

The radial-collapse transport computes the parity of `K s = #(colMeet β Q V W s)`, the number of
parameter triples `(u, y, z)` of the `8`-box at which the collapsed plane meets the chain `V` at `y`
and the *uncollapsed* plane meets the chain `W` at `z` (`Work.Drive.colCount`).  The S4 box-parity
engine (`Work.Drive.exists_even_ppMeetEnd_add_intrinsic`) produces instead the parity of
`#(ppMeetEnd (colPlane β Q) (fun _ u => diskPlane Q u) V W s)`, the number of zeros of the pair map
on the `s`-face of the `9`-box.

The two are the same number, by the coordinate dictionary of the `9`-box: the map

> `x ↦ (ftU x, ftY x, ftZ x)`

is a bijection from the `s`-face onto the `8`-box of triples, because the `9`-box membership of `x`
together with `ftS x = s` for `s ∈ [0,1]` says exactly that `ftU x`, `ftY x`, `ftZ x` are in the three
boxes, and the pair equations of `ppMeet` are literally the two meet equations of `colMeet`.  The
inverse is `(u, y, z) ↦ mk9 s u y z` (`Work.Drive.PMB.mk9`), and the only hypothesis is
`s ∈ [0,1]` (without it the `s`-face is empty while `colMeet` need not be).

This is the `CappingSpace`-valued and general-`s` form of `Work.Drive.PMB.ncard_endFace` (which is
stated for `s = 0 ∨ s = 1` and for `ℝ⁴`-valued chains), and the chain-free statement is
`Work.Drive.ncard_ppMeetEnd_eq_ncard_ppTriple` below.
-/

namespace Work.Drive

open Manifold Set

noncomputable section

variable {M : Type*}

/-- **The parameter triples of a pair meet at the family parameter `s`**: `u` in the plane square,
`y`, `z` in the two sweep cubes, with the collapsed plane meeting `V` at `y` and the fixed plane
meeting `W` at `z`.  This is `Work.Drive.pairMeetSet` with the second family read at `s` and with the
value space left arbitrary (in particular `Work.Drive.CappingSpace`). -/
def ppTriple (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) (s : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  {p | p.1 ∈ Submission.Drive.unitBox 1 ∧ p.2.1 ∈ Submission.Drive.unitBox 2 ∧
       p.2.2 ∈ Submission.Drive.unitBox 2 ∧ E s p.1 = V p.2.1 ∧ E' s p.1 = W p.2.2}

/-- **The `s`-face of the pair-meet set has the cardinality of the triple set**: the coordinate
dictionary of the `9`-box gives a bijection
`x ↦ (ftU x, ftY x, ftZ x)` from `ppMeetEnd E E' V W s` onto `ppTriple E E' V W s`, with inverse
`(u, y, z) ↦ mk9 s u y z`. -/
lemma ncard_ppMeetEnd_eq_ncard_ppTriple
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (ppMeetEnd E E' V W s).ncard = (ppTriple E E' V W s).ncard := by
  refine Set.ncard_congr (fun x _ => (ftU x, ftY x, ftZ x)) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxmem, hsx⟩ := hx
    obtain ⟨hbox, h1, h2⟩ := hxmem
    rw [ppTriple, Set.mem_ofPred_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show ∀ i : Fin 2, ftU x i ∈ Set.Icc (0 : ℝ) 1
      intro i
      rw [PMB.ftU_apply]
      exact hbox _
    · show ∀ i : Fin 3, ftY x i ∈ Set.Icc (0 : ℝ) 1
      intro i
      rw [PMB.ftY_apply]
      exact hbox _
    · show ∀ i : Fin 3, ftZ x i ∈ Set.Icc (0 : ℝ) 1
      intro i
      rw [PMB.ftZ_apply]
      exact hbox _
    · show E s (ftU x) = V (ftY x)
      rw [← hsx]
      exact h1
    · show E' s (ftU x) = W (ftZ x)
      rw [← hsx]
      exact h2
  · intro x x' hx hx' h
    have hsx : ftS x = s := hx.2
    have hsx' : ftS x' = s := hx'.2
    have h1 : ftU x = ftU x' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.1) h
    have h2 : ftY x = ftY x' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.2.1) h
    have h3 : ftZ x = ftZ x' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.2.2) h
    rw [← PMB.mk9_ft x, ← PMB.mk9_ft x', h1, h2, h3, hsx, hsx']
  · intro p hp
    rw [ppTriple, Set.mem_ofPred_eq] at hp
    obtain ⟨hu, hy, hz, h1, h2⟩ := hp
    refine ⟨PMB.mk9 s p.1 p.2.1 p.2.2, ?_, ?_⟩
    · refine ⟨?_, PMB.ftS_mk9 s p.1 p.2.1 p.2.2⟩
      exact ⟨PMB.mk9_mem_unitBox hs hu hy hz, by simpa using h1, by simpa using h2⟩
    · rw [PMB.ftU_mk9, PMB.ftY_mk9, PMB.ftZ_mk9]

/-- **The collapsed meet set is the triple set of the collapse family.** -/
lemma colMeet_eq_ppTriple (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) (s : ℝ) :
    colMeet β Q V W s = ppTriple (colPlane β Q) (fun _ u => diskPlane Q u) V W s :=
  rfl

/-- **The bridge**: the number of pair meets at the family parameter `s` (the S4 box-parity count) is
the collapsed triple count `K s` of the radial-collapse transport. -/
theorem ncard_ppMeetEnd_eq_colCount
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (Work.Drive.ppMeetEnd (colPlane β Q) (fun _ u => diskPlane Q u) V W s).ncard
      = colCount β Q V W s := by
  rw [colCount, colMeet_eq_ppTriple]
  exact ncard_ppMeetEnd_eq_ncard_ppTriple (colPlane β Q) (fun _ u => diskPlane Q u) V W hs

end

end Work.Drive
