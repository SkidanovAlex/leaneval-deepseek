import Mathlib
import Submission.Work.Drive.regBaseAssembly
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.encodedTransverse

/-!
# The collar interiority at the base `s = 0` of the collapse family

`Work.Drive.hregBase_design_chains` carries the design datum `hint`: at every meet of the collapse pair
`(E, E')` against the two sweeps `(V, W)` with `ftS x ∈ {0, 1}`, the plane parameter and both sweep
parameters are **strictly interior** (`Work.Drive.CollarInterior x`).

This module produces `hint` at the base `s = 0`, from the triple-meet hypothesis `Meet3Hyp M D` of the
three chains `D 0`, `D 1`, `D 2` of which the collapse family and the two sweeps are the `s = 0`
degeneration (`E 0 u = E' 0 u = D 0 (mk3 u 1)`, `V = D 1`, `W = D 2` — the hypotheses `hE0`, `hE'0`,
`hV`, `hW` of `Work.Drive.ppRegAt_zero_of_meet3Hyp`).

At `ftS x = 0` a pair meet of the `9`-box is a **triple point** `v3 x = (mk3 (ftU x) 1, ftY x, ftZ x)`
of `(D 0, D 1, D 2)`, in which block `0` sits on the **top face** (its third coordinate is `1`) while
`Work.Drive.ppMeet` puts every coordinate of `x` in `[0,1]`.  The face clause of `Meet3Hyp` then forces
the face to be in block `0`, because a face in another block would make the third coordinate of
`mk3 (ftU x) 1` — which is `1` — strictly interior; and within block `0` the face coordinate is forced
to be `2` for the same reason.  Hence all the *other* coordinates are strictly interior, which is
exactly `CollarInterior x`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The collar interiority at the base of a collapse family** (the `s = 0` clause of the design's
`CollarInterior` datum, `NOTES_LEAD_hodd_blockT6.md` §4.1(2)). -/
theorem collarInterior_zero_of_meet3Hyp {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M}
    (hD : Meet3Hyp M D)
    (hE0 : ∀ u : EuclideanSpace ℝ (Fin 2), E 0 u = D 0 (mk3 u 1))
    (hE'0 : ∀ u : EuclideanSpace ℝ (Fin 2), E' 0 u = D 0 (mk3 u 1))
    (hV : ∀ y : EuclideanSpace ℝ (Fin 3), V y = D 1 y)
    (hW : ∀ z : EuclideanSpace ℝ (Fin 3), W z = D 2 z)
    {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ ppMeet E E' V W) (hs : ftS x = 0) :
    CollarInterior x := by
  have hbox9 : x ∈ Submission.Drive.unitBox 8 := hx.1
  have hboxU : ∀ i : Fin 2, ftU x i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    have h := hbox9 ⟨1 + i.val, by omega⟩
    simpa [ftU] using h
  have hboxY : ∀ i : Fin 3, ftY x i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    have h := hbox9 ⟨3 + i.val, by omega⟩
    simpa [ftY] using h
  have hboxZ : ∀ i : Fin 3, ftZ x i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    have h := hbox9 ⟨6 + i.val, by omega⟩
    simpa [ftZ] using h
  -- the two triples of values coincide
  have hp1 : E 0 (ftU x) = E (ftS x) (ftU x) := by rw [hs]
  have hp1' : E' 0 (ftU x) = E (ftS x) (ftU x) := by rw [hE'0, ← hE0, hp1]
  have h0 : D 0 (mk3 (ftU x) 1) = D 1 (ftY x) := by
    rw [← hE0 (ftU x), hp1, hx.2.1, hV]
  have h2 : D 0 (mk3 (ftU x) 1) = D 2 (ftZ x) := by
    rw [← hE'0 (ftU x), ← hs, hx.2.2, hW]
  -- the base triple point of `D`
  set v3 : Fin 3 → EuclideanSpace ℝ (Fin 3) := ![mk3 (ftU x) 1, ftY x, ftZ x] with hv3
  have hv3_0 : v3 0 = mk3 (ftU x) 1 := by rw [hv3]; simp
  have hv3_1 : v3 1 = ftY x := by rw [hv3]; simp
  have hv3_2 : v3 2 = ftZ x := by rw [hv3]; simp
  have hbox0 : mk3 (ftU x) 1 ∈ Submission.Drive.unitBox 2 := by
    intro i
    fin_cases i
    · simpa [mk3] using hboxU 0
    · simpa [mk3] using hboxU 1
    · simp [mk3]
  have hboxv3 : ∀ k : Fin 3, v3 k ∈ Submission.Drive.unitBox 2 := by
    intro k
    fin_cases k
    · simpa [hv3_0] using hbox0
    · simpa [hv3_1, Submission.Drive.unitBox] using (fun i => hboxY i)
    · simpa [hv3_2, Submission.Drive.unitBox] using (fun i => hboxZ i)
  have hteq1 : D 0 (v3 0) = D 1 (v3 1) := by rw [hv3_0, hv3_1]; exact h0
  have hteq2 : D 0 (v3 0) = D 2 (v3 2) := by rw [hv3_0, hv3_2]; exact h2
  have hbdry : ∃ k, v3 k ∈ Submission.Drive.unitBoxBdry 2 :=
    ⟨0, hboxv3 0, 2, Or.inr (by rw [hv3_0]; simp [mk3])⟩
  obtain ⟨k, i, hki, hrest, hothers, v, hvdir, hvne⟩ :=
    hD.face v3 hboxv3 hteq1 hteq2 hbdry
  -- the face must be in block `0`, at coordinate `2`
  have hk0 : k = 0 := by
    by_contra hk
    have h := hothers 0 (by simpa using (Ne.symm hk)) 2
    rw [hv3_0] at h
    simp [mk3] at h
  subst hk0
  have hi0 : i ≠ 0 := by
    intro h
    have hh := hrest 2 (by rw [h]; decide)
    rw [hv3_0] at hh
    simp [mk3] at hh
  have hi1 : i ≠ 1 := by
    intro h
    have hh := hrest 2 (by rw [h]; decide)
    rw [hv3_0] at hh
    simp [mk3] at hh
  have hi2 : i = 2 := by
    fin_cases i
    · exact absurd rfl hi0
    · exact absurd rfl hi1
    · rfl
  refine ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · have h := hrest 0 (by rw [hi2]; decide)
      rw [hv3_0] at h
      simpa [mk3] using h
    · have h := hrest 1 (by rw [hi2]; decide)
      rw [hv3_0] at h
      simpa [mk3] using h
  · intro j
    have h := hothers 1 (by decide) j
    rw [hv3_1] at h
    exact h
  · intro j
    have h := hothers 2 (by decide) j
    rw [hv3_2] at h
    exact h

end

end Work.Drive
