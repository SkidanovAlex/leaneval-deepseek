import Mathlib
import Submission.Work.EKLC6Core.cutHMargin
import Submission.Work.EKLC6Core.cutHDefs
import Submission.Work.EKLC6Core.cutDefs
import Submission.Work.EKLC6Core.cutSetup
import Submission.Work.EKLC6Core.mem_VThick_frontier_of_mem_of_not_mem
import Submission.Work.EKLComp.LeafDefs

namespace Work.EKLC6Core

open Work.EKLContract

set_option linter.unusedVariables false

/-!
# `Work.EKLC6Core.cut_margin_at_depth`

The **single-step (depth-`δ`) margin of the cut σ-algebra**.  This is the local form of
`Work.EKLC6Core.cutHMargin`: instead of assuming that the point `z` is at time `n` of a
`CutGood` orbit, one assumes directly that

* `z` is at distance `δ` from the shell `shellThin S δ` (`hdeep`),
* `z` is free for the `U`-action (`hzfree`),
* the radius `τ` satisfies `20 τ ≤ δ`, `τ ≤ 1` (through `δ ≤ 1`) and `τ ≤ 10 ρ`.

Then every `u ∈ Uball U τ` keeps `z` inside its `MCut S O`-atom, i.e.
`Uball U τ ⊆ shape (MCut S O) U z`.

The proof is the geometric half of Pisa 7.31: `z` is deep inside the cell/bad partition, so the
crossing lemma `mem_VThick_frontier_of_mem_of_not_mem` shows that a displacement by
`u ∈ V τ` cannot cross a frontier (that would put `z` in the `20 τ`-thickening of a frontier,
hence in the shell); the locally `U`-equivariant lift then transports the `sat`-pattern.
-/

theorem cut_margin_at_depth {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3} {ε : ℝ}
    (S : Work.EKLC6Core.CutData μ U ε) (O : ℕ → Set Work.EKLContract.SL3)
    (hOopen : ∀ m, IsOpen (O m))
    (hvis : ∀ z : Work.EKLContract.SL3, ∃ m, z ∈ Work.EKLC6Core.sat U (O m))
    (hsep : ∀ z w : Work.EKLContract.SL3,
      (∀ m, (z ∈ Work.EKLC6Core.sat U (O m) ↔ w ∈ Work.EKLC6Core.sat U (O m))) →
      w ∈ Work.EKLC6Core.sat U ({z}))
    (huni : ∀ u ∈ U, ((u : Matrix (Fin 3) (Fin 3) ℝ) - 1) ^ 3 = 0)
    {z : Work.EKLContract.X3} (hzfree : z ∈ Work.EKLC6Core.cutFree U)
    {δ τ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hdeep : z ∉ Work.EKLC6Core.shellThin S δ)
    (hτ0 : 0 < τ) (hτδ : 20 * τ ≤ δ) (hτρ : τ ≤ 10 * S.ρ) :
    Work.EKLComp.Uball U τ ⊆ Work.EKLContract.shape (Work.EKLC6Core.MCut S O) U z := by
  classical
  -- `τ ≤ 1`, so that the crossing lemma applies at scale `τ`
  have hτle1 : τ ≤ 1 := by nlinarith [hδ0, hτ0, hτδ, hδ1]
  -- `z` is outside the shell at the smaller scale `20 τ`
  have hshell : z ∉ shellThin S (20 * τ) := fun h => hdeep (shellThin_mono S hτδ h)
  intro u hu
  obtain ⟨huU, huV⟩ := hu
  refine ⟨huU, ?_⟩
  -- `u ∈ V (10 ρ)`, the smallness needed by the equivariance of the lift
  have huV10 : u ∈ V (10 * S.ρ) := fun i j => lt_of_lt_of_le (huV i j) hτρ
  -- **crossing lemma**: small `u`-translations do not cross the frontier of a cell
  have hcell : ∀ i : Fin S.N, z ∈ S.cell i → u • z ∈ S.cell i := by
    intro i hzi
    by_contra hnot
    exact hshell (Or.inl (Set.mem_iUnion.mpr ⟨i,
      mem_VThick_frontier_of_mem_of_not_mem huni (S.hopen i) hτ0 hτle1 u huU huV
        (Or.inl ⟨hzi, hnot⟩)⟩))
  -- **crossing lemma** for the open exceptional piece
  have hbad : z ∈ S.bad → u • z ∈ S.bad := by
    intro hzbad
    by_contra hnot
    exact hshell (Or.inr (mem_VThick_frontier_of_mem_of_not_mem huni S.hbad_open hτ0 hτle1
      u huU huV (Or.inl ⟨hzbad, hnot⟩)))
  -- **the atoms are `u`-invariant on the generating family**
  have hbad_iff : (u • z ∈ S.bad ↔ z ∈ S.bad) := by
    refine ⟨?_, fun h => hbad h⟩
    intro hub
    by_contra hznb
    exact hshell (Or.inr (mem_VThick_frontier_of_mem_of_not_mem huni S.hbad_open hτ0 hτle1
      u huU huV (Or.inr ⟨hznb, hub⟩)))
  have hcell_iff : ∀ (i : Fin S.N) (m : ℕ),
      (u • z ∈ genCell S O i m ↔ z ∈ genCell S O i m) := by
    intro i m
    by_cases hzi : z ∈ S.cell i
    · -- the same cell: the lift transports the pattern
      have h1 : u • z ∈ genCell S O i m ↔ S.lift i (u • z) ∈ sat U (O m) :=
        genCell_mem_iff S O i m (hcell i hzi)
      have h2 : S.lift i (u • z) = u * S.lift i z :=
        S.lift_eq i z hzi hzfree (u • z) (hcell i hzi) u huV10 huU rfl
      have h3 : u * S.lift i z ∈ sat U (O m) ↔ S.lift i z ∈ sat U (O m) :=
        mem_sat_mul_iff huU (O m) (S.lift i z)
      have h4 : z ∈ genCell S O i m ↔ S.lift i z ∈ sat U (O m) :=
        genCell_mem_iff S O i m hzi
      simp only [h1, h2, h3, h4]
    · -- a different cell: `u • z` cannot enter (or leave) `cell i`
      have hzng : z ∉ genCell S O i m := fun h => hzi h.2
      have huzng : u • z ∉ genCell S O i m := by
        intro h
        exact hshell (Or.inl (Set.mem_iUnion.mpr ⟨i,
          mem_VThick_frontier_of_mem_of_not_mem huni (S.hopen i) hτ0 hτle1 u huU huV
            (Or.inr ⟨hzi, h.2⟩)⟩))
      exact ⟨fun h => absurd h huzng, fun h => absurd h hzng⟩
  -- finally, `atom (MCut S O) z` is cut out by the patterns against the generators
  change u • z ∈ atom (MeasurableSpace.generateFrom (famAtom S O)) z
  rw [mem_atom_generateFrom_iff]
  intro A hA
  simp only [famAtom, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hA
  rcases hA with ⟨p, hp⟩ | hb
  · rw [← hp]
    exact hcell_iff p.1 p.2
  · rw [hb]
    exact hbad_iff

end Work.EKLC6Core
