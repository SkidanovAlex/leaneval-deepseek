import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.generation_of_level_factors
import Submission.Work.OROneRel.winRho_winRoot

/-!
# Generation of `⟨α | u ^ l⟩` by the window vertex from *pinned* level factors

This file proves `Work.OROneRel.winVertex_generation_of_pin`: if the vertex
`winVertex Wt c lo hi u l` of the window decomposition already contains, for every level `i`, the
*level factor* `mk (Wt i) · (mk τ) ^ (-i)` (the hypothesis `hpin`), and the window meets every edge
orbit (`hcov`), then the vertex together with the class of the deck element `τ` generates the whole
one-relator group `⟨α | u ^ l⟩`.

This is the "pinned" repair of `Work.OROneRel.winVertex_generation` (whose unconditioned form is
refuted in `Work.OROneRel.winVertex_generation_false`): the counterexample there fails exactly
because the level factor `mk (Wt 1) · (mk τ)⁻¹` is *not* in the vertex.  With the level factors
available inside the vertex, the argument is the one of
`Work.OROneRel.generation_of_level_factors`: for a generator `x`, pick a level `i` with
`(x,i) ∈ winE c lo hi`; the loop class `Wt i · x · (Wt (i + c x))⁻¹` is in the vertex by
`Work.OROneRel.winVertex_coverClassAt_mem`, and the level factors at `i` and `i + c x` cancel the
gauges inside the vertex, leaving

  `mk (of x) = (mk τ) ^ (-i) · (A⁻¹ · C · B) · (mk τ) ^ (i + c x)`

with `A`, `C`, `B` the two level factors and the loop class.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The loop class of the edge `(x,i)` is the word `Wt i · x · (Wt (i + c x))⁻¹`. -/
private theorem coverClassAt_eq_pin (c : α → ℤ) (Wt : ℤ → FreeGroup α) (x : α) (i : ℤ) :
    coverClassAt Wt c (x, i) = Wt i * FreeGroup.of x * (Wt (i + c x))⁻¹ := by
  rw [coverClassAt, gaugeMap_of]

/-- **The loop class of a window edge lies in the vertex.** -/
private theorem winVertex_coverClassAt_mem_pin (u : FreeGroup α) (l : ℕ) (c : α → ℤ)
    (Wt : ℤ → FreeGroup α) (lo hi : ℤ) {e : α × ℤ} (he : e ∈ winE c lo hi) :
    PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (coverClassAt Wt c e) ∈
      winVertex Wt c lo hi u l := by
  rw [winVertex]
  by_cases hcl : coverClassAt Wt c e = 1
  · rw [hcl, map_one]
    exact Subgroup.one_mem _
  · let e' : winBeta Wt c lo hi := ⟨e, he, hcl⟩
    refine ⟨winRho Wt c lo hi (FreeGroup.of e'), ⟨_, rfl⟩, ?_⟩
    show PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
        (winRho Wt c lo hi (FreeGroup.of e')) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (coverClassAt Wt c e)
    rw [winRho_of]

theorem winVertex_generation_of_pin {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (c : α → ℤ) (τ : FreeGroup α) (Wt : ℤ → FreeGroup α) (lo hi : ℤ)
    (hcu : Work.OROneRel.cohom c u = 1)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (hpin : ∀ i : ℤ,
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt i) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i) ∈
        Work.OROneRel.winVertex Wt c lo hi u l) :
    Work.OROneRel.winVertex Wt c lo hi u l ⊔
      Subgroup.closure {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ} = ⊤ := by
  set S : Subgroup (PresentedGroup ({u ^ l} : Set (FreeGroup α))) :=
    winVertex Wt c lo hi u l ⊔
      Subgroup.closure {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ} with hS
  have hτS : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ ∈ S :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))
  have key : ∀ x : α, PresentedGroup.of x ∈ S := by
    intro x
    obtain ⟨i, hmem⟩ := hcov x
    have hA : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt i) *
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i) ∈ S :=
      Subgroup.mem_sup_left (hpin i)
    have hB : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt (i + c x)) *
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-(i + c x)) ∈ S :=
      Subgroup.mem_sup_left (hpin (i + c x))
    have hC : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
        (Wt i * FreeGroup.of x * (Wt (i + c x))⁻¹) ∈ S :=
      Subgroup.mem_sup_left (by
        rw [← coverClassAt_eq_pin]
        exact winVertex_coverClassAt_mem_pin u l c Wt lo hi hmem)
    have hmid : (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt i) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i))⁻¹ *
        PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
          (Wt i * FreeGroup.of x * (Wt (i + c x))⁻¹) *
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt (i + c x)) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-(i + c x))) ∈ S :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hA) hC) hB
    have heq : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (FreeGroup.of x) =
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i) *
          ((PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt i) *
            (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i))⁻¹ *
            PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
              (Wt i * FreeGroup.of x * (Wt (i + c x))⁻¹) *
            (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt (i + c x)) *
              (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-(i + c x))))
          * (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (i + c x) := by
      simp only [map_mul, map_inv]
      group
    change PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (FreeGroup.of x) ∈ S
    rw [heq]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (zpow_mem hτS (-i)) hmid) (zpow_mem hτS (i + c x))
  rw [eq_top_iff]
  intro g _
  exact PresentedGroup.generated_by _ S key g

end Work.OROneRel
