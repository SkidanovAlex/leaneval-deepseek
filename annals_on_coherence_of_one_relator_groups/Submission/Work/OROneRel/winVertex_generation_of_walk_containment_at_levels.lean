import Mathlib
import Submission.Work.OROneRel.winSplitNoPin
import Submission.Work.OROneRel.winVertex_levelFactor_mem
import Submission.Work.OROneRel.winBasisDefs

/-!
# The generation plank of the window splitting from *walk containment at the used levels*

This file proves `Work.OROneRel.winVertex_generation_of_walk_containment_at_levels`: if, for every
generator `x : α`, there is a single window level `i` of `x` (i.e. `(x,i) ∈ winE c lo hi`) such that
the decorated walks of `τ ^ i` and `τ ^ (i + c x)` stay inside the window, then the vertex
`winVertex Wt c lo hi u l` together with the class of the deck element `τ` generates
`G = ⟨α | u ^ l⟩`.

This is the *level-local* form of `Work.OROneRel.winVertex_generation_of_pin` /
`Work.OROneRel.winVertex_levelFactor_mem`: the membership of the level factor at a level `i` in the
vertex only needs the containment of the walk of `τ ^ i` *at that level*, not at all levels of the
window.  The argument is therefore the one of `Work.OROneRel.winVertex_generation_of_levelFactors`
(the cancellation of the gauges `Wt i · τ ^ (-i)` and `Wt (i + c x) · τ ^ (-(i + c x))` against the
loop class `Wt i · x · (Wt (i + c x))⁻¹` of the edge `(x,i)`), with the two level-factor memberships
supplied by the auxiliary lemma `winVertex_levelFactor_mem_of_walk` below.
-/

universe u

namespace Work.OROneRel

/-- **The level factor at a level whose `τ`-walk is contained in the window.**  If every edge of the
decorated walk of `τ ^ i` lies in the window `winE c lo hi`, then the level factor
`mk (Wt i) * (mk τ) ^ (-i)` lies in the vertex `winVertex Wt c lo hi u l`.

This is `Work.OROneRel.winVertex_levelFactor_mem` with the interval hypothesis `htr` specialised to
the single level `i` (and the superfluous hypotheses dropped): the telescoping computation of
`Work.OROneRel.gauge_decor` shows that the walk of `τ ^ i` has gauge `τ ^ i * (Wt i)⁻¹`, and the live
word of that walk (whose letters are the traversals of non-trivial loop class, i.e. exactly the
letters of the vertex alphabet) has the same `winRho`-image `τ ^ i * (Wt i)⁻¹`.  Inverting it gives
a word whose `winRho`-image is `Wt i * τ ^ (-i)`, whose `PresentedGroup.mk`-image is the level
factor, and which lies in the vertex by definition. -/
private theorem winVertex_levelFactor_mem_of_walk {α : Type u} {u : FreeGroup α} {l : ℕ}
    {c : α → ℤ} {Wt : ℤ → FreeGroup α} {lo hi : ℤ} {τ : FreeGroup α}
    (hW0 : Wt 0 = 1) (hτ : Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1)
    (i : ℤ)
    (htr : ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (τ ^ i)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c lo hi) :
    PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt i) *
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i) ∈
      Work.OROneRel.winVertex Wt c lo hi u l := by
  classical
  -- the decorated walk of `τ ^ i`, all of whose edges lie in the window
  let J : List ((α × ℤ) × Bool) := Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (τ ^ i))
  have hJedges : ∀ p ∈ J, Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi := htr
  -- the walk of `τ ^ i` ends at the level `i`
  have hlsig : Work.OROneRel.lsig c (Work.OROneRel.wordOf (τ ^ i)) = i := by
    have h1 : Work.OROneRel.cohom c (τ ^ i) =
        Multiplicative.ofAdd (Work.OROneRel.lsig c (Work.OROneRel.wordOf (τ ^ i))) := by
      have h := Work.OROneRel.cohom_mk c (Work.OROneRel.wordOf (τ ^ i))
      rw [Work.OROneRel.mk_wordOf] at h
      exact h
    have h2 : Work.OROneRel.cohom c (τ ^ i) = Multiplicative.ofAdd i := by
      rw [map_zpow, hτ]
      rw [← Int.ofAdd_mul]; simp
    exact Multiplicative.ofAdd.injective (h1.symm.trans h2)
  -- telescoping: the product of the loop classes of the walk of `τ ^ i` is `τ ^ i * (Wt i)⁻¹`
  have hgauge : Work.OROneRel.gaugeMap Wt c (FreeGroup.mk J) = τ ^ i * (Wt i)⁻¹ := by
    show Work.OROneRel.gaugeMap Wt c
        (FreeGroup.mk (Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (τ ^ i)))) =
      τ ^ i * (Wt i)⁻¹
    rw [Work.OROneRel.gauge_decor, Work.OROneRel.mk_wordOf, hlsig, hW0, zero_add]
    simp
  -- the live word of the walk has the same `winRho`-image
  have hrho : Work.OROneRel.winRho Wt c lo hi
      (FreeGroup.mk (Work.OROneRel.liveDecor Wt c lo hi J)) = τ ^ i * (Wt i)⁻¹ := by
    rw [Work.OROneRel.liveDecorWinRho Wt c J hJedges, hgauge]
  -- applying `mk` to the class of the inverse live word gives an element of the vertex
  have hmem : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
      (Work.OROneRel.winRho Wt c lo hi
        ((FreeGroup.mk (Work.OROneRel.liveDecor Wt c lo hi J))⁻¹)) ∈
        Work.OROneRel.winVertex Wt c lo hi u l := by
    rw [Work.OROneRel.winVertex]
    exact Subgroup.mem_map.mpr ⟨_, ⟨_, rfl⟩, rfl⟩
  -- and it is the level factor
  have heq : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
      (Work.OROneRel.winRho Wt c lo hi
        ((FreeGroup.mk (Work.OROneRel.liveDecor Wt c lo hi J))⁻¹))
      = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt i) *
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i) := by
    rw [map_inv, hrho, map_inv, map_mul, map_inv, map_zpow, mul_inv_rev, inv_inv, ← zpow_neg]
  rw [← heq]
  exact hmem

theorem winVertex_generation_of_walk_containment_at_levels {α : Type u} {u : FreeGroup α} {l : ℕ}
    {c : α → ℤ} {Wt : ℤ → FreeGroup α} {lo hi : ℤ} {τ : FreeGroup α}
    (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hτ : Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1)
    (hwalk : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi ∧
      (∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (τ ^ i)),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c lo hi) ∧
      (∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (τ ^ (i + c x))),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c lo hi)) :
    Work.OROneRel.winVertex Wt c lo hi u l ⊔
      Subgroup.closure {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ} = ⊤ := by
  -- It suffices to produce, for each generator `x`, the level-factor memberships at one window level
  -- `i` of `x` and at `i + c x`; these come from the walk containment of `τ ^ i`, `τ ^ (i + c x)`.
  refine Work.OROneRel.winVertex_generation_of_levelFactors hW0 hcu hwin τ ?_
  intro x
  obtain ⟨i, hei, hwi, hwx⟩ := hwalk x
  exact ⟨i, hei,
    winVertex_levelFactor_mem_of_walk hW0 hτ i hwi,
    winVertex_levelFactor_mem_of_walk hW0 hτ (i + c x) hwx⟩

end Work.OROneRel
