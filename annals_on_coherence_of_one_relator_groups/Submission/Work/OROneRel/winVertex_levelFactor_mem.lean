import Mathlib
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.winVertex_generation_of_pin
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.liveDecorWinRho

namespace Work.OROneRel

universe u

/-!
# The level factors of a window decomposition lie in the vertex

This file proves `Work.OROneRel.winVertex_levelFactor_mem`: if the window `[lo,hi]` contains both
endpoints of every edge of the decorated walk of `τ ^ i` for every level `i ∈ [lo,hi]` (`htr`), then
the *level factor*

`mk (Wt i) · (mk τ) ^ (-i)`

lies in the vertex `winVertex Wt c lo hi u l = winRho.range.map mk` of the window decomposition,
for every level `i ∈ [lo,hi]`.

## The argument

Let `J = decor c 0 (wordOf (τ ^ i))` be the decorated walk of `τ ^ i`, starting at level `0`; by
`htr` all its edges lie in the window `winE c lo hi`.  Since `cohom c (τ ^ i) = (ofAdd 1) ^ i =
ofAdd i` (`hτ`) and `lsig c (wordOf (τ ^ i))` computes the same total weight (`cohom_mk`), the walk
of `τ ^ i` *ends* at the level `i`, and the telescoping identity `gauge_decor` (with `Wt 0 = 1`)
gives

`gaugeMap Wt c (mk J) = Wt 0 * τ ^ i * (Wt (0 + i))⁻¹ = τ ^ i * (Wt i)⁻¹`.

The live word of `J` -- the traversals whose edge lies in the window and has non-trivial loop class
-- maps under `winRho` to the same product (`liveDecorWinRho`, the letters deleted by `liveDecor`
being exactly those of trivial loop class, hence contributing `1`), so

`winRho (mk (liveDecor Wt c lo hi J)) = τ ^ i * (Wt i)⁻¹`.

Inverting this word gives an element of `F (winBeta Wt c lo hi)` whose `winRho`-image is
`Wt i * τ ^ (-i)`; applying `mk` (which lies in `winVertex` by definition of the vertex as the image
of `winRho.range` under `mk`) yields exactly the level factor.
-/

/-- `(Multiplicative.ofAdd 1) ^ n = Multiplicative.ofAdd n` in the infinite cyclic group
`Multiplicative ℤ`: the deck element `τ` of weight `1` has `τ ^ i` of weight `i`. -/
private theorem ofAdd_one_zpow_local (n : ℤ) :
    ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) ^ n) = Multiplicative.ofAdd n := by
  rw [← Int.ofAdd_mul]
  simp

theorem winVertex_levelFactor_mem {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (c : α → ℤ) (τ : FreeGroup α) (Wt : ℤ → FreeGroup α) (lo hi : ℤ)
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (hcu : Work.OROneRel.cohom c u = 1)
    (hτ : Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1)
    (htr : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (τ ^ i)),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c lo hi) :
    ∀ i : ℤ, lo ≤ i → i ≤ hi →
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt i) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i) ∈
        Work.OROneRel.winVertex Wt c lo hi u l := by
  classical
  intro i hlo hhi
  -- the decorated walk of `τ ^ i`, whose edges all lie in the window
  let J : List ((α × ℤ) × Bool) := decor c 0 (wordOf (τ ^ i))
  have hJedges : ∀ p ∈ J, coverEdge p ∈ winE c lo hi := htr i hlo hhi
  -- the walk of `τ ^ i` ends at the level `i`
  have hlsig : lsig c (wordOf (τ ^ i)) = i := by
    have h1 : cohom c (τ ^ i) = Multiplicative.ofAdd (lsig c (wordOf (τ ^ i))) := by
      have h := cohom_mk c (wordOf (τ ^ i))
      rw [mk_wordOf] at h
      exact h
    have h2 : cohom c (τ ^ i) = Multiplicative.ofAdd i := by
      rw [map_zpow, hτ, ofAdd_one_zpow_local]
    exact Multiplicative.ofAdd.injective (h1.symm.trans h2)
  -- telescoping: the product of the loop classes of the walk of `τ ^ i` is `τ ^ i * (Wt i)⁻¹`
  have hgauge : gaugeMap Wt c (FreeGroup.mk J) = τ ^ i * (Wt i)⁻¹ := by
    show gaugeMap Wt c (FreeGroup.mk (decor c 0 (wordOf (τ ^ i)))) = τ ^ i * (Wt i)⁻¹
    rw [gauge_decor, mk_wordOf, hlsig, hW0, zero_add]
    simp
  -- the live word of the walk has the same `winRho`-image
  have hrho : winRho Wt c lo hi (FreeGroup.mk (liveDecor Wt c lo hi J)) = τ ^ i * (Wt i)⁻¹ := by
    rw [liveDecorWinRho Wt c J hJedges, hgauge]
  -- applying `mk` to the class of the inverse live word gives an element of the vertex
  have hmem : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
      (winRho Wt c lo hi ((FreeGroup.mk (liveDecor Wt c lo hi J))⁻¹)) ∈
        winVertex Wt c lo hi u l := by
    rw [winVertex]
    exact Subgroup.mem_map.mpr ⟨_, ⟨_, rfl⟩, rfl⟩
  -- and it is the level factor
  have heq : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
      (winRho Wt c lo hi ((FreeGroup.mk (liveDecor Wt c lo hi J))⁻¹))
      = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt i) *
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i) := by
    rw [map_inv, hrho, map_inv, map_mul, map_inv, map_zpow, mul_inv_rev, inv_inv, ← zpow_neg]
  rw [← heq]
  exact hmem

end Work.OROneRel
