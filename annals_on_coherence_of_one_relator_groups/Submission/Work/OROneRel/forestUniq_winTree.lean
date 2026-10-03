import Mathlib
import Submission.Work.OROneRel.delWordDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.exists_treeGauge

/-!
# The edges of trivial loop class of a gauge form a forest

`Work.OROneRel.forestUniq_winTree`: for any gauge `Wt : ℤ → FreeGroup α` (a word attached to every
level of the `ℤ`-cover) and any window `[lo,hi]`, the edges of the window of *trivial loop class*
(`winTree Wt c lo hi`) satisfy the forest property `ForestUniq`: two non-backtracking walks whose
edges all lie in the tree, with the same endpoints, traverse the same edges.

## The argument

Two ingredients (neither needs the gauge to have any prescribed weight, so the hypothesis `hcoh` of
the statement is never used):

* `noBT_isReduced` below: a walk without immediate backtrack spells a *reduced* word.  An adjacent
  inverse pair `(x,b),(x,!b)` of the word decorates to two consecutive traversals of the same
  level-graph edge in opposite directions, which `NoBT` forbids.
* `telescope_walkIn` below: along a walk all of whose edges have `coverClassAt W c · = 1`, the gauge
  values telescope: each step multiplies the gauge value by the traversed letter, so
  `W a * mk L = W (a + lsig c L)`.

The two walks of the `ForestUniq` data have the same endpoints, so telescoping shows that they spell
the same element of `F α`; both words are reduced, and a reduced word is determined by its value
(`FreeGroup.Red.exact` and `FreeGroup.IsReduced.red_iff_eq`).  Hence the two walks have the same
letters, in particular the same edge sequence.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The first step of the decorated walk: the head decoration of `p` (read at the level `a`),
followed by the walk of the tail read at the level `a + linc c p`. -/
private theorem decor_head_level (c : α → ℤ) (a : ℤ) (p : α × Bool) (M : List (α × Bool)) :
    decor c a (p :: M) = ((p.1, if p.2 then a else a - c p.1), p.2) :: decor c (a + linc c p) M := by
  obtain ⟨z, d⟩ := p
  cases d <;> rfl

/-- **A walk without immediate backtrack is spelled by a reduced word.**  The only way a word can
fail to be reduced is an adjacent pair of inverse letters `(x, b), (x, !b)`; the decorations of such
a pair are two consecutive traversals of the *same* level-graph edge with opposite signs, which
`NoBT` forbids. -/
private theorem noBT_isReduced (c : α → ℤ) :
    ∀ (a : ℤ) (L : List (α × Bool)), NoBT c a L → FreeGroup.IsReduced L
  | _, [], _ => FreeGroup.IsReduced.nil
  | _, [_], _ => FreeGroup.IsReduced.singleton
  | a, (x, b) :: (y, d) :: L', h => by
      rw [FreeGroup.isReduced_cons_cons]
      refine ⟨?_, noBT_isReduced c (a + linc c (x, b)) ((y, d) :: L') ?_⟩
      · intro hxy
        have hh := h [] (decor c (a + linc c (x, b) + linc c (y, d)) L')
            ((x, if b then a else a - c x), b)
            ((y, if d then a + linc c (x, b) else a + linc c (x, b) - c y), d)
            (by cases b <;> cases d <;> rfl)
        rcases hh with hne | heq
        · by_contra hbd
          apply hne
          cases b <;> cases d <;>
            simp_all [linc, coverEdge, Int.sub_eq_add_neg]
        · exact heq
      · intro L₁ L₂ r s hEq
        exact h ([((x, if b then a else a - c x), b)] ++ L₁) L₂ r s (by
          rw [decor_head_level c a (x, b) ((y, d) :: L'), hEq]
          simp)

/-- The empty word has weight zero. -/
private theorem lsig_nil_aux (c : α → ℤ) : lsig c ([] : List (α × Bool)) = 0 := rfl

/-- **Telescoping of the gauge values along a walk of trivial loop class.**  If every edge traversed
by the walk of `L` from the level `a` has `coverClassAt W c · = 1`, then the gauge value `W a`
multiplied by the word of `L` is the gauge value at the endpoint `a + lsig c L`. -/
private theorem telescope_walkIn (W : ℤ → FreeGroup α) (c : α → ℤ) (T : Set (α × ℤ))
    (hT : ∀ e ∈ T, coverClassAt W c e = 1) :
    ∀ (a : ℤ) (L : List (α × Bool)), WalkIn c T a L →
      W a * FreeGroup.mk L = W (a + lsig c L)
  | a, [], _ => by
      rw [show FreeGroup.mk ([] : List (α × Bool)) = 1 from FreeGroup.one_eq_mk.symm, lsig_nil_aux,
        add_zero, mul_one]
  | a, (x, true) :: M, hL => by
      have hmem : ((x, a) : α × ℤ) ∈ T := by
        have h := hL ((x, a), true) (by rw [decor_head_level]; exact List.mem_cons_self ..)
        simpa [coverEdge] using h
      have htail : WalkIn c T (a + c x) M := fun r hr =>
        hL r (by rw [decor_head_level]; exact List.mem_cons_of_mem _ hr)
      have ih := telescope_walkIn W c T hT (a + c x) M htail
      have hcl : W a * FreeGroup.of x = W (a + c x) := by
        have h := hT _ hmem
        rw [coverClassAt, gaugeMap_of] at h
        rwa [mul_inv_eq_one] at h
      have hmk : FreeGroup.mk ((x, true) :: M) = FreeGroup.of x * FreeGroup.mk M := by
        rw [show ((x, true) : α × Bool) :: M = [(x, true)] ++ M from rfl, ← FreeGroup.mul_mk,
          show FreeGroup.mk ([(x, true)] : List (α × Bool)) = FreeGroup.of x from rfl]
      rw [hmk, ← mul_assoc, hcl, ih]
      congr 1
      simp [lsig]
      ring
  | a, (x, false) :: M, hL => by
      have hmem : ((x, a - c x) : α × ℤ) ∈ T := by
        have h := hL ((x, a - c x), false) (by rw [decor_head_level]; exact List.mem_cons_self ..)
        simpa [coverEdge] using h
      have htail : WalkIn c T (a - c x) M := fun r hr =>
        hL r (by rw [decor_head_level]; exact List.mem_cons_of_mem _ hr)
      have ih := telescope_walkIn W c T hT (a - c x) M htail
      have hcl : W a * (FreeGroup.of x)⁻¹ = W (a - c x) := by
        have h := hT _ hmem
        rw [coverClassAt, gaugeMap_of] at h
        rw [show (a - c x) + c x = a from by ring, mul_inv_eq_one] at h
        rw [← h]
        group
      have hmk : FreeGroup.mk ((x, false) :: M) = (FreeGroup.of x)⁻¹ * FreeGroup.mk M := by
        rw [show ((x, false) : α × Bool) :: M = [(x, false)] ++ M from rfl, ← FreeGroup.mul_mk,
          show FreeGroup.mk ([(x, false)] : List (α × Bool)) = (FreeGroup.of x)⁻¹ from by
            rw [show ([(x, false)] : List (α × Bool)) = FreeGroup.invRev [(x, true)] from rfl,
              ← FreeGroup.inv_mk, show FreeGroup.mk [(x, true)] = FreeGroup.of x from rfl]]
      rw [hmk, ← mul_assoc, hcl, ih]
      congr 1
      simp only [lsig, List.map_cons, List.sum_cons, Bool.false_eq_true, if_false]
      ring

theorem forestUniq_winTree {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (hcoh : ∀ i : ℤ, lo ≤ i → i ≤ hi → Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i) :
    Work.OROneRel.ForestUniq c (Work.OROneRel.winTree Wt c lo hi) := by
  intro L₁ L₂ a b hls₁ hw₁ hn₁ hls₂ hw₂ hn₂
  have hred₁ : FreeGroup.IsReduced L₁ := noBT_isReduced c a L₁ hn₁
  have hred₂ : FreeGroup.IsReduced L₂ := noBT_isReduced c a L₂ hn₂
  have hT : ∀ e ∈ Work.OROneRel.winTree Wt c lo hi, Work.OROneRel.coverClassAt Wt c e = 1 :=
    fun e he => he.2
  have ht₁ := telescope_walkIn Wt c (Work.OROneRel.winTree Wt c lo hi) hT a L₁ hw₁
  have ht₂ := telescope_walkIn Wt c (Work.OROneRel.winTree Wt c lo hi) hT a L₂ hw₂
  have hb₁ : a + Work.OROneRel.lsig c L₁ = b := by rw [hls₁]; ring
  have hb₂ : a + Work.OROneRel.lsig c L₂ = b := by rw [hls₂]; ring
  have hmk : FreeGroup.mk L₁ = FreeGroup.mk L₂ := by
    apply mul_left_cancel (a := Wt a)
    rw [ht₁, ht₂, hb₁, hb₂]
  have hL : L₁ = L₂ := by
    obtain ⟨M, hM₁, hM₂⟩ := FreeGroup.Red.exact.mp hmk
    have h1 : M = L₁ := (FreeGroup.IsReduced.red_iff_eq hred₁).mp hM₁
    have h2 : M = L₂ := (FreeGroup.IsReduced.red_iff_eq hred₂).mp hM₂
    exact h1.symm.trans h2
  exact Or.inl (by rw [hL])

end Work.OROneRel
