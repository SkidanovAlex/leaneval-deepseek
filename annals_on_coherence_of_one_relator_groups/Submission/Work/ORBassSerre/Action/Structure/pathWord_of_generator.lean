import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.BSWalk
import Submission.Work.ORBassSerre.Action.Structure.exists_parent_chain
import Submission.Work.ORBassSerre.Action.Structure.exists_concat

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action.Structure

open Quiver

/-!
# Every generator of the graph-of-groups presentation is the element of a closed path word

Let `d` be the spanning-tree datum of a cocompact action of `G` on a graph `V` without inversions,
and let `D : d.PresData` be presentation data of the fundamental domain, with fundamental group
`Γ = Gamma d D` and canonical map `Φ : Γ →* G`.

The generators of `Γ` are

* the elements `πV A (of i)` of the vertex groups `vgroup A`, and
* the stable letters `t_E` of the non-tree edge orbits `E`.

The purpose of this file is to show that every generator of `Γ` is the `elt` of a *closed* path
word based at the root of the spanning tree (the statement `pathWord_of_generator`).  This is the
input to the reduction argument of `BSReduction`, which expresses every element of `Γ` as the `elt`
of a closed path word based at the root.

The construction is the following.  For a vertex orbit `A` the parent chain
(`exists_parent_chain`) gives a chain of tree edges from the root down to `A`; along such a chain
every step is a *tree* edge orbit, so its contribution to `elt` is trivial
(`stepGam_eq_one_of_tree`), and we may take all letters to be `1` (`Letter.gam_eq_one`).  Hence
there are path words `root → A` (`exists_pathWord_root_to`) and `A → root`
(`exists_pathWord_to_root`) with trivial `elt`, and concatenating them with the single-letter word
at `A` carrying a given element of `vgroup A` (`exists_singleLetter`) — respectively with the single
step along a non-tree edge orbit `E` from `srcE E` to `tgtE E`, which contributes exactly
`stepGam D E true` (`exists_stepWord`) — produces the wanted closed path word.

The triviality of a path word all of whose steps are tree edges and all of whose letters are trivial
is recorded as `PathWord.elt_eq_one_of_triv`.
-/

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

namespace TreeDatum

variable {d : TreeDatum G V}
variable [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]

/-! ## Trivial steps and trivial letters -/

/-- A step along a *tree* edge orbit contributes `1` to the `Γ`-element of a path word. -/
theorem stepGam_eq_one_of_tree (D : d.PresData) {E : Work.ORBassSerre.orbitE G V}
    (h : d.IsTreeEdge E) (b : Bool) : stepGam D E b = 1 := by
  rw [stepGam, dif_pos h]

/-- A letter whose underlying element of `G` is trivial is trivial in `Γ`. -/
theorem Letter.gam_eq_one (D : d.PresData) (l : Letter d) (hx : l.2 = 1) :
    Letter.gam l D = 1 := by
  obtain ⟨A, x⟩ := l
  rw [Letter.gam, hx, map_one]

/-- **A path word all of whose steps are tree edge steps and all of whose letters are trivial
represents `1` in `Γ`.** -/
theorem PathWord.elt_eq_one_of_triv (D : d.PresData) (W : PathWord d)
    (hstep : ∀ k, k < W.len → d.IsTreeEdge (W.stepE k))
    (hlet : ∀ k, k ≤ W.len → (W.letter k).2 = 1) : W.elt D = 1 := by
  have hg : ∀ k, k ≤ W.len → Letter.gam (W.letter k) D = 1 :=
    fun k hk => Letter.gam_eq_one D (W.letter k) (hlet k hk)
  have htpre : ∀ k, k ≤ W.len → W.tpre D k = 1 := by
    intro k
    induction k with
    | zero => intro _; rw [PathWord.tpre_zero]
    | succ k ih =>
      intro hk
      rw [PathWord.tpre_succ, ih (by omega), hg k (by omega),
        stepGam_eq_one_of_tree D (hstep k (by omega)) (W.stepB k), mul_one, one_mul]
  rw [PathWord.elt, htpre W.len le_rfl, hg W.len le_rfl, mul_one]

/-! ## Path words along the parent chain -/

/-- **The path word from the root orbit to a given vertex orbit**, along the parent chain, with all
letters trivial.  Every step is a step along a *tree* edge orbit, so `elt` is trivial for every
presentation datum. -/
theorem exists_pathWord_root_to [Nonempty (Work.ORBassSerre.orbitE G V)]
    (A : Work.ORBassSerre.orbitV G V) :
    ∃ W : PathWord d, W.orb 0 = d.root ∧ W.orb W.len = A ∧
      ∀ D : d.PresData, W.elt D = 1 := by
  classical
  obtain ⟨c, n, hc0, hcn, hne, hpar⟩ := exists_parent_chain (G := G) (V := V) d A
  let stepE : ℕ → Work.ORBassSerre.orbitE G V :=
    fun k => if h : k < n then Quotient.mk'' (d.parArrow (c (k + 1)) (hne k h))
      else Classical.arbitrary (Work.ORBassSerre.orbitE G V)
  have hstepE : ∀ k (hk : k < n),
      stepE k = Quotient.mk'' (d.parArrow (c (k + 1)) (hne k hk)) :=
    fun k hk => by simp only [stepE, dif_pos hk]
  let W : PathWord d :=
    { len := n
      orb := c
      letter := fun k => ⟨c k, 1⟩
      letter_orbit := fun k _ => rfl
      stepE := stepE
      stepB := fun _ => true
      step_src := fun k hk => by
        show moveSrc (stepE k) true = c k
        rw [moveSrc_true, hstepE k hk, d.srcE_parArrow (hne k hk), hpar k hk]
      step_tgt := fun k hk => by
        show moveTgt (stepE k) true = c (k + 1)
        rw [moveTgt_true, hstepE k hk, d.tgtE_parArrow (hne k hk)] }
  refine ⟨W, ?_, ?_, ?_⟩
  · show c 0 = d.root
    exact hc0
  · show c n = A
    exact hcn
  · intro D
    refine PathWord.elt_eq_one_of_triv (d := d) D W ?_ ?_
    · intro k hk
      have hk' : k < n := hk
      show d.IsTreeEdge (stepE k)
      rw [hstepE k hk']
      exact d.isTreeEdge_mk (hne k hk')
    · intro k hk
      rfl

/-- **The path word from a given vertex orbit to the root orbit**, along the parent chain, with all
letters trivial.  Every step is a step along a *tree* edge orbit, so `elt` is trivial for every
presentation datum. -/
theorem exists_pathWord_to_root [Nonempty (Work.ORBassSerre.orbitE G V)]
    (A : Work.ORBassSerre.orbitV G V) :
    ∃ W : PathWord d, W.orb 0 = A ∧ W.orb W.len = d.root ∧
      ∀ D : d.PresData, W.elt D = 1 := by
  classical
  obtain ⟨c, n, hc0, hcn, hne, hpar⟩ := exists_parent_chain (G := G) (V := V) d A
  have hne' : ∀ k, k < n → c (n - k) ≠ d.root := by
    intro k hk
    have h1 : n - k = (n - k - 1) + 1 := by omega
    rw [h1]
    exact hne (n - k - 1) (by omega)
  have hpar' : ∀ k, k < n → d.par (c (n - k)) = c (n - k - 1) := by
    intro k hk
    have h1 : n - k = (n - k - 1) + 1 := by omega
    rw [h1]
    exact hpar (n - k - 1) (by omega)
  let stepE : ℕ → Work.ORBassSerre.orbitE G V :=
    fun k => if h : k < n then Quotient.mk'' (d.parArrow (c (n - k)) (hne' k h))
      else Classical.arbitrary (Work.ORBassSerre.orbitE G V)
  have hstepE : ∀ k (hk : k < n),
      stepE k = Quotient.mk'' (d.parArrow (c (n - k)) (hne' k hk)) :=
    fun k hk => by simp only [stepE, dif_pos hk]
  let W : PathWord d :=
    { len := n
      orb := fun k => c (n - k)
      letter := fun k => ⟨c (n - k), 1⟩
      letter_orbit := fun k _ => rfl
      stepE := stepE
      stepB := fun _ => false
      step_src := fun k hk => by
        show moveSrc (stepE k) false = c (n - k)
        rw [moveSrc_false, hstepE k hk, d.tgtE_parArrow (hne' k hk)]
      step_tgt := fun k hk => by
        show moveTgt (stepE k) false = c (n - (k + 1))
        rw [moveTgt_false, hstepE k hk, d.srcE_parArrow (hne' k hk), hpar' k hk]
        congr 1 }
  refine ⟨W, ?_, ?_, ?_⟩
  · show c (n - 0) = A
    rw [Nat.sub_zero, hcn]
  · show c (n - n) = d.root
    rw [Nat.sub_self, hc0]
  · intro D
    refine PathWord.elt_eq_one_of_triv (d := d) D W ?_ ?_
    · intro k hk
      have hk' : k < n := hk
      show d.IsTreeEdge (stepE k)
      rw [hstepE k hk']
      exact d.isTreeEdge_mk (hne' k hk')
    · intro k hk
      rfl

/-! ## The one-letter word and the single step -/

/-- The path word of length `0` at a vertex orbit, consisting of a single letter. -/
theorem exists_singleLetter [Nonempty (Work.ORBassSerre.orbitE G V)]
    (A : Work.ORBassSerre.orbitV G V) (g : ↥(d.vgroup A)) :
    ∃ W : PathWord d, W.orb 0 = A ∧ W.len = 0 ∧
      ∀ D : d.PresData, W.elt D = d.gEltHom D A g := by
  refine ⟨{ len := 0
            orb := fun _ => A
            letter := fun _ => ⟨A, g⟩
            letter_orbit := fun _ _ => rfl
            stepE := fun _ => Classical.arbitrary _
            stepB := fun _ => true
            step_src := fun k hk => absurd hk (Nat.not_lt_zero k)
            step_tgt := fun k hk => absurd hk (Nat.not_lt_zero k) }, rfl, rfl, ?_⟩
  intro D
  rw [PathWord.elt, PathWord.tpre_zero, one_mul]
  rfl

/-- **The path word consisting of the single step along `E`** from `srcE E` to `tgtE E`, with all
letters trivial.  Its `elt` is exactly the stable-letter part of that step. -/
theorem exists_stepWord [Nonempty (Work.ORBassSerre.orbitE G V)]
    (E : Work.ORBassSerre.orbitE G V) :
    ∃ W : PathWord d,
      W.orb 0 = Work.ORBassSerre.Action.srcE (G := G) (V := V) E ∧
      W.orb W.len = Work.ORBassSerre.Action.tgtE (G := G) (V := V) E ∧
      ∀ D : d.PresData, W.elt D = stepGam D E true := by
  classical
  let orb : ℕ → Work.ORBassSerre.orbitV G V :=
    fun k => if k = 0 then Work.ORBassSerre.Action.srcE (G := G) (V := V) E
      else Work.ORBassSerre.Action.tgtE (G := G) (V := V) E
  let W : PathWord d :=
    { len := 1
      orb := orb
      letter := fun k => ⟨orb k, 1⟩
      letter_orbit := fun k _ => rfl
      stepE := fun _ => E
      stepB := fun _ => true
      step_src := by
        intro k hk
        interval_cases k
        simp [orb, moveSrc]
      step_tgt := by
        intro k hk
        interval_cases k
        simp [orb, moveTgt] }
  refine ⟨W, ?_, ?_, ?_⟩
  · show orb 0 = Work.ORBassSerre.Action.srcE (G := G) (V := V) E
    simp [orb]
  · show orb 1 = Work.ORBassSerre.Action.tgtE (G := G) (V := V) E
    simp [orb]
  · intro D
    have h0 : Letter.gam (show Letter d from ⟨orb 0, 1⟩) D = 1 :=
      Letter.gam_eq_one D _ rfl
    have h1 : Letter.gam (show Letter d from ⟨orb 1, 1⟩) D = 1 :=
      Letter.gam_eq_one D _ rfl
    show (W.tpre D 1 * Letter.gam (W.letter 1) D) = stepGam D E true
    rw [PathWord.tpre_succ, PathWord.tpre_zero]
    show (1 * Letter.gam (W.letter 0) D * stepGam D (W.stepE 0) (W.stepB 0)) *
      Letter.gam (W.letter 1) D = stepGam D E true
    rw [h0, h1]
    show (1 * 1 * stepGam D E true) * 1 = stepGam D E true
    rw [mul_one, mul_one, one_mul]

/-! ## The vertex-group generator and the stable letter -/

/-- The generator of `Γ` corresponding to a generator of a vertex group is the `Γ`-element of the
element of the vertex group which it represents. -/
theorem gEltHom_generator (D : d.PresData) (A : Work.ORBassSerre.orbitV G V)
    (i : Fin (D.nV A)) :
    d.gEltHom D A (D.πV A (FreeGroup.of i)) =
      PresentedGroup.of (Sum.inl (⟨A, i⟩ : Σ B, Fin (D.nV B))) := by
  rw [show d.gEltHom D A (D.πV A (FreeGroup.of i)) =
      PresentedGroup.mk (rels d D)
        (blockOf d D A (wordOf d D A (D.πV A (FreeGroup.of i)))) from rfl]
  rw [mk_block_eq_of_πV_eq d D (w := wordOf d D A (D.πV A (FreeGroup.of i)))
    (w' := FreeGroup.of i) (by rw [wordOf_spec]), blockOf_of]
  rfl

/-- The stable-letter part of the step along a *non-tree* edge orbit `E` in the direction from
`srcE E` to `tgtE E` is the generator of `Γ` attached to `E`. -/
theorem stepGam_true_eq_of_not_tree (D : d.PresData) {E : Work.ORBassSerre.orbitE G V}
    (h : ¬ d.IsTreeEdge E) :
    stepGam D E true = PresentedGroup.of (Sum.inr (⟨E, h⟩ : {E // ¬ d.IsTreeEdge E})) := by
  rw [stepGam, dif_neg h]
  rfl

end TreeDatum

theorem pathWord_of_generator {G : Type*} {V : Type*}
    [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V]
    {d : Work.ORBassSerre.Action.Structure.TreeDatum G V}
    [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]
    [Nonempty (Work.ORBassSerre.orbitE G V)]
    (D : d.PresData) (x : d.PresGen D) :
    ∃ W : Work.ORBassSerre.Action.Structure.TreeDatum.PathWord d,
      W.orb 0 = d.root ∧ W.Closed ∧ W.elt D = PresentedGroup.of x := by
  classical
  rcases x with ⟨A, i⟩ | ⟨E, hE⟩
  · -- a generator of a vertex group: walk from the root to `A`, take the letter representing
    -- `πV A (of i)` there, and walk back
    obtain ⟨W₁, h10, h1L, h1e⟩ := TreeDatum.exists_pathWord_root_to (d := d) A
    obtain ⟨W₂, h20, h2len, h2e⟩ :=
      TreeDatum.exists_singleLetter (d := d) A (D.πV A (FreeGroup.of i))
    obtain ⟨W₃, h30, h3L, h3e⟩ := TreeDatum.exists_pathWord_to_root (d := d) A
    obtain ⟨W₁₂, -, h120, h12L, h12e⟩ := exists_concat W₁ W₂ (by rw [h1L, h20])
    obtain ⟨W, -, h0, hL, he⟩ := exists_concat W₁₂ W₃ (by rw [h12L, h2len, h20, h30])
    have h0' : W.orb 0 = d.root := by rw [h0, h120, h10]
    refine ⟨W, h0', ?_, ?_⟩
    · show W.orb W.len = W.orb 0
      rw [hL, h3L]
      exact h0'.symm
    · rw [he, h12e, h1e, h2e, h3e]
      simp only [one_mul, mul_one]
      exact TreeDatum.gEltHom_generator (d := d) D A i
  · -- a stable letter: walk from the root to `srcE E`, step along `E`, and walk back to the root
    obtain ⟨W₁, h10, h1L, h1e⟩ := TreeDatum.exists_pathWord_root_to (d := d)
      (Work.ORBassSerre.Action.srcE (G := G) (V := V) E)
    obtain ⟨W₂, h20, h2L, h2e⟩ := TreeDatum.exists_stepWord (d := d) E
    obtain ⟨W₃, h30, h3L, h3e⟩ := TreeDatum.exists_pathWord_to_root (d := d)
      (Work.ORBassSerre.Action.tgtE (G := G) (V := V) E)
    obtain ⟨W₁₂, -, h120, h12L, h12e⟩ := exists_concat W₁ W₂ (by rw [h1L, h20])
    obtain ⟨W, -, h0, hL, he⟩ := exists_concat W₁₂ W₃ (by rw [h12L, h2L, h30])
    have h0' : W.orb 0 = d.root := by rw [h0, h120, h10]
    refine ⟨W, h0', ?_, ?_⟩
    · show W.orb W.len = W.orb 0
      rw [hL, h3L]
      exact h0'.symm
    · rw [he, h12e, h1e, h2e, h3e]
      simp only [one_mul, mul_one]
      exact TreeDatum.stepGam_true_eq_of_not_tree (d := d) D hE

end Work.ORBassSerre.Action.Structure
