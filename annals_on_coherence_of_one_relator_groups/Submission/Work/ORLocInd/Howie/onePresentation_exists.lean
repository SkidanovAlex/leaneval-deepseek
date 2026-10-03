import Mathlib
import Submission.Work.ORLocInd.Howie.RoseBasic
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.OROneRel.Basic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.ambiguousOpen false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

universe u

namespace Work.ORLocInd.Howie

open Quiver

/-! ## `FreeGroup.toWord` does not depend on the `DecidableEq α` instance -/

/-- The maximal reduction of a free group element does not depend on the `DecidableEq` instance
used to compute it: both candidates are reduced words representing the same element, and `mk` is
injective on reduced words. -/
theorem toWord_eq_of_decidableEq {α : Type u} (i j : DecidableEq α) (x : FreeGroup α) :
    @FreeGroup.toWord α i x = @FreeGroup.toWord α j x := by
  have h1 : FreeGroup.IsReduced (@FreeGroup.toWord α i x) := @FreeGroup.isReduced_toWord α i x
  have h2 : FreeGroup.IsReduced (@FreeGroup.toWord α j x) := @FreeGroup.isReduced_toWord α j x
  have hmk : FreeGroup.mk (@FreeGroup.toWord α i x) = FreeGroup.mk (@FreeGroup.toWord α j x) := by
    rw [@FreeGroup.mk_toWord α i x, @FreeGroup.mk_toWord α j x]
  obtain ⟨M, hM1, hM2⟩ := FreeGroup.Red.exact.mp hmk
  rw [h1.red_iff_eq] at hM1
  rw [h2.red_iff_eq] at hM2
  exact hM1.symm.trans hM2

/-! ## The word of a path of the rose

`roseWord` (in `RoseBasic`) is `p.arrowList.map (fun e => e.hom)`, but it is *stated* for closed
paths at `roseVtx α`.  Since `Rose α` is (definitionally) a subsingleton, the very same term makes
sense for a path between any two vertices of the rose; we record it as `pathWord` so that the
decomposition lemmas for arbitrary paths of the rose can be used. -/

/-- The word read off a path of the rose (the arrows of the path, in order, as letters). -/
def pathWord {α : Type u} {a b : Rose α} (p : Quiver.Path a b) : List (α × Bool) :=
  p.arrowList.map (fun e => e.hom)

@[simp] theorem pathWord_nil {α : Type u} {a : Rose α} :
    pathWord (Quiver.Path.nil : Quiver.Path a a) = [] := rfl

theorem pathWord_toPath {α : Type u} {a b : Rose α} (e : a ⟶ b) :
    pathWord (e.toPath) = [e] := by
  show (e.toPath.arrowList.map (fun f => f.hom)) = [e]
  rw [Quiver.Path.arrowList_toPath']
  rfl

theorem pathWord_comp {α : Type u} {a b c : Rose α} (p : Quiver.Path a b)
    (q : Quiver.Path b c) : pathWord (p.comp q) = pathWord p ++ pathWord q := by
  simp [pathWord, Quiver.Path.arrowList_comp']

theorem pathWord_cons {α : Type u} {a b c : Rose α} (p : Quiver.Path a b) (e : b ⟶ c) :
    pathWord (p.cons e) = pathWord p ++ [e] := by
  simp [pathWord, Quiver.Path.arrowList_cons]

/-- `pathWord` agrees with `roseWord` on closed paths at the rose vertex. -/
theorem pathWord_eq_roseWord {α : Type u} (p : Quiver.Path (roseVtx α) (roseVtx α)) :
    pathWord p = roseWord p := rfl

/-- The word of `rosePath L` is `L`. -/
@[simp] theorem pathWord_rosePath {α : Type u} (L : List (α × Bool)) :
    pathWord (rosePath L) = L := by
  rw [pathWord_eq_roseWord, roseWord_rosePath]

/-- The word of the `m`-fold concatenation of a closed path. -/
theorem pathWord_compPower {α : Type u} {v : Rose α} (q : Quiver.Path v v) (m : ℕ) :
    pathWord (Quiver.Path.compPower q m) = (List.replicate m (pathWord q)).flatten := by
  induction m with
  | zero => simp [Quiver.Path.compPower]
  | succ n ih =>
      rw [Quiver.Path.compPower_succ, pathWord_comp, ih, List.replicate_succ, List.flatten_cons]

/-- Every path of the rose is `rosePath` of its own word. -/
theorem rosePath_pathWord {α : Type u} : ∀ (b : Rose α) (p : Quiver.Path (roseVtx α) b),
    rosePath (pathWord p) = p := by
  intro b p
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [pathWord_cons, rosePath_append, ih, rosePath_singleton]
      rfl

/-- `rosePath` is injective. -/
theorem rosePath_injective {α : Type u} : Function.Injective (rosePath (α := α)) :=
  fun _ _ h => by
    have h' := congrArg roseWord h
    rwa [roseWord_rosePath, roseWord_rosePath] at h'

/-- The closed path `[(x,b),(x,!b)]` is the backtrack `(x,b) · (x,b)⁻¹`. -/
theorem rosePath_cons_cons {α : Type u} (x : α) (b : Bool) (K : List (α × Bool)) :
    rosePath ((x, b) :: (x, !b) :: K)
      = (rosePath [(x, b)]).comp ((rosePath [(x, !b)]).comp (rosePath K)) := by
  rw [rosePath_cons, rosePath_cons, rosePath_singleton, rosePath_singleton]

/-- `rosePath` turns a reduction step of the words into a backtrack deletion. -/
theorem deleteBacktrack_rosePath_of_step {α : Type u} {L M : List (α × Bool)}
    (h : FreeGroup.Red.Step L M) :
    Quiver.Path.DeleteBacktrack (rosePath L) (rosePath M) := by
  obtain @⟨L₁, L₂, x, b⟩ := h
  have hpath : rosePath (L₁ ++ (x, b) :: (x, !b) :: L₂)
      = (rosePath L₁).comp
          ((rosePath [(x, b)]).comp ((rosePath [(x, !b)]).comp (rosePath L₂))) := by
    rw [rosePath_append, rosePath_cons_cons]
  have hpath₂ : rosePath (L₁ ++ L₂) = (rosePath L₁).comp (rosePath L₂) :=
    rosePath_append L₁ L₂
  rw [hpath, hpath₂]
  exact Quiver.Path.DeleteBacktrack.intro (a := roseVtx α) (x := roseVtx α) (y := roseVtx α)
    (b := roseVtx α) (p₁ := rosePath L₁) (e := (x, b)) (p₂ := rosePath L₂)

/-- A `DeleteBacktrack` step between closed paths of the rose produces a `FreeGroup.Red.Step`
between their words. -/
theorem exists_of_deleteBacktrack {α : Type u} {p q : Quiver.Path (roseVtx α) (roseVtx α)}
    (h : Quiver.Path.DeleteBacktrack p q) :
    ∃ L M : List (α × Bool), p = rosePath L ∧ q = rosePath M ∧ FreeGroup.Red.Step L M := by
  cases h with
  | intro p₁ e p₂ =>
    refine ⟨pathWord p₁ ++ (e.1, e.2) :: (e.1, !e.2) :: pathWord p₂, pathWord p₁ ++ pathWord p₂,
      ?_, ?_,
      FreeGroup.Red.Step.not (L₁ := pathWord p₁) (L₂ := pathWord p₂) (x := e.1) (b := e.2)⟩
    · rw [rosePath_append, rosePath_cons_cons, rosePath_singleton, rosePath_singleton,
        rosePath_pathWord (roseVtx α) p₁, rosePath_pathWord (roseVtx α) p₂]
      rfl
    · rw [rosePath_append, rosePath_pathWord (roseVtx α) p₁, rosePath_pathWord (roseVtx α) p₂]

/-- A `DeleteBacktrack` step between closed paths of the rose is exactly a `FreeGroup.Red.Step`
between their words. -/
theorem deleteBacktrack_rosePath_iff {α : Type u} (L M : List (α × Bool)) :
    Quiver.Path.DeleteBacktrack (rosePath L) (rosePath M) ↔ FreeGroup.Red.Step L M := by
  constructor
  · intro h
    obtain ⟨L', M', hL', hM', hstep⟩ := exists_of_deleteBacktrack h
    rw [← rosePath_injective hL', ← rosePath_injective hM'] at hstep
    exact hstep
  · exact deleteBacktrack_rosePath_of_step

/-- `IsReduced` of `rosePath L` is `FreeGroup.IsReduced L`. -/
theorem isReduced_rosePath_iff' {α : Type u} (L : List (α × Bool)) :
    (rosePath L).IsReduced ↔ FreeGroup.IsReduced L := by
  rw [FreeGroup.isReduced_iff_not_step, Quiver.Path.IsReduced]
  constructor
  · intro h M hM
    exact h (rosePath M) (deleteBacktrack_rosePath_of_step hM)
  · intro h q hq
    obtain ⟨L', M, hL', hq', hstep⟩ := exists_of_deleteBacktrack hq
    rw [← rosePath_injective hL'] at hstep
    exact h M hstep

/-- `rosePath` of a repeated word is a power of closed paths. -/
theorem rosePath_flatten_replicate {α : Type u} (L : List (α × Bool)) (m : ℕ) :
    rosePath ((List.replicate m L).flatten) = Quiver.Path.compPower (rosePath L) m := by
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, rosePath_append, ih,
        Quiver.Path.compPower_succ]

/-- `IsProperPower` of `rosePath L` is being a proper power of words. -/
theorem isProperPower_rosePath_iff' {α : Type u} (L : List (α × Bool)) :
    IsProperPower (rosePath L) ↔
      ∃ (L' : List (α × Bool)) (m : ℕ), 2 ≤ m ∧ L = (List.replicate m L').flatten := by
  constructor
  · rintro ⟨q, m, hm, hq⟩
    refine ⟨pathWord q, m, hm, ?_⟩
    have h := congrArg pathWord hq
    rwa [pathWord_rosePath, pathWord_compPower] at h
  · rintro ⟨L', m, hm, rfl⟩
    exact ⟨rosePath L', m, hm, rosePath_flatten_replicate L' m⟩

/-- If a word is cyclically reduced then so is the corresponding closed path of the rose. -/
theorem isCyclicallyReduced_rosePath' {α : Type u} {L : List (α × Bool)}
    (h : FreeGroup.IsCyclicallyReduced L) : IsCyclicallyReduced (rosePath L) := by
  rintro ⟨u, e, q, hq⟩
  have hL : L = e :: pathWord q ++ [Quiver.reverse e] := by
    have h' := congrArg pathWord hq
    rw [pathWord_rosePath, pathWord_comp, pathWord_toPath, pathWord_cons] at h'
    exact h'
  have hjoin := (FreeGroup.isCyclicallyReduced_cons_append_iff (L := pathWord q)
    (a := Quiver.reverse e) (b := e)).1 (hL ▸ h)
  exact Bool.not_ne_self e.2 (hjoin.2 rfl)

/-! ## The vertex group of the rose is the free group -/

/-- In the free group, a one-letter word times its inverse letter is trivial. -/
theorem mk_pair_inv {α : Type u} (x : α) (b : Bool) :
    FreeGroup.mk [(x, b)] * FreeGroup.mk [(x, !b)] = 1 := by
  rw [FreeGroup.mul_mk, FreeGroup.one_eq_mk]
  exact FreeGroup.Red.exact.2
    ⟨[], Relation.ReflTransGen.single
      (FreeGroup.Red.Step.not (L₁ := []) (L₂ := []) (x := x) (b := b)), FreeGroup.Red.refl⟩

/-- `FreeGroup.mk` is multiplicative on concatenated words. -/
theorem mk_append {α : Type u} (L₁ L₂ : List (α × Bool)) :
    FreeGroup.mk (L₁ ++ L₂) = FreeGroup.mk L₁ * FreeGroup.mk L₂ :=
  (FreeGroup.mul_mk (L₁ := L₁) (L₂ := L₂)).symm

/-- The class of the word of a path is unchanged by deleting a backtrack. -/
theorem mk_pathWord_of_deleteBacktrack {α : Type u} {p q : Quiver.Path (roseVtx α) (roseVtx α)}
    (h : Quiver.Path.DeleteBacktrack p q) :
    FreeGroup.mk (pathWord p) = FreeGroup.mk (pathWord q) := by
  cases h with
  | intro p₁ e p₂ =>
    have h1 : pathWord (p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)))
        = pathWord p₁ ++ ([e] ++ ([Quiver.reverse e] ++ pathWord p₂)) := by
      rw [pathWord_comp, pathWord_comp, pathWord_comp, pathWord_toPath, pathWord_toPath]
    have h2 : pathWord (p₁.comp p₂) = pathWord p₁ ++ pathWord p₂ := pathWord_comp p₁ p₂
    have hpair : FreeGroup.mk [e] * FreeGroup.mk [Quiver.reverse e] = 1 := mk_pair_inv e.1 e.2
    rw [h1, h2, mk_append, mk_append, mk_append, mk_append,
      ← mul_assoc (FreeGroup.mk [e]) (FreeGroup.mk [Quiver.reverse e])
        (FreeGroup.mk (pathWord p₂)),
      hpair, one_mul]

/-- The class of the word of a path is unchanged by reduction. -/
theorem mk_pathWord_of_reducesTo {α : Type u} {p q : Quiver.Path (roseVtx α) (roseVtx α)}
    (h : p.ReducesTo q) : FreeGroup.mk (pathWord p) = FreeGroup.mk (pathWord q) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (mk_pathWord_of_deleteBacktrack hstep)

theorem mk_pathWord_red {α : Type u} (p : Quiver.Path (roseVtx α) (roseVtx α)) :
    FreeGroup.mk (pathWord (red p)) = FreeGroup.mk (pathWord p) :=
  (mk_pathWord_of_reducesTo (p := p) (q := red p) (reducesTo_red p)).symm

/-- Two reduced words with the same class in the free group are equal. -/
theorem mk_eq_of_isReduced {α : Type u} {L₁ L₂ : List (α × Bool)}
    (h : FreeGroup.mk L₁ = FreeGroup.mk L₂) (h₁ : FreeGroup.IsReduced L₁)
    (h₂ : FreeGroup.IsReduced L₂) : L₁ = L₂ := by
  obtain ⟨M, hM1, hM2⟩ := FreeGroup.Red.exact.mp h
  rw [h₁.red_iff_eq] at hM1
  rw [h₂.red_iff_eq] at hM2
  exact hM1.symm.trans hM2

/-- A word which is not reduced contains two adjacent inverse letters. -/
theorem exists_adjacent_of_not_isReduced {α : Type u} {L : List (α × Bool)}
    (h : ¬ FreeGroup.IsReduced L) :
    ∃ (L₁ L₂ : List (α × Bool)) (x : α) (b : Bool), L = L₁ ++ (x, b) :: (x, !b) :: L₂ := by
  induction L with
  | nil => exact absurd FreeGroup.IsReduced.nil h
  | cons a t ih =>
    obtain ⟨a1, a2⟩ := a
    cases t with
    | nil => exact absurd FreeGroup.IsReduced.singleton h
    | cons b t =>
      obtain ⟨b1, b2⟩ := b
      rw [FreeGroup.isReduced_cons_cons, not_and_or] at h
      rcases h with hneg | hrest
      · obtain ⟨h1, h2⟩ : a1 = b1 ∧ a2 ≠ b2 := by tauto
        have hb2 : b2 = !a2 := by
          revert h2
          cases a2 <;> cases b2 <;> simp
        have hb : (b1, b2) = (a1, !a2) := Prod.ext h1.symm hb2
        exact ⟨[], t, a1, a2, by rw [hb]; rfl⟩
      · obtain ⟨L₁, L₂, x, bb, hdec⟩ := ih hrest
        exact ⟨(a1, a2) :: L₁, L₂, x, bb, by rw [hdec]; rfl⟩

/-- The word of a reduced path of the rose is a reduced word. -/
theorem isReduced_pathWord {α : Type u} {p : Quiver.Path (roseVtx α) (roseVtx α)}
    (hp : p.IsReduced) : FreeGroup.IsReduced (pathWord p) := by
  by_contra h
  obtain ⟨L₁, L₂, x, b, hdec⟩ := exists_adjacent_of_not_isReduced h
  have hL : rosePath (L₁ ++ (x, b) :: (x, !b) :: L₂)
      = (rosePath L₁).comp
          ((rosePath [(x, b)]).comp ((rosePath [(x, !b)]).comp (rosePath L₂))) := by
    rw [rosePath_append, rosePath_cons_cons]
  have hM : rosePath (L₁ ++ L₂) = (rosePath L₁).comp (rosePath L₂) := rosePath_append L₁ L₂
  have hd : Quiver.Path.DeleteBacktrack (rosePath (L₁ ++ (x, b) :: (x, !b) :: L₂))
      (rosePath (L₁ ++ L₂)) := by
    rw [hL, hM]
    exact Quiver.Path.DeleteBacktrack.intro (a := roseVtx α) (x := roseVtx α) (y := roseVtx α)
      (b := roseVtx α) (p₁ := rosePath L₁) (e := (x, b)) (p₂ := rosePath L₂)
  exact hp _ (rosePath_pathWord (roseVtx α) p ▸ (hdec.symm ▸ hd))

/-- The vertex group of the free groupoid of the rose is the free group, via the map sending a
reduced closed path to the class of the word it reads. -/
theorem vertexGroup_rose_equiv' {α : Type u} :
    ∃ e : VertexGroup (roseVtx α) ≃* FreeGroup α,
      ∀ (p : Quiver.Path (roseVtx α) (roseVtx α)) (hp : p.IsReduced),
        e ⟨p, hp⟩ = FreeGroup.mk (roseWord p) := by
  let Φ : VertexGroup (roseVtx α) →* FreeGroup α :=
    { toFun := fun p => FreeGroup.mk (pathWord p.1)
      map_one' := by
        show FreeGroup.mk (pathWord (Quiver.Path.nil : Quiver.Path (roseVtx α) (roseVtx α))) = 1
        rw [pathWord_nil]
        exact FreeGroup.one_eq_mk.symm
      map_mul' := by
        intro p q
        show FreeGroup.mk (pathWord (red (p.1.comp q.1)))
          = FreeGroup.mk (pathWord p.1) * FreeGroup.mk (pathWord q.1)
        rw [mk_pathWord_red, pathWord_comp, mk_append] }
  have hinj : Function.Injective Φ := by
    intro p q hpq
    have hred : FreeGroup.IsReduced (pathWord p.1) := isReduced_pathWord p.2
    have hred' : FreeGroup.IsReduced (pathWord q.1) := isReduced_pathWord q.2
    have heq : pathWord p.1 = pathWord q.1 := mk_eq_of_isReduced hpq hred hred'
    refine Subtype.ext ?_
    rw [← rosePath_pathWord (roseVtx α) p.1, heq, rosePath_pathWord (roseVtx α) q.1]
  have hsurj : Function.Surjective Φ := by
    intro g
    refine ⟨⟨rosePath (@FreeGroup.toWord α (Classical.decEq α) g), ?_⟩, ?_⟩
    · exact (isReduced_rosePath_iff' _).2 (@FreeGroup.isReduced_toWord α (Classical.decEq α) g)
    · show FreeGroup.mk (pathWord (rosePath (@FreeGroup.toWord α (Classical.decEq α) g))) = g
      rw [pathWord_rosePath, @FreeGroup.mk_toWord α (Classical.decEq α) g]
  refine ⟨MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩, ?_⟩
  intro p hp
  rfl

/-! ## The one-relator presentation on the rose -/

/-- The code of an arrow of the rose: the generator of the letter. -/
def roseEdgeOf {α : Type u} : Quiver.Total (Rose α) → α := fun e => e.hom.1

/-- The groupoid presentation `⟨rose | rosePath L⟩` on the rose: one vertex, one loop per
generator, and the single relator `rosePath L` (a closed path at the vertex). -/
def rosePresentation {α : Type u} [LinearOrder α] (L : List (α × Bool))
    (hred : (rosePath L).IsReduced) (hcyc : IsCyclicallyReduced (rosePath L))
    (hpp : ¬ IsProperPower (rosePath L)) : Presentation (Rose α) where
  α := α
  edgeOf := roseEdgeOf
  edgeOf_reverse := by
    rintro ⟨a, b, f⟩
    rfl
  noSelfLoop := by
    intro v e h
    exact Bool.not_ne_self e.2 (congrArg Prod.snd h)
  ι := ULift.{u, 0} (Fin 1)
  base := fun _ => roseVtx α
  path := fun _ => rosePath L
  reduced := fun _ => hred
  cyclicallyReduced := fun _ => hcyc
  notProperPower := fun _ => hpp
  staggered := by
    intro i j hij
    exact absurd (Subsingleton.elim i j ▸ hij) (lt_irrefl j)

/-- The code of the rose presentation separates unoriented edges (it reads off the generator). -/
theorem rosePresentation_codeSeparates {α : Type u} [LinearOrder α] (L : List (α × Bool))
    (hred : (rosePath L).IsReduced) (hcyc : IsCyclicallyReduced (rosePath L))
    (hpp : ¬ IsProperPower (rosePath L)) :
    (rosePresentation L hred hcyc hpp).CodeSeparates := by
  intro e f h
  obtain ⟨a, b, g⟩ := e
  obtain ⟨a', b', g'⟩ := f
  rcases Bool.eq_or_eq_not g.2 g'.2 with h2 | h2
  · left
    have hg : g = g' := Prod.ext h h2
    rw [hg]
    rfl
  · right
    have hg : g = (g'.1, !g'.2) := Prod.ext h h2
    rw [hg]
    rfl

/-! ## Relating the relator normal closure to `PresentedGroup` -/

theorem normalClosure_conjugateSet_eq {α : Type u} (r : FreeGroup α) :
    Subgroup.normalClosure {y : FreeGroup α | ∃ g : FreeGroup α, y = g * r * g⁻¹}
      = Subgroup.normalClosure ({r} : Set (FreeGroup α)) := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.normalClosure_le_normal ?_
    rintro y ⟨g, rfl⟩
    exact Subgroup.Normal.conj_mem Subgroup.normalClosure_normal r
      (Subgroup.subset_normalClosure (Set.mem_singleton r)) g
  · refine Subgroup.normalClosure_le_normal ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.subset_normalClosure ⟨1, by simp⟩

/-- Under the bijection of `vertexGroup_rose_equiv`, the relator normal closure of the rose
presentation at its vertex is the normal closure of `r` in the free group. -/
theorem map_relatorNormalClosure_eq {α : Type u} [LinearOrder α] (L : List (α × Bool))
    (hred : (rosePath L).IsReduced) (hcyc : IsCyclicallyReduced (rosePath L))
    (hpp : ¬ IsProperPower (rosePath L)) (r : FreeGroup α) (hr : FreeGroup.mk L = r)
    (e : VertexGroup (roseVtx α) ≃* FreeGroup α)
    (he : ∀ (p : Quiver.Path (roseVtx α) (roseVtx α)) (hp : p.IsReduced),
        e ⟨p, hp⟩ = FreeGroup.mk (roseWord p)) :
    Subgroup.map (e : VertexGroup (roseVtx α) →* FreeGroup α)
        ((rosePresentation L hred hcyc hpp).relatorNormalClosure (roseVtx α))
      = Subgroup.normalClosure ({r} : Set (FreeGroup α)) := by
  have hmap : Subgroup.map (e : VertexGroup (roseVtx α) →* FreeGroup α)
        ((rosePresentation L hred hcyc hpp).relatorNormalClosure (roseVtx α))
      = Subgroup.normalClosure ((e : VertexGroup (roseVtx α) →* FreeGroup α) ''
          (rosePresentation L hred hcyc hpp).relatorSet (roseVtx α)) := by
    show Subgroup.map (e : VertexGroup (roseVtx α) →* FreeGroup α)
        (Subgroup.normalClosure ((rosePresentation L hred hcyc hpp).relatorSet (roseVtx α))) = _
    exact Subgroup.map_normalClosure _ _ e.surjective
  have hset : (e : VertexGroup (roseVtx α) →* FreeGroup α) ''
        (rosePresentation L hred hcyc hpp).relatorSet (roseVtx α)
      = {y : FreeGroup α | ∃ g : FreeGroup α, y = g * r * g⁻¹} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, δ, hδ, rfl⟩ := hx
      let d : VertexGroup (roseVtx α) := ⟨δ, hδ⟩
      let R : VertexGroup (roseVtx α) := ⟨rosePath L, hred⟩
      refine ⟨e d, ?_⟩
      have hx_eq : (⟨pmul δ (pmul ((rosePresentation L hred hcyc hpp).path i) δ.reverse),
            pmul_isReduced _ _⟩ : VertexGroup (roseVtx α)) = d * R * d⁻¹ := by
        refine Subtype.ext ?_
        simp only [VertexGroup.coe_mul, VertexGroup.coe_inv, Subtype.coe_mk]
        rw [pmul_assoc]
        rfl
      have hcalc : e (d * R * d⁻¹) = e d * e R * (e d)⁻¹ := by
        rw [MulEquiv.map_mul e (d * R) d⁻¹, MulEquiv.map_mul e d R, MulEquiv.map_inv e d]
      have hd : e d = FreeGroup.mk (roseWord δ) := he δ hδ
      have hR : e R = FreeGroup.mk (roseWord (rosePath L)) := he (rosePath L) hred
      rw [hx_eq]
      change e (d * R * d⁻¹) = e d * r * (e d)⁻¹
      rw [hcalc]
      simp only [hd, hR, roseWord_rosePath, hr]
    · rintro ⟨g, rfl⟩
      obtain ⟨δ₀, hδ₀⟩ := e.surjective g
      obtain ⟨δ, hδ⟩ := δ₀
      let d : VertexGroup (roseVtx α) := ⟨δ, hδ⟩
      let R : VertexGroup (roseVtx α) := ⟨rosePath L, hred⟩
      refine ⟨d * R * d⁻¹, ?_, ?_⟩
      · refine ⟨ULift.up 0, δ, hδ, ?_⟩
        refine Subtype.ext ?_
        simp only [VertexGroup.coe_mul, VertexGroup.coe_inv, Subtype.coe_mk]
        rw [pmul_assoc]
        rfl
      · have hcalc : e (d * R * d⁻¹) = e d * e R * (e d)⁻¹ := by
          rw [MulEquiv.map_mul e (d * R) d⁻¹, MulEquiv.map_mul e d R, MulEquiv.map_inv e d]
        have hd : e d = g := hδ₀
        have hR : e R = FreeGroup.mk (roseWord (rosePath L)) := he (rosePath L) hred
        change e (d * R * d⁻¹) = g * r * g⁻¹
        rw [hcalc]
        simp only [hd, hR, roseWord_rosePath, hr]
  rw [hmap, hset, normalClosure_conjugateSet_eq r]

/-- The one-relator group `⟨α | r⟩`, with `r` cyclically reduced, non-trivial and not a proper
power, is the vertex group of a `CodeSeparates` groupoid presentation on the rose `Rose α`.  The
single relator is `rosePath (FreeGroup.toWord r)`; the graph has one vertex and one loop per
generator, so `P.ι ≃ PUnit` and `staggered` is vacuous.  The isomorphism is the one induced by
`FreeGroup.mk` on reduced words.

Please BUILD THE DICTIONARY in this file (it is the reusable content):
  * `rosePath` is injective on reduced words, `roseWord` on reduced paths, and
    `DeleteBacktrack p q ↔ FreeGroup.Red (roseWord p) (roseWord q)`-style correspondence;
  * hence `(rosePath L).IsReduced ↔ FreeGroup.IsReduced L`;
  * `IsCyclicallyReduced (rosePath L) ↔ FreeGroup.IsCyclicallyReduced L` (note `P.noSelfLoop` holds
    because `Bool.not_not`), and `IsProperPower (rosePath L)` for `List`-words is
    `∃ L' m, 2 ≤ m ∧ L = (List.replicate m L').flatten`;
  * the group isomorphism `VertexGroup (roseVtx α) ≃* FreeGroup α` via `roseWord`/`FreeGroup.mk`,
    and `PresentedGroup ({r} : Set (FreeGroup α))` identified with the vertex group of the
    presentation at `roseVtx α`.
The definitions `Rose`, `roseVtx`, `roseQuiver`, `roseReverse`, `roseTotal`, `rosePath`, `roseWord`
and their basic API are in `Submission.Work.ORLocInd.Howie.RoseBasic` (import it; do not redefine
them, and use `roseVtx α`, never `PUnit.unit`, for the vertex). -/
theorem onePresentation_exists {α : Type u} [LinearOrder α] (r : FreeGroup α)
    (hr : Work.OROneRel.IsCyclicallyReducedRelator r) (hr1 : r ≠ 1)
    (hpp : ¬ Work.OROneRel.IsProperPower r) :
    ∃ P : Work.ORLocInd.Howie.Presentation (Work.ORLocInd.Howie.Rose α),
      P.CodeSeparates ∧
      Nonempty (P.vertexGroup (Work.ORLocInd.Howie.roseVtx α) ≃*
        PresentedGroup ({r} : Set (FreeGroup α))) := by
  have hcyc : FreeGroup.IsCyclicallyReduced (@FreeGroup.toWord α (Classical.decEq α) r) := by
    have h1 := hr
    unfold Work.OROneRel.IsCyclicallyReducedRelator at h1
    exact h1
  have hred : FreeGroup.IsReduced (@FreeGroup.toWord α (Classical.decEq α) r) := hcyc.1
  have hmk : FreeGroup.mk (@FreeGroup.toWord α (Classical.decEq α) r) = r :=
    @FreeGroup.mk_toWord α (Classical.decEq α) r
  have hppL : ¬ (∃ (L' : List (α × Bool)) (m : ℕ), 2 ≤ m ∧
      @FreeGroup.toWord α (Classical.decEq α) r = (List.replicate m L').flatten) := by
    rintro ⟨L', m, hm, hL⟩
    refine hpp ⟨FreeGroup.mk L', m, hm, ?_⟩
    rw [← hmk, hL, FreeGroup.pow_mk]
  have hpathred : (rosePath (@FreeGroup.toWord α (Classical.decEq α) r)).IsReduced :=
    (isReduced_rosePath_iff' _).2 hred
  have hpathcyc : IsCyclicallyReduced (rosePath (@FreeGroup.toWord α (Classical.decEq α) r)) :=
    isCyclicallyReduced_rosePath' hcyc
  have hpathpp : ¬ IsProperPower (rosePath (@FreeGroup.toWord α (Classical.decEq α) r)) :=
    fun h => hppL ((isProperPower_rosePath_iff' _).1 h)
  refine ⟨rosePresentation _ hpathred hpathcyc hpathpp,
    rosePresentation_codeSeparates _ hpathred hpathcyc hpathpp, ?_⟩
  obtain ⟨e, he⟩ := vertexGroup_rose_equiv' (α := α)
  exact ⟨QuotientGroup.congr _ _ e
    (map_relatorNormalClosure_eq _ hpathred hpathcyc hpathpp r hmk e he)⟩

end Work.ORLocInd.Howie
