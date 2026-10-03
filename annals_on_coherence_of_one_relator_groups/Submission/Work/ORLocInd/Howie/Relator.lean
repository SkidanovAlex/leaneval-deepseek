/-
# Relators of a groupoid presentation `⟨Γ | R⟩` (Howie 2000)

Vocabulary for Howie's Theorem 3.1: a *groupoid presentation* of a graph `Γ` (a quiver with an
involutive reversal of arrows) consists of a set `R` of *cyclically reduced* closed paths in `Γ`
which are *staggered* and none of which is a *proper power*.

The present file collects the purely combinatorial notions used by the proof:

* `Quiver.totalReverse`, the reverse of an arrow as an element of `Quiver.Total V`;
* `Quiver.Path.arrowList` : the arrows of a path, in order;
* `Work.ORLocInd.Howie.pathMax`, `pathMin` : the greatest and least *unoriented edge* occurring in
  a path, relative to a "code" `ω : Quiver.Total V → α` which is constant on `{e, e⁻¹}` and takes
  values in a linear order.  Howie's staggered condition is stated in these terms (an *edge* of the
  graph is an unordered pair `{e, e⁻¹}`; this is what makes the Tietze step of Case 2 of his proof
  work, and it is also compatible with the ordering of the cyclic cover);
* `Work.ORLocInd.Howie.edgeCount` : the number of occurrences of an unoriented edge in a path;
* `CompPower`, `IsCyclicallyReduced`, `IsProperPower` : the closed-path notions;
* `Presentation` : the data of a staggered presentation without proper powers.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Quiver

/-- The reverse of an arrow, as an element of `Quiver.Total V`. -/
def totalReverse {V : Type u} [Quiver V] [Quiver.HasReverse V] (e : Quiver.Total V) : Quiver.Total V :=
  Quiver.Total.mk e.right e.left (Quiver.reverse e.hom)

@[simp] theorem totalReverse_mk {V : Type u} [Quiver V] [Quiver.HasReverse V] {a b : V}
    (e : a ⟶ b) :
    totalReverse (Quiver.Total.mk a b e) = Quiver.Total.mk b a (Quiver.reverse e) := rfl

@[simp] theorem totalReverse_involutive {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (e : Quiver.Total V) : totalReverse (totalReverse e) = e := by
  cases e with
  | mk a b f => simp [totalReverse]

theorem totalReverse_injective {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] :
    Function.Injective (@totalReverse V _ _) := fun a b h => by
  have h' := congrArg totalReverse h
  simpa using h'

@[simp] theorem totalReverse_left {V : Type u} [Quiver V] [Quiver.HasReverse V]
    (e : Quiver.Total V) : (totalReverse e).left = e.right := rfl

@[simp] theorem totalReverse_right {V : Type u} [Quiver V] [Quiver.HasReverse V]
    (e : Quiver.Total V) : (totalReverse e).right = e.left := rfl

@[simp] theorem totalReverse_hom {V : Type u} [Quiver V] [Quiver.HasReverse V]
    (e : Quiver.Total V) : (totalReverse e).hom = Quiver.reverse e.hom := rfl

end Quiver

namespace Quiver.Path

variable {V : Type u} [Quiver V]
variable {a b c : V}

/-- The arrows of a path, in order (from the first to the last). -/
def arrowList : ∀ {b : V}, Path a b → List (Quiver.Total V)
  | _, nil => []
  | _, cons p e => arrowList p ++ [Quiver.Total.mk _ _ e]

@[simp] theorem arrowList_nil : (nil : Path a a).arrowList = [] := rfl

theorem arrowList_cons (p : Path a b) (e : b ⟶ c) :
    (p.cons e).arrowList = p.arrowList ++ [Quiver.Total.mk b c e] := rfl

theorem arrowList_length_eq (p : Path a b) : p.arrowList.length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [arrowList_cons, ih]

/-- The `m`-fold concatenation of a closed path with itself. -/
def compPower {v : V} (q : Path v v) : ℕ → Path v v
  | 0 => nil
  | n + 1 => q.comp (compPower q n)

@[simp] theorem compPower_zero {v : V} (q : Path v v) : compPower q 0 = nil := rfl

theorem compPower_succ {v : V} (q : Path v v) (n : ℕ) :
    compPower q (n + 1) = q.comp (compPower q n) := rfl

theorem compPower_length {v : V} (q : Path v v) (n : ℕ) :
    (compPower q n).length = n * q.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [compPower_succ, length_comp, ih]; ring

end Quiver.Path

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## The edge order (unoriented edges) -/

section EdgeOrder

variable {α : Type u} [LinearOrder α]

/-- The greatest element of a path's arrow list, coded as an unoriented edge. -/
def pathMax (ω : Quiver.Total V → α) {a b : V} (p : Quiver.Path a b) : WithBot α :=
  (p.arrowList.map (fun e => (ω e : WithBot α))).foldr max ⊥

/-- The least element of a path's arrow list, coded as an unoriented edge. -/
def pathMin (ω : Quiver.Total V → α) {a b : V} (p : Quiver.Path a b) : WithTop α :=
  (p.arrowList.map (fun e => (ω e : WithTop α))).foldr min ⊤

/-- The number of arrows of `p` whose code is the code of `e`.

**Warning.** This is *not* the number of occurrences of the unoriented edge `{e, e⁻¹}`: the code `ω`
need not separate the unoriented edges of `Γ` (this is the hypothesis `Presentation.CodeSeparates`),
and when it does not, the count through `ω` overcounts.  Counterexample: a theta graph (two vertices
`u`, `w`, two parallel edges) with the *constant* code and the relator `ab0 · ba1`: see
`Submission/Work/ORLocInd/Howie/case2_cex.lean`.  Howie's Case 2 must therefore carry
`Presentation.CodeSeparates` as a hypothesis. -/
def edgeCount (ω : Quiver.Total V → α) {a b : V} (p : Quiver.Path a b) (e : Quiver.Total V) : ℕ :=
  (p.arrowList.filter (fun f => ω f = ω e)).length

end EdgeOrder

/-! ## The closed-path notions -/

/-- A closed path is *cyclically reduced* if its first and last arrows are not mutually inverse,
i.e. no backtrack is created by reading the path cyclically. -/
def IsCyclicallyReduced {v : V} (p : Quiver.Path v v) : Prop :=
  ¬ ∃ (u : V) (e : v ⟶ u) (q : Quiver.Path u u),
      p = e.toPath.comp (q.cons (Quiver.reverse e))

/-- A closed path is a *proper power* if it is a repetition of a closed path two or more times. -/
def IsProperPower {v : V} (p : Quiver.Path v v) : Prop :=
  ∃ (q : Quiver.Path v v) (m : ℕ), 2 ≤ m ∧ p = Quiver.Path.compPower q m

/-! ## Groupoid presentations -/

/-- A *groupoid presentation* `⟨Γ | R⟩` whose relator set is **staggered** and has no proper
powers, in the form in which Howie's Theorem 3.1 is stated.

The linear order on the relators and the "code" `ω` of unoriented edges make the relators
simultaneously ordered: the greatest edge of a smaller relator is smaller than the greatest edge of
a larger one, and likewise for the least edges. -/
structure Presentation (V : Type u) [Quiver V] [Quiver.HasInvolutiveReverse V] where
  /-- the type of unoriented edges, as a linearly ordered code -/
  α : Type u
  /-- the order on unoriented edges -/
  [linearOrder : LinearOrder α]
  /-- the unoriented edge of an arrow -/
  edgeOf : Quiver.Total V → α
  /-- the code is constant on `{e, e⁻¹}` -/
  edgeOf_reverse : ∀ e : Quiver.Total V, edgeOf (Quiver.totalReverse e) = edgeOf e
  /-- the reversal is fixed-point-free: no arrow is its own inverse.
  (Howie's graphs have a fixed-point-free involution.  Without this hypothesis the notion of a
  cyclically reduced closed path is degenerate: a self-inverse loop `e = e⁻¹` is "cyclically
  reduced" for the definition below and `compPower e 2` is not reduced.) -/
  noSelfLoop : ∀ (v : V) (e : v ⟶ v), Quiver.reverse e ≠ e
  /-- the type of relators.  No finiteness is required here: the *cyclic cover* of a presentation
  (Howie's Case 1) has relators indexed by `ι × ℤ`, so it is infinite, and the span of a datum
  inside it is what is used in the induction.  Finiteness of `ι` is a hypothesis of Case 2
  (`case2`), where the inner induction on the number of relators takes place; it is supplied there
  by the span hypothesis. -/
  ι : Type u
  /-- the order on relators -/
  [linearOrder_ι : LinearOrder ι]
  /-- the base vertex of a relator -/
  base : ι → V
  /-- the closed path of a relator -/
  path : (i : ι) → Quiver.Path (base i) (base i)
  /-- relators are reduced -/
  reduced : ∀ i, (path i).IsReduced
  /-- relators are cyclically reduced -/
  cyclicallyReduced : ∀ i, IsCyclicallyReduced (path i)
  /-- no relator is a proper power -/
  notProperPower : ∀ i, ¬ IsProperPower (path i)
  /-- the staggered condition -/
  staggered : ∀ i j : ι, i < j →
    pathMax edgeOf (path i) < pathMax edgeOf (path j) ∧
      pathMin edgeOf (path i) < pathMin edgeOf (path j)

namespace Presentation

attribute [instance] Presentation.linearOrder Presentation.linearOrder_ι

variable (P : Presentation V)

/-- The relator of index `i`, as an element of the vertex group at its base vertex. -/
noncomputable def relatorLoop (i : P.ι) : VertexGroup (P.base i) := ⟨P.path i, P.reduced i⟩

/-- The set of conjugates (into the vertex group at `v`) of the relators of `P`. -/
noncomputable def relatorSet (v : V) : Set (VertexGroup v) :=
  {x | ∃ (i : P.ι) (δ : Quiver.Path v (P.base i)), δ.IsReduced ∧
        x = ⟨pmul δ (pmul (P.path i) δ.reverse), pmul_isReduced _ _⟩}

/-- The normal closure, inside the vertex group at `v` of the free groupoid, of the conjugates of
the relators: the kernel of the projection to the vertex group of `⟨Γ | R⟩` at `v`. -/
noncomputable def relatorNormalClosure (v : V) : Subgroup (VertexGroup v) :=
  Subgroup.normalClosure (P.relatorSet v)

instance relatorNormalClosure_normal (v : V) : (P.relatorNormalClosure v).Normal :=
  Subgroup.normalClosure_normal

/-- The *vertex group of the presented groupoid* `⟨Γ | R⟩` at `v`. -/
noncomputable def vertexGroup (v : V) : Type u := VertexGroup v ⧸ P.relatorNormalClosure v

noncomputable instance (v : V) : Group (P.vertexGroup v) :=
  QuotientGroup.Quotient.group (P.relatorNormalClosure v)

/-- The projection `F(Γ)_v → π₁(⟨Γ | R⟩, v)`. -/
noncomputable def toVertexGroup (v : V) : VertexGroup v →* P.vertexGroup v :=
  QuotientGroup.mk' (P.relatorNormalClosure v)

theorem toVertexGroup_apply (v : V) (x : VertexGroup v) :
    P.toVertexGroup v x = QuotientGroup.mk x :=
  QuotientGroup.mk'_apply (N := P.relatorNormalClosure v) x

end Presentation

end Work.ORLocInd.Howie
