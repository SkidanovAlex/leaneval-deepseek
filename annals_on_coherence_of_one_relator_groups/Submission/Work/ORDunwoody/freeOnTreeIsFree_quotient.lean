import Mathlib
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORBassSerre.Assembly.freeOnTreeIsFree_of_noInversions
import Submission.Work.ORBassSerre.Action.QuotientGroupOrbitV
import Submission.Work.ORBassSerre.QuotientTree.stabilizer_quotient_mk
import Submission.Work.ORBassSerre.QuotientTree.orbitQuiver_nonempty_hom_iff

set_option autoImplicit false

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace Work.ORDunwoody

open Work.ORBassSerre

section QuotientGraphAction

variable {G : Type u} {V : Type u} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [GraphAction G V]

/-- The action of `G ⧸ N` on the orbits of arrows of `V ⧸ N` commutes with reversal of arrows. -/
theorem quotient_smul_orbitEReverse (N : Subgroup G) [N.Normal] (q : G ⧸ N)
    (E : orbitE N V) : q • orbitEReverse E = orbitEReverse (q • E) := by
  induction E using Quotient.inductionOn with
  | h e =>
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [orbitEReverse_mk, quotient_smul_mk, GraphAction.smul_reverse_apply,
      ← orbitEReverse_mk, ← quotient_smul_mk]

/-- The labelling of an arrow of the quotient graph by a class of arrows of `V`. -/
theorem orbitReverse_val (N : Subgroup G) [N.Normal] {A B : orbitV N V} (E : A ⟶ B) :
    (Quiver.reverse E).1 = orbitEReverse E.1 := rfl

/-- Two `Quiver.Total`s of the quotient graph with propositionally equal endpoints and equal
arrow labels are equal. -/
theorem total_ext_quotient (N : Subgroup G) [N.Normal] {a a' b b' : orbitV N V}
    (ha : a = a') (hb : b = b') (f : a ⟶ b) (f' : a' ⟶ b') (hl : f.1 = f'.1) :
    Quiver.Total.mk a b f = Quiver.Total.mk a' b' f' := by
  subst ha
  subst hb
  exact congrArg (Quiver.Total.mk a b) (Subtype.ext hl)

/-- The action of `G ⧸ N` on the total space of the quotient graph `V ⧸ N`. -/
noncomputable def quotientTotalSmul (N : Subgroup G) [N.Normal] (q : G ⧸ N)
    (t : Quiver.Total (orbitV N V)) : Quiver.Total (orbitV N V) :=
  Quiver.Total.mk (q • t.left) (q • t.right) ⟨q • t.hom.1, by
    obtain ⟨e, he, hl, hr⟩ := t.hom.2
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N q
    refine ⟨g • e, ?_, ?_, ?_⟩
    · rw [← hg, ← quotient_smul_mk, he]
    · have h2 : (g • e).left = g • e.left := GraphAction.smul_left g e
      rw [h2, ← hg, ← quotient_smul_mk, hl]
    · have h3 : (g • e).right = g • e.right := GraphAction.smul_right g e
      rw [h3, ← hg, ← quotient_smul_mk, hr]⟩

@[simp] theorem quotientTotalSmul_left (N : Subgroup G) [N.Normal] (q : G ⧸ N)
    (t : Quiver.Total (orbitV N V)) : (quotientTotalSmul N q t).left = q • t.left := rfl

@[simp] theorem quotientTotalSmul_right (N : Subgroup G) [N.Normal] (q : G ⧸ N)
    (t : Quiver.Total (orbitV N V)) : (quotientTotalSmul N q t).right = q • t.right := rfl

@[simp] theorem quotientTotalSmul_hom (N : Subgroup G) [N.Normal] (q : G ⧸ N)
    (t : Quiver.Total (orbitV N V)) : (quotientTotalSmul N q t).hom.1 = q • t.hom.1 := rfl

theorem quotientTotalSmul_one (N : Subgroup G) [N.Normal] (t : Quiver.Total (orbitV N V)) :
    quotientTotalSmul N 1 t = t := by
  obtain ⟨l, r, f⟩ := t
  refine total_ext_quotient N (one_smul (G ⧸ N) l) (one_smul (G ⧸ N) r) _ _
    (one_smul (G ⧸ N) f.1)

theorem quotientTotalSmul_mul (N : Subgroup G) [N.Normal] (q p : G ⧸ N)
    (t : Quiver.Total (orbitV N V)) :
    quotientTotalSmul N (q * p) t = quotientTotalSmul N q (quotientTotalSmul N p t) := by
  obtain ⟨l, r, f⟩ := t
  refine total_ext_quotient N (mul_smul q p l) (mul_smul q p r) _ _ (mul_smul q p f.1)

theorem quotientTotalSmul_reverse (N : Subgroup G) [N.Normal] (q : G ⧸ N)
    (t : Quiver.Total (orbitV N V)) :
    quotientTotalSmul N q t.reverse = (quotientTotalSmul N q t).reverse := by
  obtain ⟨l, r, f⟩ := t
  refine total_ext_quotient N rfl rfl _ _ ?_
  exact quotient_smul_orbitEReverse (G := G) (V := V) N q f.1

/-- The action of the quotient group `G ⧸ N` on the quotient graph `V ⧸ N` of a `G`-graph. -/
noncomputable instance instGraphActionQuotientOrbit (N : Subgroup G) [N.Normal] :
    GraphAction (G ⧸ N) (orbitV N V) where
  smulTotal := quotientTotalSmul N
  smulTotal_one := quotientTotalSmul_one N
  smulTotal_mul := quotientTotalSmul_mul N
  smul_left := fun _ _ => rfl
  smul_right := fun _ _ => rfl
  smul_reverse := quotientTotalSmul_reverse N

@[simp] theorem graphActionQuotient_smulTotal (N : Subgroup G) [N.Normal] (q : G ⧸ N)
    (t : Quiver.Total (orbitV N V)) :
    GraphAction.smulTotal q t = quotientTotalSmul N q t := rfl

end QuotientGraphAction

section QuotientActionProperties

variable {G : Type u} {V : Type u} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [GraphAction G V]

/-- If `G` acts on `V` without inversions, then so does `G ⧸ N` on the quotient graph `V ⧸ N`. -/
theorem quotient_actsWithoutInversions (h : ActsWithoutInversions G V) (N : Subgroup G) [N.Normal] :
    ActsWithoutInversions (G ⧸ N) (orbitV N V) := by
  intro q e he
  obtain ⟨l, r, f⟩ := e
  obtain ⟨e₀, he₀, -, -⟩ := f.2
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N q
  have h1 : (GraphAction.smulTotal q (Quiver.Total.mk l r f)).hom.1
      = (Quiver.Total.mk l r f).reverse.hom.1 := by rw [he]
  rw [graphActionQuotient_smulTotal, quotientTotalSmul_hom, Quiver.Total.reverse_mk,
    orbitReverse_val] at h1
  rw [← he₀, orbitEReverse_mk, ← hg, quotient_smul_mk] at h1
  have hrel : MulAction.orbitRel ↥N (Quiver.Total V) e₀.reverse (g • e₀) :=
    Quotient.exact h1.symm
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨k, hk⟩ := hrel
  have hk' : ((k : G) * g) • e₀ = e₀.reverse := by
    rw [Subgroup.smul_def, ← mul_smul] at hk
    exact hk
  exact h ((k : G) * g) e₀ hk'

/-- If every vertex stabilizer of the `G`-action on `V` lies in the normal subgroup `N`, then
`G ⧸ N` acts freely on the quotient graph `V ⧸ N`. -/
theorem quotient_actsFreely (N : Subgroup G) [N.Normal]
    (hN : ∀ v : V, MulAction.stabilizer G v ≤ N) : ActsFreely (G ⧸ N) (orbitV N V) := by
  rw [actsFreely_iff_stabilizer_bot]
  intro x
  obtain ⟨v, rfl⟩ := Quotient.exists_rep x
  rw [Work.ORBassSerre.QuotientTree.stabilizer_quotient_mk]
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact hN v

end QuotientActionProperties

/-- **`Work.ORDunwoody.FreeOnTreeIsFree`, `quotient` conjunct.**

Let `G` act on a simplicial tree `S` without inverting any edge, and let `K` be the normal closure
of the vertex stabilizers.  Then `G ⧸ K` is a free group.

Proof: `K` is the normal closure of the set of elements of `G` which fix a vertex, so the quotient
graph `S ⧸ K` of the tree `S` by the subgroup `K` is again a tree (JL Lemma 4.1 /
`isTree_orbitV_of_normalClosure_elliptic`).  The quotient group `G ⧸ K` acts on `S ⧸ K`; the
vertex stabilizers of this action are the images of the vertex stabilizers of `S` in `G ⧸ K`,
which are trivial because those subgroups lie in `K`, so the action is free; and it has no
inversions, because an inversion in the quotient lifts to an inversion of an edge of `S` by an
element of `G`.  Hence `G ⧸ K` is free by `isFreeGroup_of_actsFreely_on_tree`. -/
theorem freeOnTreeIsFree_quotient (Y : Type u) :
    (∀ (G : Type u) [Group G] {V : Type u} [MulAction G V] (S : Work.ORDunwoody.GTree G V)
      (K : Subgroup G) [K.Normal],
      (∀ (g : G) ⦃u v : V⦄, S.Adj u v → g • u = v → g • v = u → g = 1) →
      (K = Subgroup.normalClosure (⋃ v : V, (S.vertexStab v : Set G))) →
      ∃ (α : Type u), Nonempty ((G ⧸ K) ≃* FreeGroup α)) := by
  intro G instG V instV S K instKN hninv hK
  obtain ⟨Q, hR, hA, htree, hadj, -⟩ := Work.ORDunwoody.Lemmas.ofGTree_quiverTree S
  letI : Quiver V := Q
  letI : Quiver.HasInvolutiveReverse V := hR
  letI : Work.ORBassSerre.GraphAction G V := hA
  haveI : Nonempty V := S.isTree.connected.nonempty
  -- The no-inversion hypothesis, in the form used by the Bass--Serre machinery.
  have hninvG : Work.ORBassSerre.ActsWithoutInversions G V := by
    rintro g ⟨a, b, φ⟩ he
    have hab : S.Adj a b := (hadj a b).mp ⟨φ⟩
    have hleft : g • a = b := by
      have h := congrArg Quiver.Total.left he
      simpa only [Work.ORBassSerre.GraphAction.smul_left, Quiver.Total.reverse_left] using h
    have hright : g • b = a := by
      have h := congrArg Quiver.Total.right he
      simpa only [Work.ORBassSerre.GraphAction.smul_right, Quiver.Total.reverse_right] using h
    have hg : g = 1 := hninv g hab hleft hright
    have hba : b = a := by rw [← hleft, hg, one_smul]
    exact (S.adj_self a) (hba ▸ hab)
  -- The vertex stabilizers of `S` lie in `K`.
  have hKle : ∀ v : V, MulAction.stabilizer G v ≤ K := by
    intro v x hx
    rw [hK]
    exact Subgroup.subset_normalClosure
      (Set.subset_iUnion (fun i : V => (S.vertexStab i : Set G)) v hx)
  -- `K` is the normal closure of the vertex-fixing elements, so `S ⧸ K` is a tree.
  have htreeK : Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV ↥K V) :=
    Work.ORBassSerre.Action.isTree_orbitV_of_normalClosure_elliptic (G := G) (V := V) htree K
      (⋃ v : V, (S.vertexStab v : Set G))
      (fun g hg => by
        rw [Set.mem_iUnion] at hg
        obtain ⟨v, hv⟩ := hg
        exact ⟨v, MulAction.mem_stabilizer_iff.mp hv⟩)
      hK.symm
  haveI : Nonempty (Work.ORBassSerre.orbitV ↥K V) := ⟨Quotient.mk'' (Classical.arbitrary V)⟩
  have hfree : Work.ORBassSerre.ActsFreely (G ⧸ K) (Work.ORBassSerre.orbitV ↥K V) :=
    quotient_actsFreely (G := G) (V := V) K hKle
  have hninvQ : Work.ORBassSerre.ActsWithoutInversions (G ⧸ K)
      (Work.ORBassSerre.orbitV ↥K V) :=
    quotient_actsWithoutInversions (G := G) (V := V) hninvG K
  haveI : IsFreeGroup (G ⧸ K) :=
    Work.ORBassSerre.Action.isFreeGroup_of_actsFreely_on_tree htreeK hfree hninvQ
  exact ⟨IsFreeGroup.Generators (G ⧸ K), ⟨IsFreeGroup.toFreeGroup (G ⧸ K)⟩⟩

end Work.ORDunwoody
