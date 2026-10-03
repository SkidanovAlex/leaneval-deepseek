import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.RepProjection

set_option linter.unusedSectionVars false

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre

universe u

/-!
# A chain of vertex-group letters has a non-trivial product

Let `G` act on a tree `V` (without inversions) and let `d : TreeDatum G V` be a spanning tree
datum of the action, with vertex groups `d.vgroup A = Stab_G (d.vert A)`.  The hypothesis `hG` is
the *trap* (ping-pong) property: a non-trivial element of `d.vgroup A` moves every vertex whose
nearest representative is not `d.vert A` into the "trap" `{v | nearestRep v = d.vert A}`.

The main result is that a product of non-trivial letters `h₁ ⋯ hₙ` with `hⱼ ∈ d.vgroup Aⱼ`, whose
consecutive orbits are distinct, is never trivial (`list_prod_ne_one`).

The proof is the ping-pong (normal form) argument.  Its heart is the propagation lemma
`aux_chain_prop`: for a chain `l = [(A₁,h₁), …, (Aₙ,hₙ)]` with all `hⱼ ≠ 1` and head `x₀`,

* the product `w = h₁ ⋯ hₙ` maps any vertex `y` whose nearest representative differs from that of
  the last element of `l` into the trap of the head orbit, and
* `w` maps *every* representative `d.vert C` into the trap of the head orbit.

The propagation is read from right to left: the last letter sends `y` into the trap of its orbit (by
`hG`, or because it fixes `d.vert Aₙ` when `y = d.vert Aₙ`), and then each letter sends the trap of
its successor's orbit into its own trap, because consecutive orbits of a chain differ.  The second
part of the statement is needed because it applies to points lying inside a trap.

Finally, `l = [(A₁,h₁),…,(Aₙ,hₙ)]` with `n ≥ 2` and trivial product would send the representative
`d.vert A₂` into the trap of `A₁`, forcing `A₁ = A₂` and contradicting the chain condition.
-/

variable {G : Type u} {V : Type u} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-- A chosen representative of a vertex orbit is its own nearest representative. -/
private theorem aux_nearestRep_vert {hT : Work.ORBassSerre.IsTree V}
    (d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V) (A : Work.ORBassSerre.orbitV G V) :
    Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d (d.vert A) = d.vert A := by
  have h := Work.ORLocInd.FKSKernel.Kurosh.nearestRep_le hT d (d.vert A) A
  simp only [Work.ORLocInd.FKSKernel.Kurosh.dist_self] at h
  exact ((Work.ORLocInd.FKSKernel.Kurosh.dist_eq_zero_iff hT).mp (Nat.eq_zero_of_le_zero h)).symm

/-- Distinct vertex orbits have distinct representatives. -/
private theorem aux_vert_injective (d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V) :
    Function.Injective d.vert := by
  intro A B h
  rw [← d.vert_mk A, ← d.vert_mk B, h]

/-- An element of a vertex group fixes the representative of its orbit. -/
private theorem aux_smul_vert_self (d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V)
    (x : Σ A : Work.ORBassSerre.orbitV G V, ↥(d.vgroup A)) :
    (x.2 : G) • d.vert x.1 = d.vert x.1 :=
  MulAction.mem_stabilizer_iff.mp x.2.2

/-- The last entry of `t ++ [x]` is `x`. -/
private theorem aux_getLast?_concat {α : Type u} (t : List α) (x : α) :
    (t ++ [x]).getLast? = some x := by
  rw [List.getLast?_eq_getLast_of_ne_nil (by simp : t ++ [x] ≠ [])]
  exact congrArg some (List.getLast_append_singleton t)

/-- The product of `l ++ [x]` acts by first applying the last letter `x`. -/
private theorem aux_prod_concat_smul {d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V}
    (l : List (Σ A : Work.ORBassSerre.orbitV G V, ↥(d.vgroup A)))
    (x : Σ A : Work.ORBassSerre.orbitV G V, ↥(d.vgroup A)) (y : V) :
    ((List.map (fun z => (z.2 : G)) (l ++ [x])).prod) • y
      = ((List.map (fun z => (z.2 : G)) l).prod) • ((x.2 : G) • y) := by
  rw [List.map_append, List.prod_append, mul_smul]
  simp

/-- The junction condition of a chain: in `t ++ [x]` the last element of `t` is related to `x`. -/
private theorem aux_rel_of_getLast?_concat {α : Type u} {R : α → α → Prop} {t : List α}
    {x z : α} (hchain : List.IsChain R (t ++ [x])) (hz : t.getLast? = some z) : R z x :=
  (List.isChain_append.mp hchain).2.2 z (by simp [hz]) x (by simp)

/-- **Propagation of the ping-pong traps.**  Let `l` be a `List.IsChain` of pairs `(A, h)` with
`h ∈ d.vgroup A` and `h ≠ 1`, with head `x₀`.  Then the product of the letters of `l` maps every
vertex `y` whose nearest representative differs from that of the last element of `l` into the trap
of the head orbit, and it maps every representative into that trap. -/
private theorem aux_chain_prop (hT : Work.ORBassSerre.IsTree V)
    (d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V)
    (hG : ∀ (A : Work.ORBassSerre.orbitV G V) (h : ↥(d.vgroup A)), (h : G) ≠ 1 → ∀ v : V,
      Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d v ≠ d.vert A →
      Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d ((h : G) • v) = d.vert A) :
    ∀ (l : List (Σ A : Work.ORBassSerre.orbitV G V, ↥(d.vgroup A))),
      (∀ x ∈ l, (x.2 : G) ≠ 1) →
      List.IsChain (fun x y : Σ A : Work.ORBassSerre.orbitV G V, ↥(d.vgroup A) =>
        x.1 ≠ y.1) l →
      ∀ (x₀ : Σ A : Work.ORBassSerre.orbitV G V, ↥(d.vgroup A)), l.head? = some x₀ →
      (∀ y : V, (∀ z, l.getLast? = some z →
          Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d y ≠ d.vert z.1) →
        Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d
          ((List.map (fun x => (x.2 : G)) l).prod • y) = d.vert x₀.1) ∧
      (∀ C : Work.ORBassSerre.orbitV G V,
        Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d
          ((List.map (fun x => (x.2 : G)) l).prod • d.vert C) = d.vert x₀.1) := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro hne hchain x₀ hhead
    exact absurd hhead (by simp)
  | append_singleton t x ih =>
    intro hne hchain x₀ hhead
    have hlast : (t ++ [x]).getLast? = some x := aux_getLast?_concat t x
    cases t with
    | nil =>
      -- the list is `[x]`, so its head `x₀` is `x`
      have hx₀ : x = x₀ := by simpa using hhead
      rw [← hx₀]
      refine ⟨?_, ?_⟩
      · intro y hy
        simpa using hG x.1 x.2 (hne x (by simp)) y (hy x hlast)
      · intro C
        by_cases hC : C = x.1
        · subst hC
          simp only [aux_smul_vert_self d x, aux_nearestRep_vert, List.map_cons, List.map_nil,
            List.prod_cons, List.prod_nil, mul_one, List.nil_append]
        · simpa using hG x.1 x.2 (hne x (by simp)) (d.vert C) (by
            rw [aux_nearestRep_vert]
            exact fun hcon => hC (aux_vert_injective d hcon))
    | cons z t' =>
      have hx₀ : x₀ = z := (by simpa using hhead : z = x₀).symm
      rw [hx₀]
      have htne : ∀ y ∈ z :: t', (y.2 : G) ≠ 1 := fun y hy =>
        hne y (List.mem_append_left [x] hy)
      have htchain : List.IsChain (fun a b : Σ A : Work.ORBassSerre.orbitV G V,
          ↥(d.vgroup A) => a.1 ≠ b.1) (z :: t') := hchain.left_of_append
      have hIH := ih htne htchain z rfl
      have hjun : ∀ z', (z :: t').getLast? = some z' → x.1 ≠ z'.1 := fun z' hz' =>
        Ne.symm (aux_rel_of_getLast?_concat
          (R := fun a b : Σ A : Work.ORBassSerre.orbitV G V, ↥(d.vgroup A) => a.1 ≠ b.1)
          hchain hz')
      refine ⟨?_, ?_⟩
      · intro y hy
        have hstep : Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d ((x.2 : G) • y) =
            d.vert x.1 := hG x.1 x.2 (hne x (by simp)) y (hy x hlast)
        have hy' : ∀ z', (z :: t').getLast? = some z' →
            Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d ((x.2 : G) • y) ≠ d.vert z'.1 := by
          intro z' hz'
          rw [hstep]
          exact fun hcon => hjun z' hz' (aux_vert_injective d hcon)
        rw [aux_prod_concat_smul (z :: t') x y]
        exact hIH.1 ((x.2 : G) • y) hy'
      · intro C
        have hstep : Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d ((x.2 : G) • d.vert C) =
            d.vert x.1 := by
          by_cases hC : C = x.1
          · subst hC
            simp only [aux_smul_vert_self d x, aux_nearestRep_vert]
          · exact hG x.1 x.2 (hne x (by simp)) (d.vert C) (by
              rw [aux_nearestRep_vert]
              exact fun hcon => hC (aux_vert_injective d hcon))
        have hy' : ∀ z', (z :: t').getLast? = some z' →
            Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d ((x.2 : G) • d.vert C) ≠
              d.vert z'.1 := by
          intro z' hz'
          rw [hstep]
          exact fun hcon => hjun z' hz' (aux_vert_injective d hcon)
        rw [aux_prod_concat_smul (z :: t') x (d.vert C)]
        exact hIH.1 ((x.2 : G) • d.vert C) hy'

theorem list_prod_ne_one {G : Type u} {V : Type u} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V) (d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V)
    (hG : ∀ (A : Work.ORBassSerre.orbitV G V) (h : ↥(d.vgroup A)), (h : G) ≠ 1 → ∀ v : V,
      Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d v ≠ d.vert A →
      Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d ((h : G) • v) = d.vert A)
    (l : List (Σ A : Work.ORBassSerre.orbitV G V, ↥(d.vgroup A)))
    (hne : ∀ x ∈ l, (x.2 : G) ≠ 1)
    (hchain : List.IsChain (fun x y : Σ A : Work.ORBassSerre.orbitV G V, ↥(d.vgroup A) =>
      x.1 ≠ y.1) l) :
    (l.map (fun x => (x.2 : G))).prod = 1 → l = [] := by
  intro hprod
  rcases l with _ | ⟨x₀, t⟩
  · rfl
  rcases t with _ | ⟨x₁, rest⟩
  · exfalso
    have hx : (x₀.2 : G) = 1 := by simpa using hprod
    exact hne x₀ (by simp) hx
  · exfalso
    have hhead : (x₀ :: x₁ :: rest).head? = some x₀ := rfl
    have hconj :=
      (aux_chain_prop hT d hG (x₀ :: x₁ :: rest) hne hchain x₀ hhead).2 x₁.1
    rw [hprod, one_smul, aux_nearestRep_vert] at hconj
    have h01 : x₀.1 ≠ x₁.1 :=
      (by simpa only [List.isChain_cons_cons] using hchain : x₀.1 ≠ x₁.1 ∧
        List.IsChain (fun x y : Σ A : Work.ORBassSerre.orbitV G V, ↥(d.vgroup A) =>
          x.1 ≠ y.1) (x₁ :: rest)).1
    exact h01 (aux_vert_injective d hconj).symm

end Work.ORLocInd.FKSKernel.Kurosh
