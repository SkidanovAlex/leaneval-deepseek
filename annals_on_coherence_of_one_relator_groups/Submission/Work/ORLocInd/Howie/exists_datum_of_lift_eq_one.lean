/-
# The existence of a datum for prescribed `γ` and `W` (Howie 2000)

Howie's proof of Theorem 3.1 (`A short proof of a theorem of Brodskii`, Publ. Mat. 44 (2000),
641--647) is by contradiction on a *datum* `∆` in a staggered groupoid presentation `⟨Γ | R⟩`:
`n` reduced closed paths `γ_j` at a vertex `v`, `n` words `W_j` in the free group on `n`
generators, and for each term of each word a relator `r_i^{±1}` with a path `δ` from `v` to its
base, such that `W_j(γ_1, …, γ_n) = ∏_k δ_k r_{i_k}^{±1} δ_k⁻¹` holds in the free groupoid
 `F(Γ)` (`Howie/Datum.lean`).  This file proves that *any* pair `(γ, W)` whose relations already
hold in the presented groupoid `π₁(⟨Γ | R⟩, v)` — i.e. `W_j(γ_1, …, γ_n) = 1` in
`π₁(⟨Γ | R⟩, v)` — can be completed to a datum:

  `Work.ORLocInd.Howie.exists_datum_of_lift_eq_one`.

Concretely, the projection `F(Γ)_v → π₁(⟨Γ | R⟩, v)` has kernel the normal closure `N` of the
conjugates of the relators, so `x_j := W_j(γ_1, …, γ_n) ∈ F(Γ)_v` lies in `N`; and an element of
`N` is a finite product of conjugates of relators.  Each such conjugate is the loop of a term:

* `exists_loop_of_mem_relatorSet` — an element of `P.relatorSet v` is the loop of a term (with
  sign `false`);
* `exists_loop_conj` (from `Howie/exists_loop_conj.lean`) — conjugating a loop is again a loop;
* `loop_flip` (from `Howie/loop_flip.lean`) — the loop of the flipped term is the inverse loop, so
  the *inverse* of an element of `P.relatorSet v` is again a loop of a term; this makes the set of
  products of loops a subgroup of `F(Γ)_v`, so `Subgroup.closure_induction` turns membership in `N`
  into an explicit list of terms (`exists_prod_loop_of_mem_relatorNormalClosure`).

The path identities all rest on `pmul_reverse_comp` in `Howie/LoopAux.lean`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.Datum
import Submission.Work.ORLocInd.Howie.LoopAux
import Submission.Work.ORLocInd.Howie.exists_loop_conj
import Submission.Work.ORLocInd.Howie.loop_flip

set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
variable {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}

/-! ## Loops of terms and the normal closure of the relators -/

/-- Every element of the relator set `P.relatorSet v` (a conjugate of a relator of `P` into the
vertex group at `v`) is the loop of a term of `P` at `v` (with sign `false`). -/
theorem exists_loop_of_mem_relatorSet {x : VertexGroup v} (hx : x ∈ P.relatorSet v) :
    ∃ t : RelatorTerm P v, RelatorTerm.loop t = x := by
  obtain ⟨i, δ, hδ, rfl⟩ := hx
  exact ⟨⟨i, false, δ, hδ⟩, by
    apply Subtype.ext
    simp [RelatorTerm.loop, RelatorTerm.signedPath]⟩

/-- Every conjugate of a relator of `P` into the vertex group at `v` is the loop of a term of `P`
at `v`: this is `exists_loop_of_mem_relatorSet` followed by the conjugation of a loop
(`exists_loop_conj`). -/
theorem exists_loop_of_mem_conjugatesOfSet {x : VertexGroup v}
    (hx : x ∈ Group.conjugatesOfSet (P.relatorSet v)) :
    ∃ t : RelatorTerm P v, RelatorTerm.loop t = x := by
  obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
  obtain ⟨t, ht⟩ := exists_loop_of_mem_relatorSet ha
  obtain ⟨t', ht'⟩ := exists_loop_conj t c
  exact ⟨t', by rw [ht', ht]⟩

/-- The inverse of a product of loops is a product of loops: replace every term of the list by its
flip (`loop_flip`) and reverse the list. -/
theorem exists_prod_inv (L : List (RelatorTerm P v)) :
    ∃ L' : List (RelatorTerm P v),
      (L'.map RelatorTerm.loop).prod = ((L.map RelatorTerm.loop).prod)⁻¹ := by
  induction L with
  | nil => exact ⟨[], by simp⟩
  | cons t L ih =>
    obtain ⟨L', hL'⟩ := ih
    refine ⟨L' ++ [RelatorTerm.flip t], ?_⟩
    rw [List.map_append, List.prod_append, hL']
    simp [loop_flip]

/-- **Every element of the normal closure of the relators is a product of loops of terms.** -/
theorem exists_prod_loop_of_mem_relatorNormalClosure (x : VertexGroup v)
    (hx : x ∈ P.relatorNormalClosure v) :
    ∃ L : List (RelatorTerm P v), (L.map RelatorTerm.loop).prod = x := by
  have hx' : x ∈ Subgroup.closure (Group.conjugatesOfSet (P.relatorSet v)) := hx
  refine Subgroup.closure_induction (k := Group.conjugatesOfSet (P.relatorSet v))
    (p := fun x _ => ∃ L : List (RelatorTerm P v), (L.map RelatorTerm.loop).prod = x)
    ?_ ?_ ?_ ?_ hx'
  · intro y hy
    obtain ⟨t, ht⟩ := exists_loop_of_mem_conjugatesOfSet hy
    exact ⟨[t], by simpa using ht⟩
  · exact ⟨[], by simp⟩
  · intro a b _ _ iha ihb
    obtain ⟨La, hLa⟩ := iha
    obtain ⟨Lb, hLb⟩ := ihb
    exact ⟨La ++ Lb, by rw [List.map_append, List.prod_append, hLa, hLb]⟩
  · intro a _ iha
    obtain ⟨L, hL⟩ := iha
    obtain ⟨L', hL'⟩ := exists_prod_inv L
    exact ⟨L', by rw [hL', hL]⟩

/-! ## The datum -/

/-- The element of the free group on `n` generators evaluated at `γ`, after projection to the
presented groupoid, is the evaluation at the images of the `γ_i`: `π ∘ lift γ = lift (π ∘ γ)`. -/
theorem toVertexGroup_lift (γ : Fin n → VertexGroup v) (x : FreeGroup (Fin n)) :
    P.toVertexGroup v (FreeGroup.lift γ x)
      = FreeGroup.lift (fun i => P.toVertexGroup v (γ i)) x :=
  FreeGroup.lift_unique (f := fun i => P.toVertexGroup v (γ i))
    ((P.toVertexGroup v).comp (FreeGroup.lift γ))
    (fun i => by simp [FreeGroup.lift_apply_of])

/-- **Existence of a datum for prescribed `γ` and `W`.**  If the relations `W_j(γ_1, …, γ_n) = 1`
already hold in the presented groupoid `π₁(⟨Γ | R⟩, v)`, then there is a datum whose generators are
`γ` and whose words are `W`, i.e. the elements `W_j(γ_1, …, γ_n) ∈ F(Γ)_v` can be written as
products of conjugates of relators of `P` (with signs and paths). -/
theorem exists_datum_of_lift_eq_one {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    [DecidableEq V] {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (γ : Fin n → Work.ORLocInd.Howie.VertexGroup v) (W : Fin n → FreeGroup (Fin n))
    (h : ∀ j, FreeGroup.lift (fun i => P.toVertexGroup v (γ i)) (W j) = 1) :
    ∃ D : Work.ORLocInd.Howie.Datum P v n, D.γ = γ ∧ D.W = W := by
  classical
  -- the `x_j = W_j(γ_1, …, γ_n)` lie in the kernel of the projection to the presented group
  have hmem : ∀ j, FreeGroup.lift γ (W j) ∈ P.relatorNormalClosure v := by
    intro j
    refine (QuotientGroup.eq_one_iff (FreeGroup.lift γ (W j))).mp ?_
    rw [← P.toVertexGroup_apply v (FreeGroup.lift γ (W j)), toVertexGroup_lift γ (W j)]
    exact h j
  -- so each of them is a product of loops of terms
  choose terms hterms using fun j =>
    exists_prod_loop_of_mem_relatorNormalClosure (FreeGroup.lift γ (W j)) (hmem j)
  exact ⟨⟨γ, W, terms, fun j => (hterms j).symm⟩, rfl, rfl⟩

end Work.ORLocInd.Howie
