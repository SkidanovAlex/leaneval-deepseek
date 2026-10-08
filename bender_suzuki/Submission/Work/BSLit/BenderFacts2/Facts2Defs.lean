import Mathlib
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSLit.BenderFacts2.Facts2Defs` — vocabulary for `BenderModelFacts2Prop`

The three clauses of `Submission.Blueprint.BenderModelFacts2Prop` are stated for a group `Y`
which is a *model* (one of `PSL(2,2ⁿ)`, `Sz(2^(2n+1))`, `PSU(3,2ⁿ)`) and a strongly embedded
subgroup `H`.  For each of the three families the clauses are proved for the *Borel* `B` and
then transported along the conjugation that carries `B` to the given strongly embedded `H`.

To make this transport reusable, we package the conjunction of the three conclusions as

`BenderFacts2For G H`  (the second clause is stated *without* the `IsZassenhaus` guard, which
is only ever a hypothesis weakening the clause, never used),

and provide the transport lemmas along a group isomorphism (the three clauses themselves, and
the auxiliary computation of the centraliser of a conjugate).
-/

set_option autoImplicit false

namespace Work.BSLit.BenderFacts2

/-- **The three clauses of `BenderModelFacts2Prop`, unconditional in `IsZassenhaus`.** -/
def BenderFacts2For (G : Type*) [Group G] (H : Subgroup G) : Prop :=
  (∀ x ∈ H, (∃ k : ℕ, orderOf x = 2 ^ k) → x ^ 4 = 1) ∧
  ∀ u ∈ Submission.Blueprint.involutions (H : Set G),
    ∀ t : G, orderOf t = 2 → t ∉ H →
      IsCyclic ↥(Subgroup.centralizer ({u * t} : Set G)) ∧
      (∀ y ∈ Subgroup.centralizer ({u * t} : Set G), u * y * u⁻¹ = y⁻¹) ∧
      (127 ≤ (Submission.Blueprint.involutions (H : Set G)).ncard →
        6 ≤ Nat.card ↥(Subgroup.centralizer ({u * t} : Set G)))

/-- **The centraliser of a conjugate** is the conjugate of the centraliser, for an arbitrary
group isomorphism. -/
theorem centralizer_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (a : G) :
    (Subgroup.centralizer ({a} : Set G)).map e.toMonoidHom
      = Subgroup.centralizer ({e a} : Set G') := by
  have h1 : (Subgroup.centralizer ({a} : Set G)).map e.toMonoidHom
      ≤ Subgroup.centralizer ({e a} : Set G') := by
    have h := Subgroup.map_centralizer_le_centralizer_image ({a} : Set G) e.toMonoidHom
    simpa using h
  refine le_antisymm h1 ?_
  have h2 := Subgroup.map_centralizer_le_centralizer_image ({e a} : Set G')
    e.symm.toMonoidHom
  have himg : (⇑e.symm.toMonoidHom) '' ({e a} : Set G') = ({a} : Set G) := by
    ext x
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, rfl, rfl⟩
      simp
    · intro hx
      exact ⟨e a, rfl, by rw [hx]; simp⟩
  rw [himg] at h2
  have h3 := Subgroup.map_mono (f := e.toMonoidHom) h2
  rwa [Subgroup.map_map, show (e.toMonoidHom.comp e.symm.toMonoidHom) = MonoidHom.id G' from by
        ext x
        simp,
    Subgroup.map_id] at h3

end Work.BSLit.BenderFacts2
