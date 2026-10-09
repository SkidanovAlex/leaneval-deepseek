import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.yonedaPair_extToClasses_eq_zero_of_locTrivial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A transversal of the orbits of a group action, containing a prescribed point

For a group `G` acting on a type `α` and a point `a : α` we construct a set `R ⊆ α` of orbit
representatives ("transversal") which contains `a` and meets every orbit of the action in exactly
one point:

`∀ w : α, ∃! w' : R, ∃ σ : G, σ • w = w'.1`.

The construction is the standard one: quotient `α` by the orbit equivalence relation, use the
canonical section `Quotient.out` of the quotient map, and modify it on the orbit of `a` so that
the chosen representative of that orbit is `a` itself.
-/

namespace Work.SSGRoute.E7cOmega

/-- The orbit equivalence relation of the action of `G` on `α`: `x ~ y` iff `y = σ • x` for
some `σ : G`. -/
private def transvOrbitSetoid (G α : Type*) [Group G] [MulAction G α] : Setoid α where
  r x y := ∃ σ : G, σ • x = y
  iseqv := ⟨fun x => ⟨1, one_smul G x⟩,
    fun {x y} h => by
      obtain ⟨σ, hσ⟩ := h
      exact ⟨σ⁻¹, by rw [← hσ, inv_smul_smul]⟩,
    fun {x y z} hxy hyz => by
      obtain ⟨σ, hσ⟩ := hxy
      obtain ⟨τ, hτ⟩ := hyz
      exact ⟨τ * σ, by rw [mul_smul, hσ, hτ]⟩⟩

/-- The orbit relation is symmetric: transitivity of the action. -/
private lemma transvOrbitSetoid_symm {G α : Type*} [Group G] [MulAction G α] {x y : α}
    (h : ∃ σ : G, σ • x = y) : ∃ τ : G, τ • y = x := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ⁻¹, by rw [← hσ, inv_smul_smul]⟩

/-- A section of the quotient map `α → α/~` for the orbit relation, normalized so that the orbit
of `a` is represented by `a` itself. -/
private noncomputable def transvRepClass (G α : Type*) [Group G] [MulAction G α] (a : α)
    (q : Quotient (transvOrbitSetoid G α)) : α := by
  classical
  exact if q = Quotient.mk (transvOrbitSetoid G α) a then a else Quotient.out q

/-- The representative chosen by `transvRepClass` really lies in the class it represents. -/
private lemma transvRepClass_mk (G α : Type*) [Group G] [MulAction G α] (a : α)
    (q : Quotient (transvOrbitSetoid G α)) :
    Quotient.mk (transvOrbitSetoid G α) (transvRepClass G α a q) = q := by
  unfold transvRepClass
  split_ifs with h
  · exact h.symm
  · exact Quotient.out_eq q

/-- The chosen representative of the orbit of `w`. -/
private noncomputable def transvRep (G α : Type*) [Group G] [MulAction G α] (a w : α) : α :=
  transvRepClass G α a (Quotient.mk (transvOrbitSetoid G α) w)

/-- `transvRep G α a w` lies in the orbit of `w`. -/
private lemma transvRep_mk (G α : Type*) [Group G] [MulAction G α] (a w : α) :
    Quotient.mk (transvOrbitSetoid G α) (transvRep G α a w)
      = Quotient.mk (transvOrbitSetoid G α) w :=
  transvRepClass_mk G α a _

/-- The orbit of `a` is represented by `a` itself. -/
private lemma transvRep_self (G α : Type*) [Group G] [MulAction G α] (a : α) :
    transvRep G α a a = a := by
  unfold transvRep transvRepClass
  rw [if_pos rfl]

/-- **Existence of a transversal containing a prescribed point.** Every orbit of an action of a
group `G` on a type `α` is met by `R` in exactly one point, and the prescribed point `a` lies in
`R` (so `a` is the chosen representative of its own orbit). -/
theorem exists_transversal_containing {G α : Type} [Group G] [MulAction G α] (a : α) :
    ∃ R : Set α, a ∈ R ∧ ∀ w : α, ∃! w' : R, ∃ σ : G, σ • w = w'.1 := by
  classical
  refine ⟨Set.range (transvRep G α a), ⟨a, transvRep_self G α a⟩, ?_⟩
  intro w
  refine ⟨⟨transvRep G α a w, ⟨w, rfl⟩⟩, ?_, ?_⟩
  · -- `transvRep G α a w` is in the orbit of `w` (the quotient relation is symmetric)
    exact transvOrbitSetoid_symm (Quotient.exact (transvRep_mk G α a w))
  · -- uniqueness: any representative of the orbit of `w` equals the chosen one
    rintro ⟨y, hyR⟩ hy
    obtain ⟨u, hu⟩ := hyR
    have hyw : Quotient.mk (transvOrbitSetoid G α) w
        = Quotient.mk (transvOrbitSetoid G α) y :=
      Quotient.sound hy
    have huw : Quotient.mk (transvOrbitSetoid G α) u
        = Quotient.mk (transvOrbitSetoid G α) w := by
      calc Quotient.mk (transvOrbitSetoid G α) u
          = Quotient.mk (transvOrbitSetoid G α) (transvRep G α a u) :=
              (transvRep_mk G α a u).symm
        _ = Quotient.mk (transvOrbitSetoid G α) y := by rw [hu]
        _ = Quotient.mk (transvOrbitSetoid G α) w := hyw.symm
    have hy_eq : y = transvRep G α a w := by
      rw [← hu]
      unfold transvRep
      rw [huw]
    exact Subtype.ext hy_eq

end Work.SSGRoute.E7cOmega
