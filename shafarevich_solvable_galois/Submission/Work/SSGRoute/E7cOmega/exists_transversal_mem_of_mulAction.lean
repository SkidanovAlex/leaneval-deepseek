import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A transversal of the orbits of a group action, containing a prescribed point

Given a group `G` acting on a type `α` and a point `r : α`, we produce a set `R ⊆ α` of orbit
representatives ("transversal") which contains `r` and meets every orbit in exactly one point:

`∀ w : α, ∃! w' : R, ∃ σ : G, σ • w = w'.1`.

The construction is the standard one: quotient `α` by the orbit equivalence relation, take the
canonical section `Quotient.out` of the quotient map, and modify it on the class of `r` so that the
chosen representative of that class is `r` itself.
-/

namespace Work.SSGRoute.E7cOmega

/-- The orbit equivalence relation of an action of `G` on `α`:
`a ~ b` iff `b = σ • a` for some `σ : G`. -/
def orbitSetoid (G α : Type) [Group G] [MulAction G α] : Setoid α where
  r a b := ∃ σ : G, σ • a = b
  iseqv := ⟨fun a => ⟨1, one_smul G a⟩,
            fun {a b} h => by
              obtain ⟨σ, hσ⟩ := h
              exact ⟨σ⁻¹, by rw [← hσ]; exact inv_smul_smul σ a⟩,
            fun {a b c} hab hbc => by
              obtain ⟨σ, hσ⟩ := hab
              obtain ⟨τ, hτ⟩ := hbc
              exact ⟨τ * σ, by rw [mul_smul, hσ, hτ]⟩⟩

/-- A section of the quotient map `α → α/~` for the orbit relation, normalized so that the class
of `r` is represented by `r` itself. -/
noncomputable def orbitRepClass (G α : Type) [Group G] [MulAction G α] (r : α)
    (q : Quotient (orbitSetoid G α)) : α := by
  classical
  exact if q = Quotient.mk (orbitSetoid G α) r then r else Quotient.out q

/-- The chosen representative of the orbit of `w`. -/
noncomputable def orbitRep (G α : Type) [Group G] [MulAction G α] (r w : α) : α :=
  orbitRepClass G α r (Quotient.mk (orbitSetoid G α) w)

/-- The representative chosen by `orbitRepClass` really lies in the class it represents. -/
lemma orbitRepClass_mk_eq (G α : Type) [Group G] [MulAction G α] (r : α)
    (q : Quotient (orbitSetoid G α)) :
    Quotient.mk (orbitSetoid G α) (orbitRepClass G α r q) = q := by
  unfold orbitRepClass
  split_ifs with h
  · exact h.symm
  · exact Quotient.out_eq q

/-- `orbitRep G α r w` is equivalent to `w` under the orbit relation. -/
lemma orbitRep_class (G α : Type) [Group G] [MulAction G α] (r w : α) :
    Quotient.mk (orbitSetoid G α) (orbitRep G α r w) = Quotient.mk (orbitSetoid G α) w :=
  orbitRepClass_mk_eq G α r (Quotient.mk (orbitSetoid G α) w)

/-- **Existence of a transversal containing a prescribed point** for an arbitrary group action:
there is a set `R` of orbit representatives with `r ∈ R` and meeting each orbit in exactly one
point. -/
theorem exists_transversal_mem_of_mulAction (G α : Type) [Group G] [MulAction G α] (r : α) :
    ∃ R : Set α, r ∈ R ∧ ∀ w : α, ∃! w' : R, ∃ σ : G, σ • w = w'.1 := by
  classical
  refine ⟨Set.range (orbitRep G α r), ⟨r, ?_⟩, ?_⟩
  · show orbitRep G α r r = r
    unfold orbitRep orbitRepClass
    rw [if_pos rfl]
  · intro w
    refine ⟨⟨orbitRep G α r w, ⟨w, rfl⟩⟩, ?_, ?_⟩
    · have h := orbitRep_class G α r w
      exact Quotient.exact h.symm
    · rintro ⟨y, hyR⟩ hy
      obtain ⟨u, hu⟩ := hyR
      obtain ⟨σ, hσ⟩ := hy
      have hw : Quotient.mk (orbitSetoid G α) w = Quotient.mk (orbitSetoid G α) y :=
        Quotient.sound ⟨σ, hσ⟩
      have hy' : Quotient.mk (orbitSetoid G α) y = Quotient.mk (orbitSetoid G α) u := by
        rw [← hu]; exact orbitRep_class G α r u
      have hw' : Quotient.mk (orbitSetoid G α) w = Quotient.mk (orbitSetoid G α) u :=
        hw.trans hy'
      have hyw : y = orbitRep G α r w := by
        rw [← hu]
        unfold orbitRep
        rw [hw'.symm]
      exact Subtype.ext hyw

end Work.SSGRoute.E7cOmega
