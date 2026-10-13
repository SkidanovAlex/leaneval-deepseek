/-
  WilC5 — the chain step of the Zorn argument for `Work.WilC5.extends_of_elementary_sat`.

  The poset of partial elementary maps (`PEM L M N`, ordered by extension) is closed under unions
  of chains: the union of a compatible family of partial maps is again one, and is the least upper
  bound of the family.  Two facts are needed.

  * `chain_exists_le_finset` — a finite subfamily of a chain has an upper bound in the chain.
  * `PEM.iUnion_valid` — the union of a nonempty chain of valid partial maps is valid and is an
    upper bound of the chain.
-/
import Mathlib
import Submission.Work.WilC5.ExtSatAux

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language
open scoped FirstOrder

/-- **A finite subfamily of a chain has an upper bound in the chain.**  Used to bound the (finitely
many) parameters of a formula inside a single member of a chain of partial maps. -/
theorem chain_exists_le_finset {α : Type*} [Preorder α] {c : Set α} (hc : IsChain (· ≤ ·) c)
    {u0 : α} (hu0 : u0 ∈ c) {F : Finset α} (hF : ∀ x ∈ F, x ∈ c) :
    ∃ u ∈ c, ∀ x ∈ F, x ≤ u := by
  induction F using Finset.induction_on with
  | empty => exact ⟨u0, hu0, by simp⟩
  | insert a F ha ih =>
    have hF' : ∀ x ∈ F, x ∈ c := fun x hx => hF x (Finset.mem_insert_of_mem hx)
    have hac : a ∈ c := hF a (Finset.mem_insert_self a F)
    obtain ⟨u, hu, hle⟩ := ih hF'
    rcases eq_or_ne a u with h'au | hne
    · rw [h'au] at *
      exact ⟨u, hu, fun x hx => by
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact le_rfl
        · exact hle x hx⟩
    · rcases hc hac hu hne with h | h
      · exact ⟨u, hu, fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact h
          · exact hle x hx⟩
      · exact ⟨a, hac, fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact le_rfl
          · exact le_trans (hle x hx) h⟩

/-- **The union of a chain of partial elementary maps is a partial elementary map**, and is an upper
bound of the chain.  Its domain is the union of the domains. -/
theorem PEM.iUnion_valid {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M]
    [L.Structure N] {c : Set (PEM L M N)} (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hvalid : ∀ p ∈ c, p.Valid) :
    ∃ ub : PEM L M N, ub.Valid ∧ ub.1 = ⋃ p ∈ c, p.1 ∧ ∀ p ∈ c, p ≤ ub := by
  classical
  -- any two members of the chain agree on the intersection of their domains
  have agree : ∀ {p q : PEM L M N}, p ∈ c → q ∈ c → ∀ (x : N) (hp : x ∈ p.1) (hq : x ∈ q.1),
      p.2 ⟨x, hp⟩ = q.2 ⟨x, hq⟩ := by
    intro p q hpc hqc x hpx hqx
    rcases eq_or_ne p q with hpq | hpq
    · subst hpq; exact congrArg _ (Subtype.ext rfl)
    · rcases hc hpc hqc hpq with h | h
      · obtain ⟨hsub, hag⟩ := h
        exact (hag ⟨x, hpx⟩).symm.trans (congrArg _ (Subtype.ext rfl))
      · obtain ⟨hsub, hag⟩ := h
        exact (congrArg _ (Subtype.ext rfl)).symm.trans (hag ⟨x, hqx⟩)
  -- every element of the union lies in some member of the chain
  have mem_union : ∀ x : ↥(⋃ p ∈ c, p.1), ∃ p : PEM L M N, p ∈ c ∧ x.1 ∈ p.1 := by
    intro x
    obtain ⟨p, hp'⟩ := Set.mem_iUnion.1 x.2
    obtain ⟨hp, hx⟩ := Set.mem_iUnion.1 hp'
    exact ⟨p, hp, hx⟩
  -- the value of the union map
  have key : ∀ x : ↥(⋃ p ∈ c, p.1),
      ∃ y : M, ∃ (p : PEM L M N) (hp : p ∈ c) (hx : x.1 ∈ p.1), p.2 ⟨x.1, hx⟩ = y := by
    intro x
    obtain ⟨p, hp, hx⟩ := mem_union x
    exact ⟨p.2 ⟨x.1, hx⟩, p, hp, hx, rfl⟩
  let f : (↥(⋃ p ∈ c, p.1)) → M := fun x => Classical.choose (key x)
  have f_spec : ∀ x : ↥(⋃ p ∈ c, p.1),
      ∃ (p : PEM L M N) (hp : p ∈ c) (hx : x.1 ∈ p.1), p.2 ⟨x.1, hx⟩ = f x :=
    fun x => Classical.choose_spec (key x)
  have f_eq : ∀ (p : PEM L M N) (hp : p ∈ c) (x : N) (hx : x ∈ p.1)
      (hux : x ∈ ⋃ p ∈ c, p.1), p.2 ⟨x, hx⟩ = f ⟨x, hux⟩ := by
    intro p hp x hx hux
    obtain ⟨q, hq, hqx, hEq⟩ := f_spec ⟨x, hux⟩
    exact (agree hq hp x hqx hx).symm.trans hEq
  refine ⟨⟨⋃ p ∈ c, p.1, f⟩, ?_, rfl, ?_⟩
  · -- validity of the union map
    intro φ
    have hincl : ∀ v : ↥φ.freeVarFinset, ∃ p ∈ c, v.1.1 ∈ p.1 := fun v => mem_union v.1
    let g : ↥φ.freeVarFinset → PEM L M N := fun v => Classical.choose (hincl v)
    have g_mem : ∀ v : ↥φ.freeVarFinset, g v ∈ c := fun v => (Classical.choose_spec (hincl v)).1
    have g_prop : ∀ v : ↥φ.freeVarFinset, v.1.1 ∈ (g v).1 :=
      fun v => (Classical.choose_spec (hincl v)).2
    obtain ⟨u, hu, hle⟩ := chain_exists_le_finset hc hne.some_mem
      (F := Finset.univ.image g) (fun x hx => by
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
        exact g_mem v)
    have humem : ∀ v : ↥φ.freeVarFinset, v.1.1 ∈ u.1 := fun v =>
      (hle (g v) (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)).1 (g_prop v)
    let f'' : ↥φ.freeVarFinset → u.1 := fun v => ⟨v.1.1, humem v⟩
    have h1 : Formula.Realize (φ.restrictFreeVar f'') (Subtype.val : u.1 → N)
        ↔ Formula.Realize φ (Subtype.val : ↥(⋃ p ∈ c, p.1) → N) :=
      BoundedFormula.realize_restrictFreeVar (Subtype.val : ↥(⋃ p ∈ c, p.1) → N)
        (fun _ => rfl)
    have h2 : Formula.Realize (φ.restrictFreeVar f'') u.2 ↔ Formula.Realize φ f :=
      BoundedFormula.realize_restrictFreeVar f (fun a => by
        show u.2 (f'' a) = f a.1
        exact f_eq u hu a.1.1 (humem a) a.1.2)
    have h3 := hvalid u hu (φ.restrictFreeVar f'')
    exact h1.symm.trans (h3.trans h2)
  · -- the union is above every member
    intro p hp
    refine ⟨fun x hx => Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hx⟩⟩, fun x => ?_⟩
    exact (f_eq p hp x.1 x.2 _).symm

end Work.WilC5
