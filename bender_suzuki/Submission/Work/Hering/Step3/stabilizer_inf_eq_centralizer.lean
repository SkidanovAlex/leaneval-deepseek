import Mathlib
import Submission.Work.Hering.Step3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step3

open LeanEval.GroupTheory.Defs

/-- Under the conjugation action of `G` on its set of involutions, the stabilizer of an
involution `a` is the centralizer of the singleton `{a}`. -/
theorem stabilizer_eq_centralizer_singleton {G : Type*} [Group G] {a : G}
    (ha : orderOf a = 2) :
    MulAction.stabilizer G (⟨a, ha⟩ : {x : G // x ∈ involutions G})
      = Subgroup.centralizer ({a} : Set G) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have h1 : g * a * g⁻¹ = a := by
      have h2 := congrArg (fun t : {x : G // x ∈ involutions G} => (t : G)) h
      simpa [coe_smul_involutions] using h2
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc a * g = (g * a * g⁻¹) * g := by rw [h1]
      _ = g * a := by group
  · intro h
    apply Subtype.ext
    simp only [coe_smul_involutions]
    have h1 : a * g = g * a := h a (Set.mem_singleton a)
    rw [h1.symm]
    group

/-- The intersection of the centralizers of two elements is the centralizer of the pair. -/
theorem centralizer_singleton_inf {G : Type*} [Group G] (a b : G) :
    Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G)
      = Subgroup.centralizer ({a, b} : Set G) := by
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨ha', hb'⟩ y hy
    rcases (by simpa using hy : y = a ∨ y = b) with rfl | rfl
    · exact ha' y rfl
    · exact hb' y rfl
  · intro h
    exact ⟨fun y hy => h y (by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inl hy),
           fun y hy => h y (by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr hy)⟩

/-- The stabilizer in `G` of the two involutions `a`, `b` under the conjugation action on
`Inv(G)` is the centralizer of the subgroup `U = ⟨a, b⟩` they generate. -/
theorem stabilizer_inf_eq_centralizer {G : Type*} [Group G] {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) {U : Subgroup G}
    (hU : U = Subgroup.closure ({a, b} : Set G)) :
    MulAction.stabilizer G (⟨a, ha⟩ : {x : G // x ∈ involutions G}) ⊓
      MulAction.stabilizer G (⟨b, hb⟩ : {x : G // x ∈ involutions G})
      = Subgroup.centralizer (U : Set G) := by
  rw [stabilizer_eq_centralizer_singleton ha, stabilizer_eq_centralizer_singleton hb,
      hU, Subgroup.centralizer_closure]
  exact centralizer_singleton_inf a b

end Work.Hering.Step3
