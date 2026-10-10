import Mathlib.FieldTheory.KrullTopology
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

open _root_.SSGRoute

/-- A finite infimum of open subgroups is open (induction on the finite index set). -/
private theorem isOpen_finset_inf {G ι : Type} [Group G] [TopologicalSpace G]
    (s : Finset ι) (W : ι → Subgroup G)
    (h : ∀ i ∈ s, IsOpen ((W i : Subgroup G) : Set G)) :
    IsOpen (((s.inf W : Subgroup G) : Set G)) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, Subgroup.coe_inf]
    exact (h a (Finset.mem_insert_self a s)).inter
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Membership in a finite infimum of subgroups. -/
private theorem mem_finset_inf {G ι : Type} [Group G] {s : Finset ι} {W : ι → Subgroup G}
    {x : G} (hx : x ∈ s.inf W) : ∀ i ∈ s, x ∈ W i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    intro i hi
    rw [Finset.inf_insert] at hx
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · exact (Subgroup.mem_inf.mp hx).1
    · exact ih (Subgroup.mem_inf.mp hx).2 i hi

/-- The finite datum `histDatum K y f` is locally zero on each local group: it is a finite sum of the
corrections `correctionDatum K ½y (f j).2 (f j).1`, each of which is locally constant on
`decomp k A ⊓ K.fixingSubgroup`, so one takes the intersection of their local-constancy moduli and
evaluates at the unit (`correctionDatum_locConst`). -/
theorem swHistDatum_locConst {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy1 : y 1 = 0) (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    {n : ℕ} (f : Fin n → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hz1 : ∀ j, (f j).2 1 = 0) (hzc : ∀ j, SSGRoute.IsLocConstOn K.fixingSubgroup (f j).2)
    (A : ValuationSubring Ω) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup →
        Work.SSGRoute.ZDataMup.histDatum K y f A x = 0 := by
  classical
  -- The global datum `½y` is locally constant on `K.fixingSubgroup` and kills the unit.
  have hglc : SSGRoute.IsLocConstOn K.fixingSubgroup (fun σ => (2 : ZMod p)⁻¹ * y σ) := by
    obtain ⟨U, hUo, hU⟩ := hyc
    exact ⟨U, hUo, fun g hg u hu huH => by
      show (2 : ZMod p)⁻¹ * y (g * u) = (2 : ZMod p)⁻¹ * y g
      rw [hU g hg u hu huH]⟩
  have hg1 : (fun σ => (2 : ZMod p)⁻¹ * y σ) 1 = 0 := by
    simp [hy1]
  -- A local-constancy modulus for each summand.
  choose U hUo hU using fun j =>
    Work.SSGRoute.ZDataMup.correctionDatum_locConst K (fun σ => (2 : ZMod p)⁻¹ * y σ)
      ((f j).2) ((f j).1) A hglc hg1 (hzc j) (hz1 j)
  refine ⟨Finset.univ.inf U, isOpen_finset_inf _ _ (fun j _ => hUo j), ?_⟩
  intro x hx hxA
  simp only [Work.SSGRoute.ZDataMup.histDatum]
  exact Finset.sum_eq_zero fun j _ =>
    hU j x (mem_finset_inf hx j (Finset.mem_univ j)) hxA

end Work.SSGRoute.H9
