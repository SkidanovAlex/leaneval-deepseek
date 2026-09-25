import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open scoped BigOperators

namespace Commons.LinearAlgebra.Submodule

theorem finrank_iSup_le_sum_of_finite
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (S : ι → Submodule K V) [∀ i, Module.Finite K ↥(S i)] :
    Module.finrank K ↥(⨆ i : ι, S i) ≤ ∑ i : ι, Module.finrank K ↥(S i) := by
  classical
  let P : Finset ι → Prop := fun s =>
    Module.Finite K ↥(s.sup S) ∧
      Module.finrank K ↥(s.sup S) ≤ ∑ i ∈ s, Module.finrank K ↥(S i)
  have h_empty : P ∅ := by
    dsimp [P]
    constructor
    · rw [Finset.sup_empty]
      infer_instance
    · simp
  have h_insert : ∀ (a : ι) (s : Finset ι), a ∉ s → P s → P (insert a s) := by
    intro a s ha ih
    rcases ih with ⟨hfin_s, hle_s⟩
    have hfin_a : Module.Finite K ↥(S a) := inferInstance
    have hfin_sup : Module.Finite K ↥(S a ⊔ s.sup S) := by infer_instance
    have hfin_insert : Module.Finite K ↥((insert a s).sup S) := by
      rw [Finset.sup_insert]
      exact hfin_sup
    constructor
    · exact hfin_insert
    · rw [Finset.sup_insert, Finset.sum_insert ha]
      have hsup : Module.finrank K ↥(S a ⊔ s.sup S) ≤
          Module.finrank K ↥(S a) + Module.finrank K ↥(s.sup S) := by
        have hfin_eq := Submodule.finrank_sup_add_finrank_inf_eq (S a) (s.sup S)
        omega
      exact le_trans hsup (Nat.add_le_add_left hle_s _)
  have hP := Finset.induction_on (motive := P) (Finset.univ : Finset ι) h_empty h_insert
  have huniv : (Finset.univ : Finset ι).sup S = ⨆ i : ι, S i := by
    rw [Finset.sup_eq_iSup]
    change (⨆ i ∈ (↑(Finset.univ : Finset ι) : Set ι), S i) = ⨆ i : ι, S i
    rw [Finset.coe_univ]
    exact iSup_univ
  have hmain : Module.finrank K ↥((Finset.univ : Finset ι).sup S) ≤
      ∑ i : ι, Module.finrank K ↥(S i) := hP.2
  rw [huniv] at hmain
  simpa using hmain

end Commons.LinearAlgebra.Submodule