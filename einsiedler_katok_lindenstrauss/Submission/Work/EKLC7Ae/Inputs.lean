import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.SmulMS
import Submission.Work.EKLC7.shape_smulMS
import Submission.Work.EKLC7.isPlaqueAlgebra_smulMS
import Submission.Work.EKLC7.atom_smulMS
import Submission.Work.EKLContract.All
import Submission.Work.EKLContract.Lemmas.SL3Topology
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLComp.smulMS_propor
import Submission.Work.EKLC7Ae.Endgame

/-!
# `Work.EKLC7Ae.Inputs` — the two inputs of the endgame

* `exists_countable_dense_in_U`: a countable dense inverse-closed subset of a closed subgroup
  `U ≤ SL₃(ℝ)`;
* `shape_propor_ae`: the shape proportionality of the leafwise measures, deduced from the
  comparison lemma `Work.EKLComp.smulMS_propor` and the `equivariant` field of `IsLeafwise`.
-/

namespace Work.EKLC7Ae

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

noncomputable section

/-- A closed subgroup of `SL₃(ℝ)` has a countable dense inverse-closed subset. -/
theorem exists_countable_dense_in_U (U : Subgroup SL3) (hUcl : IsClosed (U : Set SL3)) :
    ∃ D : Set SL3, D.Countable ∧ D ⊆ (U : Set SL3) ∧ closure D = (U : Set SL3) ∧
      ∀ u : SL3, u ∈ D → u⁻¹ ∈ D := by
  haveI : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  haveI : PolishSpace ↥(U : Set SL3) := hUcl.polishSpace
  haveI : TopologicalSpace.SeparableSpace ↥(U : Set SL3) := inferInstance
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (↥(U : Set SL3))
  set A : Set SL3 := (fun v : ↥(U : Set SL3) => (v : SL3)) '' S with hA
  set I : Set SL3 := (fun x : SL3 => x⁻¹) '' A with hI
  have hAc : A.Countable := by rw [hA]; exact hSc.image _
  have hIc : I.Countable := by rw [hI]; exact hAc.image _
  have hAU : A ⊆ (U : Set SL3) := by
    rw [hA]
    rintro u ⟨v, -, rfl⟩
    exact v.2
  have hIU : I ⊆ (U : Set SL3) := by
    rw [hI]
    rintro u ⟨v, hv, rfl⟩
    exact U.inv_mem (hAU hv)
  have hAcl : closure A = (U : Set SL3) := by
    refine Set.Subset.antisymm (closure_minimal hAU hUcl) ?_
    have hSd' : (U : Set SL3) ⊆ closure A := by
      rw [hA]
      exact Subtype.dense_iff.mp hSd
    exact hSd'
  refine ⟨A ∪ I, hAc.union hIc, ?_, ?_, ?_⟩
  · rintro u (hu | hu)
    · exact hAU hu
    · exact hIU hu
  · rw [closure_union, hAcl, Set.union_eq_left.mpr (closure_minimal hIU hUcl)]
  · rintro u (hu | hu)
    · exact Or.inr ⟨u, hu, rfl⟩
    · obtain ⟨v, hv, rfl⟩ := hu
      simpa only [inv_inv, Set.mem_union] using Or.inl hv

/-- **The shape proportionality of the leafwise measures** (Pisa 6.27 for a single plaque,
EKL (6)), in the form consumed by `Work.EKLC7Ae.aeHaar_of_shape_propor`.

For every `u` in a countable set `D ⊆ U` and `μ`-a.e. `x` in the carrier of one of the plaque
algebras `(Z n, m n)`, the left translate of `ν x` by `u⁻¹` is a finite non-zero multiple of
`ν x` on the shape `shape (m n) U x`.

The proof combines the comparison `Work.EKLComp.smulMS_propor` (which compares the `condexp`
field of `ν` at `x` and at `u • x`) with the `equivariant` field of `IsLeafwise`, which relates
`ν x` to the right translate of `ν (u • x)`. -/
theorem shape_propor_ae (h2 : P_X3) (μ : Measure X3) [IsProbabilityMeasure μ]
    (U : Subgroup SL3) (hU : IsHoro U) (t0 : Fin 3 → ℝ)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1))
    (ν : X3 → Measure SL3) (X' : Set X3) (hL : IsLeafwise μ U ν X')
    (hinv : IsUInvariant μ U)
    {Z : ℕ → Set X3} {m : ℕ → MeasurableSpace X3}
    (hpa : ∀ n, IsPlaqueAlgebra U (Z n) (m n))
    (D : Set SL3) (hDU : D ⊆ (U : Set SL3)) (hDc : D.Countable) :
    ∀ᵐ x ∂μ, x ∈ X' → ∀ u ∈ D, u • x ∈ X' → ∀ n, x ∈ Z n →
      ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧
        ((ν x).map (fun g => u⁻¹ * g)).restrict (shape (m n) U x)
          = κ • (ν x).restrict (shape (m n) U x) := by
  have hfree : ∀ᵐ x ∂μ, ∀ w ∈ U, w • x = x → w = 1 :=
    Work.EKLRelCross.ae_free_orbit h2 μ U hU t0 hmp hcontr
  haveI : Countable ↥D := hDc.to_subtype
  have key : ∀ p : ↥D × ℕ, ∀ᵐ x ∂μ, x ∈ X' → (p.1 : SL3) • x ∈ X' → x ∈ Z p.2 →
      ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧
        ((ν x).map (fun g => (p.1 : SL3)⁻¹ * g)).restrict (shape (m p.2) U x)
          = κ • (ν x).restrict (shape (m p.2) U x) := by
    intro p
    have hcmp := Work.EKLComp.smulMS_propor h2 U hU hinv (hDU p.1.2) hL hfree (hpa p.2)
    rw [MeasureTheory.ae_restrict_iff' ((hpa p.2).1 _ (hpa p.2).2.2.1)] at hcmp
    filter_upwards [hcmp] with x hx
    intro hxX' hux hxZ
    obtain ⟨c, hc0, hct, hc⟩ := hx hxZ hxX' hux
    obtain ⟨c', hc'0, hc't, hc'⟩ := hL.equivariant x hxX' (p.1 : SL3) (hDU p.1.2) hux
    have hmap1 : (ν x).map (fun g : SL3 => (p.1 : SL3)⁻¹ * g)
        = c' • (ν ((p.1 : SL3) • x)).map (fun g : SL3 => (p.1 : SL3)⁻¹ * g * (p.1 : SL3)) := by
      rw [hc', Measure.map_smul] <;> try fun_prop
      congr 1
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext g
      simp only [Function.comp_apply, mul_assoc]
    refine ⟨c' * c, mul_ne_zero hc'0 hc0, ENNReal.mul_ne_top hc't hct, ?_⟩
    rw [hmap1, Measure.restrict_smul, hc, smul_smul]
  have hall := MeasureTheory.ae_all_iff.mpr key
  filter_upwards [hall] with x hx
  intro hxX' u hu hux n hn
  exact hx (⟨u, hu⟩, n) hxX' hux hn

end

end Work.EKLC7Ae
