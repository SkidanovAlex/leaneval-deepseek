import Mathlib
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Map
import Submission.Work.ORCoherence.Tensor.balanced_span_tmul_one_finsupp_eq_top

namespace Work.ORCoherence.Tensor

open scoped TensorProduct

/-- The balanced tensor product `S ⊗[R] M` is generated, as an `S`-module, by the
elements `1 ⊗ m`. -/
theorem span_tmul_one_eq_top_aux {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (M : Type*) [AddCommGroup M] [Module R M] :
    Submodule.span S (Set.range (fun m : M => Balanced.tmul f 1 m)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    induction y using TensorProduct.induction_on with
    | zero =>
        rw [Submodule.Quotient.mk_zero]
        exact Submodule.zero_mem _
    | tmul s m =>
        change Balanced.tmul f s m ∈
          Submodule.span S (Set.range (fun m : M => Balanced.tmul f 1 m))
        have h2 : s • Balanced.tmul f 1 m = Balanced.tmul f s m := by
          rw [Balanced.smul_tmul, mul_one]
        rw [← h2]
        exact Submodule.smul_mem _ s (Submodule.subset_span ⟨m, rfl⟩)
    | add y z hy hz =>
        rw [Submodule.Quotient.mk_add]
        exact Submodule.add_mem _ hy hz

/-- The balanced tensor product `S ⊗[R] (X →₀ R)` is generated, as an `S`-module, by the
elements `1 ⊗ (single i 1)`. -/
theorem span_tmul_one_finsupp_eq_top_aux {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (X : Type*) :
    Submodule.span S (Set.range (fun i : X => Balanced.tmul f 1 (Finsupp.single i (1 : R)))) =
      ⊤ := by
  set q : Submodule S (Balanced f (X →₀ R)) :=
    Submodule.span S (Set.range (fun i : X => Balanced.tmul f 1 (Finsupp.single i (1 : R))))
  have hspan_single :
      Submodule.span R (Set.range (fun i : X => Finsupp.single i (1 : R))) = ⊤ := by
    have hsup : Finsupp.supported R R (Set.univ : Set X) = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro p
      simp
    have h := Finsupp.supported_eq_span_single R (Set.univ : Set X)
    rw [Set.image_univ] at h
    rw [← h, hsup]
  apply le_antisymm le_top
  rw [← span_tmul_one_eq_top_aux f (X →₀ R)]
  rw [Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  let P : Submodule R (X →₀ R) :=
    { carrier := {m | Balanced.tmul f 1 m ∈ q}
      zero_mem' := by
        show Balanced.tmul f 1 (0 : X →₀ R) ∈ q
        rw [Balanced.tmul_zero]
        exact Submodule.zero_mem _
      add_mem' := by
        intro a b ha hb
        show Balanced.tmul f 1 (a + b) ∈ q
        rw [Balanced.tmul_add]
        exact Submodule.add_mem _ ha hb
      smul_mem' := by
        intro r m hm
        show Balanced.tmul f 1 (r • m) ∈ q
        have h1 : Balanced.tmul f 1 (r • m) = Balanced.tmul f (f r) m := by
          rw [← Balanced.tmul_smul f 1 r m, one_mul]
        have h2 : Balanced.tmul f (f r) m = (f r) • Balanced.tmul f 1 m := by
          simpa using (Balanced.smul_tmul f (f r) 1 m).symm
        rw [h1, h2]
        exact Submodule.smul_mem _ (f r) hm }
  have htop : (⊤ : Submodule R (X →₀ R)) ≤ P := by
    rw [← hspan_single]
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  exact htop Submodule.mem_top

theorem balanced_moduleFinite_finsupp {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (X : Type*) [Finite X] : Module.Finite S (Balanced f (X →₀ R)) := by
  rw [Module.finite_def, ← span_tmul_one_finsupp_eq_top_aux f X]
  exact Submodule.fg_span (Set.finite_range _)

end Work.ORCoherence.Tensor
