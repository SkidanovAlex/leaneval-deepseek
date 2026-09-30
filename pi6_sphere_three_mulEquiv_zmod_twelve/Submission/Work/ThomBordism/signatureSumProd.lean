import Mathlib
import Submission.Work.SignatureBordism.signature_prod

/-!
# Additivity of the signature over a finite orthogonal sum

For a finite family of quadratic forms `Q i` on `ℚ`-vector spaces `V i`, the orthogonal sum
`x ↦ ∑ i, Q i (x i)` on the product `∀ i, V i` has signature the sum of the signatures:

`Work.ThomBordism.signature_sum_prod`.

The proof is by induction on the finite index type (`Fintype.induction_empty_option`), using the
binary `Work.SignatureBordism.signature_prod` at the `Option` step and the invariance of the
signature under linear isometries (`Work.SignatureBordism.signature_comp_linearEquiv`) for the
reindexing step.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.ThomBordism

noncomputable section

/-- **Additivity of the signature over a finite orthogonal sum.** -/
theorem signature_sum_prod {ι : Type} [Fintype ι] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)] [∀ i, FiniteDimensional ℚ (V i)]
    (Q : ∀ i, QuadraticForm ℚ (V i)) :
    Work.SignatureBordism.signature
        (∑ i, (Q i).comp (LinearMap.proj i : (∀ i, V i) →ₗ[ℚ] V i))
      = ∑ i, Work.SignatureBordism.signature (Q i) := by
  classical
  have hmain : ∀ (κ : Type) [Fintype κ], (∀ {W : κ → Type} [∀ i, AddCommGroup (W i)]
      [∀ i, Module ℚ (W i)] [∀ i, FiniteDimensional ℚ (W i)] (Q : ∀ i, QuadraticForm ℚ (W i)),
      Work.SignatureBordism.signature
          (∑ i, (Q i).comp (LinearMap.proj i : (∀ i, W i) →ₗ[ℚ] W i))
        = ∑ i, Work.SignatureBordism.signature (Q i)) := by
    intro κ _
    refine Fintype.induction_empty_option (P := fun κ instκ =>
      letI := instκ
      ∀ {W : κ → Type} [∀ i, AddCommGroup (W i)]
        [∀ i, Module ℚ (W i)] [∀ i, FiniteDimensional ℚ (W i)] (Q : ∀ i, QuadraticForm ℚ (W i)),
        Work.SignatureBordism.signature
            (∑ i, (Q i).comp (LinearMap.proj i : (∀ i, W i) →ₗ[ℚ] W i))
          = ∑ i, Work.SignatureBordism.signature (Q i)) ?_ ?_ ?_ κ
    · -- reindexing along an equivalence
      intro α β _ e hα
      intro W _ _ _ Q
      letI instα : Fintype α := Fintype.ofEquiv β e.symm
      let he' : ((b : β) → W b) ≃ₗ[ℚ] ((a : α) → W (e a)) :=
        LinearEquiv.piCongrLeft' ℚ W e.symm
      have he'_apply : ∀ (w : (b : β) → W b) (a : α), he' w a = w (e a) := by
        intro w a
        show (LinearEquiv.piCongrLeft' ℚ W e.symm) w a = w (e a)
        rw [LinearEquiv.piCongrLeft'_apply]
        rfl
      have hform : (∑ b : β, (Q b).comp (LinearMap.proj b : ((b : β) → W b) →ₗ[ℚ] W b))
          = (∑ a : α, (Q (e a)).comp
              (LinearMap.proj a : ((a : α) → W (e a)) →ₗ[ℚ] W (e a))).comp
            (he' : ((b : β) → W b) →ₗ[ℚ] ((a : α) → W (e a))) := by
        ext w
        calc (∑ b : β, (Q b).comp (LinearMap.proj b : ((b : β) → W b) →ₗ[ℚ] W b)) w
            = ∑ b : β, Q b (w b) := by
              rw [sum_apply]
              exact Finset.sum_congr rfl fun b _ => by
                rw [QuadraticMap.comp_apply, LinearMap.proj_apply]
          _ = (∑ a : α, (Q (e a)).comp
                (LinearMap.proj a : ((a : α) → W (e a)) →ₗ[ℚ] W (e a))) (he' w) := by
              rw [sum_apply]
              rw [show (∑ a : α, ((Q (e a)).comp
                    (LinearMap.proj a : ((a : α) → W (e a)) →ₗ[ℚ] W (e a))) (he' w))
                  = ∑ a : α, Q (e a) (w (e a)) from
                Finset.sum_congr rfl fun a _ => by
                  rw [QuadraticMap.comp_apply, LinearMap.proj_apply, he'_apply]]
              exact (Fintype.sum_equiv e (fun a => Q (e a) (w (e a)))
                (fun b => Q b (w b)) (fun a => rfl)).symm
      have hα' := hα (W := fun a => W (e a)) (Q := fun a => Q (e a))
      calc Work.SignatureBordism.signature
            (∑ b : β, (Q b).comp (LinearMap.proj b : ((b : β) → W b) →ₗ[ℚ] W b))
          = Work.SignatureBordism.signature
              ((∑ a : α, (Q (e a)).comp
                (LinearMap.proj a : ((a : α) → W (e a)) →ₗ[ℚ] W (e a))).comp
                (he' : ((b : β) → W b) →ₗ[ℚ] ((a : α) → W (e a)))) := by
            rw [hform]
        _ = Work.SignatureBordism.signature
              (∑ a : α, (Q (e a)).comp
                (LinearMap.proj a : ((a : α) → W (e a)) →ₗ[ℚ] W (e a))) :=
            Work.SignatureBordism.signature_comp_linearEquiv _ he'
        _ = ∑ a : α, Work.SignatureBordism.signature (Q (e a)) := hα'
        _ = ∑ b : β, Work.SignatureBordism.signature (Q b) :=
            Fintype.sum_equiv e _ _ (fun a => rfl)
    · -- the empty index type
      intro W _ _ _ Q
      haveI : Subsingleton (∀ i : PEmpty, W i) :=
        ⟨fun a b => funext fun i => i.elim⟩
      rw [Work.SignatureBordism.signature_eq_zero_of_subsingleton, Fintype.sum_empty]
    · -- the `Option` step
      intro α _ hα
      intro W _ _ _ Q
      haveI : FiniteDimensional ℚ ((i : α) → W (some i)) := Module.Finite.pi
      let Qr : QuadraticForm ℚ ((i : α) → W (some i)) :=
        ∑ i, (Q (some i)).comp (LinearMap.proj i : ((i : α) → W (some i)) →ₗ[ℚ] W (some i))
      have hform : (∑ i : Option α, (Q i).comp
            (LinearMap.proj i : ((i : Option α) → W i) →ₗ[ℚ] W i))
          = ((Q none).prod Qr).comp
              ((LinearEquiv.piOptionEquivProd ℚ :
                ((i : Option α) → W i) ≃ₗ[ℚ] (W none × ((i : α) → W (some i)))) :
                ((i : Option α) → W i) →ₗ[ℚ] (W none × ((i : α) → W (some i)))) := by
        ext v
        rw [QuadraticMap.comp_apply]
        have hsum : (∑ i : Option α, (Q i).comp
              (LinearMap.proj i : ((i : Option α) → W i) →ₗ[ℚ] W i))
            = (Q none).comp (LinearMap.proj none : ((i : Option α) → W i) →ₗ[ℚ] W none)
              + ∑ i : α, (Q (some i)).comp
                  (LinearMap.proj (some i) : ((i : Option α) → W i) →ₗ[ℚ] W (some i)) :=
          Fintype.sum_option (α := α) (f := fun i : Option α => (Q i).comp
            (LinearMap.proj i : ((i : Option α) → W i) →ₗ[ℚ] W i))
        have hL : (∑ i : Option α, (Q i).comp
              (LinearMap.proj i : ((i : Option α) → W i) →ₗ[ℚ] W i)) v
            = Q none (v none) + ∑ i : α, Q (some i) (v (some i)) := by
          simp only [sum_apply, Fintype.sum_option, add_apply, QuadraticMap.comp_apply,
            LinearMap.proj_apply]
        have hR : ((Q none).prod Qr)
              (((LinearEquiv.piOptionEquivProd ℚ :
                ((i : Option α) → W i) ≃ₗ[ℚ] (W none × ((i : α) → W (some i)))) :
                ((i : Option α) → W i) →ₗ[ℚ]
                  (W none × ((i : α) → W (some i)))) v)
            = Q none (v none) + ∑ i : α, Q (some i) (v (some i)) := by
          have hQr : Qr = ∑ i : α, (Q (some i)).comp
              (LinearMap.proj i : ((i : α) → W (some i)) →ₗ[ℚ] W (some i)) := rfl
          simp only [QuadraticMap.prod_apply, hQr, sum_apply,
            QuadraticMap.comp_apply, LinearMap.proj_apply]
          rfl
        rw [hL, hR]
      calc Work.SignatureBordism.signature
            (∑ i : Option α, (Q i).comp (LinearMap.proj i : ((i : Option α) → W i) →ₗ[ℚ] W i))
          = Work.SignatureBordism.signature (((Q none).prod Qr).comp
              ((LinearEquiv.piOptionEquivProd ℚ :
                ((i : Option α) → W i) ≃ₗ[ℚ] (W none × ((i : α) → W (some i)))) :
                ((i : Option α) → W i) →ₗ[ℚ] (W none × ((i : α) → W (some i))))) := by
            rw [hform]
        _ = Work.SignatureBordism.signature ((Q none).prod Qr) :=
            Work.SignatureBordism.signature_comp_linearEquiv _ _
        _ = Work.SignatureBordism.signature (Q none) + Work.SignatureBordism.signature Qr :=
            Work.SignatureBordism.signature_prod _ _
        _ = Work.SignatureBordism.signature (Q none) +
              ∑ i : α, Work.SignatureBordism.signature (Q (some i)) := by
            rw [show Qr = ∑ i : α, (Q (some i)).comp
                (LinearMap.proj i : ((i : α) → W (some i)) →ₗ[ℚ] W (some i)) from rfl,
              hα (fun i => Q (some i))]
        _ = ∑ i : Option α, Work.SignatureBordism.signature (Q i) :=
            (Fintype.sum_option (α := α)
              (f := fun i : Option α => Work.SignatureBordism.signature (Q i))).symm
  exact hmain ι Q

end

end Work.ThomBordism
