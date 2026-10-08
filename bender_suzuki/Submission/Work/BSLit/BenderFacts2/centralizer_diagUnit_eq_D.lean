import Mathlib
import Submission.Work.Models.PSL2.D_facts

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2

open Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-- Diagonal matrices commute: `D` is the image of the abelian group `Fˣ` under the
injective homomorphism `Work.Models.PSL2.DUnitHom`. -/
private lemma inD_mul_comm {A B : Work.Models.SL2 F} (hA : Work.Models.PSL2.inD A)
    (hB : Work.Models.PSL2.inD B) : A * B = B * A := by
  have e : ↥(Work.Models.PSL2.D (F := F)) ≃* Fˣ :=
    MulEquiv.ofBijective (Work.Models.PSL2.DUnitHom (F := F))
      ⟨Work.Models.PSL2.DUnitHom_injective, Work.Models.PSL2.DUnitHom_surjective⟩
  have h : (⟨A, hA⟩ : ↥(Work.Models.PSL2.D (F := F))) * ⟨B, hB⟩
      = (⟨B, hB⟩ : ↥(Work.Models.PSL2.D (F := F))) * ⟨A, hA⟩ := by
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  exact congrArg Subtype.val h

/-- Entry computation: if `A` commutes with `diagUnit u`, then the `(0,1)`-entries satisfy
`A₀₁ * u⁻¹ = u * A₀₁`. -/
private lemma commute_diagUnit_apply_zero_one (u : Fˣ) {A : Work.Models.SL2 F}
    (hcomm : A * Work.Models.PSL2.diagUnit u = Work.Models.PSL2.diagUnit u * A) :
    (A : Matrix (Fin 2) (Fin 2) F) 0 1 * ((u⁻¹ : Fˣ) : F)
      = (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 0 1 := by
  have hmat : (((A * Work.Models.PSL2.diagUnit u : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F))
      = (((Work.Models.PSL2.diagUnit u * A : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F)) :=
    congrArg (fun B : Work.Models.SL2 F => (B : Matrix (Fin 2) (Fin 2) F)) hcomm
  have h := congrFun (congrFun hmat 0) 1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Work.Models.PSL2.diagUnit, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val', mul_zero, add_zero,
    zero_mul, Fin.isValue] at h
  simpa using h

/-- Entry computation: if `A` commutes with `diagUnit u`, then the `(1,0)`-entries satisfy
`A₁₀ * u = u⁻¹ * A₁₀`. -/
private lemma commute_diagUnit_apply_one_zero (u : Fˣ) {A : Work.Models.SL2 F}
    (hcomm : A * Work.Models.PSL2.diagUnit u = Work.Models.PSL2.diagUnit u * A) :
    (A : Matrix (Fin 2) (Fin 2) F) 1 0 * (u : F)
      = ((u⁻¹ : Fˣ) : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  have hmat : (((A * Work.Models.PSL2.diagUnit u : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F))
      = (((Work.Models.PSL2.diagUnit u * A : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F)) :=
    congrArg (fun B : Work.Models.SL2 F => (B : Matrix (Fin 2) (Fin 2) F)) hcomm
  have h := congrFun (congrFun hmat 1) 0
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Work.Models.PSL2.diagUnit, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val', mul_zero, add_zero,
    zero_mul, Fin.isValue] at h
  simpa using h

/-- Converse direction: an element of `D` commutes with any `diagUnit u`. -/
private lemma commute_diagUnit_of_mem_D (u : Fˣ) {A : Work.Models.SL2 F}
    (hA : A ∈ Work.Models.PSL2.D (F := F)) :
    A * Work.Models.PSL2.diagUnit u = Work.Models.PSL2.diagUnit u * A :=
  inD_mul_comm hA (Work.Models.PSL2.diagUnit_mem u)

/-- If `u + u⁻¹ ≠ 0`, an element of `SL(2,F)` commuting with `diag(u,u⁻¹)` is diagonal. -/
private lemma mem_D_of_commute_diagUnit (u : Fˣ)
    (hu : (u : F) + ((u⁻¹ : Fˣ) : F) ≠ 0) {A : Work.Models.SL2 F}
    (hcomm : A * Work.Models.PSL2.diagUnit u = Work.Models.PSL2.diagUnit u * A) :
    A ∈ Work.Models.PSL2.D (F := F) := by
  have h01 := commute_diagUnit_apply_zero_one u hcomm
  have h10 := commute_diagUnit_apply_one_zero u hcomm
  have hb : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have h01' : (A : Matrix (Fin 2) (Fin 2) F) 0 1 * ((u⁻¹ : Fˣ) : F)
        = (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (u : F) := by rw [h01, mul_comm]
    have hzero : (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (((u⁻¹ : Fˣ) : F) - (u : F)) = 0 := by
      rw [mul_sub, h01', sub_self]
    have hne : (((u⁻¹ : Fˣ) : F) - (u : F)) ≠ 0 := by
      rw [CharTwo.sub_eq_add, add_comm]; exact hu
    exact (mul_eq_zero.mp hzero).resolve_right hne
  have hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h10' : (A : Matrix (Fin 2) (Fin 2) F) 1 0 * (u : F)
        = (A : Matrix (Fin 2) (Fin 2) F) 1 0 * ((u⁻¹ : Fˣ) : F) := by rw [h10, mul_comm]
    have hzero : (A : Matrix (Fin 2) (Fin 2) F) 1 0 * ((u : F) - ((u⁻¹ : Fˣ) : F)) = 0 := by
      rw [mul_sub, h10', sub_self]
    have hne : ((u : F) - ((u⁻¹ : Fˣ) : F)) ≠ 0 := by
      rw [CharTwo.sub_eq_add]; exact hu
    exact (mul_eq_zero.mp hzero).resolve_right hne
  rw [Work.Models.PSL2.mem_D_iff']
  exact ⟨hb, hc⟩

/-- The centraliser in `SL(2,F)` (`F` of characteristic `2`) of a diagonal unit
`diag(u, u⁻¹)` is the full diagonal torus `D`, provided `u + u⁻¹ ≠ 0`.

Direct entry computation: for `A = !![a,b;c,d]`, the equation `A * diag(u,u⁻¹) = diag(u,u⁻¹) * A`
reads `b * u⁻¹ = u * b` and `c * u = u⁻¹ * c`, i.e. `b * (u + u⁻¹) = 0` and `c * (u + u⁻¹) = 0`;
since `u + u⁻¹ ≠ 0` is a unit, `b = c = 0`.  Conversely diagonal matrices commute, as they are
the image of the abelian group `Fˣ`. -/
theorem centralizer_diagUnit_eq_D {F : Type*} [Field F] [CharP F 2] (u : Fˣ)
    (hu : (u : F) + ((u⁻¹ : Fˣ) : F) ≠ 0) :
    Subgroup.centralizer ({Work.Models.PSL2.diagUnit u} : Set (Work.Models.SL2 F))
      = Work.Models.PSL2.D (F := F) := by
  apply le_antisymm
  · intro A hA
    rw [Subgroup.mem_centralizer_singleton_iff] at hA
    exact mem_D_of_commute_diagUnit u hu hA
  · intro A hA
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_diagUnit_of_mem_D u hA

end Work.BSLit.BenderFacts2
