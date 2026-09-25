import Mathlib

/-!
# Setup for the Golod–Shafarevich inequality

Definitions and elementary facts used in the proof of the Golod–Shafarevich inequality
`4 * r > d ^ 2` for finite `p`-groups.
-/

open scoped MonoidAlgebra

namespace Work.GolodShafarevich

section Augmentation

variable (R : Type*) [CommSemiring R] (M : Type*) [Monoid M]

/-- The augmentation algebra map `R[M] →ₐ[R] R`, sending every `m : M` to `1`. -/
noncomputable def augAlgHom : MonoidAlgebra R M →ₐ[R] R :=
  MonoidAlgebra.lift R R M 1

/-- The augmentation ideal of the monoid algebra `R[M]`. -/
noncomputable def augIdeal : Ideal (MonoidAlgebra R M) :=
  RingHom.ker (augAlgHom R M)

theorem mem_augIdeal_iff {x : MonoidAlgebra R M} :
    x ∈ augIdeal R M ↔ augAlgHom R M x = 0 := Iff.rfl

@[simp]
theorem augAlgHom_of (m : M) : augAlgHom R M (MonoidAlgebra.of R M m) = 1 :=
  MonoidAlgebra.lift_of 1 m

@[simp]
theorem augAlgHom_one : augAlgHom R M 1 = 1 := map_one (augAlgHom R M)

theorem augAlgHom_apply (x : MonoidAlgebra R M) :
    augAlgHom R M x = x.coeff.sum (fun _ r => r) := by
  rw [augAlgHom, MonoidAlgebra.lift_apply]
  simp

end Augmentation

section AugmentationRing

variable (R : Type*) [CommRing R] (M : Type*) [Monoid M]

theorem of_sub_one_mem_augIdeal (m : M) :
    MonoidAlgebra.of R M m - 1 ∈ augIdeal R M := by
  rw [mem_augIdeal_iff, map_sub, augAlgHom_of, map_one, sub_self]

theorem sub_smul_one_mem_span (x : MonoidAlgebra R M) :
    x - (augAlgHom R M x) • (1 : MonoidAlgebra R M) ∈
      Submodule.span R (Set.range (fun m : M => MonoidAlgebra.of R M m - 1)) := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
    have h : MonoidAlgebra.of R M m - (augAlgHom R M (MonoidAlgebra.of R M m)) •
        (1 : MonoidAlgebra R M) = MonoidAlgebra.of R M m - 1 := by
      rw [augAlgHom_of, one_smul]
    rw [h]
    exact Submodule.subset_span ⟨m, rfl⟩
  | add x y hx hy =>
    have h : (x + y : MonoidAlgebra R M) - (augAlgHom R M (x + y)) • 1 =
        (x - (augAlgHom R M x) • 1) + (y - (augAlgHom R M y) • 1) := by
      rw [map_add, add_smul]
      abel
    rw [h]
    exact Submodule.add_mem _ hx hy
  | smul r x hx =>
    have h : (r • x : MonoidAlgebra R M) - (augAlgHom R M (r • x)) • 1 =
        r • (x - (augAlgHom R M x) • 1) := by
      rw [map_smul, smul_eq_mul, ← smul_smul, smul_sub]
    rw [h]
    exact Submodule.smul_mem _ r hx

/-- The augmentation ideal is spanned (over `R`) by the elements `of m - 1`. -/
theorem augIdeal_eq_span :
    (augIdeal R M).restrictScalars R =
      Submodule.span R (Set.range (fun m : M => MonoidAlgebra.of R M m - 1)) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have h := sub_smul_one_mem_span R M x
    have hx' : augAlgHom R M x = 0 := hx
    simpa [hx'] using h
  · rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact of_sub_one_mem_augIdeal R M m

end AugmentationRing

section Fox

variable (R : Type*) [CommRing R] {α : Type*}

/-- Auxiliary Fox derivative (free derivative) on words. -/
noncomputable def foxDerivAux [DecidableEq α] (i : α) :
    List (α × Bool) → MonoidAlgebra R (FreeGroup α)
  | [] => 0
  | (j, true) :: w =>
      (if i = j then (1 : MonoidAlgebra R (FreeGroup α)) else 0) +
        MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of j) * foxDerivAux i w
  | (j, false) :: w =>
      -(MonoidAlgebra.of R (FreeGroup α) ((FreeGroup.of j)⁻¹) *
          (if i = j then (1 : MonoidAlgebra R (FreeGroup α)) else 0)) +
        MonoidAlgebra.of R (FreeGroup α) ((FreeGroup.of j)⁻¹) * foxDerivAux i w

section

variable {R}

theorem foxDerivAux_nil [DecidableEq α] (i : α) : foxDerivAux R i [] = 0 := rfl

theorem mk_cons_true {β : Type*} (j : β) (L : List (β × Bool)) :
    FreeGroup.mk ((j, true) :: L) = FreeGroup.of j * FreeGroup.mk L := rfl

theorem mk_cons_false {β : Type*} (j : β) (L : List (β × Bool)) :
    FreeGroup.mk ((j, false) :: L) = (FreeGroup.of j)⁻¹ * FreeGroup.mk L := rfl

theorem of_mul_of_inv [DecidableEq α] (j : α) :
    MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of j) *
      MonoidAlgebra.of R (FreeGroup α) ((FreeGroup.of j)⁻¹) = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem of_inv_mul_of [DecidableEq α] (j : α) :
    MonoidAlgebra.of R (FreeGroup α) ((FreeGroup.of j)⁻¹) *
      MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of j) = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

/-- The two-letter cancellation step for the Fox derivative. -/
theorem foxDerivAux_pair [DecidableEq α] (i x : α) (b : Bool) (L : List (α × Bool)) :
    foxDerivAux R i ((x, b) :: (x, !b) :: L) = foxDerivAux R i L := by
  cases b
  · simp only [foxDerivAux, Bool.not_false]
    rw [mul_add, ← mul_assoc, of_inv_mul_of x, one_mul]
    abel
  · simp only [foxDerivAux, Bool.not_true]
    rw [mul_add, mul_neg, ← mul_assoc, ← mul_assoc, of_mul_of_inv x, one_mul, one_mul]
    abel

theorem foxDerivAux_append [DecidableEq α] (i : α) (L₁ L₂ : List (α × Bool)) :
    foxDerivAux R i (L₁ ++ L₂) = foxDerivAux R i L₁ +
      MonoidAlgebra.of R (FreeGroup α) (FreeGroup.mk L₁) * foxDerivAux R i L₂ := by
  induction L₁ with
  | nil =>
    simp only [List.nil_append, List.append_nil, foxDerivAux, zero_add]
    rw [show FreeGroup.mk ([] : List (α × Bool)) = 1 from FreeGroup.one_eq_mk.symm, map_one,
      one_mul]
  | cons hd tl ih =>
    obtain ⟨j, b⟩ := hd
    cases b
    · simp only [List.cons_append, foxDerivAux, mk_cons_false j tl, map_mul, ih]
      noncomm_ring
    · simp only [List.cons_append, foxDerivAux, mk_cons_true j tl, map_mul, ih]
      noncomm_ring

theorem foxDerivAux_cancel [DecidableEq α] (i : α) (L₁ L₂ : List (α × Bool)) (x : α)
    (b : Bool) :
    foxDerivAux R i (L₁ ++ (x, b) :: (x, !b) :: L₂) = foxDerivAux R i (L₁ ++ L₂) := by
  simp only [foxDerivAux_append, foxDerivAux_pair]

theorem foxDerivAux_step [DecidableEq α] (i : α) {L₁ L₂ : List (α × Bool)}
    (h : FreeGroup.Red.Step L₁ L₂) : foxDerivAux R i L₁ = foxDerivAux R i L₂ := by
  cases h with
  | not => exact foxDerivAux_cancel i _ _ _ _

end

/-- The Fox derivative (free derivative) of an element of a free group,
with respect to the generator `i`. -/
noncomputable def foxDeriv [DecidableEq α] (i : α) :
    FreeGroup α → MonoidAlgebra R (FreeGroup α) :=
  Quot.lift (foxDerivAux R i) fun _ _ h => foxDerivAux_step i h

variable {R}

@[simp]
theorem foxDeriv_mk [DecidableEq α] (i : α) (L : List (α × Bool)) :
    foxDeriv R i (FreeGroup.mk L) = foxDerivAux R i L := rfl

theorem foxDeriv_mul [DecidableEq α] (i : α) (w₁ w₂ : FreeGroup α) :
    foxDeriv R i (w₁ * w₂) = foxDeriv R i w₁ +
      MonoidAlgebra.of R (FreeGroup α) w₁ * foxDeriv R i w₂ := by
  induction w₁ using Quot.inductionOn with
  | _ L₁ =>
    induction w₂ using Quot.inductionOn with
    | _ L₂ => simp [FreeGroup.mul_mk, foxDerivAux_append]

@[simp]
theorem foxDeriv_one [DecidableEq α] (i : α) : foxDeriv R i (1 : FreeGroup α) = 0 := rfl

theorem foxDeriv_of [DecidableEq α] (i j : α) :
    foxDeriv R i (FreeGroup.of j) =
      (if i = j then (1 : MonoidAlgebra R (FreeGroup α)) else 0) := by
  rw [show FreeGroup.of j = FreeGroup.mk [(j, true)] from rfl, foxDeriv_mk]
  simp only [foxDerivAux, foxDerivAux_nil, mul_zero, add_zero]

theorem foxDeriv_inv [DecidableEq α] (i : α) (w : FreeGroup α) :
    foxDeriv R i (w⁻¹) =
      -(MonoidAlgebra.of R (FreeGroup α) (w⁻¹) * foxDeriv R i w) := by
  have h := foxDeriv_mul (R := R) i (w⁻¹) w
  rw [inv_mul_cancel, foxDeriv_one] at h
  exact eq_neg_iff_add_eq_zero.mpr h.symm

theorem foxDeriv_fundamental [Fintype α] [DecidableEq α] (w : FreeGroup α) :
    ∑ i : α, foxDeriv R i w * (MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of i) - 1) =
      MonoidAlgebra.of R (FreeGroup α) w - 1 := by
  induction w using FreeGroup.induction_on with
  | one =>
    rw [Finset.sum_eq_zero fun i _ => by rw [foxDeriv_one, zero_mul], map_one, sub_self]
  | of j =>
    rw [Finset.sum_eq_single j]
    · simp [foxDeriv_of]
    · intro b _ hb
      simp [foxDeriv_of, hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  | inv_of j ih =>
    have h1 : ∀ i : α, foxDeriv R i (FreeGroup.of j)⁻¹ *
          (MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of i) - 1) =
        -(MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of j)⁻¹ *
          (foxDeriv R i (FreeGroup.of j) *
            (MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of i) - 1))) := by
      intro i
      rw [foxDeriv_inv, neg_mul, mul_assoc]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_neg_distrib, ← Finset.mul_sum, ih,
      mul_sub, mul_one, of_inv_mul_of j, neg_sub]
  | mul x y hx hy =>
    have key :
        (∑ i : α, foxDeriv R i (x * y) *
            (MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of i) - 1)) =
          (∑ i : α, foxDeriv R i x *
              (MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of i) - 1)) +
            MonoidAlgebra.of R (FreeGroup α) x *
              (∑ i : α, foxDeriv R i y *
                (MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of i) - 1)) := by
      have h1 : ∀ i : α, foxDeriv R i (x * y) *
            (MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of i) - 1) =
          foxDeriv R i x * (MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of i) - 1) +
            (MonoidAlgebra.of R (FreeGroup α) x * foxDeriv R i y) *
              (MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of i) - 1) := by
        intro i
        rw [foxDeriv_mul, add_mul]
      have h2 : ∀ i : α, (MonoidAlgebra.of R (FreeGroup α) x * foxDeriv R i y) *
            (MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of i) - 1) =
          MonoidAlgebra.of R (FreeGroup α) x *
            (foxDeriv R i y *
              (MonoidAlgebra.of R (FreeGroup α) (FreeGroup.of i) - 1)) :=
        fun i => mul_assoc _ _ _
      rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun i _ => h2 i), ← Finset.mul_sum]
    rw [key, hx, hy, mul_sub, mul_one, map_mul]
    abel

end Fox

end Work.GolodShafarevich
