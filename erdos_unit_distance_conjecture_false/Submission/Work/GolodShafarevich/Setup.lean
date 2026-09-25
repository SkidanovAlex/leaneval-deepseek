import Submission.Work.GolodShafarevich.Defs

/-!
# Golod–Shafarevich setup, part II

The map `ψ : R[G]^d → R[G]`, `x ↦ ∑ xᵢ (φ(gᵢ) - 1)`, whose kernel is the relation module,
the derivative vectors `Vfun`, and exponent sums.
-/

open scoped MonoidAlgebra

namespace Work.GolodShafarevich

section ExpSum

variable {α : Type*} [DecidableEq α]

/-- The exponent-sum homomorphism `F(α) → (α → ℤ)`. -/
noncomputable def expSumHom : FreeGroup α →* Multiplicative (α → ℤ) :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (Pi.single j 1)

/-- The exponent sum of the generator `i` in a word. -/
noncomputable def expSum (i : α) (w : FreeGroup α) : ℤ :=
  Multiplicative.toAdd (expSumHom w) i

theorem expSum_of (i j : α) :
    expSum i (FreeGroup.of j) = if i = j then 1 else 0 := by
  rw [expSum, expSumHom, FreeGroup.lift_apply_of]
  simp [Pi.single_apply]

theorem expSum_mul (i : α) (w₁ w₂ : FreeGroup α) :
    expSum i (w₁ * w₂) = expSum i w₁ + expSum i w₂ := by
  simp [expSum]

theorem expSum_one (i : α) : expSum i (1 : FreeGroup α) = 0 := by
  simp [expSum]

theorem expSum_inv (i : α) (w : FreeGroup α) : expSum i (w⁻¹) = -expSum i w := by
  simp [expSum]

end ExpSum

section ExpSumAug

variable {R : Type*} [CommRing R] {α : Type*}

theorem augAlgHom_ite_one_zero (c : Prop) [Decidable c] :
    augAlgHom R (FreeGroup α)
        (if c then (1 : MonoidAlgebra R (FreeGroup α)) else 0) = if c then 1 else 0 := by
  split_ifs <;> simp

theorem foxDeriv_aug_mul [DecidableEq α] (i : α) (w₁ w₂ : FreeGroup α) :
    augAlgHom R (FreeGroup α) (foxDeriv R i (w₁ * w₂)) =
      augAlgHom R (FreeGroup α) (foxDeriv R i w₁) +
        augAlgHom R (FreeGroup α) (foxDeriv R i w₂) := by
  rw [foxDeriv_mul, map_add, map_mul, augAlgHom_of, one_mul]

theorem foxDeriv_aug_inv [DecidableEq α] (i : α) (w : FreeGroup α) :
    augAlgHom R (FreeGroup α) (foxDeriv R i (w⁻¹)) =
      -augAlgHom R (FreeGroup α) (foxDeriv R i w) := by
  rw [foxDeriv_inv, map_neg, map_mul, augAlgHom_of, one_mul]

/-- The exponent sum of `i` in `w` is the augmentation of the Fox derivative. -/
theorem expSum_cast_eq_aug (p : ℕ) [DecidableEq α] (i : α) (w : FreeGroup α) :
    ((expSum i w : ℤ) : ZMod p) =
      augAlgHom (ZMod p) (FreeGroup α) (foxDeriv (ZMod p) i w) := by
  induction w using FreeGroup.induction_on with
  | one => simp [expSum_one]
  | of j =>
    rw [expSum_of, foxDeriv_of, augAlgHom_ite_one_zero]
    split_ifs <;> simp
  | inv_of j ih =>
    rw [expSum_inv, foxDeriv_aug_inv, Int.cast_neg, ih]
  | mul x y ihx ihy =>
    rw [expSum_mul, foxDeriv_aug_mul, Int.cast_add, ihx, ihy]

end ExpSumAug

section GroupAlg

variable (R : Type*) [CommRing R] {d : ℕ} {G : Type*} [Group G]

/-- The algebra map `R[F_d] →ₐ[R] R[G]` induced by `φ : F_d →* G`. -/
noncomputable def groupAlgMap (φ : FreeGroup (Fin d) →* G) :
    MonoidAlgebra R (FreeGroup (Fin d)) →ₐ[R] MonoidAlgebra R G :=
  MonoidAlgebra.mapDomainAlgHom R R φ

@[simp]
theorem groupAlgMap_of (φ : FreeGroup (Fin d) →* G) (w : FreeGroup (Fin d)) :
    groupAlgMap R φ (MonoidAlgebra.of R (FreeGroup (Fin d)) w) =
      MonoidAlgebra.of R G (φ w) := by
  rw [groupAlgMap, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.mapDomain_single, MonoidAlgebra.of_apply]

theorem augAlgHom_groupAlgMap (φ : FreeGroup (Fin d) →* G)
    (x : MonoidAlgebra R (FreeGroup (Fin d))) :
    augAlgHom R G (groupAlgMap R φ x) = augAlgHom R (FreeGroup (Fin d)) x := by
  induction x using MonoidAlgebra.induction_on with
  | of w =>
    rw [groupAlgMap_of, augAlgHom_of, augAlgHom_of]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul r x hx => simp only [map_smul, hx]

/-- The element `φ(gᵢ) - 1` of the group algebra. -/
noncomputable def gGenSubOne (φ : FreeGroup (Fin d) →* G) (i : Fin d) :
    MonoidAlgebra R G :=
  groupAlgMap R φ (MonoidAlgebra.of R (FreeGroup (Fin d)) (FreeGroup.of i)) - 1

theorem mem_augIdeal_gGenSubOne (φ : FreeGroup (Fin d) →* G) (i : Fin d) :
    gGenSubOne R φ i ∈ augIdeal R G := by
  rw [mem_augIdeal_iff, gGenSubOne, map_sub, groupAlgMap_of, augAlgHom_of, map_one, sub_self]

/-- The linear map `R[G]^d → R[G]`, `x ↦ ∑ᵢ xᵢ (φ(gᵢ) - 1)`. -/
noncomputable def psi (φ : FreeGroup (Fin d) →* G) :
    (Fin d → MonoidAlgebra R G) →ₗ[MonoidAlgebra R G] MonoidAlgebra R G where
  toFun x := ∑ i, x i * gGenSubOne R φ i
  map_add' x y := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, RingHom.id_apply]

theorem psi_apply (φ : FreeGroup (Fin d) →* G) (x : Fin d → MonoidAlgebra R G) :
    psi R φ x = ∑ i, x i * gGenSubOne R φ i := rfl

/-- The derivative vector of a word `w ∈ F_d`. -/
noncomputable def Vfun (φ : FreeGroup (Fin d) →* G) :
    FreeGroup (Fin d) → (Fin d → MonoidAlgebra R G) :=
  fun w i => groupAlgMap R φ (foxDeriv R i w)

theorem Vfun_apply (φ : FreeGroup (Fin d) →* G) (w : FreeGroup (Fin d)) (i : Fin d) :
    Vfun R φ w i = groupAlgMap R φ (foxDeriv R i w) := rfl

theorem Vfun_mul (φ : FreeGroup (Fin d) →* G) (w₁ w₂ : FreeGroup (Fin d)) (i : Fin d) :
    Vfun R φ (w₁ * w₂) i =
      Vfun R φ w₁ i + MonoidAlgebra.of R G (φ w₁) * Vfun R φ w₂ i := by
  simp only [Vfun_apply, foxDeriv_mul, map_add, map_mul, groupAlgMap_of]

theorem psi_Vfun (φ : FreeGroup (Fin d) →* G) (w : FreeGroup (Fin d)) :
    psi R φ (Vfun R φ w) = MonoidAlgebra.of R G (φ w) - 1 := by
  have h1 : ∀ i : Fin d, gGenSubOne R φ i =
      groupAlgMap R φ (MonoidAlgebra.of R (FreeGroup (Fin d)) (FreeGroup.of i) - 1) :=
    fun i => by rw [gGenSubOne, map_sub, map_one]
  have h : (∑ i, Vfun R φ w i * gGenSubOne R φ i) =
      groupAlgMap R φ (∑ i : Fin d, foxDeriv R i w *
        (MonoidAlgebra.of R (FreeGroup (Fin d)) (FreeGroup.of i) - 1)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Vfun_apply, h1 i, ← map_mul]
  rw [psi_apply, h, foxDeriv_fundamental, map_sub, groupAlgMap_of, map_one]

theorem Vfun_one (φ : FreeGroup (Fin d) →* G) : Vfun R φ 1 = 0 := by
  funext i
  show groupAlgMap R φ (foxDeriv R i 1) = 0
  rw [foxDeriv_one, map_zero]

theorem Vfun_inv (φ : FreeGroup (Fin d) →* G) (w : FreeGroup (Fin d)) :
    Vfun R φ (w⁻¹) = -((MonoidAlgebra.of R G ((φ w)⁻¹)) • Vfun R φ w) := by
  funext i
  show groupAlgMap R φ (foxDeriv R i (w⁻¹)) = _
  rw [foxDeriv_inv, map_neg, map_mul, groupAlgMap_of, map_inv]
  rfl

theorem Vfun_mul_inv (φ : FreeGroup (Fin d) →* G) (g : FreeGroup (Fin d)) :
    Vfun R φ g + MonoidAlgebra.of R G (φ g) • Vfun R φ (g⁻¹) = 0 := by
  funext i
  have h := Vfun_mul R φ g (g⁻¹) i
  rw [mul_inv_cancel, congr_fun (Vfun_one R φ) i] at h
  simpa using h.symm

/-- For an element `n` in the kernel of `φ`, the derivative vectors are equivariant
under conjugation. -/
theorem Vfun_conj (φ : FreeGroup (Fin d) →* G) {g n : FreeGroup (Fin d)} (hn : φ n = 1) :
    Vfun R φ (g * n * g⁻¹) = MonoidAlgebra.of R G (φ g) • Vfun R φ n := by
  funext i
  show groupAlgMap R φ (foxDeriv R i (g * n * g⁻¹)) = _
  rw [foxDeriv_mul, foxDeriv_mul]
  simp only [map_add, map_mul, groupAlgMap_of, hn, map_one, mul_one]
  rw [← Vfun_apply R φ g i, ← Vfun_apply R φ n i, ← Vfun_apply R φ (g⁻¹) i, Pi.smul_apply]
  have h0 : Vfun R φ g i + MonoidAlgebra.of R G (φ g) * Vfun R φ (g⁻¹) i = 0 := by
    have h := congr_fun (Vfun_mul_inv R φ g) i
    simpa using h
  rw [show Vfun R φ g i + MonoidAlgebra.of R G (φ g) * Vfun R φ n i +
        MonoidAlgebra.of R G (φ g) * Vfun R φ (g⁻¹) i =
      (Vfun R φ g i + MonoidAlgebra.of R G (φ g) * Vfun R φ (g⁻¹) i) +
        MonoidAlgebra.of R G (φ g) * Vfun R φ n i from by abel, h0, zero_add]
  simp

end GroupAlg

end Work.GolodShafarevich
