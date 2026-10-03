import Mathlib
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.Tensor
import Submission.Work.ORFlatness.rightFlat_of_retract

set_option autoImplicit false
set_option maxHeartbeats 1000000

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

/-!
# Flatness of projective right modules

We prove that a projective right `R`-module `X` over an arbitrary ring `R` is right flat
(`Work.ORFlatness.RightFlat`, i.e. tensoring on the left by `X` preserves injective maps
of left `R`-modules), by exhibiting `X` as a retract of the free right module
`X →₀ Rᵐᵒᵖ` and using:

* `Work.ORFlatness.rightFlat_finsupp` : every free right module `ι →₀ Rᵐᵒᵖ` is right flat;
* `Work.ORFlatness.rightFlat_of_retract` : right flatness descends to retracts.

The free case rests on the computation of the balanced tensor product
`BalTensor R (ι →₀ Rᵐᵒᵖ) N` as `ι →₀ N` (the map `phi` below, with computation rule
`mk x n ↦ x.mapRange (fun c => c.unop • n)`), for which the induced map `id ⊗ g` is
carried to `Finsupp.mapRange g`.
-/

noncomputable section

variable {R : Type u} [Ring R] {ι : Type u} {N : Type u} [AddCommGroup N] [Module R N]

/-- The additive map `Rᵐᵒᵖ →+ N` given by `c ↦ c.unop • n`. -/
def unopSmulHom (n : N) : Rᵐᵒᵖ →+ N where
  toFun c := c.unop • n
  map_zero' := by simp
  map_add' a b := by simp [add_smul]

/-- The function underlying the isomorphism `BalTensor R (ι →₀ Rᵐᵒᵖ) N ≃+ (ι →₀ N)`:
`mk x n ↦ x.mapRange (fun c => c.unop • n)`, i.e. `mk (single i 1) n ↦ single i n`. -/
def phiFun (x : ι →₀ Rᵐᵒᵖ) (n : N) : ι →₀ N :=
  (Finsupp.mapRange.addMonoidHom (unopSmulHom (N := N) n)) x

@[simp] theorem phiFun_apply (x : ι →₀ Rᵐᵒᵖ) (n : N) (i : ι) :
    phiFun x n i = (x i).unop • n := by
  rw [phiFun, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply]
  rfl

theorem phiFun_add_left (x x' : ι →₀ Rᵐᵒᵖ) (n : N) :
    phiFun (x + x') n = phiFun x n + phiFun x' n := by
  rw [phiFun, phiFun, phiFun, map_add]

theorem phiFun_zsmul_left (z : ℤ) (x : ι →₀ Rᵐᵒᵖ) (n : N) :
    phiFun (z • x) n = z • phiFun x n := by
  rw [phiFun, phiFun, map_zsmul]

theorem phiFun_add_right (x : ι →₀ Rᵐᵒᵖ) (n n' : N) :
    phiFun x (n + n') = phiFun x n + phiFun x n' := by
  ext i
  simp [smul_add]

theorem phiFun_zsmul_right (z : ℤ) (x : ι →₀ Rᵐᵒᵖ) (n : N) :
    phiFun x (z • n) = z • phiFun x n := by
  ext i
  simp only [phiFun_apply, Finsupp.smul_apply]
  rw [smul_comm]

/-- The ℤ-bilinear map `(x, n) ↦ x.mapRange (fun c => c.unop • n)`. -/
def phiBilin : (ι →₀ Rᵐᵒᵖ) →ₗ[ℤ] N →ₗ[ℤ] (ι →₀ N) :=
  LinearMap.mk₂ ℤ phiFun phiFun_add_left phiFun_zsmul_left phiFun_add_right phiFun_zsmul_right

@[simp] theorem phiBilin_apply (x : ι →₀ Rᵐᵒᵖ) (n : N) : phiBilin x n = phiFun x n := by
  rw [phiBilin, LinearMap.mk₂_apply]

/-- `phiBilin` respects the balancing relation defining `BalTensor R (ι →₀ Rᵐᵒᵖ) N`. -/
theorem phiBilin_bal (x : ι →₀ Rᵐᵒᵖ) (n : N) (r : R) :
    phiBilin (op r • x) n = phiBilin x (r • n) := by
  rw [phiBilin_apply, phiBilin_apply]
  ext i
  simp only [phiFun_apply, Finsupp.smul_apply]
  simp [MulOpposite.unop_mul, mul_smul]

/-- The additive map `BalTensor R (ι →₀ Rᵐᵒᵖ) N →+ (ι →₀ N)` carrying `mk x n` to
`x.mapRange (fun c => c.unop • n)`; a right inverse of `psi` below. -/
def phi : BalTensor R (ι →₀ Rᵐᵒᵖ) N →+ (ι →₀ N) :=
  BalTensor.lift R phiBilin (fun x n r => phiBilin_bal x n r)

theorem phi_mk (x : ι →₀ Rᵐᵒᵖ) (n : N) : phi (BalTensor.mk R x n) = phiFun x n := by
  rw [phi, BalTensor.lift_mk, phiBilin_apply]

/-- The additive map `(ι →₀ N) →+ BalTensor R (ι →₀ Rᵐᵒᵖ) N` carrying `single i n` to
`mk (single i 1) n`; a left inverse of `phi`. -/
def psi : (ι →₀ N) →+ BalTensor R (ι →₀ Rᵐᵒᵖ) N :=
  Finsupp.liftAddHom (fun i => BalTensor.mkRight R (Finsupp.single i (1 : Rᵐᵒᵖ)))

theorem psi_single (i : ι) (n : N) :
    psi (Finsupp.single i n) = BalTensor.mk R (Finsupp.single i (1 : Rᵐᵒᵖ)) n := by
  rw [psi, Finsupp.liftAddHom_apply_single]
  rfl

theorem phiFun_single (i : ι) (c : Rᵐᵒᵖ) (n : N) :
    phiFun (Finsupp.single i c) n = Finsupp.single i (c.unop • n) := by
  rw [phiFun, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single]
  rfl

theorem psi_phiFun (x : ι →₀ Rᵐᵒᵖ) (n : N) :
    psi (phiFun x n) = BalTensor.mk R x n := by
  have hA : (psi (R := R) (ι := ι) (N := N)).comp
        (Finsupp.mapRange.addMonoidHom (unopSmulHom (N := N) n) :
          (ι →₀ Rᵐᵒᵖ) →+ (ι →₀ N))
      = BalTensor.mkLeft R n := by
    apply Finsupp.addHom_ext
    intro i c
    show psi (phiFun (Finsupp.single i c) n) = BalTensor.mk R (Finsupp.single i c) n
    have hx : (op c.unop : Rᵐᵒᵖ) • (Finsupp.single i (1 : Rᵐᵒᵖ)) = Finsupp.single i c := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one, MulOpposite.op_unop]
    rw [phiFun_single, psi_single, ← BalTensor.mk_smul_right, hx]
  exact DFunLike.congr_fun hA x

theorem psi_phi (z : BalTensor R (ι →₀ Rᵐᵒᵖ) N) : psi (phi z) = z := by
  have hC : psi.comp (phi (R := R) (ι := ι) (N := N)) = AddMonoidHom.id _ := by
    apply BalTensor.ext R
    intro x n
    rw [AddMonoidHom.comp_apply, phi_mk, AddMonoidHom.id_apply, psi_phiFun]
  exact DFunLike.congr_fun hC z

/-- `phi : BalTensor R (ι →₀ Rᵐᵒᵖ) N →+ (ι →₀ N)`, the computation of the balanced
tensor product of a free right module with a left module, is injective. -/
theorem phi_injective : Function.Injective (phi (R := R) (ι := ι) (N := N)) := by
  intro z w hzw
  rw [← psi_phi z, ← psi_phi w, hzw]

end

/-- Every free right `R`-module `ι →₀ Rᵐᵒᵖ` is right flat: the map `phi`s above turns
`BalTensor.map R id g` into `Finsupp.mapRange g`, which is injective whenever `g` is. -/
theorem rightFlat_finsupp (R : Type u) [Ring R] (ι : Type u) :
    RightFlat R (ι →₀ Rᵐᵒᵖ) := by
  unfold RightFlat
  intro M N instM modM instN modN g hg
  let G : (ι →₀ M) →+ (ι →₀ N) := Finsupp.mapRange.addMonoidHom g.toAddMonoidHom
  have hG : ∀ v, G v = Finsupp.mapRange (g : M → N) (map_zero g) v := by
    intro v
    rw [Finsupp.mapRange.addMonoidHom_apply]
    rfl
  -- the square `(Finsupp.mapRange g) ∘ phi = phi ∘ (id ⊗ g)` commutes
  have key : G.comp (phi (R := R) (ι := ι) (N := M))
      = (phi (R := R) (ι := ι) (N := N)).comp
        (BalTensor.map R (LinearMap.id : (ι →₀ Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (ι →₀ Rᵐᵒᵖ)) g) := by
    apply BalTensor.ext R
    intro x n
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, phi_mk, BalTensor.map_mk,
      LinearMap.id_apply, phi_mk, hG]
    ext i
    simp [phiFun_apply, map_smul]
  have key' : ∀ v, Finsupp.mapRange (g : M → N) (map_zero g) (phi (R := R) (ι := ι) (N := M) v)
      = (phi (R := R) (ι := ι) (N := N))
          (BalTensor.map R (LinearMap.id : (ι →₀ Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (ι →₀ Rᵐᵒᵖ)) g v) := by
    intro v
    rw [← hG (phi (R := R) (ι := ι) (N := M) v)]
    exact DFunLike.congr_fun key v
  have hinj : Function.Injective (Finsupp.mapRange (g : M → N) (map_zero g)) :=
    Finsupp.mapRange_injective (α := ι) (g : M → N) (map_zero g) hg
  intro z w hzw
  have h : Finsupp.mapRange (g : M → N) (map_zero g) (phi (R := R) (ι := ι) (N := M) z)
      = Finsupp.mapRange (g : M → N) (map_zero g) (phi (R := R) (ι := ι) (N := M) w) := by
    rw [key' z, key' w, hzw]
  exact (phi_injective (R := R) (ι := ι) (N := M)) (hinj h)

/-- A projective **right** `R`-module is right flat: tensoring on the left by it preserves injective maps of left modules. (`Work.ORFlatness.RightFlat` is defined in `Submission.Work.ORFlatness.Flat`.)

Suggested route, all inside this file: (i) prove the auxiliary isomorphism `balTensor_finsupp_equiv : BalTensor R (ι →₀ Rᵐᵒᵖ) N ≃+ (ι →₀ N)` with computation rule `mk (Finsupp.single i 1) n ↦ Finsupp.single i n`, sending `mk x n` to `x.mapRange (fun c => c.unop • n)`; (ii) deduce `RightFlat R (ι →₀ Rᵐᵒᵖ)` (under `id ⊗ f` the iso is carried to `Finsupp.mapRange f`, which is injective for injective `f`); (iii) prove that right flatness is inherited by retracts: if `r ∘ i = id` then `map i id` is injective for a right-flat `Y` (`(map i id) ∘ (id ⊗ f) = (id ⊗ f) ∘ (map i id)` by functoriality in both variables, then apply `map r id` and use `map_comp`, `map_id` as in `Work.ORFlatness.injective_map_of_retract`); (iv) conclude with `Module.projective_def`, which says that `Module.Projective Rᵐᵒᵖ X` gives a section `s : X → (X →₀ Rᵐᵒᵖ)` of `Finsupp.linearCombination Rᵐᵒᵖ id`, i.e. exhibits `X` as a retract of the free module `X →₀ Rᵐᵒᵖ`. -/
theorem rightFlat_of_projective (R : Type u) [Ring R] {X : Type u} [AddCommGroup X]
    [Module Rᵐᵒᵖ X] [Module.Projective Rᵐᵒᵖ X] :
    Work.ORFlatness.RightFlat R X := by
  -- `X` is a retract of the free right module `X →₀ Rᵐᵒᵖ`
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (Finsupp.linearCombination Rᵐᵒᵖ (id : X → X)) (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X)
    (Finsupp.linearCombination_surjective Rᵐᵒᵖ Function.surjective_id)
  exact rightFlat_of_retract (rightFlat_finsupp R X) s
    (Finsupp.linearCombination Rᵐᵒᵖ (id : X → X)) hs

end Work.ORFlatness
