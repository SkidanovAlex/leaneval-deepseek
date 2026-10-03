import Mathlib
import Submission.Work.ORFlatness.Flat

set_option autoImplicit false
set_option maxHeartbeats 1000000

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

/-! ## The isomorphism `BalTensor R X (ι →₀ R) ≃+ (ι →₀ X)`

For a right `R`-module `X` and an index type `ι`, the balanced tensor product
`BalTensor R X (ι →₀ R)` is additively isomorphic to `ι →₀ X`, via
`mk x y ↦ y.mapRange (fun r => op r • x)`, so that `mk x (single i 1) ↦ single i x`.
This is the mirror of `Work.ORFlatness.balTensorFinsuppEquiv`. -/

/-- `r ↦ op r • x`, as an additive homomorphism `R →+ X`. -/
private def rightSmulHom (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (x : X) : R →+ X where
  toFun r := op r • x
  map_zero' := by simp
  map_add' r s := by simp [add_smul]

private theorem rightSmulHom_apply (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (x : X) (r : R) : rightSmulHom R X x r = op r • x := rfl

private theorem mapRange_rightSmulHom_add (R : Type u) [Ring R] (X : Type u)
    [AddCommGroup X] [Module Rᵐᵒᵖ X] (ι : Type u) (x x' : X) :
    Finsupp.mapRange.addMonoidHom (ι := ι) (rightSmulHom R X (x + x')) =
      Finsupp.mapRange.addMonoidHom (ι := ι) (rightSmulHom R X x) +
        Finsupp.mapRange.addMonoidHom (ι := ι) (rightSmulHom R X x') := by
  apply AddMonoidHom.ext
  intro y
  apply Finsupp.ext
  intro i
  simp only [Finsupp.mapRange.addMonoidHom_apply, AddMonoidHom.add_apply, Finsupp.add_apply,
    Finsupp.mapRange_apply, rightSmulHom_apply]
  exact smul_add _ x x'

private noncomputable def fwdBilin (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (ι : Type u) : X →ₗ[ℤ] (ι →₀ R) →ₗ[ℤ] (ι →₀ X) :=
  (AddMonoidHom.mk' (fun x : X =>
      (Finsupp.mapRange.addMonoidHom (ι := ι) (rightSmulHom R X x)).toIntLinearMap)
    (fun x x' => by
      apply LinearMap.ext
      intro y
      exact congrArg (fun f : (ι →₀ R) →+ (ι →₀ X) => f y)
        (mapRange_rightSmulHom_add R X ι x x'))).toIntLinearMap

private theorem fwdBilin_apply (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (ι : Type u) (x : X) (n : ι →₀ R) :
    fwdBilin R X ι x n = Finsupp.mapRange (fun r => op r • x) (by simp) n := by
  show (Finsupp.mapRange.addMonoidHom (ι := ι) (rightSmulHom R X x)) n = _
  rw [Finsupp.mapRange.addMonoidHom_apply]
  rfl

private noncomputable def balFwdFinsupp (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (ι : Type u) : BalTensor R X (ι →₀ R) →+ (ι →₀ X) :=
  BalTensor.lift R (fwdBilin R X ι) (by
    intro x n r
    rw [fwdBilin_apply, fwdBilin_apply]
    apply Finsupp.ext
    intro i
    simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul,
      MulOpposite.op_mul, mul_smul])

private theorem balFwdFinsupp_mk (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (ι : Type u) (x : X) (n : ι →₀ R) :
    balFwdFinsupp R X ι (BalTensor.mk R x n)
      = Finsupp.mapRange (fun r => op r • x) (by simp) n := by
  rw [balFwdFinsupp, BalTensor.lift_mk, fwdBilin_apply]

private theorem mapRange_rightSmulHom_eq (R : Type u) [Ring R] (X : Type u)
    [AddCommGroup X] [Module Rᵐᵒᵖ X] (ι : Type u) (x : X) (n : ι →₀ R) :
    Finsupp.mapRange (fun r => op r • x) (by simp) n
      = (Finsupp.mapRange.addMonoidHom (ι := ι) (rightSmulHom R X x)) n := by
  rw [Finsupp.mapRange.addMonoidHom_apply]
  rfl

private noncomputable def balBwdFinsupp (R : Type u) [Ring R] (X : Type u)
    [AddCommGroup X] [Module Rᵐᵒᵖ X] (ι : Type u) :
    (ι →₀ X) →+ BalTensor R X (ι →₀ R) :=
  Finsupp.liftAddHom (fun i : ι => BalTensor.mkLeft R (Finsupp.single i (1 : R)))

private theorem balBwdFinsupp_single (R : Type u) [Ring R] (X : Type u)
    [AddCommGroup X] [Module Rᵐᵒᵖ X] (ι : Type u) (i : ι) (x : X) :
    balBwdFinsupp R X ι (Finsupp.single i x) = BalTensor.mk R x (Finsupp.single i 1) := by
  show (Finsupp.single i x).sum (fun j => ⇑(BalTensor.mkLeft R (Finsupp.single j (1 : R)))) = _
  rw [Finsupp.sum_single_index]
  · rfl
  · simp

private theorem balBwdFinsupp_comp_fwd (R : Type u) [Ring R] (X : Type u)
    [AddCommGroup X] [Module Rᵐᵒᵖ X] (ι : Type u) (x : X) :
    (balBwdFinsupp R X ι).comp
        (Finsupp.mapRange.addMonoidHom (ι := ι) (rightSmulHom R X x))
      = BalTensor.mkRight R x := by
  apply Finsupp.addHom_ext
  intro i r
  rw [AddMonoidHom.comp_apply, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
    balBwdFinsupp_single]
  show BalTensor.mk R (op r • x) (Finsupp.single i 1) = BalTensor.mk R x (Finsupp.single i r)
  rw [BalTensor.mk_smul_right]
  congr 1
  ext j
  simp [smul_eq_mul]

private theorem balBwdFinsupp_comp_fwd_hom (R : Type u) [Ring R] (X : Type u)
    [AddCommGroup X] [Module Rᵐᵒᵖ X] (ι : Type u) :
    (balBwdFinsupp R X ι).comp (balFwdFinsupp R X ι) = AddMonoidHom.id _ := by
  apply BalTensor.ext R
  intro x n
  rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, balFwdFinsupp_mk, mapRange_rightSmulHom_eq]
  exact congrArg (fun f => f n) (balBwdFinsupp_comp_fwd R X ι x)

private theorem balFwdFinsupp_comp_bwd (R : Type u) [Ring R] (X : Type u)
    [AddCommGroup X] [Module Rᵐᵒᵖ X] (ι : Type u) :
    (balFwdFinsupp R X ι).comp (balBwdFinsupp R X ι) = AddMonoidHom.id _ := by
  apply Finsupp.addHom_ext
  intro i x
  rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, balBwdFinsupp_single, balFwdFinsupp_mk,
    Finsupp.mapRange_single]
  simp

private noncomputable def balFinsuppEquiv (R : Type u) [Ring R] (X : Type u)
    [AddCommGroup X] [Module Rᵐᵒᵖ X] (ι : Type u) :
    BalTensor R X (ι →₀ R) ≃+ (ι →₀ X) where
  toFun := balFwdFinsupp R X ι
  invFun := balBwdFinsupp R X ι
  left_inv := fun a => by
    have h := congrArg
      (fun f : BalTensor R X (ι →₀ R) →+ BalTensor R X (ι →₀ R) => f a)
      (balBwdFinsupp_comp_fwd_hom R X ι)
    simpa using h
  right_inv := fun v => by
    have h := congrArg (fun f : (ι →₀ X) →+ (ι →₀ X) => f v)
      (balFwdFinsupp_comp_bwd R X ι)
    simpa using h
  map_add' := fun a b => map_add (balFwdFinsupp R X ι) a b

private theorem balFinsuppEquiv_mk (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (ι : Type u) (x : X) (n : ι →₀ R) :
    balFinsuppEquiv R X ι (BalTensor.mk R x n)
      = Finsupp.mapRange (fun r => op r • x) (by simp) n :=
  balFwdFinsupp_mk R X ι x n

/-- Naturality of `balFinsuppEquiv` in the right module: for `f : X →ₗ[Rᵐᵒᵖ] Y` the square
`e_Y ∘ (f ⊗ id) = (mapRange f) ∘ e_X` commutes. -/
private theorem mapRange_natural (R : Type u) [Ring R] (X Y : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] [AddCommGroup Y] [Module Rᵐᵒᵖ Y] (ι : Type u)
    (f : X →ₗ[Rᵐᵒᵖ] Y) :
    (balFinsuppEquiv R Y ι).toAddMonoidHom.comp
        (BalTensor.map R f (LinearMap.id : (ι →₀ R) →ₗ[R] (ι →₀ R)))
      = (Finsupp.mapRange.addMonoidHom (ι := ι) f.toAddMonoidHom).comp
        (balFinsuppEquiv R X ι).toAddMonoidHom := by
  apply BalTensor.ext R
  intro x n
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [BalTensor.map_mk, LinearMap.id_apply, balFinsuppEquiv_mk, balFinsuppEquiv_mk,
    Finsupp.mapRange.addMonoidHom_apply]
  apply Finsupp.ext
  intro i
  simp only [Finsupp.mapRange_apply]
  exact (f.map_smul (op (n i)) x).symm

/-- Every free left `R`-module `ι →₀ R` is left flat: under `balFinsuppEquiv` the map
`BalTensor.map R f id` induced by an injective `f` is carried to `Finsupp.mapRange f`. -/
private theorem leftFlat_finsupp (R : Type u) [Ring R] (ι : Type u) :
    LeftFlat R (ι →₀ R) := by
  unfold LeftFlat
  intro X Y instX modX instY modY f hf
  have hsquare := mapRange_natural R X Y ι f
  have hinj : Function.Injective
      (Finsupp.mapRange.addMonoidHom (ι := ι) f.toAddMonoidHom) := by
    intro v w hvw
    have h2 : Finsupp.mapRange (f : X → Y) (map_zero f) v
        = Finsupp.mapRange (f : X → Y) (map_zero f) w := by
      simpa only [Finsupp.mapRange.addMonoidHom_apply, LinearMap.toAddMonoidHom_coe] using hvw
    exact Finsupp.mapRange_injective (f : X → Y) (map_zero f) hf h2
  intro z w hzw
  have h1 : (Finsupp.mapRange.addMonoidHom (ι := ι) f.toAddMonoidHom)
        ((balFinsuppEquiv R X ι) z) =
      (Finsupp.mapRange.addMonoidHom (ι := ι) f.toAddMonoidHom)
        ((balFinsuppEquiv R X ι) w) := by
    have hz := congrArg (fun g => g z) hsquare
    have hw := congrArg (fun g => g w) hsquare
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] at hz hw
    rw [← hz, ← hw, hzw]
  exact (balFinsuppEquiv R X ι).injective (hinj h1)

/-- Left flatness is inherited by retracts (mirror of `Work.ORFlatness.rightFlat_of_retract`). -/
private theorem leftFlat_of_retract_aux {R : Type u} [Ring R] {F X : Type u}
    [AddCommGroup F] [Module R F] [AddCommGroup X] [Module R X]
    (hF : LeftFlat R F) (ι : X →ₗ[R] F) (r : F →ₗ[R] X)
    (hr : r.comp ι = LinearMap.id) : LeftFlat R X := by
  intro A B _ _ _ _ f hf
  have hretract : (BalTensor.map R (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) r).comp
      (BalTensor.map R (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) ι) = AddMonoidHom.id _ := by
    rw [← BalTensor.map_comp, hr, LinearMap.id_comp, BalTensor.map_id]
  have hnat : (BalTensor.map R f (LinearMap.id : F →ₗ[R] F)).comp
        (BalTensor.map R (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) ι) =
      (BalTensor.map R (LinearMap.id : B →ₗ[Rᵐᵒᵖ] B) ι).comp
        (BalTensor.map R f (LinearMap.id : X →ₗ[R] X)) := by
    rw [← BalTensor.map_comp, ← BalTensor.map_comp]
    simp
  have hinjF : Function.Injective (BalTensor.map R f (LinearMap.id : F →ₗ[R] F)) := hF f hf
  intro z w hzw
  have h1 : BalTensor.map R (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) ι z
      = BalTensor.map R (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) ι w := by
    apply hinjF
    have hz := congrArg (fun g => g z) hnat
    have hw := congrArg (fun g => g w) hnat
    simp only [AddMonoidHom.comp_apply] at hz hw
    rw [hz, hw, hzw]
  calc z = (BalTensor.map R (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) r)
        ((BalTensor.map R (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) ι) z) := by
        rw [← AddMonoidHom.comp_apply, hretract, AddMonoidHom.id_apply]
    _ = (BalTensor.map R (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) r)
        ((BalTensor.map R (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) ι) w) := by rw [h1]
    _ = w := by
        rw [← AddMonoidHom.comp_apply, hretract, AddMonoidHom.id_apply]

/-- A projective **left** `R`-module is left flat: tensoring on the right by it preserves injective maps of right modules. This is the mirror of `Work.ORFlatness.rightFlat_of_projective` (`Submission/Work/ORFlatness/rightFlat_of_projective.lean`), which proves the corresponding fact for right `R`-modules; the same route works here, with the two slots of `Work.ORFlatness.BalTensor` interchanged:

(i) prove the auxiliary isomorphism `BalTensor R X (ι → ₀ R) ≃+ (ι → ₀ X)` sending `mk x (Finsupp.single i 1)` to `Finsupp.single i x` (equivalently `mk x y` to `y.mapRange (fun r => x • r)`), by exhibiting the two inverse additive maps; this gives `LeftFlat R (ι → ₀ R)`;
(ii) show that left flatness is inherited by retracts: if `r ∘ i = id` then `map i (id)` is injective for left-flat `Y` (functoriality in both variables plus `map_comp`, `map_id`, as in `Work.ORFlatness.injective_map_of_retract`);
(iii) conclude from `Module.projective_def`, which for `Module.Projective R M` produces a section `s : M → (M → ₀ R)` of `Finsupp.linearCombination R id`, exhibiting `M` as a retract of the free module `M → ₀ R`. -/
theorem leftFlat_of_projective (R : Type u) [Ring R] {M : Type u} [AddCommGroup M]
    [Module R M] [Module.Projective R M] : Work.ORFlatness.LeftFlat R M := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (Finsupp.linearCombination R (id : M → M)) (LinearMap.id : M →ₗ[R] M)
    (Finsupp.linearCombination_surjective R Function.surjective_id)
  exact leftFlat_of_retract_aux (leftFlat_finsupp R M) s
    (Finsupp.linearCombination R (id : M → M)) hs

end Work.ORFlatness
