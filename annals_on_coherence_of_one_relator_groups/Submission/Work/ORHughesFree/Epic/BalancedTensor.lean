import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The `R`-balanced tensor product `S ⊗[R] S`

For a ring homomorphism `f : R →+* S` we regard `S` as an `(R,R)`-bimodule and construct the
abelian group `S ⊗[R] S` used in the Isbell–Silver–Mazet criterion: the quotient of the
ℤ-tensor product `S ⊗[ℤ] S` by the "balance" relations `s·f r ⊗ t = s ⊗ f r·t`.
-/

namespace Work.ORHughesFree.Epic

variable {R S : Type*} [Ring R] [Ring S]

/-- The set of "balance" relations `s·f r ⊗ t - s ⊗ f r·t` inside the ℤ-tensor product
`S ⊗[ℤ] S`, where `S` is regarded as an `(R,R)`-bimodule via `f`. -/
def balRel (f : R →+* S) : Set (TensorProduct ℤ S S) :=
  {x | ∃ s t : S, ∃ r : R, x = (s * f r) ⊗ₜ[ℤ] t - s ⊗ₜ[ℤ] (f r * t)}

/-- The `R`-balanced tensor product `S ⊗[R] S` of the `(R,R)`-bimodule `S` with itself. -/
abbrev BalancedTensor (f : R →+* S) : Type _ :=
  (TensorProduct ℤ S S) ⧸ AddSubgroup.closure (balRel f)

namespace BalancedTensor

instance (f : R →+* S) : AddCommGroup (BalancedTensor f) := inferInstanceAs (AddCommGroup _)

/-- The canonical additive projection `S ⊗[ℤ] S → S ⊗[R] S`. -/
def mk (f : R →+* S) : TensorProduct ℤ S S →+ BalancedTensor f := QuotientAddGroup.mk' _

/-- The class of the elementary tensor `s ⊗ t` in `S ⊗[R] S`. -/
def tmul (f : R →+* S) (s t : S) : BalancedTensor f := mk f (s ⊗ₜ[ℤ] t)

theorem mk_eq_zero_of_mem (f : R →+* S) {x : TensorProduct ℤ S S} (hx : x ∈ balRel f) :
    mk f x = 0 :=
  AddMonoidHom.mem_ker.mp (by
    rw [mk, QuotientAddGroup.ker_mk']
    exact AddSubgroup.subset_closure hx)

/-- The balance relation `s·f r ⊗ t = s ⊗ f r·t`. -/
theorem tmul_balance (f : R →+* S) (s t : S) (r : R) :
    tmul f (s * f r) t = tmul f s (f r * t) := by
  show mk f ((s * f r) ⊗ₜ[ℤ] t) = mk f (s ⊗ₜ[ℤ] (f r * t))
  rw [← sub_eq_zero, ← map_sub]
  exact mk_eq_zero_of_mem f ⟨s, t, r, rfl⟩

theorem tmul_add (f : R →+* S) (s s' t : S) :
    tmul f (s + s') t = tmul f s t + tmul f s' t := by
  show mk f ((s + s') ⊗ₜ[ℤ] t) = mk f (s ⊗ₜ[ℤ] t) + mk f (s' ⊗ₜ[ℤ] t)
  rw [TensorProduct.add_tmul, map_add]

theorem tmul_add_right (f : R →+* S) (s t t' : S) :
    tmul f s (t + t') = tmul f s t + tmul f s t' := by
  show mk f (s ⊗ₜ[ℤ] (t + t')) = mk f (s ⊗ₜ[ℤ] t) + mk f (s ⊗ₜ[ℤ] t')
  rw [TensorProduct.tmul_add, map_add]

/-- **Extensionality.**  Two additive maps out of `S ⊗[R] S` which agree on all elementary
tensors `tmul s t` are equal. -/
theorem addHom_ext (f : R →+* S) {A : Type*} [AddCommGroup A]
    {φ ψ : BalancedTensor f →+ A}
    (h : ∀ s t : S, φ (tmul f s t) = ψ (tmul f s t)) : φ = ψ := by
  have key : ∀ x : TensorProduct ℤ S S, φ (mk f x) = ψ (mk f x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero (mk f), map_zero φ, map_zero ψ]
    | tmul a b => exact h a b
    | add a b ha hb => rw [map_add (mk f) a b, map_add φ, map_add ψ, ha, hb]
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  simpa only [mk, QuotientAddGroup.mk'_apply] using key y

/-- **Universal property of `S ⊗[R] S`.**  An `R`-balanced `ℤ`-bilinear map `β : S × S → A` with
values in an abelian group factors uniquely through `S ⊗[R] S`. -/
noncomputable def lift (f : R →+* S) {A : Type*} [AddCommGroup A] (β : S →ₗ[ℤ] S →ₗ[ℤ] A)
    (hβ : ∀ s t : S, ∀ r : R, β (s * f r) t = β s (f r * t)) : BalancedTensor f →+ A :=
  QuotientAddGroup.lift (AddSubgroup.closure (balRel f)) (TensorProduct.lift β).toAddMonoidHom (by
    rw [AddSubgroup.closure_le]
    rintro x ⟨s, t, r, rfl⟩
    show (TensorProduct.lift β) ((s * f r) ⊗ₜ[ℤ] t - s ⊗ₜ[ℤ] (f r * t)) = 0
    rw [map_sub, TensorProduct.lift.tmul, TensorProduct.lift.tmul, hβ s t r, sub_self])

theorem lift_tmul (f : R →+* S) {A : Type*} [AddCommGroup A] (β : S →ₗ[ℤ] S →ₗ[ℤ] A)
    (hβ : ∀ s t : S, ∀ r : R, β (s * f r) t = β s (f r * t)) (s t : S) :
    lift f β hβ (tmul f s t) = β s t := by
  have h1 : lift f β hβ (tmul f s t)
      = (TensorProduct.lift β).toAddMonoidHom (s ⊗ₜ[ℤ] t) := by
    rw [lift, tmul, mk, QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk]
  rw [h1]
  exact TensorProduct.lift.tmul s t

/-! ### The `(S,S)`-bimodule structure -/

/-- The additive map `a ⊗ b ↦ (s * a) ⊗ b` on `S ⊗[ℤ] S`. -/
noncomputable def mulLeftAux (s : S) : TensorProduct ℤ S S →+ TensorProduct ℤ S S :=
  (TensorProduct.lift
    { toFun := fun a => TensorProduct.mk ℤ S S (s * a)
      map_add' := by intro a b; rw [mul_add, map_add]
      map_smul' := by
        intro n a
        rw [mul_smul_comm]
        exact LinearMap.map_smul (TensorProduct.mk ℤ S S) n (s * a) }).toAddMonoidHom

theorem mulLeftAux_tmul (s a b : S) : mulLeftAux s (a ⊗ₜ[ℤ] b) = (s * a) ⊗ₜ[ℤ] b := by
  simp [mulLeftAux]

theorem mulLeftAux_balRel (f : R →+* S) (s : S) {x : TensorProduct ℤ S S}
    (hx : x ∈ balRel f) : mulLeftAux s x ∈ balRel f := by
  obtain ⟨a, b, r, rfl⟩ := hx
  refine ⟨s * a, b, r, ?_⟩
  rw [map_sub, mulLeftAux_tmul, mulLeftAux_tmul, mul_assoc]

/-- The left `S`-module structure on `S ⊗[R] S`. -/
noncomputable def smulLeft (f : R →+* S) (s : S) : BalancedTensor f →+ BalancedTensor f :=
  QuotientAddGroup.lift (AddSubgroup.closure (balRel f)) ((mk f).comp (mulLeftAux s))
    ((AddSubgroup.closure_le _).mpr fun _ hx =>
      mk_eq_zero_of_mem f (mulLeftAux_balRel f s hx))

theorem smulLeft_tmul (f : R →+* S) (s a b : S) :
    smulLeft f s (tmul f a b) = tmul f (s * a) b := by
  have h1 : smulLeft f s (tmul f a b) = (mk f) (mulLeftAux s (a ⊗ₜ[ℤ] b)) := by
    rw [smulLeft]
    exact QuotientAddGroup.lift_mk _ _ _
  rw [h1, mulLeftAux_tmul]
  rfl

/-- The additive map `a ⊗ b ↦ a ⊗ (b * s)` on `S ⊗[ℤ] S`. -/
noncomputable def mulRightAux (s : S) : TensorProduct ℤ S S →+ TensorProduct ℤ S S :=
  (TensorProduct.lift
    { toFun := fun a => (TensorProduct.mk ℤ S S a).comp (LinearMap.mulRight ℤ s)
      map_add' := by
        intro a b
        ext c
        simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
      map_smul' := by
        intro n a
        ext c
        simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.map_smul,
          RingHom.id_apply, LinearMap.mulRight_apply] }).toAddMonoidHom

theorem mulRightAux_tmul (s a b : S) : mulRightAux s (a ⊗ₜ[ℤ] b) = a ⊗ₜ[ℤ] (b * s) := by
  simp [mulRightAux]

theorem mulRightAux_balRel (f : R →+* S) (s : S) {x : TensorProduct ℤ S S}
    (hx : x ∈ balRel f) : mulRightAux s x ∈ balRel f := by
  obtain ⟨a, b, r, rfl⟩ := hx
  refine ⟨a, b * s, r, ?_⟩
  rw [map_sub, mulRightAux_tmul, mulRightAux_tmul, mul_assoc]

/-- The right `S`-module structure on `S ⊗[R] S`. -/
noncomputable def smulRight (f : R →+* S) (s : S) : BalancedTensor f →+ BalancedTensor f :=
  QuotientAddGroup.lift (AddSubgroup.closure (balRel f)) ((mk f).comp (mulRightAux s))
    ((AddSubgroup.closure_le _).mpr fun _ hx =>
      mk_eq_zero_of_mem f (mulRightAux_balRel f s hx))

theorem smulRight_tmul (f : R →+* S) (s a b : S) :
    smulRight f s (tmul f a b) = tmul f a (b * s) := by
  have h1 : smulRight f s (tmul f a b) = (mk f) (mulRightAux s (a ⊗ₜ[ℤ] b)) := by
    rw [smulRight]
    exact QuotientAddGroup.lift_mk _ _ _
  rw [h1, mulRightAux_tmul]
  rfl

theorem smulLeft_add (f : R →+* S) (s s' : S) :
    smulLeft f (s + s') = smulLeft f s + smulLeft f s' := by
  refine addHom_ext f fun a b => ?_
  simp only [AddMonoidHom.add_apply, smulLeft_tmul, add_mul, tmul_add]

theorem smulLeft_mul (f : R →+* S) (s s' : S) :
    smulLeft f (s * s') = (smulLeft f s).comp (smulLeft f s') := by
  refine addHom_ext f fun a b => ?_
  simp only [AddMonoidHom.comp_apply, smulLeft_tmul, mul_assoc]

theorem smulLeft_one (f : R →+* S) :
    smulLeft f (1 : S) = AddMonoidHom.id (BalancedTensor f) := by
  refine addHom_ext f fun a b => ?_
  simp only [AddMonoidHom.id_apply, smulLeft_tmul, one_mul]

theorem smulRight_add (f : R →+* S) (s s' : S) :
    smulRight f (s + s') = smulRight f s + smulRight f s' := by
  refine addHom_ext f fun a b => ?_
  simp only [AddMonoidHom.add_apply, smulRight_tmul, mul_add, tmul_add_right]

theorem smulRight_mul (f : R →+* S) (s s' : S) :
    smulRight f (s * s') = (smulRight f s').comp (smulRight f s) := by
  refine addHom_ext f fun a b => ?_
  simp only [AddMonoidHom.comp_apply, smulRight_tmul, mul_assoc]

theorem smulRight_one (f : R →+* S) :
    smulRight f (1 : S) = AddMonoidHom.id (BalancedTensor f) := by
  refine addHom_ext f fun a b => ?_
  simp only [AddMonoidHom.id_apply, smulRight_tmul, mul_one]

theorem smulLeft_smulRight (f : R →+* S) (s s' : S) :
    (smulLeft f s).comp (smulRight f s') = (smulRight f s').comp (smulLeft f s) := by
  refine addHom_ext f fun a b => ?_
  simp only [AddMonoidHom.comp_apply, smulLeft_tmul, smulRight_tmul]

/-- The element `tmul 1 1` commutes with the image of `R`. -/
theorem smulLeft_eq_smulRight_tmul_one_one (f : R →+* S) (r : R) :
    smulLeft f (f r) (tmul f 1 1) = smulRight f (f r) (tmul f 1 1) := by
  simp only [smulLeft_tmul, smulRight_tmul, one_mul, mul_one]
  simpa using tmul_balance f 1 1 r

/-! ### The `(S,S)`-bimodule structure as type class instances -/

theorem smulLeft_zero (f : R →+* S) : smulLeft f (0 : S) = 0 := by
  ext x
  have h : smulLeft f (0 + 0 : S) = smulLeft f 0 + smulLeft f 0 := smulLeft_add f 0 0
  rw [zero_add] at h
  have h' := congrArg (fun g : BalancedTensor f →+ BalancedTensor f => g x) h
  simp only [AddMonoidHom.add_apply] at h'
  have h2 : smulLeft f 0 x + 0 = smulLeft f 0 x + smulLeft f 0 x := by
    rw [add_zero]; exact h'
  exact (add_left_cancel h2).symm

theorem smulRight_zero (f : R →+* S) : smulRight f (0 : S) = 0 := by
  ext x
  have h : smulRight f (0 + 0 : S) = smulRight f 0 + smulRight f 0 := smulRight_add f 0 0
  rw [zero_add] at h
  have h' := congrArg (fun g : BalancedTensor f →+ BalancedTensor f => g x) h
  simp only [AddMonoidHom.add_apply] at h'
  have h2 : smulRight f 0 x + 0 = smulRight f 0 x + smulRight f 0 x := by
    rw [add_zero]; exact h'
  exact (add_left_cancel h2).symm

noncomputable instance instSMul (f : R →+* S) : SMul S (BalancedTensor f) :=
  ⟨fun s x => smulLeft f s x⟩

noncomputable instance instSMulOp (f : R →+* S) : SMul Sᵐᵒᵖ (BalancedTensor f) :=
  ⟨fun s x => smulRight f (MulOpposite.unop s) x⟩

noncomputable instance instDistribMulAction (f : R →+* S) :
    DistribMulAction S (BalancedTensor f) where
  one_smul x := by
    change smulLeft f 1 x = x
    rw [smulLeft_one, AddMonoidHom.id_apply]
  mul_smul s s' x := by
    change smulLeft f (s * s') x = smulLeft f s (smulLeft f s' x)
    rw [smulLeft_mul, AddMonoidHom.comp_apply]
  smul_zero s := map_zero (smulLeft f s)
  smul_add s x y := map_add (smulLeft f s) x y

noncomputable instance instDistribMulActionOp (f : R →+* S) :
    DistribMulAction Sᵐᵒᵖ (BalancedTensor f) where
  one_smul x := by
    change smulRight f (MulOpposite.unop (1 : Sᵐᵒᵖ)) x = x
    rw [MulOpposite.unop_one, smulRight_one, AddMonoidHom.id_apply]
  mul_smul s s' x := by
    change smulRight f (MulOpposite.unop (s * s')) x
        = smulRight f (MulOpposite.unop s) (smulRight f (MulOpposite.unop s') x)
    rw [MulOpposite.unop_mul, smulRight_mul, AddMonoidHom.comp_apply]
  smul_zero s := map_zero (smulRight f (MulOpposite.unop s))
  smul_add s x y := map_add (smulRight f (MulOpposite.unop s)) x y

noncomputable instance instModule (f : R →+* S) : Module S (BalancedTensor f) where
  add_smul s s' x := by
    change smulLeft f (s + s') x = smulLeft f s x + smulLeft f s' x
    rw [smulLeft_add, AddMonoidHom.add_apply]
  zero_smul x := by
    change smulLeft f 0 x = 0
    rw [smulLeft_zero, AddMonoidHom.zero_apply]

noncomputable instance instModuleOp (f : R →+* S) : Module Sᵐᵒᵖ (BalancedTensor f) where
  add_smul s s' x := by
    change smulRight f (MulOpposite.unop (s + s')) x
        = smulRight f (MulOpposite.unop s) x + smulRight f (MulOpposite.unop s') x
    rw [MulOpposite.unop_add, smulRight_add, AddMonoidHom.add_apply]
  zero_smul x := by
    change smulRight f (MulOpposite.unop (0 : Sᵐᵒᵖ)) x = 0
    rw [MulOpposite.unop_zero, smulRight_zero, AddMonoidHom.zero_apply]

noncomputable instance instSMulCommClass (f : R →+* S) :
    SMulCommClass S Sᵐᵒᵖ (BalancedTensor f) where
  smul_comm s s' x := by
    change smulLeft f s (smulRight f (MulOpposite.unop s') x)
        = smulRight f (MulOpposite.unop s') (smulLeft f s x)
    exact congrArg (fun g : BalancedTensor f →+ BalancedTensor f => g x)
      (smulLeft_smulRight f s (MulOpposite.unop s'))

end BalancedTensor

end Work.ORHughesFree.Epic
