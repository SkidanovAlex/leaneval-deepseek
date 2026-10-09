import Mathlib
import Submission.Work.SSGRoute.PT.homCoindFree_coind_iso
import Submission.Work.SSGRoute.ExtChain.ChainGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro for `Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)` for an arbitrary finite index type `ι`

This is `Work.SSGRoute.PT.homCoindFree_coind_iso` with `Fin n` replaced by an arbitrary finite
type `ι`, for the coefficient `Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι` of `ExtChain/ChainGamma.lean` (the same
module `Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)` with the conjugation action, wrapped in a `@[reducible] def` so
that instance search terminates).

The isomorphism is the classical Shapiro/Frobenius identification

  `Φ(w)(γ) i = γ⁻¹ · w (ρ (res γ) e_i)`,  `Φ⁻¹(f)(e_{i,g}) = s(g) · f(s(g)) i`,

where `s` is a section of `res k K` (surjective because `Ω` is algebraically closed).

## Instance note

As in `homCoindFree_coind_iso.lean`, the `Γ`-action on `Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)` is pinned with
a local `SMul` instance: without it, type class search picks Mathlib's *pointwise* action on
`AddMonoidHom` (`(σ • w) x = σ • w x`), for which the statement is false.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute.PT

open CategoryTheory

noncomputable section

/-- The conjugation action of `Γ = Gal(Ω/k)` on `Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)`, pinned so that type
class search does not pick the pointwise action on `AddMonoidHom`. -/
def smulConjCoindFreeT (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ι : Type) : SMul (Ω ≃ₐ[k] Ω) (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) :=
  ⟨fun σ φ => (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv
    (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)).smul σ φ⟩

attribute [local instance 10000] smulConjCoindFreeT

section Main

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] {ι : Type}
  [Fintype ι]

/-- `ℤ[Gal(K/k)]^ι`, the underlying module of `Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι`. -/
abbrev FreeRepT (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (ι : Type) : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
  Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι

/-- The basis element `e_{i,g} = δ_i · g` of `ℤ[Gal(K/k)]^ι`. -/
def basisVT (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (ι : Type) (i : ι) (g : K ≃ₐ[k] K) : (FreeRepT k Ω K ι).V :=
  Finsupp.single i (MonoidAlgebra.single g 1)

/-- The pinned action is the conjugation action. -/
theorem homCoindFreeT_smul_apply (σ : Ω ≃ₐ[k] Ω) (w : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι)
    (x : (FreeRepT k Ω K ι).V) :
    (σ • w) x = σ • w ((FreeRepT k Ω K ι).ρ (((SSGRoute.res k K) σ)⁻¹) x) := rfl

/-- The `Gal(K/k)`-action on the basis of `ℤ[Gal(K/k)]^ι`. -/
@[simp] theorem ρ_basisVT (g : K ≃ₐ[k] K) (i : ι) :
    (FreeRepT k Ω K ι).ρ g (basisVT k Ω K ι i 1) = basisVT k Ω K ι i g := by
  show ((Representation.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι) g)
      (Finsupp.single i (MonoidAlgebra.single 1 1)) = _
  rw [Representation.free_single_single, mul_one]
  rfl

/-- Composition of the `Gal(K/k)`-action on `ℤ[Gal(K/k)]^ι`. -/
theorem ρ_mul_applyT (g h : K ≃ₐ[k] K) (x : (FreeRepT k Ω K ι).V) :
    (FreeRepT k Ω K ι).ρ g ((FreeRepT k Ω K ι).ρ h x) = (FreeRepT k Ω K ι).ρ (g * h) x := by
  rw [Rep.ρ_mul]
  rfl

/-- Evaluation of `freeHomEquiv.symm` at a basis vector. -/
theorem freeHomEquiv_symm_basisT (h : ι → (K ≃ₐ[k] K) → Additive Ωˣ) (i : ι)
    (g : K ≃ₐ[k] K) :
    Work.SSGRoute.freeHomEquiv.symm h (basisVT k Ω K ι i g) = h i g := by
  have h1 := Work.SSGRoute.freeHomEquiv_apply (k := k) (Ω := Ω) (K := K) (ι := ι)
    (Work.SSGRoute.freeHomEquiv.symm h) i g
  rw [AddEquiv.apply_symm_apply] at h1
  exact h1.symm

/-! ## The forward map `Work.SSGRoute.ExtChain.homCoindFreeT → Coind` -/

/-- Coordinates of a homomorphism in the coinduced form: `w ↦ (γ ↦ i ↦ γ⁻¹ · w(γ · e_i))`. -/
def toCoindFunT (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ι : Type) [Fintype ι] (w : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) :
    (Ω ≃ₐ[k] Ω) → (ι → Additive Ωˣ) :=
  fun γ i => γ⁻¹ • w ((FreeRepT k Ω K ι).ρ (SSGRoute.res k K γ) (basisVT k Ω K ι i 1))

theorem toCoindFunT_rel (w : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) (γ : Ω ≃ₐ[k] Ω) (u : K.fixingSubgroup) :
    toCoindFunT k Ω K ι w (γ * (u : Ω ≃ₐ[k] Ω)) = u⁻¹ • toCoindFunT k Ω K ι w γ := by
  funext i
  have h1 : SSGRoute.res k K (γ * (u : Ω ≃ₐ[k] Ω)) = SSGRoute.res k K γ := by
    rw [map_mul, res_eq_one_of_mem_fixingSubgroup (k := k) (Ω := Ω) (K := K) u, mul_one]
  show (γ * (u : Ω ≃ₐ[k] Ω))⁻¹
        • w ((FreeRepT k Ω K ι).ρ (SSGRoute.res k K (γ * (u : Ω ≃ₐ[k] Ω)))
            (basisVT k Ω K ι i 1))
      = (u : Ω ≃ₐ[k] Ω)⁻¹
        • (γ⁻¹ • w ((FreeRepT k Ω K ι).ρ (SSGRoute.res k K γ) (basisVT k Ω K ι i 1)))
  rw [h1, mul_inv_rev, mul_smul]

/-- The forward map `Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ) → Coind_{G_K}^Γ((Ωˣ)^ι)`. -/
def toCoindT (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ι : Type) [Fintype ι] (w : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) :
    Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (ι → Additive Ωˣ) :=
  ⟨toCoindFunT k Ω K ι w, fun γ u => toCoindFunT_rel (k := k) (Ω := Ω) (K := K) (ι := ι) w γ u⟩

theorem toCoindT_add (w w' : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) :
    toCoindT k Ω K ι (w + w') = toCoindT k Ω K ι w + toCoindT k Ω K ι w' := by
  apply Subtype.ext
  funext γ i
  show γ⁻¹ • (w + w') ((FreeRepT k Ω K ι).ρ (SSGRoute.res k K γ) (basisVT k Ω K ι i 1))
      = γ⁻¹ • w ((FreeRepT k Ω K ι).ρ (SSGRoute.res k K γ) (basisVT k Ω K ι i 1))
        + γ⁻¹ • w' ((FreeRepT k Ω K ι).ρ (SSGRoute.res k K γ) (basisVT k Ω K ι i 1))
  rw [AddMonoidHom.add_apply, smul_add]

theorem toCoindT_smul (σ : Ω ≃ₐ[k] Ω) (w : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) :
    toCoindT k Ω K ι (σ • w) = σ • toCoindT k Ω K ι w := by
  apply Subtype.ext
  funext γ i
  have hL : toCoindT k Ω K ι (σ • w) γ i
      = (γ⁻¹ * σ) • w ((FreeRepT k Ω K ι).ρ (SSGRoute.res k K (σ⁻¹ * γ))
          (basisVT k Ω K ι i 1)) := by
    show γ⁻¹ • (σ • w) ((FreeRepT k Ω K ι).ρ (SSGRoute.res k K γ) (basisVT k Ω K ι i 1)) = _
    rw [homCoindFreeT_smul_apply, ρ_mul_applyT, ← mul_smul]
    congr 1
    rw [← map_inv, ← map_mul]
  have hR : (σ • toCoindT k Ω K ι w) γ i
      = (γ⁻¹ * σ) • w ((FreeRepT k Ω K ι).ρ (SSGRoute.res k K (σ⁻¹ * γ))
          (basisVT k Ω K ι i 1)) := by
    rw [Coind.smul_apply]
    show (σ⁻¹ * γ)⁻¹ • w ((FreeRepT k Ω K ι).ρ (SSGRoute.res k K (σ⁻¹ * γ))
        (basisVT k Ω K ι i 1)) = _
    rw [mul_inv_rev, inv_inv]
  rw [hL, hR]

/-! ## The inverse map `Coind → Work.SSGRoute.ExtChain.homCoindFreeT` -/

/-- Coordinates of a coinduced function: evaluate at the section of `g`, act, and read off
component `i`. -/
def coindCoordT (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (ι → Additive Ωˣ)) :
    ι → (K ≃ₐ[k] K) → Additive Ωˣ :=
  fun i g => resSection k Ω K g • f (resSection k Ω K g) i

/-- The inverse map `Coind_{G_K}^Γ((Ωˣ)^ι) → Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)`. -/
def ofCoindT (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ι : Type) [Fintype ι] (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (ι → Additive Ωˣ)) :
    Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι :=
  Work.SSGRoute.freeHomEquiv.symm (coindCoordT (k := k) (Ω := Ω) (K := K) (ι := ι) f)

theorem freeHomEquiv_ofCoindT (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (ι → Additive Ωˣ)) :
    Work.SSGRoute.freeHomEquiv (ofCoindT k Ω K ι f) = coindCoordT f := by
  show Work.SSGRoute.freeHomEquiv
      (Work.SSGRoute.freeHomEquiv.symm (coindCoordT (k := k) (Ω := Ω) (K := K) (ι := ι) f))
    = coindCoordT f
  rw [AddEquiv.apply_symm_apply]

theorem ofCoindT_apply_basis (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (ι → Additive Ωˣ))
    (i : ι) (g : K ≃ₐ[k] K) :
    ofCoindT k Ω K ι f (basisVT k Ω K ι i g) = resSection k Ω K g • f (resSection k Ω K g) i := by
  show Work.SSGRoute.freeHomEquiv.symm (coindCoordT (k := k) (Ω := Ω) (K := K) (ι := ι) f)
      (basisVT k Ω K ι i g) = resSection k Ω K g • f (resSection k Ω K g) i
  rw [freeHomEquiv_symm_basisT]
  rfl

theorem ofCoindT_add (f f' : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (ι → Additive Ωˣ)) :
    ofCoindT k Ω K ι (f + f') = ofCoindT k Ω K ι f + ofCoindT k Ω K ι f' := by
  apply Work.SSGRoute.freeHomEquiv.injective
  rw [freeHomEquiv_ofCoindT, map_add, freeHomEquiv_ofCoindT, freeHomEquiv_ofCoindT]
  funext i g
  show resSection k Ω K g • (f (resSection k Ω K g) i + f' (resSection k Ω K g) i)
      = resSection k Ω K g • f (resSection k Ω K g) i
        + resSection k Ω K g • f' (resSection k Ω K g) i
  rw [smul_add]

/-! ## The two inverse laws -/

/-- `γ' · f γ'` only depends on `res γ'`. -/
theorem coind_smul_self_eqT (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (ι → Additive Ωˣ))
    (γ : Ω ≃ₐ[k] Ω) (u : K.fixingSubgroup) :
    ((γ * (u : Ω ≃ₐ[k] Ω)) • f (γ * (u : Ω ≃ₐ[k] Ω))) = γ • f γ := by
  rw [Coind.coe_mul]
  show (γ * (u : Ω ≃ₐ[k] Ω)) • ((u : Ω ≃ₐ[k] Ω)⁻¹ • f γ) = γ • f γ
  have hcoe : (γ * (u : Ω ≃ₐ[k] Ω)) * ((u : Ω ≃ₐ[k] Ω)⁻¹) = γ := by
    rw [mul_assoc, ← Subgroup.coe_inv, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      mul_one]
  rw [← mul_smul, hcoe]

theorem coind_smul_self_lift_eqT (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (ι → Additive Ωˣ))
    (γ γ' : Ω ≃ₐ[k] Ω) (h : SSGRoute.res k K γ' = SSGRoute.res k K γ) :
    γ' • f γ' = γ • f γ := by
  have hu : γ⁻¹ * γ' ∈ K.fixingSubgroup := by
    rw [← mem_fixingSubgroup_iff_res_eq_one, map_mul, map_inv, h, inv_mul_cancel]
  have hγγ' : γ * (⟨γ⁻¹ * γ', hu⟩ : K.fixingSubgroup) = γ' := by
    show γ * (γ⁻¹ * γ') = γ'
    group
  rw [← hγγ']
  exact coind_smul_self_eqT (k := k) (Ω := Ω) (K := K) (ι := ι) f γ ⟨γ⁻¹ * γ', hu⟩

theorem coind_smul_self_lift_applyT
    (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (ι → Additive Ωˣ))
    (γ γ' : Ω ≃ₐ[k] Ω) (h : SSGRoute.res k K γ' = SSGRoute.res k K γ) (i : ι) :
    γ' • f γ' i = γ • f γ i :=
  congrFun (coind_smul_self_lift_eqT (k := k) (Ω := Ω) (K := K) (ι := ι) f γ γ' h) i

theorem ofCoindT_toCoindT (w : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) : ofCoindT k Ω K ι (toCoindT k Ω K ι w) = w := by
  apply Work.SSGRoute.freeHomEquiv.injective
  rw [freeHomEquiv_ofCoindT]
  funext i g
  show resSection k Ω K g • toCoindT k Ω K ι w (resSection k Ω K g) i
      = Work.SSGRoute.freeHomEquiv w i g
  rw [show toCoindT k Ω K ι w (resSection k Ω K g) i
      = (resSection k Ω K g)⁻¹ • w ((FreeRepT k Ω K ι).ρ (SSGRoute.res k K (resSection k Ω K g))
          (basisVT k Ω K ι i 1)) from rfl,
    resSection_spec, ← mul_smul, mul_inv_cancel, one_smul, ρ_basisVT,
    Work.SSGRoute.freeHomEquiv_apply]
  rfl

theorem toCoindT_ofCoindT (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (ι → Additive Ωˣ)) :
    toCoindT k Ω K ι (ofCoindT k Ω K ι f) = f := by
  apply Subtype.ext
  funext γ i
  show γ⁻¹ • ofCoindT k Ω K ι f ((FreeRepT k Ω K ι).ρ (SSGRoute.res k K γ)
      (basisVT k Ω K ι i 1)) = f γ i
  rw [ρ_basisVT, ofCoindT_apply_basis,
    coind_smul_self_lift_applyT (k := k) (Ω := Ω) (K := K) (ι := ι) f γ
      (resSection k Ω K (SSGRoute.res k K γ))
      (resSection_spec (k := k) (Ω := Ω) (K := K) (SSGRoute.res k K γ)) i,
    ← mul_smul, inv_mul_cancel, one_smul]

end Main

theorem homCoindFree_coind_iso_gen_aux (k Ω : Type) [Field k] [CharZero k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ι : Type) [Fintype ι] :
    ∃ Φ : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι ≃+
        Work.SSGRoute.PT.Coind (Ω ≃ₐ[k] Ω) (K.fixingSubgroup) (ι → Additive Ωˣ),
      ∀ (σ : Ω ≃ₐ[k] Ω) (w : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι),
        Φ (σ • w) = σ • Φ w := by
  refine ⟨{ toFun := toCoindT k Ω K ι
            invFun := ofCoindT k Ω K ι
            left_inv := fun w => ofCoindT_toCoindT (k := k) (Ω := Ω) (K := K) (ι := ι) w
            right_inv := fun f => toCoindT_ofCoindT (k := k) (Ω := Ω) (K := K) (ι := ι) f
            map_add' := fun w w' => toCoindT_add (k := k) (Ω := Ω) (K := K) (ι := ι) w w' }, ?_⟩
  intro σ w
  exact toCoindT_smul (k := k) (Ω := Ω) (K := K) (ι := ι) σ w

theorem homCoindFree_coind_iso_gen (k Ω : Type) [Field k] [CharZero k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ι : Type) [Fintype ι] :
    ∃ Zc : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι ≃+
        Work.SSGRoute.PT.Coind (Ω ≃ₐ[k] Ω) (K.fixingSubgroup) (ι → Additive Ωˣ),
      Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Zc.toAddMonoidHom := by
  obtain ⟨Φ, hΦ⟩ := homCoindFree_coind_iso_gen_aux (k := k) (Ω := Ω) (K := K) (ι := ι)
  exact ⟨Φ, fun σ w => hΦ σ w⟩

end

end Work.SSGRoute.PT
