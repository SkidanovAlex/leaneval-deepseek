import Mathlib
import Submission.Work.SSGRoute.PT.shapiro_H2_coind
import Submission.Work.SSGRoute.PT.e1a_chain
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro: `Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ) ≅ Coind_{Gal(Ω/K)}^{Gal(Ω/k)}(Ωˣ)^n`

For `k` a field with algebraic closure `Ω`, `K/k` a finite Galois subextension and `n : ℕ`, the
`Gal(Ω/k)`-module `homCoindFree k Ω K n = Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ)` with the *conjugation* action

  `(σ · φ) x = σ · φ (M.ρ ((res σ)⁻¹) x)`

is isomorphic to the coinduced module `Coind_{G_K}^Γ ((Ωˣ)^n)` (`Γ = Gal(Ω/k)`,
`G_K = K.fixingSubgroup = Gal(Ω/K) = ker res`), compatibly with the `Γ`-action.  The isomorphism
is the classical Shapiro/Frobenius identification

  `Φ(φ)(γ) i = γ⁻¹ · φ (γ · e_i)`,  `Φ⁻¹(f)(e_{i,g}) = s(g) · f(s(g)) i`,

where `s` is a section of `res k K` (surjective because `Ω` is algebraically closed).

## Instance note

`homCoindFree k Ω K n` is (`@[reducible]`) `M.V →+ Additive Ωˣ`; type class search for `SMul` would
otherwise pick the *pointwise* action on `AddMonoidHom` (`(σ • w) x = σ • w x`).  With the pointwise
action the statement below is **false** (`Γ`-invariants would be `(kˣ)^{n·|G|}` on the left but
`(Kˣ)^n` on the right), so the conjugation action is pinned here with a local instance, exactly as
in `Submission/Work/SSGRoute/PT/homCoind_SES.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute.PT

open CategoryTheory

noncomputable section

variable (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- The conjugation action of `Γ = Gal(Ω/k)` on `Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ)`, pinned so that type
class search does not pick the pointwise action on `AddMonoidHom`. -/
def smulConjCoindFree (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] (n : ℕ) :
    SMul (Ω ≃ₐ[k] Ω) (homCoindFree k Ω K n) :=
  ⟨fun σ φ => (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv
      (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (Fin n))).smul σ φ⟩

attribute [local instance 10000] smulConjCoindFree

section Main

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] {n : ℕ}

/-- `ℤ[Gal(K/k)]^n`, the underlying module of `homCoindFree k Ω K n`. -/
abbrev FreeRep (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (n : ℕ) : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
  Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (Fin n)

/-- The basis element `e_{i,g} = δ_i · g` of `ℤ[Gal(K/k)]^n`. -/
def basisV (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (n : ℕ) (i : Fin n) (g : K ≃ₐ[k] K) : (FreeRep k Ω K n).V :=
  Finsupp.single i (MonoidAlgebra.single g 1)

/-- The pinned action is the conjugation action. -/
theorem homCoindFree_smul_apply (σ : Ω ≃ₐ[k] Ω) (w : homCoindFree k Ω K n)
    (x : (FreeRep k Ω K n).V) :
    (σ • w) x = σ • w ((FreeRep k Ω K n).ρ (((SSGRoute.res k K) σ)⁻¹) x) := rfl

/-- The `Gal(K/k)`-action on the basis of `ℤ[Gal(K/k)]^n`. -/
@[simp] theorem ρ_basisV (g : K ≃ₐ[k] K) (i : Fin n) :
    (FreeRep k Ω K n).ρ g (basisV k Ω K n i 1) = basisV k Ω K n i g := by
  show ((Representation.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (Fin n)) g)
      (Finsupp.single i (MonoidAlgebra.single 1 1)) = _
  rw [Representation.free_single_single, mul_one]
  rfl

/-- Composition of the `Gal(K/k)`-action on `ℤ[Gal(K/k)]^n`. -/
theorem ρ_mul_apply (g h : K ≃ₐ[k] K) (x : (FreeRep k Ω K n).V) :
    (FreeRep k Ω K n).ρ g ((FreeRep k Ω K n).ρ h x) = (FreeRep k Ω K n).ρ (g * h) x := by
  rw [Rep.ρ_mul]
  rfl

/-- `K.fixingSubgroup` is the kernel of `res k K`. -/
theorem mem_fixingSubgroup_iff_res_eq_one (u : Ω ≃ₐ[k] Ω) :
    SSGRoute.res k K u = 1 ↔ u ∈ K.fixingSubgroup := by
  rw [show SSGRoute.res k K u = u.restrictNormal K from rfl, AlgEquiv.restrictNormal_eq_one_iff,
    IntermediateField.mem_fixingSubgroup_iff]

/-- Elements of `K.fixingSubgroup` are trivial in `Gal(K/k)`. -/
theorem res_eq_one_of_mem_fixingSubgroup (u : K.fixingSubgroup) :
    SSGRoute.res k K (u : Ω ≃ₐ[k] Ω) = 1 :=
  (mem_fixingSubgroup_iff_res_eq_one (k := k) (Ω := Ω) (K := K) u).mpr u.2

/-- A section of `res k K` (`Ω` algebraically closed). -/
def resSection (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] (g : K ≃ₐ[k] K) :
    Ω ≃ₐ[k] Ω :=
  Classical.choose (AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) Ω g)

theorem resSection_spec (g : K ≃ₐ[k] K) :
    SSGRoute.res k K (resSection k Ω K g) = g :=
  Classical.choose_spec (AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) Ω g)

/-- Coordinates of a coinduced function: evaluate at the section of `g`, act, and read off
component `i`. -/
def coindCoord (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ)) :
    Fin n → (K ≃ₐ[k] K) → Additive Ωˣ :=
  fun i g => resSection k Ω K g • f (resSection k Ω K g) i

/-- Evaluation of `freeHomEquiv.symm` at a basis vector. -/
theorem freeHomEquiv_symm_basis (h : Fin n → (K ≃ₐ[k] K) → Additive Ωˣ) (i : Fin n)
    (g : K ≃ₐ[k] K) :
    Work.SSGRoute.freeHomEquiv.symm h (basisV k Ω K n i g) = h i g := by
  have h1 := Work.SSGRoute.freeHomEquiv_apply (k := k) (Ω := Ω) (K := K) (ι := Fin n)
    (Work.SSGRoute.freeHomEquiv.symm h) i g
  rw [AddEquiv.apply_symm_apply] at h1
  exact h1.symm

/-! ## The forward map `homCoindFree → Coind` -/

/-- Coordinates of a homomorphism in the coinduced form: `w ↦ (γ ↦ i ↦ γ⁻¹ · w(γ · e_i))`. -/
def toCoindFun (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (n : ℕ) (w : homCoindFree k Ω K n) :
    (Ω ≃ₐ[k] Ω) → (Fin n → Additive Ωˣ) :=
  fun γ i => γ⁻¹ • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1))

theorem toCoindFun_rel (w : homCoindFree k Ω K n) (γ : Ω ≃ₐ[k] Ω) (u : K.fixingSubgroup) :
    toCoindFun k Ω K n w (γ * (u : Ω ≃ₐ[k] Ω)) = u⁻¹ • toCoindFun k Ω K n w γ := by
  funext i
  have h1 : SSGRoute.res k K (γ * (u : Ω ≃ₐ[k] Ω)) = SSGRoute.res k K γ := by
    rw [map_mul, res_eq_one_of_mem_fixingSubgroup (k := k) (Ω := Ω) (K := K) u, mul_one]
  show (γ * (u : Ω ≃ₐ[k] Ω))⁻¹
        • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K (γ * (u : Ω ≃ₐ[k] Ω))) (basisV k Ω K n i 1))
      = (u : Ω ≃ₐ[k] Ω)⁻¹
        • (γ⁻¹ • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1)))
  rw [h1, mul_inv_rev, mul_smul]

/-- The forward map `Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ) → Coind_{G_K}^Γ((Ωˣ)^n)`. -/
def toCoind (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (n : ℕ) (w : homCoindFree k Ω K n) :
    Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ) :=
  ⟨toCoindFun k Ω K n w, fun γ u => toCoindFun_rel (k := k) (Ω := Ω) (K := K) (n := n) w γ u⟩

theorem toCoind_add (w w' : homCoindFree k Ω K n) :
    toCoind k Ω K n (w + w') = toCoind k Ω K n w + toCoind k Ω K n w' := by
  apply Subtype.ext
  funext γ i
  show γ⁻¹ • (w + w') ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1))
      = γ⁻¹ • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1))
        + γ⁻¹ • w' ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1))
  rw [AddMonoidHom.add_apply, smul_add]

theorem toCoind_smul (σ : Ω ≃ₐ[k] Ω) (w : homCoindFree k Ω K n) :
    toCoind k Ω K n (σ • w) = σ • toCoind k Ω K n w := by
  apply Subtype.ext
  funext γ i
  have hL : toCoind k Ω K n (σ • w) γ i
      = (γ⁻¹ * σ) • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K (σ⁻¹ * γ))
          (basisV k Ω K n i 1)) := by
    show γ⁻¹ • (σ • w) ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1)) = _
    rw [homCoindFree_smul_apply, ρ_mul_apply, ← mul_smul]
    congr 1
    rw [← map_inv, ← map_mul]
  have hR : (σ • toCoind k Ω K n w) γ i
      = (γ⁻¹ * σ) • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K (σ⁻¹ * γ))
          (basisV k Ω K n i 1)) := by
    rw [Coind.smul_apply]
    show (σ⁻¹ * γ)⁻¹ • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K (σ⁻¹ * γ))
        (basisV k Ω K n i 1)) = _
    rw [mul_inv_rev, inv_inv]
  rw [hL, hR]

/-! ## The inverse map `Coind → homCoindFree` -/

/-- The inverse map `Coind_{G_K}^Γ((Ωˣ)^n) → Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ)`. -/
def ofCoind (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (n : ℕ) (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ)) :
    homCoindFree k Ω K n :=
  Work.SSGRoute.freeHomEquiv.symm (coindCoord (k := k) (Ω := Ω) (K := K) (n := n) f)

theorem freeHomEquiv_ofCoind (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ)) :
    Work.SSGRoute.freeHomEquiv (ofCoind k Ω K n f) = coindCoord f := by
  show Work.SSGRoute.freeHomEquiv
      (Work.SSGRoute.freeHomEquiv.symm (coindCoord (k := k) (Ω := Ω) (K := K) (n := n) f))
    = coindCoord f
  rw [AddEquiv.apply_symm_apply]

theorem ofCoind_apply_basis (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ))
    (i : Fin n) (g : K ≃ₐ[k] K) :
    ofCoind k Ω K n f (basisV k Ω K n i g) = resSection k Ω K g • f (resSection k Ω K g) i := by
  show Work.SSGRoute.freeHomEquiv.symm (coindCoord (k := k) (Ω := Ω) (K := K) (n := n) f)
      (basisV k Ω K n i g) = resSection k Ω K g • f (resSection k Ω K g) i
  rw [freeHomEquiv_symm_basis]
  rfl

theorem ofCoind_add (f f' : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ)) :
    ofCoind k Ω K n (f + f') = ofCoind k Ω K n f + ofCoind k Ω K n f' := by
  apply Work.SSGRoute.freeHomEquiv.injective
  rw [freeHomEquiv_ofCoind, map_add, freeHomEquiv_ofCoind, freeHomEquiv_ofCoind]
  funext i g
  show resSection k Ω K g • (f (resSection k Ω K g) i + f' (resSection k Ω K g) i)
      = resSection k Ω K g • f (resSection k Ω K g) i
        + resSection k Ω K g • f' (resSection k Ω K g) i
  rw [smul_add]

/-! ## The two inverse laws -/

/-- `γ' · f γ'` only depends on `res γ'`. -/
theorem coind_smul_self_eq (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ))
    (γ : Ω ≃ₐ[k] Ω) (u : K.fixingSubgroup) :
    ((γ * (u : Ω ≃ₐ[k] Ω)) • f (γ * (u : Ω ≃ₐ[k] Ω))) = γ • f γ := by
  rw [Coind.coe_mul]
  show (γ * (u : Ω ≃ₐ[k] Ω)) • ((u : Ω ≃ₐ[k] Ω)⁻¹ • f γ) = γ • f γ
  have hcoe : (γ * (u : Ω ≃ₐ[k] Ω)) * ((u : Ω ≃ₐ[k] Ω)⁻¹) = γ := by
    rw [mul_assoc, ← Subgroup.coe_inv, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      mul_one]
  rw [← mul_smul, hcoe]

theorem coind_smul_self_lift_eq (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ))
    (γ γ' : Ω ≃ₐ[k] Ω) (h : SSGRoute.res k K γ' = SSGRoute.res k K γ) :
    γ' • f γ' = γ • f γ := by
  have hu : γ⁻¹ * γ' ∈ K.fixingSubgroup := by
    rw [← mem_fixingSubgroup_iff_res_eq_one, map_mul, map_inv, h, inv_mul_cancel]
  have hγγ' : γ * (⟨γ⁻¹ * γ', hu⟩ : K.fixingSubgroup) = γ' := by
    show γ * (γ⁻¹ * γ') = γ'
    group
  rw [← hγγ']
  exact coind_smul_self_eq (k := k) (Ω := Ω) (K := K) (n := n) f γ ⟨γ⁻¹ * γ', hu⟩

theorem coind_smul_self_lift_apply (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ))
    (γ γ' : Ω ≃ₐ[k] Ω) (h : SSGRoute.res k K γ' = SSGRoute.res k K γ) (i : Fin n) :
    γ' • f γ' i = γ • f γ i :=
  congrFun (coind_smul_self_lift_eq (k := k) (Ω := Ω) (K := K) (n := n) f γ γ' h) i

theorem ofCoind_toCoind (w : homCoindFree k Ω K n) : ofCoind k Ω K n (toCoind k Ω K n w) = w := by
  apply Work.SSGRoute.freeHomEquiv.injective
  rw [freeHomEquiv_ofCoind]
  funext i g
  show resSection k Ω K g • toCoind k Ω K n w (resSection k Ω K g) i
      = Work.SSGRoute.freeHomEquiv w i g
  rw [show toCoind k Ω K n w (resSection k Ω K g) i
      = (resSection k Ω K g)⁻¹ • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K (resSection k Ω K g))
          (basisV k Ω K n i 1)) from rfl,
    resSection_spec, ← mul_smul, mul_inv_cancel, one_smul, ρ_basisV,
    Work.SSGRoute.freeHomEquiv_apply]
  rfl

theorem toCoind_ofCoind (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ)) :
    toCoind k Ω K n (ofCoind k Ω K n f) = f := by
  apply Subtype.ext
  funext γ i
  show γ⁻¹ • ofCoind k Ω K n f ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1))
      = f γ i
  rw [ρ_basisV, ofCoind_apply_basis,
    coind_smul_self_lift_apply (k := k) (Ω := Ω) (K := K) (n := n) f γ
      (resSection k Ω K (SSGRoute.res k K γ))
      (resSection_spec (k := k) (Ω := Ω) (K := K) (SSGRoute.res k K γ)) i,
    ← mul_smul, inv_mul_cancel, one_smul]

end Main

theorem homCoindFree_coind_iso (k Ω : Type) [Field k] [CharZero k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (n : ℕ) :
    ∃ Φ : Work.SSGRoute.PT.homCoindFree k Ω K n ≃+
        Work.SSGRoute.PT.Coind (Ω ≃ₐ[k] Ω) (K.fixingSubgroup) (Fin n → Additive Ωˣ),
      ∀ (σ : Ω ≃ₐ[k] Ω) (w : Work.SSGRoute.PT.homCoindFree k Ω K n),
        Φ (σ • w) = σ • Φ w := by
  refine ⟨{ toFun := toCoind k Ω K n
            invFun := ofCoind k Ω K n
            left_inv := fun w => ofCoind_toCoind (k := k) (Ω := Ω) (K := K) (n := n) w
            right_inv := fun f => toCoind_ofCoind (k := k) (Ω := Ω) (K := K) (n := n) f
            map_add' := fun w w' => toCoind_add (k := k) (Ω := Ω) (K := K) (n := n) w w' }, ?_⟩
  intro σ w
  exact toCoind_smul (k := k) (Ω := Ω) (K := K) (n := n) σ w

/-- **The `IsEquivariant` form** of `homCoindFree_coind_iso`: the Shapiro isomorphism is
`Gal(Ω/k)`-equivariant in the sense of `Work.GroupCohomology.IsEquivariant` (the shape consumed by
the `E1a` computation). -/
theorem homCoindFree_coind_iso_conj (k Ω : Type) [Field k] [CharZero k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] (n : ℕ) :
    ∃ Zc : Work.SSGRoute.PT.homCoindFree k Ω K n ≃+
        Work.SSGRoute.PT.Coind (Ω ≃ₐ[k] Ω) (K.fixingSubgroup) (Fin n → Additive Ωˣ),
      Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Zc.toAddMonoidHom := by
  obtain ⟨Φ, hΦ⟩ := homCoindFree_coind_iso (k := k) (Ω := Ω) (K := K) (n := n)
  exact ⟨Φ, hΦ⟩

end

end Work.SSGRoute.PT
