import Mathlib
import Submission.Work.SSGRoute.ExtChain.subsingleton_ext_fpRegular
import Submission.Work.SSGRoute.ExtChain.ext_iso_subsingleton
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The dévissage base case for the twisted dual of the free rank-one module

`Coeff = ULift ℤ`, so `Ext` in `Rep Coeff G` is `Ext` over `ℤ[G]`.  This file proves

`Ext^{≥2}_G (DualMod p (𝔽_p[G] ⊗ T), A) = 0`

for a **one-dimensional** `𝔽_p[G]`-module `T` (here `DualMod p X = Hom_{𝔽_p}(X, μ_p)`, modelled as
the `𝔽_p`-linear dual with the contragredient action).  The point is that for `dim T = 1` the module
`N := DualMod p (𝔽_p[G] ⊗ T)` is (non-canonically) **the regular module `𝔽_p[G]`**:

fix `e : T ≃ₗ[𝔽_p] 𝔽_p`, let `t₀ = e⁻¹ 1` (so `e t₀ = 1` and `t = (e t) • t₀` for all `t`), and let
`α g := e (g • t₀)`, so that `g • t = α g • t` for all `t` and `α : G → 𝔽_pˣ`.  Then

  `Ψ f := ∑_{σ : G} (α σ * f (e_σ ⊗ t₀)) • e_σ`   (`e_σ = single σ 1`)

is a `G`-equivariant `𝔽_p`-linear isomorphism `N ≅ 𝔽_p[G]`.  Equivariance is exactly where the twist
`α` is needed: the contragredient action gives
`(g • f)(e_τ ⊗ t₀) = f(g⁻¹ • (e_τ ⊗ t₀)) = f(e_{g⁻¹τ} ⊗ ((α g)⁻¹ • t₀)) = (α g)⁻¹ * f(e_{g⁻¹τ} ⊗ t₀)`,
while `(g • Ψ f).coeff τ = (Ψ f).coeff (g⁻¹ * τ) = α (g⁻¹ τ) * f (e_{g⁻¹τ} ⊗ t₀)`, and
`α (g⁻¹ τ) = (α g)⁻¹ * α τ`.

Composing with the already-proved dévissage base case `subsingleton_ext_fpRegular` for the regular
module, and transporting `Subsingleton` along the induced isomorphism of `Ext` groups
(`ext_iso_subsingleton`), gives the claim.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory
open scoped TensorProduct

namespace Work.SSGRoute.ExtChain

noncomputable section

/-! ## `Coeff`-linearity of additive maps

`Coeff = ULift ℤ` acts on an additive group through the canonical `ℤ`-action, which every additive
map preserves.  This lets us build the two maps below as additive maps only and lift them to
`Rep Coeff G`-linear maps for free. -/

/-- Every additive map between additive groups is `Coeff = ULift ℤ`-linear. -/
-- NOTE (name clash): the same helper is declared in `ExtChain/dualMod_tensor_regular_iso.lean` and
-- in `ExtChain/ext2_fn_two_helpers.lean`; this copy is `private` so that a module may import this
-- file together with those (needed by `ExtChain/himg_of_ideles_input_fin_clean.lean`).
private def coeffLinearMapOfAddHom {M N : Type} [AddCommGroup M] [AddCommGroup N] (f : M →+ N) :
    M →ₗ[SSGRoute.PTExt.Coeff] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := by
    intro c x
    show f (c • x) = c • f x
    rw [ULift.smul_def, ULift.smul_def]
    exact map_zsmul f c.down x

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]
variable {T : Type} [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
  [SMulCommClass G (ZMod p) T]

/-! ## The standard basis of `𝔽_p[G]` -/

/-- The element `e_σ = single σ 1` of the group algebra. -/
def stdVec (σ : G) : MonoidAlgebra (ZMod p) G := MonoidAlgebra.single σ 1

@[simp] theorem stdVec_coeff_self (σ : G) : (stdVec (p := p) σ).coeff σ = 1 := by
  simp [stdVec, MonoidAlgebra.coeff_single]

theorem stdVec_coeff_of_ne {σ τ : G} (h : σ ≠ τ) : (stdVec (p := p) σ).coeff τ = 0 := by
  rw [stdVec, MonoidAlgebra.coeff_single]
  exact Finsupp.single_eq_of_ne h.symm

/-- The standard vectors span: `x = ∑_σ (coeff_σ x) • e_σ`. -/
theorem sum_coeff_smul_stdVec (x : MonoidAlgebra (ZMod p) G) :
    (∑ σ : G, (x.coeff σ) • stdVec (p := p) σ) = x := by
  conv_rhs => rw [Work.CohomologicalShrinking.eq_sum_coeff_smul_single p G x]
  exact Finset.sum_congr rfl (fun σ _ => by rw [stdVec])

/-- The rule for the left regular action on coefficients. -/
theorem smul_coeff (g : G) (x : MonoidAlgebra (ZMod p) G) (τ : G) :
    (g • x).coeff τ = x.coeff (g⁻¹ * τ) := by
  rw [Work.CohomologicalShrinking.smul_monoidAlgebra p G g x,
    MonoidAlgebra.coeff_single_mul_apply, one_mul]

/-- The left regular action on the standard basis. -/
theorem smul_stdVec (g σ : G) : g • stdVec (p := p) σ = stdVec (p := p) (g * σ) := by
  show g • MonoidAlgebra.single σ 1 = MonoidAlgebra.single (g * σ) 1
  rw [Work.CohomologicalShrinking.smul_monoidAlgebra p G g (MonoidAlgebra.single σ 1),
    MonoidAlgebra.single_mul_single, mul_one]

/-! ### Cancellation of the twist -/

theorem mul_inv_cancel_aux {p : ℕ} [Fact p.Prime] {a b : ZMod p} (ha : a ≠ 0) :
    a * (b * a⁻¹) = b := by
  rw [mul_comm b a⁻¹, ← mul_assoc, mul_comm a a⁻¹, inv_mul_cancel₀ ha, one_mul]

theorem twist_cancel {p : ℕ} [Fact p.Prime] {a b c : ZMod p} (ha : a ≠ 0) :
    (a * b) * (a⁻¹ * c) = b * c := by
  rw [mul_mul_mul_comm, mul_comm a a⁻¹, inv_mul_cancel₀ ha, one_mul]

/-! ## A generator `t₀`, its dual functional `e`, and the character `α` -/

theorem exists_linearEquiv_of_finrank_eq_one (hT1 : Module.finrank (ZMod p) T = 1) :
    Nonempty (T ≃ₗ[ZMod p] ZMod p) := by
  have hfin : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT1]; norm_num)
  exact ⟨LinearEquiv.ofFinrankEq T (ZMod p) (by rw [hT1, Module.finrank_self])⟩

variable (e : T ≃ₗ[ZMod p] ZMod p)

/-- A generator of the one-dimensional module `T`: `t₀ = e⁻¹ 1`. -/
def t0 : T := e.symm 1

theorem e_t0 : e (t0 e) = 1 := by
  simp [t0]

theorem t0_ne_zero : t0 e ≠ 0 := by
  intro h
  have h1 : e (t0 e) = 0 := by rw [h, map_zero]
  rw [e_t0 e] at h1
  exact one_ne_zero h1

/-- `e` of a multiple of `t₀`. -/
theorem e_smul_t0 (c : ZMod p) : e (c • t0 e) = c := by
  rw [t0, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

/-- `t₀` generates `T`. -/
theorem smul_t0_eq (t : T) : e t • t0 e = t := by
  refine e.injective ?_
  rw [map_smul, e_t0 e, smul_eq_mul, mul_one]

/-- The multiplier of `t₀` is determined by the vector. -/
theorem smul_t0_injective {c d : ZMod p} (h : c • t0 e = d • t0 e) : c = d := by
  have h' := congrArg e h
  rw [e_smul_t0, e_smul_t0] at h'
  exact h'

/-- The character of the one-dimensional `G`-module `T`: `g • t₀ = α g • t₀`. -/
def alpha (g : G) : ZMod p := e (g • t0 e)

theorem alpha_smul_t0 (g : G) : g • t0 e = alpha e g • t0 e :=
  (smul_t0_eq e (g • t0 e)).symm

/-- The character relation on all of `T`. -/
theorem e_smul (g : G) (t : T) : e (g • t) = alpha e g * e t := by
  have h : g • t = (e t * alpha e g) • t0 e := by
    conv_lhs => rw [← smul_t0_eq e t]
    rw [smul_comm, alpha_smul_t0 e g, smul_smul]
  rw [h, e_smul_t0, mul_comm]

theorem alpha_one : alpha e (1 : G) = 1 := by
  rw [alpha, one_smul, e_t0]

theorem alpha_mul (g h : G) : alpha e (g * h) = alpha e g * alpha e h := by
  have h2 : alpha e (g * h) • t0 e = (alpha e g * alpha e h) • t0 e := by
    rw [← alpha_smul_t0 e (g * h), mul_smul, alpha_smul_t0 e h, smul_comm, alpha_smul_t0 e g,
      smul_smul, mul_comm]
  exact smul_t0_injective e h2

theorem alpha_mul_inv (g : G) : alpha e g * alpha e g⁻¹ = 1 := by
  rw [← alpha_mul e g g⁻¹, mul_inv_cancel, alpha_one]

theorem alpha_inv (g : G) : alpha e g⁻¹ = (alpha e g)⁻¹ :=
  eq_inv_of_mul_eq_one_right (alpha_mul_inv e g)

theorem alpha_ne_zero (g : G) : alpha e g ≠ 0 := by
  intro h
  have h1 := alpha_mul_inv e g
  rw [h, zero_mul] at h1
  exact one_ne_zero h1.symm

theorem alpha_inv_smul_t0 (g : G) : g⁻¹ • t0 e = (alpha e g)⁻¹ • t0 e := by
  rw [alpha_smul_t0 e g⁻¹, alpha_inv e g]

/-! ## The two maps `Φ` and `Ψ` -/

/-- The functional `θ_σ (v ⊗ t) = (e t) * (α σ)⁻¹ * (coeff_σ v)`. -/
def theta (σ : G) : (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) T) →ₗ[ZMod p] ZMod p :=
  TensorProduct.lift
    { toFun := fun v => (e : T →ₗ[ZMod p] ZMod p).smulRight ((alpha e σ)⁻¹ * v.coeff σ)
      map_add' := by
        intro v w
        ext t
        rw [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.smulRight_apply,
          LinearMap.smulRight_apply, MonoidAlgebra.coeff_add, Finsupp.add_apply, smul_eq_mul,
          smul_eq_mul, smul_eq_mul]
        ring
      map_smul' := by
        intro c v
        ext t
        rw [LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.smulRight_apply,
          MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul,
          RingHom.id_apply]
        ring }

@[simp] theorem theta_tmul (σ : G) (v : MonoidAlgebra (ZMod p) G) (t : T) :
    theta e σ (v ⊗ₜ[ZMod p] t) = e t * ((alpha e σ)⁻¹ * v.coeff σ) := by
  rw [theta, TensorProduct.lift.tmul]
  show (e : T →ₗ[ZMod p] ZMod p).smulRight ((alpha e σ)⁻¹ * v.coeff σ) t
      = e t * ((alpha e σ)⁻¹ * v.coeff σ)
  rw [LinearMap.smulRight_apply, smul_eq_mul]
  simp

/-- `Ψ`, the additive isomorphism `(𝔽_p[G] ⊗ T)^∨ → 𝔽_p[G]`. -/
def psiHom : ((TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) T) →ₗ[ZMod p] ZMod p) →+
    MonoidAlgebra (ZMod p) G where
  toFun f := ∑ σ : G, (alpha e σ * f (stdVec (p := p) σ ⊗ₜ[ZMod p] t0 e)) • stdVec (p := p) σ
  map_zero' := by simp
  map_add' f g := by
    simp only [LinearMap.add_apply, mul_add, add_smul, Finset.sum_add_distrib]

/-- `Φ`, the inverse of `Ψ`. -/
def phiHom : MonoidAlgebra (ZMod p) G →+
    ((TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) T) →ₗ[ZMod p] ZMod p) where
  toFun x := ∑ σ : G, (x.coeff σ) • theta e σ
  map_zero' := by simp
  map_add' x y := by
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]

@[simp] theorem psiHom_apply
    (f : (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) T) →ₗ[ZMod p] ZMod p) :
    psiHom e f
      = ∑ σ : G, (alpha e σ * f (stdVec (p := p) σ ⊗ₜ[ZMod p] t0 e)) • stdVec (p := p) σ :=
  rfl

@[simp] theorem phiHom_apply (x : MonoidAlgebra (ZMod p) G) :
    phiHom e x = ∑ σ : G, (x.coeff σ) • theta e σ := rfl

/-- The coefficient of `Ψ f`. -/
@[simp] theorem psiHom_coeff
    (f : (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) T) →ₗ[ZMod p] ZMod p) (τ : G) :
    (psiHom e f).coeff τ = alpha e τ * f (stdVec (p := p) τ ⊗ₜ[ZMod p] t0 e) := by
  rw [psiHom_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single τ]
  · rw [stdVec_coeff_self, mul_one]
  · intro σ _ hσ
    rw [stdVec_coeff_of_ne (τ := τ) hσ, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ τ) h

/-- The value of `Φ x` on a pure tensor. -/
theorem phiHom_tmul (x : MonoidAlgebra (ZMod p) G) (v : MonoidAlgebra (ZMod p) G) (t : T) :
    phiHom e x (v ⊗ₜ[ZMod p] t)
      = e t * ∑ σ : G, (x.coeff σ) * ((alpha e σ)⁻¹ * v.coeff σ) := by
  rw [phiHom_apply, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [LinearMap.smul_apply, smul_eq_mul, theta_tmul]
  ring

/-- `f` applied to a multiple of `t₀` in the second tensor factor. -/
theorem apply_smul_t0
    (f : (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) T) →ₗ[ZMod p] ZMod p)
    (v : MonoidAlgebra (ZMod p) G) (c : ZMod p) :
    f (v ⊗ₜ[ZMod p] (c • t0 e)) = c * f (v ⊗ₜ[ZMod p] t0 e) := by
  rw [TensorProduct.tmul_smul, map_smul, smul_eq_mul]

/-- `f` on an element built from the standard basis. -/
theorem apply_smul_stdVec_tmul
    (f : (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) T) →ₗ[ZMod p] ZMod p)
    (c : ZMod p) (σ : G) (t : T) :
    f ((c • stdVec (p := p) σ) ⊗ₜ[ZMod p] t)
      = e t * (c * f (stdVec (p := p) σ ⊗ₜ[ZMod p] t0 e)) := by
  rw [← TensorProduct.smul_tmul', map_smul, smul_eq_mul]
  have h : stdVec (p := p) σ ⊗ₜ[ZMod p] t
      = (e t) • (stdVec (p := p) σ ⊗ₜ[ZMod p] t0 e) := by
    conv_lhs => rw [← smul_t0_eq e t]
    rw [TensorProduct.tmul_smul]
  rw [h, map_smul, smul_eq_mul]
  ring

/-- The expansion of `f (v ⊗ t)` in the basis `e_σ`. -/
theorem apply_tmul_expansion
    (f : (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) T) →ₗ[ZMod p] ZMod p)
    (v : MonoidAlgebra (ZMod p) G) (t : T) :
    f (v ⊗ₜ[ZMod p] t)
      = e t * ∑ σ : G, (v.coeff σ) * f (stdVec (p := p) σ ⊗ₜ[ZMod p] t0 e) := by
  have h : ∀ σ : G, f ((v.coeff σ • stdVec (p := p) σ) ⊗ₜ[ZMod p] t)
      = e t * (v.coeff σ * f (stdVec (p := p) σ ⊗ₜ[ZMod p] t0 e)) :=
    fun σ => apply_smul_stdVec_tmul e f (v.coeff σ) σ t
  conv_lhs => rw [← sum_coeff_smul_stdVec v]
  rw [TensorProduct.sum_tmul, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun σ _ => h σ)

/-- `Φ ∘ Ψ = id`. -/
theorem phiHom_psiHom
    (f : (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) T) →ₗ[ZMod p] ZMod p) :
    phiHom e (psiHom e f) = f := by
  refine LinearMap.ext (fun m => ?_)
  refine TensorProduct.induction_on (motive := fun m => phiHom e (psiHom e f) m = f m) m ?_ ?_ ?_
  · simp
  · intro v t
    rw [phiHom_tmul, apply_tmul_expansion]
    congr 1
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [psiHom_coeff, twist_cancel (alpha_ne_zero e σ)]
    ring
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

/-- `Ψ ∘ Φ = id`. -/
theorem psiHom_phiHom (x : MonoidAlgebra (ZMod p) G) : psiHom e (phiHom e x) = x := by
  refine MonoidAlgebra.ext (Finsupp.ext (fun τ => ?_))
  rw [psiHom_coeff]
  have hval : phiHom e x (stdVec (p := p) τ ⊗ₜ[ZMod p] t0 e) = x.coeff τ * (alpha e τ)⁻¹ := by
    rw [phiHom_tmul, e_t0, one_mul]
    rw [Finset.sum_eq_single τ]
    · rw [stdVec_coeff_self, mul_one]
    · intro σ _ hσ
      rw [stdVec_coeff_of_ne (σ := τ) (τ := σ) hσ.symm, mul_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ τ) h
  rw [hval, mul_inv_cancel_aux (alpha_ne_zero e τ)]

/-! ## `G`-equivariance of `Ψ` -/

theorem smul_inv_stdVec_tmul_t0 (g τ : G) :
    g⁻¹ • (stdVec (p := p) τ ⊗ₜ[ZMod p] t0 e)
      = stdVec (p := p) (g⁻¹ * τ) ⊗ₜ[ZMod p] ((alpha e g)⁻¹ • t0 e) := by
  rw [Work.Shrinking.diagTensor_smul_tmul, smul_stdVec, alpha_inv_smul_t0]

/-- `Ψ` is `G`-equivariant for the contragredient action on the dual and the regular action. -/
theorem psiHom_smul
    (g : G) (f : (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) T) →ₗ[ZMod p] ZMod p) :
    psiHom e (g • f) = g • psiHom e f := by
  refine MonoidAlgebra.ext (Finsupp.ext (fun τ => ?_))
  rw [psiHom_coeff, Work.SSGRoute.DualMod.dualSMul_apply, smul_inv_stdVec_tmul_t0,
    apply_smul_t0, smul_coeff, psiHom_coeff, alpha_mul, alpha_inv]
  ring

/-! ## The isomorphism `N ≅ 𝔽_p[G]` and the vanishing in degrees `≥ 2` -/

/-- **`DualMod p (𝔽_p[G] ⊗ T)` is the regular module for a one-dimensional `T`.** -/
theorem nonempty_iso_dualMod_rankOne (hT1 : Module.finrank (ZMod p) T = 1) :
    Nonempty (SSGRoute.PTExt.modRep G (Work.SSGRoute.DualMod p
        (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) T))
      ≅ SSGRoute.PTExt.modRep G (MonoidAlgebra (ZMod p) G)) := by
  obtain ⟨e⟩ := exists_linearEquiv_of_finrank_eq_one (T := T) hT1
  refine ⟨Rep.mkIso (Representation.Equiv.mk
    (LinearEquiv.mk (toLinearMap := coeffLinearMapOfAddHom (psiHom e))
      (invFun := coeffLinearMapOfAddHom (phiHom e))
      (fun f => phiHom_psiHom e f) (fun x => psiHom_phiHom e x)) ?_)⟩
  intro g
  refine LinearMap.ext (fun f => ?_)
  show psiHom e (g • f) = g • psiHom e f
  exact psiHom_smul e g f

end

end Work.SSGRoute.ExtChain

namespace Work.SSGRoute.ExtChain

theorem subsingleton_ext_dualMod_regular_rankOne (p : ℕ) [Fact p.Prime] (G : Type) [Group G]
    [Fintype G] (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (hT1 : Module.finrank (ZMod p) T = 1)
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) (r : ℕ) (hr : 2 ≤ r) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (SSGRoute.PTExt.modRep G (Work.SSGRoute.DualMod p
        (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) T))) A r) := by
  obtain ⟨e⟩ := nonempty_iso_dualMod_rankOne (p := p) (G := G) (T := T) hT1
  exact (ext_iso_subsingleton e r).mpr (subsingleton_ext_fpRegular p G A r hr)

end Work.SSGRoute.ExtChain
