import Mathlib
import Submission.Work.SSGRoute.PT.mkb_ld02_defs
import Submission.Work.SSGRoute.PT.finite_dualMod_tensor
import Submission.Work.SSGRoute.selfdual
import Submission.Work.SSGRoute.dualPairingEquiv
import Submission.Work.Shrinking.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Hom_ℤ(N, Ωˣ) ≅ (N ⊗ T)^∨` for `T` the cyclotomic dual of `μ_p`

The Tate-twist cancellation in the `ConjHom` shape needed by
`Work.SSGRoute.PT.h3_H3_conjHom_subsingleton`: for `N₁` a finite `𝔽_p[Gal(K/k)]`-module on which
the decomposition group `D_A = SSGRoute.decomp k A` acts compatibly with `res k K` (`hpinN`), the
additive group `Hom_ℤ(N₁, Ωˣ)` with its *conjugation* `D_A`-action is `D_A`-equivariantly
isomorphic to the *finite* module `N₁^∨(1) = DualMod p (N₁ ⊗ T)`, `T = μ_p^∨` (`IsCyclotomicDual`)
on which `D_A` acts through `res k K`.

The mathematics is the classical twist cancellation: since `N₁` is `p`-torsion, every additive
`f : N₁ →+ Ωˣ` lands in `Ωˣ[p] = μ_p = ⟨ζ⟩`, so `Hom_ℤ(N₁,Ωˣ) = Hom_{𝔽_p}(N₁, μ_p)`; the discrete
logarithm along `ζ` identifies this with `DualMod p N₁` (`conjIsoToHomAddEquiv` +
`Work.SSGRoute.dualEquiv_zpow`), and choosing `u : T ≃ₗ 𝔽_p` (a line, `hT.1`) transports
functionals along `L (n ⊗ t) = u t • n`.  Each step is equivariant only up to the cyclotomic twist
`c •` (`σζ = ζ^c`) and the two twists are inverse to each other because `T` carries the *inverse*
cyclotomic character (`hT.2`), so they cancel (`hL1`, `hL2` in the proof below).

The proof is the same route as the proved `Work.SSGRoute.SelfDual.dualPairingEquiv`
(`Work.SSGRoute.dualPairingEquiv_homCoind`), read in the opposite direction; it is written out
here so that the vanishing theorem `h3_H3_conjHom_subsingleton` is self-contained.
-/

open scoped TensorProduct Pointwise

namespace Work.SSGRoute.PT

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-! ## Auxiliary additive equivalences -/

/-- `ConjHom X C` is a copy of `X →+ C` (it carries a different action); forgetting the action is
an additive equivalence. -/
def conjIsoToHomAddEquiv {X : Type*} [AddCommGroup X] {C : Type*} [AddCommGroup C] :
    ConjHom X C ≃+ (X →+ C) where
  toFun f := f.toHom
  invFun φ := ⟨φ⟩
  left_inv f := by cases f; rfl
  right_inv φ := rfl
  map_add' f g := rfl

@[simp] lemma conjIsoToHomAddEquiv_apply {X : Type*} [AddCommGroup X] {C : Type*}
    [AddCommGroup C] (f : ConjHom X C) : conjIsoToHomAddEquiv f = f.toHom := rfl

/-- Precomposition with a linear equivalence, on duals: `ψ ↦ ψ ∘ e`. -/
def conjIsoDualPrecompAddEquiv {R : Type*} [Semiring R] {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) : (N →ₗ[R] R) ≃+ (M →ₗ[R] R) where
  toFun ψ := ψ.comp (e : M →ₗ[R] N)
  invFun φ := φ.comp (e.symm : N →ₗ[R] M)
  left_inv ψ := by ext x; simp
  right_inv φ := by ext y; simp
  map_add' ψ ψ' := by ext x; rfl

@[simp] lemma conjIsoDualPrecompAddEquiv_apply {R : Type*} [Semiring R] {M N : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N)
    (ψ : N →ₗ[R] R) (x : M) : conjIsoDualPrecompAddEquiv e ψ x = ψ (e x) := rfl

/-- An additive equivalence of `𝔽_p`-modules is `𝔽_p`-linear. -/
lemma conjIsoAddEquivSmul {p : ℕ} [NeZero p] {M N : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] (ρ : M ≃+ N) (c : ZMod p) (x : M) :
    ρ (c • x) = c • ρ x := by
  rw [Work.SSGRoute.zmod_smul_eq_val_nsmul c x, Work.SSGRoute.zmod_smul_eq_val_nsmul c (ρ x)]
  exact map_nsmul (ρ : M →+ N) c.val x

/-- `x ↦ ζu^x` is injective. -/
lemma conjIsoZetaPowHom_injective {A : Type*} [CommRing A] [IsDomain A] {p : ℕ} [Fact p.Prime]
    (ζu : Aˣ) (hζu : IsPrimitiveRoot ζu p) :
    Function.Injective (Work.SSGRoute.zetaPowHom ζu hζu) := by
  intro a b hab
  have h3 : (hζu.zmodEquivZPowers a : ↥(Subgroup.zpowers ζu))
      = (hζu.zmodEquivZPowers b : ↥(Subgroup.zpowers ζu)) := by
    have h4 := congrArg Additive.toMul hab
    simpa [Work.SSGRoute.zetaPowHom, MonoidHom.toAdditive] using h4
  exact hζu.zmodEquivZPowers.injective (by simpa using congrArg Additive.ofMul h3)

/-! ## The twist cancellation -/

theorem conjHomUnits_dualMod_tensor_addEquiv
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω)
    (N₁ : Type) [AddCommGroup N₁] [Module (ZMod p) N₁]
      [DistribMulAction (K ≃ₐ[k] K) N₁] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N₁] [Finite N₁]
    [instN : DistribMulAction ↥(SSGRoute.decomp k A) N₁]
    (hpinN : ∀ (σ : ↥(SSGRoute.decomp k A)) (n : N₁),
      σ • n = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • n) :
    ∃ e : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω)) ≃+
        Work.SSGRoute.DualMod p (TensorProduct (ZMod p) N₁ T),
      (letI : DistribMulAction ↥(SSGRoute.decomp k A)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) N₁ T)) :=
        Work.SSGRoute.decompDistribMulAction K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) N₁ T)) A
       ∀ (σ : ↥(SSGRoute.decomp k A)) (f : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))),
        e (σ • f) = σ • e f) := by
  classical
  -- the action of `D_A` on the target, as in the statement
  letI : DistribMulAction ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) N₁ T)) :=
    Work.SSGRoute.decompDistribMulAction K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) N₁ T)) A
  haveI hNp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- `ζ` as a unit, and `ζu` is a primitive `p`-th root of unity
  let ζu : Ωˣ := (hζ.isUnit hNp.out).unit
  have hζu_coe : (ζu : Ω) = ζ := IsUnit.unit_spec _
  have hζu : IsPrimitiveRoot ζu p := by
    have h2 : IsPrimitiveRoot (ζu : Ω) p := by rw [hζu_coe]; exact hζ
    exact IsPrimitiveRoot.coe_units_iff.mp h2
  haveI hTf : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  -- a `𝔽_p`-basis of the line `T`
  let u : T ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.ofFinrankEq (R := ZMod p) T (ZMod p) (by rw [hT.1, Module.finrank_self])
  -- the identification `N₁ ⊗ T ≃ N₁`, `n ⊗ t ↦ u t • n`
  let L : TensorProduct (ZMod p) N₁ T ≃ₗ[ZMod p] N₁ :=
    (TensorProduct.congr (LinearEquiv.refl (ZMod p) N₁) u).trans (TensorProduct.rid (ZMod p) N₁)
  have hL : ∀ (n : N₁) (t : T), L (n ⊗ₜ[ZMod p] t) = u t • n := by
    intro n t
    simp [L, TensorProduct.congr_tmul]
  -- step 1: discrete logarithm along `ζ` (with the conjugation action on the source)
  let Ψ' : ConjHom N₁ (Additive (Units Ω)) ≃+ Work.SSGRoute.DualMod p N₁ :=
    conjIsoToHomAddEquiv.trans (Work.SSGRoute.dualEquiv_zpow p ζu hζu N₁).symm
  -- step 2: transport of functionals along `L`
  let ρ : Work.SSGRoute.DualMod p N₁ ≃+ Work.SSGRoute.DualMod p (TensorProduct (ZMod p) N₁ T) :=
    conjIsoDualPrecompAddEquiv (R := ZMod p) L
  let e : ConjHom N₁ (Additive (Units Ω)) ≃+
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) N₁ T) := Ψ'.trans ρ
  -- the defining property of `Ψ'`: `ζ ^ (Ψ' f n) = f n`
  have hΨ' : ∀ (f : ConjHom N₁ (Additive (Units Ω))) (n : N₁),
      Work.SSGRoute.zetaPowHom ζu hζu ((Ψ' f) n) = f n := by
    intro f n
    show Work.SSGRoute.zetaPowHom ζu hζu
      (((Work.SSGRoute.dualEquiv_zpow p ζu hζu N₁).symm f.toHom) n) = f n
    rw [← Work.SSGRoute.dualEquiv_zpow_apply p ζu hζu N₁ _ n, AddEquiv.apply_symm_apply]
    rfl
  refine ⟨e, fun σ f => ?_⟩
  -- `c` is the cyclotomic character value: `σ ζ = ζ ^ c`
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (σ : Ω ≃ₐ[k] Ω) • ζ = ζ ^ c := by
    have hpow : ((σ : Ω ≃ₐ[k] Ω) • ζ) ^ p = 1 := by
      rw [show ((σ : Ω ≃ₐ[k] Ω) • ζ) = (σ : Ω ≃ₐ[k] Ω) ζ from rfl, ← map_pow, hζ.pow_eq_one,
        map_one]
    obtain ⟨c, -, hc⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hζ hpow
    exact ⟨c, hc.symm⟩
  -- the same relation, for the unit `ζu`
  have hσu : (σ : Ω ≃ₐ[k] Ω) • ζu = ζu ^ c := by
    apply Units.ext
    rw [show ((↑((σ : Ω ≃ₐ[k] Ω) • ζu) : Ω)) = (σ : Ω ≃ₐ[k] Ω) • (↑ζu : Ω) from rfl, hζu_coe, hc,
      Units.val_pow_eq_pow_val, hζu_coe]
  -- step 1 is equivariant up to the twist `c •` (the character of `μ_p`)
  have hL1 : Ψ' (σ • f) = (c : ZMod p) • (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • Ψ' f) := by
    apply LinearMap.ext
    intro n
    apply conjIsoZetaPowHom_injective ζu hζu
    rw [LinearMap.smul_apply, DualMod.dualSMul_apply,
      show (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹
        = SSGRoute.res k K (σ⁻¹ : ↥(SSGRoute.decomp k A)) from by
        rw [← map_inv (SSGRoute.res k K) (σ : Ω ≃ₐ[k] Ω)]; rfl]
    rw [hΨ' (σ • f) n, ConjHom.smul_apply, hpinN σ⁻¹ n]
    rw [← hΨ' f (SSGRoute.res k K (σ⁻¹ : ↥(SSGRoute.decomp k A)) • n)]
    rw [show (c : ZMod p) • ((Ψ' f) (SSGRoute.res k K (σ⁻¹ : ↥(SSGRoute.decomp k A)) • n))
        = c • ((Ψ' f) (SSGRoute.res k K (σ⁻¹ : ↥(SSGRoute.decomp k A)) • n)) from
      Nat.cast_smul_eq_nsmul (ZMod p) c _]
    exact Work.SSGRoute.zetaPowHom_smul ζu hζu (σ : Ω ≃ₐ[k] Ω) hσu _
  -- step 2 is equivariant up to the inverse twist (the character of `T` is `c⁻¹`)
  have hL2 : SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • ρ (Ψ' f)
      = (c : ZMod p) • ρ (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • Ψ' f) := by
    have hct : ∀ t : T, (c : ZMod p) • (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • t) = t := by
      intro t
      rw [Nat.cast_smul_eq_nsmul (ZMod p) c]
      exact hT.2 (σ : Ω ≃ₐ[k] Ω) c hc t
    have hres : ∀ t : T, (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹ • t = (c : ZMod p) • t := by
      intro t
      have h := hct ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹ • t)
      rw [smul_inv_smul] at h
      exact h.symm
    suffices hgen : ∀ ψ : Work.SSGRoute.DualMod p N₁,
        SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • ρ ψ
          = (c : ZMod p) • ρ (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • ψ) from hgen (Ψ' f)
    intro ψ
    apply LinearMap.ext
    intro x
    refine TensorProduct.induction_on (motive := fun x => (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • ρ ψ) x
          = ((c : ZMod p) • ρ (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • ψ)) x) x ?_ ?_ ?_
    · simp
    · intro n t
      have hres' : u ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹ • t)
          = (c : ZMod p) * u t := by
        rw [hres t, map_smul, smul_eq_mul]
      calc ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) • ρ ψ) (n ⊗ₜ[ZMod p] t)
          = (ρ ψ) ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹ • (n ⊗ₜ[ZMod p] t)) :=
            DualMod.dualSMul_apply p _ _ _
        _ = (ρ ψ) (((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹ • n)
              ⊗ₜ[ZMod p] ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹ • t)) := by
            rw [Work.Shrinking.diagTensor_smul_tmul]
        _ = ψ (u ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹ • t)
              • ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹ • n)) := by
            rw [conjIsoDualPrecompAddEquiv_apply, hL]
        _ = ψ (((c : ZMod p) * u t) • ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹ • n)) := by
            rw [hres']
        _ = (c : ZMod p) • (ψ (u t • ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹ • n))) := by
            rw [mul_smul, map_smul]
        _ = (c : ZMod p) • (ψ ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹ • (u t • n))) := by
            rw [← smul_comm ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹) (u t) n]
        _ = (c : ZMod p) • (((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) • ψ) (u t • n)) := by
            rw [DualMod.dualSMul_apply]
        _ = (c : ZMod p) • ((ρ ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) • ψ))
              (n ⊗ₜ[ZMod p] t)) := by
            rw [conjIsoDualPrecompAddEquiv_apply, hL]
        _ = ((c : ZMod p) • ρ ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) • ψ))
              (n ⊗ₜ[ZMod p] t) := by
            rw [LinearMap.smul_apply]
    · intro y z hy hz
      rw [map_add, map_add, hy, hz]
  -- the twists cancel
  have hlast : SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • e f = σ • e f := rfl
  rw [← hlast]
  calc e (σ • f) = ρ (Ψ' (σ • f)) := rfl
    _ = ρ ((c : ZMod p) • (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • Ψ' f)) := by rw [hL1]
    _ = (c : ZMod p) • ρ (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • Ψ' f) :=
          conjIsoAddEquivSmul ρ (c : ZMod p) (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • Ψ' f)
    _ = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • ρ (Ψ' f) := hL2.symm
    _ = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • e f := rfl

end Work.SSGRoute.PT
