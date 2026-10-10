import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.ext_h1_bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The duality `E ≅ Hom(E ⊗ T, μ_p)^∨` for `T` the cyclotomic dual

`Work.SSGRoute.dualPairingEquiv`: for a finite `𝔽_p[Gal(K/k)]`-module `E`, a `Gal(K/k)`-module `T`
that is a line on which `Gal(K/k)` acts by the inverse cyclotomic character (`IsCyclotomicDual`,
`ζ ∈ K` a primitive `p`-th root of unity), there is a `Gal(Ω/k)`-equivariant additive isomorphism

  `E ≃+ (DualMod p (E ⊗ T) →+ Additive Ωˣ)`.

The proof proceeds through three elementary bricks:

* `zetaPowHom ζ hζ : ZMod p →+ Additive Ωˣ`, `x ↦ ζ^x`, whose range is the group `μ_p` of `p`-th
  roots of unity;
* `dualEquiv_zpow`: `(X →ₗ[𝔽_p] 𝔽_p) ≃+ (X →+ Additive Ωˣ)` for every `𝔽_p`-module `X` (the
  "image lands in `μ_p`" content);
* `zetaPowHom_smul`: `σ • ζ^x = ζ^{c x}` when `σ ζ = ζ^c`, the cyclotomic twist responsible for
  the equivariance.
-/

open scoped TensorProduct

namespace Work.SSGRoute

noncomputable def zetaPowHom {A : Type*} [CommRing A] {p : ℕ} (ζu : Aˣ)
    (hζu : IsPrimitiveRoot ζu p) : ZMod p →+ Additive Aˣ :=
  (MonoidHom.toAdditive (Subgroup.subtype (Subgroup.zpowers ζu))).comp
    hζu.zmodEquivZPowers.toAddMonoidHom

lemma zetaPowHom_coe_nat {A : Type*} [CommRing A] {p : ℕ} (ζu : Aˣ)
    (hζu : IsPrimitiveRoot ζu p) (n : ℕ) :
    zetaPowHom ζu hζu (n : ZMod p) = Additive.ofMul (ζu ^ n) := by
  simp [zetaPowHom, hζu.zmodEquivZPowers_apply_coe_nat]

lemma zmod_smul_eq_val_nsmul {p : ℕ} [NeZero p] {M : Type*} [AddCommMonoid M] [Module (ZMod p) M]
    (c : ZMod p) (x : M) : c • x = c.val • x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul]

private lemma dpe_nsmul_ofMul {G : Type*} [Group G] (n : ℕ) (u : G) :
    n • (Additive.ofMul u) = Additive.ofMul (u ^ n) := by
  induction n with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih, pow_succ]; rfl

lemma toMul_nsmul {G : Type*} [Group G] (n : ℕ) (y : Additive G) :
    Additive.toMul (n • y) = Additive.toMul y ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul]
    change Additive.toMul (k • y) * Additive.toMul y = Additive.toMul y ^ (k + 1)
    rw [ih, pow_succ]

noncomputable def dualEquiv_zpow (p : ℕ) [Fact p.Prime] {A : Type*} [CommRing A] [IsDomain A]
    (ζu : Aˣ) (hζu : IsPrimitiveRoot ζu p) (X : Type*) [AddCommGroup X] [Module (ZMod p) X] :
    (X →ₗ[ZMod p] ZMod p) ≃+ (X →+ Additive Aˣ) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hmem : ∀ (χ : X →+ Additive Aˣ) (x : X),
      Additive.toMul (χ x) ∈ Subgroup.zpowers ζu := by
    intro χ x
    have hp : p • χ x = 0 := by
      have hx : (p • x : X) = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x]; simp
      rw [← map_nsmul χ p x, hx, map_zero]
    have hpow : Additive.toMul (χ x) ^ p = 1 := by
      rw [← toMul_nsmul p (χ x)]
      simpa using congrArg Additive.toMul hp
    rw [hζu.zpowers_eq]
    exact (mem_rootsOfUnity p (Additive.toMul (χ x))).2 hpow
  let Theta : (X →ₗ[ZMod p] ZMod p) →+ (X →+ Additive Aˣ) :=
    { toFun := fun ψ => (zetaPowHom ζu hζu).comp ψ.toAddMonoidHom
      map_zero' := by ext x; simp
      map_add' := by intro ψ ψ'; ext x; simp [map_add] }
  let Psi : (X →+ Additive Aˣ) → (X →ₗ[ZMod p] ZMod p) := fun χ =>
    { toFun := fun x => hζu.zmodEquivZPowers.symm
          (Additive.ofMul (⟨Additive.toMul (χ x), hmem χ x⟩ : ↥(Subgroup.zpowers ζu)))
      map_add' := by
        intro x y
        have hw : (⟨Additive.toMul (χ (x + y)), hmem χ (x + y)⟩ : ↥(Subgroup.zpowers ζu))
            = (⟨Additive.toMul (χ x), hmem χ x⟩ : ↥(Subgroup.zpowers ζu))
              * (⟨Additive.toMul (χ y), hmem χ y⟩ : ↥(Subgroup.zpowers ζu)) := by
          apply Subtype.ext
          show Additive.toMul (χ (x + y)) = Additive.toMul (χ x) * Additive.toMul (χ y)
          rw [map_add]
          rfl
        have h : Additive.ofMul (⟨Additive.toMul (χ (x + y)), hmem χ (x + y)⟩ : ↥(Subgroup.zpowers ζu))
            = Additive.ofMul (⟨Additive.toMul (χ x), hmem χ x⟩ : ↥(Subgroup.zpowers ζu))
              + Additive.ofMul (⟨Additive.toMul (χ y), hmem χ y⟩ : ↥(Subgroup.zpowers ζu)) := hw
        rw [h]
        exact map_add hζu.zmodEquivZPowers.symm _ _
      map_smul' := by
        intro c x
        change hζu.zmodEquivZPowers.symm
            (Additive.ofMul (⟨Additive.toMul (χ (c • x)), hmem χ (c • x)⟩ : ↥(Subgroup.zpowers ζu)))
          = c • hζu.zmodEquivZPowers.symm
            (Additive.ofMul (⟨Additive.toMul (χ x), hmem χ x⟩ : ↥(Subgroup.zpowers ζu)))
        rw [zmod_smul_eq_val_nsmul c
              (hζu.zmodEquivZPowers.symm
                (Additive.ofMul (⟨Additive.toMul (χ x), hmem χ x⟩ : ↥(Subgroup.zpowers ζu)))),
          ← map_nsmul hζu.zmodEquivZPowers.symm c.val
              (Additive.ofMul (⟨Additive.toMul (χ x), hmem χ x⟩ : ↥(Subgroup.zpowers ζu))),
          dpe_nsmul_ofMul c.val (⟨Additive.toMul (χ x), hmem χ x⟩ : ↥(Subgroup.zpowers ζu))]
        have hw : (⟨Additive.toMul (χ (c • x)), hmem χ (c • x)⟩ : ↥(Subgroup.zpowers ζu))
            = (⟨Additive.toMul (χ x), hmem χ x⟩ : ↥(Subgroup.zpowers ζu)) ^ c.val := by
          apply Subtype.ext
          show Additive.toMul (χ (c • x)) = (Additive.toMul (χ x)) ^ c.val
          rw [show c • x = c.val • x from zmod_smul_eq_val_nsmul c x]
          rw [map_nsmul χ c.val x]
          exact toMul_nsmul c.val (χ x)
        have h : Additive.ofMul (⟨Additive.toMul (χ (c • x)), hmem χ (c • x)⟩ : ↥(Subgroup.zpowers ζu))
            = Additive.ofMul ((⟨Additive.toMul (χ x), hmem χ x⟩ : ↥(Subgroup.zpowers ζu)) ^ c.val) := hw
        rw [h] }
  have hleft : Function.LeftInverse Psi Theta := by
    intro ψ
    refine LinearMap.ext fun x => ?_
    dsimp only [Psi, Theta]
    simp [zetaPowHom, MonoidHom.toAdditive]
  have hright : Function.RightInverse Psi Theta := by
    intro χ
    refine AddMonoidHom.ext fun x => ?_
    dsimp only [Psi, Theta]
    simp [zetaPowHom, MonoidHom.toAdditive]
  exact AddEquiv.ofBijective Theta ⟨hleft.injective, hright.surjective⟩

@[simp] lemma dualEquiv_zpow_apply (p : ℕ) [Fact p.Prime] {A : Type*} [CommRing A] [IsDomain A]
    (ζu : Aˣ) (hζu : IsPrimitiveRoot ζu p) (X : Type*) [AddCommGroup X] [Module (ZMod p) X]
    (ψ : X →ₗ[ZMod p] ZMod p) (x : X) :
    dualEquiv_zpow p ζu hζu X ψ x = zetaPowHom ζu hζu (ψ x) := rfl

lemma zetaPowHom_smul {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {p : ℕ} [NeZero p]
    (ζu : Ωˣ) (hζu : IsPrimitiveRoot ζu p) (σ : Ω ≃ₐ[k] Ω) {c : ℕ}
    (hσ : σ • ζu = ζu ^ c) (x : ZMod p) :
    σ • zetaPowHom ζu hζu x = zetaPowHom ζu hζu (c • x) := by
  have hcx : c • (x.val : ZMod p) = ((c * x.val : ℕ) : ZMod p) := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) c (x.val : ZMod p), smul_eq_mul, ← Nat.cast_mul]
  rw [show x = (x.val : ZMod p) from (ZMod.natCast_zmod_val x).symm, hcx,
    zetaPowHom_coe_nat, zetaPowHom_coe_nat]
  rw [show σ • (Additive.ofMul (ζu ^ x.val) : Additive Ωˣ)
      = Additive.ofMul (σ • (ζu ^ x.val)) from rfl]
  rw [show σ • (ζu ^ x.val) = (σ • ζu) ^ x.val from by ext; simp]
  rw [hσ, pow_mul]


theorem dualPairingEquiv (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    ∃ Φ : E ≃+ (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) →+ Additive Ωˣ),
      (∀ (σ : Ω ≃ₐ[k] Ω) (e : E) (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        Φ ((SSGRoute.res k K σ) • e) φ = σ • (Φ e ((SSGRoute.res k K σ)⁻¹ • φ))) := by
  classical
  haveI hNp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let ζu : Ωˣ := (hζ.isUnit hNp.out).unit
  have hζu_coe : (ζu : Ω) = ζ := IsUnit.unit_spec _
  have hζu : IsPrimitiveRoot ζu p := by
    have : IsPrimitiveRoot (ζu : Ω) p := by rw [hζu_coe]; exact hζ
    exact IsPrimitiveRoot.coe_units_iff.mp this
  haveI hTf : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  let A := TensorProduct (ZMod p) E T
  haveI hAf : Module.Finite (ZMod p) A := by
    unfold A; exact Module.Finite.tensorProduct (ZMod p) E T
  haveI hAr : Module.IsReflexive (ZMod p) A := inferInstance
  let u : T ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.ofFinrankEq (R := ZMod p) T (ZMod p) (by rw [hT.1, Module.finrank_self])
  let t₀ : T := u.symm 1
  let isoE : E ≃ₗ[ZMod p] A :=
    (TensorProduct.rid (ZMod p) E).symm.trans
      ((TensorProduct.congr (LinearEquiv.refl (ZMod p) E) u).symm)
  have hisoE : ∀ e : E, isoE e = e ⊗ₜ[ZMod p] t₀ := by
    intro e
    rw [show isoE e = (TensorProduct.congr (LinearEquiv.refl (ZMod p) E) u).symm
        ((TensorProduct.rid (ZMod p) E).symm e) from rfl]
    rw [TensorProduct.rid_symm_apply, TensorProduct.congr_symm, TensorProduct.congr_tmul]
    simp [t₀]
  let Φ : E ≃+ (Work.SSGRoute.DualMod p A →+ Additive Ωˣ) :=
    ((isoE.toAddEquiv).trans ((Module.evalEquiv (ZMod p) A).toAddEquiv)).trans
      (dualEquiv_zpow p ζu hζu (Work.SSGRoute.DualMod p A))
  have hΦ : ∀ (e : E) (φ : Work.SSGRoute.DualMod p A),
      Φ e φ = zetaPowHom ζu hζu (φ (e ⊗ₜ[ZMod p] t₀)) := by
    intro e φ
    show dualEquiv_zpow p ζu hζu (Work.SSGRoute.DualMod p A)
        ((Module.evalEquiv (ZMod p) A) (isoE e)) φ = _
    rw [dualEquiv_zpow_apply, Module.evalEquiv_apply, Module.Dual.eval_apply, hisoE]
  refine ⟨Φ, ?_⟩
  intro σ e φ
  obtain ⟨c, hc⟩ : ∃ c : ℕ, σ • ζ = ζ ^ c := by
    have hpow : (σ • ζ) ^ p = 1 := by
      rw [show σ • ζ = σ ζ from rfl, ← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨c, -, hc⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hζ hpow
    exact ⟨c, hc.symm⟩
  have hσζu : σ • ζu = ζu ^ c := by
    apply Units.ext
    rw [show (↑(σ • ζu) : Ω) = σ • (↑ζu : Ω) from rfl, hζu_coe, hc,
      Units.val_pow_eq_pow_val, hζu_coe]
  have hkey : ∀ x : ZMod p, σ • zetaPowHom ζu hζu x = zetaPowHom ζu hζu (c • x) :=
    fun x => zetaPowHom_smul ζu hζu σ hσζu x
  have hTt : (c : ZMod p) • ((SSGRoute.res k K σ) • t₀) = t₀ := by
    rw [Nat.cast_smul_eq_nsmul (ZMod p) c ((SSGRoute.res k K σ) • t₀)]
    exact hT.2 σ c hc t₀
  have hz : (c : ZMod p) • ((SSGRoute.res k K σ) • (e ⊗ₜ[ZMod p] t₀))
      = ((SSGRoute.res k K σ) • e) ⊗ₜ[ZMod p] t₀ := by
    rw [Work.Shrinking.diagTensor_smul_tmul]
    rw [← TensorProduct.tmul_smul (c : ZMod p) ((SSGRoute.res k K σ) • e)
      ((SSGRoute.res k K σ) • t₀)]
    rw [hTt]
  rw [hΦ (SSGRoute.res k K σ • e) φ, hΦ e ((SSGRoute.res k K σ)⁻¹ • φ)]
  rw [show ((SSGRoute.res k K σ)⁻¹ • φ) (e ⊗ₜ[ZMod p] t₀)
      = φ ((SSGRoute.res k K σ) • (e ⊗ₜ[ZMod p] t₀)) from by
    rw [Work.SSGRoute.DualMod.dualSMul_apply]; simp]
  rw [← hz, map_smul]
  rw [show (c : ZMod p) • (φ ((SSGRoute.res k K σ) • (e ⊗ₜ[ZMod p] t₀)))
      = c • (φ ((SSGRoute.res k K σ) • (e ⊗ₜ[ZMod p] t₀))) from
    Nat.cast_smul_eq_nsmul (ZMod p) c _]
  rw [hkey]



end Work.SSGRoute
