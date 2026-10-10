import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.PT.e1a_chain
import Submission.Work.SSGRoute.dualPairingEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a, a *canonical* coefficient isomorphism `E ≅ Hom_ℤ(E',Ωˣ)`, natural in `E`

The banked `Work.SSGRoute.dualPairingEquiv_homCoind` is a `Classical.choose`-based `∃`-statement:
it realises the coefficient identification for one `E` at a time, hence it carries no naturality.
The target theorem `Work.SSGRoute.PT.e1a_ext_sha2_bridge` needs the naturality square
(`β E₂ (Sha2Map f b) = (mk₀ F).comp (β E₁ b) _`), so the coefficient identification has to be a
*single* construction, uniform in `E`.

This file provides it.  The construction is the explicit one of
`Submission/Work/SSGRoute/dualPairingEquiv.lean`: fix once and for all

* `ζu = (hζ.isUnit _).unit ∈ Ωˣ` (`e1aZetaUnit`),
* an `𝔽_p`-linear isomorphism `u : T ≃ₗ 𝔽_p` (`e1aTEquiv`, from `finrank T = 1`) and
  `t₀ = u.symm 1 ∈ T` (`e1aTGen`),

and put `Ψ_E(e)(φ) = ζu ^ (φ (e ⊗ t₀))` (`e1aCoeffEquiv`).  Nothing in this formula depends on `E`
except `e` and the tensor factor, so `Ψ` is natural: for the transpose `F : E₂' → E₁'` of
`f : E₁ → E₂` (i.e. `hF`), both sides of

  `Ψ_{E₂} (f e) φ = (Ψ_{E₁} e) (F.hom φ)`

are `ζu ^ (φ ((f e) ⊗ t₀))` by `hF` at the pure tensor `e ⊗ t₀`.  `e1a_coeff_iso_natural` is that
statement together with the equivariance (proved exactly as in `dualPairingEquiv`).
-/

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute.PT

noncomputable section

/-- `ζ` as a unit of `Ωˣ`. -/
def e1aZetaUnit (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ p) : Ωˣ :=
  (hζ.isUnit (Fact.out : p.Prime).ne_zero).unit

theorem e1aZetaUnit_val (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ p) : ((e1aZetaUnit p Ω ζ hζ : Ωˣ) : Ω) = ζ :=
  IsUnit.unit_spec _

theorem e1aZetaUnit_isPrimitiveRoot (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ p) : IsPrimitiveRoot (e1aZetaUnit p Ω ζ hζ) p :=
  IsPrimitiveRoot.coe_units_iff.mp (by rw [e1aZetaUnit_val]; exact hζ)

/-- A fixed `𝔽_p`-linear isomorphism `T ≃ 𝔽_p` (from `finrank T = 1`). -/
def e1aTEquiv (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    (hT : Module.finrank (ZMod p) T = 1) : T ≃ₗ[ZMod p] ZMod p := by
  haveI : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT]; norm_num)
  exact LinearEquiv.ofFinrankEq (R := ZMod p) T (ZMod p) (by rw [hT, Module.finrank_self])

/-- The fixed generator `t₀ ∈ T`. -/
def e1aTGen (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    (hT : Module.finrank (ZMod p) T = 1) : T :=
  (e1aTEquiv p T hT).symm 1

/-- The canonical `𝔽_p`-linear isomorphism `E ≅ E ⊗ T` sending `e` to `e ⊗ t₀`. -/
def e1aIsoE (p : ℕ) [Fact p.Prime] (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [AddCommGroup T]
    [Module (ZMod p) T] (hT : Module.finrank (ZMod p) T = 1) :
    E ≃ₗ[ZMod p] TensorProduct (ZMod p) E T := by
  haveI : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT]; norm_num)
  exact (TensorProduct.rid (ZMod p) E).symm.trans
    ((TensorProduct.congr (LinearEquiv.refl (ZMod p) E) (e1aTEquiv p T hT)).symm)

theorem e1aIsoE_apply (p : ℕ) [Fact p.Prime] (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [AddCommGroup T]
    [Module (ZMod p) T] (hT : Module.finrank (ZMod p) T = 1) (e : E) :
    e1aIsoE p E T hT e = e ⊗ₜ[ZMod p] e1aTGen p T hT := by
  rw [show e1aIsoE p E T hT e = (TensorProduct.congr (LinearEquiv.refl (ZMod p) E)
      (e1aTEquiv p T hT)).symm ((TensorProduct.rid (ZMod p) E).symm e) from rfl]
  rw [TensorProduct.rid_symm_apply, TensorProduct.congr_symm, TensorProduct.congr_tmul]
  simp [e1aTGen]

/-- **The canonical coefficient isomorphism** `E ≃+ Hom_ℤ(E',Ωˣ)`, `e ↦ (φ ↦ ζu^(φ (e ⊗ t₀)))`. -/
noncomputable def e1aCoeffEquiv (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    E ≃+ Work.SSGRoute.homCoind k Ω K
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  haveI : Module.Finite (ZMod p) (TensorProduct (ZMod p) E T) :=
    Module.Finite.tensorProduct (ZMod p) E T
  haveI : Module.IsReflexive (ZMod p) (TensorProduct (ZMod p) E T) := inferInstance
  exact ((e1aIsoE p E T hT.1).toAddEquiv.trans
      ((Module.evalEquiv (ZMod p) (TensorProduct (ZMod p) E T)).toAddEquiv)).trans
    (Work.SSGRoute.dualEquiv_zpow p (e1aZetaUnit p Ω ζ hζ) (e1aZetaUnit_isPrimitiveRoot p Ω ζ hζ)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))

/-- The computation rule for `e1aCoeffEquiv`. -/
@[simp] theorem e1aCoeffEquiv_apply (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (e : E) (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :
    e1aCoeffEquiv p k Ω K ζ hζ hζK T hT E e φ
      = Work.SSGRoute.zetaPowHom (e1aZetaUnit p Ω ζ hζ) (e1aZetaUnit_isPrimitiveRoot p Ω ζ hζ)
          (φ (e ⊗ₜ[ZMod p] e1aTGen p T hT.1)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  haveI : Module.Finite (ZMod p) (TensorProduct (ZMod p) E T) :=
    Module.Finite.tensorProduct (ZMod p) E T
  haveI : Module.IsReflexive (ZMod p) (TensorProduct (ZMod p) E T) := inferInstance
  show Work.SSGRoute.dualEquiv_zpow p _ _
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
      ((Module.evalEquiv (ZMod p) (TensorProduct (ZMod p) E T))
        (e1aIsoE p E T hT.1 e)) φ = _
  rw [Work.SSGRoute.dualEquiv_zpow_apply, Module.evalEquiv_apply, Module.Dual.eval_apply,
    e1aIsoE_apply]

/-- **The naturality of the coefficient identification**: `e1a_coeff_iso_natural`. -/
theorem e1a_coeff_iso_natural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    ∃ Ψ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        E ≃+ Work.SSGRoute.homCoind k Ω K
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))),
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (σ : Ω ≃ₐ[k] Ω) (e : E), Ψ E ((SSGRoute.res k K σ) • e) = σ • Ψ E e) ∧
      (∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
        (F : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) ⟶
          SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))
        (hF : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
          (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T) from F.hom φ)
            (TensorProduct.tmul (ZMod p) e t)
          = φ (TensorProduct.tmul (ZMod p) (f e) t))
        (e : E₁), Ψ E₂ (f e) = (Ψ E₁ e).comp F.hom.toAddMonoidHom) := by
  classical
  haveI hNp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hTf : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  refine ⟨fun E _ _ _ _ _ => e1aCoeffEquiv p k Ω K ζ hζ hζK T hT E, ?_, ?_⟩
  · -- equivariance: proved in the conjugated form (as in `dualPairingEquiv`)
    intro E _ _ _ _ _
    have hconj : ∀ (σ : Ω ≃ₐ[k] Ω) (e : E)
        (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        e1aCoeffEquiv p k Ω K ζ hζ hζK T hT E ((SSGRoute.res k K σ) • e) φ
          = σ • (e1aCoeffEquiv p k Ω K ζ hζ hζK T hT E e
              (((SSGRoute.res k K) σ)⁻¹ • φ)) := by
      intro σ e φ
      rw [e1aCoeffEquiv_apply, e1aCoeffEquiv_apply]
      obtain ⟨c, hc⟩ : ∃ c : ℕ, σ • ζ = ζ ^ c := by
        have hpow : (σ • ζ) ^ p = 1 := by
          rw [show σ • ζ = σ ζ from rfl, ← map_pow, hζ.pow_eq_one, map_one]
        obtain ⟨c, -, hc⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hζ hpow
        exact ⟨c, hc.symm⟩
      have hσζu : σ • e1aZetaUnit p Ω ζ hζ = (e1aZetaUnit p Ω ζ hζ) ^ c := by
        apply Units.ext
        rw [show (↑(σ • e1aZetaUnit p Ω ζ hζ) : Ω) = σ • (↑(e1aZetaUnit p Ω ζ hζ) : Ω) from rfl,
          e1aZetaUnit_val, hc, Units.val_pow_eq_pow_val, e1aZetaUnit_val]
      have hkey : ∀ x : ZMod p,
          σ • Work.SSGRoute.zetaPowHom (e1aZetaUnit p Ω ζ hζ)
              (e1aZetaUnit_isPrimitiveRoot p Ω ζ hζ) x
            = Work.SSGRoute.zetaPowHom (e1aZetaUnit p Ω ζ hζ)
                (e1aZetaUnit_isPrimitiveRoot p Ω ζ hζ) (c • x) :=
        fun x => Work.SSGRoute.zetaPowHom_smul (e1aZetaUnit p Ω ζ hζ)
          (e1aZetaUnit_isPrimitiveRoot p Ω ζ hζ) σ hσζu x
      have hTt : (c : ZMod p) • ((SSGRoute.res k K σ) • e1aTGen p T hT.1) = e1aTGen p T hT.1 := by
        rw [Nat.cast_smul_eq_nsmul (ZMod p) c ((SSGRoute.res k K σ) • e1aTGen p T hT.1)]
        exact hT.2 σ c hc (e1aTGen p T hT.1)
      have hz : (c : ZMod p) • ((SSGRoute.res k K σ) • (e ⊗ₜ[ZMod p] e1aTGen p T hT.1))
          = ((SSGRoute.res k K σ) • e) ⊗ₜ[ZMod p] e1aTGen p T hT.1 := by
        rw [Work.Shrinking.diagTensor_smul_tmul]
        rw [← TensorProduct.tmul_smul (c : ZMod p) ((SSGRoute.res k K σ) • e)
          ((SSGRoute.res k K σ) • e1aTGen p T hT.1)]
        rw [hTt]
      rw [show (((SSGRoute.res k K) σ)⁻¹ • φ) (e ⊗ₜ[ZMod p] e1aTGen p T hT.1)
          = φ ((SSGRoute.res k K σ) • (e ⊗ₜ[ZMod p] e1aTGen p T hT.1)) from by
        rw [Work.SSGRoute.DualMod.dualSMul_apply]; simp]
      rw [← hz, map_smul]
      rw [show (c : ZMod p) • (φ ((SSGRoute.res k K σ) • (e ⊗ₜ[ZMod p] e1aTGen p T hT.1)))
          = c • (φ ((SSGRoute.res k K σ) • (e ⊗ₜ[ZMod p] e1aTGen p T hT.1))) from
        Nat.cast_smul_eq_nsmul (ZMod p) c _]
      rw [hkey]
    intro σ e
    apply AddMonoidHom.ext
    intro φ
    set φ' : TensorProduct (ZMod p) E T →ₗ[ZMod p] ZMod p := φ with hφ'
    dsimp only
    rw [Work.SSGRoute.homCoind.smul_apply]
    exact hconj σ e φ'
  · -- naturality
    intro E₁ _ _ _ _ _ E₂ _ _ _ _ _ f hf F hF e
    apply AddMonoidHom.ext
    intro φ
    dsimp only
    rw [e1aCoeffEquiv_apply]
    simp only [AddMonoidHom.comp_apply]
    rw [e1aCoeffEquiv_apply]
    congr 1
    exact (hF φ e (e1aTGen p T hT.1)).symm

end

end Work.SSGRoute.PT
