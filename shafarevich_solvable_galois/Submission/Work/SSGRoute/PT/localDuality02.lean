import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Module.StablyFree.Basic
import Submission.Work.SSGRoute.PT.localTatePairing_deg02
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The double Tate twist for a rank-one coefficient module

`TateDoubleTwist` machinery for the `PT/localDuality02` node: for a one-dimensional `𝔽_p[G]`-module
`T` and a finite `𝔽_p[G]`-module `M`, the double Tate twist

  `M ⟶ DualMod p (DualMod p (M ⊗ T) ⊗ T)`

(= `(M^∨(1))^∨(1)`) given by the evaluation `m ↦ (f ↦ (t ↦ f (m ⊗ t)))` is an equivariant
`𝔽_p`-linear isomorphism (`tateTwistEquiv`, equivariance `phi_smul`).  This is the pure-module-
theoretic input that identifies the second conjunct of `localDuality02` with the first.
-/

open scoped TensorProduct Pointwise
open Classical

namespace Work.SSGRoute.PT

noncomputable section

open scoped TensorProduct
open Classical


variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
  {M T : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
  [SMulCommClass G (ZMod p) M]
  [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T] [SMulCommClass G (ZMod p) T]

noncomputable def thetaFun (m : M) : DualMod p (M ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p T where
  toFun f :=
    { toFun := fun t => f (m ⊗ₜ[ZMod p] t)
      map_add' := fun t₁ t₂ => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun c t => by rw [TensorProduct.tmul_smul, map_smul]; rfl }
  map_add' f g := by ext t; rfl
  map_smul' c f := by ext t; rfl

noncomputable def theta : M →ₗ[ZMod p] (DualMod p (M ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p T) where
  toFun := thetaFun (p := p) (T := T)
  map_add' m n := by ext f t; simp [thetaFun, TensorProduct.add_tmul]
  map_smul' c m := by
    ext f t
    show f ((c • m) ⊗ₜ[ZMod p] t) = c • f (m ⊗ₜ[ZMod p] t)
    rw [show (c • m) ⊗ₜ[ZMod p] t = c • (m ⊗ₜ[ZMod p] t) from rfl, map_smul]

noncomputable def conjAct (g : G) (φ : DualMod p (M ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p T) :
    DualMod p (M ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p T where
  toFun f := g • φ (g⁻¹ • f)
  map_add' f f' := by rw [smul_add, map_add, smul_add]
  map_smul' c f := by rw [smul_comm g⁻¹ c f, map_smul, smul_comm]; rfl

@[simp] lemma conjAct_apply (g : G) (φ : DualMod p (M ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p T)
    (f : DualMod p (M ⊗[ZMod p] T)) (t : T) :
    conjAct g φ f t = (φ (g⁻¹ • f)) (g⁻¹ • t) := by
  simp [conjAct, DualMod.dualSMul_apply]

theorem thetaFun_smul (g : G) (m : M) (f : DualMod p (M ⊗[ZMod p] T)) (t : T) :
    thetaFun (g • m) f t = thetaFun m (g⁻¹ • f) (g⁻¹ • t) := by
  simp only [thetaFun, LinearMap.coe_mk, AddHom.coe_mk, DualMod.dualSMul_apply, inv_inv]
  simp

theorem theta_smul (g : G) (m : M) :
    (theta (p:=p) (M:=M) (T:=T)) (g • m)
      = conjAct (p:=p) (M:=M) (T:=T) g ((theta (p:=p) (M:=M) (T:=T)) m) := by
  ext f t; rw [conjAct_apply]; exact thetaFun_smul g m f t

theorem theta_injective (hT : Module.finrank (ZMod p) T = 1) : Function.Injective (theta (p:=p) (M:=M) (T:=T)) := by
  intro m n hmn
  have h0 : theta (p:=p) (M:=M) (T:=T) (m - n) = 0 := by rw [map_sub, hmn, sub_self]
  have h1 : ∀ t : T, (m - n) ⊗ₜ[ZMod p] t = 0 := by
    intro t
    refine (Module.forall_dual_apply_eq_zero_iff (ZMod p) (V := M ⊗[ZMod p] T)
      ((m - n) ⊗ₜ[ZMod p] t)).mp ?_
    intro f
    have hft : thetaFun (p:=p) (T:=T) (m - n) f t = 0 := by
      have := congrArg (fun φ => φ f t) h0
      simpa [theta] using this
    simpa [thetaFun] using hft
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one (R := ZMod p) hT
  have h2 : (m - n) ⊗ₜ[ZMod p] (e 1) = 0 := h1 (e 1)
  have h3 := congrArg (TensorProduct.congr (LinearEquiv.refl (ZMod p) M) e.symm) h2
  simp only [map_zero, TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.symm_apply_apply] at h3
  have h4 := congrArg (TensorProduct.rid (ZMod p) M) h3
  simpa [sub_eq_zero] using h4

/-- Currying `DualMod p (M' ⊗ T) ≃ₗ (M' →ₗ DualMod p T)`. -/
noncomputable def curry :
    DualMod p (DualMod p (M ⊗[ZMod p] T) ⊗[ZMod p] T) ≃ₗ[ZMod p]
      (DualMod p (M ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p T) :=
  (TensorProduct.lift.equiv (RingHom.id (ZMod p)) (DualMod p (M ⊗[ZMod p] T)) T (ZMod p)).symm

@[simp] lemma curry_apply (ψ : DualMod p (DualMod p (M ⊗[ZMod p] T) ⊗[ZMod p] T))
    (m' : DualMod p (M ⊗[ZMod p] T)) (t : T) :
    curry ψ m' t = ψ (m' ⊗ₜ[ZMod p] t) := rfl

theorem curry_smul (g : G) (ψ : DualMod p (DualMod p (M ⊗[ZMod p] T) ⊗[ZMod p] T)) :
    curry (g • ψ) = conjAct g (curry ψ) := by
  ext m' t
  rw [conjAct_apply, curry_apply, curry_apply, DualMod.dualSMul_apply]
  congr 1

/-- The canonical linear map `M → DualMod p (DualMod p (M ⊗ T) ⊗ T)`. -/
noncomputable def phi : M →ₗ[ZMod p] DualMod p (DualMod p (M ⊗[ZMod p] T) ⊗[ZMod p] T) :=
  curry.symm.toLinearMap.comp theta

theorem phi_apply (m : M) (m' : DualMod p (M ⊗[ZMod p] T)) (t : T) :
    phi m (m' ⊗ₜ[ZMod p] t) = m' (m ⊗ₜ[ZMod p] t) := by
  unfold phi
  rw [LinearMap.comp_apply]
  change curry (curry.symm (theta m)) m' t = m' (m ⊗ₜ[ZMod p] t)
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem phi_smul (g : G) (m : M) :
    phi (p:=p) (M:=M) (T:=T) (g • m) = g • phi (p:=p) (M:=M) (T:=T) m := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul m' t =>
    rw [phi_apply, DualMod.dualSMul_apply,
      show g⁻¹ • (m' ⊗ₜ[ZMod p] t) = (g⁻¹ • m') ⊗ₜ[ZMod p] (g⁻¹ • t) from by simp,
      phi_apply, DualMod.dualSMul_apply, inv_inv]
    congr 1
    simp




theorem phi_injective {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {M T : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T] [SMulCommClass G (ZMod p) T]
    (hT : Module.finrank (ZMod p) T = 1) :
    Function.Injective (phi (p:=p) (M:=M) (T:=T)) := by
  intro a b h
  have h' : theta (p:=p) (M:=M) (T:=T) a = theta (p:=p) (M:=M) (T:=T) b :=
    curry.symm.injective (by simpa [phi] using h)
  exact theta_injective hT h'



theorem phi_surjective {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {M T : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T] [SMulCommClass G (ZMod p) T]
    [Finite M] (hT : Module.finrank (ZMod p) T = 1) :
    Function.Surjective (phi (p:=p) (M:=M) (T:=T)) := by
  haveI hTfin : Finite T := finite_of_finrank_eq_one (p := p) T hT
  haveI hMT : Finite (M ⊗[ZMod p] T) := finite_tensor (p := p) M T
  haveI hD : Finite (DualMod p (M ⊗[ZMod p] T)) := finite_dualMod (p := p) (M ⊗[ZMod p] T)
  haveI hDT : Finite (DualMod p (M ⊗[ZMod p] T) ⊗[ZMod p] T) :=
    finite_tensor (p := p) (DualMod p (M ⊗[ZMod p] T)) T
  haveI hN : Finite (DualMod p (DualMod p (M ⊗[ZMod p] T) ⊗[ZMod p] T)) :=
    finite_dualMod (p := p) (DualMod p (M ⊗[ZMod p] T) ⊗[ZMod p] T)
  haveI : Module.Finite (ZMod p) M := Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) T := Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) (DualMod p (M ⊗[ZMod p] T)) := Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) (DualMod p (M ⊗[ZMod p] T) ⊗[ZMod p] T) :=
    Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) (DualMod p (DualMod p (M ⊗[ZMod p] T) ⊗[ZMod p] T)) :=
    Module.Finite.of_finite
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have hker : LinearMap.ker (phi (p:=p) (M:=M) (T:=T)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (phi_injective (G := G) hT)
  have h1 : Module.finrank (ZMod p) ↥(LinearMap.range (phi (p:=p) (M:=M) (T:=T)))
      = Module.finrank (ZMod p) M := by
    have := LinearMap.finrank_range_add_finrank_ker (phi (p:=p) (M:=M) (T:=T))
    rw [hker, finrank_bot, add_zero] at this
    exact this
  rw [h1, finrank_dualMod, Module.finrank_tensorProduct, finrank_dualMod,
    Module.finrank_tensorProduct, hT, mul_one, mul_one]




end

end Work.SSGRoute.PT

namespace Work.SSGRoute.PT

open scoped TensorProduct Pointwise
open Classical
open Work.SSGRoute

noncomputable section

/-- An equivariant `𝔽_p`-linear isomorphism of coefficient modules induces an isomorphism of the
fixed-point submodules `H0loc`. -/
theorem finrank_H0loc_eq_of_equiv {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    {M M' : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [AddCommGroup M'] [Module (ZMod p) M'] [DistribMulAction (K ≃ₐ[k] K) M']
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M']
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (e : M ≃ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m) :
    Module.finrank (ZMod p) (H0loc p k Ω K M H) =
      Module.finrank (ZMod p) (H0loc p k Ω K M' H) := by
  have hmem : ∀ (m : M), m ∈ H0loc p k Ω K M H ↔ e m ∈ H0loc p k Ω K M' H := by
    intro m
    constructor
    · intro hm g hg
      rw [← he (SSGRoute.res k K g) m, hm g hg]
    · intro hm g hg
      have h1 : e (SSGRoute.res k K g • m) = e m := by rw [he, hm g hg]
      exact e.injective h1
  let F : ↥(H0loc p k Ω K M H) →ₗ[ZMod p] ↥(H0loc p k Ω K M' H) :=
    { toFun := fun m => ⟨e m, (hmem m).mp m.2⟩
      map_add' := fun a b => by ext; simp
      map_smul' := fun c a => by ext; simp }
  have hF : Function.Bijective F := by
    constructor
    · intro a b hab
      have h1 : e a = e b := by simpa [F] using congrArg Subtype.val hab
      exact Subtype.ext (e.injective h1)
    · intro y
      refine ⟨⟨e.symm y, (hmem _).mpr ?_⟩, ?_⟩
      · simpa using y.2
      · ext; simp [F]
  exact (LinearEquiv.ofBijective F hF).finrank_eq

end

end Work.SSGRoute.PT

namespace Work.SSGRoute.PT

open scoped TensorProduct Pointwise
open Classical
open Work.SSGRoute

noncomputable section

/-- The double Tate twist `M ≃ₗ DualMod p (DualMod p (M ⊗ T) ⊗ T)`, as an equivariant
isomorphism (with the group `K ≃ₐ[k] K` made explicit so that the ambient instances determine it). -/
theorem tateTwist_equiv {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    {M T : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] (hT : Module.finrank (ZMod p) T = 1) :
    ∃ e : M ≃ₗ[ZMod p] DualMod p (DualMod p (M ⊗[ZMod p] T) ⊗[ZMod p] T),
      ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m :=
  ⟨LinearEquiv.ofBijective (phi (p := p) (M := M) (T := T))
    ⟨phi_injective (p := p) (G := K ≃ₐ[k] K) (M := M) (T := T) hT,
     phi_surjective (p := p) (G := K ≃ₐ[k] K) (M := M) (T := T) hT⟩,
   fun g m => phi_smul (p := p) (G := K ≃ₐ[k] K) g m⟩

/-- **The reduction of the target to its arithmetic core.**  If Tate duality holds in degree `0`/`2`
(`dim H²(D_A, M) = dim H⁰(D_A, M^∨(1))` for every finite `M` — the first conjunct of the target),
then the full target follows: the second conjunct is the first applied to `M^∨(1)`, using that the
double Tate twist is an equivariant involution (proved above as `phi_smul`/`phi_injective`/
`phi_surjective`). -/
theorem localDuality02_of_core
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hcore : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
      [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Module.finrank (ZMod p) (H2loc p k Ω K M (SSGRoute.decomp k A)) =
        Module.finrank (ZMod p) (H0loc p k Ω K
          (DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A))) :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
        [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        (Module.finrank (ZMod p) (H2loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (H0loc p k Ω K
            (DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A))) ∧
        (Module.finrank (ZMod p) (H2loc p k Ω K
            (DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (H0loc p k Ω K M (SSGRoute.decomp k A))) := by
  intro A hA M _ _ _ _
  refine ⟨hcore A hA M, ?_⟩
  haveI hTfin : Finite T := finite_of_finrank_eq_one (p := p) T hT.1
  haveI hMT : Finite (M ⊗[ZMod p] T) := finite_tensor (p := p) M T
  haveI hD : Finite (DualMod p (M ⊗[ZMod p] T)) := finite_dualMod (p := p) (M ⊗[ZMod p] T)
  rw [hcore A hA (DualMod p (M ⊗[ZMod p] T))]
  obtain ⟨e, he⟩ := tateTwist_equiv (p := p) (k := k) (Ω := Ω) K (M := M) (T := T) hT.1
  exact (finrank_H0loc_eq_of_equiv (p := p) (k := k) (Ω := Ω) K (SSGRoute.decomp k A) e he).symm

end

end Work.SSGRoute.PT

namespace Work.SSGRoute.PT

open scoped TensorProduct Pointwise
open Classical

/-- **Tate duality in degrees `0` and `2` for a decomposition group** (Milne, *Arithmetic Duality
Theorems*, Cor. I.2.3 at `r = 0`): for every finite place `A` and every finite
`𝔽_p[Gal(K/k)]`-module `M`, `dim H²(D_A, M) = dim H⁰(D_A, M^∨(1))` and
`dim H²(D_A, M^∨(1)) = dim H⁰(D_A, M)`, where `M^∨(1) = DualMod p (M ⊗ T)`. -/
theorem localDuality02
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
        [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        (Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A))) ∧
        (Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A))) :=
  localDuality02_of_core p k Ω K ζ hζ hζK T hT
    (fun A hA M => localTatePairing_deg02 p k Ω K ζ hζ hζK T hT A hA M)

end Work.SSGRoute.PT


