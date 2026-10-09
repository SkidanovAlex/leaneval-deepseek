import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local `H¹` with trivial coefficients

If the action of `Gal(K/k)` on a finite `𝔽_p`-module `M` is trivial (and likewise the action on
`𝔽_p = ZMod p`), then the locally constant `1`-coboundaries of the subgroup `H ≤ G_k = Ω ≃ₐ[k] Ω`
are exactly the functions vanishing on `H`, and the local cohomology `H1loc` is the tensor product
of `H1loc(𝔽_p)` with `M`:

  `H1loc p k Ω K M H ≃ₗ[𝔽_p] H1loc p k Ω K (ZMod p) H ⊗[𝔽_p] M`.

Consequently `H1loc p k Ω K M H` is finite dimensional with
`finrank H1loc(M) = finrank M * finrank H1loc(𝔽_p)`.
-/

namespace Work.SSGRoute.PT

open Work.SSGRoute
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

omit [NumberField k] [IsAlgClosure k Ω] in
/-- **Coboundaries for a trivial action.**  If `Gal(K/k)` acts trivially on `M`, then a cochain
`f : G_k → M` is a `1`-coboundary on `H` iff it vanishes on `H`. -/
theorem mem_coboundaries_iff (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (htriv : ∀ (σ : K ≃ₐ[k] K) (m : M), σ • m = m) (f : (Ω ≃ₐ[k] Ω) → M) :
    f ∈ coboundaries p k Ω K M H ↔ ∀ g ∈ H, f g = 0 := by
  constructor
  · rintro ⟨m, hm⟩ g hg
    rw [hm g hg, htriv (SSGRoute.res k K g) m, sub_self]
  · intro hf
    exact ⟨0, fun g hg => by rw [hf g hg, htriv (SSGRoute.res k K g) 0, sub_self]⟩

/-- The submodule by which one quotients the locally constant cocycles to obtain `H1loc`. -/
abbrev H1locB (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : Submodule (ZMod p) ↥(lcCocycles p k Ω K M H) :=
  Submodule.comap (lcCocycles p k Ω K M H).subtype (coboundaries p k Ω K M H)

omit [NumberField k] [IsAlgClosure k Ω] in
set_option maxHeartbeats 2000000 in
/-- **`H1loc` of a trivial module is `H1loc(𝔽_p) ⊗ M`.** -/
theorem h1loc_equiv_tensor
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (htrivp : ∀ (σ : K ≃ₐ[k] K) (x : ZMod p), σ • x = x)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (htriv : ∀ (σ : K ≃ₐ[k] K) (m : M), σ • m = m) :
    Nonempty (H1loc p k Ω K (ZMod p) H ⊗[ZMod p] M ≃ₗ[ZMod p] H1loc p k Ω K M H) := by
  classical
  have hfinM : Module.Finite (ZMod p) M := Module.Finite.of_finite
  let b := Module.finBasis (ZMod p) M
  -- multiplication of a `𝔽_p`-valued cocycle by an element of `M`
  let smulC : lcCocycles p k Ω K (ZMod p) H → M → lcCocycles p k Ω K M H := fun f m =>
    ⟨fun g => f.1 g • m, by
      refine ⟨?_, ?_⟩
      · intro g hg h hh
        have hc := f.2.1 g hg h hh
        show f.1 (g * h) • m = f.1 g • m + SSGRoute.res k K g • (f.1 h • m)
        rw [hc, add_smul, htrivp (SSGRoute.res k K g) (f.1 h),
          htriv (SSGRoute.res k K g) (f.1 h • m)]
      · obtain ⟨U, hUo, hU⟩ := f.2.2
        exact ⟨U, hUo, fun g hg u hu huH => by
          show f.1 (g * u) • m = f.1 g • m
          rw [hU g hg u hu huH]⟩⟩
  have smulC_apply : ∀ (f : lcCocycles p k Ω K (ZMod p) H) (m : M),
      (smulC f m : (Ω ≃ₐ[k] Ω) → M) = fun g => f.1 g • m := fun f m => rfl
  -- the `𝔽_p`-bilinear map `Z¹(𝔽_p) → M →ₗ Z¹(M)`
  let psi : lcCocycles p k Ω K (ZMod p) H →ₗ[ZMod p] M →ₗ[ZMod p] lcCocycles p k Ω K M H :=
    { toFun := fun f =>
        { toFun := fun m => smulC f m
          map_add' := fun m n => by
            apply Subtype.ext; funext g
            show f.1 g • (m + n) = f.1 g • m + f.1 g • n
            rw [smul_add]
          map_smul' := fun c m => by
            apply Subtype.ext; funext g
            show f.1 g • (c • m) = c • (f.1 g • m)
            rw [smul_comm] }
      map_add' := fun f f' => by
        apply LinearMap.ext; intro m
        apply Subtype.ext; funext g
        show (f.1 g + f'.1 g) • m = f.1 g • m + f'.1 g • m
        rw [add_smul]
      map_smul' := fun c f => by
        apply LinearMap.ext; intro m
        apply Subtype.ext; funext g
        show (c • f.1 g) • m = c • (f.1 g • m)
        rw [smul_assoc] }
  have psi_apply : ∀ (f : lcCocycles p k Ω K (ZMod p) H) (m : M),
      (psi f m : (Ω ≃ₐ[k] Ω) → M) = fun g => f.1 g • m := fun f m => rfl
  -- coordinate cocycles
  let cc : lcCocycles p k Ω K M H → Fin (Module.finrank (ZMod p) M) →
      lcCocycles p k Ω K (ZMod p) H := fun f i =>
    ⟨fun g => b.coord i (f.1 g), by
      refine ⟨?_, ?_⟩
      · intro g hg h hh
        have hc := f.2.1 g hg h hh
        show b.coord i (f.1 (g * h)) =
          b.coord i (f.1 g) + SSGRoute.res k K g • b.coord i (f.1 h)
        rw [hc, htriv (SSGRoute.res k K g) (f.1 h),
          htrivp (SSGRoute.res k K g) (b.coord i (f.1 h)), map_add]
      · obtain ⟨U, hUo, hU⟩ := f.2.2
        exact ⟨U, hUo, fun g hg u hu huH => by
          show b.coord i (f.1 (g * u)) = b.coord i (f.1 g)
          rw [hU g hg u hu huH]⟩⟩
  have cc_apply : ∀ (f : lcCocycles p k Ω K M H) (i : Fin (Module.finrank (ZMod p) M)),
      (cc f i : (Ω ≃ₐ[k] Ω) → ZMod p) = fun g => b.coord i (f.1 g) := fun f i => rfl
  -- `Θ₂ : Z¹(M) → V ⊗ M`
  let theta2 : lcCocycles p k Ω K M H →ₗ[ZMod p] (H1loc p k Ω K (ZMod p) H ⊗[ZMod p] M) :=
    { toFun := fun f =>
        ∑ i, (Submodule.mkQ (H1locB p k Ω K (ZMod p) H) (cc f i)) ⊗ₜ[ZMod p] b i
      map_add' := fun f f' => by
        have hcc : ∀ i, cc (f + f') i = cc f i + cc f' i := fun i => by
          apply Subtype.ext; funext g
          show b.coord i (f.1 g + f'.1 g) = b.coord i (f.1 g) + b.coord i (f'.1 g)
          rw [map_add]
        rw [Finset.sum_congr rfl (fun i _ => by
          rw [hcc i, map_add, TensorProduct.add_tmul])]
        rw [Finset.sum_add_distrib]
      map_smul' := fun c f => by
        have hcc : ∀ i, cc (c • f) i = c • cc f i := fun i => by
          apply Subtype.ext; funext g
          show b.coord i (c • f.1 g) = c • b.coord i (f.1 g)
          rw [map_smul]
        simp only [hcc, map_smul, TensorProduct.smul_tmul', Finset.smul_sum,
          RingHom.id_apply] }
  have theta2_apply : ∀ f : lcCocycles p k Ω K M H,
      (theta2 f : H1loc p k Ω K (ZMod p) H ⊗[ZMod p] M)
        = ∑ i, (Submodule.mkQ (H1locB p k Ω K (ZMod p) H) (cc f i)) ⊗ₜ[ZMod p] b i :=
    fun f => rfl
  have thetaKill : H1locB p k Ω K M H ≤ theta2.ker := by
    intro f hf
    rw [LinearMap.mem_ker]
    rw [theta2_apply]
    rw [Submodule.mem_comap] at hf
    have hf0 : ∀ g ∈ H, f.1 g = 0 :=
      (mem_coboundaries_iff p k Ω K M H htriv f.1).mp hf
    have hzero : ∀ i, Submodule.mkQ (H1locB p k Ω K (ZMod p) H) (cc f i) = 0 := fun i => by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        mem_coboundaries_iff p k Ω K (ZMod p) H htrivp]
      intro g hg
      show b.coord i (f.1 g) = 0
      rw [hf0 g hg, map_zero]
    rw [Finset.sum_eq_zero (fun i _ => by rw [hzero i, TensorProduct.zero_tmul])]
  let theta : H1loc p k Ω K M H →ₗ[ZMod p] (H1loc p k Ω K (ZMod p) H ⊗[ZMod p] M) :=
    Submodule.liftQ (H1locB p k Ω K M H) theta2 thetaKill
  have theta_apply : ∀ f : lcCocycles p k Ω K M H,
      (theta (Submodule.mkQ (H1locB p k Ω K M H) f) : H1loc p k Ω K (ZMod p) H ⊗[ZMod p] M)
        = ∑ i, (Submodule.mkQ (H1locB p k Ω K (ZMod p) H) (cc f i)) ⊗ₜ[ZMod p] b i :=
    fun f => rfl
  -- `Φ₂ : Z¹(𝔽_p) → M →ₗ H1loc(M)`
  let phi2 : lcCocycles p k Ω K (ZMod p) H →ₗ[ZMod p] M →ₗ[ZMod p] H1loc p k Ω K M H :=
    { toFun := fun f => (Submodule.mkQ (H1locB p k Ω K M H)).comp (psi f)
      map_add' := fun f f' => by
        apply LinearMap.ext; intro m
        simp only [LinearMap.comp_apply, LinearMap.add_apply, psi.map_add, map_add]
      map_smul' := fun c f => by
        apply LinearMap.ext; intro m
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, psi.map_smul, map_smul,
          RingHom.id_apply] }
  have phi2_apply : ∀ (f : lcCocycles p k Ω K (ZMod p) H) (m : M),
      phi2 f m = Submodule.mkQ (H1locB p k Ω K M H) (psi f m) := fun f m => rfl
  have phiKill : H1locB p k Ω K (ZMod p) H ≤ phi2.ker := by
    intro f hf
    rw [LinearMap.mem_ker]
    apply LinearMap.ext; intro m
    rw [phi2_apply, LinearMap.zero_apply]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      mem_coboundaries_iff p k Ω K M H htriv]
    intro g hg
    have hf0 : f.1 g = 0 :=
      (mem_coboundaries_iff p k Ω K (ZMod p) H htrivp f.1).mp (Submodule.mem_comap.mp hf) g hg
    show f.1 g • m = 0
    rw [hf0, zero_smul]
  let phi3 : H1loc p k Ω K (ZMod p) H →ₗ[ZMod p] M →ₗ[ZMod p] H1loc p k Ω K M H :=
    Submodule.liftQ (H1locB p k Ω K (ZMod p) H) phi2 phiKill
  let Phi : (H1loc p k Ω K (ZMod p) H ⊗[ZMod p] M) →ₗ[ZMod p] H1loc p k Ω K M H :=
    TensorProduct.lift phi3
  have Phi_apply : ∀ (y : H1loc p k Ω K (ZMod p) H) (m : M),
      Phi (y ⊗ₜ[ZMod p] m) = phi3 y m := fun y m => rfl
  have phi3_apply : ∀ (f : lcCocycles p k Ω K (ZMod p) H) (m : M),
      phi3 (Submodule.mkQ (H1locB p k Ω K (ZMod p) H) f) m
        = Submodule.mkQ (H1locB p k Ω K M H) (psi f m) := fun f m => rfl
  -- `Φ ∘ Θ = id`
  have hPhiΘ : ∀ f : lcCocycles p k Ω K M H,
      Phi (theta (Submodule.mkQ (H1locB p k Ω K M H) f))
        = Submodule.mkQ (H1locB p k Ω K M H) f := by
    intro f
    rw [theta_apply, map_sum]
    have hterm : ∀ i, Phi ((Submodule.mkQ (H1locB p k Ω K (ZMod p) H) (cc f i))
        ⊗ₜ[ZMod p] b i) = Submodule.mkQ (H1locB p k Ω K M H) (psi (cc f i) (b i)) :=
      fun i => rfl
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← map_sum]
    congr 1
    apply Subtype.ext; funext g
    simp only [Submodule.coe_sum, Finset.sum_apply, psi_apply, cc_apply,
      Module.Basis.coord_apply, Module.Basis.sum_repr]
  -- `Θ ∘ Φ = id` on pure tensors
  have hThetaPhi : ∀ (y : H1loc p k Ω K (ZMod p) H) (m : M),
      theta (Phi (y ⊗ₜ[ZMod p] m)) = y ⊗ₜ[ZMod p] m := by
    intro y m
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (H1locB p k Ω K (ZMod p) H) y
    rw [Phi_apply, phi3_apply, theta_apply]
    have hcc : ∀ i, cc (psi f m) i = (b.coord i m) • f := by
      intro i
      apply Subtype.ext; funext g
      show b.coord i (f.1 g • m) = (b.coord i m) • (f.1 g)
      rw [map_smul]
      exact mul_comm _ _
    rw [Finset.sum_congr rfl (fun i _ => by rw [hcc i])]
    rw [Finset.sum_congr rfl (fun i _ => by rw [map_smul])]
    rw [Finset.sum_congr rfl (fun i _ =>
      TensorProduct.smul_tmul (b.coord i m) (Submodule.mkQ (H1locB p k Ω K (ZMod p) H) f) (b i))]
    rw [← TensorProduct.tmul_sum]
    simp only [Module.Basis.coord_apply, Module.Basis.sum_repr]
  have hleft : ∀ x : H1loc p k Ω K (ZMod p) H ⊗[ZMod p] M, theta (Phi x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul y m => exact hThetaPhi y m
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hright : ∀ y : H1loc p k Ω K M H, Phi (theta y) = y := by
    intro y
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (H1locB p k Ω K M H) y
    exact hPhiΘ f
  exact ⟨{ toFun := Phi, invFun := theta, map_add' := Phi.map_add, map_smul' := Phi.map_smul, left_inv := hleft, right_inv := hright }⟩

/-- **Finiteness and the dimension of the local `H¹` of a trivial module**: if `Gal(K/k)` acts
trivially on `M` then `H1loc p k Ω K M H` is a finite `𝔽_p`-vector space of dimension
`finrank M · finrank H1loc(𝔽_p)`. -/
theorem h1loc_finrank_trivialAction
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (htrivp : ∀ (σ : K ≃ₐ[k] K) (x : ZMod p), σ • x = x)
    [Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p) H)]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (htriv : ∀ (σ : K ≃ₐ[k] K) (m : M), σ • m = m) :
    Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M H) ∧
      Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M H) =
        Module.finrank (ZMod p) M *
          Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p) H) := by
  classical
  obtain ⟨e⟩ := h1loc_equiv_tensor p k Ω K H htrivp M htriv
  have hfinM : Module.Finite (ZMod p) M := Module.Finite.of_finite
  have hten : Module.Finite (ZMod p)
      (Work.SSGRoute.H1loc p k Ω K (ZMod p) H ⊗[ZMod p] M) :=
    Module.Finite.tensorProduct (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p) H) M
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_tensorProduct, mul_comm]

end

end Work.SSGRoute.PT
