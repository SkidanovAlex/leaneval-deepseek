import Mathlib
import Submission.Work.SSGRoute.ShapiroNaturalDefs
import Submission.Work.GroupCohomology.All
import Submission.Work.SSGRoute.shapiro_framed_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the Shapiro packaging of a family of `2`-cocycles

This file proves `Work.SSGRoute.shapiro_packaging_natural`: for a finite family of subgroups
`H a ≤ G` and `2`-cocycles `κ a` on `H a` with values in an `𝔽_p[G]`-module `M`, the *fixed*
`𝔽_p[G]`-module `shapiroT p G ι H = ∏_a 𝔽_p[G ⧸ H a]` carries a packaged family of `2`-cocycles
`C a` on `G` together with `H a`-equivariant coefficient maps `ev a`, in such a way that the
whole construction is natural in the coefficient module `M`.

The per-coordinate input is `Work.SSGRoute.shapiro_framed_natural` (Shapiro induction for an
abstract framed `G`-set `X`, with `𝔽_p[X]` the induced module); the assembling step performed
here transports the `a`-th coordinate datum along the coordinate insertion
`shapiroSingle a : 𝔽_p[G ⧸ H a] → shapiroT` and reads it back through the coordinate projection
`shapiroProj a`, using the equivariance of `LinearMap.lTensor` for the diagonal `G`-action on
tensor products.
-/

namespace Work.SSGRoute

open scoped TensorProduct

/-! ## The elementary equivariance toolkit -/

/-- A `G`-equivariant `𝔽_p`-linear map between two `𝔽_p[G]`-modules carries `2`-cocycles to
`2`-cocycles. -/
theorem shapiroPkg_mem_Z2_comp_of_equivariant
    {p : ℕ} {G : Type*} [Group G]
    {A B : Type*} [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
    (ψ : A →ₗ[ZMod p] B) (hψ : ∀ (g : G) (a : A), ψ (g • a) = g • ψ a)
    (c : G × G → A) (hc : c ∈ Work.GroupCohomology.Z2 G A) :
    (fun q => ψ (c q)) ∈ Work.GroupCohomology.Z2 G B := by
  rw [Work.GroupCohomology.mem_Z2_iff] at hc ⊢
  intro g h k
  have h1 : c (g * h, k) + c (g, h) = g • c (h, k) + c (g, h * k) := hc g h k
  calc ψ (c (g * h, k)) + ψ (c (g, h))
      = ψ (c (g * h, k) + c (g, h)) := by rw [map_add]
    _ = ψ (g • c (h, k) + c (g, h * k)) := by rw [h1]
    _ = g • ψ (c (h, k)) + ψ (c (g, h * k)) := by rw [map_add, hψ]

/-- `LinearMap.lTensor` of a `G`-equivariant map is `G`-equivariant for the diagonal `G`-actions
on tensor products (`Work.Shrinking.instDistribMulActionTensorProduct`). -/
theorem shapiroPkg_lTensor_equivariant
    {p : ℕ} {G : Type*} [Group G]
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    {N N' : Type*} [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [AddCommGroup N'] [Module (ZMod p) N']
    [DistribMulAction G N'] [SMulCommClass G (ZMod p) N']
    (f : N →ₗ[ZMod p] N') (hf : ∀ (g : G) (n : N), f (g • n) = g • f n) (g : G)
    (x : M ⊗[ZMod p] N) :
    (LinearMap.lTensor M f) (g • x) = g • (LinearMap.lTensor M f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
      rw [Work.Shrinking.diagTensor_smul_tmul, LinearMap.lTensor_tmul, hf,
        LinearMap.lTensor_tmul, Work.Shrinking.diagTensor_smul_tmul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- `LinearMap.lTensor` and `LinearMap.rTensor` commute. -/
theorem shapiroPkg_lTensor_rTensor_comm
    {p : ℕ} {M N M' N' : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M']
    [AddCommMonoid N'] [Module (ZMod p) M] [Module (ZMod p) N] [Module (ZMod p) M']
    [Module (ZMod p) N'] (f : M →ₗ[ZMod p] M') (g : N →ₗ[ZMod p] N')
    (z : M ⊗[ZMod p] N) :
    (LinearMap.lTensor M' g) ((LinearMap.rTensor N f) z)
      = (LinearMap.rTensor N' f) ((LinearMap.lTensor M g) z) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

/-! ## Equivariance of the coordinate projection and insertion of `shapiroT` -/

/-- The coordinate projection `shapiroProj p G ι H a` is `G`-equivariant. -/
theorem shapiroPkg_shapiroProj_equivariant (p : ℕ) (G : Type*) [Group G] (ι : Type*)
    (H : ι → Subgroup G) (a : ι) (g : G) (v : shapiroT p G ι H) :
    shapiroProj p G ι H a (g • v) = g • shapiroProj p G ι H a v := by
  simp only [shapiroProj, LinearMap.proj_apply, Pi.smul_apply]

/-- The coordinate insertion `shapiroSingle p G ι H a` is `G`-equivariant. -/
theorem shapiroPkg_shapiroSingle_equivariant (p : ℕ) (G : Type*) [Group G] (ι : Type*)
    [DecidableEq ι] (H : ι → Subgroup G) (a : ι) (g : G)
    (v : Shapiro.PermModX p (G ⧸ H a)) :
    shapiroSingle p G ι H a (g • v) = g • shapiroSingle p G ι H a v := by
  simp only [shapiroSingle, LinearMap.single_apply, Pi.single_smul]

/-- The coordinate projection is a left inverse of the coordinate insertion inside a tensor
product. -/
theorem shapiroPkg_shapiroProj_single_apply (p : ℕ) (G : Type*) [Group G] (ι : Type*)
    [DecidableEq ι] (H : ι → Subgroup G) (M : Type*) [AddCommGroup M] [Module (ZMod p) M]
    (a : ι) (x : M ⊗[ZMod p] Shapiro.PermModX p (G ⧸ H a)) :
    (LinearMap.lTensor M (shapiroProj p G ι H a))
      ((LinearMap.lTensor M (shapiroSingle p G ι H a)) x) = x := by
  revert x
  simp only [shapiroSingle, shapiroProj]
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m t =>
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.single_apply,
        LinearMap.proj_apply, Pi.single_eq_same]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-! ## The packaging theorem -/

theorem shapiro_packaging_natural (p : ℕ) (G : Type*) [Group G] [Fintype G]
    (ι : Type*) [Fintype ι] (H : ι → Subgroup G)
    (M : Type*) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    (κ : ∀ a : ι, ↥(H a) × ↥(H a) → M)
    (hκ : ∀ a : ι,
      (letI : DistribMulAction ↥(H a) M := DistribMulAction.compHom M (Subgroup.subtype (H a))
       κ a ∈ Work.GroupCohomology.Z2 (↥(H a)) M)) :
    ∃ (ev : ∀ a : ι, TensorProduct (ZMod p) M (shapiroT p G ι H) →ₗ[ZMod p] M)
      (_ : ∀ (a : ι) (h : ↥(H a)) (z : TensorProduct (ZMod p) M (shapiroT p G ι H)),
        ev a ((h : G) • z) = (h : G) • ev a z)
      (C : ∀ a : ι, G × G → TensorProduct (ZMod p) M (shapiroT p G ι H)),
      (∀ a : ι, C a ∈ Work.GroupCohomology.Z2 G (TensorProduct (ZMod p) M (shapiroT p G ι H))) ∧
      (∀ (a : ι) (h h' : ↥(H a)),
        ev a (C a ((h : G), (h' : G))) = κ a (h, h')) ∧
      (∀ (M' : Type*) [AddCommGroup M'] [Module (ZMod p) M'] [DistribMulAction G M']
        [SMulCommClass G (ZMod p) M']
        (θ : M →ₗ[ZMod p] M') (_ : ∀ (g : G) (m : M), θ (g • m) = g • θ m),
        ∃ (evθ : ∀ a : ι, TensorProduct (ZMod p) M' (shapiroT p G ι H) →ₗ[ZMod p] M')
          (_ : ∀ (a : ι) (h : ↥(H a)) (z : TensorProduct (ZMod p) M' (shapiroT p G ι H)),
            evθ a ((h : G) • z) = (h : G) • evθ a z),
          ∀ (a : ι) (z : TensorProduct (ZMod p) M (shapiroT p G ι H)),
            evθ a (θ.rTensor (shapiroT p G ι H) z) = θ (ev a z)) := by
  classical
  -- the per-coordinate Shapiro induction, instantiated at the framed `G`-set `G ⧸ H a`
  have hdata := fun a : ι =>
    shapiro_framed_natural p G (H a) (G ⧸ H a) (Shapiro.sec p G (H a))
      (fun g x => (Shapiro.A p G (H a) g x).property) (Shapiro.basePoint p G (H a))
      (Shapiro.sec_basePoint p G (H a)) (fun h => Shapiro.basePoint_smul_eq p G (H a) h)
      M (κ a) (hκ a)
  choose E hE D hDZ hDval hDnat using hdata
  -- `ev a` reads the `a`-th coordinate; `C a` is inserted into the `a`-th coordinate
  refine ⟨fun a => (E a).comp (LinearMap.lTensor M (shapiroProj p G ι H a)), ?_,
    fun a q => (LinearMap.lTensor M (shapiroSingle p G ι H a)) (D a q), ?_, ?_, ?_⟩
  · intro a h z
    show (E a) ((LinearMap.lTensor M (shapiroProj p G ι H a)) ((h : G) • z))
      = (h : G) • (E a) ((LinearMap.lTensor M (shapiroProj p G ι H a)) z)
    rw [shapiroPkg_lTensor_equivariant (f := shapiroProj p G ι H a)
      (fun g' n => shapiroPkg_shapiroProj_equivariant p G ι H a g' n) (h : G) z]
    exact hE a h _
  · intro a
    exact shapiroPkg_mem_Z2_comp_of_equivariant
      (ψ := LinearMap.lTensor M (shapiroSingle p G ι H a))
      (fun g' x => shapiroPkg_lTensor_equivariant (f := shapiroSingle p G ι H a)
        (fun g'' n => shapiroPkg_shapiroSingle_equivariant p G ι H a g'' n) g' x)
      (D a) (hDZ a)
  · intro a h h'
    show (E a) ((LinearMap.lTensor M (shapiroProj p G ι H a))
      ((LinearMap.lTensor M (shapiroSingle p G ι H a)) (D a ((h : G), (h' : G))))) = κ a (h, h')
    rw [shapiroPkg_shapiroProj_single_apply p G ι H M a (D a ((h : G), (h' : G)))]
    exact hDval a h h'
  · intro M' _ _ _ _ θ hθ
    have hE' : ∀ a : ι,
        ∃ (E' : TensorProduct (ZMod p) M' (Shapiro.PermModX p (G ⧸ H a)) →ₗ[ZMod p] M')
          (_ : ∀ (h : ↥(H a)) (z : TensorProduct (ZMod p) M' (Shapiro.PermModX p (G ⧸ H a))),
            E' ((h : G) • z) = (h : G) • E' z),
          ∀ z : TensorProduct (ZMod p) M (Shapiro.PermModX p (G ⧸ H a)),
            E' ((LinearMap.rTensor (Shapiro.PermModX p (G ⧸ H a)) θ) z) = θ (E a z) :=
      fun a => hDnat a M' θ hθ
    choose E' hE'ev hE'nat using hE'
    refine ⟨fun a => (E' a).comp (LinearMap.lTensor M' (shapiroProj p G ι H a)), ?_, ?_⟩
    · intro a h z
      show (E' a) ((LinearMap.lTensor M' (shapiroProj p G ι H a)) ((h : G) • z))
        = (h : G) • (E' a) ((LinearMap.lTensor M' (shapiroProj p G ι H a)) z)
      rw [shapiroPkg_lTensor_equivariant (f := shapiroProj p G ι H a)
        (fun g' n => shapiroPkg_shapiroProj_equivariant p G ι H a g' n) (h : G) z]
      exact hE'ev a h _
    · intro a z
      show (E' a) ((LinearMap.lTensor M' (shapiroProj p G ι H a))
          ((LinearMap.rTensor (shapiroT p G ι H) θ) z))
        = θ ((E a) ((LinearMap.lTensor M (shapiroProj p G ι H a)) z))
      rw [shapiroPkg_lTensor_rTensor_comm (f := θ) (g := shapiroProj p G ι H a) z]
      exact hE'nat a _

end Work.SSGRoute
