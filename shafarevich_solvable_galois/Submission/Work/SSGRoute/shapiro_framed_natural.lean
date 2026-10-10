import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Tactic.Have
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.TensorProduct.Map
import Submission.Work.GroupCohomology.Basic
import Submission.Work.SSGRoute.ShapiroInduced
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

open scoped TensorProduct

universe u v w

/-- **Naturality of the identification `M ⊗ 𝔽_p[X] ≃ (X → M)`.**  Tensoring a `𝔽_p`-linear map
`θ : M → M'` with the identity of `𝔽_p[X]` corresponds, under the canonical identification with
function spaces, to postcomposition with `θ`. -/
theorem permEquivX_rTensor (p : ℕ) (X : Type w) [Fintype X] [DecidableEq X]
    (M : Type v) [AddCommGroup M] [Module (ZMod p) M]
    (M' : Type u) [AddCommGroup M'] [Module (ZMod p) M']
    (θ : M →ₗ[ZMod p] M') (z : M ⊗[ZMod p] Shapiro.PermModX p X) :
    Shapiro.permEquivX p X M' ((LinearMap.rTensor (Shapiro.PermModX p X) θ) z)
      = fun x => θ (Shapiro.permEquivX p X M z x) := by
  induction z using TensorProduct.induction_on with
  | zero => ext x; simp
  | tmul m f =>
      ext x
      rw [LinearMap.rTensor_tmul, Shapiro.permEquivX_tmul, Shapiro.permEquivX_tmul]
      exact (map_smul θ (f x) m).symm
  | add z w hz hw =>
      rw [map_add, map_add, hz, hw]
      ext x
      simp only [Pi.add_apply, map_add]

/-- **Half of Shapiro, on an abstract framed `G`-set with a fixed coefficient module, natural in
the coefficients.**

Let `H ≤ G`, let `X` be a framed `G`-set with base point `x₀` fixed by `H`, and let `M` be an
`𝔽_p[G]`-module.  For a `2`-cocycle `c` on `H` with values in `M` there are

* an `H`-equivariant `𝔽_p`-linear `ev : M ⊗ 𝔽_p[X] → M`,
* a `2`-cocycle `C` on `G` with values in the diagonal module `M ⊗ 𝔽_p[X]`,

such that `ev (C (h, h')) = c (h, h')` for all `h h' : H`, and such that the construction is
natural in the coefficient module: for every `G`-equivariant `𝔽_p`-linear `θ : M → M'` there is a
`H`-equivariant `𝔽_p`-linear `evθ : M' ⊗ 𝔽_p[X] → M'` with
`evθ ((θ.rTensor 𝔽_p[X]) z) = θ (ev z)` for all `z`. -/
theorem shapiro_framed_natural (p : ℕ) (G : Type*) [Group G] (H : Subgroup G)
    (X : Type*) [MulAction G X] [Fintype X] [DecidableEq X]
    (s : X → G) (hsec : ∀ (g : G) (x : X), (s x)⁻¹ * g * s (g⁻¹ • x) ∈ H)
    (x₀ : X) (hbase : s x₀ = 1) (hfix : ∀ h : ↥H, (h : G) • x₀ = x₀)
    (M : Type*) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    (c : ↥H × ↥H → M)
    (hc : (letI : DistribMulAction ↥H M := DistribMulAction.compHom M (Subgroup.subtype H)
      c ∈ Work.GroupCohomology.Z2 ↥H M)) :
    ∃ (ev : TensorProduct (ZMod p) M (Work.SSGRoute.Shapiro.PermModX p X) →ₗ[ZMod p] M)
      (_ : ∀ (h : ↥H) (z : TensorProduct (ZMod p) M (Work.SSGRoute.Shapiro.PermModX p X)),
        ev ((h : G) • z) = (h : G) • ev z)
      (C : G × G → TensorProduct (ZMod p) M (Work.SSGRoute.Shapiro.PermModX p X)),
      C ∈ Work.GroupCohomology.Z2 G
        (TensorProduct (ZMod p) M (Work.SSGRoute.Shapiro.PermModX p X)) ∧
      (∀ h h' : ↥H, ev (C ((h : G), (h' : G))) = c (h, h')) ∧
      (∀ (M' : Type*) [AddCommGroup M'] [Module (ZMod p) M'] [DistribMulAction G M']
        [SMulCommClass G (ZMod p) M']
        (θ : M →ₗ[ZMod p] M') (_ : ∀ (g : G) (m : M), θ (g • m) = g • θ m),
        ∃ (evθ : TensorProduct (ZMod p) M' (Work.SSGRoute.Shapiro.PermModX p X) →ₗ[ZMod p] M')
          (_ : ∀ (h : ↥H) (z : TensorProduct (ZMod p) M' (Work.SSGRoute.Shapiro.PermModX p X)),
            evθ ((h : G) • z) = (h : G) • evθ z),
          ∀ z : TensorProduct (ZMod p) M (Work.SSGRoute.Shapiro.PermModX p X),
            evθ ((LinearMap.rTensor (Work.SSGRoute.Shapiro.PermModX p X) θ) z) = θ (ev z)) := by
  classical
  -- The `H`-action used throughout is the restriction of the `G`-action.
  letI : DistribMulAction ↥H M := DistribMulAction.compHom M (Subgroup.subtype H)
  have hc' : ∀ a b e : ↥H, c (a * b, e) + c (a, b) = (a : G) • c (b, e) + c (a, b * e) :=
    (Work.GroupCohomology.mem_Z2_iff ↥H M c).mp hc
  let Φ := Shapiro.permEquivX p X M
  let ev : M ⊗[ZMod p] Shapiro.PermModX p X →ₗ[ZMod p] M :=
    (LinearMap.proj x₀).comp Φ.toLinearMap
  let C : G × G → M ⊗[ZMod p] Shapiro.PermModX p X :=
    fun q => Φ.symm (Shapiro.funCX G H X s hsec M c q.1 q.2)
  refine ⟨ev, ?_, C, ?_, ?_, ?_⟩
  · -- `ev` is `H`-equivariant
    intro h z
    have hfix' : (((h : G))⁻¹ • x₀ : X) = x₀ := by simpa using hfix (h⁻¹)
    show Φ ((h : G) • z) x₀ = (h : G) • (Φ z x₀)
    rw [Shapiro.permEquivX_smul p G X M (h : G) z]
    show (h : G) • Φ z ((h : G)⁻¹ • x₀) = (h : G) • Φ z x₀
    rw [hfix']
  · -- the cocycle condition
    rw [Work.GroupCohomology.mem_Z2_iff]
    intro g g' g''
    have hC : ∀ a b : G, Φ (C (a, b)) = Shapiro.funCX G H X s hsec M c a b := by
      intro a b
      dsimp only [C]
      rw [LinearEquiv.apply_symm_apply]
    have hsmul : Φ (g • C (g', g''))
        = fun x => g • Shapiro.funCX G H X s hsec M c g' g'' (g⁻¹ • x) := by
      rw [Shapiro.permEquivX_smul p G X M g (C (g', g'')), hC g' g'']
    apply Φ.injective
    calc Φ (C (g * g', g'') + C (g, g'))
        = Φ (C (g * g', g'')) + Φ (C (g, g')) := by rw [map_add]
      _ = Shapiro.funCX G H X s hsec M c (g * g') g''
            + Shapiro.funCX G H X s hsec M c g g' := by rw [hC (g * g') g'', hC g g']
      _ = (fun x => g • Shapiro.funCX G H X s hsec M c g' g'' (g⁻¹ • x))
            + Shapiro.funCX G H X s hsec M c g (g' * g'') := by
            funext x
            simp only [Pi.add_apply]
            exact Shapiro.funCX_add_eq G H X s hsec M c hc' g g' g'' x
      _ = Φ (g • C (g', g'')) + Φ (C (g, g' * g'')) := by rw [← hsmul, ← hC g (g' * g'')]
      _ = Φ (g • C (g', g'') + C (g, g' * g'')) := by rw [← map_add]
  · -- the value at the base point
    intro h h'
    show Φ (C (h, h')) x₀ = c (h, h')
    dsimp only [C]
    rw [LinearEquiv.apply_symm_apply]
    exact Shapiro.funCX_base G H X s hsec x₀ M hbase hfix c h h'
  · -- naturality in the coefficient module
    intro M' hAdd hMod hAct hComm θ hθ
    letI : AddCommGroup M' := hAdd
    letI : Module (ZMod p) M' := hMod
    letI : DistribMulAction G M' := hAct
    letI : SMulCommClass G (ZMod p) M' := hComm
    let Φ' := Shapiro.permEquivX p X M'
    refine ⟨(LinearMap.proj x₀).comp Φ'.toLinearMap, ?_, ?_⟩
    · intro h z
      have hfix' : (((h : G))⁻¹ • x₀ : X) = x₀ := by simpa using hfix (h⁻¹)
      show Φ' ((h : G) • z) x₀ = (h : G) • (Φ' z x₀)
      rw [Shapiro.permEquivX_smul p G X M' (h : G) z]
      show (h : G) • Φ' z ((h : G)⁻¹ • x₀) = (h : G) • Φ' z x₀
      rw [hfix']
    · intro z
      show Φ' ((LinearMap.rTensor (Shapiro.PermModX p X) θ) z) x₀ = θ (Φ z x₀)
      rw [permEquivX_rTensor p X M M' θ z]

end Work.SSGRoute
