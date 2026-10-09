import Mathlib
import Submission.Work.Shrinking.Basic
import Submission.Work.GroupCohomology.Basic
import Submission.Work.SSGRoute.ShapiroSetup
import Submission.Work.SSGRoute.ShapiroInduced
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped TensorProduct

/-- **Induction ("half of Shapiro") for 2-cocycles.** Let `G` be a finite group, `H ≤ G` a
subgroup, `p` a prime and `M` an `𝔽_p[G]`-module. For every 2-cocycle `c` on `H` with values in `M`
(the `H`-action being the restriction of the `G`-action) there is a finitely generated
`𝔽_p[G]`-module `T`, an `H`-equivariant `𝔽_p`-linear map `ev : M ⊗ T → M` and a 2-cocycle `C` on
`G` with values in `M ⊗ T` such that `ev (C (h,h')) = c (h,h')` for all `h h' : H`.

(Here `M ⊗ T` carries the diagonal `G`-action, `Work.Shrinking.instDistribMulActionTensorProduct`.)

Construction: take `T` the permutation module on the coset space, with `ev` the coefficient at the
coset `H`; the cocycle `C` is the standard induced 2-cocycle (built from a section of the coset
projection and the two "coset decomposition" factors in `H`). -/
theorem shapiro_induce_two_cocycle (p : ℕ) (G : Type*) [Group G] [Fintype G] (H : Subgroup G)
    [Fintype H] (M : Type*) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] (c : H × H → M) (hc : c ∈ Work.GroupCohomology.Z2 H M) :
    ∃ (T : Type*) (_ : AddCommGroup T) (_ : Module (ZMod p) T) (_ : DistribMulAction G T)
      (_ : SMulCommClass G (ZMod p) T) (_ : Module.Finite (ZMod p) T)
      (ev : M ⊗[ZMod p] T →ₗ[ZMod p] M)
      (_ : ∀ (h : H) (x : M ⊗[ZMod p] T), ev ((h : G) • x) = (h : G) • ev x)
      (C : G × G → M ⊗[ZMod p] T),
      C ∈ Work.GroupCohomology.Z2 G (M ⊗[ZMod p] T) ∧
        ∀ h h' : H, ev (C (h, h')) = c (h, h') := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  -- A "small", universe-flexible model `X` of the `G`-set `G ⧸ H`: `X` is a lifting of a
  -- finite type, so it can be placed in any universe.
  let X := ULift (Fin (Fintype.card (G ⧸ H)))
  let e : X ≃ (G ⧸ H) := Equiv.ulift.trans (Fintype.equivFin (G ⧸ H)).symm
  haveI : Fintype X := Fintype.ofEquiv (G ⧸ H) e.symm
  letI : MulAction G X :=
    { smul := fun g y => e.symm (g • e y)
      one_smul := fun y => by
        show e.symm (1 • e y) = y
        rw [one_smul, Equiv.symm_apply_apply]
      mul_smul := fun g g' y => by
        show e.symm ((g * g') • e y) = e.symm (g • e (e.symm (g' • e y)))
        rw [Equiv.apply_symm_apply, mul_smul] }
  let s : X → G := fun y => Shapiro.sec p G H (e y)
  let x₀ : X := e.symm (Shapiro.basePoint p G H)
  have hsec : ∀ (g : G) (y : X), (s y)⁻¹ * g * s (g⁻¹ • y) ∈ H := by
    intro g y
    have h1 : s (g⁻¹ • y) = Shapiro.sec p G H (g⁻¹ • e y) := by
      show Shapiro.sec p G H (e (g⁻¹ • y)) = Shapiro.sec p G H (g⁻¹ • e y)
      congr 1
      change e (e.symm (g⁻¹ • e y)) = g⁻¹ • e y
      rw [Equiv.apply_symm_apply]
    have h2 : (s y)⁻¹ * g * s (g⁻¹ • y) = (Shapiro.A p G H g (e y) : G) := by
      rw [Shapiro.coe_A, h1]
    rw [h2]
    exact (Shapiro.A p G H g (e y)).property
  have hbase : s x₀ = 1 := by
    show Shapiro.sec p G H (e (e.symm (Shapiro.basePoint p G H))) = 1
    rw [Equiv.apply_symm_apply]
    exact Shapiro.sec_basePoint p G H
  have hfix : ∀ h : H, (h : G) • x₀ = x₀ := by
    intro h
    have hx : e x₀ = Shapiro.basePoint p G H :=
      Equiv.apply_symm_apply e (Shapiro.basePoint p G H)
    change e.symm ((h : G) • e x₀) = x₀
    rw [hx, Shapiro.basePoint_smul_eq p G H h]
  have hc' : ∀ a b e : H, c (a * b, e) + c (a, b) = (a : G) • c (b, e) + c (a, b * e) :=
    (Work.GroupCohomology.mem_Z2_iff H M c).mp hc
  let Φ := Shapiro.permEquivX p X M
  let ev : M ⊗[ZMod p] Shapiro.PermModX p X →ₗ[ZMod p] M :=
    (LinearMap.proj x₀).comp Φ.toLinearMap
  let C : G × G → M ⊗[ZMod p] Shapiro.PermModX p X :=
    fun q => Φ.symm (Shapiro.funCX G H X s hsec M c q.1 q.2)
  refine ⟨Shapiro.PermModX p X, inferInstance, inferInstance, inferInstance, inferInstance,
    Shapiro.moduleFinite_permModX p X, ev, ?_, C, ?_, ?_⟩
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
    dsimp only [C, x₀]
    rw [LinearEquiv.apply_symm_apply]
    exact Shapiro.funCX_base G H X s hsec x₀ M hbase hfix c h h'

end Work.SSGRoute
