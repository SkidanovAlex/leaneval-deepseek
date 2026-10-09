import Mathlib
import Submission.Work.SSGRoute.ZDataMup.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

/-- Every `𝔽_p`-vector space (any module over the field `ZMod p`) carries a bilinear form which is
non-degenerate in its first variable.  Route: `Module.Basis.ofVectorSpace` (available since `ZMod p`
is a division ring) gives a basis `b`; put `F x y := ∑ᶠ i, (b.repr x i) * (b.repr y i)`.  If `x ≠ 0`
pick `i` in the support of `b.repr x` and take `y := b i`, so `F x y = b.repr x i ≠ 0`. -/
theorem exists_leftNondegenerate_bilinearForm (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] :
    ∃ F : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p, ∀ x : V, (∀ y : V, F x y = 0) → x = 0 := by
  classical
  -- Concretely the "dot product with respect to a basis": the functional `F x` is the linear form
  -- whose `i`-th coordinate against the dual basis `b.coord` is `b.repr x i`.
  let b := Module.Basis.ofVectorSpace (ZMod p) V
  refine ⟨(b.constr (ZMod p)) b.coord, ?_⟩
  intro x hx
  -- Key symmetry/duality computation: `F x` evaluated at the basis vector `b i` recovers the
  -- `i`-th coordinate of `x`.
  have hkey : ∀ i : ↑(Module.Basis.ofVectorSpaceIndex (ZMod p) V),
      (LinearMap.applyₗ (b i)).comp ((b.constr (ZMod p)) b.coord) = b.coord i := by
    intro i
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, Module.Basis.constr_basis, LinearMap.applyₗ_apply_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self_apply, eq_comm]
  have hxi : ∀ i : ↑(Module.Basis.ofVectorSpaceIndex (ZMod p) V),
      ((b.constr (ZMod p)) b.coord) x (b i) = (b.coord i) x := by
    intro i
    have := congrArg (fun f : V →ₗ[ZMod p] ZMod p => f x) (hkey i)
    simpa [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply] using this
  -- Since `F x` vanishes everywhere, in particular on every basis vector, so every coordinate of
  -- `x` is zero, whence `x = 0`.
  have hrepr : b.repr x = 0 := by
    ext i
    have h0 : (b.coord i) x = 0 := by rw [← hxi i, hx (b i)]
    rwa [← Module.Basis.coord_apply b i x]
  exact (b.repr.map_eq_zero_iff).mp hrepr

end Work.SSGRoute.ZDataMup
