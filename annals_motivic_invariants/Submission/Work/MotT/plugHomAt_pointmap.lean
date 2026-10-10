import Mathlib
import Submission.Work.MotT.TwistPointKDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

/-- **Galois equivariance of the point evaluation on the base-change generators.**  Let `W` be a
Weierstrass curve over a field `K`, `L` a field extension of `K`, `σ : L ≃ₐ[K] L`, and let
`q₁ q₂ : L` be such that `(q₁,q₂)` is a nonsingular affine point of the base change `W⁄L` (and
likewise for `(σ q₁, σ q₂)`).  For an element `r` of the affine coordinate ring of `W⁄L` which is a
`K`-polynomial in the two coordinates `coordX`, `coordY`
(`r ∈ Algebra.adjoin K {coordX, coordY}`), the value of `r` at `(q₁,q₂)` is carried by `σ` to the
value at `(σ q₁, σ q₂)`:

`σ (plugHomAt (W⁄L) q₁ q₂ h r) = plugHomAt (W⁄L) (σ q₁) (σ q₂) h' r`.

Route: `Algebra.adjoin_induction` on the generating set.  The two maps agree on the generators
`coordX`, `coordY` (`plugHomAt_coordX`, `plugHomAt_coordY`) and on the constants
`algebraMap K (Coord (W⁄L)) c` (both sides are `algebraMap K L c`, using `σ.commutes` and
`plugHomAt_algebraMap_K`), and both sides are additive and multiplicative in `r`. -/
theorem plugHomAt_pointmap {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (σ : L ≃ₐ[K] L) {q₁ q₂ : L}
    (h : WeierstrassCurve.Affine.Nonsingular (W.baseChange L) q₁ q₂)
    (h' : WeierstrassCurve.Affine.Nonsingular (W.baseChange L) (σ q₁) (σ q₂))
    (r : Work.MotC2.Coord (W.baseChange L))
    (hr : r ∈ Algebra.adjoin K ({Work.MotC2.coordX (W.baseChange L),
      Work.MotC2.coordY (W.baseChange L)} : Set (Work.MotC2.Coord (W.baseChange L)))) :
    σ (plugHomAt (W.baseChange L) q₁ q₂ h r) =
      plugHomAt (W.baseChange L) (σ q₁) (σ q₂) h' r := by
  let E := W.baseChange L
  -- Two `K`-algebra homomorphisms `Coord E →ₐ[K] L`: the composite `σ ∘ plugHomAt` and the
  -- evaluation at the conjugate point `(σ q₁, σ q₂)`.
  let φ : Work.MotC2.Coord E →ₐ[K] L :=
    σ.toAlgHom.comp ((plugHomAt E q₁ q₂ h).restrictScalars K)
  let ψ : Work.MotC2.Coord E →ₐ[K] L :=
    (plugHomAt E (σ q₁) (σ q₂) h').restrictScalars K
  have key : ∀ x ∈ Algebra.adjoin K ({Work.MotC2.coordX E, Work.MotC2.coordY E} : Set _),
      φ x = ψ x := by
    intro x hx
    refine Algebra.adjoin_induction (p := fun x _ => φ x = ψ x) ?_ ?_ ?_ ?_ hx
    · -- the two generators `coordX`, `coordY`
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl <;> simp [φ, ψ, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        AlgEquiv.toAlgHom_apply]
    · -- the constants: both sides are `algebraMap K L c`
      intro c
      show φ (algebraMap K (Work.MotC2.Coord E) c) = ψ (algebraMap K (Work.MotC2.Coord E) c)
      simp only [φ, ψ, AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.toAlgHom_apply]
      rw [plugHomAt_algebraMap_K, plugHomAt_algebraMap_K]
      exact σ.commutes c
    · -- additivity
      intro x y _ _ hpx hpy
      rw [map_add, map_add, hpx, hpy]
    · -- multiplicativity
      intro x y _ _ hpx hpy
      rw [map_mul, map_mul, hpx, hpy]
  have := key r hr
  simpa [φ, ψ, AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.toAlgHom_apply] using this

end Work.MotT
