import Mathlib
import Submission.Work.MotT.TwistPointKDefs
import Submission.Work.MotT.evalAt_unique
import Submission.Work.MotC2.TransPlace

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

/-- **Evaluation commutes with translation.**  Let `E` be an elliptic Weierstrass curve over a
field `L`, let `Q = (q₁,q₂)` and `Q' = (q₁',q₂')` be nonsingular affine points, and let
`A : E.toAffine.Point` with `Q + A = Q'` (all points over `L`).  Then for every function `f` regular
at `Q'`, the translated function `τ_A f = transAlgEquiv E A f` is regular at `Q` and has the same
value there: `evalAtLoc E q₁ q₂ (τ_A f) = evalAtLoc E q₁' q₂' f`.

Here `evalAtLoc E a b : ↥(affPlaceAt E a b) →ₐ[L] L` is the residue map of the local ring at the
nonsingular affine point `(a,b)` (`Work.MotT.TwistPointKDefs`), characterised by
`evalAtLoc E a b (algebraMap (Coord E) _ r) = plugHomAt E a b h r`.

Route (handed to the prover).

1. Membership: `map_transAlgEquiv_affPlaceAt` (in `Work.MotT.TwistPointKDefs`) gives
   `Subalgebra.map (τ_A) (affPlaceAt E q₁' q₂') = affPlaceAt E q₁ q₂`, hence `τ_A f ∈ affPlaceAt E q₁ q₂`.

2. It suffices (`evalAtLoc_ext`) to prove, for every `r : Coord E`,
   `evalAtLoc E q₁ q₂ ⟨τ_A (algebraMap (Coord E) (Func E) r), _⟩ = plugHomAt E q₁' q₂' h' r`.

3. Both `r ↦ evalAtLoc E q₁ q₂ ⟨τ_A (algebraMap (Coord E) (Func E) r), _⟩` and
   `plugHomAt E q₁' q₂' h'` are `L`-algebra homomorphisms `Coord E →ₐ[L] L`, and `Coord E` is
   generated over `L` by `coordX`, `coordY` (`Work.MotC2.adjoin_coordX_coordY`).  So it suffices to
   check on `coordX` and `coordY`: the first sends them to `evalAtLoc E q₁ q₂ ⟨transX E A, _⟩` and
   `evalAtLoc E q₁ q₂ ⟨transY E A, _⟩` (`transAlgEquiv_apply`, `Work.MotC2.phi_genX`,
   `Work.MotC2.phi_genY`), the second to `q₁'` and `q₂'`.

4. Numerical input: `evalAtLoc E q₁ q₂ ⟨transX E A, _⟩ = q₁'`, `... ⟨transY E A, _⟩ = q₂'`.
   * `A = 0`: `transX_zero`; `evalAtLoc` of `algebraMap (Coord E) _ coordX` is `q₁`, and `Q' = Q`.
   * `A = Point.some a b hA`, `q₁ ≠ a`: by `transX_some` and `slope_of_X_ne (genX_ne_algebraMap E a)`,
     `transX E A = addX (baseE E) (genX E) (algebraMap L (Func E) a)
        ((genY E - algebraMap L (Func E) b) / (genX E - algebraMap L (Func E) a))`.
     Since `q₁ ≠ a`, `genX E - algebraMap L (Func E) a` is a unit of `↥(affPlaceAt E q₁ q₂)` (its
     `evalAtLoc`-value is `q₁ - a ≠ 0`), so the expression lies in the local ring and `evalAtLoc`
     commutes with the polynomial `addX` formula: `addX E q₁ a ((q₂-b)/(q₁-a)) =
     addX E q₁ a (slope E q₁ a q₂ b)`, which is `q₁'` by `Point.add_of_X_ne` applied to `hA` and
     `Point.some.injEq`.
   * `A = Point.some a b hA`, `q₁ = a`: then `q₂ = b` (Mathlib's `Y_eq_of_X_eq`, using that
     `Q + A ≠ 0`), so `A = Q` and `slope E q₁ a q₂ b = (3q₁^2 + 2a₂q₁ + a₄ - a₁q₂)/(q₂ - negY E q₁ q₂)`
     (`slope_of_Y_ne`).  Put `u := genX E - alg a`, `v := genY E - alg b` in `Func E`; subtracting the
     Weierstrass relation (`genX_genY_relation E`) from the equation at `(a,b)` gives, in
     `↥(affPlaceAt E q₁ q₂)`, `v * (ψ + a₁*u + v) = u * (λ + (3a + a₂)*u + u^2)` with
     `ψ = 2b + a₁*a + a₃`, `λ = 3a^2 + 2a₂*a + a₄ - a₁*b`.  `ψ + a₁*u + v` is a unit (value `ψ ≠ 0`,
     since `Q + A = 2Q ≠ 0`), hence `v/u = (λ + (3a+a₂)*u + u^2) * (ψ + a₁u + v)⁻¹` in the local ring
     and `evalAtLoc (v/u) = λ/ψ = slope E q₁ a q₂ q₂`; conclude with
     `Point.add_self_of_Y_ne`/`add_of_Y_ne` and `Point.some.injEq`.-/
theorem evalAtLoc_transAlgEquiv {L : Type} [Field L] [DecidableEq L]
    (E : WeierstrassCurve L) [E.IsElliptic] {q₁ q₂ q₁' q₂' : L}
    [hns : Work.MotC2.IsNonsingularPoint E q₁ q₂]
    [hns' : Work.MotC2.IsNonsingularPoint E q₁' q₂'] (A : E.toAffine.Point)
    (hA : WeierstrassCurve.Affine.Point.some q₁ q₂ hns.nonsingular + A
      = WeierstrassCurve.Affine.Point.some q₁' q₂' hns'.nonsingular) :
    ∀ f : ↥(Work.MotC2.affPlaceAt E q₁' q₂'),
      ∃ hf : (Work.MotC2.transAlgEquiv E A) (f : Work.MotC2.Func E)
          ∈ Work.MotC2.affPlaceAt E q₁ q₂,
        evalAtLoc E q₁ q₂ ⟨_, hf⟩ = evalAtLoc E q₁' q₂' f := by
  intro f
  -- `τ_A` carries the local ring at `Q'` into the local ring at `Q`
  have hmem : ∀ x : ↥(Work.MotC2.affPlaceAt E q₁' q₂'),
      (Work.MotC2.transAlgEquiv E A) (x : Work.MotC2.Func E) ∈
        Work.MotC2.affPlaceAt E q₁ q₂ := by
    intro x
    rw [← map_transAlgEquiv_affPlaceAt E hns.nonsingular hns'.nonsingular A hA]
    exact Subalgebra.mem_map.mpr ⟨(x : Work.MotC2.Func E), x.2, rfl⟩
  refine ⟨hmem f, ?_⟩
  -- the composite `evalAtLoc E q₁ q₂ ∘ τ_A` is an `L`-algebra map `𝒪_{Q'} →ₐ[L] L`, and so is
  -- `evalAtLoc E q₁' q₂'`; the residue map out of a rational place is unique
  have hψ : (evalAtLoc E q₁ q₂).comp
      (((Work.MotC2.transAlgEquiv E A).toAlgHom.comp
          (Subalgebra.val (Work.MotC2.affPlaceAt E q₁' q₂'))).codRestrict
        (Work.MotC2.affPlaceAt E q₁ q₂) (fun y => hmem y)) = evalAtLoc E q₁' q₂' :=
    evalAt_unique E q₁' q₂' _ _
  have h := DFunLike.congr_fun hψ f
  exact h

end Work.MotT
