import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Route V5 (characteristic `5`): base preservation for the Artin–Schreier link

This is the node **V1_AS** of `MOTIVIC_S45_LEAD.md` §C5 (`base_preserved_AS`), the
characteristic-`5` analogue of **V1** of §3 of that file: if `θ : F₁ ≃ₐ[𝕜] F₂` is a
`𝕜`-isomorphism of two `K = 𝕜(t)`-fields that both embed over the constants into the function
field `N(E)` of an elliptic curve over an algebraically closed field `N ⊇ K`, and both carry
the Artin–Schreier bridge condition `ASUnramified` (`Work.MotV5.ASUnramified`) at the poles of
`t`, then `θ` preserves `K`.

The proof is the one of §3 V1:

1. the composite `ι₂ ∘ θ` carries the `ASUnramified` hypothesis of `F₁` to the H1-hypothesis
   (`hurwitz_AS`) of the point `r = ι₂ (θ t)`;
2. `hurwitz_AS` (the hypothesis `hH1` of the statement) then puts `r` in the constants `N`,
   so `r` is algebraic over `K`, and by injectivity of `ι₂` so is `θ t`;
3. `hR₂` (regularity: `K` is relatively algebraically closed in `F₂`) makes `θ t ∈ K`;
4. an `𝕜`-algebra map out of `K = 𝕜(t)` that sends `t` into the image of `K` maps all of `K`
   into that image.

## Note on the coefficient ring of the polynomial in `hH1`

The hypothesis `hH1` contains the polynomial `Polynomial.X ^ 3 + Polynomial.X`.  In this
context *three* different algebra structures `Algebra ?R (WeierstrassCurve.Affine.FunctionField
E)` are in scope (`?R = 𝕜`, `?R = RatFunc 𝕜`, `?R = N`), and nothing in the surrounding
expression determines the coefficient ring of the polynomial, so as written Lean refuses to
elaborate the statement at all (`typeclass instance problem is stuck: Semiring ?m`).  Since the
*value* `Polynomial.aeval x (Polynomial.X ^ 3 + Polynomial.X) = x ^ 3 + x` does not depend on
the coefficient ring, the mathematical content of `hH1` is the same whichever ring is chosen.
We therefore make the elaboration determinate by declaring `ℤ` as a `default_instance` for
`Semiring` (see `instDefaultSemiringInt` below); Lean then instantiates the polynomial over
`ℤ`, for which `Algebra ℤ (FunctionField E)` is available, and the statement elaborates
verbatim, with no annotation added.
-/

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV5

/-- A `Semiring` `default_instance` (Mathlib provides no `Semiring` `default_instance`).

It fires only when Lean is asked to solve a goal `Semiring ?m` whose argument is still a
metavariable — precisely the coefficient-ring ambiguity of `Polynomial.X ^ 3 + Polynomial.X`
in `base_preserved_AS` — and resolves it to `ℤ`.  Every determined `Semiring` goal is left
untouched.  Nothing mathematical depends on the choice, since for `x : FunctionField E` the
value `aeval x (X ^ 3 + X)` is `x ^ 3 + x` for the coefficient ring `ℤ` exactly as for `𝕜`,
`𝕜(t)` or `N`. -/
@[default_instance]
instance instDefaultSemiringInt : Semiring ℤ := inferInstance

/-- **The bridge gives the Hurwitz-`AS` hypothesis.**  Let `ι : F →+* N(E)` be a ring map
compatible with the constants `𝕜`, and let `F` satisfy the Artin–Schreier bridge condition
`ASUnramified` at the poles of `t = algebraMap 𝕜(t) F X`.  Then the point `r = ι t` of `N(E)`
satisfies the hypothesis of `hurwitz_AS` for the polynomial `X ^ 3 + X`: at every valuation of
`N(E)` trivial on `N` at which `r` has a pole, the Artin–Schreier function `r³ + r` is
congruent to a value `u⁵ - u` modulo the valuation ring.

Indeed, for such a valuation `v` the composite `v ∘ ι` is a valuation of `F` trivial on `𝕜`,
and `ASUnramified` supplies the value `u ∈ F`, whose image in `N(E)` is the required `u`. -/
theorem asHyp_of_ASUnramified {𝕜 F N : Type*} [Field 𝕜] [Field F] [Field N] [CharP 𝕜 5]
    [Algebra 𝕜 F] [Algebra (RatFunc 𝕜) F] [IsScalarTower 𝕜 (RatFunc 𝕜) F]
    [Algebra 𝕜 N] [Algebra (RatFunc 𝕜) N] [IsScalarTower 𝕜 (RatFunc 𝕜) N]
    (E : WeierstrassCurve N) [E.IsElliptic]
    (ι : F →+* WeierstrassCurve.Affine.FunctionField E)
    (hι : ∀ c : 𝕜, ι (algebraMap 𝕜 F c) = algebraMap N _ (algebraMap 𝕜 N c))
    (hB : Work.MotV5.ASUnramified 𝕜 F (algebraMap (RatFunc 𝕜) F RatFunc.X)
      (algebraMap (RatFunc 𝕜) F (Work.MotV.fAS 𝕜))) :
    ∀ v : Valuation (WeierstrassCurve.Affine.FunctionField E) ℤᵐ⁰,
      Work.MotV.TrivOn N v → 1 < v (ι (algebraMap (RatFunc 𝕜) F RatFunc.X)) →
      ∃ u : WeierstrassCurve.Affine.FunctionField E,
        v (Polynomial.aeval (ι (algebraMap (RatFunc 𝕜) F RatFunc.X))
            (Polynomial.X ^ 3 + Polynomial.X : Polynomial ℤ) - (u ^ 5 - u)) ≤ 1 := by
  intro v hv h1
  -- `v ∘ ι` is a valuation of `F` which is trivial on the constants `𝕜`
  have htriv : Work.MotV.TrivOn 𝕜 (v.comap ι) := by
    intro c hc
    rw [Valuation.comap_apply, hι]
    exact hv _ (by simpa using hc)
  -- the bridge at `v ∘ ι`; its pole hypothesis is `1 < v (ι t) = (v ∘ ι) t`
  obtain ⟨u, hu⟩ := hB (v.comap ι) htriv h1
  refine ⟨ι u, ?_⟩
  -- `fAS = X ^ 3 + X`, so the two Artin–Schreier expressions agree
  have hgoal_eq : ι (algebraMap (RatFunc 𝕜) F (Work.MotV.fAS 𝕜) - (u ^ 5 - u))
      = Polynomial.aeval (ι (algebraMap (RatFunc 𝕜) F RatFunc.X))
          (Polynomial.X ^ 3 + Polynomial.X : Polynomial ℤ) - ((ι u) ^ 5 - ι u) := by
    simp [Work.MotV.fAS]
  simpa only [Valuation.comap_apply, hgoal_eq] using hu

/-- **An `𝕜`-algebra isomorphism that sends `X` into the base preserves the base.**  If
`θ : F₁ ≃ₐ[𝕜] F₂` sends the parameter `X = RatFunc.X` of `F₁` to the image of some
`d : 𝕜(t)` in `F₂`, then `θ` maps the whole image of `𝕜(t)` in `F₁` into the image of
`𝕜(t)` in `F₂`.

The map `g = θ ∘ algebraMap (𝕜(t)) F₁` is a `𝕜`-algebra map `𝕜(t) → F₂`; the image of `𝕜(t)`
in `F₂` is a subfield `S` (the field range of `algebraMap (𝕜(t)) F₂`), and the preimage of `S`
under `g` is an intermediate field of `𝕜(t)`.  Since `𝕜(t)` is generated over `𝕜` by `X`
(`RatFunc.adjoin_X`) and `g X ∈ S`, that preimage is everything. -/
theorem basePreserved_of_X {𝕜 F₁ F₂ : Type*} [Field 𝕜] [Field F₁] [Field F₂]
    [Algebra 𝕜 F₁] [Algebra 𝕜 F₂] [Algebra (RatFunc 𝕜) F₁] [Algebra (RatFunc 𝕜) F₂]
    [IsScalarTower 𝕜 (RatFunc 𝕜) F₁] [IsScalarTower 𝕜 (RatFunc 𝕜) F₂]
    (θ : F₁ ≃ₐ[𝕜] F₂) (d : RatFunc 𝕜)
    (hd : θ (algebraMap (RatFunc 𝕜) F₁ RatFunc.X) = algebraMap (RatFunc 𝕜) F₂ d) :
    ∀ c : RatFunc 𝕜, ∃ d', θ (algebraMap (RatFunc 𝕜) F₁ c) = algebraMap (RatFunc 𝕜) F₂ d' := by
  intro c
  let g : RatFunc 𝕜 →ₐ[𝕜] F₂ := θ.toAlgHom.comp (IsScalarTower.toAlgHom 𝕜 (RatFunc 𝕜) F₁)
  -- the image of `𝕜(t)` in `F₂`
  set S : IntermediateField 𝕜 F₂ := (IsScalarTower.toAlgHom 𝕜 (RatFunc 𝕜) F₂).fieldRange with hS
  -- `g X` lies in `S` by hypothesis
  have hX : g RatFunc.X ∈ S := by
    rw [hS, AlgHom.mem_fieldRange]
    exact ⟨d, by simpa [g] using hd.symm⟩
  -- `𝕜(t)` is generated over `𝕜` by `X`, so the preimage of `S` is everything
  have htop : S.comap g = ⊤ := by
    rw [eq_top_iff, ← RatFunc.adjoin_X]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro x rfl
    exact hX
  have hc : c ∈ S.comap g := by rw [htop]; trivial
  change g c ∈ S at hc
  rw [hS, AlgHom.mem_fieldRange] at hc
  obtain ⟨d', hd'⟩ := hc
  refine ⟨d', ?_⟩
  rw [IsScalarTower.toAlgHom_apply] at hd'
  rw [hd']
  simp [g]

theorem base_preserved_AS {𝕜 F₁ F₂ N : Type*} [Field 𝕜] [Field F₁] [Field F₂] [Field N]
    [CharP 𝕜 5] [IsAlgClosed N] [CharP N 5]
    [Algebra 𝕜 F₁] [Algebra 𝕜 F₂] [Algebra (RatFunc 𝕜) F₁] [Algebra (RatFunc 𝕜) F₂]
    [IsScalarTower 𝕜 (RatFunc 𝕜) F₁] [IsScalarTower 𝕜 (RatFunc 𝕜) F₂]
    [Algebra 𝕜 N] [Algebra (RatFunc 𝕜) N] [IsScalarTower 𝕜 (RatFunc 𝕜) N]
    [Algebra.IsAlgebraic (RatFunc 𝕜) N]
    (E : WeierstrassCurve N) [E.IsElliptic]
    (hH1 : ∀ r : WeierstrassCurve.Affine.FunctionField E,
      (∀ v : Valuation (WeierstrassCurve.Affine.FunctionField E) (WithZero (Multiplicative ℤ)),
        Work.MotV.TrivOn N v → 1 < v r →
        ∃ u, v (Polynomial.aeval r (Polynomial.X ^ 3 + Polynomial.X) - (u ^ 5 - u)) ≤ 1) →
      ∃ c : N, algebraMap N _ c = r)
    (ι₁ : F₁ →+* WeierstrassCurve.Affine.FunctionField E)
    (ι₂ : F₂ →+* WeierstrassCurve.Affine.FunctionField E)
    (hι₁ : ∀ c : RatFunc 𝕜,
      ι₁ (algebraMap (RatFunc 𝕜) F₁ c) = algebraMap N _ (algebraMap (RatFunc 𝕜) N c))
    (hι₂ : ∀ c : RatFunc 𝕜,
      ι₂ (algebraMap (RatFunc 𝕜) F₂ c) = algebraMap N _ (algebraMap (RatFunc 𝕜) N c))
    (hB₁ : Work.MotV5.ASUnramified 𝕜 F₁ (algebraMap (RatFunc 𝕜) F₁ RatFunc.X)
      (algebraMap (RatFunc 𝕜) F₁ (Work.MotV.fAS 𝕜)))
    (hB₂ : Work.MotV5.ASUnramified 𝕜 F₂ (algebraMap (RatFunc 𝕜) F₂ RatFunc.X)
      (algebraMap (RatFunc 𝕜) F₂ (Work.MotV.fAS 𝕜)))
    (hR₁ : ∀ r : F₁, IsAlgebraic (RatFunc 𝕜) r → ∃ c, algebraMap (RatFunc 𝕜) F₁ c = r)
    (hR₂ : ∀ r : F₂, IsAlgebraic (RatFunc 𝕜) r → ∃ c, algebraMap (RatFunc 𝕜) F₂ c = r)
    (θ : F₁ ≃ₐ[𝕜] F₂) :
    ∀ c : RatFunc 𝕜, ∃ d, θ (algebraMap (RatFunc 𝕜) F₁ c) = algebraMap (RatFunc 𝕜) F₂ d := by
  intro c
  -- the composite `ι₂ ∘ θ : F₁ → N(E)` is compatible with the constants `𝕜`
  have hι' : ∀ c : 𝕜, ι₂ (θ (algebraMap 𝕜 F₁ c)) = algebraMap N _ (algebraMap 𝕜 N c) := by
    intro c
    rw [AlgEquiv.commutes θ c, IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) F₂, hι₂,
      ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) N]
  -- steps 1 + 2: `hurwitz_AS` puts `r = ι₂ (θ t)` into the constants
  obtain ⟨c₀, hc₀⟩ := hH1 (ι₂ (θ (algebraMap (RatFunc 𝕜) F₁ RatFunc.X)))
    (asHyp_of_ASUnramified E (ι₂.comp (θ : F₁ →+* F₂)) hι' hB₁)
  -- `r` is therefore algebraic over `𝕜(t)`
  have halgN : IsAlgebraic (RatFunc 𝕜)
      (algebraMap N (WeierstrassCurve.Affine.FunctionField E) c₀) :=
    (Algebra.IsAlgebraic.isAlgebraic c₀).algebraMap
  have halgr : IsAlgebraic (RatFunc 𝕜) (ι₂ (θ (algebraMap (RatFunc 𝕜) F₁ RatFunc.X))) := by
    rw [← hc₀]; exact halgN
  -- and by injectivity of `ι₂` so is `θ t`
  have halgθ : IsAlgebraic (RatFunc 𝕜) (θ (algebraMap (RatFunc 𝕜) F₁ RatFunc.X)) :=
    IsAlgebraic.of_ringHom_of_comp_eq (R := RatFunc 𝕜) (S := RatFunc 𝕜)
      (A := F₂) (B := WeierstrassCurve.Affine.FunctionField E)
      (f := RingHom.id (RatFunc 𝕜)) (g := ι₂) halgr Function.surjective_id
      (fun a b h => ι₂.injective h) (by ext x; exact (hι₂ x).symm)
  -- step 3: regularity of `F₂` makes `θ t ∈ 𝕜(t)`
  obtain ⟨d, hd⟩ := hR₂ _ halgθ
  -- step 4: an `𝕜`-algebra map sending `t` into the base preserves the base
  exact basePreserved_of_X θ d hd.symm c

end Work.MotV5
