import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BSLit.Wielandt

/-- **Dimension of the range of `x ↦ a • e x` under an intertwining isomorphism.**

Let `k` be a field, `R` a `k`-algebra, `P` a `k`- and `R`-module with compatible actions
(`IsScalarTower k R P`, `SMulCommClass R k P`), `e : P →ₗ[R] P` an `R`-linear endomorphism, and
`A : N →ₗ[k] N` a `k`-linear endomorphism of `N`.  If `φ : ↥(range e) ≃ₗ[k] N` intertwines the
`R`-action by `a ∈ R` on `range e` with `A`, i.e. `φ (a • x) = A (φ x)` for all `x ∈ range e`, then
the rank over `k` of `x ↦ a • e x` on `P` equals the rank over `k` of `A`.

Indeed `range ((lsmul k k P a) ∘ e) = a • (range e)`, and the `k`-linear monomorphism
`subk : ↥(range e) →ₗ[k] P` carries `range (a • ·)` (the `a`-scalar multiples inside `range e`)
onto it; so the two ranks agree with `finrank ↥(range (a • ·))`, which in turn is carried by `φ`
onto `finrank ↥(range A)`. -/
theorem RankRangeLsmulComp {k R P N : Type*} [Field k] [Semiring R] [Algebra k R]
    [AddCommMonoid P] [Module k P] [Module R P] [IsScalarTower k R P] [SMulCommClass R k P]
    [AddCommMonoid N] [Module k N] [Module.Finite k P]
    (a : R) (e : P →ₗ[R] P) (A : N →ₗ[k] N)
    (φ : ↥(LinearMap.range e) ≃ₗ[k] N)
    (hφ : ∀ x : ↥(LinearMap.range e), φ (a • x) = A (φ x)) :
    Module.finrank k ↥(LinearMap.range ((Algebra.lsmul k k P a) ∘ₗ (e.restrictScalars k))) =
      Module.finrank k ↥(LinearMap.range A) := by
  classical
  -- The "multiply by `a`" endomorphism of `↥(range e)`.
  let s : ↥(LinearMap.range e) →ₗ[k] ↥(LinearMap.range e) :=
    { toFun := fun x => ⟨a • (x : P), by
        obtain ⟨y, hy⟩ := x.2
        exact ⟨a • y, by rw [map_smul, hy]⟩⟩
      map_add' := by intro x y; ext; simp [smul_add]
      map_smul' := by intro c x; ext; exact smul_comm a c (x : P) }
  have hs_apply : ∀ x : ↥(LinearMap.range e), s x = a • x := fun x => Subtype.ext rfl
  -- The `k`-linear inclusion of `↥(range e)` into `P`.
  let subk : ↥(LinearMap.range e) →ₗ[k] P :=
    { toFun := fun x => (x : P)
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hsubk_inj : Function.Injective subk := fun x y h => Subtype.ext h
  -- `φ` intertwines `s` with `A`.
  have hcomp : φ.toLinearMap ∘ₗ s = A ∘ₗ φ.toLinearMap := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs_apply x]
    exact hφ x
  -- Therefore `finrank ↥(range s) = finrank ↥(range A)`.
  have h1 : Module.finrank k ↥(LinearMap.range (φ.toLinearMap ∘ₗ s)) =
      Module.finrank k ↥(LinearMap.range s) := by
    rw [LinearMap.range_comp]
    exact (LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective φ.toLinearMap φ.injective (LinearMap.range s))).symm
  have h2 : Module.finrank k ↥(LinearMap.range (A ∘ₗ φ.toLinearMap)) =
      Module.finrank k ↥(LinearMap.range A) := by
    rw [LinearMap.range_comp, (LinearMap.range_eq_top).mpr φ.surjective, Submodule.map_top]
  have hAs : Module.finrank k ↥(LinearMap.range A) = Module.finrank k ↥(LinearMap.range s) := by
    rw [← h2, ← hcomp, h1]
  -- `subk` intertwines `s` with left multiplication by `a` on `P`.
  have hsub : subk ∘ₗ s = (Algebra.lsmul k k P a) ∘ₗ subk := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Algebra.lsmul_apply]
    rfl
  -- `range e` and `range subk` agree as `k`-submodules of `P`.
  have hrange : LinearMap.range (e.restrictScalars k) = LinearMap.range subk := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_range]
    constructor
    · rintro ⟨y₀, hy⟩
      exact ⟨⟨x, y₀, hy⟩, rfl⟩
    · rintro ⟨y₀, hy⟩
      obtain ⟨z, hz⟩ := y₀.2
      refine ⟨z, ?_⟩
      rw [LinearMap.restrictScalars_apply, hz]
      exact hy
  -- The two ranges are equal.
  have hge : LinearMap.range ((Algebra.lsmul k k P a) ∘ₗ (e.restrictScalars k)) =
      Submodule.map subk (LinearMap.range s) := by
    rw [LinearMap.range_comp, hrange,
      ← LinearMap.range_comp subk (Algebra.lsmul k k P a), ← hsub,
      ← LinearMap.range_comp s subk]
  have hfin_g : Module.finrank k
      ↥(LinearMap.range ((Algebra.lsmul k k P a) ∘ₗ (e.restrictScalars k))) =
      Module.finrank k ↥(LinearMap.range s) := by
    rw [hge]
    exact (LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective subk hsubk_inj (LinearMap.range s))).symm
  rw [hfin_g, hAs]

end Work.BSLit.Wielandt
