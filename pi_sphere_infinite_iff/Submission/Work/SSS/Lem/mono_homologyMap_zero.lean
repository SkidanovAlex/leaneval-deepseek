import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS.Lem

open CategoryTheory

/-- **H₀ of a chain map with `φ₀` mono and `φ₁` iso is mono.**

Let `φ : K ⟶ L` be a morphism of chain complexes of `ℤ`-modules indexed by `ℕ`
(so the only differential out of degree `0` is `K.d 1 0 : K.X 1 ⟶ K.X 0`, and
`H₀(K) = K.X 0 ⧸ im (K.d 1 0)`). If `φ.f 0` is a monomorphism and `φ.f 1` is an
isomorphism, then `H₀(φ) : H₀(K) ⟶ H₀(L)` is a monomorphism.

Proof (the standard diagram chase): `H₀(K) = K.X 0 ⧸ im (K.d 1 0) = coker (K.d 1 0)`
and `H₀(φ)` is induced by `φ.f 0`. Suppose `x ∈ K.X 0` is killed, i.e.
`φ.f 0 x = (L.d 1 0) y`. Since `φ.f 1` is an isomorphism, `y = φ.f 1 z`, hence by
naturality `φ.f 0 x = φ.f 0 ((K.d 1 0) z)`; since `φ.f 0` is mono, `x = (K.d 1 0) z`.

Formally we use the criterion `HomologicalComplex.mono_homologyMap_iff_up_to_refinements`,
which reduces the statement to exactly this chase "up to refinements" in any abelian
category, applied with `i = 1, j = 0, k = 0`. -/
theorem mono_homologyMap_zero {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L)
    (h₀ : CategoryTheory.Mono (φ.f 0)) (h₁ : CategoryTheory.IsIso (φ.f 1)) :
    CategoryTheory.Mono (HomologicalComplex.homologyMap φ 0) := by
  -- For `ComplexShape.down ℕ` we have `c.prev 0 = 1` and `c.next 0 = 0`, so the
  -- degree `0` short complex of a chain complex is `K.X 1 ⟶ K.X 0 ⟶ K.X 0`.
  rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements (φ := φ) (i := 1) (j := 0) (k := 0)
      (ComplexShape.prev_eq' (c := ComplexShape.down ℕ) (i := 0) (j := 1) (by rfl))
      (by apply ComplexShape.next_eq_self'; intro k hk; exact Nat.succ_ne_zero k hk)]
  -- `x₂` is a cycle in degree `0` (automatic, as `K.d 0 0 = 0`), and `y₁` is a
  -- refinement-lift of `φ.f 0 x₂` along `L.d 1 0`.
  intro A x₂ hx₂ y₁ hy
  -- Lift `y₁` along the epimorphism `φ.f 1`.
  obtain ⟨A', π, hπ, z, hz⟩ :=
    CategoryTheory.surjective_up_to_refinements_of_epi (φ.f 1) y₁
  refine ⟨A', π, hπ, z, ?_⟩
  -- It remains to see that `π x₂ = (K.d 1 0) z`, which follows from `φ.f 0` being
  -- mono together with the naturality of `φ`.
  refine (cancel_mono (φ.f 0)).1 ?_
  simp only [Category.assoc]
  rw [hy, ← Category.assoc, hz, Category.assoc, φ.comm 1 0]

end Work.SSS.Lem
