import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The rank of a quotient by a sub-quotient (the "tower" formula for `Module.rank`)

For submodules `S ≤ T` of a module `M` over a ring `R` with the rank-nullity property, the
short exact sequence `0 → T/S → M/S → M/T → 0` gives

`rank (M ⧸ S) = rank (M ⧸ T) + rank (T ⧸ S|_T)`,

where `S|_T = comap T.subtype S`.  We prove this in `rank_quotient_subquotient` and then deduce
the "subquotient tower" statement used in the Riemann–Roch development, namely that for
submodules `S ≤ T ≤ A` of a `k`-vector space `P`

`rank (A ⧸ S|_A) = rank (A ⧸ T|_A) + rank (T ⧸ S|_T)`.

Note that this is *not* a formal consequence of the two rank-nullity identities for the pairs
`S ≤ A` and `T ≤ A` (cardinal addition does not cancel); one genuinely uses that the quotient
`A ⧸ S|_A` has `T|_A ⧸ S|_A` as a subspace with quotient `A ⧸ T|_A`.
-/

namespace Work.RiemannRoch.Aquot

universe u

open Submodule

/-- **Rank of a quotient by a sub-quotient.**  For submodules `S ≤ T` of a module `M` over a ring
`R` satisfying the rank-nullity theorem,
`rank (M ⧸ S) = rank (M ⧸ T) + rank (T ⧸ comap T.subtype S)`.

This is the rank form of the short exact sequence `0 → T/S → M/S → M/T → 0`. -/
lemma rank_quotient_subquotient {R : Type u} [Ring R] [HasRankNullity.{u} R] {M : Type u}
    [AddCommGroup M] [Module R M] {S T : Submodule R M} (hST : S ≤ T) :
    Module.rank R (M ⧸ S) = Module.rank R (M ⧸ T) + Module.rank R (T ⧸ comap T.subtype S) := by
  have h1 := Submodule.rank_quotient_add_rank (R := R) (M := M ⧸ S) (T.map S.mkQ)
  have h2 : Module.rank R ((M ⧸ S) ⧸ T.map S.mkQ) = Module.rank R (M ⧸ T) :=
    (Submodule.quotientQuotientEquivQuotient S T hST).rank_eq
  have h3 : Module.rank R (T.map S.mkQ) = Module.rank R (T ⧸ comap T.subtype S) := by
    have hker : LinearMap.ker (S.mkQ.comp T.subtype) = comap T.subtype S := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    have hrange : LinearMap.range (S.mkQ.comp T.subtype) = T.map S.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [← hker, ← hrange]
    exact (S.mkQ.comp T.subtype).quotKerEquivRange.rank_eq.symm
  rw [← h1, h2, h3]

/-- **Quotients by corresponding submodules have the same rank.**  If `e : M ≃ₗ[R] N` is a linear
equivalence and `p : Submodule R M`, then `rank (M ⧸ p) = rank (N ⧸ p.map e)`. -/
lemma rank_quotient_linearEquiv_map {R : Type u} [Ring R] [HasRankNullity.{u} R] {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (p : Submodule R M) :
    Module.rank R (M ⧸ p) = Module.rank R (N ⧸ p.map (e : M →ₗ[R] N)) := by
  haveI : Nontrivial R := nontrivial_of_hasRankNullity R
  let f : M ⧸ p →ₗ[R] N ⧸ p.map (e : M →ₗ[R] N) :=
    Submodule.mapQ p (p.map (e : M →ₗ[R] N)) (e : M →ₗ[R] N) (Submodule.le_comap_map _ p)
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    rw [Submodule.range_mapQ p (p.map (e : M →ₗ[R] N)) (e : M →ₗ[R] N) (Submodule.le_comap_map _ p),
      LinearMap.range_eq_top.mpr e.surjective, Submodule.map_top]
    simp
  have hker : LinearMap.ker f = ⊥ := by
    rw [Submodule.ker_mapQ p (p.map (e : M →ₗ[R] N)) (e : M →ₗ[R] N) (Submodule.le_comap_map _ p),
      Submodule.comap_map_eq_of_injective e.injective p, Submodule.mkQ_map_self]
  rw [LinearMap.rank_eq_of_surjective hsurj, hker, rank_bot, add_zero]

/-- **The tower formula for `Module.rank`.**  For submodules `S ≤ T ≤ A` of a `k`-vector space `P`,

`rank (A ⧸ S|_A) = rank (A ⧸ T|_A) + rank (T ⧸ S|_T)`

where `X|_Y = comap Y.subtype X`. -/
theorem rank_quotient_tower {k : Type u} [Field k] {P : Type u} [AddCommGroup P] [Module k P]
    (S T A : Submodule k P) (hST : S ≤ T) (hTA : T ≤ A) :
    Module.rank k (↥A ⧸ Submodule.comap A.subtype S) =
      Module.rank k (↥A ⧸ Submodule.comap A.subtype T) +
        Module.rank k (↥T ⧸ Submodule.comap T.subtype S) := by
  -- the restrictions of `S` and `T` to the submodule `A`
  let p : Submodule k ↥A := Submodule.comap A.subtype S
  let q : Submodule k ↥A := Submodule.comap A.subtype T
  have hpq : p ≤ q := Submodule.comap_mono hST
  have h1 : Module.rank k (↥A ⧸ p) =
      Module.rank k (↥A ⧸ q) + Module.rank k (↥q ⧸ Submodule.comap q.subtype p) :=
    rank_quotient_subquotient hpq
  -- the identification `T|_A ≃ T`, `x ↦ x`, of the restriction of `T` to `A` with `T`
  let e : ↥q ≃ₗ[k] ↥T :=
  { toFun := fun x => ⟨((x : ↥q) : ↥A), Submodule.mem_comap.mp x.2⟩
    invFun := fun y => ⟨⟨(y : P), hTA y.2⟩, Submodule.mem_comap.mpr (by simpa using y.2)⟩
    left_inv := fun x => by ext; rfl
    right_inv := fun y => by ext; rfl
    map_add' := fun x y => by ext; rfl
    map_smul' := fun c x => by ext; rfl }
  -- under `e`, the submodule `S|_A ⊆ T|_A` corresponds to `S|_T ⊆ T`
  have hmap : (p.submoduleOf q).map (e : ↥q →ₗ[k] ↥T) = Submodule.comap T.subtype S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Submodule.mem_comap.mpr (Submodule.mem_comap.mp hx)
    · intro hy
      refine ⟨⟨⟨(y : P), hTA y.2⟩, Submodule.mem_comap.mpr (by simpa using y.2)⟩, ?_, ?_⟩
      · exact Submodule.mem_comap.mpr (Submodule.mem_comap.mp hy)
      · ext; rfl
  have h2 : Module.rank k (↥q ⧸ Submodule.comap q.subtype p) =
      Module.rank k (↥T ⧸ Submodule.comap T.subtype S) := by
    have hb := rank_quotient_linearEquiv_map (R := k) e (p.submoduleOf q)
    rw [hmap] at hb
    exact hb
  rw [h1, h2]

end Work.RiemannRoch.Aquot
