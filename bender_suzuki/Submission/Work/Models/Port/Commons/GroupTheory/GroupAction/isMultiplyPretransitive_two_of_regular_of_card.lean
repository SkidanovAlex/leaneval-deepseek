import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.GroupAction

open MulAction

/-- Let `G` act transitively on a finite set `Ω` with `1 < |Ω|`. If `U ≤ stabilizer G α`
acts *freely* off the fixed point `α` (every `u ≠ 1` fixes only `α`) and `|Ω| = |U| + 1`,
then `G` is `2`-transitive on `Ω`.

Indeed, `|Ω \ {α}| = |U|` and `U` acts freely on `Ω \ {α}`, so the orbit map
`u ↦ u • x` is a bijection `U → Ω \ {α}` for every `x ≠ α`: the action of `U` on the
complement of `α` is *regular*, hence transitive.  Consequently `stabilizer G α` is
`1`-transitive on `SubMulAction.ofStabilizer G α`, and Wielandt's theorem
(`SubMulAction.ofStabilizer.isMultiplyPretransitive`) upgrades this to `2`-transitivity
of `G` on `Ω`. -/
theorem isMultiplyPretransitive_two_of_regular_of_card {G Ω : Type*} [Group G] [Finite G]
    [MulAction G Ω] [Finite Ω] (htrans : MulAction.IsPretransitive G Ω) (hne : 1 < Nat.card Ω)
    (α : Ω) {U : Subgroup G} (hU : U ≤ MulAction.stabilizer G α)
    (hreg : ∀ u : U, u ≠ 1 → ∀ x : Ω, (u : G) • x = x → x = α)
    (hcard : Nat.card Ω = Nat.card U + 1) : MulAction.IsMultiplyPretransitive G Ω 2 := by
  classical
  -- Every element of `U` fixes `α` because `U ≤ stabilizer G α`.
  have hfixα : ∀ u : U, (u : G) • α = α := fun u =>
    MulAction.mem_stabilizer_iff.mp (hU u.prop)
  -- `stabilizer G α` acts (pre)transitively on the complement of `α`.
  have key : ∀ x : SubMulAction.ofStabilizer G α,
      ∀ y : SubMulAction.ofStabilizer G α,
      ∃ g : MulAction.stabilizer G α, g • x = y := by
    intro x y
    -- The orbit map `u ↦ u • x`, landing in the complement of `α`.
    let φ : U → SubMulAction.ofStabilizer G α := fun u =>
      ⟨(u : G) • (x : Ω), by
        rw [SubMulAction.mem_ofStabilizer_iff]
        intro h
        have hh : (u : G) • (x : Ω) = (u : G) • α := by rw [h, hfixα u]
        exact x.prop ((smul_left_cancel_iff (u : G)).mp hh)⟩
    -- `φ` is injective: freeness of the action of `U` off `α`.
    have hφinj : Function.Injective φ := by
      intro u v huv
      have huv' : (u : G) • (x : Ω) = (v : G) • (x : Ω) := congrArg Subtype.val huv
      have hw : ((v⁻¹ * u : U) : G) • (x : Ω) = (x : Ω) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, huv', inv_smul_smul]
      have h1 : (v⁻¹ * u : U) = 1 := by
        by_contra h
        exact x.prop (hreg (v⁻¹ * u) h (x : Ω) hw)
      have : u = v := by
        have h4 := congrArg (fun z : U => v * z) h1
        simpa [mul_inv_cancel_left] using h4
      exact this
    -- `|U| = |Ω \ {α}|`.
    have hcard' : Nat.card U = Nat.card (SubMulAction.ofStabilizer G α) := by
      have h2 := SubMulAction.nat_card_ofStabilizer_add_one_eq (G := G) (a := α)
      omega
    -- A bijection by cardinality, in particular surjective.
    have hφsurj : Function.Surjective φ :=
      ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hφinj, hcard'⟩).2
    obtain ⟨u, hu⟩ := hφsurj y
    refine ⟨⟨(u : G), hU u.prop⟩, ?_⟩
    have hsmul : (⟨(u : G), hU u.prop⟩ : MulAction.stabilizer G α) • x = φ u := by
      apply Subtype.ext
      rw [SetLike.val_smul]
      rfl
    rw [hsmul, hu]
  have hpre : MulAction.IsPretransitive (MulAction.stabilizer G α)
      (SubMulAction.ofStabilizer G α) := ⟨key⟩
  have h1 : MulAction.IsMultiplyPretransitive (MulAction.stabilizer G α)
      (SubMulAction.ofStabilizer G α) 1 := MulAction.is_one_pretransitive_iff.mpr hpre
  haveI : MulAction.IsPretransitive G Ω := htrans
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive (n := 1) (a := α)).mpr h1

end Commons.GroupTheory.GroupAction