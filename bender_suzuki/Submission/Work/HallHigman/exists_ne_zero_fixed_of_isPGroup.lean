import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.HallHigman

/-- A `p`-group acting on a nontrivial finite module over `ZMod p` has a nonzero fixed vector.

The proof is the classical orbit-counting argument: the additive group of `V` is a finite
`F_p`-vector space, hence has cardinality divisible by `p`; the orbits of `P` on `V` have size
a power of `p`, so the number of fixed points is congruent to `Nat.card V` modulo `p`, and
since `0` is fixed there is a second, nonzero fixed point. -/
lemma exists_ne_zero_fixed_of_isPGroup {p : ℕ} [Fact p.Prime] {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (ρ : Representation (ZMod p) G V)
    {P : Subgroup G} (hP : IsPGroup p P) (hV : Nontrivial V) :
    ∃ v : V, v ≠ 0 ∧ ∀ g ∈ P, ρ g v = v := by
  -- Turn the restriction of `ρ` to `P` into a multiplicative action of `P` on `V`.
  letI : MulAction P V := MulAction.compHom V (ρ.comp P.subtype)
  -- `V` is a finite-dimensional `F_p`-vector space, so its cardinality is a power of `p`.
  have hpV : p ∣ Nat.card V := by
    haveI : Fintype V := Fintype.ofFinite V
    haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
    have hfin : 0 < Module.finrank (ZMod p) V := Module.finrank_pos
    have hcard : Fintype.card V = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) V :=
      Module.card_eq_pow_finrank
    have hZ : Fintype.card (ZMod p) = p := ZMod.card p
    rw [Nat.card_eq_fintype_card, hcard, hZ]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hfin)
  -- The zero vector is fixed.
  have hfix : (0 : V) ∈ MulAction.fixedPoints P V := by
    rw [MulAction.mem_fixedPoints]
    intro g
    rw [MulAction.compHom_smul_def]
    simp
  -- Since `p ∣ Nat.card V` and `0` is fixed, there is a *different* fixed point.
  obtain ⟨b, hb, hb0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hpV hfix
  refine ⟨b, fun h => hb0 h.symm, ?_⟩
  intro g hg
  have := (MulAction.mem_fixedPoints.mp hb) ⟨g, hg⟩
  rw [MulAction.compHom_smul_def] at this
  simpa using this

end Work.HallHigman
