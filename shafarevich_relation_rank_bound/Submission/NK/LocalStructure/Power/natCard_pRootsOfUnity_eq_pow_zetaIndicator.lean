import Mathlib
import Submission.NK.LocalStructure.Defs

/-!
# The order of `μ_p(κ)` is `p ^ δ`

For a field `κ` and a prime `p`, the `p`-torsion `pRootsOfUnity p κ = {ζ : κ | ζ ^ p = 1}`
of the multiplicative group is either trivial or of order `p`, according as `κ` contains a
primitive `p`-th root of unity or not.  With `δ = zetaIndicator p κ ∈ {0,1}` the indicator of
`ζ_p ∈ κ`, this reads `#μ_p(κ) = p ^ δ`.
-/

namespace NK.LocalStructure.Power

theorem natCard_pRootsOfUnity_eq_pow_zetaIndicator (p : ℕ) (κ : Type*)
    [Field κ] (hp : p.Prime) :
    Nat.card (NK.LocalStructure.pRootsOfUnity p κ) =
      p ^ NK.LocalInputs.zetaIndicator p κ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- The `p`-th roots of unity inside `κ` are the `p`-th roots of unity of the unit group.
  have hcard : Nat.card (NK.LocalStructure.pRootsOfUnity p κ)
      = Nat.card (rootsOfUnity p κ) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : NK.LocalStructure.pRootsOfUnity p κ =>
        rootsOfUnity.mkOfPowEq x.1 x.2) ⟨?_, ?_⟩)
    · intro a b hab
      exact Subtype.ext (by
        simpa using congrArg (fun u : rootsOfUnity p κ => ((u : κˣ) : κ)) hab)
    · intro u
      refine ⟨⟨((u : κˣ) : κ), ?_⟩, ?_⟩
      · exact (mem_rootsOfUnity' p (u : κˣ)).mp u.2
      · apply rootsOfUnity.coe_injective
        simp
  by_cases h : ∃ ζ : κ, IsPrimitiveRoot ζ p
  · -- If a primitive `p`-th root of unity exists, the group of `p`-th roots of unity has order `p`.
    rw [(NK.LocalInputs.zetaIndicator_eq_one_iff p κ).mpr h, pow_one, hcard]
    obtain ⟨ζ, hζ⟩ := h
    exact hζ.card_rootsOfUnity
  · -- Otherwise the only `p`-th root of unity is `1`.
    rw [(NK.LocalInputs.zetaIndicator_eq_zero_iff p κ).mpr h, pow_zero,
      Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, by simp⟩⟩⟩
    have key : ∀ x : κ, x ^ p = 1 → x = 1 := by
      intro x hx
      rcases hp.eq_one_or_self_of_dvd (orderOf x) (orderOf_dvd_iff_pow_eq_one.mpr hx) with
        h1 | h2
      · exact orderOf_eq_one_iff.mp h1
      · exact absurd ⟨x, IsPrimitiveRoot.iff_orderOf.mpr h2⟩ h
    rw [key a.1 a.2, key b.1 b.2]

end NK.LocalStructure.Power
