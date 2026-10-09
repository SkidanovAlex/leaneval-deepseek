import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Uniqueness of order embeddings of an ordered field into `ℝ`

Let `F` be a field equipped with a linear order making it a strict ordered ring (so `F` is an
ordered field), and let `ρ κ : F →+*o ℝ` be order-preserving (unital) ring homomorphisms.  Then
`ρ = κ`.

The reason is that such a map is automatically strictly monotone (it is monotone by definition
and injective because `F` is a field while `ℝ` is a domain), hence it reflects `<`.  Writing
`q = (r : F)` for the image of a rational `r`, a ring homomorphism sends `q` to `(r : ℝ)`.
If `ρ x ≠ κ x`, pick a rational `r` strictly between `ρ x` and `κ x` in `ℝ` (density of `ℚ` in
`ℝ`); then `ρ x < ρ q` forces `x < q` while `κ q < κ x` forces `q < x`, a contradiction.
-/

namespace Work.SSGRoute.ZDataTwo

/-- Two order-preserving ring homomorphisms from an ordered field into `ℝ` coincide. -/
theorem orderEmbedding_ext {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (ρ κ : F →+*o ℝ) : ρ = κ := by
  -- A ring homomorphism from a field is injective, so a monotone one is strictly monotone.
  have hρ : StrictMono ρ :=
    ρ.monotone'.strictMono_of_injective (RingHom.injective (ρ : F →+* ℝ))
  have hκ : StrictMono κ :=
    κ.monotone'.strictMono_of_injective (RingHom.injective (κ : F →+* ℝ))
  ext x
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hlt
  · -- Case `ρ x < κ x`: a rational strictly in between gives `x < q < x`.
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
    have hqρ : ρ (r : F) = (r : ℝ) := map_ratCast ρ r
    have hqκ : κ (r : F) = (r : ℝ) := map_ratCast κ r
    have hxq : x < (r : F) := hρ.lt_iff_lt.mp (hqρ ▸ hr1)
    have hqx : (r : F) < x := hκ.lt_iff_lt.mp (hqκ ▸ hr2)
    exact absurd hxq (not_lt.mpr hqx.le)
  · -- Case `κ x < ρ x`: symmetric, with the roles of `ρ` and `κ` exchanged.
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
    have hqρ : ρ (r : F) = (r : ℝ) := map_ratCast ρ r
    have hqκ : κ (r : F) = (r : ℝ) := map_ratCast κ r
    have hxq : x < (r : F) := hκ.lt_iff_lt.mp (hqκ ▸ hr1)
    have hqx : (r : F) < x := hρ.lt_iff_lt.mp (hqρ ▸ hr2)
    exact absurd hxq (not_lt.mpr hqx.le)

end Work.SSGRoute.ZDataTwo
