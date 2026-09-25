import Mathlib
import Submission.Work.QuadraticFields.RankTwo

/-!
# The `2`-rank of an elementary abelian `2`-group

`rankTwo A` is the `𝔽₂`-dimension of `A ⧸ A²` (see `Work.QuadraticFields.RankTwo`).  For a
elementary abelian `2`-group, i.e. a group of the shape `(ZMod 2)^ι`, every element is a square, so
the quotient is the group itself and the `2`-rank is the number of generators.

The elementary-abelian case is the extreme case of the genus-theory counting input: it is the one
in which the group of *independent quadratic characters* of `A` has full size.
-/

namespace Work.QuadraticFields

/-- For any `ZMod 2`-module `V`, multiplication by `2` is the zero endomorphism of `V`; hence the
quotient `ModN V 2` that computes `rankTwo (Multiplicative V)` is just `V` and the two `𝔽₂`-ranks
agree. -/
private lemma rankTwo_multiplicative_eq_finrank_of_zmod_two (V : Type*) [AddCommGroup V]
    [Module (ZMod 2) V] :
    rankTwo (Multiplicative V) = Module.finrank (ZMod 2) V := by
  -- The endomorphism "multiplication by `2`" of the `ℤ`-module `V` vanishes.
  have hrange : LinearMap.range (LinearMap.lsmul ℤ V 2) = ⊥ := by
    rw [LinearMap.range_eq_bot]
    ext x
    rw [LinearMap.lsmul_apply]
    -- `2 • x` is `((2 : ℤ) : ZMod 2) • x`, and `2 = 0` in `ZMod 2`.
    rw [← Int.cast_smul_eq_zsmul (ZMod 2) (2 : ℤ) x]
    rw [show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_smul]
    rfl
  -- The quotient map `V → ModN V 2` is bijective, so it is an isomorphism of `𝔽₂`-vector spaces.
  have e : V ≃ₗ[ZMod 2] ModN V 2 :=
    LinearEquiv.ofBijective (AddMonoidHom.toZModLinearMap 2 (ModN.mkQ (G := V) 2)) (by
      constructor
      · intro x y hxy
        have hxy' : ModN.mkQ (G := V) 2 x = ModN.mkQ (G := V) 2 y := hxy
        have h1 : ModN.mkQ (G := V) 2 (x - y) = 0 := by
          rw [map_sub, hxy', sub_self]
        have h2 : x - y ∈ LinearMap.range (LinearMap.lsmul ℤ V 2) := by
          rw [← Submodule.Quotient.mk_eq_zero (LinearMap.range (LinearMap.lsmul ℤ V 2))]
          simpa [ModN.mkQ, Submodule.mkQ_apply] using h1
        rw [hrange, Submodule.mem_bot] at h2
        exact sub_eq_zero.mp h2
      · intro y
        obtain ⟨x, hx⟩ :=
          Submodule.mkQ_surjective (LinearMap.range (LinearMap.lsmul ℤ V 2)) y
        exact ⟨x, by simpa [ModN.mkQ, Submodule.mkQ_apply] using hx⟩)
  calc rankTwo (Multiplicative V)
      = Module.finrank (ZMod 2) (ModN V 2) := rfl
    _ = Module.finrank (ZMod 2) V := (LinearEquiv.finrank_eq e).symm

theorem rankTwo_pi_zmod_two (ι : Type*) [Fintype ι] :
    rankTwo (Multiplicative (ι → ZMod 2)) = Fintype.card ι := by
  rw [rankTwo_multiplicative_eq_finrank_of_zmod_two]
  exact Module.finrank_fintype_fun_eq_card (ZMod 2)

end Work.QuadraticFields
