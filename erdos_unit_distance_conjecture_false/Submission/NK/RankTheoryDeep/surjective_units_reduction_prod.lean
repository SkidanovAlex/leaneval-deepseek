import Mathlib

namespace NK.RankTheoryDeep

/-- **Chinese remainder theorem for units of `ZMod`.**

If the family `m : ι → ℕ` is pairwise coprime, the canonical reduction
`ZMod (∏ i, m i) → ∀ i, ZMod (m i)` is a ring equivalence
(`ZMod.prodEquivPi`), so it induces a bijection on units, and transporting along the
monoid equivalence "units of a product are the product of the units" gives that the
componentwise reduction is surjective. -/
theorem surjective_units_reduction_prod {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : ∀ i, m i ≠ 0) (hcop : Pairwise fun i j => Nat.Coprime (m i) (m j)) :
    Function.Surjective fun u : (ZMod (∏ i, m i))ˣ =>
      fun i => Units.map (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (ZMod (m i))).toMonoidHom u := by
  have _ := hm
  intro v
  -- The Chinese remainder theorem, as a ring equivalence.
  have hsurj : Function.Surjective (Units.map (ZMod.prodEquivPi m hcop).toMonoidHom) :=
    (Units.map_bijective (ZMod.prodEquivPi m hcop).bijective).surjective
  -- `MulEquiv.piUnits` identifies units of the product ring with the product of the units,
  -- so the goal function is the composite of two surjections.
  obtain ⟨w, hw⟩ := hsurj (MulEquiv.piUnits.symm v)
  refine ⟨w, ?_⟩
  have h1 : MulEquiv.piUnits (Units.map (ZMod.prodEquivPi m hcop).toMonoidHom w) = v := by
    rw [hw, MulEquiv.apply_symm_apply]
  funext i
  rw [← congrArg (fun f : (i : ι) → (ZMod (m i))ˣ => f i) h1]
  apply Units.ext
  show (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (ZMod (m i))) (w : ZMod (∏ i, m i))
      = (ZMod.prodEquivPi m hcop) (w : ZMod (∏ i, m i)) i
  exact (ZMod.prodEquivPi_apply m hcop (w : ZMod (∏ i, m i)) i).symm

end NK.RankTheoryDeep
