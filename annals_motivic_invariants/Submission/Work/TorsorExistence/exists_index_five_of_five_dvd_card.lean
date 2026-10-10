import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.TorsorExistence

/-- A finite abelian group whose order is divisible by `5` has a subgroup of index `5`.

Proof: by the structure theorem for finite abelian groups, `G` is isomorphic to a product of
`Multiplicative (ZMod (n i))`; since `5` divides the product of the `n i`, some `n i` is divisible
by `5`. Projecting onto that coordinate and reducing `ZMod (n i) → ZMod 5` gives a surjective
homomorphism `G →* Multiplicative (ZMod 5)`; its kernel has index `5`. -/
theorem exists_index_five_of_five_dvd_card {G : Type*} [CommGroup G] [Finite G]
    (h : 5 ∣ Nat.card G) : ∃ H : Subgroup G, H.index = 5 := by
  classical
  obtain ⟨ι, instι, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  have hcard : Nat.card G = ∏ i, n i := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    exact Finset.prod_congr rfl fun a _ => by
      rw [← Nat.card_congr (Multiplicative.ofAdd : ZMod (n a) ≃ Multiplicative (ZMod (n a))),
        Nat.card_zmod]
  have h5 : 5 ∣ ∏ i, n i := hcard ▸ h
  obtain ⟨i, -, hi⟩ :=
    (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp (by norm_num : Nat.Prime 5)) n).mp h5
  let red : Multiplicative (ZMod (n i)) →* Multiplicative (ZMod 5) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom hi (ZMod 5))
  let proj : ((j : ι) → Multiplicative (ZMod (n j))) →* Multiplicative (ZMod (n i)) :=
    Pi.evalMonoidHom (fun j => Multiplicative (ZMod (n j))) i
  let φ : G →* Multiplicative (ZMod 5) := (red.comp proj).comp e.toMonoidHom
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨b, hb⟩ := ZMod.castHom_surjective hi (Multiplicative.toAdd y)
    refine ⟨e.symm (Function.update 1 i (Multiplicative.ofAdd b)), ?_⟩
    simp only [φ, MonoidHom.comp_apply, proj, Pi.evalMonoidHom_apply, red,
      MulEquiv.toMonoidHom_eq_coe]
    simp [hb]
  refine ⟨φ.ker, ?_⟩
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  simp [Nat.card_eq_fintype_card]

end Work.TorsorExistence
