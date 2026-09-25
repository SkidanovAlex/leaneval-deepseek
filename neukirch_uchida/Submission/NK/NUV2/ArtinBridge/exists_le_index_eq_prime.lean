import Mathlib
import Submission.NK.GlobalCFTdeep.exists_normal_subgroup_index_eq_prime_of_solvable

set_option linter.style.haveILetI false

namespace NK.NUV2.ArtinBridge

/-- `Multiplicative α` is a type synonym for `α`, hence has the same cardinality. -/
private lemma natCard_multiplicative (X : Type*) : Nat.card (Multiplicative X) = Nat.card X :=
  Nat.card_congr (Equiv.refl X : X ≃ Multiplicative X)

/-- **Index-`p` subgroups.** A finite-index subgroup of a commutative group whose index is
divisible by the prime `p` is contained in a subgroup of index exactly `p`.

Working in the finite commutative quotient `G ⧸ N`, the structure theorem for finite abelian
groups writes it as a product of cyclic groups `∏ᵢ ℤ/nᵢ`; the divisibility `p ∣ ∏ᵢ nᵢ` produces a
coordinate `i` with `p ∣ nᵢ`, and reducing that coordinate modulo `p` gives a surjection
`G ⧸ N →* Multiplicative (ℤ/p)`. Its kernel pulled back to `G` is the required `V`. -/
theorem exists_le_index_eq_prime {G : Type} [CommGroup G] (N : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hN : N.FiniteIndex) (hdiv : p ∣ N.index) :
    ∃ V : Subgroup G, N ≤ V ∧ V.index = p := by
  classical
  haveI hNfi : N.FiniteIndex := hN
  haveI hQfin : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  -- decompose the quotient by the structure theorem for finite abelian groups
  obtain ⟨ι, hι, nn, hnn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite (G ⧸ N)
  letI : Fintype ι := hι
  have hcard : Nat.card (G ⧸ N) = ∏ i, nn i := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    exact Finset.prod_congr rfl (fun i _ => by
      rw [natCard_multiplicative, Nat.card_zmod])
  have hprod : p ∣ ∏ i, nn i := by rw [← hcard]; exact hdiv
  -- a prime dividing the product divides one factor
  obtain ⟨i₀, hi₀⟩ : ∃ i, p ∣ nn i := by
    have h' : p ∣ Finset.univ.prod nn := hprod
    obtain ⟨i, -, hi⟩ :=
      (Prime.dvd_finsetProd_iff (S := Finset.univ) (Nat.prime_iff.mp Fact.out) nn).mp h'
    exact ⟨i, hi⟩
  -- reduce the `i₀`-th coordinate modulo `p`
  let c : Multiplicative (ZMod (nn i₀)) →* Multiplicative (ZMod p) :=
    AddMonoidHom.toMultiplicative ((ZMod.castHom hi₀ (ZMod p)).toAddMonoidHom)
  let π : ((i : ι) → Multiplicative (ZMod (nn i))) →* Multiplicative (ZMod (nn i₀)) :=
    Pi.evalMonoidHom (fun i => Multiplicative (ZMod (nn i))) i₀
  let φ : (G ⧸ N) →* Multiplicative (ZMod p) := c.comp (π.comp e.toMonoidHom)
  have hc : Function.Surjective c := by simpa [c] using ZMod.castHom_surjective hi₀
  have hπ : Function.Surjective π := by
    intro y
    exact ⟨Function.update 1 i₀ y, by simp [π, Pi.evalMonoidHom]⟩
  have he : Function.Surjective (⇑e.toMonoidHom) := fun y => by
    obtain ⟨x, hx⟩ := e.surjective y
    exact ⟨x, hx⟩
  have hφ : Function.Surjective φ := by
    have h := (hc.comp hπ).comp he
    simpa only [φ, MonoidHom.coe_comp, Function.comp_assoc] using h
  let ψ : G →* Multiplicative (ZMod p) := φ.comp (QuotientGroup.mk' N)
  refine ⟨ψ.ker, ?_, ?_⟩
  · intro x hx
    have h1 : (QuotientGroup.mk' N) x = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hx
    show φ ((QuotientGroup.mk' N) x) = 1
    rw [h1, map_one]
  · rw [Subgroup.index_ker ψ]
    have htop : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr (by
      have h := hφ.comp (QuotientGroup.mk'_surjective N)
      simpa only [ψ, MonoidHom.coe_comp] using h)
    rw [htop, Subgroup.card_top, natCard_multiplicative, Nat.card_zmod]

end NK.NUV2.ArtinBridge
