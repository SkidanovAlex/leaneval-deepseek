import Mathlib
import Submission.Work.ORLyndon.signedSum_regular
import Submission.Work.ORLyndon.base_regularity_transport_of_le

namespace Work.ORLyndon

/-- **Signed sums over a subgroup are regular.**  Let `H ≤ G`, let `χ : H →* Multiplicative ℤ`
be an additive character of the subgroup (equivalently a homomorphism `H → ℤ`), and let
`a = ∑ i ∈ s, ε i • of (g i) ∈ K[G]` be a signed sum whose terms `g i` all lie in `H` and whose
`χ`-degrees are `≤` the degree of `g i₀`, attained *uniquely* at `i₀` (with `ε i₀ ≠ 0`).  Then
`a` is a right non-zero-divisor: `b * a = 0` forces `b = 0`.

The argument is a reduction to the ambient-group statement `signedSum_regular`: the element
`a = E₀.map (H.subtype)` is the image of the analogous signed sum `E₀ ∈ K[H]`, which is right
regular in `K[H]` by `signedSum_regular` applied to `χ`.  Right regularity then transports from
`K[H]` to all of `K[G]` along the free `K[H]`-module structure of `K[G]`
(`base_regularity_transport_of_range` gives it for elements supported in `H`, and
`rightRegular_transport_subgroupAlgMap` removes that restriction). -/
theorem signedSum_regular_of_subgroup {G : Type*} [Group G] {K : Type*} [Field K]
    {ι : Type*} (s : Finset ι) (g : ι → G) (ε : ι → K) (H : Subgroup G)
    (hH : ∀ i, g i ∈ H) (χ : H →* Multiplicative ℤ) (i₀ : ι) (hi₀ : i₀ ∈ s) (hε : ε i₀ ≠ 0)
    (hle : ∀ i ∈ s, Multiplicative.toAdd (χ ⟨g i, hH i⟩) ≤
      Multiplicative.toAdd (χ ⟨g i₀, hH i₀⟩))
    (huniq : ∀ i ∈ s, Multiplicative.toAdd (χ ⟨g i, hH i⟩) =
      Multiplicative.toAdd (χ ⟨g i₀, hH i₀⟩) → i = i₀) :
    ∀ b : MonoidAlgebra K G,
      b * (∑ i ∈ s, ε i • MonoidAlgebra.of K G (g i)) = 0 → b = 0 := by
  classical
  set a : MonoidAlgebra K G := ∑ i ∈ s, ε i • MonoidAlgebra.of K G (g i) with ha
  set E₀ : MonoidAlgebra K H :=
    ∑ i ∈ s, ε i • MonoidAlgebra.of K H (⟨g i, hH i⟩ : H) with hE₀
  -- `E₀ ∈ K[H]` is right regular, by the ambient-group lemma applied to `χ` on `H`.
  have hreg : ∀ c : MonoidAlgebra K H, c * E₀ = 0 → c = 0 := by
    intro c hc
    rw [hE₀] at hc
    exact signedSum_regular (K := K) χ s (fun i => (⟨g i, hH i⟩ : H)) ε i₀ hi₀ hε hle huniq c hc
  -- `a` is the image of `E₀` under the algebra map `K[H] → K[G]`.
  have hmap : MonoidAlgebra.mapDomainRingHom K (Subgroup.subtype H) E₀ = a := by
    rw [hE₀, ha]
    simp
  -- Regularity for elements of `K[G]` whose support is contained in `H`.
  have hbase : ∀ c : MonoidAlgebra K G, (∀ x ∈ c.coeff.support, x ∈ H) → c * a = 0 → c = 0 := by
    intro c hc hca
    refine base_regularity_transport_of_range (Subgroup.subtype H) (Subgroup.subtype_injective H)
      E₀ hreg c ?_ ?_
    · intro x hx
      rw [Subgroup.range_subtype]
      exact hc x hx
    · rwa [hmap]
  -- The support of `a` is contained in `H`.
  have hsupp : ↑a.coeff.support ⊆ (H : Set G) := by
    rw [← hmap]
    intro x hx
    have hcoe : (MonoidAlgebra.mapDomainRingHom K (Subgroup.subtype H) E₀).coeff
        = Finsupp.mapDomain (⇑(Subgroup.subtype H)) E₀.coeff := by
      rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain]
    have hxne : (Finsupp.mapDomain (⇑(Subgroup.subtype H)) E₀.coeff) x ≠ 0 := by
      rw [← hcoe]
      exact Finsupp.mem_support_iff.mp hx
    obtain ⟨y, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hxne
    exact y.2
  intro b hb
  exact rightRegular_transport_subgroupAlgMap H a hsupp hbase b (by rw [ha]; exact hb)

end Work.ORLyndon
