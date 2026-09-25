import Mathlib

set_option linter.style.haveILetI false

namespace Work.CFTLib.Character

/-- If `c ∉ H` and `c` has `p`-power order, then there is a nontrivial character
`A →* Multiplicative (ZMod p)` (i.e. a homomorphism to the additive group `ZMod p`)
which is trivial on `H`. -/
theorem charKilling {A : Type} [CommGroup A] [Finite A] (p : ℕ) [Fact p.Prime]
    {H : Subgroup A} {c : A} (hcH : c ∉ H) (hc : ∃ k : ℕ, c ^ (p ^ k) = 1) :
    ∃ χ : A →* Multiplicative (ZMod p), χ ≠ 1 ∧ ∀ h ∈ H, χ h = 1 := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := hc
  -- The class of `c` in `A ⧸ H` is nontrivial and has `p`-power order.
  have hq_ne : QuotientGroup.mk' H c ≠ 1 := by
    rw [QuotientGroup.mk'_apply]
    intro h
    exact hcH ((QuotientGroup.eq_one_iff c).mp h)
  have hq_pow : (QuotientGroup.mk' H c) ^ (p ^ k) = 1 := by
    rw [← map_pow, hk, map_one]
  have hord_dvd : orderOf (QuotientGroup.mk' H c) ∣ p ^ k :=
    orderOf_dvd_iff_pow_eq_one.mpr hq_pow
  have hord_ne : orderOf (QuotientGroup.mk' H c) ≠ 1 :=
    fun h => hq_ne ((orderOf_eq_one_iff).mp h)
  -- hence `p ∣ orderOf` and so `p ∣ |A ⧸ H|`.
  have hp_dvd_ord : p ∣ orderOf (QuotientGroup.mk' H c) := by
    obtain ⟨j, _hjle, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hord_dvd
    rw [hjeq]
    have hj : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hjeq
      exact hord_ne hjeq
    exact dvd_pow_self p hj
  have hpdvd_card : p ∣ Nat.card (A ⧸ H) :=
    dvd_trans hp_dvd_ord (orderOf_dvd_natCard _)
  -- Structure theorem for finite abelian groups.
  obtain ⟨ι, hι, n, _hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite (A ⧸ H)
  haveI := hι
  have hcard : Nat.card (A ⧸ H) = ∏ i, n i := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Nat.card_congr (Multiplicative.ofAdd (α := ZMod (n i))), Nat.card_zmod]
  have hpdvdprod : p ∣ ∏ i, n i := hcard ▸ hpdvd_card
  obtain ⟨i, hi⟩ : ∃ i, p ∣ n i := by
    have h := (Prime.dvd_finsetProd_iff (S := Finset.univ) (p := p) hp.prime
      (fun i => n i)).mp hpdvdprod
    obtain ⟨a, _, ha⟩ := h
    exact ⟨a, ha⟩
  -- Build a nontrivial character of the `i`-th cyclic factor.
  let ch : ZMod (n i) →+* ZMod p := ZMod.castHom hi (ZMod p)
  let φ : Multiplicative (ZMod (n i)) →* Multiplicative (ZMod p) :=
    AddMonoidHom.toMultiplicative ch.toAddMonoidHom
  let proj : ((j : ι) → Multiplicative (ZMod (n j))) →* Multiplicative (ZMod (n i)) :=
    Pi.evalMonoidHom (fun j => Multiplicative (ZMod (n j))) i
  let ψ : (A ⧸ H) →* Multiplicative (ZMod p) := φ.comp (proj.comp e.toMonoidHom)
  let z : Multiplicative (ZMod (n i)) := Multiplicative.ofAdd (1 : ZMod (n i))
  have hφz : φ z ≠ 1 := by
    have h1 : φ z = Multiplicative.ofAdd (1 : ZMod p) := by
      simp only [φ, z, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd]
      rw [show ch.toAddMonoidHom (1 : ZMod (n i)) = 1 from by
            change ch (1 : ZMod (n i)) = 1
            exact map_one ch]
    rw [h1]
    intro h
    exact one_ne_zero ((ofAdd_eq_one).mp h)
  let y : ((j : ι) → Multiplicative (ZMod (n j))) := Pi.mulSingle i z
  have hproj : proj y = z := by
    show (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (n j))) i)
        (Pi.mulSingle i z) = z
    rw [Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same]
  let g0 : A ⧸ H := e.symm y
  have hg0 : e.toMonoidHom g0 = y := by
    show e (e.symm y) = y
    exact e.apply_symm_apply y
  have hψg0 : ψ g0 ≠ 1 := by
    have hψ : ψ g0 = φ z := by
      show φ (proj (e (e.symm y))) = φ z
      rw [e.apply_symm_apply, hproj]
    rw [hψ]
    exact hφz
  obtain ⟨a0, ha0⟩ := QuotientGroup.mk'_surjective H g0
  let χ : A →* Multiplicative (ZMod p) := ψ.comp (QuotientGroup.mk' H)
  refine ⟨χ, ?_, ?_⟩
  · -- `χ` is nontrivial
    intro hχ
    have hχa : χ a0 = ψ g0 := by
      show ψ ((QuotientGroup.mk' H) a0) = ψ g0
      rw [ha0]
    rw [hχ] at hχa
    simp only [MonoidHom.one_apply] at hχa
    exact hψg0 hχa.symm
  · -- `χ` kills `H`
    intro h hh
    show ψ ((QuotientGroup.mk' H) h) = 1
    have hk1 : (QuotientGroup.mk' H) h = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff h).mpr hh
    rw [hk1, map_one]

end Work.CFTLib.Character
