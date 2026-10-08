import Mathlib
import Submission.Work.NPC.Fpf.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Sylow plumbing for the fixed-point-free nilpotency theorem (A8b, part 2)

Three elementary lemmas used in the induction proving "a finite solvable group with a
fixed-point-free automorphism of prime order is nilpotent" (`Work.Frobenius.Fpf.isNilpotent_of_fpf_prime`).
They concern a Sylow subgroup `R` of a finite group `K`, a normal subgroup `N ⊴ K`, and the passage
between `K` and the quotient `K ⧸ N`.

* `normal_sup_of_map_normal`: if the image of the Sylow `R` in `K ⧸ N` is normal there, then
  `R ⊔ N ⊴ K` (image of a normal subgroup under `comap`, plus `comap (map f H) = H ⊔ ker f`).
* `normal_of_sylow_of_normal_subgroupOf`: a Sylow subgroup which is normal in a normal subgroup
  containing it is normal in the whole group (normality in `S` makes it *characteristic* in `S`
  by Sylow uniqueness, and `S ⊴ K`).
* `coprime_card_of_isPGroup_of_ne`: two subgroups of coprime prime-power orders (distinct primes)
  have coprime orders.
-/

universe u

namespace Work.Frobenius.Fpf

open Work.NPC.Fpf

variable {K : Type*} [Group K]

/-- If the image of `R : Sylow r K` in `K ⧸ N` is normal, then `R ⊔ N` is normal in `K`. -/
theorem normal_sup_of_map_normal [Finite K] {N : Subgroup K} [N.Normal] {r : ℕ} [Fact r.Prime]
    (R : Sylow r K)
    (h : ((Sylow.mapSurjective (QuotientGroup.mk'_surjective N) R : Sylow r (K ⧸ N)) :
      Subgroup (K ⧸ N)).Normal) :
    ((R : Subgroup K) ⊔ N).Normal := by
  rw [Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective N) R] at h
  have h2 : (Subgroup.comap (QuotientGroup.mk' N)
      (Subgroup.map (QuotientGroup.mk' N) ((R : Subgroup K)))).Normal := h.comap _
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2

/-- A Sylow subgroup `R` that is normal in a normal subgroup `S ⊴ K` containing it is normal in
`K`. -/
theorem normal_of_sylow_of_normal_subgroupOf [Finite K] {r : ℕ} [Fact r.Prime] (R : Sylow r K)
    {S : Subgroup K} (hS : S.Normal) (hRS : (R : Subgroup K) ≤ S)
    (hRn : ((R : Subgroup K).subgroupOf S).Normal) : (R : Subgroup K).Normal := by
  haveI : S.Normal := hS
  have hRn' : (R.subtype hRS).Normal := by
    show (↑(R.subtype hRS) : Subgroup ↥S).Normal
    rw [Sylow.coe_subtype]
    exact hRn
  have hchar : (R.subtype hRS).Characteristic := Sylow.characteristic_of_normal _ hRn'
  have hchar' : ((R : Subgroup K).subgroupOf S).Characteristic := by
    rw [← Sylow.coe_subtype (P := R) (N := S) (h := hRS)]
    exact hchar
  refine Subgroup.Normal.mk fun n hn g => ?_
  have hnS : n ∈ S := hRS hn
  have hmap := (Subgroup.characteristic_iff_map_eq.mp hchar') (MulAut.conjNormal (H := S) g)
  have hmem : (MulAut.conjNormal (H := S) g) ⟨n, hnS⟩ ∈ ((R : Subgroup K).subgroupOf S) := by
    have h1 : (MulAut.conjNormal (H := S) g) ⟨n, hnS⟩ ∈
        ((R : Subgroup K).subgroupOf S).map (MulAut.conjNormal (H := S) g).toMonoidHom :=
      ⟨⟨n, hnS⟩, hn, rfl⟩
    rwa [hmap] at h1
  have hval : (((MulAut.conjNormal (H := S) g) ⟨n, hnS⟩ : ↥S) : K) = g * n * g⁻¹ := by
    simp [MulAut.conjNormal_apply]
  rwa [Subgroup.mem_subgroupOf, hval] at hmem

/-- Two subgroups of distinct prime-power orders have coprime orders. -/
theorem coprime_card_of_isPGroup_of_ne {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    [Finite K] {N R : Subgroup K} (hN : IsPGroup p ↥N) (hR : IsPGroup r ↥R) :
    (Nat.card R).Coprime (Nat.card N) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨m, hm⟩ := hN.exists_card_eq
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  rw [hn, hm]
  have h1 : r.Coprime p := (Nat.coprime_primes hr hp).mpr (Ne.symm hpr)
  exact (h1.pow_right m).pow_left n

end Work.Frobenius.Fpf
