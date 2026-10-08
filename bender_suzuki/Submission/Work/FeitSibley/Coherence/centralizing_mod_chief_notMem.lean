import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.Q1_isNilpotent_of_D_ne_bot
import Submission.Work.FeitSibley.Coherence.prime_dvd_quotient_of_le_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi II, Appendice XII, step (1): the centre of `Q₁/Q₃` is strictly larger than `Q₂/Q₃`

Let `h : FSData G` with `h.D ≠ ⊥`, and let `Q₃ ≤ Q₂ ≤ [Q₁,Q₁]` be `H`-invariant subgroups with
`[Q₂,Q₁] ≤ Q₃` and no `H`-invariant subgroup strictly between them (an `H`-chief factor).  If
two distinct primes divide `|Q₁|`, then there is `z ∈ Q₁` centralising `Q₁` modulo `Q₃` with
`z ∉ Q₂`.

Equivalently: writing `Z = Z(Q₁/Q₃)` for the preimage in `G` of the centre of `Q₁/Q₃`, one has
`Q₂ ⊊ Z` (`[Q₂,Q₁] ≤ Q₃` is exactly `Q₂ ≤ Z`).

The proof is by contradiction.  `Q₁` is nilpotent (`Q1_isNilpotent_of_D_ne_bot`, Thompson).
Passing to the quotient `Q₁/Q₃`, one has `Z(Q₁/Q₃) = Q₂/Q₃` in the contradictory case, so
`|Z(Q₁/Q₃)| = |Q₂/Q₃|`.  On the one hand `Q₃ ≤ [Q₁,Q₁]`, so both of the two primes dividing
`|Q₁|` divide `|Q₁/Q₃|`; in a nilpotent group every prime dividing the order divides the order
of the centre, so both divide `|Z(Q₁/Q₃)| = |Q₂/Q₃|`.  On the other hand `Q₂/Q₃` is abelian and
`H`-chief, hence an elementary abelian `p`-group for a single prime `p`: an abelian chief factor
has prime-power order (`chief_factor_atMostOnePrime'`).  Contradiction.

The two ingredients extracted as separate lemmas are
* `prime_dvd_quotient_of_le_commutator` (nilpotency/commutator bookkeeping),
* `chief_factor_atMostOnePrime'` (an abelian chief factor has prime power order).
This module is the analogue of `Coherence/exists_centralizing_notMem_of_chief.lean` for the
same statement.
-/

set_option linter.style.haveILetI false

open Classical
open scoped commutatorElement

namespace Work.FeitSibley.Coherence

noncomputable section

/-- **An abelian chief factor has prime-power order.**  If `Q₃ ≤ Q₂` are both normalised by
`H`, if `Q₂/Q₃` is abelian (`hab`), and if there is no `H`-invariant subgroup strictly between
`Q₃` and `Q₂` (`hchief`), then `|Q₂/Q₃|` is divisible by at most one prime.

Proof.  Let `N = Q₃ ⊴ Q₂` and `L = Q₂/N` (abelian, by `hab`), and let `r` be a prime.  The set
`A_r = {a ∈ Q₂ | aʳ ∈ Q₃}` is a subgroup of `G` (`L` being abelian, the `r`-th power map
descends), it satisfies `Q₃ ≤ A_r ≤ Q₂`, and it is `H`-invariant because
`(t a t⁻¹)ʳ = t aʳ t⁻¹` and `H` normalises both `Q₂` and `Q₃`.  Hence `A_r = Q₃` or
`A_r = Q₂` by `hchief`.

If `A_r = Q₂` then every element of `L` has `r`-th power `1`, so for any prime `s` dividing
`|L|` a Cauchy element `y` of order `s` satisfies `s = orderOf y ∣ r`; if `s ≠ r` this is
impossible.  If `A_r = Q₃` then `L` has no element of order `r`, contradicting Cauchy's
theorem when `r ∣ |L|`.  Hence a prime `r ≠ s` cannot satisfy both `r ∣ |L|` and `s ∣ |L|`. -/
theorem chief_factor_atMostOnePrime' {G : Type} [Group G] [Fintype G]
    (H Q2 Q3 : Subgroup G) (hQ3Q2 : Q3 ≤ Q2)
    [(Q3.subgroupOf Q2).Normal]
    (hQ2n : H ≤ Subgroup.normalizer (Q2 : Set G))
    (hQ3n : H ≤ Subgroup.normalizer (Q3 : Set G))
    (hab : ∀ a : G, a ∈ Q2 → ∀ b : G, b ∈ Q2 → a * b * a⁻¹ * b⁻¹ ∈ Q3)
    (hchief : ∀ A : Subgroup G, Q3 ≤ A → A ≤ Q2 → H ≤ Subgroup.normalizer (A : Set G) →
      A = Q3 ∨ A = Q2)
    {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hrdvd : r ∣ Nat.card (↥Q2 ⧸ (Q3.subgroupOf Q2)))
    (hsdvd : s ∣ Nat.card (↥Q2 ⧸ (Q3.subgroupOf Q2))) : False := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact s.Prime := ⟨hs⟩
  let N : Subgroup ↥Q2 := Q3.subgroupOf Q2
  haveI hNnormal : N.Normal := inferInstance
  let L := ↥Q2 ⧸ N
  haveI : Fintype L :=
    Fintype.ofSurjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  -- membership in `N` through the quotient map
  have hNiff : ∀ y : ↥Q2, y ∈ N ↔ QuotientGroup.mk' N y = 1 :=
    fun y => (QuotientGroup.eq_one_iff y).symm
  -- detecting powers in the quotient
  have hes : ∀ (x : ↥Q2) (n : ℕ),
      (QuotientGroup.mk' N x) ^ n = 1 ↔ (x : G) ^ n ∈ Q3 := by
    intro x n
    rw [← map_pow, ← hNiff, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  -- `L = Q₂/Q₃` is abelian because `[Q₂,Q₂] ≤ Q₃`
  have hLLcomm : ∀ x y : L, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hc : ⁅QuotientGroup.mk' N a, QuotientGroup.mk' N b⁆ = 1 := by
      have hmap : ⁅QuotientGroup.mk' N a, QuotientGroup.mk' N b⁆ = QuotientGroup.mk' N ⁅a, b⁆ := by
        simp [commutatorElement_def]
      rw [hmap, ← hNiff, Subgroup.mem_subgroupOf]
      simpa [commutatorElement_def] using hab (a : G) a.2 (b : G) b.2
    exact Commute.eq (commutatorElement_eq_one_iff_commute.mp hc)
  -- the subgroup `A = {a ∈ Q₂ | aʳ ∈ Q₃}`
  let A : Subgroup G :=
    { carrier := {a : G | a ∈ Q2 ∧ a ^ r ∈ Q3}
      mul_mem' := by
        intro a b ha hb
        refine ⟨Q2.mul_mem ha.1 hb.1, ?_⟩
        have ha' : (QuotientGroup.mk' N (⟨a, ha.1⟩ : ↥Q2)) ^ r = 1 := (hes ⟨a, ha.1⟩ r).mpr ha.2
        have hb' : (QuotientGroup.mk' N (⟨b, hb.1⟩ : ↥Q2)) ^ r = 1 := (hes ⟨b, hb.1⟩ r).mpr hb.2
        have h1 : (QuotientGroup.mk' N ((⟨a, ha.1⟩ : ↥Q2) * ⟨b, hb.1⟩)) ^ r = 1 := by
          rw [map_mul, Commute.mul_pow ((commute_iff_eq _ _).mpr (hLLcomm _ _)) r, ha', hb',
            mul_one]
        have h2 : ((⟨a, ha.1⟩ : ↥Q2) * ⟨b, hb.1⟩) ^ r ∈ N :=
          (hNiff _).mpr (by rw [map_pow]; exact h1)
        rw [Subgroup.mem_subgroupOf] at h2
        simpa [Subgroup.coe_pow, Subgroup.coe_mul] using h2
      one_mem' := ⟨Q2.one_mem, by rw [one_pow]; exact Q3.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha2, har⟩
        exact ⟨Q2.inv_mem ha2, by rw [inv_pow]; exact Q3.inv_mem har⟩ }
  have hQ3leA : Q3 ≤ A := by
    intro a ha
    exact ⟨hQ3Q2 ha, pow_mem ha r⟩
  have hAleQ2 : A ≤ Q2 := fun a ha => ha.1
  -- `A` is `H`-invariant
  have hAn : H ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro t ht a ha
    obtain ⟨ha2, har⟩ := ha
    refine ⟨(Subgroup.le_normalizer_iff.mp hQ2n) t ht a ha2, ?_⟩
    have hconj : (t * a * t⁻¹) ^ r = t * a ^ r * t⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
    rw [hconj]
    exact (Subgroup.le_normalizer_iff.mp hQ3n) t ht (a ^ r) har
  rcases hchief A hQ3leA hAleQ2 hAn with hA | hA
  · -- `A = Q₃` is impossible: `L` has an element of order `r`
    obtain ⟨y, hy⟩ :=
      exists_prime_orderOf_dvd_card (G := L) r (by rw [← Nat.card_eq_fintype_card]; exact hrdvd)
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective N y
    have hyr : y ^ r = 1 := by rw [← hy, pow_orderOf_eq_one]
    have har : (a : G) ^ r ∈ Q3 := (hes a r).mp (by rw [ha]; exact hyr)
    have hmemA : (a : G) ∈ A := ⟨a.2, har⟩
    have haQ3 : (a : G) ∈ Q3 := hA ▸ hmemA
    have hmemN : a ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      exact haQ3
    have hy1 : y = 1 := by
      rw [← ha]
      exact (hNiff a).mp hmemN
    exact hr.ne_one (by rw [← hy, hy1, orderOf_one])
  · -- `A = Q₂` is impossible: then `L` has exponent `r`, so `s ∣ r`
    have hall : ∀ a : G, a ∈ Q2 → a ^ r ∈ Q3 := by
      intro a ha
      exact (hA.symm ▸ ha : a ∈ A).2
    obtain ⟨y, hy⟩ :=
      exists_prime_orderOf_dvd_card (G := L) s (by rw [← Nat.card_eq_fintype_card]; exact hsdvd)
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective N y
    have h1 : y ^ r = 1 := by
      rw [← ha]
      exact (hes a r).mpr (hall (a : G) a.2)
    have h4 : orderOf y ∣ r := orderOf_dvd_of_pow_eq_one h1
    have h3 : s ∣ r := by rwa [hy] at h4
    rcases hr.eq_one_or_self_of_dvd s h3 with h | h
    · exact hs.ne_one h
    · exact hrs h.symm

theorem centralizing_mod_chief_notMem {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (hD : h.D ≠ ⊥)
    (h2 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.card h.Q1 ∧ q ∣ Nat.card h.Q1)
    (Q2 Q3 : Subgroup G) (hQ3Q2 : Q3 ≤ Q2) (hQ2 : Q2 ≤ ⁅h.Q1, h.Q1⁆) (hQ3' : Q3 ≤ ⁅h.Q1, h.Q1⁆)
    (hQ2n : h.H ≤ Subgroup.normalizer (Q2 : Set G))
    (hQ3n : h.H ≤ Subgroup.normalizer (Q3 : Set G))
    (hchief : ∀ A : Subgroup G, Q3 ≤ A → A ≤ Q2 → h.H ≤ Subgroup.normalizer (A : Set G) →
      A = Q3 ∨ A = Q2)
    (hcen : ⁅Q2, h.Q1⁆ ≤ Q3) :
    ∃ z : G, z ∈ h.Q1 ∧ (∀ y : G, y ∈ h.Q1 → z * y * z⁻¹ * y⁻¹ ∈ Q3) ∧ z ∉ Q2 := by
  classical
  haveI hNil : Group.IsNilpotent ↥h.Q1 := Q1_isNilpotent_of_D_ne_bot h hD
  have hQ1comm : ⁅h.Q1, h.Q1⁆ ≤ h.Q1 :=
    (Subgroup.commutator_le_sup h.Q1 h.Q1).trans (le_of_eq (sup_idem h.Q1))
  have hQ2leQ1 : Q2 ≤ h.Q1 := hQ2.trans hQ1comm
  have hQ3leQ1 : Q3 ≤ h.Q1 := hQ3'.trans hQ1comm
  -- `Q₃` is normalised by `Q₁` (because `[Q₃,Q₁] ≤ [Q₂,Q₁] ≤ Q₃`).
  have hQ3norm : h.Q1 ≤ Subgroup.normalizer (Q3 : Set G) := by
    have hcomm : ⁅Q3, h.Q1⁆ ≤ Q3 := (Subgroup.commutator_mono hQ3Q2 le_rfl).trans hcen
    rw [Subgroup.le_normalizer_iff]
    intro g hg q hq
    have h2' : ⁅q, g⁆ ∈ Q3 := (Subgroup.commutator_le.mp hcomm) q hq g hg
    have h1' : ⁅g, q⁆ ∈ Q3 := by
      rw [show ⁅g, q⁆ = ⁅q, g⁆⁻¹ from by
        rw [commutatorElement_def, commutatorElement_def]; group]
      exact Subgroup.inv_mem _ h2'
    rw [show g * q * g⁻¹ = ⁅g, q⁆ * q from by rw [commutatorElement_def]; group]
    exact Subgroup.mul_mem _ h1' hq
  have hQ2normQ3 : Q2 ≤ Subgroup.normalizer (Q3 : Set G) := hQ2leQ1.trans hQ3norm
  -- Work inside `Q₁`.
  let N : Subgroup ↥h.Q1 := Q3.subgroupOf h.Q1
  haveI hNnormal : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQ3leQ1).mpr hQ3norm
  haveI hN2normal : (Q3.subgroupOf Q2).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ3Q2).mpr hQ2normQ3
  let Q2A : Subgroup ↥h.Q1 := Q2.subgroupOf h.Q1
  -- `Z = {x ∈ Q₁ | [x,Q₁] ≤ Q₃}`, the preimage of the centre of `Q₁/Q₃`.
  let Z : Subgroup ↥h.Q1 := Subgroup.upperCentralSeriesStep N
  -- `[Q₂,Q₁] ≤ Q₃` gives `Q₂ ≤ Z`.
  have hQ2A_le_Z : Q2A ≤ Z := by
    intro x hx
    rw [Subgroup.mem_upperCentralSeriesStep]
    intro y
    rw [Subgroup.mem_subgroupOf, show ((⁅x, y⁆ : ↥h.Q1) : G) = ⁅(x : G), (y : G)⁆ from by
      rw [commutatorElement_def, commutatorElement_def]; rfl]
    exact (Subgroup.commutator_le.mp hcen) (x : G) (Subgroup.mem_subgroupOf.mp hx) (y : G) y.2
  -- It remains to produce `z ∈ Z ∖ Q₂`.
  suffices hex : ∃ z : ↥h.Q1, z ∈ Z ∧ z ∉ Q2A by
    obtain ⟨z, hzZ, hzQ2⟩ := hex
    refine ⟨(z : G), z.2, ?_, ?_⟩
    · intro y hy
      have hmem : ⁅z, (⟨y, hy⟩ : ↥h.Q1)⁆ ∈ N :=
        (Subgroup.mem_upperCentralSeriesStep N z).mp hzZ (⟨y, hy⟩ : ↥h.Q1)
      rw [Subgroup.mem_subgroupOf,
        show ((⁅z, (⟨y, hy⟩ : ↥h.Q1)⁆ : ↥h.Q1) : G) = z * y * z⁻¹ * y⁻¹ from by
          rw [commutatorElement_def]; rfl] at hmem
      exact hmem
    · intro hz
      exact hzQ2 (Subgroup.mem_subgroupOf.mpr hz)
  by_contra hcon
  have hZle : Z ≤ Q2A := by
    intro z hz
    by_contra hz2
    exact hcon ⟨z, hz, hz2⟩
  have hZeq : Z = Q2A := le_antisymm hZle hQ2A_le_Z
  -- `Z(A/N) = Q₂A/N`.
  have hRange : (QuotientGroup.mk' N).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
  have hcenter : Subgroup.center (↥h.Q1 ⧸ N) = Q2A.map (QuotientGroup.mk' N) := by
    have h1 : Subgroup.comap (QuotientGroup.mk' N) (Subgroup.center (↥h.Q1 ⧸ N)) = Q2A := by
      rw [← Subgroup.upperCentralSeriesStep_eq_comap_center N]; exact hZeq
    have h2 := Subgroup.map_comap_eq (QuotientGroup.mk' N) (Subgroup.center (↥h.Q1 ⧸ N))
    rw [hRange, top_inf_eq] at h2
    rw [← h2, h1]
  -- Cardinality: `|Z(A/N)| = |Q₂ ⧸ Q₃|` (both are `Q₂/Q₃`).
  let Φ : ↥Q2 →* (↥h.Q1 ⧸ N) := (QuotientGroup.mk' N).comp (Subgroup.inclusion hQ2leQ1)
  have hker : Φ.ker = Q3.subgroupOf Q2 := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (↑(Subgroup.inclusion hQ2leQ1 x) : ↥h.Q1 ⧸ N) = 1 ↔ (x : G) ∈ Q3
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hrange : Φ.range = Q2A.map (QuotientGroup.mk' N) := by
    change ((QuotientGroup.mk' N).comp (Subgroup.inclusion hQ2leQ1)).range =
      Q2A.map (QuotientGroup.mk' N)
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    exact ⟨fun ⟨y, hy⟩ => by rw [← hy, Subgroup.coe_inclusion]; exact y.2,
           fun hx => ⟨⟨(x : G), hx⟩, Subtype.ext (by rw [Subgroup.coe_inclusion])⟩⟩
  have hcard : Nat.card ↥(Subgroup.center (↥h.Q1 ⧸ N)) =
      Nat.card (↥Q2 ⧸ (Q3.subgroupOf Q2)) := by
    rw [hcenter, ← hrange, ← hker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv).symm
  -- `N ≤ [Q₁,Q₁]`.
  have hN_le_comm : N ≤ ⁅(⊤ : Subgroup ↥h.Q1), ⊤⁆ := by
    intro x hx
    have hxQ3 : (x : G) ∈ Q3 := Subgroup.mem_subgroupOf.mp hx
    have hx' : (x : G) ∈ ⁅h.Q1, h.Q1⁆ := hQ3' hxQ3
    have hmap : Subgroup.map h.Q1.subtype ⁅(⊤ : Subgroup ↥h.Q1), ⊤⁆ = ⁅h.Q1, h.Q1⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [← hmap, Subgroup.mem_map] at hx'
    obtain ⟨w, hw, hwG⟩ := hx'
    exact (show w = x from Subtype.ext hwG) ▸ hw
  -- `Q₂/Q₃` is abelian.
  have hab : ∀ (a : G), a ∈ Q2 → ∀ (b : G), b ∈ Q2 → a * b * a⁻¹ * b⁻¹ ∈ Q3 := by
    intro a ha b hb
    have haZ : (⟨a, hQ2leQ1 ha⟩ : ↥h.Q1) ∈ Z :=
      hQ2A_le_Z (Subgroup.mem_subgroupOf.mpr ha)
    have hmem :=
      (Subgroup.mem_upperCentralSeriesStep N ⟨a, hQ2leQ1 ha⟩).mp haZ (⟨b, hQ2leQ1 hb⟩ : ↥h.Q1)
    rw [Subgroup.mem_subgroupOf] at hmem
    rwa [show ((⁅(⟨a, hQ2leQ1 ha⟩ : ↥h.Q1), (⟨b, hQ2leQ1 hb⟩ : ↥h.Q1)⁆ : ↥h.Q1) : G)
        = a * b * a⁻¹ * b⁻¹ from by rw [commutatorElement_def]; rfl] at hmem
  -- Final contradiction with the two primes dividing `|Q₁|`.
  obtain ⟨p0, q0, hp0, hq0, hp0q0, hp0dvd, hq0dvd⟩ := h2
  have hp0dvdA : p0 ∣ Nat.card ↥h.Q1 := by simpa using hp0dvd
  have hq0dvdA : q0 ∣ Nat.card ↥h.Q1 := by simpa using hq0dvd
  have hp0N : p0 ∣ Nat.card (↥h.Q1 ⧸ N) :=
    prime_dvd_quotient_of_le_commutator N hN_le_comm hp0 hp0dvdA
  have hq0N : q0 ∣ Nat.card (↥h.Q1 ⧸ N) :=
    prime_dvd_quotient_of_le_commutator N hN_le_comm hq0 hq0dvdA
  have hp0c : p0 ∣ Nat.card ↥(Subgroup.center (↥h.Q1 ⧸ N)) := by
    haveI : Fact p0.Prime := ⟨hp0⟩
    exact Group.IsNilpotent.prime_dvd_card_center hp0N
  have hq0c : q0 ∣ Nat.card ↥(Subgroup.center (↥h.Q1 ⧸ N)) := by
    haveI : Fact q0.Prime := ⟨hq0⟩
    exact Group.IsNilpotent.prime_dvd_card_center hq0N
  have hp0b : p0 ∣ Nat.card (↥Q2 ⧸ (Q3.subgroupOf Q2)) := by rwa [← hcard]
  have hq0b : q0 ∣ Nat.card (↥Q2 ⧸ (Q3.subgroupOf Q2)) := by rwa [← hcard]
  exact chief_factor_atMostOnePrime' h.H Q2 Q3 hQ3Q2 hQ2n hQ3n hab hchief hp0 hq0 hp0q0 hp0b hq0b

end

end Work.FeitSibley.Coherence
