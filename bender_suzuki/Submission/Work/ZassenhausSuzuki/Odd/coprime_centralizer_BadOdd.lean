import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_basic
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_conj_of_prime_dvd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.Odd.coprime_centralizer_BadOdd`

A "bad" element `y` of odd order (odd order, `y ≠ 1`, not strongly real) has centraliser
`C_G(y)` of order coprime to `|A|` for every `ℱ`-subgroup `A` (`A = IsCZ`,
`A = C_G(x)` for a strongly real element `x ≠ 1` with `x * x ≠ 1`).

The mathematics is a standard Sylow argument.

* By `Work.ZassenhausSuzuki.Odd.isCZ_coprime_index`, `A` is a **Hall** subgroup of `G`:
  `|A|` and `[G : A]` are coprime.  Hence a Sylow `p`-subgroup of `A` (transported into `G`)
  is a Sylow `p`-subgroup of `G`; in particular, for every prime `p` with `p ∣ |A|` and every
  `p`-element `z` of `G`, some conjugate of `z` lies in `A`.
* Suppose a prime `p` divided both `|C_G(y)|` and `|A|`.  Then (Cauchy) `C_G(y)` contains an
  element `z` of order `p`; since `p ∣ |A|` and `A` is Hall, some conjugate `g z g⁻¹` lies in
  `A`.  Now `g z g⁻¹ ∈ A` is non-identity, so `C_G(g z g⁻¹) = A`
  (`Work.ZassenhausSuzuki.Odd.isCZ_basic`), and `g y g⁻¹` commutes with `g z g⁻¹`
  (conjugating `z * y = y * z`).  Hence `g y g⁻¹ ∈ A`, so `g y g⁻¹` — being a non-identity
  element of `A` — is strongly real, and hence `y` is strongly real, contradicting `BadOdd`.

The two ingredients of the argument are isolated below: conjugation preserves strongly real
elements (`isStronglyReal_mul_conj_inv`), and a Hall subgroup contains a conjugate of every
`p`-element for each prime `p` dividing its order (`exists_conj_mem_of_hall_index_coprime`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace Work.ZassenhausSuzuki.Odd

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- Conjugation preserves strongly real elements. -/
private theorem isStronglyReal_mul_conj_inv {x g : G}
    (hx : Work.ZassenhausSuzuki.IsStronglyReal x) :
    Work.ZassenhausSuzuki.IsStronglyReal (g * x * g⁻¹) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  exact ⟨g * a * g⁻¹, g * b * g⁻¹,
    by rw [conj_mul, ha, mul_one, mul_inv_cancel],
    by rw [conj_mul, hb, mul_one, mul_inv_cancel], conj_mul⟩

/-- If `A` is a Hall subgroup of the finite group `G` (`|A|` coprime to `[G : A]`), if `p` is a
prime dividing `|A|`, and if `z` has order `p`, then some conjugate of `z` lies in `A`.

Indeed a Sylow `p`-subgroup of `A` is a Sylow `p`-subgroup of `G` (as `p ∤ [G : A]`), every
`p`-subgroup of `G` is contained in a conjugate Sylow subgroup, and `⟨z⟩` is such a
`p`-subgroup. -/
private theorem exists_conj_mem_of_hall_index_coprime {A : Subgroup G}
    (hcop : Nat.Coprime (Nat.card ↥A) A.index)
    {p : ℕ} [Fact p.Prime] (hpA : p ∣ Nat.card ↥A) {z : G} (hz : orderOf z = p) :
    ∃ g : G, (MulAut.conj g) z ∈ A := by
  classical
  have hAi : ¬ p ∣ A.index := by
    intro hpi
    exact Nat.not_coprime_of_dvd_of_dvd (Fact.out : Nat.Prime p).one_lt hpA hpi hcop
  -- a Sylow `p`-subgroup of `A`, transported into `G`
  obtain ⟨SA⟩ := Sylow.nonempty (p := p) (G := ↥A)
  set KA : Subgroup G := Subgroup.map A.subtype (SA : Subgroup ↥A) with hKAdef
  have hKAle : KA ≤ A := Subgroup.map_subtype_le _
  have hKAp : IsPGroup p KA := (SA.isPGroup').map A.subtype
  have hKAsub : KA.subgroupOf A = (SA : Subgroup ↥A) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, hwy⟩; exact (Subtype.ext hwy) ▸ hw
    · exact fun hy => ⟨y, hy, rfl⟩
  -- it is a Sylow `p`-subgroup of `G`, since `p ∤ [G : A]`
  have hKAi : ¬ p ∣ KA.index := by
    intro hpi
    have h1 : p ∣ KA.relIndex A := by
      rw [← Subgroup.relIndex_mul_index hKAle] at hpi
      rcases (Fact.out : Nat.Prime p).dvd_mul.mp hpi with hh | hh
      · exact hh
      · exact absurd hh hAi
    have h2 : KA.relIndex A = (SA : Subgroup ↥A).index := by
      show (KA.subgroupOf A).index = _
      rw [hKAsub]
    rw [h2] at h1
    exact SA.not_dvd_index h1
  -- `⟨z⟩` is a `p`-subgroup, so it lies in a Sylow `p`-subgroup `S` of `G`
  have hzp : IsPGroup p ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨S, hSle⟩ := IsPGroup.exists_le_sylow hzp
  -- `S` is conjugate to the Sylow subgroup `KA`
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S (hKAp.toSylow hKAi)
  refine ⟨g, ?_⟩
  have hconj : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = KA := by
    have h1 : ((g • S : Sylow p G) : Subgroup G)
        = (S : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      congr 1
    have h2 : ((hKAp.toSylow hKAi : Sylow p G) : Subgroup G) = KA :=
      IsPGroup.toSylow_coe hKAp hKAi
    have h3 := congrArg (fun T : Sylow p G => (T : Subgroup G)) hg
    rw [h2, h1] at h3
    exact h3
  have hzS : z ∈ (S : Subgroup G) := hSle (Subgroup.mem_zpowers z)
  have hzKA : (MulAut.conj g) z ∈ KA := by
    rw [← hconj]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hzS
  exact hKAle hzKA

/-- **`Work.ZassenhausSuzuki.Odd.coprime_centralizer_BadOdd`.**  A bad odd element has
centraliser of order coprime to the order of every `ℱ`-subgroup. -/
theorem coprime_centralizer_BadOdd (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) {y : G}
    (hy : Work.ZassenhausSuzuki.Odd.BadOdd y) {A : Subgroup G}
    (hA : Work.ZassenhausSuzuki.Odd.IsCZ A) :
    Nat.Coprime (Nat.card ↥(Subgroup.centralizer ({y} : Set G))) (Nat.card ↥A) := by
  classical
  -- suppose a prime `p` divides both orders
  by_contra hnc
  obtain ⟨p, hp, hpC, hpA⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  haveI : Fact p.Prime := ⟨hp⟩
  -- Cauchy: an element `z` of order `p` commuting with `y`
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.centralizer ({y} : Set G))) p hpC
  have hzG : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe, hz]
  have hzy : (z : G) * y = y * (z : G) := Subgroup.mem_centralizer_singleton_iff.mp z.2
  -- some conjugate of `z` lies in the Hall subgroup `A`
  obtain ⟨g, hgz⟩ := exists_conj_mem_of_hall_index_coprime (A := A)
      (Work.ZassenhausSuzuki.Odd.isCZ_coprime_index h hA) hpA hzG
  have hgz_ne : (MulAut.conj g) (z : G) ≠ 1 := by
    intro hc
    have hz1G : (z : G) = 1 := (MulAut.conj g).injective (by rw [hc, map_one])
    have hz1 : z = 1 := Subtype.ext hz1G
    rw [hz1] at hz
    simp at hz
    exact hp.ne_one hz.symm
  -- `g * y * g⁻¹` commutes with the non-identity element `g * z * g⁻¹` of `A`
  have hcomm : (g * y * g⁻¹) * ((MulAut.conj g) (z : G)) =
      ((MulAut.conj g) (z : G)) * (g * y * g⁻¹) := by
    have hform : (MulAut.conj g) (z : G) = g * (z : G) * g⁻¹ := MulAut.conj_apply g (z : G)
    rw [hform]
    calc (g * y * g⁻¹) * (g * (z : G) * g⁻¹)
        = g * (y * (z : G)) * g⁻¹ := by group
      _ = g * ((z : G) * y) * g⁻¹ := by rw [← hzy]
      _ = (g * (z : G) * g⁻¹) * (g * y * g⁻¹) := by group
  -- so `g * y * g⁻¹` lies in `C_G(g * z * g⁻¹) = A`
  have hcent := ((isCZ_basic h hA).2.2 ((MulAut.conj g) (z : G)) hgz hgz_ne).2
  have hgyA : g * y * g⁻¹ ∈ A := by
    rw [← hcent]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hgyne : g * y * g⁻¹ ≠ 1 := by
    intro hc
    exact hy.2.1 (by calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
                       _ = g⁻¹ * 1 * g := by rw [hc]
                       _ = 1 := by group)
  -- hence `g * y * g⁻¹` is strongly real, and so is `y`
  have hsr := ((isCZ_basic h hA).2.2 (g * y * g⁻¹) hgyA hgyne).1
  refine hy.2.2 ?_
  have h1 := isStronglyReal_mul_conj_inv (g := g⁻¹) hsr
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y from by group] at h1

end Work.ZassenhausSuzuki.Odd
