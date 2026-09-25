import Mathlib
import Submission.NK.GlobalCFTdeep.AbstractH0
import Submission.NK.GlobalCFTdeep.SecondInequality.normHom_range_le_of_le
import Submission.NK.GlobalCFTdeep.SecondInequality.pow_index_mem_normHom_range
import Submission.NK.GlobalCFTdeep.SecondInequality.card_quotient_comap_dvd
import Submission.NK.GlobalCFTdeep.SecondInequality.factorization_natCard_eq_zero_of_pow_eq_one

open scoped BigOperators

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

open NK.GlobalCFTdeep

variable {G : Type*} [Group G] [Fintype G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- Elementary arithmetic of quotients: for subgroups `N₁ ≤ N₂` of a group `A`, the quotient
`A ⧸ N₁` sits in the extension `(N₂ ⧸ N₁) ↣ (A ⧸ N₁) ↠ (A ⧸ N₂)`, so its cardinality is the
product of the two factors.  Everything is phrased with `Nat.card` of quotient *types*, so the
statement is meaningful (and true, with value `0`) also when the quotients are infinite. -/
theorem natCard_quotient_eq_mul {A : Type*} [CommGroup A] (N₁ N₂ : Subgroup A) (h : N₁ ≤ N₂) :
    Nat.card (A ⧸ N₁) = Nat.card (↥N₂ ⧸ N₁.subgroupOf N₂) * Nat.card (A ⧸ N₂) := by
  rw [← Subgroup.index_eq_card N₁, ← Subgroup.index_eq_card N₂,
    ← Subgroup.index_eq_card (N₁.subgroupOf N₂)]
  exact (Subgroup.relIndex_mul_index h).symm

/-- If moreover the quotient `N₂ ⧸ N₁` has exponent dividing `n`, with `p ∤ n` and `p` prime, then
the `p`-parts of `Nat.card (A ⧸ N₁)` and of `Nat.card (A ⧸ N₂)` agree: the extra factor
`Nat.card (↥N₂ ⧸ N₁.subgroupOf N₂)` is a `p'`-number. -/
theorem factorization_natCard_quotient_eq_of_pow_eq_one {A : Type*} [CommGroup A]
    (N₁ N₂ : Subgroup A) (h : N₁ ≤ N₂) {p n : ℕ} (hp : p.Prime) (hn : ¬ p ∣ n)
    (hexp : ∀ q : ↥N₂ ⧸ N₁.subgroupOf N₂, q ^ n = 1)
    (hA : Nat.card (A ⧸ N₁) ≠ 0) :
    (Nat.card (A ⧸ N₁)).factorization p = (Nat.card (A ⧸ N₂)).factorization p := by
  have hsplit := natCard_quotient_eq_mul N₁ N₂ h
  have ha : Nat.card (↥N₂ ⧸ N₁.subgroupOf N₂) ≠ 0 := by
    intro hz; rw [hsplit, hz] at hA; simp at hA
  have hb : Nat.card (A ⧸ N₂) ≠ 0 := by
    intro hz; rw [hsplit, hz, mul_zero] at hA; exact hA rfl
  have hzero : (Nat.card (↥N₂ ⧸ N₁.subgroupOf N₂)).factorization p = 0 :=
    factorization_natCard_eq_zero_of_pow_eq_one ha hp hn hexp
  rw [hsplit, Nat.factorization_mul ha hb]
  simp only [Finsupp.add_apply, hzero, zero_add]

/-- The restriction `H0 G M → H0 H M` is injective on `p`-primary parts when `p ∤ [G:H]`, in the elementary model `H0 G M = M^G ⧸ N_G M` of degree-zero Tate cohomology for a finite group `G` acting on a commutative group `M`.

Proof plan. Fix a right transversal `T` of `H` in `G` (`Set.range Quotient.out` for the right coset setoid, whose `Subgroup.IsComplement H T` is `Subgroup.isComplement_range_right Quotient.out_eq'`), so `Subgroup.IsComplement.equiv` gives the bijection `↥H × ↥T ≃ G`, `(h,t) ↦ h * t`; and a left transversal `S` (`Set.range Quotient.out` for `G ⧸ H`, `Subgroup.isComplement_range_left Quotient.out_eq'`), giving `↥S × ↥H ≃ G`, `(s,h) ↦ s * h`.
* `(normHom G M).range ≤ (normHom H M).range`: `∏ g, g • x` factors over `↥H × ↥T` as `∏ t, normHom H M (t • x)`.
* If `y ∈ fixedSubgroup G M ⊓ (normHom H M).range`, say `y = normHom H M x`, then `y ^ H.index = ∏ s : ↥S, s • y = ∏ s : ↥S, s • normHom H M x = normHom G M x` lies in `(normHom G M).range` (use `Nat.card ↥S = H.index`).
* Arithmetic: with `A = fixedSubgroup G M`, `B = fixedSubgroup H M`, `PA = (normHom G M).range.subgroupOf A ≤ PB = (normHom H M).range.subgroupOf A`, the map `φ : ↥A →* ↥B ⧸ PB` has kernel `PB` and range injects into `↥B ⧸ (normHom H M).range.subgroupOf B`; `Subgroup.relIndex_mul_index` gives `Nat.card (↥A ⧸ PA) = Nat.card (↥A ⧸ PB) * Nat.card (PB ⧸ PA.subgroupOf PB)`, and the last factor is a quotient of a group killed by `H.index`, hence has `p`-part `1`. Finally `Nat.factorization_mul`, `Nat.factorization_le_iff_dvd`, `Subgroup.card_subgroup_dvd_card`. -/
theorem factorization_natCard_H0_le {G M : Type*} [Group G] [Fintype G] [CommGroup M]
    [MulDistribMulAction G M] (H : Subgroup G) [Fintype ↥H] {p : ℕ} (hp : p.Prime)
    (hm : ¬ p ∣ H.index)
    (hG : Nat.card (NK.GlobalCFTdeep.H0 G M) ≠ 0)
    (hH : Nat.card (NK.GlobalCFTdeep.H0 H M) ≠ 0) :
    (Nat.card (NK.GlobalCFTdeep.H0 G M)).factorization p ≤
      (Nat.card (NK.GlobalCFTdeep.H0 H M)).factorization p := by
  classical
  let A : Subgroup M := fixedSubgroup G M
  let B : Subgroup M := fixedSubgroup H M
  let PA : Subgroup M := (normHom G M).range
  let PB : Subgroup M := (normHom H M).range
  let N₁ : Subgroup ↥A := PA.subgroupOf A
  let N₂ : Subgroup ↥A := PB.subgroupOf A
  have hAB : A ≤ B := fun x hx g => hx (g : G)
  have hPAPB : PA ≤ PB := normHom_range_le_of_le H
  have hNle : N₁ ≤ N₂ := fun x hx => hPAPB hx
  have hsplit := natCard_quotient_eq_mul N₁ N₂ hNle
  have hAne : Nat.card (↥A ⧸ N₁) ≠ 0 := hG
  have hd_ne : Nat.card (↥A ⧸ N₂) ≠ 0 := by
    intro hz; rw [hsplit, hz, mul_zero] at hAne; exact hAne rfl
  -- the kernel of the restriction map has exponent dividing `[G : H]`
  have hexp : ∀ q : ↥N₂ ⧸ N₁.subgroupOf N₂, q ^ H.index = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N₁.subgroupOf N₂) q
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    simp only [N₁, N₂, A, PA, PB, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact pow_index_mem_normHom_range H (Subgroup.mem_subgroupOf.mp x.2) x.1.2
  -- the `p`-part of `H0 G M` is the `p`-part of the image of the restriction map
  have hmain : (Nat.card (H0 G M)).factorization p = (Nat.card (↥A ⧸ N₂)).factorization p :=
    factorization_natCard_quotient_eq_of_pow_eq_one N₁ N₂ hNle hp hm hexp hAne
  -- the image of the restriction map is a subgroup of `H0 H M`
  have hcomap : (PB.subgroupOf B).comap (Subgroup.inclusion hAB) = N₂ := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion, N₂, PB, B]
  have hBne : Nat.card (↥B ⧸ PB.subgroupOf B) ≠ 0 := hH
  have hdvd : Nat.card (↥A ⧸ N₂) ∣ Nat.card (H0 H M) := by
    have h1 := card_quotient_comap_dvd (Subgroup.inclusion hAB) (PB.subgroupOf B)
      (by rw [hcomap]; exact hd_ne) hBne
    rw [hcomap] at h1
    exact h1
  have hle : (Nat.card (↥A ⧸ N₂)).factorization ≤ (Nat.card (H0 H M)).factorization :=
    (Nat.factorization_le_iff_dvd hd_ne hH).mpr hdvd
  rw [hmain]
  exact hle p

end NK.GlobalCFTdeep.SecondInequality
