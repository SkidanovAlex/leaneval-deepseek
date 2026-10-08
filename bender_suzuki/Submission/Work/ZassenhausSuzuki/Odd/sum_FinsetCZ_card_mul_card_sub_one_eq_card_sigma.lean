import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `sum_FinsetCZ_card_mul_card_sub_one_eq_card_sigma`

The fibre decomposition underlying Suzuki 1962, Proposition 13 (see Huppert–Blackburn
XI.11.6, and the module docstring of `Submission.Work.ZassenhausSuzuki.Odd.OddDefs`):

$$\sum_{A \in \mathcal F} |A|\,(|A| - 1)
   = \#\{(x, y) : x \text{ strongly real}, x \ne 1, x^2 \ne 1,\ y \in C_G(x)\}.$$

Here `𝓕 = FinsetCZ` is the Bender–Suzuki family of centralisers `A = C_G(x)` of the strongly
real elements `x ≠ 1` with `x * x ≠ 1`.

The mathematics is a pure fibre count, with the structural input
`centralizer_abelian_of_strongly_real` (Suzuki 1962, Prop. 14):

* for every `A ∈ 𝓕` the subgroup `A` is abelian of **odd** order, and every `y ∈ A`, `y ≠ 1`
  is again strongly real with `C_G(y) = A`; consequently squaring is injective on `A`
  (`y * y ≠ 1` for `y ≠ 1`), and the fibre of `A` under `x ↦ C_G(x)` is exactly `A \ {1}`;
* hence `x ↦ C_G(x)` maps the set `S` of strongly real non-identity non-involutions onto
  `𝓕`, with fibres of size `|A| - 1`, and

  `Nat.card (Σ x : S, C_G(x)) = Σ_{x ∈ S} |C_G(x)| = Σ_{A ∈ 𝓕} |A| (|A| - 1)`.

The sum over `S` is grouped by the centraliser with `Finset.sum_fiberwise_of_maps_to`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

/-- The set of strongly real elements of `G` that are neither `1` nor involutions: the index
set of the sigma type in `sum_FinsetCZ_card_mul_card_sub_one_eq_card_sigma`. -/
private abbrev IsSRElem {G : Type} [Group G] (x : G) : Prop :=
  Work.ZassenhausSuzuki.IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1

/-- The cardinality of `Finset.filter p Finset.univ` as a `Nat.card` of a subtype. -/
private lemma card_filter_univ_eq_natCard {α : Type} [Fintype α] (p : α → Prop)
    [DecidablePred p] :
    (Finset.univ.filter p).card = Nat.card {a : α // p a} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Removing the identity from a finite group costs exactly one element. -/
private lemma card_subtype_ne_one (K : Type) [Group K] [Finite K] :
    Nat.card {u : K // u ≠ 1} = Nat.card K - 1 := by
  have h1 : Nat.card {u : K // u ≠ 1} = Nat.card ↥(({1}ᶜ : Set K)) := rfl
  rw [h1, Nat.card_coe_set_eq, Set.compl_eq_univ_sdiff,
    Set.ncard_sdiff_singleton_of_mem (Set.mem_univ (1 : K)), Set.ncard_univ]

/-- In a finite group of odd order, a non-identity element is not an involution. -/
private lemma sq_ne_one_of_odd_card {K : Type} [Group K] [Finite K] (hodd : Odd (Nat.card K))
    {y : K} (hy : y ≠ 1) : y * y ≠ 1 := by
  intro h2
  have hdvd : orderOf y ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa [pow_two] using h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact hy (orderOf_eq_one_iff.mp h1)
  · exact hodd.not_two_dvd_nat (by rw [← h1]; exact orderOf_dvd_natCard y)

/-- Version of `sq_ne_one_of_odd_card` for a subgroup of odd order. -/
private lemma sq_ne_one_of_odd_card_mem {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hodd : Odd (Nat.card ↥A)) {y : G} (hy : y ∈ A) (hy1 : y ≠ 1) : y * y ≠ 1 := by
  intro h2
  have hne : (⟨y, hy⟩ : ↥A) ≠ 1 :=
    fun hc => hy1 (by simpa using congrArg (fun z : ↥A => (z : G)) hc)
  have hs : (⟨y, hy⟩ : ↥A) * ⟨y, hy⟩ = 1 := Subtype.ext (by simpa using h2)
  exact sq_ne_one_of_odd_card (K := ↥A) (y := (⟨y, hy⟩ : ↥A)) hodd hne hs

/-- A subgroup with its identity removed, counted. -/
private lemma card_subtype_mem_ne_one {G : Type} [Group G] [Finite G] (A : Subgroup G) :
    Nat.card {y : G // y ∈ (A : Set G) ∧ y ≠ 1} = Nat.card ↥A - 1 := by
  have h1 : Nat.card {y : G // y ∈ (A : Set G) ∧ y ≠ 1}
      = Nat.card (((A : Set G) \ {1}) : Set G) := rfl
  rw [h1, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem A.one_mem,
    ← Nat.card_coe_set_eq (A : Set G)]
  congr 1

/-- An element lies in the centraliser of a singleton it generates. -/
private lemma mem_A_of_centralizer_eq {G : Type} [Group G] {A : Subgroup G} {y : G}
    (hy : Subgroup.centralizer ({y} : Set G) = A) : y ∈ A := by
  rw [← hy]
  exact Subgroup.mem_centralizer_singleton_iff.mpr rfl

/-- Membership in the Bender–Suzuki family `𝓕 = FinsetCZ`. -/
private lemma mem_FinsetCZ_iff {G : Type} [Group G] [Finite G] {A : Subgroup G} :
    A ∈ FinsetCZ (G := G) ↔ IsCZ A := by
  classical
  rw [FinsetCZ]
  simp

/-- **Suzuki 1962, Prop. 14, in the form used here.**  Every member of the Bender–Suzuki
family is abelian of odd order, and consists of strongly real elements with the same
centraliser. -/
private lemma isCZ_struct {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : SzOddHyp H Q t) {A : Subgroup G} (hA : IsCZ A) :
    IsMulCommutative ↥A ∧ Odd (Nat.card ↥A) ∧
      ∀ a ∈ A, a ≠ 1 →
        Work.ZassenhausSuzuki.IsStronglyReal a ∧ Subgroup.centralizer ({a} : Set G) = A := by
  obtain ⟨x, hsr, _hx1, hx2, hAx⟩ := hA
  have hmain := Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real
      h.hsplit h.hzass h.h2 hx2 hsr
  exact ⟨by rw [← hAx]; exact hmain.1,
    by rw [← hAx]; exact hmain.2.1,
    fun a ha ha1 => by
      rw [← hAx] at ha ⊢
      exact hmain.2.2 a ha ha1⟩

/-- **The fibre of `x ↦ C_G(x)` over `A ∈ 𝓕` is `A \ {1}`.**  For `A ∈ FinsetCZ` the
strongly real elements `x ≠ 1`, `x * x ≠ 1` with `C_G(x) = A` are exactly the non-identity
elements of `A`, so there are `|A| - 1` of them. -/
private lemma fibre_card_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : SzOddHyp H Q t) {A : Subgroup G} (hA : IsCZ A) :
    Nat.card {x : {x : G // IsSRElem x} // Subgroup.centralizer ({x.1} : Set G) = A}
      = Nat.card ↥A - 1 := by
  classical
  obtain ⟨_hcom, hodd, hcent⟩ := isCZ_struct h hA
  have hmem : ∀ x : {x : {x : G // IsSRElem x} // Subgroup.centralizer ({x.1} : Set G) = A},
      x.1.1 ∈ A := fun x => mem_A_of_centralizer_eq x.2
  have hne : ∀ x : {x : {x : G // IsSRElem x} // Subgroup.centralizer ({x.1} : Set G) = A},
      x.1.1 ≠ 1 := fun x => x.1.2.2.1
  have hSR : ∀ y : G, y ∈ A → y ≠ 1 → IsSRElem y :=
    fun y hy hy1 => ⟨(hcent y hy hy1).1, hy1, sq_ne_one_of_odd_card_mem hodd hy hy1⟩
  have hcent' : ∀ y : G, y ∈ A → y ≠ 1 → Subgroup.centralizer ({y} : Set G) = A :=
    fun y hy hy1 => (hcent y hy hy1).2
  have hbij : Function.Bijective
      (fun x : {x : {x : G // IsSRElem x} // Subgroup.centralizer ({x.1} : Set G) = A} =>
        (⟨x.1.1, hmem x, hne x⟩ : {y : G // y ∈ (A : Set G) ∧ y ≠ 1})) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : {y : G // y ∈ (A : Set G) ∧ y ≠ 1} => z.1) hxy))
    · intro z
      refine ⟨⟨⟨z.1, hSR z.1 z.2.1 z.2.2⟩, hcent' z.1 z.2.1 z.2.2⟩, ?_⟩
      exact Subtype.ext rfl
  exact Eq.trans (Nat.card_congr (Equiv.ofBijective _ hbij)) (card_subtype_mem_ne_one A)

/-- **Fibre decomposition of `Σ_{x ∈ S} |C_G(x)|`.**  The strongly real non-identity
non-involutions of `G` fall into the centralisers `A ∈ FinsetCZ`, and `A` contributes
`|A| (|A| - 1)`:  its `|A| - 1` elements `x ≠ 1`, each with `|C_G(x)| = |A|`. -/
theorem sum_FinsetCZ_card_mul_card_sub_one_eq_card_sigma {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) :
    (∑ A ∈ Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G), Nat.card ↥A * (Nat.card ↥A - 1))
      = Nat.card (Σ x : {x : G // Work.ZassenhausSuzuki.IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1},
          ↥(Subgroup.centralizer ({x.1} : Set G))) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  show (∑ A ∈ FinsetCZ (G := G), Nat.card ↥A * (Nat.card ↥A - 1))
      = Nat.card (Σ x : {x : G // IsSRElem x}, ↥(Subgroup.centralizer ({x.1} : Set G)))
  rw [Nat.card_sigma]
  have hmaps : ∀ x ∈ (Finset.univ : Finset {x : G // IsSRElem x}),
      Subgroup.centralizer ({x.1} : Set G) ∈ FinsetCZ (G := G) := by
    intro x _
    exact mem_FinsetCZ_iff.mpr ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, rfl⟩
  have hgroup := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset {x : G // IsSRElem x}))
      (t := FinsetCZ (G := G))
      (g := fun x : {x : G // IsSRElem x} => Subgroup.centralizer ({x.1} : Set G))
      hmaps (fun x : {x : G // IsSRElem x} => Nat.card ↥(Subgroup.centralizer ({x.1} : Set G)))
  rw [← hgroup]
  apply Finset.sum_congr rfl
  intro A hA
  have hAc : IsCZ A := mem_FinsetCZ_iff.mp hA
  have hfib : (Finset.univ.filter
        (fun x : {x : G // IsSRElem x} => Subgroup.centralizer ({x.1} : Set G) = A)).card
      = Nat.card ↥A - 1 := by
    rw [card_filter_univ_eq_natCard]
    exact fibre_card_eq h hAc
  have hconst : ∀ x ∈ (Finset.univ.filter
        (fun x : {x : G // IsSRElem x} => Subgroup.centralizer ({x.1} : Set G) = A)),
      Nat.card ↥(Subgroup.centralizer ({x.1} : Set G)) = Nat.card ↥A :=
    fun x hx => by rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, hfib]
  exact mul_comm _ _

end Work.ZassenhausSuzuki.Odd
