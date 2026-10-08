import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.prop1b
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.GlaubermanZJ.Main
import Submission.Work.ThompsonFrobenius.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.L5Base` — foundations for Peterfalvi II Ch. V §2 Lemma 5

The two black boxes of the blueprint that Lemma 5 needs and that are available **without**
Feit–Thompson are exported here in their `FeitThompsonProp`-free form:

* `glaubermanZJ` — Glauberman's `ZJ`-theorem (`Work.GlaubermanZJ.GlaubermanZJ` carries an
  unused `FeitThompsonProp` hypothesis, dropped here);
* `thompsonFrobenius` — Thompson's theorem on fixed-point-free automorphisms of prime order
  (the delivered proof goes through `GlaubermanZJProp` and does not use `FeitThompsonProp`).

With Thompson's theorem in hand, Peterfalvi II Ch. V §1 Prop. 1 (b), (c) apply verbatim
(`prop1b`, `prop1c`), which yields the structural facts about the elementary abelian group
`Q₀ = Inv(H) ∪ {1}` used by Lemma 5: `Q₀sub H = Q₀ H` is elementary abelian, the involutions
of `H` commute pairwise, and the elements of `K = J(D,t)` act regularly on `Q₀^#`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.L5

open Submission.Blueprint

/-- **Glauberman's `ZJ`-theorem**, without the unused `FeitThompsonProp` hypothesis. -/
theorem glaubermanZJ : Submission.Blueprint.GlaubermanZJProp := by
  intro G _ _ p hp hpne hsol hab P
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hMchar : (Submission.Blueprint.pPrimeCore p G).Characteristic :=
    Work.GlaubermanZJ.pPrimeCore_characteristic (G := G) hp
  have hdisj : (P : Subgroup G) ⊓ Submission.Blueprint.pPrimeCore p G = ⊥ :=
    Work.GlaubermanZJ.sylow_inf_pPrimeCore_eq_bot (G := G) hp P
  let q : G →* G ⧸ (Submission.Blueprint.pPrimeCore p G) :=
    QuotientGroup.mk' (Submission.Blueprint.pPrimeCore p G)
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  haveI : Finite (G ⧸ (Submission.Blueprint.pPrimeCore p G)) := Finite.of_surjective q hsurj
  let Pbar : Sylow p (G ⧸ (Submission.Blueprint.pPrimeCore p G)) := Sylow.mapSurjective hsurj P
  have hPbar : (Pbar : Subgroup (G ⧸ (Submission.Blueprint.pPrimeCore p G))) =
      (P : Subgroup G).map q := Sylow.coe_mapSurjective hsurj P
  haveI : Group.IsSolvable G := hsol
  have hsolQ : Group.IsSolvable (G ⧸ (Submission.Blueprint.pPrimeCore p G)) := inferInstance
  have h2Q : 5 ≤ p ∨ Work.GlaubermanZJ.HasAbelianSylowTwo
      (G ⧸ (Submission.Blueprint.pPrimeCore p G)) :=
    Or.inr (Work.GlaubermanZJ.hasAbelianSylowTwo_quotient hab
      (Submission.Blueprint.pPrimeCore p G))
  have hcoreQ : Work.Fitting.pPrimeCore p (G ⧸ (Submission.Blueprint.pPrimeCore p G)) = ⊥ :=
    Work.GlaubermanZJ.pPrimeCore_quotient_eq_bot (G := G) hp
  have hred : (Submission.Blueprint.ZJ
      (Pbar : Subgroup (G ⧸ (Submission.Blueprint.pPrimeCore p G)))).Characteristic :=
    Work.GlaubermanZJ.GlaubermanZJ_reduced hp hpne hsolQ h2Q hcoreQ Pbar
  rw [hPbar] at hred
  have hchar : ((Submission.Blueprint.ZJ ((P : Subgroup G).map q)).comap q).Characteristic :=
    Work.GlaubermanZJ.characteristic_comap_mk (Submission.Blueprint.pPrimeCore p G) hMchar hred
  rw [Work.GlaubermanZJ.ZJ_comap_mk_eq_sup p (P : Subgroup G) hdisj] at hchar
  exact hchar

/-- **Thompson's theorem**, without the unused `FeitThompsonProp` hypothesis. -/
theorem thompsonFrobenius : Submission.Blueprint.ThompsonFrobeniusProp := by
  intro Q _ _ α hq hfpf
  exact Work.ThompsonFrobenius.isNilpotent_of_fpf_pow glaubermanZJ (Nat.card Q) Q rfl
    α (orderOf α) hq (pow_orderOf_eq_one α) hfpf

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- `K = J(D,t)` is nontrivial: `|K| = |Inv H| ≥ 2` (Ch. I §2 + the four-group of `(B0)`). -/
theorem exists_mem_Kset_ne_one (hS : Situation G) (h : IsSplitRankOne H Q t) :
    ∃ x : G, x ∈ Work.ThmF.Kset H t ∧ x ≠ 1 := by
  obtain ⟨hfour, -⟩ := hS.1
  have h2 := Bender.cardInvGeTwo h.stronglyEmbedded hfour
  have hcard := Bender.cardKsetEqInv h.stronglyEmbedded h.invol h.not_mem
  have hlt : 1 < (Work.ThmF.Kset H t).ncard := by
    rw [hcard]; omega
  obtain ⟨x, hx, hx1⟩ := Set.exists_ne_of_one_lt_ncard hlt 1
  exact ⟨x, hx, hx1⟩

/-- **Ch. V §1 Prop. 1 (b)**: `Q` is nilpotent. -/
theorem Q_nilpotent (hS : Situation G) (hC4 : ChIIFourProp) (h : IsSplitRankOne H Q t) :
    Group.IsNilpotent ↥Q :=
  ChV12.prop1b hS hC4 thompsonFrobenius H Q t h (exists_mem_Kset_ne_one hS h)

/-- **Ch. V §1 Prop. 1 (c)**: the involutions of `H` commute pairwise. -/
theorem involutions_commute (hS : Situation G) (hC4 : ChIIFourProp) (h : IsSplitRankOne H Q t) :
    ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G), a * b = b * a := by
  have hD : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
      ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b :=
    Bender.DTransitiveInv h.stronglyEmbedded h.invol h.not_mem
  have hc := ChV12.prop1c hS H Q t h hD (Q_nilpotent hS hC4 h)
  intro a ha b hb
  exact (mem_centerOf.mp (hc a ha)).2 b (mem_centerOf.mp (hc b hb)).1

/-- `Q₀sub H = Q₀ H` as sets, when the involutions of `H` commute. -/
theorem Q0sub_eq_Q0 (hcomm : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
    a * b = b * a) : (Work.ThmF.Q0sub H : Set G) = Work.ThmF.Q0 H := by
  obtain ⟨-, -, -, hlast⟩ := ChV12.Q0sub_elementary H hcomm
  refine Set.Subset.antisymm ?_ (Work.ThmF.Q0_le_Q0sub H)
  intro x hx
  by_cases h1 : x = 1
  · rw [h1]; exact Work.ThmF.one_mem_Q0 H
  · exact Or.inl (hlast x hx h1)

/-- `Q₀sub H` is an elementary abelian `2`-group, and every non-identity element of it is an
involution of `H`. -/
theorem Q0sub_elementary (hcomm : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
    a * b = b * a) :
    (∀ x ∈ Work.ThmF.Q0sub H, x * x = 1) ∧
      (∀ x ∈ Work.ThmF.Q0sub H, ∀ y ∈ Work.ThmF.Q0sub H, x * y = y * x) ∧
      (∀ x ∈ Work.ThmF.Q0sub H, x ≠ 1 → x ∈ involutions (H : Set G)) := by
  obtain ⟨h1, h2, -, h4⟩ := ChV12.Q0sub_elementary H hcomm
  exact ⟨h1, h2, h4⟩

/-- `|Q₀sub H| = |Inv H| + 1` when the involutions of `H` commute. -/
theorem card_Q0sub_eq (hcomm : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
    a * b = b * a) :
    Nat.card ↥(Work.ThmF.Q0sub H) = (involutions (H : Set G)).ncard + 1 := by
  have hset := Q0sub_eq_Q0 (H := H) hcomm
  have hcard : Nat.card ↥(Work.ThmF.Q0sub H) = (Work.ThmF.Q0 H).ncard := by
    rw [← Set.ncard_univ (α := ↥(Work.ThmF.Q0sub H)), Set.ncard_coe, hset]
  rw [hcard, Work.ThmF.Q0]
  have hnot : (1 : G) ∉ involutions (H : Set G) := by
    simp [involutions, orderOf_one]
  have hdisj : Disjoint (involutions (H : Set G)) ({1} : Set G) := by
    rw [Set.disjoint_singleton_right]; exact hnot
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton]

/-- `K = J(D,t)` acts regularly on the involutions of `H` (Ch. I §2, Lemma 1 + Prop. 1 (c)):
for `a, b ∈ Inv H` there is a unique `k ∈ K` with `k a k⁻¹ = b`. -/
theorem Kset_regular (h : IsSplitRankOne H Q t) :
    ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
      ∃! k : G, k ∈ Work.ThmF.Kset H t ∧ k * a * k⁻¹ = b := by
  intro a ha b hb
  have hcard : (Work.ThmF.Kset H t).ncard = (involutions (H : Set G)).ncard :=
    Bender.cardKsetEqInv h.stronglyEmbedded h.invol h.not_mem
  have hmaps : ∀ x ∈ Work.ThmF.Kset H t, x * a * x⁻¹ ∈ involutions (H : Set G) := by
    intro x hx
    have hxH : x ∈ H :=
      (Subgroup.mem_inf.mp (Work.ThmF.Kset_subset H t hx)).1
    exact ⟨H.mul_mem (H.mul_mem hxH ha.1) (H.inv_mem hxH),
      by rw [Bender.orderOf_conj_eq, ha.2]⟩
  have hinj : Set.InjOn (fun x => x * a * x⁻¹) (Work.ThmF.Kset H t) :=
    Bender.Kset_conj_injective h.stronglyEmbedded h.invol h.not_mem ha.1 ha.2
  have himg : ((fun x => x * a * x⁻¹) '' (Work.ThmF.Kset H t)).ncard
      = (involutions (H : Set G)).ncard := by
    rw [Set.InjOn.ncard_image hinj, hcard]
  have hsub : (fun x => x * a * x⁻¹) '' (Work.ThmF.Kset H t) ⊆ involutions (H : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps x hx
  have hset : (fun x => x * a * x⁻¹) '' (Work.ThmF.Kset H t) = involutions (H : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq himg.symm)
  obtain ⟨k, hk, hkab⟩ := hset ▸ hb
  exact ⟨k, ⟨hk, hkab⟩,
    fun k' ⟨hk', hk'ab⟩ => hinj hk' hk (by
      show k' * a * k'⁻¹ = k * a * k⁻¹
      rw [hk'ab]
      show b = k * a * k⁻¹
      rw [← hkab])⟩

end Work.ThmF.L5
