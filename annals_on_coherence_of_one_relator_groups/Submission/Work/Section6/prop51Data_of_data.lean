/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# [JZLA20, Proposition 5.1]: the data of the proposition from the data of [JZLA20, Theorem 6.1]

This file assembles the `Prop51Data (Kˣ × H) P DN` of [JZLA20, Proposition 5.1] out of the data
supplied by the induction step of [JZLA20, Theorem 6.1] (see `PlanStep.md`, Step B): a ring `P`
containing the skew Laurent series ring `A((t;τ))` over `DN = D_{N,P}` (`laurentEmbed`), the ring
homomorphism `φP : K[H] →+* P`, and the two inclusions

* `DN ≤ D_{H,P}`, where `D_{H,P}` is the division closure of `φP(K[H])` in `P`, and
* `φP(K[N]) ⊆ DN`,

together with the identification `Φ(t) = laurentEmbed (t-variable)` and the group-theoretic facts
`H = N · ⟨t⟩`, `t^k N t^{-k} ⊆ N`.

Every remaining field of `Prop51Data` is then *constructed*: the universal morphism
`Φ : Rat(Kˣ × H) →+* P` is `D_{H,P} ↪ P` composed with `Phi φP`, its rational-semiring
compatibility is `Phi_isRational`, the `H`-complexity is `treeG φP` (extended by `0` off the
division closure, `treeHClosure`), and the three `⋄`-properties are the definitional properties of
`ratOpClosure`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Prop51
import Submission.Work.ORHughesFree.Section6.RatStruct
import Submission.Work.ORHughesFree.Section6.TreeG
import Submission.Work.ORHughesFree.Section6.ClosureBasic
import Submission.Work.ORHughesFree.Section6.ratOpClosure_spec
import Submission.Work.ORHughesFree.Section6.UnitOf
import Submission.Work.ORHughesFree.Section6.Reduce
import Submission.Work.ORHughesFree.DivisionClosure.inverse_mem_divisionClosure
import Submission.Work.Section6.unitsTimesSubgroup_conj
import Submission.Work.Section6.exists_prod_decomp
import Submission.Work.Section6.unitsTimesSubgroup_conj_of_conj
import Submission.Work.Section6.Phi_ofGroup_neg_one
import Submission.Work.Section6.Phi_ofGroup_mem_of_N
import Submission.Work.Section6.Phi_ofGroup_t
import Submission.Work.Section6.divisionClosure_inv_closed
import Submission.Work.Section6.codRestrict_subtype_comp_Phi

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Section6

open Work.ORHughesFree

/-! ## Auxiliary computations -/

/-- The `H`-complexity of [JZLA20, §4.3], extended to a total function on `U` by `0` off the
division closure `D = D_{K[G],U}`: on `D` it is `treeG φ`. -/
noncomputable def treeHClosure {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) : U → Tree := fun a => by
  classical
  exact if h : a ∈ divisionClosure (Set.range φ) then treeG φ ⟨a, h⟩ else 0

/-- The characteristic property of `treeHClosure` on the division closure: it is realised and it is
the minimum of `Rat.treeOfRat` over the realisers. -/
theorem treeHClosure_spec {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (a : U)
    (ha : a ∈ divisionClosure (Set.range φ)) :
    (∃ α : RatU (Kˣ × G),
      ((divisionClosure (Set.range φ)).subtype.comp (Phi φ)) α = a ∧
      Rat.treeOfRat (Kˣ × G) α = treeHClosure φ a) ∧
    ∀ β : RatU (Kˣ × G),
      ((divisionClosure (Set.range φ)).subtype.comp (Phi φ)) β = a →
      Tree.le (treeHClosure φ a) (Rat.treeOfRat (Kˣ × G) β) := by
  have htree : treeHClosure φ a = treeG φ ⟨a, ha⟩ := dif_pos ha
  obtain ⟨⟨α, hα, hαt⟩, hmin⟩ := treeG_spec φ ⟨a, ha⟩
  refine ⟨⟨α, ?_, ?_⟩, ?_⟩
  · exact congrArg Subtype.val hα
  · rw [htree]; exact hαt
  · intro β hβ
    rw [htree]
    exact hmin β (Subtype.ext hβ)

/-! ## The main statement -/

theorem prop51Data_of_data {K : Type} [Field K] {H : Type} [Group H]
    (N : Subgroup H) (t : H)
    {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN]
    (nontrivDN : Nontrivial ↥DN)
    (DN_inv_closed : ∀ x ∈ DN, IsUnit x → ∃ y ∈ DN, x * y = 1 ∧ y * x = 1)
    (laurentEmbed : Work.ORHughesFree.SkewLaurentSeries ↥DN →+* P)
    (laurentEmbed_injective : Function.Injective laurentEmbed)
    (laurentEmbed_coeff : ∀ d : ↥DN,
      laurentEmbed (Work.ORHughesFree.skewLaurentCoeff ↥DN d) = (d : P))
    (φP : MonoidAlgebra K H →+* P)
    (hleDN : DN ≤ Work.ORHughesFree.divisionClosure (Set.range φP))
    (hNmem : ∀ x : MonoidAlgebra K ↥N,
      φP (MonoidAlgebra.mapDomainRingHom K N.subtype x) ∈ DN)
    (ht : φP (MonoidAlgebra.single t (1 : K)) =
      laurentEmbed (Work.ORHughesFree.skewLaurentSeriesT ↥DN :
        Work.ORHughesFree.SkewLaurentSeries ↥DN))
    (hdecomp : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k)
    (hconj : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N) :
    Nonempty (Work.ORHughesFree.Prop51Data (Kˣ × H) P DN) := by
  classical
  -- the division closure `D_{H,P}` and the universal morphism `Φ`
  let DH : Subring P := divisionClosure (Set.range φP)
  let Φ : RatU (Kˣ × H) →+* P := DH.subtype.comp (Phi φP)
  have hNontrivDH : Nontrivial ↥DH := by
    obtain ⟨x, y, hxy⟩ := nontrivDN.exists_pair_ne
    exact ⟨⟨(x : P), hleDN x.2⟩, ⟨(y : P), hleDN y.2⟩,
      fun h => hxy (Subtype.ext (congrArg (fun z : ↥DH => (z : P)) h))⟩
  have hmap_mem : ∀ α : RatU (Kˣ × H), Φ α ∈ DH := fun α => (Phi φP α).2
  have hΦ_rat : IsRationalUSemiringHom (RatU.rational) (ratStruct φP)
      (Φ.codRestrict DH hmap_mem) := by
    have hcod : Φ.codRestrict DH hmap_mem = Phi φP := codRestrict_subtype_comp_Phi φP
    rw [hcod]
    exact Phi_isRational φP
  have hratOp_zero : (ratStruct φP).ratOp 0 = 0 := (ratStruct φP).ratOp_zero
  have hratOp_of_isUnit : ∀ x : ↥DH, IsUnit x → x * (ratStruct φP).ratOp x = 1 := by
    intro x hx
    rw [ratStruct_ratOp]
    exact (Work.ORHughesFree.Section6.ratOpClosure_spec DH hNontrivDH).2.1 x hx
  have hratOp_ne_zero : ∀ x : ↥DH, (ratStruct φP).ratOp x ≠ 0 → IsUnit x := by
    intro x hx
    by_contra h
    refine hx ?_
    rw [ratStruct_ratOp]
    unfold ratOpClosure
    rw [dif_neg h]
  have hN_conj : ∀ (k : ℤ) (n : Kˣ × H),
      n ∈ unitsTimesSubgroup (K := K) N →
      (((1 : Kˣ), t) : Kˣ × H) ^ k * n * (((1 : Kˣ), t) : Kˣ × H) ^ (-k) ∈
        unitsTimesSubgroup (K := K) N :=
    unitsTimesSubgroup_conj_of_conj (K := K) N t hconj
  have hdecomp' : ∀ u : Kˣ × H, ∃ (n : Kˣ × H) (k : ℤ),
      n ∈ unitsTimesSubgroup (K := K) N ∧ u = n * (((1 : Kˣ), t) : Kˣ × H) ^ k :=
    exists_prod_decomp (K := K) N t hdecomp
  have hΦ_N : ∀ u : Kˣ × H, u ∈ unitsTimesSubgroup (K := K) N →
      Φ (RatU.ofGroup u) ∈ DN :=
    fun u hu => Phi_ofGroup_mem_of_N φP N hNmem u hu
  have hΦ_t : Φ (RatU.ofGroup ((1 : Kˣ), t)) =
      laurentEmbed (skewLaurentSeriesT ↥DN : SkewLaurentSeries ↥DN) :=
    Phi_ofGroup_t φP t laurentEmbed ht
  have hPhi_neg_one : ∃ u : Kˣ × H, Φ (RatU.ofGroup u) = -1 := Phi_ofGroup_neg_one φP
  refine ⟨{
    nontrivialDN := nontrivDN
    DN_inv_closed := DN_inv_closed
    DH := DH
    le_DN_DH := hleDN
    DH_inv_closed := divisionClosure_inv_closed (Set.range φP)
    Φ := Φ
    map_mem := hmap_mem
    treeH := treeHClosure φP
    treeH_spec := treeHClosure_spec φP
    rDH := ratStruct φP
    Φ_rat := hΦ_rat
    ratOp_zero := hratOp_zero
    ratOp_of_isUnit := hratOp_of_isUnit
    laurentEmbed := laurentEmbed
    laurentEmbed_injective := laurentEmbed_injective
    laurentEmbed_coeff := laurentEmbed_coeff
    N := unitsTimesSubgroup (K := K) N
    t := ((1 : Kˣ), t)
    decomp := hdecomp'
    Φ_N := hΦ_N
    Φ_t := hΦ_t
    Phi_neg_one := hPhi_neg_one
    N_conj := hN_conj
    ratOp_ne_zero := hratOp_ne_zero }⟩

end Work.Section6
