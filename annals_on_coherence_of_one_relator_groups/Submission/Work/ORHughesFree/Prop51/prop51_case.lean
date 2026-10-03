import Mathlib
import Submission.Work.ORHughesFree.Prop51
import Submission.Work.ORHughesFree.Prop51.ConclB
import Submission.Work.ORHughesFree.Prop51.conj
import Submission.Work.ORHughesFree.Tree.exp_mono
import Submission.Work.ORHughesFree.Prop51.base_case
import Submission.Work.ORHughesFree.Prop51.ofGroup_t_pow
import Submission.Work.ORHughesFree.RatU.exists_decomp
import Submission.Work.ORHughesFree.RatU.isWord_wid
import Submission.Work.ORHughesFree.Prop51.conclB_add
import Submission.Work.ORHughesFree.Prop51.conclB_mul
import Submission.Work.ORHughesFree.Prop51.conclB_ratOp

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORHughesFree.Prop51

open Work.ORHughesFree

/-- Transitivity of the DHS04 tree order in the mixed form `a ≤ b < c → a < c`. -/
theorem lt_of_le_of_lt_Tree {a b c : Tree} (h1 : Tree.le a b) (h2 : Tree.lt b c) :
    Tree.lt a c := by
  rcases h1 with rfl | h1
  · exact h2
  · refine Tree.lt_of_le_of_ne (Tree.le_trans (Tree.le_of_lt h1) (Tree.le_of_lt h2)) ?_
    intro heq
    have hcb : Tree.lt c b := heq ▸ h1
    have hbc : Tree.lt b c := h2
    have : c = b := Tree.le_antisymm (Tree.le_of_lt hcb) (Tree.le_of_lt hbc)
    exact Tree.lt_irrefl (this ▸ hbc)


variable {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
  [MulSemiringAction (Multiplicative ℤ) ↥DN]

theorem conclB_zero' (d : Prop51Data Γ P DN) (T : Tree) : ConclB d 0 T := by
  refine ⟨0, map_zero d.laurentEmbed, fun k => ?_, fun k _ j _ => rfl⟩
  have hc : d.coeffToP ((0 : SkewLaurentSeries ↥DN).1 k) = 0 := rfl
  rw [hc, treeH_zero d]
  exact Tree.le_zero T

theorem lt_of_lt_of_le_Tree {a b c : Tree} (h1 : Tree.lt a b) (h2 : Tree.le b c) : Tree.lt a c := by
  rcases h2 with h2 | h2
  · rw [h2] at h1; exact h1
  · exact Tree.lt_trans h1 h2

theorem lt_of_not_le_Tree {a b : Tree} (h : ¬ Tree.le b a) : Tree.lt a b := by
  rcases Tree.le_total a b with hle | hle
  · refine Tree.lt_of_le_of_ne hle (fun hab => h ?_)
    rw [← hab]
    exact Tree.le_refl a
  · exact absurd hle h

/-- The `H`-complexity of `Φ y` is at most `Tree y`: this is the general form used below. -/
theorem lt_treeH_Phi_of_lt {d : Prop51Data Γ P DN} {a b : P} {β y : RatU Γ}
    (hle : Tree.le (d.treeH b) (d.treeH a)) (htree : Rat.treeOfRat Γ β = d.treeH b)
    (hβ : d.Φ β = b) (hy : Tree.lt (Rat.treeOfRat Γ y) (Rat.treeOfRat Γ β)) :
    Tree.lt (d.treeH (d.Φ y)) (d.treeH a) := by
  have h1 : Tree.lt (d.treeH (d.Φ y)) (Rat.treeOfRat Γ β) :=
    Tree.lt_of_le_of_lt' (d.treeH_le_treeOfRat y) hy
  refine lt_of_lt_of_le_Tree h1 ?_
  rw [htree]; exact hle

/-- **[JZLA20, Proposition 5.1]**, the induction step.  Assuming the conclusion for every
`b' ∈ D_{H,P}` of strictly smaller `H`-complexity than `a` (`hsmall`), every `b ∈ D_{H,P}` with
`Tree_H b ≤ Tree_H a` which is realised by `β ∈ Rat(E × H)` of complexity exactly `Tree_H b`
satisfies `Prop51Concl d b`.

The proof decomposes `β` along the four clauses of `RatU.exists_decomp` and uses the three
transfer lemmas `conclB_add`, `conclB_mul`, `conclB_ratOp` for the sums, products and `⋄`'s of
`Rat(E × H)`; the crucial points are that the pieces of the decomposition have strictly smaller
complexity (so that `hsmall` applies to them, since `treeH ≤ Tree` is monotone) and that they
*realise* the `H`-complexity of their images (otherwise a smaller realisation of a piece would
give a smaller realisation of `β`, contradicting its minimality `d.treeH_spec`). -/
theorem prop51_case {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Prop51Data Γ P DN)
    {a b : P}
    (hsmall : ∀ (b' : P) (_ : b' ∈ d.DH),
      Tree.lt (d.treeH b') (d.treeH a) → Prop51Concl d b')
    (hinv : Prop51Inv d a)
    (hb : b ∈ d.DH) (hle : Tree.le (d.treeH b) (d.treeH a))
    (β : RatU Γ) (hβ : d.Φ β = b) (htree : Rat.treeOfRat Γ β = d.treeH b) :
    Prop51Concl d b := by
  refine (prop51Concl_iff_conclB d b).mpr ?_
  by_cases hlt : Tree.lt (d.treeH b) (d.treeH a)
  · exact (prop51Concl_iff_conclB d b).mp (hsmall b hb hlt)
  · rcases eq_or_ne β 0 with hβ0 | hβne
    · rw [hβ0, map_zero] at hβ
      rw [← hβ]
      exact conclB_zero' d _
    · rcases RatU.exists_decomp β hβne with hgrp | hprod | hsum | hrat
      · -- group case
        obtain ⟨u, hu⟩ := hgrp
        rcases d.decomp u with ⟨n, k, hn, huk⟩
        rw [← hβ, hu]
        exact (prop51Concl_iff_conclB d _).mp (base_case d u n k hn huk)
      · -- product case
        obtain ⟨y, z, hyz, hyw, hzw, hylt, hzlt⟩ := hprod
        have hcle : Tree.lt (d.treeH (d.Φ y)) (d.treeH a) :=
          lt_treeH_Phi_of_lt hle htree hβ hylt
        have hcle' : Tree.lt (d.treeH (d.Φ z)) (d.treeH a) :=
          lt_treeH_Phi_of_lt hle htree hβ hzlt
        have hCy : ConclB d (d.Φ y) (d.treeH (d.Φ y)) :=
          (prop51Concl_iff_conclB d (d.Φ y)).mp (hsmall (d.Φ y) (d.map_mem y) hcle)
        have hCz : ConclB d (d.Φ z) (d.treeH (d.Φ z)) :=
          (prop51Concl_iff_conclB d (d.Φ z)).mp (hsmall (d.Φ z) (d.map_mem z) hcle')
        have hz0 : z ≠ 0 := RatU.isWord_ne_zero' hzw
        have hminy : d.treeH (d.Φ y) = Rat.treeOfRat Γ y := by
          refine Tree.le_antisymm (d.treeH_le_treeOfRat y) ?_
          by_contra hcon
          have hlt' := lt_of_not_le_Tree hcon
          obtain ⟨γ, hγ, hγt⟩ := d.exists_realizing (d.map_mem y)
          have hΦ : d.Φ (γ * z) = b := by rw [map_mul, hγ, ← hβ, hyz, map_mul]
          have hbnd := (d.treeH_spec b hb).2 (γ * z) hΦ
          rw [Rat.treeOfRat_mul, hγt] at hbnd
          have hyz' : Rat.treeOfRat Γ y * Rat.treeOfRat Γ z = d.treeH b := by
            rw [← Rat.treeOfRat_mul, ← hyz, htree]
          have hz0' : Rat.treeOfRat Γ z ≠ 0 :=
            fun h => hz0 ((Rat.treeOfRat_eq_zero_iff Γ z).mp h)
          have h1 : Tree.lt (d.treeH (d.Φ y) * Rat.treeOfRat Γ z) (d.treeH b) := by
            rw [← hyz']
            exact Tree.lt_mul_right hlt' hz0'
          exact Tree.lt_irrefl (Tree.lt_of_le_of_lt' hbnd h1)
        have hy0 : y ≠ 0 := RatU.isWord_ne_zero' hyw
        have hminz : d.treeH (d.Φ z) = Rat.treeOfRat Γ z := by
          refine Tree.le_antisymm (d.treeH_le_treeOfRat z) ?_
          by_contra hcon
          have hlt' := lt_of_not_le_Tree hcon
          obtain ⟨γ, hγ, hγt⟩ := d.exists_realizing (d.map_mem z)
          have hΦ : d.Φ (y * γ) = b := by
            rw [map_mul, hγ, ← hβ, hyz, map_mul]
          have hbnd := (d.treeH_spec b hb).2 (y * γ) hΦ
          rw [Rat.treeOfRat_mul, hγt] at hbnd
          have hyz' : Rat.treeOfRat Γ y * Rat.treeOfRat Γ z = d.treeH b := by
            rw [← Rat.treeOfRat_mul, ← hyz, htree]
          have hy0' : Rat.treeOfRat Γ y ≠ 0 :=
            fun h => hy0 ((Rat.treeOfRat_eq_zero_iff Γ y).mp h)
          have h1 : Tree.lt (Rat.treeOfRat Γ y * d.treeH (d.Φ z)) (d.treeH b) := by
            rw [← hyz']
            exact Tree.lt_mul_left hlt' hy0'
          exact Tree.lt_irrefl (Tree.lt_of_le_of_lt' hbnd h1)
        have hT₁ : d.treeH (d.Φ y) ≠ 0 := by
          rw [hminy]
          exact fun h => hy0 ((Rat.treeOfRat_eq_zero_iff Γ y).mp h)
        have hT₂ : d.treeH (d.Φ z) ≠ 0 := by
          rw [hminz]
          exact fun h => hz0 ((Rat.treeOfRat_eq_zero_iff Γ z).mp h)
        have hw₁ : Tree.wid (d.treeH (d.Φ y)) = 1 := by
          rw [hminy]; exact RatU.isWord_wid hyw
        have hw₂ : Tree.wid (d.treeH (d.Φ z)) = 1 := by
          rw [hminz]; exact RatU.isWord_wid hzw
        have hce : d.Φ y * d.Φ z = b := by rw [← hβ, hyz, map_mul]
        have hmulC : ConclB d (d.Φ y * d.Φ z) (d.treeH (d.Φ y) * d.treeH (d.Φ z)) :=
          conclB_mul d hCy hCz hT₁ hT₂ hw₁ hw₂
        have hbound : d.treeH (d.Φ y) * d.treeH (d.Φ z) = d.treeH b := by
          rw [hminy, hminz, ← Rat.treeOfRat_mul, ← hyz, htree]
        rw [← hbound, ← hce]
        exact hmulC
      · -- sum case
        obtain ⟨y, z, hyz, hy0, hz0, hylt, hzlt⟩ := hsum
        have hcle : Tree.lt (d.treeH (d.Φ y)) (d.treeH a) :=
          lt_treeH_Phi_of_lt hle htree hβ hylt
        have hcle' : Tree.lt (d.treeH (d.Φ z)) (d.treeH a) :=
          lt_treeH_Phi_of_lt hle htree hβ hzlt
        have hCy : ConclB d (d.Φ y) (d.treeH (d.Φ y)) :=
          (prop51Concl_iff_conclB d (d.Φ y)).mp (hsmall (d.Φ y) (d.map_mem y) hcle)
        have hCz : ConclB d (d.Φ z) (d.treeH (d.Φ z)) :=
          (prop51Concl_iff_conclB d (d.Φ z)).mp (hsmall (d.Φ z) (d.map_mem z) hcle')
        have hminy : d.treeH (d.Φ y) = Rat.treeOfRat Γ y := by
          refine Tree.le_antisymm (d.treeH_le_treeOfRat y) ?_
          by_contra hcon
          have hlt' := lt_of_not_le_Tree hcon
          obtain ⟨γ, hγ, hγt⟩ := d.exists_realizing (d.map_mem y)
          have hΦ : d.Φ (γ + z) = b := by rw [map_add, hγ, ← hβ, hyz, map_add]
          have hbnd := (d.treeH_spec b hb).2 (γ + z) hΦ
          rw [Rat.treeOfRat_add, hγt] at hbnd
          have hyz' : Rat.treeOfRat Γ y + Rat.treeOfRat Γ z = d.treeH b := by
            rw [← Rat.treeOfRat_add, ← hyz, htree]
          have h1 : Tree.lt (d.treeH (d.Φ y) + Rat.treeOfRat Γ z) (d.treeH b) := by
            rw [← hyz']
            exact Tree.lt_add_right hlt' _
          exact Tree.lt_irrefl (Tree.lt_of_le_of_lt' hbnd h1)
        have hminz : d.treeH (d.Φ z) = Rat.treeOfRat Γ z := by
          refine Tree.le_antisymm (d.treeH_le_treeOfRat z) ?_
          by_contra hcon
          have hlt' := lt_of_not_le_Tree hcon
          obtain ⟨γ, hγ, hγt⟩ := d.exists_realizing (d.map_mem z)
          have hΦ : d.Φ (y + γ) = b := by rw [map_add, hγ, ← hβ, hyz, map_add]
          have hbnd := (d.treeH_spec b hb).2 (y + γ) hΦ
          rw [Rat.treeOfRat_add, hγt] at hbnd
          have hyz' : Rat.treeOfRat Γ y + Rat.treeOfRat Γ z = d.treeH b := by
            rw [← Rat.treeOfRat_add, ← hyz, htree]
          have h1 : Tree.lt (Rat.treeOfRat Γ y + d.treeH (d.Φ z)) (d.treeH b) := by
            rw [← hyz']
            exact Tree.lt_add_left hlt'
          exact Tree.lt_irrefl (Tree.lt_of_le_of_lt' hbnd h1)
        have hce : d.Φ y + d.Φ z = b := by rw [← hβ, hyz, map_add]
        have hsumC : ConclB d (d.Φ y + d.Φ z) (d.treeH (d.Φ y) + d.treeH (d.Φ z)) :=
          conclB_add d hCy hCz
        have hbound : d.treeH (d.Φ y) + d.treeH (d.Φ z) = d.treeH b := by
          rw [hminy, hminz, ← Rat.treeOfRat_add, ← hyz, htree]
        rw [← hbound, ← hce]
        exact hsumC
      · -- ⋄ case
        obtain ⟨y, hy, hylt⟩ := hrat
        have hy0 : y ≠ 0 := fun h => hβne (by rw [hy, h]; exact (RatU.rational (U := Γ)).ratOp_zero)
        have hcle : Tree.lt (d.treeH (d.Φ y)) (d.treeH a) :=
          lt_treeH_Phi_of_lt hle htree hβ hylt
        have hCy : ConclB d (d.Φ y) (d.treeH (d.Φ y)) :=
          (prop51Concl_iff_conclB d (d.Φ y)).mp (hsmall (d.Φ y) (d.map_mem y) hcle)
        have hkey : d.rDH.ratOp (⟨d.Φ y, d.map_mem y⟩ : ↥d.DH)
            = (d.Φ.codRestrict d.DH d.map_mem) (RatU.rational.ratOp y) := by
          rw [d.Φ_rat.map_rat y]
          rfl
        have hrat_eq : ((d.rDH.ratOp (⟨d.Φ y, d.map_mem y⟩ : ↥d.DH) : ↥d.DH) : P) = b := by
          rw [← hβ, hy]
          rw [hkey]
          rfl
        have hminy : d.treeH (d.Φ y) = Rat.treeOfRat Γ y := by
          refine Tree.le_antisymm (d.treeH_le_treeOfRat y) ?_
          by_contra hcon
          have hlt' := lt_of_not_le_Tree hcon
          obtain ⟨γ, hγ, hγt⟩ := d.exists_realizing (d.map_mem y)
          have hEl : (d.Φ.codRestrict d.DH d.map_mem) (RatU.rational.ratOp γ)
              = (⟨b, hb⟩ : ↥d.DH) := by
            rw [d.Φ_rat.map_rat γ]
            rw [show (d.Φ.codRestrict d.DH d.map_mem) γ = (⟨d.Φ y, d.map_mem y⟩ : ↥d.DH)
              from Subtype.ext hγ]
            exact Subtype.ext hrat_eq
          have hΦ : d.Φ (RatU.rational.ratOp γ) = b := congrArg Subtype.val hEl
          have hbnd := (d.treeH_spec b hb).2 (RatU.rational.ratOp γ) hΦ
          have hbnd' : Tree.le (d.treeH b) (Tree.exp (Tree.exp (Rat.treeOfRat Γ γ))) :=
            Tree.le_trans hbnd (Rat.treeOfRat_rat_le Γ γ)
          rw [hγt] at hbnd'
          have hyz' : Tree.exp (Tree.exp (Rat.treeOfRat Γ y)) = d.treeH b := by
            rw [← Rat.treeOfRat_rat_rational hy0, ← hy, htree]
          have h1 : Tree.lt (Tree.exp (Tree.exp (d.treeH (d.Φ y)))) (d.treeH b) := by
            rw [← hyz']
            exact Tree.exp_lt_exp (Tree.exp_lt_exp hlt')
          exact Tree.lt_irrefl (Tree.lt_of_le_of_lt' hbnd' h1)
        have hunit : ∀ (f : SkewLaurentSeries ↥DN), d.laurentEmbed f = d.Φ y → ∀ k : ℤ,
            f.1 k ≠ 0 → IsUnit (f.1 k) := by
          intro f hf k hk
          obtain ⟨g, hg, hgb, -⟩ := hCy
          have hfg : f = g := d.laurentEmbed_injective (by rw [hf, hg])
          rw [← hfg] at hgb
          have hlt' : Tree.lt (d.treeH (d.coeffToP (f.1 k))) (d.treeH a) :=
            lt_of_le_of_lt_Tree (hgb k) hcle
          have hne : d.coeffToP (f.1 k) ≠ 0 := fun h => hk (Subtype.ext h)
          have hneT : d.treeH (d.coeffToP (f.1 k)) ≠ d.treeH a := by
            intro heq
            rw [heq] at hlt'
            exact Tree.lt_irrefl hlt'
          obtain ⟨z, hz, hz1, hz2⟩ :=
            hinv (d.coeffToP (f.1 k)) (d.coeffToP_mem (f.1 k)) hne
              (Tree.le_of_lt hlt') hneT
          have hunitP : IsUnit ((f.1 k : ↥DN) : P) :=
            ⟨⟨((f.1 k : ↥DN) : P), (z : P), hz1, hz2⟩, rfl⟩
          obtain ⟨w, hw, hw1, hw2⟩ :=
            d.DN_inv_closed ((f.1 k : ↥DN) : P) (f.1 k).2 hunitP
          exact ⟨⟨f.1 k, ⟨w, hw⟩, Subtype.ext hw1, Subtype.ext hw2⟩, rfl⟩
        have hratC : ConclB d ((d.rDH.ratOp ⟨d.Φ y, d.map_mem y⟩ : ↥d.DH) : P)
            (Tree.exp (Tree.exp (d.treeH (d.Φ y)))) :=
          conclB_ratOp d (d.map_mem y) hCy hunit
        have hbound : Tree.exp (Tree.exp (d.treeH (d.Φ y))) = d.treeH b := by
          rw [hminy, ← Rat.treeOfRat_rat_rational hy0, ← hy, htree]
        rw [← hbound, ← hrat_eq]
        exact hratC

end Work.ORHughesFree.Prop51
