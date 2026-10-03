import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.Psi_mem_A_iff
import Submission.Work.ORHughesFree.Rat.mem_ofGroup_mul_A_iff
import Submission.Work.ORHughesFree.Rat.Xgen_mem_closure_iff
import Submission.Work.ORHughesFree.RatU.exists_decomp
import Submission.Work.ORHughesFree.Rat.treeOrderFacts
import Submission.Work.ORHughesFree.Rat.Dich.isWord_letter_decomp
import Submission.Work.ORHughesFree.Rat.Dich.exists_good_rep
import Submission.Work.ORHughesFree.Rat.Dich.descent_R
import Submission.Work.ORHughesFree.Rat.Dich.descent_L

/-!
# The translate dichotomy (a private copy, free of the `Src` import)

This is a copy of `Rat/Dich/ofGroup_mul_A_eq_V_or_univ.lean` (the translate dichotomy
`Rat.Dich.both_of_ne_zero`), *without* the (unused) import of `Rat/Src/exists_inP_mul_ofGroup`.
That import leads to `Rat/source_subgroup_exists`, which must import `Rat/Source/Setup`, so
leaking it into `Setup` would create an import cycle.  The mathematics is unchanged (the names
deliberately coincide with the original's, which nothing imports together with this copy).

Do not import this module in the same file as
`Submission.Work.ORHughesFree.Rat.Dich.ofGroup_mul_A_eq_V_or_univ`.
-/

set_option autoImplicit false

namespace Work.ORHughesFree.Rat.Dich

open Work.ORHughesFree
open Work.ORHughesFree.Rat
open Work.ORHughesFree.Rat.FreeProduct

variable {U : Type} [Group U]

/-- **The translate dichotomy for a non-zero element `x` of `Rat(U)`**: every left and every right
translate of `x` that lies in `Rat.A V` comes from an element of `V`. -/
def Both (x : RatU U) : Prop :=
  (∀ V : Subgroup U, ∀ w : U, x ∈ A V → x * RatU.ofGroup w ∈ A V → w ∈ V) ∧
    (∀ V : Subgroup U, ∀ w : U, x ∈ A V → RatU.ofGroup w * x ∈ A V → w ∈ V)

/-- The induction hypothesis of the main theorem at a complexity bound `T`: the translate
dichotomy holds for every non-zero element of complexity below `T` (at a fixed subgroup `V`). -/
def ISS (V : Subgroup U) (T : Tree) : Prop :=
  ∀ y : RatU U, Tree.lt (Rat.treeOfRat U y) T → y ≠ 0 →
    ((∀ w : U, y ∈ A V → y * RatU.ofGroup w ∈ A V → w ∈ V) ∧
     (∀ w : U, y ∈ A V → RatU.ofGroup w * y ∈ A V → w ∈ V))

/-- The support of the monomial `single p 1` is `{p}`. -/
theorem support_single_one (M : Type) [Monoid M] (p : M) :
    (MonoidAlgebra.single p (1 : ℕ)).coeff.support = {p} := by
  ext q
  constructor
  · intro hq
    exact Finsupp.support_single_subset hq
  · intro hq
    rw [Finset.mem_singleton] at hq
    subst hq
    rw [Finsupp.mem_support_iff, MonoidAlgebra.coeff_single]
    simp

/-- `φ w ∈ Rat.A V` iff `w ∈ V`. -/
theorem ofGroup_mem_A_iff' (V : Subgroup U) (w : U) :
    RatU.ofGroup w ∈ A V ↔ w ∈ V :=
  ⟨fun h => Weak.ofGroup_mem_A_weak h, fun h => Weak.A_ofGroup_mem h⟩

/-- **The translate dichotomy for all non-zero elements.** -/
theorem both_of_ne_zero (x : RatU U) (hx0 : x ≠ 0) : Both x := by
  have key : ∀ t : Tree, ∀ x : RatU U, Rat.treeOfRat U x = t → x ≠ 0 → Both x := by
    intro t
    induction t using Tree.lt_wf.induction with
    | _ t ih =>
      intro x hxt hx0
      have hISS : ∀ V : Subgroup U, ISS V t := fun V y hy hy0 =>
        ⟨(ih (Rat.treeOfRat U y) hy y rfl hy0).1 V, (ih (Rat.treeOfRat U y) hy y rfl hy0).2 V⟩
      rcases RatU.exists_decomp x hx0 with
        ⟨u, rfl⟩ | ⟨y, z, rfl, hyw, hzw, hlt1, hlt2⟩ |
          ⟨y, z, rfl, hy0, hz0, hlt1, hlt2⟩ | ⟨y, rfl, hlt⟩
      · -- `x = φ u`
        refine ⟨fun V w hu hw => ?_, fun V w hu hw => ?_⟩
        · have huV : u ∈ V := (ofGroup_mem_A_iff' V u).mp hu
          have huw : u * w ∈ V :=
            (ofGroup_mem_A_iff' V (u * w)).mp (by rwa [← RatU.ofGroup_mul] at hw)
          rw [show w = u⁻¹ * (u * w) from (inv_mul_cancel_left u w).symm]
          exact V.mul_mem (V.inv_mem huV) huw
        · have huV : u ∈ V := (ofGroup_mem_A_iff' V u).mp hu
          have hwu : w * u ∈ V :=
            (ofGroup_mem_A_iff' V (w * u)).mp (by rwa [← RatU.ofGroup_mul] at hw)
          rw [show w = (w * u) * u⁻¹ from by rw [mul_assoc, mul_inv_cancel, mul_one]]
          exact V.mul_mem hwu (V.inv_mem huV)
      · -- `x = y * z`, both words
        have hxw' : RatU.IsWord (y * z) := RatU.IsWord.mul hyw hzw
        refine ⟨fun V w hx hxw => ?_, fun V w hx hxw => ?_⟩
        · rcases isWord_letter_decomp (y * z) hxw' hx0 with ⟨u, hu⟩ | ⟨l, hl, hgoodl, hPsi⟩
          · -- `x = φ u`
            have huV : u ∈ V := (ofGroup_mem_A_iff' V u).mp (by rw [← hu]; exact hx)
            have huw : u * w ∈ V :=
              (ofGroup_mem_A_iff' V (u * w)).mp
                (by rw [RatU.ofGroup_mul, ← hu]; exact hxw)
            rw [show w = u⁻¹ * (u * w) from (inv_mul_cancel_left u w).symm]
            exact V.mul_mem (V.inv_mem huV) huw
          · -- the letter list of `x`
            have hmemA : ∀ p ∈ (Psi (y * z)).coeff.support, p ∈ Orbit.NUV V :=
              (Psi_mem_A_iff V (y * z)).mp ((mem_A_iff_exists V (y * z)).mp hx)
            have hP0 : (Sum.inr (Quotient.mk (relNESetoid U) ⟨l, hl⟩) : NU U) ∈ Orbit.NUV V := by
              rw [hPsi, support_single_one] at hmemA
              exact hmemA _ (by simp)
            have hmemAw : ∀ p ∈ (Psi ((y * z) * RatU.ofGroup w)).coeff.support,
                p ∈ Orbit.NUV V :=
              (Psi_mem_A_iff V ((y * z) * RatU.ofGroup w)).mp
                ((mem_A_iff_exists V ((y * z) * RatU.ofGroup w)).mp hxw)
            have hPw0 : (Sum.inr (Quotient.mk (relNESetoid U)
                ⟨mulLast l w, mulLast_ne_nil w hl⟩) : NU U) ∈ Orbit.NUV V := by
              rw [map_mul, Psi_ofGroup, hPsi, MonoidAlgebra.single_mul_single, mul_one,
                NU.mk_mul_Ugen, support_single_one] at hmemAw
              exact hmemAw _ (by simp)
            obtain ⟨B, hB, hlen, hgoodB, htree, hclass⟩ :=
              exists_good_rep V l hl (fun y hy => (hgoodl y hy).1) hP0
            have hP : (Sum.inr (Quotient.mk (relNESetoid U) ⟨B, hB⟩) : NU U) ∈ Orbit.NUV V := by
              rwa [hclass]
            have hPg : (Sum.inr (Quotient.mk (relNESetoid U)
                ⟨mulLast B w, mulLast_ne_nil w hB⟩) : NU U) ∈ Orbit.NUV V := by
              have h1 : (Sum.inr (Quotient.mk (relNESetoid U)
                    ⟨mulLast B w, mulLast_ne_nil w hB⟩) : NU U)
                  = (Sum.inr (Quotient.mk (relNESetoid U) ⟨B, hB⟩) : NU U) * NU.Ugen w :=
                (NU.mk_mul_Ugen ⟨B, hB⟩ w).symm
              rw [h1, hclass]
              exact hPw0
            have hgood' : ∀ y ∈ B, y ∈ A V ∧ y ≠ 0 ∧ Tree.lt (Rat.treeOfRat U y) t := by
              intro y hyB
              obtain ⟨hAV, hne0⟩ := hgoodB y hyB
              obtain ⟨z, hzl, hzT⟩ := htree y hyB
              exact ⟨hAV, hne0, by rw [hzT, ← hxt]; exact (hgoodl z hzl).2⟩
            exact descent_R (hISS V) B hB hgood' w hP hPg
        · rcases isWord_letter_decomp (y * z) hxw' hx0 with ⟨u, hu⟩ | ⟨l, hl, hgoodl, hPsi⟩
          · -- `x = φ u`
            have huV : u ∈ V := (ofGroup_mem_A_iff' V u).mp (by rw [← hu]; exact hx)
            have hwu : w * u ∈ V :=
              (ofGroup_mem_A_iff' V (w * u)).mp
                (by rw [RatU.ofGroup_mul, ← hu]; exact hxw)
            rw [show w = (w * u) * u⁻¹ from by rw [mul_assoc, mul_inv_cancel, mul_one]]
            exact V.mul_mem hwu (V.inv_mem huV)
          · -- the letter list of `x`
            have hmemA : ∀ p ∈ (Psi (y * z)).coeff.support, p ∈ Orbit.NUV V :=
              (Psi_mem_A_iff V (y * z)).mp ((mem_A_iff_exists V (y * z)).mp hx)
            have hP0 : (Sum.inr (Quotient.mk (relNESetoid U) ⟨l, hl⟩) : NU U) ∈ Orbit.NUV V := by
              rw [hPsi, support_single_one] at hmemA
              exact hmemA _ (by simp)
            have hmemAw : ∀ p ∈ (Psi (RatU.ofGroup w * (y * z))).coeff.support,
                p ∈ Orbit.NUV V :=
              (Psi_mem_A_iff V (RatU.ofGroup w * (y * z))).mp
                ((mem_A_iff_exists V (RatU.ofGroup w * (y * z))).mp hxw)
            have hPw0 : (Sum.inr (Quotient.mk (relNESetoid U)
                ⟨mulFirst w l, mulFirst_ne_nil w hl⟩) : NU U) ∈ Orbit.NUV V := by
              rw [map_mul, Psi_ofGroup, hPsi, MonoidAlgebra.single_mul_single, mul_one,
                NU.inl_mul_mk, support_single_one] at hmemAw
              exact hmemAw _ (by simp)
            obtain ⟨B, hB, hlen, hgoodB, htree, hclass⟩ :=
              exists_good_rep V l hl (fun y hy => (hgoodl y hy).1) hP0
            have hP : (Sum.inr (Quotient.mk (relNESetoid U) ⟨B, hB⟩) : NU U) ∈ Orbit.NUV V := by
              rwa [hclass]
            have hPg : (Sum.inr (Quotient.mk (relNESetoid U)
                ⟨mulFirst w B, mulFirst_ne_nil w hB⟩) : NU U) ∈ Orbit.NUV V := by
              have h1 : (Sum.inr (Quotient.mk (relNESetoid U)
                    ⟨mulFirst w B, mulFirst_ne_nil w hB⟩) : NU U)
                  = (Sum.inl w : NU U) *
                    (Sum.inr (Quotient.mk (relNESetoid U) ⟨B, hB⟩) : NU U) :=
                (NU.inl_mul_mk w ⟨B, hB⟩).symm
              rw [h1, hclass]
              exact hPw0
            have hgood' : ∀ y ∈ B, y ∈ A V ∧ y ≠ 0 ∧ Tree.lt (Rat.treeOfRat U y) t := by
              intro y hyB
              obtain ⟨hAV, hne0⟩ := hgoodB y hyB
              obtain ⟨z, hzl, hzT⟩ := htree y hyB
              exact ⟨hAV, hne0, by rw [hzT, ← hxt]; exact (hgoodl z hzl).2⟩
            exact descent_L (hISS V) B hB hgood' w hP hPg
      · -- `x = y + z`
        have ihy : Both y := ih (Rat.treeOfRat U y) (by rwa [hxt] at hlt1) y rfl hy0
        have ihz : Both z := ih (Rat.treeOfRat U z) (by rwa [hxt] at hlt2) z rfl hz0
        refine ⟨fun V w hsum hsumw => ?_, fun V w hsum hsumw => ?_⟩
        · have hy : y ∈ A V := Weak.A_add_left hsum
          rw [add_mul] at hsumw
          exact ihy.1 V w hy (Weak.A_add_left hsumw)
        · have hy : y ∈ A V := Weak.A_add_left hsum
          rw [mul_add] at hsumw
          exact ihy.2 V w hy (Weak.A_add_left hsumw)
      · -- `x = y⋄`
        have hy0 : y ≠ 0 := fun h0 => hx0 (by rw [h0]; exact RatU.ratOp_zero)
        have ihy : Both y := ih (Rat.treeOfRat U y) (by rwa [hxt] at hlt) y rfl hy0
        refine ⟨fun V w hx hxw => ?_, fun V w hx hxw => ?_⟩
        · have hy : y ∈ A V := Weak.A_ratOp hx
          have h1 : RatU.rational.ratOp (RatU.ofGroup w⁻¹ * y) ∈ A V := by
            rw [← RatU.ratOp_mul_ofGroup y w]
            exact hxw
          have h2 : w⁻¹ ∈ V := ihy.2 V w⁻¹ hy (Weak.A_ratOp h1)
          simpa using inv_mem h2
        · have hy : y ∈ A V := Weak.A_ratOp hx
          have h1 : RatU.rational.ratOp (y * RatU.ofGroup w⁻¹) ∈ A V := by
            rw [← RatU.ofGroup_mul_ratOp w y]
            exact hxw
          have h2 : w⁻¹ ∈ V := ihy.1 V w⁻¹ hy (Weak.A_ratOp h1)
          simpa using inv_mem h2
  exact key (Rat.treeOfRat U x) x rfl hx0

/-- **The left-translate dichotomy for `Rat.A V`.**  For `b ∈ Rat.A V` the set of `w : U` with
`ofGroup w * b ∈ Rat.A V` is either `V` itself or all of `U`. -/
theorem ofGroup_mul_A_eq_V_or_univ {U : Type} [Group U] (V : Subgroup U) {b : Work.ORHughesFree.RatU U}
    (hb : b ∈ Work.ORHughesFree.Rat.A V) :
    {w : U | Work.ORHughesFree.RatU.ofGroup w * b ∈ Work.ORHughesFree.Rat.A V} = (V : Set U) ∨
      {w : U | Work.ORHughesFree.RatU.ofGroup w * b ∈ Work.ORHughesFree.Rat.A V} = Set.univ := by
  by_cases hb0 : b = 0
  · right
    have hzero : ∀ w : U, RatU.ofGroup w * b ∈ A V := by
      intro w
      rw [hb0, mul_zero]
      exact (Weak.ASub V).zero_mem
    ext w
    exact iff_of_true (hzero w) trivial
  · left
    ext w
    constructor
    · intro hw
      exact (both_of_ne_zero b hb0).2 V w hb hw
    · intro hw
      exact (Weak.ASub V).mul_mem (Weak.A_ofGroup_mem hw) hb

end Work.ORHughesFree.Rat.Dich
