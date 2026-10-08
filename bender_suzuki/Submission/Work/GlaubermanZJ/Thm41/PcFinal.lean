import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.PGroup.All
import Submission.Work.GlaubermanZJ.Thm41.PComm
import Submission.Work.GlaubermanZJ.Thm41.Symmetry
import Submission.Work.GlaubermanZJ.Thm41.IterComm
import Submission.Work.GlaubermanZJ.Thm41.Structure
import Submission.Work.GlaubermanZJ.Thm41.PcCong
import Submission.Work.GlaubermanZJ.Thm41.PcClosure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The case `[B,A;3] = 1` of Glauberman's Theorem 4.1: the conclusion

Glauberman (Canad. J. Math. **20** (1968), p. 1112–1113): if `S` is a finite `p`-group with `p`
odd, `A ≤ S` abelian, `B ⊴ S` with `[B,B]` central in `S` and `[B,A;3] = 1`, then `[x,A]` is
abelian for every `x ∈ B`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped commutatorElement
open Subgroup

namespace Work.GlaubermanZJ

variable {G : Type*} [Group G]

/-- **Glauberman (4.10).**  `[y,c]⁻¹b⁻¹ · ([y,c]b)⁻¹ ∈ [B,B]`. -/
theorem pcomm_inv_mul_inv_mem {S A B : Subgroup G} (hBS : B ≤ S) (hAS : A ≤ S)
    (hBn : S ≤ Subgroup.normalizer (B : Set G))
    (hZc : (⁅B, B⁆ : Subgroup G) ≤ Subgroup.centralizer (S : Set G))
    (h3 : ⁅⁅⁅B, A⁆, A⁆, A⁆ = ⊥)
    {y b c : G} (hy : y ∈ B) (hb : b ∈ A) (hc : c ∈ A) :
    pcomm (pcomm y c)⁻¹ b⁻¹ * (pcomm (pcomm y c) b)⁻¹ ∈ ⁅B, B⁆ := by
  have hV : pcomm y c ∈ B := pcomm_mem_of_mem hBS hAS hBn hy hc
  have hPB : pcomm (pcomm y c) b ∈ B := pcomm_mem_of_mem hBS hAS hBn hV hb
  have hV1 : pcomm y c ∈ iterComm B A 1 := by
    rw [pcomm_eq_commutatorElement_inv]
    exact Subgroup.commutator_mem_commutator (B.inv_mem hy) (A.inv_mem hc)
  have hPB2 : pcomm (pcomm y c) b ∈ iterComm B A 2 := by
    show pcomm (pcomm y c) b ∈ ⁅⁅B, A⁆, A⁆
    rw [pcomm_eq_commutatorElement_inv]
    exact Subgroup.commutator_mem_commutator ((⁅B, A⁆ : Subgroup G).inv_mem hV1) (A.inv_mem hb)
  have hPb : pcomm (pcomm (pcomm y c) b) b⁻¹ = 1 := by
    have hmem : pcomm (pcomm (pcomm y c) b) b⁻¹ ∈ iterComm B A 3 := by
      show pcomm (pcomm (pcomm y c) b) b⁻¹ ∈ ⁅⁅⁅B, A⁆, A⁆, A⁆
      rw [pcomm_eq_commutatorElement_inv]
      exact Subgroup.commutator_mem_commutator ((⁅⁅B, A⁆, A⁆ : Subgroup G).inv_mem hPB2)
        (A.inv_mem (A.inv_mem hb))
    exact Subgroup.mem_bot.mp (h3 ▸ hmem)
  have hδ : ⁅pcomm y c, pcomm (pcomm y c) b⁆ ∈ ⁅B, B⁆ :=
    Subgroup.commutator_mem_commutator hV hPB
  have hcommPb : pcomm (pcomm y c) b * b⁻¹ = b⁻¹ * pcomm (pcomm y c) b :=
    ((pcomm_eq_one_iff_commute _ _).mp hPb).eq
  have hbPb : b * pcomm (pcomm y c) b * b⁻¹ = pcomm (pcomm y c) b := by
    calc b * pcomm (pcomm y c) b * b⁻¹
        = b * (pcomm (pcomm y c) b * b⁻¹) := by group
      _ = b * (b⁻¹ * pcomm (pcomm y c) b) := by rw [hcommPb]
      _ = pcomm (pcomm y c) b := by group
  have hE : (b * pcomm y c) * pcomm (pcomm y c) b * (b * pcomm y c)⁻¹ *
      (pcomm (pcomm y c) b)⁻¹ = ⁅pcomm y c, pcomm (pcomm y c) b⁆ := by
    calc (b * pcomm y c) * pcomm (pcomm y c) b * (b * pcomm y c)⁻¹ *
          (pcomm (pcomm y c) b)⁻¹
        = b * (pcomm y c * pcomm (pcomm y c) b * (pcomm y c)⁻¹) * b⁻¹ *
            (pcomm (pcomm y c) b)⁻¹ := by group
      _ = b * (⁅pcomm y c, pcomm (pcomm y c) b⁆ * pcomm (pcomm y c) b) * b⁻¹ *
            (pcomm (pcomm y c) b)⁻¹ := by
          rw [show pcomm y c * pcomm (pcomm y c) b * (pcomm y c)⁻¹
                = ⁅pcomm y c, pcomm (pcomm y c) b⁆ * pcomm (pcomm y c) b from by
              rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]]
      _ = b * ⁅pcomm y c, pcomm (pcomm y c) b⁆ * (pcomm (pcomm y c) b * b⁻¹) *
            (pcomm (pcomm y c) b)⁻¹ := by group
      _ = b * ⁅pcomm y c, pcomm (pcomm y c) b⁆ * (b⁻¹ * pcomm (pcomm y c) b) *
            (pcomm (pcomm y c) b)⁻¹ := by rw [hcommPb]
      _ = b * ⁅pcomm y c, pcomm (pcomm y c) b⁆ * b⁻¹ := by group
      _ = ⁅pcomm y c, pcomm (pcomm y c) b⁆ := by
          rw [Subgroup.mem_centralizer_iff.mp (hZc hδ) b (hAS hb)]
          group
  rw [pcomm_inv_inv (pcomm y c) b, hE]
  exact hδ

/-- **The `[B,A;3] = 1` case of Glauberman's Theorem 4.1.**  Let `S` be a finite `p`-group with
`p` odd, `A ≤ S` abelian, `B ⊴ S` such that `[B,B]` is central in `S`, and assume
`[B,A;3] = 1`.  Then for every `x ∈ B` the subgroup `[x,A] = commClosure x A` is abelian. -/
theorem commClosure_abelian_of_iterComm_three_eq_bot (p : ℕ) (hp : p.Prime) (hpne : p ≠ 2)
    (S A B : Subgroup G) [Finite S] (hS : IsPGroup p S)
    (hAS : A ≤ S) (hBS : B ≤ S) (hBn : S ≤ Subgroup.normalizer (B : Set G))
    (hAab : IsMulCommutative A) (hZ : ⁅B, B⁆ ≤ Work.PGroup.centerIn S)
    (h3 : ⁅⁅⁅B, A⁆, A⁆, A⁆ = ⊥) (x : G) (hx : x ∈ B) :
    IsMulCommutative (Work.PGroup.commClosure x A) := by
  have hZc : (⁅B, B⁆ : Subgroup G) ≤ Subgroup.centralizer (S : Set G) :=
    hZ.trans (centerIn_le_centralizer S)
  have key : ∀ y ∈ B, ∀ b ∈ A, ∀ c ∈ A, pcomm (pcomm y b) (pcomm y c) = 1 := by
    intro y hy b hb c hc
    have hα := pcomm_pcomm_eq_pcomm_inv (H := S) hBS hAS hBn hZc hy hb hc
    have hβ := pcomm_pcomm_eq_pcomm_inv (H := S) hBS hAS hBn hZc hy hc hb
    have hw1 := pcomm_inv_mul_inv_mem hBS hAS hBn hZc h3 hy hb hc
    have hw2 := pcomm_inv_mul_inv_mem hBS hAS hBn hZc h3 hy hc hb
    have hPQ := pcomm_pcomm_sub_mem (H := S) hBS hAS hBn hAab hy hb hc
    -- the two arguments of `(α)` and `(β)` agree modulo `[B,B]`
    have hw : pcomm (pcomm y c)⁻¹ b⁻¹ * (pcomm (pcomm y b)⁻¹ c⁻¹)⁻¹ ∈ ⁅B, B⁆ := by
      have hQw : pcomm (pcomm y b) c * (pcomm (pcomm y b)⁻¹ c⁻¹)⁻¹ ∈ ⁅B, B⁆ := by
        have h := (⁅B, B⁆ : Subgroup G).inv_mem hw2
        simpa [pcomm_inv, mul_assoc] using h
      have heq : pcomm (pcomm y c)⁻¹ b⁻¹ * (pcomm (pcomm y b)⁻¹ c⁻¹)⁻¹ =
          ((pcomm (pcomm y c)⁻¹ b⁻¹ * (pcomm (pcomm y c) b)⁻¹) *
            (pcomm (pcomm y c) b * (pcomm (pcomm y b) c)⁻¹)) *
          (pcomm (pcomm y b) c * (pcomm (pcomm y b)⁻¹ c⁻¹)⁻¹) := by group
      rw [heq]
      exact (⁅B, B⁆ : Subgroup G).mul_mem
        ((⁅B, B⁆ : Subgroup G).mul_mem hw1 hPQ) hQw
    have hcen : y * (pcomm (pcomm y c)⁻¹ b⁻¹ * (pcomm (pcomm y b)⁻¹ c⁻¹)⁻¹) =
        (pcomm (pcomm y c)⁻¹ b⁻¹ * (pcomm (pcomm y b)⁻¹ c⁻¹)⁻¹) * y :=
      Subgroup.mem_centralizer_iff.mp (hZc hw) y (hBS hy)
    have hpc : pcomm (pcomm (pcomm y c)⁻¹ b⁻¹) y =
        pcomm (pcomm (pcomm y b)⁻¹ c⁻¹) y := by
      have hsp : pcomm (pcomm y c)⁻¹ b⁻¹ =
          (pcomm (pcomm y c)⁻¹ b⁻¹ * (pcomm (pcomm y b)⁻¹ c⁻¹)⁻¹) *
            pcomm (pcomm y b)⁻¹ c⁻¹ := by group
      rw [hsp, pcomm_mul_left]
      have hone : pcomm (pcomm (pcomm y c)⁻¹ b⁻¹ * (pcomm (pcomm y b)⁻¹ c⁻¹)⁻¹) y = 1 :=
        (pcomm_eq_one_iff_commute _ _).mpr ((commute_iff_eq _ _).mpr hcen.symm)
      rw [hone]
      group
    -- `[y,b]` and `[y,c]` have the same commutator with `y` in both orders, so they coincide
    -- with their own commutator's inverse
    have h3' : pcomm (pcomm (pcomm y b)⁻¹ c⁻¹) y =
        (pcomm (pcomm y b) (pcomm y c))⁻¹ :=
      hβ.symm.trans (pcomm_inv (pcomm y b) (pcomm y c)).symm
    have hginv : pcomm (pcomm y b) (pcomm y c) =
        (pcomm (pcomm y b) (pcomm y c))⁻¹ := hα.trans (hpc.trans h3')
    -- an element of order dividing two in the odd `p`-group `S` is trivial
    have hgS : pcomm (pcomm y b) (pcomm y c) ∈ S :=
      hBS (Subgroup.commutator_le_self B (by
        rw [pcomm_eq_commutatorElement_inv]
        exact Subgroup.commutator_mem_commutator
          (B.inv_mem (pcomm_mem_of_mem hBS hAS hBn hy hb))
          (B.inv_mem (pcomm_mem_of_mem hBS hAS hBn hy hc))))
    have hg2 : pcomm (pcomm y b) (pcomm y c) * pcomm (pcomm y b) (pcomm y c) = 1 :=
      (congrArg (fun t => pcomm (pcomm y b) (pcomm y c) * t) hginv).trans
        (mul_inv_cancel _)
    obtain ⟨k, hk⟩ := hS ⟨_, hgS⟩
    have hk' : (pcomm (pcomm y b) (pcomm y c)) ^ (p ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hpne
      · exact h
    have h2p : ¬ (2 ∣ p) := fun h => by
      rw [Nat.dvd_iff_mod_eq_zero] at h
      omega
    have hcop : Nat.Coprime 2 (p ^ k) :=
      ((Nat.prime_two.coprime_iff_not_dvd).mpr h2p).pow_right k
    refine orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd
      (orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hg2))
      (orderOf_dvd_iff_pow_eq_one.mpr hk')))
  rw [Work.PGroup.commClosure]
  refine Subgroup.isMulCommutative_closure ?_
  rintro u ⟨a, ha, rfl⟩ v ⟨a', ha', rfl⟩ _
  rw [← pcomm_eq_one_iff_commute]
  show pcomm ⁅x, a⁆ ⁅x, a'⁆ = 1
  rw [
    show ⁅x, a⁆ = pcomm x⁻¹ a⁻¹ from by rw [pcomm_eq_commutatorElement_inv]; simp,
    show ⁅x, a'⁆ = pcomm x⁻¹ a'⁻¹ from by rw [pcomm_eq_commutatorElement_inv]; simp]
  exact key x⁻¹ (B.inv_mem hx) a⁻¹ (A.inv_mem ha) a'⁻¹ (A.inv_mem ha')

end Work.GlaubermanZJ
