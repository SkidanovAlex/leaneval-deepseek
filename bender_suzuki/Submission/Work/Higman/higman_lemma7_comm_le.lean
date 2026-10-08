import Mathlib
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.Defs
import Submission.Work.Higman.commutatorElement_mul_of_abel_normal
import Submission.Work.Higman.commutatorElement_sq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman

/-- If `A = Φ(C)` is a `ξ`-invariant abelian normal subgroup of a Suzuki 2-group with
`C' ≤ A²` and `C' = A ^ (2 ^ s)`, then `[A,C]` and `[C',C]` both lie in `(C')²`. -/
theorem higman_lemma7_comm_le {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A) (hCn : C.Normal)
    (hAC : A ≤ C) (hPhi : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = A)
    (hCd : ⁅C, C⁆ ≤ Work.Higman.powSub A 2)
    {e s : ℕ} (hs : 1 ≤ s) (hse : s ≤ e - 1) (h1 : ∀ x ∈ A, x ^ 2 ^ e = 1)
    (hDs : ⁅C, C⁆ = Work.Higman.powSub A (2 ^ s)) :
    ⁅A, C⁆ ≤ Work.Higman.powSub ⁅C, C⁆ 2 ∧
      ⁅⁅C, C⁆, C⁆ ≤ Work.Higman.powSub ⁅C, C⁆ 2 := by
  haveI hAn : A.Normal := hA.normal
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  -- `C' ≤ A`, because `A = Φ(C) = C² · C'`
  have hDA : ⁅C, C⁆ ≤ A := by rw [← hPhi]; exact le_sup_right
  -- `[A,C] ≤ C'` since `A ≤ C`
  have hACD : ⁅A, C⁆ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hAC le_rfl
  -- `[C', C] ≤ (C')²`, using `C' = A ^ (2 ^ s)` and the power identity on the abelian `A`
  have step2 : ∀ d ∈ ⁅C, C⁆, ∀ c ∈ C, ⁅d, c⁆ ∈ powSub ⁅C, C⁆ 2 := by
    intro d hd c hc
    obtain ⟨a, ha, haeq⟩ := (mem_powSub_iff hAb).mp (hDs ▸ hd)
    have hac : ⁅a, c⁆ ∈ A :=
      Subgroup.commutator_le_left A C (Subgroup.commutator_mem_commutator ha hc)
    have hacD : ⁅a, c⁆ ∈ ⁅C, C⁆ := hACD (Subgroup.commutator_mem_commutator ha hc)
    have hcomm : Commute a ⁅a, c⁆ := hAb a ha ⁅a, c⁆ hac
    rw [← haeq, ← Commute.commutatorElement_pow_left hcomm (2 ^ s)]
    have hp : (2 : ℕ) ^ s = 2 ^ (s - 1) * 2 := by
      cases s with
      | zero => omega
      | succ k => simp [pow_succ]
    rw [hp, pow_mul]
    exact pow_mem_powSub (Subgroup.pow_mem ⁅C, C⁆ hacD (2 ^ (s - 1)))
  -- the same statement with the arguments swapped, via `⁅x, y⁆⁻¹ = ⁅y, x⁆`
  have step2' : ∀ x ∈ C, ∀ d ∈ ⁅C, C⁆, ⁅x, d⁆ ∈ powSub ⁅C, C⁆ 2 := by
    intro x hx d hd
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (step2 d hd x hx)
  -- the subgroup of elements of `A` whose commutators with `C` lie in `(C')²`
  let T : Subgroup P :=
    { carrier := {g : P | g ∈ A ∧ ∀ c ∈ C, ⁅g, c⁆ ∈ powSub ⁅C, C⁆ 2}
      one_mem' := ⟨A.one_mem, by
        intro c hc
        rw [commutatorElement_one_left]
        exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro g h' ⟨hgA, hg⟩ ⟨hhA, hh⟩
        refine ⟨A.mul_mem hgA hhA, fun c hc => ?_⟩
        rw [commutatorElement_mul_of_abel_normal hAn hAb hgA hhA hc]
        exact Subgroup.mul_mem _ (hg c hc) (hh c hc)
      inv_mem' := by
        rintro g ⟨hgA, hg⟩
        refine ⟨A.inv_mem hgA, fun c hc => ?_⟩
        have hmul :=
          commutatorElement_mul_of_abel_normal hAn hAb hgA (A.inv_mem hgA) hc
        have hone : ⁅g * g⁻¹, c⁆ = 1 := by rw [mul_inv_cancel, commutatorElement_one_left]
        rw [hone] at hmul
        have hinv : ⁅g⁻¹, c⁆ = ⁅g, c⁆⁻¹ := eq_inv_of_mul_eq_one_right hmul.symm
        rw [hinv]
        exact Subgroup.inv_mem _ (hg c hc) }
  -- every square of an element of `C` lies in `T`, hence so does `C²`
  have hTpow : powSub C 2 ≤ T := by
    rw [powSub]
    refine (Subgroup.closure_le T).mpr ?_
    rintro y ⟨x, hx, rfl⟩
    refine ⟨le_sup_left.trans hPhi.le (pow_mem_powSub hx), fun c hc => ?_⟩
    rw [commutatorElement_sq]
    have hxc : ⁅x, c⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hc
    exact Subgroup.mul_mem _ (step2' x hx ⁅x, c⁆ hxc) (pow_mem_powSub hxc)
  -- and `C' ≤ T` by `step2`
  have hTD : ⁅C, C⁆ ≤ T := fun d hd => ⟨hDA hd, fun c hc => step2 d hd c hc⟩
  -- therefore `A = C² · C' ≤ T`, which is exactly the assertion about `[A,C]`
  have hTA : A ≤ T := by
    rw [← hPhi]
    exact sup_le hTpow hTD
  constructor
  · exact Subgroup.commutator_le.mpr (fun g hg c hc => (hTA hg).2 c hc)
  · exact Subgroup.commutator_le.mpr (fun d hd c hc => step2 d hd c hc)

end Work.Higman
