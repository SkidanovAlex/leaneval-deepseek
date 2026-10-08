import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.PGroup.All
import Submission.Work.GlaubermanZJ.Thm41.PComm
import Submission.Work.GlaubermanZJ.Thm41.Symmetry
import Submission.Work.GlaubermanZJ.Thm41.IterComm
import Submission.Work.GlaubermanZJ.Thm41.Structure
import Submission.Work.GlaubermanZJ.Thm41.PcCong

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The case `[B,A;3] = 1` of Glauberman's Theorem 4.1

Glauberman (Canad. J. Math. **20** (1968), (4.7)–(4.10), p. 1112–1113): if `S` is a finite
`p`-group with `p` odd, `A ≤ S` abelian, `B ⊴ S` with `[B,B]` central in `S` and
`[B,A;3] = 1`, then `[x,A]` is abelian for every `x ∈ B`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped commutatorElement
open Subgroup

namespace Work.GlaubermanZJ

variable {G : Type*} [Group G]

/-- `pcomm u v ∈ B` when `u ∈ A` and `v ∈ B` (the mirror of `pcomm_mem_of_mem`). -/
theorem pcomm_mem_of_mem' {H A B : Subgroup G} (hAH : A ≤ H)
    (hHn : H ≤ Subgroup.normalizer (B : Set G)) {u v : G} (hu : u ∈ A) (hv : v ∈ B) :
    pcomm u v ∈ B := by
  have h1 : u⁻¹ * v⁻¹ * u ∈ B := by
    have := (Subgroup.mem_normalizer_iff.mp (hHn (H.inv_mem (hAH hu))) v⁻¹).mp
      (B.inv_mem hv)
    simpa using this
  rw [show pcomm u v = (u⁻¹ * v⁻¹ * u) * v from by simp only [pcomm, mul_assoc]]
  exact B.mul_mem h1 hv

/-- **Glauberman (4.9).**  The Hall–Witt identity in the form
`[[y,b],[y,c]] = [[[y,c]⁻¹,b⁻¹],y]`. -/
theorem pcomm_pcomm_eq_pcomm_inv {H A B : Subgroup G} (hBH : B ≤ H) (hAH : A ≤ H)
    (hHn : H ≤ Subgroup.normalizer (B : Set G))
    (hZc : (⁅B, B⁆ : Subgroup G) ≤ Subgroup.centralizer (H : Set G))
    {y b c : G} (hy : y ∈ B) (hb : b ∈ A) (hc : c ∈ A) :
    pcomm (pcomm y b) (pcomm y c) = pcomm (pcomm (pcomm y c)⁻¹ b⁻¹) y := by
  have hV : pcomm y c ∈ B := pcomm_mem_of_mem hBH hAH hHn hy hc
  have hU : pcomm y b ∈ B := pcomm_mem_of_mem hBH hAH hHn hy hb
  have hgB' : pcomm (pcomm y b) (pcomm y c) ∈ ⁅B, B⁆ := by
    rw [pcomm_eq_commutatorElement_inv]
    exact Subgroup.commutator_mem_commutator (B.inv_mem hU) (B.inv_mem hV)
  have hw'B : pcomm b⁻¹ (pcomm y c)⁻¹ ∈ B := pcomm_mem_of_mem' hAH hHn (A.inv_mem hb) (B.inv_mem hV)
  have hWB' : pcomm (pcomm b⁻¹ (pcomm y c)⁻¹) y ∈ ⁅B, B⁆ := by
    rw [pcomm_eq_commutatorElement_inv]
    exact Subgroup.commutator_mem_commutator (B.inv_mem hw'B) (B.inv_mem hy)
  -- the three factors of the Hall–Witt identity
  have hT1 : b⁻¹⁻¹ * pcomm (pcomm y b⁻¹⁻¹) (pcomm y c) * b⁻¹ =
      pcomm (pcomm y b) (pcomm y c) := by
    have hc := Subgroup.mem_centralizer_iff.mp (hZc hgB') b (hAH hb)
    simp only [inv_inv]
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hT2 : (pcomm y c)⁻¹ * pcomm (pcomm b⁻¹ (pcomm y c)⁻¹) y * (pcomm y c) =
      pcomm (pcomm b⁻¹ (pcomm y c)⁻¹) y := by
    have hc := (Subgroup.mem_centralizer_iff.mp (hZc hWB') (pcomm y c) (hBH hV)).symm
    calc (pcomm y c)⁻¹ * pcomm (pcomm b⁻¹ (pcomm y c)⁻¹) y * (pcomm y c)
        = (pcomm y c)⁻¹ * (pcomm (pcomm b⁻¹ (pcomm y c)⁻¹) y * (pcomm y c)) := by group
      _ = (pcomm y c)⁻¹ * ((pcomm y c) * pcomm (pcomm b⁻¹ (pcomm y c)⁻¹) y) := by rw [hc]
      _ = pcomm (pcomm b⁻¹ (pcomm y c)⁻¹) y := by group
  have hT3 : y⁻¹ * pcomm (pcomm (pcomm y c) y⁻¹) b⁻¹ * y = 1 := by
    have hw''B : pcomm (pcomm y c) y⁻¹ ∈ ⁅B, B⁆ := by
      rw [pcomm_eq_commutatorElement_inv]
      exact Subgroup.commutator_mem_commutator (B.inv_mem hV) (B.inv_mem (B.inv_mem hy))
    have hcomm : pcomm (pcomm (pcomm y c) y⁻¹) b⁻¹ = 1 :=
      (pcomm_eq_one_iff_commute _ _).mpr
        ((commute_iff_eq _ _).mpr
          (Subgroup.mem_centralizer_iff.mp (hZc hw''B) b⁻¹ (hAH (A.inv_mem hb))).symm)
    rw [hcomm, mul_one, inv_mul_cancel]
  have hgW : pcomm (pcomm y b) (pcomm y c) * pcomm (pcomm b⁻¹ (pcomm y c)⁻¹) y = 1 := by
    have h := pcomm_hallWitt y b⁻¹ (pcomm y c)
    rw [hT1, hT2, hT3, mul_one] at h
    exact h
  -- `W = g⁻¹`, and `[w'⁻¹,y] = W⁻¹ = g`
  have hWeq : pcomm (pcomm b⁻¹ (pcomm y c)⁻¹) y = (pcomm (pcomm y b) (pcomm y c))⁻¹ := by
    have h := congrArg (fun x => (pcomm (pcomm y b) (pcomm y c))⁻¹ * x) hgW
    simpa [mul_assoc] using h
  have hW2 : (pcomm (pcomm b⁻¹ (pcomm y c)⁻¹) y)⁻¹ = pcomm (pcomm y b) (pcomm y c) := by
    rw [hWeq, inv_inv]
  have hwinv : pcomm (pcomm y c)⁻¹ b⁻¹ = (pcomm b⁻¹ (pcomm y c)⁻¹)⁻¹ :=
    (pcomm_inv _ _).symm
  have key : pcomm (pcomm (pcomm y c)⁻¹ b⁻¹) y = pcomm (pcomm y b) (pcomm y c) := by
    rw [hwinv, pcomm_inv_left, hW2]
    have hc : pcomm b⁻¹ (pcomm y c)⁻¹ * pcomm (pcomm y b) (pcomm y c) =
        pcomm (pcomm y b) (pcomm y c) * pcomm b⁻¹ (pcomm y c)⁻¹ :=
      Subgroup.mem_centralizer_iff.mp (hZc hgB') (pcomm b⁻¹ (pcomm y c)⁻¹) (hBH hw'B)
    rw [hc]
    group
  exact key.symm

end Work.GlaubermanZJ
