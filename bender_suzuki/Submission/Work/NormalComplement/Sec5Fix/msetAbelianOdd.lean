import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.appI_two
import Submission.Work.NormalComplement.appI_five_b
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.sec4_P2d
import Submission.Work.NormalComplement.sec5_prop1
import Submission.Work.Coprime.All
import Submission.Work.ThreePoints.Basic
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.Sec5Fix

/-- **Peterfalvi I Ch. III §5 Prop. 2 (b), the "`M` is an abelian subgroup of odd order" part.**

IMPORTANT (cycle): the file `Submission/Work/NormalComplement/sec5_prop2.lean` imports
`Submission/Work/NormalComplement/sec5_clause_d` (the consumer of this lemma), and
`Submission/Work/NormalComplement/Sec5Fix/prop2b.lean` imports `sec5_prop2`.  So **do not import
`sec5_prop2` or `Sec5Fix.prop2b`** (that would be a build cycle): copy/adapt the needed material
from the (readable) files `Sec5Fix/prop2b.lean` (the lemmas `odd_card_inf_centralizer`,
`conj_mul_inv`, `normalizedBy_centralizer_mul`, `centD_eq_inf_centralizer_mul`,
`exists_conj_mem_of_isPGroup`, `mset_eq_kset`, `kapp_eq_mset`, `exists_abelian_subgroup_of_coprime`,
and the body of `prop2b`) and `sec5_prop2.lean` (the lemmas `set_eq_pair_of_ncard_le_two`,
`ncard_fixedPts_zpowers_conj`, `fixedPts_mul_eq_empty`, `ncard_fixedPts_le_two_of_mem_Mset`,
`fixedPts_zpowers_eq_empty_of_mem_Mset`, `mul_self_eq_one_of_orderOf_eq_two`).  Only cycle-free
modules are listed in `depends_on`. -/
theorem msetAbelianOdd (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop)
    (hBC : Work.NormalComplement.Design.BurnsideClassProp)
    (hBP : Work.NormalComplement.BenderPrelimProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5)
    (M : Subgroup G) (hM : (M : Set G) = Work.NormalComplement.Design.Mset u t) :
    (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) ∧ Odd (Nat.card ↥M) := by
  classical
  -- `M` is *given* as a subgroup with underlying set `Mset u t`, so it is closed under
  -- multiplication.  For `x, y ∈ M`, `t (xy) t⁻¹ = x⁻¹ y⁻¹` while `xy ∈ M` forces
  -- `t (xy) t⁻¹ = (xy)⁻¹`; hence `(yx)⁻¹ = (xy)⁻¹` and `x` and `y` commute.
  have hab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
    intro x hx y hy
    have hxM : x ∈ Work.NormalComplement.Design.Mset u t := hM ▸ hx
    have hyM : y ∈ Work.NormalComplement.Design.Mset u t := hM ▸ hy
    have hxyM : x * y ∈ Work.NormalComplement.Design.Mset u t := hM ▸ M.mul_mem hx hy
    have h2 : t * (x * y) * t⁻¹ = x⁻¹ * y⁻¹ := by
      calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
        _ = x⁻¹ * y⁻¹ := by rw [hxM.2, hyM.2]
    have h3 : (x * y)⁻¹ = (y * x)⁻¹ := by
      rw [← hxyM.2, h2]; group
    exact inv_injective h3
  refine ⟨hab, ?_⟩
  -- `|M|` is odd: an element of order `2` in `M ⊆ Mset u t` lies in `centD H t`, of odd order.
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨z, hzM, hzord⟩ := exists_orderOf_two_of_even_card_subgroup (C := M) hodd
  have hzMset : z ∈ Work.NormalComplement.Design.Mset u t := hM ▸ hzM
  obtain ⟨hzCent, hztInv⟩ := hzMset
  -- `z` is an involution, so being inverted by `t` means commuting with `t`.
  have hz2 : z * z = 1 := by
    have hh := pow_orderOf_eq_one z
    rw [hzord] at hh
    simpa [pow_two] using hh
  have hztComm : Commute z t := by
    have h := hztInv
    rw [inv_eq_of_mul_eq_one_right hz2] at h
    -- h : t * z * t⁻¹ = z
    have h' := congrArg (fun w => w * t) h
    have h2 : (t * z * t⁻¹) * t = t * z := by group
    rw [h2] at h'
    exact h'.symm
  have hzutComm : Commute z (u * t) := Subgroup.mem_centralizer_singleton_iff.mp hzCent
  have ht2 : t * t = 1 := by
    have hh := pow_orderOf_eq_one t
    rw [h.invol] at hh
    simpa [pow_two] using hh
  -- `z` commutes with `u = (ut) t⁻¹`, so `z ∈ C_G(u) ≤ H` by strong embeddedness of `H`.
  have hzuComm : Commute z u := by
    have h1 : Commute z ((u * t) * t⁻¹) := hzutComm.mul_right hztComm.inv_right
    have h2 : (u * t) * t⁻¹ = u := by group
    rwa [h2] at h1
  have hzH : z ∈ H :=
    (Work.ThreePoints.IsStronglyEmbedded.centralizer_le (H := H) (x := u) h.se hu.1
      (by rw [hu.2.1])) (Subgroup.mem_centralizer_singleton_iff.mpr hzuComm)
  -- `z` commutes with `t`, so `z ∈ twoPoint H t`, and hence `z ∈ centD H t = twoPoint H t ⊓ C_G(t)`.
  have hzD : z ∈ Submission.Blueprint.twoPoint H t := by
    rw [Work.ThreePoints.mem_twoPoint]
    refine ⟨hzH, ?_⟩
    have h3 : t⁻¹ * z * t = z := by
      calc t⁻¹ * z * t = t⁻¹ * (z * t) := by group
        _ = t⁻¹ * (t * z) := by rw [show z * t = t * z from hztComm]
        _ = z := by group
    rw [h3]; exact hzH
  have hzcentD : z ∈ Submission.Blueprint.centD H t := by
    rw [Work.ThreePoints.centD_eq]
    exact ⟨hzD, Subgroup.mem_centralizer_singleton_iff.mpr hztComm⟩
  -- `2 = orderOf z` divides `|centD H t|`, which is odd (it is a subgroup of `twoPoint H t`).
  have h2dvd : 2 ∣ Nat.card ↥(Submission.Blueprint.centD H t) := by
    have h := Subgroup.orderOf_dvd_natCard (Submission.Blueprint.centD H t) hzcentD
    rwa [hzord] at h
  have hcentodd : Odd (Nat.card ↥(Submission.Blueprint.centD H t)) :=
    Odd.of_dvd_nat (h.se.2.2 t h.notMem) (Subgroup.card_dvd_of_le inf_le_left)
  exact (Nat.not_even_iff_odd.mpr hcentodd) (even_iff_two_dvd.mpr h2dvd)

end Work.NormalComplement.Sec5Fix
