import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmF.Prove.centDLowerCentralizerS

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.S5_cst_inf_cs` — Peterfalvi II, Ch. V §2 Lemma 3 a)

`C_G(st) ∩ C_G(s) = V`, where `V = centD H t = D ∩ C_G(t)`.

`C_G(st) ∩ C_G(s) = C_G(s) ∩ C_G(t)` (`s · (st) = t`), and:

* `C_G(s) ≤ H` because `H` is strongly embedded and `s ∈ H` is an involution
  (`Work.ThmF.centralizer_involution_le`);
* `C_G(t) ⊆ H^t = conj t H`, since an element centralising `t` and lying in `H` lies in `t H t⁻¹`.

Hence the intersection lies in `H ∩ H^t ∩ C_G(t) = V`; the reverse inclusion is
`V ≤ C_G(t)` together with `V ≤ C_G(s)` (`Prove.centDLowerCentralizerS`).
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV3.Prove

theorem S5_cst_inf_cs {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    Work.ThmF.ChV3.Cst s t ⊓ Subgroup.centralizer ({s} : Set G) =
      Submission.Blueprint.centD H t := by
  refine le_antisymm ?_ ?_
  · -- ## `Cst s t ⊓ C_G(s) ≤ centD H t`
    intro x hx
    obtain ⟨hxst, hxs⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxst hxs
    -- `hxst : x * (s*t) = (s*t) * x`, `hxs : x * s = s * x`
    have hs2 : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rwa [c.s_inv, pow_two] at h
    have hst : s * (s * t) = t := by rw [← mul_assoc, hs2, one_mul]
    have hxt : x * t = t * x := by
      calc x * t = x * (s * (s * t)) := by rw [hst]
        _ = (x * s) * (s * t) := by group
        _ = (s * x) * (s * t) := by rw [hxs]
        _ = s * (x * (s * t)) := by group
        _ = s * ((s * t) * x) := by rw [hxst]
        _ = (s * (s * t)) * x := by group
        _ = t * x := by rw [hst]
    -- `x ∈ H` since `H` is strongly embedded and `s ∈ H` is an involution
    have hsH : s ∈ H := c.split.le c.s_mem
    have hxH : x ∈ H :=
      Work.ThmF.centralizer_involution_le c.split.stronglyEmbedded hsH c.s_inv
        (Subgroup.mem_centralizer_singleton_iff.mpr hxs)
    -- `x ∈ H^t`: as `x` centralises `t`, `t⁻¹ x t = x ∈ H`
    have hxtinv : t⁻¹ * x * t = x := by
      calc t⁻¹ * x * t = t⁻¹ * (x * t) := by rw [mul_assoc]
        _ = t⁻¹ * (t * x) := by rw [hxt]
        _ = (t⁻¹ * t) * x := by rw [mul_assoc]
        _ = x := by rw [inv_mul_cancel, one_mul]
    have hxconj : x ∈ Submission.Blueprint.conj t H := by
      rw [Work.Models.mem_conj_iff, hxtinv]
      exact hxH
    rw [Submission.Blueprint.centD, Submission.Blueprint.twoPoint]
    exact ⟨⟨hxH, hxconj⟩, Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩
  · -- ## `centD H t ≤ Cst s t ⊓ C_G(s)`
    intro x hx
    have hxs : x ∈ Subgroup.centralizer ({s} : Set G) :=
      Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid hx
    have hxst : x ∈ Work.ThmF.ChV3.Cst s t := by
      have hsx : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hxs
      have htx : x * t = t * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
      rw [Work.ThmF.ChV3.Cst, Subgroup.mem_centralizer_singleton_iff]
      calc x * (s * t) = (x * s) * t := by rw [mul_assoc]
        _ = (s * x) * t := by rw [hsx]
        _ = s * (x * t) := by rw [mul_assoc]
        _ = s * (t * x) := by rw [htx]
        _ = (s * t) * x := by rw [mul_assoc]
    exact Subgroup.mem_inf.mpr ⟨hxst, hxs⟩

end Work.ThmF.ChV3.Prove
