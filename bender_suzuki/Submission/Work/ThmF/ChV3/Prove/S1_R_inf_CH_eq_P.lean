import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.S1_R_inf_CH_eq_P`

Step (2) of Peterfalvi II Ch. V §3, the piece of S1 (`centralizerP_eq`) that identifies
`R ⊓ C_H(P)`.

With `R` the preimage of the near-field `F` in `C_G(P)` (step (2) of the source, recorded in
`Chain15`), `N = Ker H Q P t = P` (step (7), hypothesis `h7`) and `f = orderOf (s * t) = |P|`
(hypothesis `hpf`), one has

  `R ⊓ (H ⊓ C_G(P)) = P`.

The argument is short and uses only the "fixed-point-freeness" clause `h15.hfpf` of the
near-field input, `R ≤ C_G(P) ≤ N_G(R)` and `Q ⊴ H`.  Indeed, if `x ∈ R ⊓ H` had `x ∉ P`,
then for every `y ∈ C_Q(P)` the commutator `y x y⁻¹ x⁻¹` lies in `R`
(`y ∈ C_G(P) ≤ N_G(R)`, `x ∈ R`) and in `Q` (`x ∈ H`, `y ∈ Q`, `Q ⊴ H`); and `R ⊓ Q = ⊥`
(the trivial intersection again computed from `hfpf`), so `C_Q(P)` centralises `x`; but then
`y x y⁻¹ x⁻¹ = 1 ∈ Ker H Q P t = P` and `hfpf` forces `y = 1` for every `y ∈ C_Q(P)`, i.e.
`C_Q(P) = ⊥`.  This is absurd because `|C_Q(P)| = f^m - 1 ≥ 2`: the prime `f = orderOf (s*t)`
is not `2`, for `f = 2` means that `s` and `t` commute, whence the structure identity
`t s t = r⁻¹ t r` gives `t = r s r⁻¹ ∈ Q ≤ H`, contradicting `t ∉ H`.

The reverse inclusion `P ≤ R ⊓ (H ⊓ C_G(P))` is immediate: `P = Ker H Q P t ≤ R`, `P ≤ V ≤ D ≤ H`
and `P = Ker H Q P t ≤ C_G(P)` by the definition of `Ker`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3.Prove

open Work.ThmF Submission.Blueprint Work.ThmF.ChV3

theorem S1_R_inf_CH_eq_P {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t)) :
    h15.R ⊓ (H ⊓ Work.ThmF.ChV3.CG P) = P := by
  classical
  -- ## `s` and `t` are involutions, and `f = orderOf (s * t) ≠ 2`
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [c.s_inv, pow_two] at h
    exact h
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [c.split.invol, pow_two] at h
    exact h
  -- if `f = 2` then `s` and `t` commute, and the structure identity gives `t ∈ Q ≤ H`
  have hf_ne_two : orderOf (s * t) ≠ 2 := by
    intro hf2
    have hst2 : (s * t) * (s * t) = 1 := by
      have h := pow_orderOf_eq_one (s * t)
      rw [hf2, pow_two] at h
      exact h
    have hts : t * s * t = s := by
      have h1 : s * (t * s * t) = s * s := by
        rw [show s * (t * s * t) = (s * t) * (s * t) by group, hst2, hs2]
      exact mul_left_cancel h1
    have hsr : s = r⁻¹ * t * r := by rw [← c.sid, hts]
    have htQ : t ∈ Q := by
      have ht : t = r * s * r⁻¹ := by rw [hsr]; group
      rw [ht]
      exact Q.mul_mem (Q.mul_mem c.r_mem c.s_mem) (Q.inv_mem c.r_mem)
    exact c.split.not_mem (c.split.le htQ)
  -- ## `R ⊓ Q = ⊥`
  have hRQ : h15.R ⊓ Q = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzR, hzQ⟩ := Subgroup.mem_inf.mp hz
    by_contra hz1
    have hzCQ : z ∈ Work.ThmF.ChV3.CQ Q P :=
      Subgroup.mem_inf.mpr ⟨hzQ, h15.hRc hzR⟩
    have hzKer : z ∉ Work.ThmF.ChV3.Ker H Q P t := by
      rw [h7]
      intro hzP
      have hzD : z ∈ twoPoint H t :=
        Work.ThreePoints.mem_twoPoint.mpr ⟨(Work.ThreePoints.mem_centD.mp (c.P_le hzP)).1,
          (Work.ThreePoints.mem_centD.mp (c.P_le hzP)).2.1⟩
      have hmem : z ∈ Q ⊓ twoPoint H t := ⟨hzQ, hzD⟩
      rw [c.split.inf_eq, Subgroup.mem_bot] at hmem
      exact hz1 hmem
    exact hz1 (h15.hfpf z hzR hzKer z hzCQ (by
      rw [h7, show z * z * z⁻¹ * z⁻¹ = 1 by group]
      exact P.one_mem))
  -- ## `C_Q(P)` centralises `R ⊓ H`
  have hcentral : ∀ y ∈ Work.ThmF.ChV3.CQ Q P, ∀ w ∈ h15.R, w ∈ H → y * w * y⁻¹ = w := by
    intro y hy w hwR hwH
    have hyC : y ∈ Work.ThmF.ChV3.CG P := (Subgroup.mem_inf.mp hy).2
    have hyQ : y ∈ Q := (Subgroup.mem_inf.mp hy).1
    have hyN : y ∈ Subgroup.normalizer (h15.R : Set G) := h15.hRn hyC
    have hywR : y * w * y⁻¹ ∈ h15.R := (Subgroup.mem_normalizer_iff.mp hyN w).mp hwR
    have hcommR : y * w * y⁻¹ * w⁻¹ ∈ h15.R := h15.R.mul_mem hywR (h15.R.inv_mem hwR)
    have hywQ : w * y * w⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (c.split.normal hwH) y).mp hyQ
    have hcommQ : y * w * y⁻¹ * w⁻¹ ∈ Q := by
      have h2 : w * y * w⁻¹ * y⁻¹ ∈ Q := Q.mul_mem hywQ (Q.inv_mem hyQ)
      have h3 : (w * y * w⁻¹ * y⁻¹)⁻¹ ∈ Q := Q.inv_mem h2
      rwa [show (w * y * w⁻¹ * y⁻¹)⁻¹ = y * w * y⁻¹ * w⁻¹ by group] at h3
    have hmem : y * w * y⁻¹ * w⁻¹ ∈ h15.R ⊓ Q := ⟨hcommR, hcommQ⟩
    rw [hRQ, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp hmem
  refine le_antisymm ?_ ?_
  · -- ## `R ⊓ (H ⊓ C_G(P)) ≤ P`
    rintro x ⟨hxR, hxH, _⟩
    by_contra hxP
    have hxKer : x ∉ Work.ThmF.ChV3.Ker H Q P t := by rw [h7]; exact hxP
    -- `hfpf` forces `C_Q(P) = ⊥`
    have hCQbot : Work.ThmF.ChV3.CQ Q P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      refine h15.hfpf x hxR hxKer y hy ?_
      rw [h7, hcentral y hy x hxR hxH, mul_inv_cancel]
      exact P.one_mem
    -- ... which contradicts `|C_Q(P)| = f^m - 1 ≥ 2`
    have hcard : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 1 := by
      rw [hCQbot]
      exact Subgroup.card_bot
    have hone : 1 + 1 = orderOf (s * t) ^ h15.m := by
      have h := h15.hcq
      rwa [hcard] at h
    have hf3 : 3 ≤ orderOf (s * t) := by
      have := h15.hf.two_le
      omega
    have hle : orderOf (s * t) ^ 1 ≤ orderOf (s * t) ^ h15.m :=
      Nat.pow_le_pow_right (by omega) h15.hm
    rw [pow_one] at hle
    omega
  · -- ## `P ≤ R ⊓ (H ⊓ C_G(P))`
    intro x hx
    have hxKer : x ∈ Work.ThmF.ChV3.Ker H Q P t := by rw [h7]; exact hx
    exact ⟨h15.hNR hxKer, (Work.ThreePoints.mem_centD.mp (c.P_le hx)).1,
      (Subgroup.mem_inf.mp hxKer).2⟩

end Work.ThmF.ChV3.Prove
