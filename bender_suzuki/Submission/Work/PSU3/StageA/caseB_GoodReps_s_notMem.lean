import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageA.caseC_W_semireg
import Submission.Work.ThmF.ChV12.prop1a

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.caseB_GoodReps_s_notMem`

The representative `s` of the `K`-orbits on `Q#` is not of the form `r · r^{-k}`, `k ∈ Kset`:

  `¬ ∃ k ∈ Kset H t, r * (k⁻¹ * r⁻¹ * k) = s`

for `s ∈ Q` an involution and `r ∈ Q` with `r * r ≠ 1`.

The proof is elementary and uses only two structural inputs:

* `Q₀ = Q0sub H = ⟨Inv H⟩` is elementary abelian and **central** in `Q`
  (`Q0sub_structure`, `Q0sub_le_centerOf`), so every `u ∈ Q₀` satisfies `u * u = 1` and commutes
  with every element of `Q`;
* `Kset H t` acts **freely** on `Q#`: `ChV12.prop1a` (`C_Q(k) = 1` for `1 ≠ k ∈ Kset H t`).

Indeed, if `k ∈ Kset` with `k ≠ 1` and `u := r * (k⁻¹ * r⁻¹ * k) = r * w⁻¹` (where
`w := k⁻¹ * r * k`) lies in `Q₀`, then `w = u⁻¹ * r` with `u` central of order `2`, so

  `w * w = (u⁻¹ * r) * (u⁻¹ * r) = u⁻² * r * r = r * r`,

while on the other hand `w * w = k⁻¹ * (r * r) * k`.  Hence `k` commutes with `r * r ∈ Q` and
`ChV12.prop1a` forces `r * r = 1`, contradicting the hypothesis.  For `k = 1` the element
`r * (k⁻¹ * r⁻¹ * k)` is `1`, and `s ≠ 1` because `orderOf s = 2`.
-/

namespace Work.PSU3.StageA

theorem caseB_GoodReps_s_notMem {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hr2 : r * r ≠ 1) :
    ¬ ∃ k ∈ Work.ThmF.Kset H t, r * (k⁻¹ * r⁻¹ * k) = s := by
  rintro ⟨k, hkK, hkeq⟩
  -- `s ≠ 1`, as `orderOf s = 2`.
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  by_cases hk1 : k = 1
  · -- `k = 1` gives `r * (1 * r⁻¹ * 1) = 1`, and `1 ≠ s`.
    subst hk1
    exact hs1 (by rw [← hkeq]; group)
  · -- `s ∈ Q₀`, hence also the left hand side `u` lies in `Q₀`.
    have hsQ0 : s ∈ Work.ThmF.Q0sub H :=
      Work.ThmF.Q0_le_Q0sub H (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨hS.split.le hs, hs2⟩))
    have huQ0 : r * (k⁻¹ * r⁻¹ * k) ∈ Work.ThmF.Q0sub H := hkeq ▸ hsQ0
    -- `Q₀` is central in `Q` and elementary abelian.
    have hcenter := (Work.ThmF.mem_centerOf (Q := Q)).mp (Q0sub_le_centerOf hS hC4 huQ0)
    have hucomm : (r * (k⁻¹ * r⁻¹ * k)) * r = r * (r * (k⁻¹ * r⁻¹ * k)) := hcenter.2 r hr
    have husq : (r * (k⁻¹ * r⁻¹ * k)) * (r * (k⁻¹ * r⁻¹ * k)) = 1 :=
      (Q0sub_structure hS hC4).1 _ huQ0
    have hucomm_inv :
        (r * (k⁻¹ * r⁻¹ * k))⁻¹ * r = r * (r * (k⁻¹ * r⁻¹ * k))⁻¹ := by
      calc (r * (k⁻¹ * r⁻¹ * k))⁻¹ * r
          = (r * (k⁻¹ * r⁻¹ * k))⁻¹ * (r * (r * (k⁻¹ * r⁻¹ * k)))
              * (r * (k⁻¹ * r⁻¹ * k))⁻¹ := by group
        _ = (r * (k⁻¹ * r⁻¹ * k))⁻¹ * ((r * (k⁻¹ * r⁻¹ * k)) * r)
              * (r * (k⁻¹ * r⁻¹ * k))⁻¹ := by rw [← hucomm]
        _ = r * (r * (k⁻¹ * r⁻¹ * k))⁻¹ := by group
    have huinv_sq : (r * (k⁻¹ * r⁻¹ * k))⁻¹ * (r * (k⁻¹ * r⁻¹ * k))⁻¹ = 1 := by
      rw [inv_eq_of_mul_eq_one_right husq]
      exact husq
    -- `w * w = r * r`, where `w := k⁻¹ * r * k = u⁻¹ * r`.
    have hww : (k⁻¹ * r * k) * (k⁻¹ * r * k) = r * r := by
      rw [show k⁻¹ * r * k = (r * (k⁻¹ * r⁻¹ * k))⁻¹ * r from by group]
      calc ((r * (k⁻¹ * r⁻¹ * k))⁻¹ * r) * ((r * (k⁻¹ * r⁻¹ * k))⁻¹ * r)
          = (r * (k⁻¹ * r⁻¹ * k))⁻¹ * (r * (r * (k⁻¹ * r⁻¹ * k))⁻¹) * r := by group
        _ = (r * (k⁻¹ * r⁻¹ * k))⁻¹
              * ((r * (k⁻¹ * r⁻¹ * k))⁻¹ * r) * r := by rw [← hucomm_inv]
        _ = ((r * (k⁻¹ * r⁻¹ * k))⁻¹ * (r * (k⁻¹ * r⁻¹ * k))⁻¹) * (r * r) := by group
        _ = r * r := by rw [huinv_sq, one_mul]
    -- on the other hand `w * w = k⁻¹ * (r * r) * k`.
    have hww' : (k⁻¹ * r * k) * (k⁻¹ * r * k) = k⁻¹ * (r * r) * k := by group
    have hkey : r * r = k⁻¹ * (r * r) * k := hww.symm.trans hww'
    -- hence `k` commutes with `r * r ∈ Q`, and `ChV12.prop1a` forces `r * r = 1`.
    have hcomm : (r * r) * k = k * (r * r) := by
      have h := congrArg (fun x => k * x) hkey
      rw [show k * (k⁻¹ * (r * r) * k) = (r * r) * k from by group] at h
      exact h.symm
    exact hr2 (Work.ThmF.ChV12.prop1a hS.situation hC4 H Q t hS.split k hkK hk1 (r * r)
      (Q.mul_mem hr hr) hcomm)

end Work.PSU3.StageA
