import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageA.HValueOfRRk

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-- **The canonical data of `r · r^{-k}` (Peterfalvi II, Ch. VI §2).**

In the situation of `PSU3Hyp H Q t`, with the structure identity `t s t = r⁻¹ t r`
(`s ∈ Inv(Q)`, `r ∈ Q`) and `w ∈ K = J(D,t)` the element with `w s w⁻¹ = s k s k⁻¹`
(regularity of the action of `K` on `Inv(H)`), the canonical form of `t (r r^{-k}) t` is

`t (r r^{-k}) t = (r r^{-w}) (w⁻² k²) t (k² r^{-w} k^{-2} · k r^{-1} k^{-1})`,

i.e. `Canon3` holds for the quadruple
`x = r r^{-k}`, `g = r r^{-w}`, `h = w⁻² k²`, `y = k² r^{-w} k^{-2} · k r^{-1} k^{-1}`.

The two ingredients are the `D`-component computed in `HValueOfRRk` (Ch. VI §2, p. 261) and
the expansion `t (r r^{-k}) t = (r t s) k (s t r⁻¹) k⁻¹`, using `s k s = w s w⁻¹ k`. -/
theorem caseB_canon_data_rrk {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) :
    ∀ k ∈ Work.ThmF.Kset H t, k ≠ 1 → ∀ w ∈ Work.ThmF.Kset H t,
      w * s * w⁻¹ = s * k * s * k⁻¹ →
      Work.PSU3.Canon3 H Q t (r * (k⁻¹ * r⁻¹ * k)) (r * (w⁻¹ * r⁻¹ * w))
        ((w⁻¹ * w⁻¹) * (k * k)) (((k * k) * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹)) * (k * r⁻¹ * k⁻¹)) := by
  intro k hk _hk1 w hw hws
  -- ## Basic setup
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := hS.split
  have ht : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  have hi : t⁻¹ = t := Work.RankOneUniqueness.inv_eq_self hsplit
  have ht2 : ∀ x : G, t * (t * x) = x := fun x => Work.RankOneUniqueness.mul_self_mul hsplit x
  have hkD : k ∈ Submission.Blueprint.twoPoint H t := Work.ThmF.Kset_subset H t hk
  have hwD : w ∈ Submission.Blueprint.twoPoint H t := Work.ThmF.Kset_subset H t hw
  have hkH : k ∈ H := Work.RankOneUniqueness.twoPoint_le_left H t hkD
  have hwH : w ∈ H := Work.RankOneUniqueness.twoPoint_le_left H t hwD
  have hwinvH : w⁻¹ ∈ H := H.inv_mem hwH
  -- `t` inverts the elements of `Kset H t` (`t` has order two, so `t⁻¹ = t`)
  have hkt : t * k * t = k⁻¹ := by
    have h := (Work.ThmF.mem_Kset_iff.mp hk).2
    rwa [hi] at h
  have hwt : t * w * t = w⁻¹ := by
    have h := (Work.ThmF.mem_Kset_iff.mp hw).2
    rwa [hi] at h
  have hkt_inv : t * k⁻¹ * t = k := by
    have h := congrArg (fun z : G => z⁻¹) hkt
    simpa only [mul_assoc, mul_inv_rev, inv_inv, hi] using h
  have hw_invt : t * w⁻¹ * t = w := by
    have h := congrArg (fun z : G => z⁻¹) hwt
    simpa only [mul_assoc, mul_inv_rev, inv_inv, hi] using h
  -- ## The two relations between `t`, `r` and `s` (from the structure identity)
  have htrt : t * r * t = r * t * s := by
    have h := congrArg (fun z : G => r * z * t) hsr
    have e1 : r * (t * s * t) * t = r * t * s * (t * t) := by group
    have e2 : r * (r⁻¹ * t * r) * t = t * r * t := by group
    rw [e1, e2, ht, mul_one] at h
    exact h.symm
  have htrit : t * r⁻¹ * t = s * t * r⁻¹ := by
    have h := congrArg (fun z : G => t * z * r⁻¹) hsr
    have e1 : t * (t * s * t) * r⁻¹ = s * t * r⁻¹ := by simp only [mul_assoc, ht2]
    have e2 : t * (r⁻¹ * t * r) * r⁻¹ = t * r⁻¹ * t := by group
    rw [e1, e2] at h
    exact h.symm
  -- ## The relation `s k s = w s w⁻¹ k` (from the hypothesis on `w`)
  have hsks : s * k * s = w * s * w⁻¹ * k := by
    rw [hws]
    group
  -- ## Two auxiliary identities
  have hk2tk2 : (k * k) * t * (k * k) = t := by
    have htk : t * k = k⁻¹ * t := by
      have h := congrArg (fun z : G => z * t) hkt
      have e : (t * k * t) * t = t * k := by simp only [mul_assoc, ht, mul_one]
      rw [e] at h
      exact h
    have htk2 : t * (k * k) = k⁻¹ * k⁻¹ * t := by
      calc t * (k * k) = (t * k) * k := by group
        _ = (k⁻¹ * t) * k := by rw [htk]
        _ = k⁻¹ * (t * k) := by group
        _ = k⁻¹ * (k⁻¹ * t) := by rw [htk]
        _ = k⁻¹ * k⁻¹ * t := by group
    calc (k * k) * t * (k * k) = (k * k) * (t * (k * k)) := by group
      _ = (k * k) * (k⁻¹ * k⁻¹ * t) := by rw [htk2]
      _ = t := by group
  have hltl : w⁻¹ * t * w⁻¹ = t := by
    have hkey : (w⁻¹ * t * w⁻¹) * t = 1 := by
      have h : w⁻¹ * (t * w⁻¹ * t) = 1 := by rw [hw_invt, inv_mul_cancel]
      rw [show (w⁻¹ * t * w⁻¹) * t = w⁻¹ * (t * w⁻¹ * t) from by group]
      exact h
    calc w⁻¹ * t * w⁻¹ = (w⁻¹ * t * w⁻¹) * (t * t) := by rw [ht, mul_one]
      _ = ((w⁻¹ * t * w⁻¹) * t) * t := by group
      _ = 1 * t := by rw [hkey]
      _ = t := one_mul t
  -- ## The value of `t (r r^{-k}) t` (Ch. VI §2 (4))
  have hmain : t * (r * (k⁻¹ * r⁻¹ * k)) * t
      = r * w⁻¹ * r⁻¹ * t * r * w * k⁻¹ * r⁻¹ * k⁻¹ := by
    calc t * (r * (k⁻¹ * r⁻¹ * k)) * t
        = (t * r * t) * (t * k⁻¹ * t) * (t * r⁻¹ * t) * (t * k * t) := by
          simp only [mul_assoc, ht2]
      _ = (r * t * s) * k * (s * t * r⁻¹) * k⁻¹ := by rw [htrt, hkt_inv, htrit, hkt]
      _ = r * t * (s * k * s) * t * r⁻¹ * k⁻¹ := by group
      _ = r * t * (w * s * w⁻¹ * k) * t * r⁻¹ * k⁻¹ := by rw [hsks]
      _ = r * (t * (w * s * w⁻¹ * k) * t) * r⁻¹ * k⁻¹ := by group
      _ = r * ((t * w * t) * (t * s * t) * (t * w⁻¹ * t) * (t * k * t))
            * r⁻¹ * k⁻¹ := by simp only [mul_assoc, ht2]
      _ = r * (w⁻¹ * (r⁻¹ * t * r) * w * k⁻¹) * r⁻¹ * k⁻¹ := by
          rw [hwt, hsr, hw_invt, hkt]
      _ = r * w⁻¹ * r⁻¹ * t * r * w * k⁻¹ * r⁻¹ * k⁻¹ := by group
  -- ## The right-hand side of the target equals the same normal form
  have hrhs : (r * (w⁻¹ * r⁻¹ * w)) * ((w⁻¹ * w⁻¹) * (k * k)) * t
        * (((k * k) * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹)) * (k * r⁻¹ * k⁻¹))
      = r * w⁻¹ * r⁻¹ * t * r * w * k⁻¹ * r⁻¹ * k⁻¹ := by
    have e1 : (r * (w⁻¹ * r⁻¹ * w)) * ((w⁻¹ * w⁻¹) * (k * k)) * t
          * (((k * k) * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹)) * (k * r⁻¹ * k⁻¹))
        = r * w⁻¹ * r⁻¹ * ((w⁻¹)⁻¹ * (w⁻¹ * w⁻¹)) * ((k * k) * t * (k * k))
            * w⁻¹ * r * w * (k⁻¹ * k⁻¹) * k * r⁻¹ * k⁻¹ := by group
    rw [e1, hk2tk2]
    have e2 : r * w⁻¹ * r⁻¹ * ((w⁻¹)⁻¹ * (w⁻¹ * w⁻¹)) * t * w⁻¹ * r * w
          * (k⁻¹ * k⁻¹) * k * r⁻¹ * k⁻¹
        = r * w⁻¹ * r⁻¹ * (((w⁻¹)⁻¹ * (w⁻¹ * w⁻¹)) * t * w⁻¹) * r * w
            * (k⁻¹ * k⁻¹) * k * r⁻¹ * k⁻¹ := by group
    rw [e2, show (w⁻¹)⁻¹ * (w⁻¹ * w⁻¹) * t * w⁻¹ = w⁻¹ * t * w⁻¹ from by group, hltl]
    group
  -- ## Memberships of the three witnesses
  have hA : r * (w⁻¹ * r⁻¹ * w) ∈ Q := by
    refine Q.mul_mem hr ?_
    simpa only [inv_inv] using
      (Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := w⁻¹) hwinvH (Q.inv_mem hr))
  have hD : (w⁻¹ * w⁻¹) * (k * k) ∈ Submission.Blueprint.twoPoint H t :=
    (Submission.Blueprint.twoPoint H t).mul_mem
      ((Submission.Blueprint.twoPoint H t).mul_mem
        ((Submission.Blueprint.twoPoint H t).inv_mem hwD)
        ((Submission.Blueprint.twoPoint H t).inv_mem hwD))
      ((Submission.Blueprint.twoPoint H t).mul_mem hkD hkD)
  have hB : ((k * k) * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹)) * (k * r⁻¹ * k⁻¹) ∈ Q := by
    refine Q.mul_mem ?_ ?_
    · have hX : w⁻¹ * r * w ∈ Q := by
        simpa only [inv_inv] using
          (Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := w⁻¹) hwinvH hr)
      have hY := Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := k * k)
        (H.mul_mem hkH hkH) hX
      simpa only [mul_inv_rev, inv_inv] using hY
    · exact Work.RankOneUniqueness.conj_mem_of_mem hsplit hkH (Q.inv_mem hr)
  exact ⟨hA, hD, hB, hmain.trans hrhs.symm⟩

end Work.PSU3.StageA
