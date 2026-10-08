import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.PSU3.RankOne.canon_conj
import Submission.Work.PSU3.StageB.Canon

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The `h`-value of `r · r^{-k}` (Peterfalvi II, Ch. VI §2, formula (4))

Let `H = Q ⋊ D` be split rank-one data with involution `t ∉ H`, `D = H ∩ H^t`, and let
`(s, r)` be a solution of the structure identity `t s t = r⁻¹ t r` with `s ∈ Inv(Q)`, `r ∈ Q`
(Ch. V §2 Lemma 1 b)).  Fix `k ∈ K - {1}` (`K = J(D,t) = Kset H t`, assumed to be a *subgroup*
here, i.e. `Ksub H t = Kset H t`), and let `ℓ ∈ K` be the element with
`ℓ⁻¹ s ℓ = s k s k⁻¹` (Ch. I §2, regularity of the action of `K` on `Inv H`).

Then the canonical form (Ch. VII §1) of `t (r r^{-k}) t` is
```
t (r r^{-k}) t = (r r^{-ℓ⁻¹}) (ℓ² k²) t (r^{ℓ⁻¹ k^{-2}} r^{-k^{-1}}),
```
proved in Ch. VI §2 (p. 261) as the displayed computation leading to formula (4),
`f(rr^{-k}) = r^{ℓ⁻¹ k^{-2}} r^{-k^{-1}}`, `g(rr^{-k}) = rr^{-ℓ⁻¹}`, `h(rr^{-k}) = ℓ²k²`.

This file proves the corresponding existential statement: the `D`-component of the canonical
form of `t (r r^{-k}) t` lies in `Kset H t` (with `Q`-components in `Q`).
-/

namespace Work.PSU3.StageA

theorem HValueOfRRk {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hr1 : r ≠ 1)
    (hsr : t * s * t = r⁻¹ * t * r)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (hfree : ∀ k ∈ Work.ThmF.Kset H t, k ≠ 1 → ∀ x ∈ Q, k⁻¹ * x * k = x → x = 1) :
    ∀ k ∈ Work.ThmF.Kset H t, k ≠ 1 → ∃ a ∈ Q, ∃ k' ∈ Work.ThmF.Kset H t, ∃ b ∈ Q,
      t * (r * (k⁻¹ * r⁻¹ * k)) * t = a * k' * t * b := by
  intro k hk hk1
  -- ## Basic setup
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := hS.split
  have ht : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  have hi : t⁻¹ = t := Work.RankOneUniqueness.inv_eq_self hsplit
  have ht2 : ∀ x : G, t * (t * x) = x := fun x => Work.RankOneUniqueness.mul_self_mul hsplit x
  have hkD : k ∈ Submission.Blueprint.twoPoint H t := Work.ThmF.Kset_subset H t hk
  have hkH : k ∈ H := Work.RankOneUniqueness.twoPoint_le_left H t hkD
  have hsH : s ∈ H := hsplit.le hs
  have hrH : r ∈ H := hsplit.le hr
  have hkKsub : k ∈ (Work.ThmF.Ksub H t : Set G) := by rw [hKsub]; exact hk
  -- `t` inverts every element of `Kset H t`
  have hkt : t * k * t = k⁻¹ := by
    have h := (Work.ThmF.mem_Kset_iff.mp hk).2
    rwa [hi] at h
  have hkt_inv : t * k⁻¹ * t = k := by
    have h := congrArg (fun z : G => z⁻¹) hkt
    simpa only [mul_assoc, mul_inv_rev, inv_inv, hi] using h
  -- ## The two relations between `t`, `r` and `s` (from the structure identity (2))
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
  -- ## `s k s k⁻¹` is an involution of `H` (involutions of `H` commute, Ch. V §1 Prop. 1 (c))
  have hs_sq : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hsInv : s ∈ Submission.Blueprint.involutions (H : Set G) := ⟨hsH, hs2⟩
  have hs'2 : orderOf (k * s * k⁻¹) = 2 := by
    rw [Work.ThmF.Bender.orderOf_conj_eq, hs2]
  have hs'Inv : k * s * k⁻¹ ∈ Submission.Blueprint.involutions (H : Set G) :=
    ⟨H.mul_mem (H.mul_mem hkH hsH) (H.inv_mem hkH), hs'2⟩
  have hs'_sq : (k * s * k⁻¹) * (k * s * k⁻¹) = 1 := by
    have h := pow_orderOf_eq_one (k * s * k⁻¹)
    rw [hs'2] at h
    simpa [pow_two] using h
  have hcomm := Work.ThmF.L5.involutions_commute hS.situation hC4 hsplit s hsInv
    (k * s * k⁻¹) hs'Inv
  have hs1 : s ≠ 1 := by
    intro hcon
    rw [hcon, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  have hskskH : s * k * s * k⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem hsH hkH) hsH) (H.inv_mem hkH)
  have hsksk_ne : s * k * s * k⁻¹ ≠ 1 := by
    intro hcon
    have h1 : s * (k * s * k⁻¹) = 1 := by simpa only [mul_assoc] using hcon
    have h2 : k * s * k⁻¹ = s⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs_sq
    have h3 : k * s * k⁻¹ = s := by rw [h2, hsi]
    have h4 : k⁻¹ * s * k = s := by
      have hh := congrArg (fun z : G => k⁻¹ * z * k) h3
      have e : k⁻¹ * (k * s * k⁻¹) * k = s := by group
      rw [e] at hh
      exact hh.symm
    exact hs1 (hfree k hk hk1 s hs h4)
  have hsksk2 : (s * k * s * k⁻¹) * (s * k * s * k⁻¹) = 1 := by
    have hx : s * k * s * k⁻¹ = s * (k * s * k⁻¹) := by group
    rw [hx]
    calc (s * (k * s * k⁻¹)) * (s * (k * s * k⁻¹))
        = s * ((k * s * k⁻¹) * s) * (k * s * k⁻¹) := by group
      _ = s * (s * (k * s * k⁻¹)) * (k * s * k⁻¹) := by rw [← hcomm]
      _ = (s * s) * ((k * s * k⁻¹) * (k * s * k⁻¹)) := by group
      _ = 1 := by rw [hs_sq, hs'_sq, mul_one]
  have hsksk_ord : orderOf (s * k * s * k⁻¹) = 2 := by
    have hdvd : orderOf (s * k * s * k⁻¹) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsksk2)
    have hle : orderOf (s * k * s * k⁻¹) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hne : orderOf (s * k * s * k⁻¹) ≠ 1 :=
      fun h => hsksk_ne (orderOf_eq_one_iff.mp h)
    have hpos : 0 < orderOf (s * k * s * k⁻¹) := orderOf_pos _
    omega
  have hskskInv : s * k * s * k⁻¹ ∈ Submission.Blueprint.involutions (H : Set G) :=
    ⟨hskskH, hsksk_ord⟩
  -- ## The element `w ∈ K` with `w s w⁻¹ = s k s k⁻¹` (regularity of the action on `Inv H`)
  obtain ⟨w, hw⟩ := Work.ThmF.L5.Kset_regular hsplit s hsInv (s * k * s * k⁻¹) hskskInv
  obtain ⟨⟨hwmem, hweq⟩, -⟩ := hw
  have hwKsub : w ∈ (Work.ThmF.Ksub H t : Set G) := by rw [hKsub]; exact hwmem
  have hwinvKsub : w⁻¹ ∈ (Work.ThmF.Ksub H t : Set G) := (Work.ThmF.Ksub H t).inv_mem hwKsub
  have hwinvmem : w⁻¹ ∈ Work.ThmF.Kset H t := by rw [← hKsub]; exact hwinvKsub
  have hwH : w ∈ H :=
    Work.RankOneUniqueness.twoPoint_le_left H t (Work.ThmF.Kset_subset H t hwmem)
  have hwinvH : w⁻¹ ∈ H := H.inv_mem hwH
  have hwt : t * w * t = w⁻¹ := by
    have h := (Work.ThmF.mem_Kset_iff.mp hwmem).2
    rwa [hi] at h
  have hw_invt : t * w⁻¹ * t = w := by
    have h := congrArg (fun z : G => z⁻¹) hwt
    simpa only [mul_assoc, mul_inv_rev, inv_inv, hi] using h
  have hterm1 : t * (w⁻¹)⁻¹ * t = w⁻¹ := by rw [inv_inv, hwt]
  -- the relation `s k s = w⁻¹ s w⁻¹ k` (with `ℓ = w⁻¹`)
  have hsks : s * k * s = (w⁻¹)⁻¹ * s * w⁻¹ * k := by
    rw [show (w⁻¹)⁻¹ = w from inv_inv w, hweq]
    group
  have hltl : w⁻¹ * t * w⁻¹ = t := by
    have hkey : (w⁻¹ * t * w⁻¹) * t = 1 := by
      have h : w⁻¹ * (t * w⁻¹ * t) = 1 := by rw [hw_invt, inv_mul_cancel]
      rw [show (w⁻¹ * t * w⁻¹) * t = w⁻¹ * (t * w⁻¹ * t) from by group]
      exact h
    calc w⁻¹ * t * w⁻¹ = (w⁻¹ * t * w⁻¹) * (t * t) := by rw [ht, mul_one]
      _ = ((w⁻¹ * t * w⁻¹) * t) * t := by group
      _ = 1 * t := by rw [hkey]
      _ = t := one_mul t
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
  -- ## The value of `t (r r^{-k}) t` (Ch. VI §2 (4))
  have hmain : t * (r * (k⁻¹ * r⁻¹ * k)) * t
      = r * w⁻¹ * r⁻¹ * t * r * w * k⁻¹ * r⁻¹ * k⁻¹ := by
    calc t * (r * (k⁻¹ * r⁻¹ * k)) * t
        = (t * r * t) * (t * k⁻¹ * t) * (t * r⁻¹ * t) * (t * k * t) := by
          simp only [mul_assoc, ht2]
      _ = (r * t * s) * k * (s * t * r⁻¹) * k⁻¹ := by
          rw [htrt, hkt_inv, htrit, hkt]
      _ = r * t * (s * k * s) * t * r⁻¹ * k⁻¹ := by group
      _ = r * t * ((w⁻¹)⁻¹ * s * w⁻¹ * k) * t * r⁻¹ * k⁻¹ := by rw [hsks]
      _ = r * (t * ((w⁻¹)⁻¹ * s * w⁻¹ * k) * t) * r⁻¹ * k⁻¹ := by group
      _ = r * ((t * (w⁻¹)⁻¹ * t) * (t * s * t) * (t * w⁻¹ * t) * (t * k * t))
            * r⁻¹ * k⁻¹ := by simp only [mul_assoc, ht2]
      _ = r * (w⁻¹ * (r⁻¹ * t * r) * w * k⁻¹) * r⁻¹ * k⁻¹ := by
          rw [hterm1, hsr, hw_invt, hkt]
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
  have hK' : (w⁻¹ * w⁻¹) * (k * k) ∈ Work.ThmF.Kset H t := by
    rw [← hKsub]
    exact (Work.ThmF.Ksub H t).mul_mem
      ((Work.ThmF.Ksub H t).mul_mem hwinvKsub hwinvKsub)
      ((Work.ThmF.Ksub H t).mul_mem hkKsub hkKsub)
  have hB : ((k * k) * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹)) * (k * r⁻¹ * k⁻¹) ∈ Q := by
    refine Q.mul_mem ?_ ?_
    · have hX : w⁻¹ * r * w ∈ Q := by
        simpa only [inv_inv] using
          (Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := w⁻¹) hwinvH hr)
      have hY := Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := k * k)
        (H.mul_mem hkH hkH) hX
      simpa only [mul_inv_rev, inv_inv] using hY
    · exact Work.RankOneUniqueness.conj_mem_of_mem hsplit hkH (Q.inv_mem hr)
  exact ⟨r * (w⁻¹ * r⁻¹ * w), hA, (w⁻¹ * w⁻¹) * (k * k), hK',
    ((k * k) * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹)) * (k * r⁻¹ * k⁻¹), hB,
    hmain.trans hrhs.symm⟩

end Work.PSU3.StageA
