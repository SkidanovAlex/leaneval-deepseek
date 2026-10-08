import Mathlib
import Submission.Work.ThreePoints.Basic
import Submission.Work.NPC.All
import Submission.Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two
import Submission.Work.BrauerSuzuki.Group.hasFourGroup_of_two_involutions
import Submission.Work.BrauerSuzuki.Group.odd_orderOf_mul
import Submission.Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution
import Submission.Work.BrauerSuzuki.Glue.brauerSuzuki_of_weak
import Submission.Work.BrauerSuzuki.Glue.weak_of_large_and_q8
import Submission.Work.BrauerSuzuki.Sylow.genQuaternion_sylow_quotient
import Submission.Work.BrauerSuzuki.Dade.main
import Submission.Work.BrauerSuzuki.Q8.strongProved

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThreePoints

open Submission.Blueprint

/-- **Two distinct involutions whose product has even order generate a four-group.**

The reduction used below: if `orderOf (x * y) = m` is even then `z := (x * y) ^ (m / 2)` is an
involution and both `x` and `y` conjugate `z` to `z⁻¹ = z`, so both commute with `z`.  Hence either
`z = x` (and `x`, `y` are distinct commuting involutions) or `z ≠ x` (and `x`, `z` are distinct
commuting involutions). -/
theorem hasFourGroup_of_two_involutions_of_even {G : Type*} [Group G] [Finite G] {x y : G}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hne : x ≠ y) (h2 : 2 ∣ orderOf (x * y)) :
    Submission.Blueprint.HasFourGroup G := by
  have hx2 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa [pow_two] using h
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    simpa [pow_two] using h
  have hxin : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx2
  have hyin : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy2
  set m : ℕ := orderOf (x * y) with hm
  have hm0 : m ≠ 0 := by
    rw [hm]
    exact (orderOf_pos (x * y)).ne'
  have hmev : Even m := even_iff_two_dvd.mpr h2
  have hmord : orderOf (x * y) = m := hm.symm
  have hz2 : orderOf ((x * y) ^ (m / 2)) = 2 :=
    Work.BrauerSuzuki.Group.orderOf_pow_div_two hmev hm0 hmord
  set z : G := (x * y) ^ (m / 2) with hz
  have hzsq : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hzsq
  have hxy_inv : (x * y)⁻¹ = y * x := by rw [mul_inv_rev, hxin, hyin]
  have hconjx : (MulAut.conj x) (x * y) = (x * y)⁻¹ := by
    rw [MulAut.conj_apply]
    rw [show x * (x * y) * x⁻¹ = y * x⁻¹ by rw [← mul_assoc, hx2, one_mul]]
    rw [hxin, hxy_inv]
  have hconjy : (MulAut.conj y) (x * y) = (x * y)⁻¹ := by
    rw [MulAut.conj_apply]
    rw [show y * (x * y) * y⁻¹ = y * x by group]
    rw [hxy_inv]
  have hxz : x * z * x⁻¹ = z := by
    have h1 : x * z * x⁻¹ = (MulAut.conj x) z := by rw [MulAut.conj_apply]
    rw [h1, hz, map_pow, hconjx, inv_pow, ← hz, hzinv]
  have hyz : y * z * y⁻¹ = z := by
    have h1 : y * z * y⁻¹ = (MulAut.conj y) z := by rw [MulAut.conj_apply]
    rw [h1, hz, map_pow, hconjy, inv_pow, ← hz, hzinv]
  rcases eq_or_ne z x with hzx | hzx
  · refine ⟨x, y, hx, hy, hne, ?_⟩
    have hyx : y * x * y⁻¹ = x := by rw [← hzx]; exact hyz
    have h1 : y * x = (y * x * y⁻¹) * y := by group
    rw [h1, hyx]
  · refine ⟨x, z, hx, hz2, fun h => hzx h.symm, ?_⟩
    have h1 : x * z = (x * z * x⁻¹) * x := by group
    rw [h1, hxz]

/-- **Brauer–Suzuki** (`Submission.Blueprint.BrauerSuzukiProp`) from the two published cases:
Dade's theorem for generalized quaternion Sylow `2`-subgroups of order `≥ 16`
(`Work.BrauerSuzuki.Dade.main`) and Glauberman's `Q₈` case
(`Work.BrauerSuzuki.Q8.strongProved`), glued by `Work.BrauerSuzuki.Glue.weak_of_large_and_q8`
and `Work.BrauerSuzuki.Glue.brauerSuzuki_of_weak` (the classification of `2`-groups with a
unique involution `Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution` and the
descent of a generalized quaternion Sylow `2`-subgroup to `G ⧸ O_{2'}(G)`
`Work.BrauerSuzuki.Sylow.genQuaternion_sylow_quotient` are already proved). -/
theorem brauerSuzukiProp_from_cases : Submission.Blueprint.BrauerSuzukiProp :=
  Work.BrauerSuzuki.Glue.brauerSuzuki_of_weak
    (Work.BrauerSuzuki.Glue.weak_of_large_and_q8 Work.BrauerSuzuki.Dade.main
      Work.BrauerSuzuki.Q8.strongProved)
    (fun P _ _ hP hu => Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution hP hu)
    (fun G _ _ S hS => Work.BrauerSuzuki.Sylow.genQuaternion_sylow_quotient S hS)

/-- **An involution is central modulo `O_{2'}(G)`**: this is the form of the Brauer–Suzuki
theorem (`G = O_{2'}(G)·C_G(t)`) that is used below. -/
theorem involution_commutator_mem_oddCore {G : Type} [Group G] [Finite G]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (h4 : ¬ Submission.Blueprint.HasFourGroup G)
    {v : G} (hv : orderOf v = 2) (g : G) :
    v * g * v⁻¹ * g⁻¹ ∈ Submission.Blueprint.oddCore G := by
  classical
  set O : Subgroup G := Submission.Blueprint.oddCore G with hO
  have hOn : O.Normal := by rw [hO]; infer_instance
  have hsup : O ⊔ Subgroup.centralizer ({v} : Set G) = ⊤ := by
    rw [hO]; exact hBrSz G h4 v hv
  obtain ⟨o, ho, c, hc, hoc⟩ :=
    Work.BrauerSuzuki.Glue.exists_mul_of_sup_eq_top_of_normal hOn hsup g
  have hcv : c * v = v * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hv2 : v * v = 1 := by
    have h := pow_orderOf_eq_one v
    rw [hv] at h
    simpa [pow_two] using h
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  have hcv' : c * v⁻¹ = v⁻¹ * c := by rw [hvinv, hcv]
  rw [← hoc]
  have hkey : v * (o * c) * v⁻¹ * (o * c)⁻¹ = (v * o * v⁻¹) * o⁻¹ := by
    calc v * (o * c) * v⁻¹ * (o * c)⁻¹
        = v * o * (c * v⁻¹ * c⁻¹) * o⁻¹ := by group
      _ = v * o * (v⁻¹ * c * c⁻¹) * o⁻¹ := by rw [hcv']
      _ = (v * o * v⁻¹) * o⁻¹ := by group
  rw [hkey]
  exact O.mul_mem (hOn.conj_mem o ho v) (O.inv_mem ho)

/-- **Peterfalvi I Ch. I §3 Prop. 1, Case 2, combinatorial core.**  In a finite group of `2`-rank
`1` (no four-group), the product of three involutions whose first two are distinct has even order.

This is the step the source proves at p. 154 by Brauer–Suzuki ("`M/O_{2'}(M)` has a unique
involution, so `t₁t₂ ∈ O_{2'}(M)`, so `t₁t₂t` has even order"), and it is the *only* use of the
Brauer–Suzuki black box inside `Work.ThreePoints.sec3_prop1_transitive`.  It is used to produce an
element of even order in a normaliser of a maximal `p`-subgroup fixing three points (Ch. I §3
Prop. 1, Case 2), hence is on the critical path of Ch. I §4 Prop. 2 and of Ch. II §4 Prop. 1 (a).

Route.  `2`-rank `1` means the Sylow `2`-subgroups are cyclic or generalized quaternion.
* `s * t` has odd order (otherwise `⟨s,t⟩ ≅ D_{2m}` with `m` even contains a four-group).
* Cyclic Sylow `2`: `G` is `2`-nilpotent, i.e. has a normal `2`-complement `N` of odd order
  (`Work.NPC.frobenius_npc` + `N_G(Q)/C_G(Q) ↪ Aut(Q)`, a `2`-group for cyclic `Q ≠ 1`); every
  element of odd order lies in `N`, so `s*t ∈ N`; if `s*t*u` also had odd order then
  `u = (s*t)⁻¹*(s*t*u) ∈ N`, contradicting `u ∉ N` (`u` has order `2`).
* Generalized quaternion Sylow `2` with `s ≠ t`: the conclusion is what remains after the cyclic
  case; Brauer–Suzuki (`G = O_{2'}(G)·C_G(z)` for an involution `z`) gives `s*t ∈ O_{2'}(G)`,
  and then `s*t*u ∉ O_{2'}(G)` (its image in `G/O_{2'}(G)` is the unique involution), so it has
  even order.  A BrSz-free route is welcome but not required if the `2`-rank-`1` structure theory
  (cyclic or generalized quaternion Sylow, `2`-nilpotency in the cyclic case, and uniqueness of
  the involution modulo `O_{2'}` in the generalized quaternion case) is available or can be built
  from `Submission.Work.BrauerSuzuki.*`.

Here this is used in its uniform form: Brauer–Suzuki says that every involution is central modulo
`O := O_{2'}(G)`.  Then `s` and `t` have the same image `s̄ = t̄` in `Ḡ = G ⧸ O` (if `s̄ ≠ t̄`,
the two distinct commuting involutions `s̄`, `t̄` would make `orderOf (s * t)` even, whence a
four-group in `G`, contradicting `h4`), so `s * t ∈ O`; and the image of `s * t * u` in `Ḡ` is
`ū ≠ 1` (as `u ∉ O`, `|O|` being odd and `orderOf u = 2`), an involution of order `2`.  Hence
`2 ∣ orderOf (s * t * u)`. -/
theorem three_involutions_even {G : Type} [Group G] [Finite G]
    (h4 : ¬ Submission.Blueprint.HasFourGroup G) {s t u : G}
    (hs : orderOf s = 2) (ht : orderOf t = 2) (hu : orderOf u = 2) (hne : s ≠ t) :
    Even (orderOf (s * t * u)) := by
  classical
  set O : Subgroup G := Submission.Blueprint.oddCore G with hO
  have hOn : O.Normal := by rw [hO]; infer_instance
  set π : G →* G ⧸ O := QuotientGroup.mk' O with hπ
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs] at h
    simpa [pow_two] using h
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu] at h
    simpa [pow_two] using h
  have hodd : Odd (Nat.card O) := by
    rw [hO]; exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
  have hnotmem : ∀ v : G, orderOf v = 2 → v ∉ O := by
    intro v hv hvo
    have hdvd : orderOf v ∣ Nat.card O := by
      have h1 := orderOf_dvd_natCard (⟨v, hvo⟩ : O)
      rwa [Subgroup.orderOf_mk] at h1
    rw [hv] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hker : ∀ x : G, π x = 1 ↔ x ∈ O := by
    intro x
    rw [hπ, ← MonoidHom.mem_ker, QuotientGroup.ker_mk' O]
  have hne_s : π s ≠ 1 := fun h => hnotmem s hs ((hker s).mp h)
  have hne_t : π t ≠ 1 := fun h => hnotmem t ht ((hker t).mp h)
  have hne_u : π u ≠ 1 := fun h => hnotmem u hu ((hker u).mp h)
  have hp2_s : (π s) ^ 2 = 1 := by rw [pow_two, ← map_mul, hs2, map_one]
  have hp2_t : (π t) ^ 2 = 1 := by rw [pow_two, ← map_mul, ht2, map_one]
  have hp2_u : (π u) ^ 2 = 1 := by rw [pow_two, ← map_mul, hu2, map_one]
  have hcomm_st : π s * π t = π t * π s :=
    Work.BrauerSuzuki.Glue.mk_comm_of_commutator_mem (O := O)
      (involution_commutator_mem_oddCore brauerSuzukiProp_from_cases h4 hs t)
  by_cases hst : π s = π t
  · -- The images agree: `s * t ∈ O` and the image of `s * t * u` is the involution `π u`.
    have hstO : s * t ∈ O := by
      refine (hker (s * t)).mp ?_
      rw [map_mul, hst, ← pow_two]
      exact hp2_t
    have hstu : π (s * t * u) = π u := by
      rw [map_mul, (hker (s * t)).mpr hstO, one_mul]
    have hord_u : orderOf (π u) = 2 := orderOf_eq_prime hp2_u hne_u
    have hdvd : orderOf (π u) ∣ orderOf (s * t * u) := by
      rw [← hstu]; exact orderOf_map_dvd π (s * t * u)
    rw [hord_u] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  · -- The images differ: `s * t` has even order, forcing a four-group.
    have hprod_ne : π (s * t) ≠ 1 := by
      rw [map_mul]
      intro h
      have h1 : π s = (π t)⁻¹ := mul_eq_one_iff_eq_inv.mp h
      have h2 : (π t)⁻¹ = π t := inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hp2_t)
      exact hst (h1.trans h2)
    have hprod_sq : (π (s * t)) ^ 2 = 1 := by
      rw [map_mul, pow_two]
      calc (π s * π t) * (π s * π t) = π s * (π t * π s) * π t := by group
        _ = π s * (π s * π t) * π t := by rw [hcomm_st]
        _ = (π s * π s) * (π t * π t) := by group
        _ = 1 := by rw [← pow_two, ← pow_two, hp2_s, hp2_t, one_mul]
    have hord_st : orderOf (π (s * t)) = 2 := orderOf_eq_prime hprod_sq hprod_ne
    have h2dvd : 2 ∣ orderOf (s * t) := by
      rw [← hord_st]; exact orderOf_map_dvd π (s * t)
    exact absurd (hasFourGroup_of_two_involutions_of_even hs ht hne h2dvd) h4

end Work.ThreePoints
