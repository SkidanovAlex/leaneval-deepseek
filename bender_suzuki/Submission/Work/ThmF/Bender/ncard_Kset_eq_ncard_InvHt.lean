import Mathlib
import Submission.Work.ThmF.Bender.DTransInvAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|K(D,t)| = |Inv(H t)|` (Peterfalvi I, Ch. I §2, Prop. 1 (c))

Let `H` be strongly embedded in the finite group `G` and let `t ∉ H` be an involution.  Writing
`K = J(D,t) = {x ∈ D | t x t⁻¹ = x⁻¹}` for `D = H ∩ H^t = twoPoint H t`, and
`InvHt H t = {u | orderOf u = 2 ∧ H^u = H^t}` for the involutions of the coset `tH`, the two sets
have the same cardinality:

  `|K| = |InvHt H t|`.

The bijection is the right multiplication by `t`:

* for `x ∈ K`, `x ∈ H ∩ H^t` and `t x t = x⁻¹`, so `(x t)² = x (t x t) = 1` and `x t ≠ 1`
  (`x t = 1 ⟹ x = t ∉ H`), while `H^{xt} = x H^t x⁻¹ = H^t` because `x ∈ H^t`;
* conversely an involution `u` with `H^u = H^t` satisfies `t⁻¹ u ∈ H` (strong embedding:
  `N_G(H) = H`) — so `u = t h` with `h ∈ H` — and `u² = 1` gives `t h t = h⁻¹`, whence
  `u t = t h t = h⁻¹ ∈ H ∩ H^t` and `t (u t) t = h = (u t)⁻¹`.

Source: Peterfalvi, *Le théorème de Bender–Suzuki I*, Ch. I §2 Prop. 1 (c).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.Bender

open LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type*} [Group G]

/-- If `H^u = H^t` then `u ∈ tH`, i.e. `t⁻¹ * u ∈ H`.  Uses that a strongly embedded subgroup
is self-normalising (`N_G(H) = H`). -/
lemma inv_mem_of_conj_eq {H : Subgroup G} (hH : IsStronglyEmbedded H) {u t : G}
    (h : Submission.Blueprint.conj u H = Submission.Blueprint.conj t H) : t⁻¹ * u ∈ H := by
  have hc : Submission.Blueprint.conj (t⁻¹ * u) H = H := by
    rw [Work.Models.conj_mul, h, Work.Models.conj_inv_conj]
  have hmem : t⁻¹ * u ∈ Subgroup.normalizer (H : Set G) :=
    Work.Models.mem_normalizer_of_conj_eq hc
  rwa [Work.Models.IsStronglyEmbedded.normalizer_eq hH] at hmem

/-- For `x ∈ K = J(D,t)`, the product `x * t` is an involution with `H^{xt} = H^t`, i.e. lies in
`InvHt H t`. -/
lemma mul_t_mem_InvHt [Finite G] {H : Subgroup G} {t : G}
    (ht2 : orderOf t = 2) (htH : t ∉ H) {x : G} (hx : x ∈ Work.ThmF.Kset H t) :
    x * t ∈ Work.ThmF.Bender.InvHt H t := by
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t; rw [ht2] at h; simpa [pow_two] using h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨hxD, hxinv⟩ := Work.ThmF.mem_Kset_iff.mp hx
  obtain ⟨hxH, hxHt⟩ := Work.Models.mem_twoPoint_iff.mp hxD
  have hx_conjHt : x ∈ Submission.Blueprint.conj t H := Work.Models.mem_conj_iff.mpr hxHt
  have hxc : Submission.Blueprint.conj x (Submission.Blueprint.conj t H)
      = Submission.Blueprint.conj t H :=
    Work.Models.conj_self_of_mem_normalizer (Subgroup.le_normalizer hx_conjHt)
  have hconj : Submission.Blueprint.conj (x * t) H = Submission.Blueprint.conj t H := by
    rw [Work.Models.conj_mul, hxc]
  have hxt2 : orderOf (x * t) = 2 := by
    have htx : t * x * t = x⁻¹ := by simpa only [htinv] using hxinv
    have hsq : (x * t) * (x * t) = 1 := by
      calc (x * t) * (x * t) = x * (t * x * t) := by group
        _ = x * x⁻¹ := by rw [htx]
        _ = 1 := mul_inv_cancel x
    apply orderOf_eq_prime
    · rwa [pow_two]
    · intro h1
      have hxt_eq : x = t := by
        calc x = x * 1 := (mul_one x).symm
          _ = x * (t * t) := by rw [htt]
          _ = (x * t) * t := by group
          _ = 1 * t := by rw [h1]
          _ = t := one_mul t
      exact htH (hxt_eq ▸ hxH)
  exact ⟨hxt2, hconj⟩

/-- For `u ∈ InvHt H t` an involution with `H^u = H^t`, the product `u * t` lies in
`K = J(D,t)`: it is an element of `H ∩ H^t` inverted by `t`. -/
lemma mul_t_mem_Kset [Finite G] {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {t : G} (ht2 : orderOf t = 2) {u : G} (hu : u ∈ Work.ThmF.Bender.InvHt H t) :
    u * t ∈ Work.ThmF.Kset H t := by
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t; rw [ht2] at h; simpa [pow_two] using h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨hu2, huconj⟩ := hu
  set h : G := t⁻¹ * u with hh_def
  have hh : h ∈ H := inv_mem_of_conj_eq hH huconj
  have hu_sq : u * u = 1 := by
    have h := pow_orderOf_eq_one u; rw [hu2] at h; simpa [pow_two] using h
  have hu_eq : t * h = u := by rw [hh_def]; group
  have h2 : t * h * t * h = 1 := by
    have h := hu_sq
    rw [← hu_eq] at h
    simpa [mul_assoc] using h
  have hth : t * h * t = h⁻¹ := by
    have := congrArg (fun z => z * h⁻¹) h2
    simpa [mul_assoc] using this
  have h4 : t * h⁻¹ * t = h := by
    have := congrArg (fun z => z⁻¹) hth
    simpa [htinv, mul_assoc] using this
  have hut : u * t = h⁻¹ := by
    rw [← hu_eq, hth]
  have hconj_hinv : h⁻¹ ∈ Submission.Blueprint.conj t H := by
    rw [Work.Models.mem_conj_iff]
    have h3 : t⁻¹ * h⁻¹ * t = h := by simpa [htinv] using h4
    rw [h3]; exact hh
  refine Work.ThmF.mem_Kset_iff.mpr ⟨?_, ?_⟩
  · rw [Work.Models.mem_twoPoint_iff]
    refine ⟨?_, ?_⟩
    · rw [hut]; exact H.inv_mem hh
    · rw [← Work.Models.mem_conj_iff, hut]; exact hconj_hinv
  · rw [hut, htinv, h4, inv_inv]

open LeanEval.GroupTheory.Defs Submission.Blueprint in theorem ncard_Kset_eq_ncard_InvHt {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (ht2 : orderOf t = 2) (htH : t ∉ H) : (Work.ThmF.Kset H t).ncard = (Work.ThmF.Bender.InvHt H t).ncard := by
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t; rw [ht2] at h; simpa [pow_two] using h
  have hmaps : Set.MapsTo (fun x => x * t) (Work.ThmF.Kset H t)
      (Work.ThmF.Bender.InvHt H t) := by
    intro x hx; exact mul_t_mem_InvHt ht2 htH hx
  have hinj : Set.InjOn (fun x => x * t) (Work.ThmF.Kset H t) := by
    intro x _ y _ hxy; exact mul_right_cancel hxy
  have hsurj : Set.SurjOn (fun x => x * t) (Work.ThmF.Kset H t)
      (Work.ThmF.Bender.InvHt H t) := by
    intro u hu
    exact ⟨u * t, mul_t_mem_Kset hH ht2 hu, by
      show (u * t) * t = u
      rw [mul_assoc, htt, mul_one]⟩
  exact Set.BijOn.ncard_eq (f := fun x => x * t) ⟨hmaps, hinj, hsurj⟩

end Work.ThmF.Bender
