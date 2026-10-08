/-
# `Work.ThreePoints.TwoPointTransitive` — Ch. I §2 Prop. 2(b): `D` acts transitively on `Inv(H)`

Peterfalvi I, Ch. I §2 Prop. 2 (b) (p. 152): with `H` strongly embedded in the finite group `G`,
`t ∉ H` an involution and `D = H ∩ H^t`, the two-point stabiliser `D` acts by conjugation
transitively on the set `Inv(H)` of involutions of `H`:

`∀ u v ∈ Inv(H), ∃ d ∈ twoPoint H t, d * u * d⁻¹ = v`

(`BenderPrelimProp` of area `NormalComplement`) and `|K| = |Inv H|` for
`K = J(D,t) = invertedBy (twoPoint H t) t` (`Work.ThmF.Bender.cardKsetEqInv`).

Proof (the source's): the map `x ↦ x u x⁻¹` is injective on `K` (Peterfalvi's Lemma 1,
`invertedBy_conj_injective` below; the source's own proof is reproduced) and its image lies in
`Inv(H)`; since `|K| = |Inv(H)|`, the image *is* `Inv(H)`, so `u` is conjugate to `v` by an
element of `K ⊆ D`.
-/
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThmF.Bender.DTransInvAux
import Submission.Work.ThmF.Bender.cardKsetEqInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G]

/-- **Peterfalvi I Ch. I §2 Lemma 1.**  For an involution `a ∈ H`, the map `x ↦ x a x⁻¹` is
injective on `K = J(D,t)`, i.e. `|a^D| ≥ |K|`. -/
theorem invertedBy_conj_injective [Finite G] {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H) {a : G} (ha : a ∈ H)
    (ha2 : orderOf a = 2) :
    Set.InjOn (fun x => x * a * x⁻¹) (invertedBy (twoPoint H t) t) := by
  intro x hx y hy hxy
  obtain ⟨hxD, hxinv⟩ := hx
  obtain ⟨hyD, hyinv⟩ := hy
  have hxH : x ∈ H := (Subgroup.mem_inf.mp hxD).1
  have hyH : y ∈ H := (Subgroup.mem_inf.mp hyD).1
  have htt : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have htt' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htx : t * x * t = x⁻¹ := by simpa only [htt'] using hxinv
  have hty : t * y * t = y⁻¹ := by simpa only [htt'] using hyinv
  have hxt2 : orderOf (x * t) = 2 := by
    refine orderOf_eq_two_of ?_ ?_
    · intro h1
      have h2 : x = t := by
        have h3 := congrArg (fun z => z * t) h1
        simpa [mul_assoc, htt] using h3
      exact htH (h2 ▸ hxH)
    · calc (x * t) * (x * t) = x * (t * x * t) := by group
        _ = x * x⁻¹ := by rw [htx]
        _ = 1 := mul_inv_cancel x
  have hyt2 : orderOf (y * t) = 2 := by
    refine orderOf_eq_two_of ?_ ?_
    · intro h1
      have h2 : y = t := by
        have h3 := congrArg (fun z => z * t) h1
        simpa [mul_assoc, htt] using h3
      exact htH (h2 ▸ hyH)
    · calc (y * t) * (y * t) = y * (t * y * t) := by group
        _ = y * y⁻¹ := by rw [hty]
        _ = 1 := mul_inv_cancel y
  have hv2 : orderOf (t * a * t⁻¹) = 2 := by
    rw [Work.ThmF.Bender.orderOf_conj_eq, ha2]
  have hv : t * a * t⁻¹ ∈ conj t H := by
    rw [mem_conj_iff]
    have h : t⁻¹ * (t * a * t⁻¹) * t = a := by
      rw [htt']
      calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
        _ = a := by rw [htt, one_mul, mul_one]
    rw [h]; exact ha
  have hξv : (x * t) * (t * a * t⁻¹) * (x * t)⁻¹ = x * a * x⁻¹ := by
    have h1 : (x * t)⁻¹ = t * x⁻¹ := by rw [mul_inv_rev, htt']
    rw [h1]
    calc (x * t) * (t * a * t⁻¹) * (t * x⁻¹)
        = x * (t * t) * a * (t⁻¹ * t) * x⁻¹ := by group
      _ = x * a * x⁻¹ := by rw [htt]; group
  have hηv : (y * t) * (t * a * t⁻¹) * (y * t)⁻¹ = x * a * x⁻¹ := by
    have h1 : (y * t)⁻¹ = t * y⁻¹ := by rw [mul_inv_rev, htt']
    rw [h1]
    calc (y * t) * (t * a * t⁻¹) * (t * y⁻¹)
        = y * (t * t) * a * (t⁻¹ * t) * y⁻¹ := by group
      _ = y * a * y⁻¹ := by rw [htt]; group
      _ = x * a * x⁻¹ := hxy.symm
  have hw2 : orderOf (x * a * x⁻¹) = 2 := by
    rw [Work.ThmF.Bender.orderOf_conj_eq, ha2]
  have hwH : x * a * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hxH ha) (H.inv_mem hxH)
  have hw_notin : x * a * x⁻¹ ∉ conj t H := by
    intro hmem
    have hconj := Work.ThmF.conj_eq_self_of_involution_mem hH hwH hw2 hmem
    exact htH ((Work.ThmF.conj_eq_iff_mem hH t).mp hconj)
  have hH' : IsStronglyEmbedded (conj t H) := conj_stronglyEmbedded hH t
  obtain ⟨u, ⟨-, huv⟩, huniq⟩ :=
    Work.ThmF.Bender.existsUnique_conj_involution hH' hv hv2 hw2 hw_notin
  have hξ : x * t = u := huniq (x * t) ⟨hxt2, hξv⟩
  have hη : y * t = u := huniq (y * t) ⟨hyt2, hηv⟩
  exact mul_right_cancel (hξ.trans hη.symm)

/-- **Peterfalvi I Ch. I §2 Prop. 2 (b).**  The two-point stabiliser `D = H ⊓ H^t` acts
transitively by conjugation on the involutions of `H`. -/
theorem twoPoint_transitive_on_involutions [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) (htH : t ∉ H) {u v : G}
    (hu : u ∈ involutions (H : Set G)) (hv : v ∈ involutions (H : Set G)) :
    ∃ d ∈ twoPoint H t, d * u * d⁻¹ = v := by
  have hK : (invertedBy (twoPoint H t) t).ncard = (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv hH ht htH
  have hmaps : ∀ x ∈ invertedBy (twoPoint H t) t, x * u * x⁻¹ ∈ involutions (H : Set G) := by
    intro x hx
    have hxH : x ∈ H := (Subgroup.mem_inf.mp hx.1).1
    exact ⟨H.mul_mem (H.mul_mem hxH hu.1) (H.inv_mem hxH),
      by rw [Work.ThmF.Bender.orderOf_conj_eq, hu.2]⟩
  have hinj : Set.InjOn (fun x => x * u * x⁻¹) (invertedBy (twoPoint H t) t) :=
    invertedBy_conj_injective hH ht htH hu.1 hu.2
  have himg : ((fun x => x * u * x⁻¹) '' (invertedBy (twoPoint H t) t)).ncard =
      (involutions (H : Set G)).ncard := by
    rw [Set.InjOn.ncard_image hinj, hK]
  have hsub : (fun x => x * u * x⁻¹) '' (invertedBy (twoPoint H t) t) ⊆
      involutions (H : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps x hx
  have heq := Set.eq_of_subset_of_ncard_le hsub (le_of_eq himg.symm)
  have hv' : v ∈ (fun x => x * u * x⁻¹) '' (invertedBy (twoPoint H t) t) := by
    rw [heq]; exact hv
  obtain ⟨d, hd, hdb⟩ := hv'
  exact ⟨d, hd.1, hdb⟩

end Work.ThreePoints
