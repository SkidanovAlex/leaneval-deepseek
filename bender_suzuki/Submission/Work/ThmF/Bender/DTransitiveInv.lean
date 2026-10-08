import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmF.Bender.DTransInvAux
import Submission.Work.ThmF.Bender.ncard_Kset_eq_ncard_InvHt
import Submission.Work.ThmF.Bender.ncard_InvHt_eq_ncard_involutions

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I, Ch. I §2 Prop. 2 (b): `D` acts transitively on `Inv(H)`

Let `H` be strongly embedded in the finite group `G` and `t ∉ H` an involution, put
`D = H ∩ H^t`.  Then the two-point stabiliser `D` acts by conjugation transitively on the set
`Inv(H)` of involutions of `H`:

* an involution of `H` lies in no conjugate of `H` but `H`
  (`Work.ThmF.conj_eq_self_of_involution_mem`), so `D` (and indeed the map `x ↦ x * t`) carries
  `K = J(D,t)` bijectively onto the involutions of the coset `Ht`, and the map
  `x ↦ x * a * x⁻¹` (`a ∈ Inv(H)`) is injective on `K` (Peterfalvi's Lemma 1);
* the involutions of `H` and those of `Ht` have the same number `n` of elements (Prop. 1 (c)).

Since the orbit of `a ∈ Inv(H)` under `D` is contained in the finite set `Inv(H)` and has at
least `n = |Inv(H)|` elements, it *is* `Inv(H)`.

Source: Peterfalvi, *Le théorème de Bender–Suzuki I*, Ch. I §2 Prop. 2 (b) (p. 152), with
Ch. I §1 (2) and §2 Prop. 1 (a), (c).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.Bender

open LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type*} [Group G] [Finite G]

/-- Peterfalvi I, Ch. I §2, Lemma 1: for an involution `a ∈ H`, the map `x ↦ x * a * x⁻¹` is
injective on `K = J(D,t) ⊆ D`.  Equivalently, `|a^D| ≥ |K|`. -/
theorem Kset_conj_injective {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht2 : orderOf t = 2) (htH : t ∉ H) {a : G} (ha : a ∈ H) (ha2 : orderOf a = 2) :
    Set.InjOn (fun x => x * a * x⁻¹) (Kset H t) := by
  intro x hx y hy hxy
  obtain ⟨hxD, hxinv⟩ := Work.ThmF.mem_Kset_iff.mp hx
  obtain ⟨hyD, hyinv⟩ := Work.ThmF.mem_Kset_iff.mp hy
  have hxH : x ∈ H := (Work.Models.mem_twoPoint_iff.mp hxD).1
  have hyH : y ∈ H := (Work.Models.mem_twoPoint_iff.mp hyD).1
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t; rw [ht2] at h; simpa [pow_two] using h
  have htt' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  -- `x * t` and `y * t` are involutions
  have hxt2 : orderOf (x * t) = 2 := by
    have hsq : (x * t) * (x * t) = 1 := by
      have htx : t * x * t = x⁻¹ := by simpa only [htt'] using hxinv
      calc (x * t) * (x * t) = x * (t * x * t) := by group
        _ = x * x⁻¹ := by rw [htx]
        _ = 1 := mul_inv_cancel x
    apply orderOf_eq_prime
    · rwa [pow_two]
    · intro h1
      have : x = t⁻¹ := by
        have h2 := congrArg (fun z => z * t⁻¹) h1
        simpa [mul_assoc] using h2
      exact htH (htt'.symm ▸ this ▸ hxH)
  have hyt2 : orderOf (y * t) = 2 := by
    have hsq : (y * t) * (y * t) = 1 := by
      have hty : t * y * t = y⁻¹ := by simpa only [htt'] using hyinv
      calc (y * t) * (y * t) = y * (t * y * t) := by group
        _ = y * y⁻¹ := by rw [hty]
        _ = 1 := mul_inv_cancel y
    apply orderOf_eq_prime
    · rwa [pow_two]
    · intro h1
      have : y = t⁻¹ := by
        have h2 := congrArg (fun z => z * t⁻¹) h1
        simpa [mul_assoc] using h2
      exact htH (htt'.symm ▸ this ▸ hyH)
  -- the involution `v = t * a * t⁻¹ ∈ H^t`
  have hv2 : orderOf (t * a * t⁻¹) = 2 := by rw [orderOf_conj_eq, ha2]
  have hv : t * a * t⁻¹ ∈ Submission.Blueprint.conj t H := by
    rw [Work.Models.mem_conj_iff]
    have h : t⁻¹ * (t * a * t⁻¹) * t = a := by
      rw [htt']
      calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
        _ = a := by rw [htt, one_mul, mul_one]
    rw [h]; exact ha
  -- both `x * t` and `y * t` conjugate `v` to `x * a * x⁻¹ = y * a * y⁻¹`
  have hξv : (x * t) * (t * a * t⁻¹) * (x * t)⁻¹ = x * a * x⁻¹ := by
    have h1 : (x * t)⁻¹ = t * x⁻¹ := by rw [mul_inv_rev, htt']
    rw [h1]
    calc (x * t) * (t * a * t⁻¹) * (t * x⁻¹)
        = x * (t * t) * a * (t⁻¹ * t) * x⁻¹ := by group
      _ = x * a * x⁻¹ := by simp [htt]
  have hηv : (y * t) * (t * a * t⁻¹) * (y * t)⁻¹ = x * a * x⁻¹ := by
    have h1 : (y * t)⁻¹ = t * y⁻¹ := by rw [mul_inv_rev, htt']
    rw [h1]
    have h : y * a * y⁻¹ = x * a * x⁻¹ := hxy.symm
    calc (y * t) * (t * a * t⁻¹) * (t * y⁻¹)
        = y * (t * t) * a * (t⁻¹ * t) * y⁻¹ := by group
      _ = y * a * y⁻¹ := by simp [htt]
      _ = x * a * x⁻¹ := h
  -- `x * a * x⁻¹` is an involution outside `H^t`
  have hw2 : orderOf (x * a * x⁻¹) = 2 := by rw [orderOf_conj_eq, ha2]
  have hw_notin : x * a * x⁻¹ ∉ Submission.Blueprint.conj t H := by
    intro hmem
    have hwH : x * a * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hxH ha) (H.inv_mem hxH)
    have h := Work.ThmF.conj_eq_self_of_involution_mem hH hwH hw2 hmem
    exact htH ((Work.ThmF.conj_eq_iff_mem hH t).mp h)
  have hH' : IsStronglyEmbedded (Submission.Blueprint.conj t H) :=
    Work.Models.IsStronglyEmbedded.conj hH t
  obtain ⟨u, ⟨hu2, huv⟩, huniq⟩ :=
    existsUnique_conj_involution hH' hv hv2 hw2 hw_notin
  have hξ : x * t = u := huniq (x * t) ⟨hxt2, hξv⟩
  have hη : y * t = u := huniq (y * t) ⟨hyt2, hηv⟩
  exact mul_right_cancel (hξ.trans hη.symm)

open LeanEval.GroupTheory.Defs Submission.Blueprint in theorem DTransitiveInv {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (ht2 : orderOf t = 2) (htH : t ∉ H) : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G), ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b := by
  intro a ha b hb
  -- the involutions of `H` and of the coset `Ht` have the same number of elements
  have hcard : (Kset H t).ncard = (involutions (H : Set G)).ncard := by
    rw [ncard_Kset_eq_ncard_InvHt hH ht2 htH, ncard_InvHt_eq_ncard_involutions hH ht2 htH]
  have hmaps : ∀ x ∈ Kset H t, x * a * x⁻¹ ∈ involutions (H : Set G) := by
    intro x hx
    have hxH : x ∈ H := (Work.Models.mem_twoPoint_iff.mp (Work.ThmF.Kset_subset H t hx)).1
    exact ⟨H.mul_mem (H.mul_mem hxH ha.1) (H.inv_mem hxH),
      by rw [orderOf_conj_eq, ha.2]⟩
  have hinj : Set.InjOn (fun x => x * a * x⁻¹) (Kset H t) :=
    Kset_conj_injective hH ht2 htH ha.1 ha.2
  have himg : ((fun x => x * a * x⁻¹) '' (Kset H t)).ncard
      = (involutions (H : Set G)).ncard := by
    rw [Set.InjOn.ncard_image hinj, hcard]
  have hsub : (fun x => x * a * x⁻¹) '' (Kset H t) ⊆ involutions (H : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps x hx
  have heq := Set.eq_of_subset_of_ncard_le hsub (le_of_eq himg.symm)
  have hb' : b ∈ (fun x => x * a * x⁻¹) '' (Kset H t) := by rw [heq]; exact hb
  obtain ⟨d, hd, hdb⟩ := hb'
  exact ⟨d, Work.ThmF.Kset_subset H t hd, hdb⟩

end Work.ThmF.Bender
