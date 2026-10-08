import Mathlib
import Submission.Work.ThmF.Bender.DTransInvAux
import Submission.Work.ThmF.Bender.cardInvGeTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I, Ch. I §2 Prop. 1 (c): `|Inv(Ht)| = |Inv(H)|`

Let `H` be strongly embedded in the finite group `G` and `t ∉ H` an involution.  Then the set
`InvHt H t` of involutions `u` with `H^u = H^t` (the involutions of the coset `Ht`) has exactly
as many elements as `H` has involutions.

This is Peterfalvi I, Ch. I §2 Prop. 1 (c), the case `H' = H^t ≠ H`:

* pick an involution `s ∈ H`; the map `u ↦ u * s * u⁻¹` is a bijection of the set of
  involutions outside `H` onto itself (Prop. 1 (a)), and it carries `Inv(Ht)` onto `Inv(H^t)`;
* conjugation by `t` identifies `Inv(H^t)` with `Inv(H)`.

Everything reduces to the uniqueness of the conjugating involution
(`Work.ThmF.Bender.existsUnique_conj_involution`, Prop. 1 (a)) and to the fact that an
involution lying in the odd-order subgroup `H ∩ H^t = twoPoint H t` does not exist.
-/

namespace Work.ThmF.Bender

set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint in theorem ncard_InvHt_eq_ncard_involutions {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (ht2 : orderOf t = 2) (htH : t ∉ H) : (Work.ThmF.Bender.InvHt H t).ncard = (Submission.Blueprint.involutions (H : Set G)).ncard := by
  classical
  -- an involution `s ∈ H`
  obtain ⟨s, hsH, hs2⟩ := exists_involution_mem_of_isStronglyEmbedded hH
  -- `D = H ∩ H^t` has odd order
  have hDodd : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) := hH.2.2 t htH
  -- an involution of `H^t` lies outside `H`
  have hOut' : ∀ {w : G}, w ∈ Submission.Blueprint.conj t H → orderOf w = 2 → w ∉ H := by
    intro w hw hw2 hwH
    have hwd : w ∈ Submission.Blueprint.twoPoint H t := ⟨hwH, hw⟩
    have hdvd : orderOf w ∣ Nat.card (Submission.Blueprint.twoPoint H t) :=
      Subgroup.orderOf_dvd_natCard _ hwd
    exact Nat.not_even_iff_odd.mpr hDodd (even_iff_two_dvd.mpr (hw2 ▸ hdvd))
  -- the image of `u ↦ u * s * u⁻¹` lies in `Inv(H^t)`
  have hmem : ∀ a ∈ InvHt H t, a * s * a⁻¹ ∈ Submission.Blueprint.involutions
      ((Submission.Blueprint.conj t H : Subgroup G) : Set G) := by
    intro a ha
    refine ⟨?_, ?_⟩
    · have h1 : a * s * a⁻¹ ∈ Submission.Blueprint.conj a H :=
        Work.Models.mem_conj_iff.mpr (by
          rw [show a⁻¹ * (a * s * a⁻¹) * a = s by group]
          exact hsH)
      rwa [ha.2] at h1
    · rw [orderOf_conj_eq, hs2]
  -- ... and the map is injective on `InvHt H t`
  have hinj : ∀ (a b : G), a ∈ InvHt H t → b ∈ InvHt H t →
      a * s * a⁻¹ = b * s * b⁻¹ → a = b := by
    intro a b ha hb hab
    have hw2 : orderOf (a * s * a⁻¹) = 2 := by rw [orderOf_conj_eq, hs2]
    have hwOut : a * s * a⁻¹ ∉ H := hOut' (hmem a ha).1 hw2
    obtain ⟨u, ⟨-, -⟩, huniq⟩ := existsUnique_conj_involution hH hsH hs2 hw2 hwOut
    have ha_eq : a = u := huniq a ⟨ha.1, rfl⟩
    have hb_eq : b = u := huniq b ⟨hb.1, hab.symm⟩
    rw [ha_eq, hb_eq]
  -- ... and surjective onto `Inv(H^t)`
  have hsurj : ∀ w ∈ Submission.Blueprint.involutions
      ((Submission.Blueprint.conj t H : Subgroup G) : Set G),
      ∃ a, ∃ _ : a ∈ InvHt H t, a * s * a⁻¹ = w := by
    intro w hw
    have hw2 : orderOf w = 2 := hw.2
    have hwOut : w ∉ H := hOut' hw.1 hw2
    obtain ⟨u, ⟨hu2, hueq⟩, -⟩ := existsUnique_conj_involution hH hsH hs2 hw2 hwOut
    refine ⟨u, ⟨hu2, ?_⟩, hueq⟩
    have hw_conj : w ∈ Submission.Blueprint.conj u H := by
      rw [Work.Models.mem_conj_iff, ← hueq]
      rw [show u⁻¹ * (u * s * u⁻¹) * u = s by group]
      exact hsH
    exact Work.ThmF.conj_eq_conj_of_mem hH hw2 hw_conj hw.1
  -- count via the bijection `u ↦ u * s * u⁻¹`
  have hcard1 : (InvHt H t).ncard = (Submission.Blueprint.involutions
      ((Submission.Blueprint.conj t H : Subgroup G) : Set G)).ncard :=
    Set.ncard_congr (fun a _ => a * s * a⁻¹) hmem hinj hsurj
  -- conjugation by `t` identifies `Inv(H^t)` with `Inv(H)`
  have hcard2 : (Submission.Blueprint.involutions
        ((Submission.Blueprint.conj t H : Subgroup G) : Set G)).ncard
      = (Submission.Blueprint.involutions (H : Set G)).ncard := by
    rw [Work.Models.involutions_conj t H]
    exact Set.ncard_image_of_injective _
      (fun x y hxy => mul_left_cancel (mul_right_cancel hxy))
  rw [hcard1, hcard2]

end Work.ThmF.Bender
