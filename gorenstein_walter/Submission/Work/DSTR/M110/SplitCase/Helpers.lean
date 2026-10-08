/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Helper lemmas for the split case of DS10a

* `oddPglImageMemPslImage`: an odd-order element of `pglImage F` lies in `pslImage F`;
* `dil_comm_negPerm`: the elements `dil a` commute with the split involution `x ↦ -x`;
* `galMap_conj_mem_pglImage`: conjugation by an element of `pglImage F` does not change
  the Galois part;
* `card_le_card_inf_ker`: an abstract counting bound: the elements of `N` mapping to a fixed
  value of a homomorphism are no more numerous than `N ∩ ker`.
-/
import Mathlib
import Submission.Work.DSTR.M110.SplitCase.SqTorus
import Submission.Work.DSTR.M110.Aut.pglIndex

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110.SplitAux

open Work.AUTL2

variable (F : Type*) [Field F] [DecidableEq F]

/-- An element of `pglImage F` of odd order lies in `pslImage F`
(the quotient `PGL(2,F)/PSL(2,F) ≅ Fˣ/(Fˣ)²` has exponent `2`). -/
theorem oddPglImageMemPslImage (p k : ℕ) [Fact p.Prime] [DecidableEq (GaloisField p k)]
    (x : Equiv.Perm (P1 (GaloisField p k))) (hx : x ∈ pglImage (GaloisField p k))
    (hodd : Odd (orderOf x)) : x ∈ pslImage (GaloisField p k) := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  set y : Equiv.Perm (P1 (GaloisField p k)) :=
    pglHom _ (Matrix.ProjGenLinGroup.mk A) with hy
  have hsq : y * y ∈ pslImage (GaloisField p k) := by
    have h1 : y * y = pglHom _ (Matrix.ProjGenLinGroup.mk (A * A)) := by
      rw [hy, ← map_mul, ← map_mul]
    rw [h1, Work.AUTL2.Aut.mem_pslImage_iff_isSquare_det]
    exact ⟨A.det, by rw [map_mul]⟩
  have hm : y ^ orderOf y = 1 := pow_orderOf_eq_one y
  obtain ⟨t, ht⟩ := hodd
  have h2 : 2 * ((orderOf y + 1) / 2) = orderOf y + 1 := by omega
  have hsplit : y = (y * y) ^ ((orderOf y + 1) / 2) := by
    calc y = y ^ (orderOf y + 1) := by rw [pow_succ, hm, one_mul]
      _ = y ^ (2 * ((orderOf y + 1) / 2)) := by rw [h2]
      _ = (y * y) ^ ((orderOf y + 1) / 2) := by rw [pow_mul, pow_two]
  rw [hsplit]
  exact Subgroup.pow_mem _ hsq _

/-- `negPerm F` is the diagonal element `smulHom F (-1)`. -/
lemma negPerm_eq_smulHom : negPerm F = smulHom F (-1) := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · rw [negPerm_infty, smulHom_apply_infty]
  · rw [negPerm_some, smulHom_apply_some, Units.val_neg, Units.val_one, neg_one_mul]

/-- The elements `dil a` commute with the split involution `x ↦ -x`. -/
lemma dil_comm_negPerm (a : Fˣ) :
    dilHom F a * negPerm F = negPerm F * dilHom F a := by
  rw [negPerm_eq_smulHom, dil_eq_smul, ← map_mul, ← map_mul, mul_comm]

/-- Conjugation by an element of `pglImage F` does not change the Galois part. -/
theorem galMap_conj_mem_pglImage (c : ↥(pgammaL F))
    (hc : (c : Equiv.Perm (P1 F)) ∈ pglImage F) (y : ↥(pgammaL F)) :
    galMap F (c * y * c⁻¹) = galMap F y := by
  have hc1 : galMap F c = 1 := galPart_of_mem F c hc
  have hci : galMap F c⁻¹ = 1 := by rw [map_inv, hc1, inv_one]
  rw [map_mul, map_mul, hc1, hci, one_mul, mul_one]

/-- **Abstract counting bound.**  If `S` is a set of elements of a subgroup `N` of `G` on which
a homomorphism `ψ` takes the constant value `σ`, and `y ∈ N` also has `ψ y = σ`, then
`|S| ≤ |N ∩ ker ψ|`. -/
theorem card_le_card_inf_ker {G H : Type*} [Group G] [Group H] [Finite G]
    (ψ : G →* H) (N : Subgroup G) (S : Set G) (hS : S ⊆ N) (y : G) (hy : y ∈ N) (σ : H)
    (hσ : ∀ z ∈ S, ψ z = σ) (hyσ : ψ y = σ) :
    Nat.card ↥S ≤ Nat.card ↥(N ⊓ ψ.ker) := by
  have hinj : Function.Injective (fun z : G => z * y⁻¹) := fun a b h =>
    mul_right_cancel h
  have hsub : (fun z : G => z * y⁻¹) '' S ⊆ ((N ⊓ ψ.ker : Subgroup G) : Set G) := by
    intro w hw
    obtain ⟨z, hz, hzw⟩ := hw
    have hzN : z ∈ N := hS hz
    have hker : z * y⁻¹ ∈ ψ.ker := by
      show ψ (z * y⁻¹) = 1
      rw [map_mul, map_inv, hσ z hz, hyσ, mul_inv_cancel]
    rw [← hzw]
    exact ⟨N.mul_mem hzN (N.inv_mem hy), hker⟩
  calc Nat.card ↥S = Nat.card ↥((fun z : G => z * y⁻¹) '' S) :=
        (Nat.card_image_of_injective hinj S).symm
    _ ≤ Nat.card ↥((N ⊓ ψ.ker : Subgroup G) : Set G) := by
        rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
        exact Set.ncard_mono hsub

/-- An element `z` with `weylEl * z` diagonal has order dividing `2`. -/
lemma sq_eq_one_of_weylEl_mul_mem_torSub (z : Equiv.Perm (P1 F))
    (hz : weylEl F * z ∈ torSub F) : z * z = 1 := by
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hz
  have hz' : z = weylEl F * smulHom F a := by rw [ha, ← mul_assoc, weyl_self, one_mul]
  rw [hz']
  calc (weylEl F * smulHom F a) * (weylEl F * smulHom F a)
      = (weylEl F * smulHom F a * weylEl F) * smulHom F a := by group
    _ = smulHom F a⁻¹ * smulHom F a := by rw [weylEl_conj_smulHom]
    _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]

/-- An element of `pglImage F` of odd order centralizing `x ↦ -x` is diagonal. -/
lemma mem_torSub_of_odd_order (h2 : (2 : F) ≠ 0) {z : Equiv.Perm (P1 F)} (hz : z ∈ pglImage F)
    (hcomm : z * negPerm F = negPerm F * z) (hodd : Odd (orderOf z)) : z ∈ torSub F := by
  rcases pglImage_centralizer_negPerm F h2 z hz hcomm with h | h
  · exact h
  · have hsq : z * z = 1 := sq_eq_one_of_weylEl_mul_mem_torSub F z h
    have hdvd : orderOf z ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hsq
    have hone : orderOf z = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact h1
      · rw [h1] at hodd; exact absurd hodd (by decide)
    have hz1 : z = 1 := orderOf_eq_one_iff.mp hone
    rw [hz1]; exact Subgroup.one_mem _


end Work.DSTR.M110.SplitAux
