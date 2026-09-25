/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Commutation of the orbit counts of the two `Subgroup`s of a double coset space

For subgroups `D H` of a group `G`, the number of orbits of `D` on the left coset space `G ⧸ H`
equals the number of orbits of `H` on the left coset space `G ⧸ D`.  Both numbers are the number of
double cosets `D \ G / H`, and the bijection is induced by inversion `g ↦ g⁻¹`, which exchanges the
two sides of a double coset.

This is the combinatorial input of the Perlis/Gassmann counting of the primes of a subfield by the
orbits of a Frobenius (`NK.WeakNU.PrimeCountOrbitInput`): the double coset space that occurs there
is invariant under exchanging the decomposition subgroup and the fixing subgroup.
-/
import Mathlib
import Submission.NK.WeakNU.Defs

namespace NK.WeakNU

/-- **The `D`-orbit relation on `G ⧸ H` is the double coset relation.**  Two left cosets of `H`
are in the same `D`-orbit if and only if their representatives differ by an element of `D` on the
left and an element of `H` on the right. -/
lemma orbitRel_iff_exists {G : Type*} [Group G] (D H : Subgroup G) (x y : G) :
    MulAction.orbitRel D (G ⧸ H) (x : G ⧸ H) (y : G ⧸ H) ↔ ∃ d ∈ D, ∃ h ∈ H, y = d * x * h := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨d, hd⟩
    have hd' : (((d : G) * y : G) : G ⧸ H) = (x : G ⧸ H) := hd
    rw [QuotientGroup.eq] at hd'
    refine ⟨(d : G)⁻¹, D.inv_mem d.2, (((d : G) * y)⁻¹ * x)⁻¹, H.inv_mem hd', ?_⟩
    group
  · rintro ⟨d, hd, h, hh, rfl⟩
    refine ⟨⟨d⁻¹, D.inv_mem hd⟩, ?_⟩
    change (((d⁻¹ : G) * (d * x * h) : G) : G ⧸ H) = (x : G ⧸ H)
    rw [show ((d⁻¹ : G) * (d * x * h)) = x * h by group, QuotientGroup.mk_mul_of_mem x hh]

/-- **The orbits of `D` on `G ⧸ H` are the double cosets `D \ G / H`.** -/
noncomputable def orbitQuotientEquivDoubleCoset {G : Type*} [Group G] (D H : Subgroup G) :
    MulAction.orbitRel.Quotient D (G ⧸ H) ≃ DoubleCoset.Quotient (D : Set G) (H : Set G) where
  toFun := Quotient.lift (fun x : G ⧸ H => DoubleCoset.mk D H (Quotient.out x)) (by
    intro x y hxy
    have hxy' : MulAction.orbitRel D (G ⧸ H) ((Quotient.out x : G) : G ⧸ H)
        ((Quotient.out y : G) : G ⧸ H) := by
      rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y] at hxy
      exact hxy
    obtain ⟨d, hd, h, hh, hyd⟩ := (orbitRel_iff_exists D H (Quotient.out x) (Quotient.out y)).mp hxy'
    exact DoubleCoset.eq.mpr ⟨d, hd, h, hh, hyd⟩)
  invFun := Quotient.lift
    (fun g : G => (Quotient.mk'' (g : G ⧸ H) : MulAction.orbitRel.Quotient D (G ⧸ H))) (by
    intro a b hab
    obtain ⟨d, hd, h, hh, hba⟩ := DoubleCoset.rel_iff.mp hab
    exact Quotient.sound' ((orbitRel_iff_exists D H a b).mpr ⟨d, hd, h, hh, hba⟩))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn' with
    | _ x =>
      simp only [Quotient.lift_mk]
      exact Quotient.sound' (by rw [QuotientGroup.out_eq' x])
  right_inv := by
    intro q
    induction q using Quotient.inductionOn' with
    | _ g =>
      simp only [Quotient.lift_mk]
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
      exact (DoubleCoset.eq.mpr
        ⟨1, D.one_mem, h, h.2, by rw [hh, one_mul]⟩).symm

/-- **The double coset space is unchanged when the two subgroups are exchanged**: inversion sends
`D \ G / H` to `H \ G / D`. -/
noncomputable def doubleCosetCommEquiv {G : Type*} [Group G] (D H : Subgroup G) :
    DoubleCoset.Quotient (D : Set G) (H : Set G) ≃ DoubleCoset.Quotient (H : Set G) (D : Set G) where
  toFun := Quotient.lift (fun g : G => DoubleCoset.mk H D g⁻¹) (by
    intro a b hab
    obtain ⟨d, hd, h, hh, hba⟩ := DoubleCoset.rel_iff.mp hab
    refine DoubleCoset.eq.mpr ⟨h⁻¹, H.inv_mem hh, d⁻¹, D.inv_mem hd, ?_⟩
    rw [hba]
    group)
  invFun := Quotient.lift (fun g : G => DoubleCoset.mk D H g⁻¹) (by
    intro a b hab
    obtain ⟨h, hh, d, hd, hba⟩ := DoubleCoset.rel_iff.mp hab
    refine DoubleCoset.eq.mpr ⟨d⁻¹, D.inv_mem hd, h⁻¹, H.inv_mem hh, ?_⟩
    rw [hba]
    group)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn' with
    | _ g => simp only [Quotient.lift_mk, inv_inv]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn' with
    | _ g => simp only [Quotient.lift_mk, inv_inv]

theorem card_orbits_coset_comm {G : Type*} [Group G] [Fintype G] (H D : Subgroup G) : Nat.card (MulAction.orbitRel.Quotient D (G ⧸ H)) = Nat.card (MulAction.orbitRel.Quotient H (G ⧸ D)) := by
  calc Nat.card (MulAction.orbitRel.Quotient D (G ⧸ H))
      = Nat.card (DoubleCoset.Quotient (D : Set G) (H : Set G)) :=
        Nat.card_congr (orbitQuotientEquivDoubleCoset D H)
    _ = Nat.card (DoubleCoset.Quotient (H : Set G) (D : Set G)) :=
        Nat.card_congr (doubleCosetCommEquiv D H)
    _ = Nat.card (MulAction.orbitRel.Quotient H (G ⧸ D)) :=
        (Nat.card_congr (orbitQuotientEquivDoubleCoset H D)).symm

end NK.WeakNU
