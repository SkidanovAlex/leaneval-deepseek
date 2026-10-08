import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.GLUE.Defs
import Submission.Work.BG.hyp12OfBGData

/-!
# Area BG: the small case `|S| = 4` of Bender–Glauberman Theorem C

For `D : Work.GW2.BGData G` with `D.n = 2` the Sylow `2`-subgroup `S` has order `2n = 4`, so
`S` is a Klein four group: `S ≅* DihedralGroup 2` is commutative.  Consequently

* `|S₀| = 2`, so `S₀ = ⟨t⟩ = ⟨t₁t₂⟩` and `t = t₁t₂`, `t₁t₂ = t₂t₁`;
* `U ≤ C_G(t)` and `t` is `t₁t₂`, hence `B₁ = U ∩ C_G(t₁) = U ∩ C_G(t₂) = B₂`;
* `S` is commutative, hence `S ≤ C_G(t₁)` and `S ≤ C_G(t₂)`.

These are the hypotheses of `Work.GW2.C16.ThmCSmallShapeProp` (used in
`Submission/Work/BG/thmCSmallShape.lean`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem thmCSmallAux {G : Type} [Group G] [Finite G] (D : BGData G) (hn : D.n = 2) :
    D.t = D.t1 * D.t2 ∧ D.t1 * D.t2 = D.t2 * D.t1 ∧ D.B1 = D.B2 ∧
    (D.S : Subgroup G) ≤ Subgroup.centralizer ({D.t1} : Set G) ∧
    (D.S : Subgroup G) ≤ Subgroup.centralizer ({D.t2} : Set G) := by
  -- `S ≅* DihedralGroup D.n`, so `|S| = 2n = 4`.
  obtain ⟨e⟩ := D.dih
  have hcardS : Nat.card ↥(D.S : Subgroup G) = 4 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hn]
  have ht1sq : D.t1 ^ 2 = 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t1_order).1
  have ht2sq : D.t2 ^ 2 = 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t2_order).1
  have ht_sq : D.t ^ 2 = 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t_order).1
  have ht_ne1 : D.t ≠ 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t_order).2
  -- `[S : S₀] = 2` and `|S| = 4`, so `|S₀| = 2`.
  have hcardS0 : Nat.card ↥D.S0 = 2 := by
    have h := Subgroup.relIndex_mul_card D.S0 (D.S : Subgroup G)
    rw [inf_eq_left.mpr D.S0_le, D.S0_index, hcardS] at h
    omega
  -- `S₀ = ⟨t₁t₂⟩` has order two, so `t₁t₂` is an involution.
  have horder : orderOf (D.t1 * D.t2) = 2 := by
    have h : Nat.card ↥(Subgroup.zpowers (D.t1 * D.t2)) = 2 := by
      rw [← D.gen]; exact hcardS0
    rwa [Nat.card_zpowers] at h
  have hsq : (D.t1 * D.t2) ^ 2 = 1 := ((orderOf_eq_prime_iff (p := 2)).mp horder).1
  have h12ne1 : D.t1 * D.t2 ≠ 1 := ((orderOf_eq_prime_iff (p := 2)).mp horder).2
  -- `t` is the unique involution of `S₀ = ⟨t₁t₂⟩`.
  have ht_eq : D.t = D.t1 * D.t2 :=
    eqOfMemZpowersOfSqEqOne (y := D.t1 * D.t2) (z := D.t) (w := D.t1 * D.t2)
      (by rw [← D.gen]; exact D.t_mem) (Subgroup.mem_zpowers _) ht_sq hsq ht_ne1 h12ne1
  have hinv1 : D.t1⁻¹ = D.t1 := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at ht1sq)
  have hinv2 : D.t2⁻¹ = D.t2 := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at ht2sq)
  -- `(t₁t₂)² = 1` gives `t₁t₂ = t₂t₁`.
  have hcomm : D.t1 * D.t2 = D.t2 * D.t1 := by
    have h1 : (D.t1 * D.t2)⁻¹ = D.t1 * D.t2 :=
      inv_eq_of_mul_eq_one_right (by rwa [pow_two] at hsq)
    calc D.t1 * D.t2 = (D.t1 * D.t2)⁻¹ := h1.symm
      _ = D.t2⁻¹ * D.t1⁻¹ := mul_inv_rev _ _
      _ = D.t2 * D.t1 := by rw [hinv1, hinv2]
  have ht1_mul : D.t1 * D.t1 = 1 := by rwa [pow_two] at ht1sq
  have ht2_mul : D.t2 * D.t2 = 1 := by rwa [pow_two] at ht2sq
  -- `t₂ = t₁ t` and `t₁ = t₂ t`, since `t = t₁t₂` and `tᵢ² = 1`.
  have ht2_eq : D.t2 = D.t1 * D.t := by
    have h : D.t1 * D.t = D.t2 := by rw [ht_eq, ← mul_assoc, ht1_mul, one_mul]
    exact h.symm
  have ht1_eq : D.t1 = D.t2 * D.t := by
    have h : D.t2 * D.t = D.t1 := by
      rw [ht_eq, hcomm, ← mul_assoc, ht2_mul, one_mul]
    exact h.symm
  -- `U ≤ C_G(t)`, so on `U` the centralizers of `t₁` and of `t₂ = t₁t` agree.
  have hU_le_H : D.U ≤ D.H := Subgroup.map_subtype_le _
  have key : ∀ x ∈ D.U, (x * D.t1 = D.t1 * x ↔ x * D.t2 = D.t2 * x) := by
    intro x hx
    have hxt : x * D.t = D.t * x := by
      have hxH : x ∈ D.H := hU_le_H hx
      exact ((Subgroup.mem_centralizer_iff.mp hxH) D.t (Set.mem_singleton D.t)).symm
    constructor
    · intro h1
      calc x * D.t2 = x * (D.t1 * D.t) := by rw [ht2_eq]
        _ = (x * D.t1) * D.t := by rw [mul_assoc]
        _ = (D.t1 * x) * D.t := by rw [h1]
        _ = D.t1 * (x * D.t) := by rw [mul_assoc]
        _ = D.t1 * (D.t * x) := by rw [hxt]
        _ = (D.t1 * D.t) * x := by rw [mul_assoc]
        _ = D.t2 * x := by rw [ht2_eq]
    · intro h2
      calc x * D.t1 = x * (D.t2 * D.t) := by rw [ht1_eq]
        _ = (x * D.t2) * D.t := by rw [mul_assoc]
        _ = (D.t2 * x) * D.t := by rw [h2]
        _ = D.t2 * (x * D.t) := by rw [mul_assoc]
        _ = D.t2 * (D.t * x) := by rw [hxt]
        _ = (D.t2 * D.t) * x := by rw [mul_assoc]
        _ = D.t1 * x := by rw [ht1_eq]
  have hB : D.B1 = D.B2 := by
    show D.U ⊓ Subgroup.centralizer ({D.t1} : Set G) =
      D.U ⊓ Subgroup.centralizer ({D.t2} : Set G)
    apply le_antisymm
    · intro x hx
      obtain ⟨hxU, hx1⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hxU, Subgroup.mem_centralizer_singleton_iff.mpr
        ((key x hxU).mp (Subgroup.mem_centralizer_singleton_iff.mp hx1))⟩
    · intro x hx
      obtain ⟨hxU, hx2⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hxU, Subgroup.mem_centralizer_singleton_iff.mpr
        ((key x hxU).mpr (Subgroup.mem_centralizer_singleton_iff.mp hx2))⟩
  -- `S` is a Klein four group, hence commutative.
  have hcommd : IsMulCommutative (DihedralGroup D.n) :=
    DihedralGroup.commutative_iff.mpr (Or.inr hn)
  have hScomm : ∀ x ∈ (D.S : Subgroup G), ∀ y ∈ (D.S : Subgroup G), x * y = y * x := by
    intro x hx y hy
    have hkey : e (⟨x, hx⟩ * ⟨y, hy⟩) = e (⟨y, hy⟩ * ⟨x, hx⟩) := by
      rw [map_mul, map_mul]
      exact hcommd.is_comm.comm _ _
    exact Subtype.ext_iff.mp (e.injective hkey)
  refine ⟨ht_eq, hcomm, hB, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hScomm x hx D.t1 D.t1_mem
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hScomm x hx D.t2 D.t2_mem

end Work.BG
