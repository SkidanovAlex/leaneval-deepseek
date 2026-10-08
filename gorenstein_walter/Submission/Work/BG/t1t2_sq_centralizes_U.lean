import Mathlib
import Submission.Work.BG.ThmABCDefs

namespace Work.BG

/-! ## Auxiliary conjugation lemmas

`MulAut.conj y` is the conjugation by `y`.  If conjugation by `y` either fixes `x` or
inverts `x`, then conjugation by `y² = y * y` fixes `x`. -/

private lemma conj_sq_of_conj_eq_self {G : Type} [Group G] {y x : G} (h : y * x * y⁻¹ = x) :
    y ^ 2 * x * (y ^ 2)⁻¹ = x := by
  have h1 : MulAut.conj y ^ 2 = MulAut.conj (y ^ 2) := (map_pow MulAut.conj y 2).symm
  have h2 : (MulAut.conj y) x = x := by rw [MulAut.conj_apply]; exact h
  have h3 : MulAut.conj (y ^ 2) x = x := by
    rw [← h1, pow_two, MulAut.mul_apply]
    simp only [h2]
  rwa [MulAut.conj_apply] at h3

private lemma conj_sq_of_conj_eq_inv {G : Type} [Group G] {y x : G} (h : y * x * y⁻¹ = x⁻¹) :
    y ^ 2 * x * (y ^ 2)⁻¹ = x := by
  have h1 : MulAut.conj y ^ 2 = MulAut.conj (y ^ 2) := (map_pow MulAut.conj y 2).symm
  have h2 : (MulAut.conj y) x = x⁻¹ := by rw [MulAut.conj_apply]; exact h
  have h3 : MulAut.conj (y ^ 2) x = x := by
    rw [← h1, pow_two, MulAut.mul_apply, h2, map_inv, h2, inv_inv]
  rwa [MulAut.conj_apply] at h3

/-- `g * x * g⁻¹ = x` is the same as `x` commuting with `g`. -/
private lemma mul_comm_of_conj_eq_self {G : Type} [Group G] {g x : G} (h : g * x * g⁻¹ = x) :
    x * g = g * x :=
  (mul_inv_eq_iff_eq_mul.mp h).symm

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16 in
/-- `t₁t₂` acts by inversion on `B₁ ∩ K₂` and trivially on `B (K₁ ∩ K₂)`, so its square
centralizes the direct product `U = (B₁ ∩ K₂)(B (K₁ ∩ K₂))`. -/
theorem t1t2_sq_centralizes_U {G : Type} [Group G] [Finite G] (D : BGData G)
    (K1 K2 : Subgroup G)
    (h1 : IsMaxInverted D.H D.t1 K1) (h2 : IsMaxInverted D.H D.t2 K2)
    (hd : IsInternalDirect D.U (D.B1 ⊓ K2) (D.B ⊔ (K1 ⊓ K2))) :
    (D.t1 * D.t2) ^ 2 ∈ Subgroup.centralizer ((D.U : Subgroup G) : Set G) := by
  -- `t₁t₂` inverts every element of `B₁ ∩ K₂`
  have hA : (D.t1 * D.t2) ^ 2 ∈
      Subgroup.centralizer (((D.B1 ⊓ K2 : Subgroup G)) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    simp only [Subgroup.mem_inf, SetLike.mem_coe] at ha
    obtain ⟨⟨-, haC1⟩, haK2⟩ := ha
    have ht1a : MulAut.conj D.t1 a = a := by
      rw [MulAut.conj_apply]
      exact (mul_inv_eq_iff_eq_mul).mpr
        ((Subgroup.mem_centralizer_iff.mp haC1) D.t1 (Set.mem_singleton D.t1))
    have ht2a : MulAut.conj D.t2 a = a⁻¹ := by
      rw [MulAut.conj_apply]; exact h2.2.2.1 a haK2
    have hy : (D.t1 * D.t2) * a * (D.t1 * D.t2)⁻¹ = a⁻¹ := by
      rw [← MulAut.conj_apply, map_mul, MulAut.mul_apply, ht2a, map_inv, ht1a]
    exact mul_comm_of_conj_eq_self (conj_sq_of_conj_eq_inv hy)
  -- `t₁t₂` fixes every element of `B = B₁ ∩ B₂` (both `t₁` and `t₂` centralize it)
  have hB : (D.t1 * D.t2) ^ 2 ∈
      Subgroup.centralizer ((D.B : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    simp only [Subgroup.mem_inf, SetLike.mem_coe] at hb
    obtain ⟨⟨-, hbC1⟩, ⟨-, hbC2⟩⟩ := hb
    have ht1b : MulAut.conj D.t1 b = b := by
      rw [MulAut.conj_apply]
      exact (mul_inv_eq_iff_eq_mul).mpr
        ((Subgroup.mem_centralizer_iff.mp hbC1) D.t1 (Set.mem_singleton D.t1))
    have ht2b : MulAut.conj D.t2 b = b := by
      rw [MulAut.conj_apply]
      exact (mul_inv_eq_iff_eq_mul).mpr
        ((Subgroup.mem_centralizer_iff.mp hbC2) D.t2 (Set.mem_singleton D.t2))
    have hy : (D.t1 * D.t2) * b * (D.t1 * D.t2)⁻¹ = b := by
      rw [← MulAut.conj_apply, map_mul, MulAut.mul_apply, ht2b, ht1b]
    exact mul_comm_of_conj_eq_self (conj_sq_of_conj_eq_self hy)
  -- `t₁t₂` fixes every element of `K₁ ∩ K₂` (both `t₁` and `t₂` invert it)
  have hK : (D.t1 * D.t2) ^ 2 ∈
      Subgroup.centralizer (((K1 ⊓ K2 : Subgroup G)) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    simp only [Subgroup.mem_inf, SetLike.mem_coe] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have ht1x : MulAut.conj D.t1 x = x⁻¹ := by
      rw [MulAut.conj_apply]; exact h1.2.2.1 x hx1
    have ht2x : MulAut.conj D.t2 x = x⁻¹ := by
      rw [MulAut.conj_apply]; exact h2.2.2.1 x hx2
    have hy : (D.t1 * D.t2) * x * (D.t1 * D.t2)⁻¹ = x := by
      rw [← MulAut.conj_apply, map_mul, MulAut.mul_apply, ht2x, map_inv, ht1x, inv_inv]
    exact mul_comm_of_conj_eq_self (conj_sq_of_conj_eq_self hy)
  -- assemble over the two factors `A = B₁ ∩ K₂` and `C = B (K₁ ∩ K₂)` of `U`
  have hAC : (D.t1 * D.t2) ^ 2 ∈
      Subgroup.centralizer
        (((D.B1 ⊓ K2) ⊔ (D.B ⊔ (K1 ⊓ K2)) : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_sup]
    refine ⟨hA, ?_⟩
    rw [Subgroup.centralizer_sup]
    exact ⟨hB, hK⟩
  have hU : ((D.B1 ⊓ K2) ⊔ (D.B ⊔ (K1 ⊓ K2)) : Subgroup G) = D.U := hd.1
  simpa only [hU] using hAC

end Work.BG
