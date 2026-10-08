import Mathlib

namespace Work.AUTL2.Normalizer

theorem exists_fieldAut_of_sq_smul (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (s : F → F) (h0 : s 0 = 0) (hadd : ∀ x y : F, s (x + y) = s x + s y)
    (hs : Function.Bijective s) (h1 : s 1 ≠ 0)
    (hsq : ∀ a : Fˣ, ∃ b : Fˣ, ∀ x : F, s (↑a ^ 2 * x) = ↑b ^ 2 * s x) :
    ∃ σ : F ≃+* F, ∀ x : F, s x = s 1 * σ x := by
  let c : F := (s 1)⁻¹
  let σf : F → F := fun x => c * s x
  have hcne : c ≠ 0 := by dsimp only [c]; exact inv_ne_zero h1
  have hc1 : c * s 1 = 1 := by dsimp only [c]; exact inv_mul_cancel₀ h1
  have hσadd : ∀ x y : F, σf (x + y) = σf x + σf y := by
    intro x y
    dsimp only [σf]
    rw [hadd x y, mul_add]
  have hσ0 : σf 0 = 0 := by dsimp only [σf]; simp [h0]
  have hσneg : ∀ x : F, σf (-x) = -σf x := by
    intro x
    have h := hσadd x (-x)
    rw [add_neg_cancel, hσ0] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hσsub : ∀ x y : F, σf (x - y) = σf x - σf y := by
    intro x y
    simp only [sub_eq_add_neg, hσadd, hσneg]
  -- Every `t^2` (t ≠ 0) acts multiplicatively.
  have key : ∀ (t : F) (y : F), σf (t ^ 2 * y) = σf (t ^ 2) * σf y := by
    intro t y
    by_cases ht : t = 0
    · subst ht
      have hz1 : (0 : F) ^ 2 * y = 0 := by ring
      have hz2 : (0 : F) ^ 2 = 0 := by ring
      rw [hz1, hz2, hσ0]
      ring
    · obtain ⟨b, hb⟩ := hsq (Units.mk0 t ht)
      have hb1 : s ((↑(Units.mk0 t ht) : F) ^ 2) = (↑b : F) ^ 2 * s 1 := by
        simpa using hb 1
      have e1 : σf ((↑(Units.mk0 t ht) : F) ^ 2 * y) = (↑b : F) ^ 2 * σf y := by
        dsimp only [σf]
        rw [hb y, mul_left_comm]
      have e2 : σf ((↑(Units.mk0 t ht) : F) ^ 2) = (↑b : F) ^ 2 := by
        dsimp only [σf]
        rw [hb1, mul_left_comm c, hc1, mul_one]
      have hfin : σf ((↑(Units.mk0 t ht) : F) ^ 2 * y)
          = σf ((↑(Units.mk0 t ht) : F) ^ 2) * σf y := e1.trans (by rw [← e2])
      simpa [Units.val_mk0 ht] using hfin
  have hσmul : ∀ x y : F, σf (x * y) = σf x * σf y := by
    intro x y
    have hxdec : x = ((x + 1) / 2) ^ 2 - ((x - 1) / 2) ^ 2 := by
      field_simp
      ring
    have hxy : x * y = ((x + 1) / 2) ^ 2 * y - ((x - 1) / 2) ^ 2 * y := by
      rw [← sub_mul, ← hxdec]
    have hfac : σf (((x + 1) / 2) ^ 2) - σf (((x - 1) / 2) ^ 2) = σf x := by
      rw [← hσsub, ← hxdec]
    rw [hxy, hσsub, key, key, ← sub_mul, hfac]
  have hfbij : Function.Bijective σf := by
    constructor
    · intro x y h
      dsimp only [σf] at h
      exact hs.1 (mul_left_cancel₀ hcne h)
    · intro z
      obtain ⟨x, hx⟩ := hs.2 (c⁻¹ * z)
      refine ⟨x, ?_⟩
      dsimp only [σf]
      rw [hx, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]
  refine ⟨RingEquiv.mk (Equiv.ofBijective σf hfbij) ?_ ?_, ?_⟩
  · intro x y
    show σf (x * y) = σf x * σf y
    exact hσmul x y
  · intro x y
    show σf (x + y) = σf x + σf y
    exact hσadd x y
  · intro x
    show s x = s 1 * σf x
    dsimp only [σf, c]
    rw [← mul_assoc, mul_inv_cancel₀ h1, one_mul]

end Work.AUTL2.Normalizer
