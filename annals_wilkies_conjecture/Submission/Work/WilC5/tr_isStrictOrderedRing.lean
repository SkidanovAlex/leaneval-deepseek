import Mathlib
import Submission.Work.WilC5.TRCanon

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

theorem tr_isStrictOrderedRing (M : Type)
    [FirstOrder.Language.Structure WilkiesDesign.CG.LRc M]
    (h : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR) :
    @IsStrictOrderedRing M (Work.WilC5.trField M h).toSemiring
      (Work.WilC5.trLinearOrder M h).toPartialOrder := by
  letI : Field M := trField M h
  letI : LinearOrder M := trLinearOrder M h
  have hle : ∀ x y : M, x ≤ y ↔ leEL x y := fun x y => Iff.rfl
  have hlt : ∀ x y : M, x < y ↔ leEL x y ∧ ¬ leEL y x := fun x y => Iff.rfl
  have hs : ∀ x y : M, leEL x y ↔ IsSquare (y - x) := by
    intro x y
    rw [leEL, isSquareL]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
  have hsq_le : ∀ x y : M, x ≤ y ↔ IsSquare (y - x) := fun x y => (hle x y).trans (hs x y)
  have hsq_lt : ∀ x y : M, x < y ↔ IsSquare (y - x) ∧ ¬ IsSquare (x - y) := by
    intro x y
    rw [hlt x y]
    exact and_congr (hs x y) (not_congr (hs y x))
  -- additive compatibility
  have hadd : ∀ a b : M, a ≤ b → ∀ c : M, a + c ≤ b + c := by
    intro a b hab c
    rw [hsq_le] at hab ⊢
    rwa [show b + c - (a + c) = b - a by ring]
  have hadd' : ∀ a b : M, a ≤ b → ∀ c : M, c + a ≤ c + b := by
    intro a b hab c
    rw [hsq_le] at hab ⊢
    rwa [show c + b - (c + a) = b - a by ring]
  have hcancel : ∀ a b c : M, a + b ≤ a + c → b ≤ c := by
    intro a b c hbc
    rw [hsq_le] at hbc ⊢
    rwa [show c - b = a + c - (a + b) by ring]
  have hcancel' : ∀ a b c : M, b + a ≤ c + a → b ≤ c := by
    intro a b c hbc
    rw [hsq_le] at hbc ⊢
    rwa [show c - b = c + a - (b + a) by ring]
  -- multiplicative compatibility
  have hmulL : ∀ a : M, 0 < a → ∀ b c : M, b < c → a * b < a * c := by
    intro a ha b c hbc
    rw [hsq_lt] at ha hbc ⊢
    have ha_sq : IsSquare a := by simpa using ha.1
    have ha_ne : a ≠ 0 := by
      intro h0
      apply ha.2
      rw [h0]
      exact ⟨0, by ring⟩
    constructor
    · rw [show a * c - a * b = a * (c - b) by ring]
      exact ha_sq.mul hbc.1
    · intro h
      apply hbc.2
      have hfac : (a * b - a * c) * a⁻¹ = b - c := by
        calc (a * b - a * c) * a⁻¹ = (a * (b - c)) * a⁻¹ := by ring
          _ = (b - c) * (a * a⁻¹) := by ring
          _ = (b - c) * 1 := by rw [mul_inv_cancel₀ ha_ne]
          _ = b - c := by rw [mul_one]
      have h2 : IsSquare ((a * b - a * c) * a⁻¹) := h.mul (IsSquare.inv ha_sq)
      rwa [hfac] at h2
  have hmulR : ∀ c : M, 0 < c → ∀ a b : M, a < b → a * c < b * c := by
    intro c hc a b hab
    rw [hsq_lt] at hc hab ⊢
    have hc_sq : IsSquare c := by simpa using hc.1
    have hc_ne : c ≠ 0 := by
      intro h0
      apply hc.2
      rw [h0]
      exact ⟨0, by ring⟩
    constructor
    · rw [show b * c - a * c = (b - a) * c by ring]
      exact hab.1.mul hc_sq
    · intro h
      apply hab.2
      have hfac : (a * c - b * c) * c⁻¹ = a - b := by
        calc (a * c - b * c) * c⁻¹ = ((a - b) * c) * c⁻¹ := by ring
          _ = (a - b) * (c * c⁻¹) := by ring
          _ = (a - b) * 1 := by rw [mul_inv_cancel₀ hc_ne]
          _ = a - b := by rw [mul_one]
      have h2 : IsSquare ((a * c - b * c) * c⁻¹) := h.mul (IsSquare.inv hc_sq)
      rwa [hfac] at h2
  have hZLO : ZeroLEOneClass M := ⟨by
    rw [hsq_le]
    exact ⟨1, by ring⟩⟩
  have hOAM : IsOrderedAddMonoid M := ⟨hadd, hadd'⟩
  have hOCAM : IsOrderedCancelAddMonoid M :=
    { toIsOrderedAddMonoid := hOAM
      le_of_add_le_add_left := hcancel
      le_of_add_le_add_right := hcancel' }
  exact { toIsOrderedCancelAddMonoid := hOCAM
          toZeroLEOneClass := hZLO
          toNontrivial := inferInstance
          toPosMulStrictMono := ⟨hmulL⟩
          toMulPosStrictMono := ⟨hmulR⟩ }

end Work.WilC5
