import Mathlib

namespace Work.HP.NA.Smooth

theorem card_ker_of_surj {R : Type*} [CommRing R] [Fintype R] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : (ι → R) →ₗ[R] (κ → R)) (hT : Function.Surjective T) (h : Fintype.card κ ≤ Fintype.card ι) :
    Nat.card (LinearMap.ker T) = (Fintype.card R) ^ (Fintype.card ι - Fintype.card κ) := by
  -- Choose a section of the surjective linear map `T`.
  obtain ⟨g, hg⟩ := hT.hasRightInverse
  -- The chosen section splits the underlying additive group: `(ι → R) ≃ ker T × (κ → R)`.
  have he : ((LinearMap.ker T) × (κ → R)) ≃ (ι → R) :=
    ⟨fun p => (p.1 : ι → R) + g p.2,
     fun z => (⟨z - g (T z), by
        rw [LinearMap.mem_ker, map_sub, hg (T z), sub_self]⟩, T z),
     by
      rintro ⟨x, y⟩
      simp only [Prod.mk.injEq]
      constructor
      · apply Subtype.ext
        change (x : ι → R) + g y - g (T ((x : ι → R) + g y)) = (x : ι → R)
        have h2' : T ((x : ι → R) + g y) = y := by
          rw [map_add, hg y, LinearMap.mem_ker.mp x.2, zero_add]
        rw [h2']
        exact add_sub_cancel_right _ _
      · rw [map_add, hg y, LinearMap.mem_ker.mp x.2, zero_add],
     by
      intro z
      exact sub_add_cancel _ _⟩
  have hcard : Nat.card ((LinearMap.ker T) × (κ → R)) = Nat.card (ι → R) :=
    Nat.card_congr he
  rw [Nat.card_prod] at hcard
  have hkc : Nat.card (κ → R) = (Fintype.card R) ^ (Fintype.card κ) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hic : Nat.card (ι → R) = (Fintype.card R) ^ (Fintype.card ι) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h1 : Nat.card (LinearMap.ker T) * (Fintype.card R) ^ (Fintype.card κ)
      = (Fintype.card R) ^ (Fintype.card ι) := by
    rw [← hkc, ← hic]
    exact hcard
  -- Now solve the arithmetic: `K * N^m = N^n` with `m ≤ n` gives `K = N^(n-m)`.
  have hN : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨0⟩
  have hpow : 0 < (Fintype.card R) ^ (Fintype.card κ) := pow_pos hN _
  have h2 : (Fintype.card R) ^ (Fintype.card ι)
      = (Fintype.card R) ^ (Fintype.card κ) * (Fintype.card R) ^ (Fintype.card ι - Fintype.card κ) := by
    rw [← pow_add, Nat.add_sub_of_le h]
  have h3 : Nat.card (LinearMap.ker T) * (Fintype.card R) ^ (Fintype.card κ)
      = (Fintype.card R) ^ (Fintype.card ι - Fintype.card κ) * (Fintype.card R) ^ (Fintype.card κ) := by
    rw [h1, h2, mul_comm]
  exact Nat.mul_right_cancel hpow h3

end Work.HP.NA.Smooth
