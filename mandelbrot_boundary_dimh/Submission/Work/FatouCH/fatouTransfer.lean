import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# Transfer of the `ℤ`-shift relation between two Fatou coordinates

Shishikura's orbit relation `MandelDim.FatouOrbit` (A.2.1(i)) says that for *any* Fatou coordinate
`Ψ` on `Q = MandelDim.Qreg b₁ b₂`, `Ψ z' = Ψ z + n` (`n : ℕ`) forces `z' = F^[n] z` with all
intermediate iterates in `Q`.  Iterating the Abel equation of a second Fatou coordinate then
converts `Φ₀ z' = Φ₀ z + k` (`k : ℤ`) into `Φ z' = Φ z + k`, and vice versa.
-/

namespace Work.FatouCH

open Set Metric Complex
open scoped Topology

variable {b₁ b₂ : Option ℂ} {F Φ₀ Φ Ψ : ℂ → ℂ}

/-- Iterating the Abel equation of a Fatou coordinate along an orbit that stays in `Q`. -/
theorem iterate_abel (hΨ : MandelDim.IsFatouCoordOn F Ψ (MandelDim.Qreg b₁ b₂)) {z : ℂ} {n : ℕ}
    (h : ∀ j ≤ n, F^[j] z ∈ MandelDim.Qreg b₁ b₂) :
    Ψ (F^[n] z) = Ψ z + (n : ℂ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : ∀ j ≤ k, F^[j] z ∈ MandelDim.Qreg b₁ b₂ :=
      fun j hj => h j (le_trans hj (Nat.le_succ k))
    have ihk : Ψ (F^[k] z) = Ψ z + (k : ℂ) := ih hk
    have hk1 : F^[k] z ∈ MandelDim.Qreg b₁ b₂ := h k (Nat.le_succ k)
    have hk2 : F (F^[k] z) ∈ MandelDim.Qreg b₁ b₂ := by
      have hstep : F^[k + 1] z = F (F^[k] z) := Function.iterate_succ_apply' F k z
      rw [← hstep]
      exact h (k + 1) le_rfl
    have habel : Ψ (F (F^[k] z)) = Ψ (F^[k] z) + 1 := hΨ.2.2 (F^[k] z) hk1 hk2
    calc Ψ (F^[k + 1] z) = Ψ (F (F^[k] z)) := by rw [Function.iterate_succ_apply']
      _ = Ψ (F^[k] z) + 1 := habel
      _ = Ψ z + (k : ℂ) + 1 := by rw [ihk]
      _ = Ψ z + ((k + 1 : ℕ) : ℂ) := by push_cast; ring

/-- Forward transfer for a nonnegative shift. -/
theorem fatouTransfer_nat (hO : MandelDim.FatouOrbit) (hadm : MandelDim.QAdm b₁ b₂)
    (hNT : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (h₀ : MandelDim.IsFatouCoordOn F Φ₀ (MandelDim.Qreg b₁ b₂))
    (h₁ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂))
    {z z' : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂) (hz' : z' ∈ MandelDim.Qreg b₁ b₂) (n : ℕ)
    (h : Φ₀ z' = Φ₀ z + (n : ℂ)) : Φ z' = Φ z + (n : ℂ) := by
  obtain ⟨horbit, hiter⟩ := hO b₁ b₂ F Φ₀ hadm hNT h₀ z hz z' hz' n h
  have h1 := iterate_abel h₁ horbit
  rwa [hiter] at h1

/-- Transfer between two Fatou coordinates: the `ℤ`-shift relation of one is the `ℤ`-shift
relation of the other. -/
theorem fatouTransfer (hO : MandelDim.FatouOrbit) (hadm : MandelDim.QAdm b₁ b₂)
    (hNT : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (h₀ : MandelDim.IsFatouCoordOn F Φ₀ (MandelDim.Qreg b₁ b₂))
    (h₁ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂)) :
    ∀ z ∈ MandelDim.Qreg b₁ b₂, ∀ z' ∈ MandelDim.Qreg b₁ b₂, ∀ k : ℤ,
      (Φ₀ z' = Φ₀ z + (k : ℂ) ↔ Φ z' = Φ z + (k : ℂ)) := by
  intro z hz z' hz' k
  constructor
  · intro h
    by_cases hk : 0 ≤ k
    · have hkn : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by
        exact_mod_cast (Int.toNat_of_nonneg hk)
      have h' : Φ₀ z' = Φ₀ z + ((k.toNat : ℕ) : ℂ) := by rw [hkn]; exact h
      have := fatouTransfer_nat hO hadm hNT h₀ h₁ hz hz' k.toNat h'
      rwa [hkn] at this
    · have hklt : k < 0 := not_le.mp hk
      have hkpos : (0 : ℤ) < -k := by omega
      have hmn : (((-k).toNat : ℕ) : ℂ) = ((-k : ℤ) : ℂ) := by
        exact_mod_cast (Int.toNat_of_nonneg hkpos.le)
      have h2 : Φ₀ z = Φ₀ z' + (((-k : ℤ)) : ℂ) := by
        rw [h, Int.cast_neg]
        ring
      have h' : Φ₀ z = Φ₀ z' + (((-k).toNat : ℕ) : ℂ) := by rw [hmn]; exact h2
      have h3 := fatouTransfer_nat hO hadm hNT h₀ h₁ hz' hz (-k).toNat h'
      rw [hmn] at h3
      rw [h3, Int.cast_neg]
      ring
  · intro h
    by_cases hk : 0 ≤ k
    · have hkn : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by
        exact_mod_cast (Int.toNat_of_nonneg hk)
      have h' : Φ z' = Φ z + ((k.toNat : ℕ) : ℂ) := by rw [hkn]; exact h
      have := fatouTransfer_nat hO hadm hNT h₁ h₀ hz hz' k.toNat h'
      rwa [hkn] at this
    · have hklt : k < 0 := not_le.mp hk
      have hkpos : (0 : ℤ) < -k := by omega
      have hmn : (((-k).toNat : ℕ) : ℂ) = ((-k : ℤ) : ℂ) := by
        exact_mod_cast (Int.toNat_of_nonneg hkpos.le)
      have h2 : Φ z = Φ z' + (((-k : ℤ)) : ℂ) := by
        rw [h, Int.cast_neg]
        ring
      have h' : Φ z = Φ z' + (((-k).toNat : ℕ) : ℂ) := by rw [hmn]; exact h2
      have h3 := fatouTransfer_nat hO hadm hNT h₁ h₀ hz' hz (-k).toNat h'
      rw [hmn] at h3
      rw [h3, Int.cast_neg]
      ring

end Work.FatouCH
