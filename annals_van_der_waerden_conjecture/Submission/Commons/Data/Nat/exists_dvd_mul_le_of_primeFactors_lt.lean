import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.PrimeFin

namespace Commons.Data.Nat

/-- Given `M ≤ X ≤ M * S` with every prime factor of `S` smaller than `Y`,
there is a divisor `B` of `M * S` with `X ≤ B` and `B < X * Y`. -/
theorem exists_dvd_mul_le_of_primeFactors_lt (M S X Y : ℕ) (hM : 1 ≤ M) (hMX : M ≤ X)
    (hY : 1 < Y) (hXS : X ≤ M * S) (h : ∀ p ∈ S.primeFactors, p < Y) :
    ∃ B : ℕ, B ∣ M * S ∧ X ≤ B ∧ (B : ℝ) < (X : ℝ) * (Y : ℝ) := by
  classical
  have hX1 : 1 ≤ X := le_trans hM hMX
  have hXpos : 0 < X := lt_of_lt_of_le Nat.zero_lt_one hX1
  -- the minimal divisor of `M * S` that is at least `X`
  have hD : ∃ d : ℕ, d ∣ M * S ∧ X ≤ d := ⟨M * S, dvd_refl _, hXS⟩
  set B := Nat.find hD with hBdef
  have hBdvd : B ∣ M * S := (Nat.find_spec hD).1
  have hBX : X ≤ B := (Nat.find_spec hD).2
  have hBmin : ∀ d, d ∣ M * S → X ≤ d → B ≤ d :=
    fun d hd hdX => Nat.find_min' hD (show d ∣ M * S ∧ X ≤ d from ⟨hd, hdX⟩)
  have hB1 : 1 ≤ B := le_trans hX1 hBX
  have hB0 : B ≠ 0 := by omega
  have hS0 : S ≠ 0 := by
    intro hS
    rw [hS, mul_zero] at hXS
    omega
  refine ⟨B, hBdvd, hBX, ?_⟩
  by_cases hcase : ∃ p, p ∈ B.primeFactors ∧ p ∈ S.primeFactors
  · -- `B` has a prime factor coming from `S`, which is `< Y`; dividing it out
    -- drops below `X` by minimality of `B`.
    rcases hcase with ⟨p, hpB, hpS⟩
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hpB).1
    have hpBdvd : p ∣ B := (Nat.mem_primeFactors.mp hpB).2.1
    have hpY : p < Y := h p hpS
    have hBpdvd : B / p ∣ M * S := (Nat.div_dvd_of_dvd hpBdvd).trans hBdvd
    have hBpltB : B / p < B := Nat.div_lt_self (lt_of_lt_of_le Nat.zero_lt_one hB1) hpp.one_lt
    have hBpltX : B / p < X := by
      by_contra hle
      push Not at hle
      exact absurd (hBmin (B / p) hBpdvd hle) (not_le.mpr hBpltB)
    have hBeq : B = B / p * p := (Nat.div_mul_cancel hpBdvd).symm
    have hlt : B < X * Y := by
      rw [hBeq]
      calc B / p * p < X * p := Nat.mul_lt_mul_of_pos_right hBpltX hpp.pos
        _ < X * Y := Nat.mul_lt_mul_of_pos_left hpY hXpos
    have hcast : (B : ℝ) < ((X * Y : ℕ) : ℝ) := by exact_mod_cast hlt
    rwa [Nat.cast_mul] at hcast
  · -- otherwise `B` is coprime to `S`, hence divides `M`, hence equals `X`.
    push Not at hcase
    have hcop : Nat.Coprime B S := by
      by_contra hnc
      obtain ⟨p, hpp, hpB, hpS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      exact (hcase p (hpp.mem_primeFactors hpB hB0)) (hpp.mem_primeFactors hpS hS0)
    have hBM : B ∣ M := hcop.dvd_of_dvd_mul_right hBdvd
    have hleM : B ≤ M := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hM) hBM
    have hBeq : B = X := le_antisymm (le_trans hleM hMX) hBX
    rw [hBeq]
    have hYr : (1 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
    have hXr : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos
    simpa using mul_lt_mul_of_pos_left hYr hXr

end Commons.Data.Nat