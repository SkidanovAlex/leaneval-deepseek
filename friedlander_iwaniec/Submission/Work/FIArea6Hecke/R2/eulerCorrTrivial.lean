import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea6Hecke.R.heckeLSeriesPartnerOdd

set_option autoImplicit false

namespace Work.FIArea6Hecke.R2

open scoped BigOperators

/-- The constant-one coefficient family is a conductor partner of any strict `χ` (at modulus `1`):
it is multiplicative, bounded, periodic modulo `1`, and (vacuously) vanishes off the units mod `1`.
It agrees with `χ` on the primary units mod `4d` exactly when `χ` is trivial there (`htriv`). -/
theorem one_isConductorPartner (d : ℕ) (chi : GaussianInt → ℂ)
    (htriv : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → chi z = 1) :
    Work.FIArea6Hecke.R.IsConductorPartner d chi (1 : GaussianInt)
      (fun _ : GaussianInt => (1 : ℂ)) := by
  refine ⟨one_dvd _, one_ne_zero, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro z w
    rw [mul_one]
  · intro z
    simp
  · intro z w _
    rfl
  · intro z hz
    exact absurd (⟨0, one_dvd _⟩ : Work.FIArea6Hecke.R.IsUnitMod 1 z) hz
  · intro z hz hzu
    exact (htriv z hz hzu).symm

/-- **Friedlander–Iwaniec, Euler-factor correction (trivial case).**  If the strict character `χ`
modulo `4d` is trivial on the primary units modulo `4d`, then `χ` differs from the constant
coefficient family `1` only at the odd rational primes dividing `4d`, and the two Hecke
`L`-series differ by the corresponding finite product of inverse local Euler factors. -/
theorem eulerCorrTrivial (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (k : ℕ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (htriv : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → chi z = 1) :
    ∃ (S : Finset ℕ) (c₁ c₂ : ℕ → ℂ),
      (∀ p ∈ S, Nat.Prime p ∧ p ∣ 4 * d ∧ p ≠ 2 ∧ ‖c₁ p‖ ≤ 1 ∧ ‖c₂ p‖ ≤ 1) ∧
      (∀ s : ℂ, 1 < s.re →
        Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1 : ℂ)) (k : ℤ) s =
          Work.FIArea5.S16Hecke.heckeLSeries chi (k : ℤ) s *
          ∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s))))⁻¹) := by
  classical
  have hpart := one_isConductorPartner d chi htriv
  obtain ⟨S, c₁, c₂, hS, hid⟩ :=
    Work.FIArea6Hecke.R.heckeLSeriesPartnerOdd d hd chi (1 : GaussianInt)
      (fun _ : GaussianInt => (1 : ℂ)) (k : ℤ) hchi hpart
  refine ⟨S, c₁, c₂, hS, ?_⟩
  intro s hs
  -- every correction factor at a prime `p ∈ S` is nonzero: `‖c_i(p) p^{-s}‖ ≤ p^{-re s} < 1`
  have hfac : ∀ p ∈ S,
      (1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s))) ≠ 0 := by
    intro p hp
    have hpp : Nat.Prime p := (hS p hp).1
    have hu : ‖((p : ℂ) ^ (-s))‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re]
      rw [Real.rpow_lt_one_iff (Nat.cast_nonneg p)]
      exact Or.inr (Or.inl ⟨by exact_mod_cast hpp.one_lt, by linarith⟩)
    have hne : ∀ c : ℂ, ‖c‖ ≤ 1 → 1 - c * ((p : ℂ) ^ (-s)) ≠ 0 := by
      intro c hc h
      have hcu : c * ((p : ℂ) ^ (-s)) = 1 := (sub_eq_zero.mp h).symm
      have hle : ‖c * ((p : ℂ) ^ (-s))‖ ≤ ‖((p : ℂ) ^ (-s))‖ := by
        rw [norm_mul]
        calc ‖c‖ * ‖((p : ℂ) ^ (-s))‖ ≤ 1 * ‖((p : ℂ) ^ (-s))‖ :=
              mul_le_mul_of_nonneg_right hc (norm_nonneg _)
          _ = ‖((p : ℂ) ^ (-s))‖ := one_mul _
      rw [hcu, norm_one] at hle
      linarith
    exact mul_ne_zero (hne (c₁ p) (hS p hp).2.2.2.1) (hne (c₂ p) (hS p hp).2.2.2.2)
  have hD : (∏ p ∈ S,
      (1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac
  rw [hid s hs, Finset.prod_inv_distrib, mul_assoc, mul_inv_cancel₀ hD, mul_one]

end Work.FIArea6Hecke.R2
