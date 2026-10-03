import Mathlib
import Submission.Work.FIArea6Hecke.R.chiPrimeDefs
import Submission.Work.FIArea6Hecke.R.heckeStripLogDerivConductor
import Submission.Work.FIArea6Hecke.R.m_eq_zero_of_selfDual
import Submission.Work.FIArea6Hecke.R.exists_realCharacter_agreeing_on_primary
import Submission.Work.FIArea6Hecke.R.LamOneNeZeroDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core
import Submission.Work.FIArea5.S16Hecke.twistAux

namespace Work.FIArea6Hecke.R

open Work.FIPlan

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Auxiliary arithmetic

The normalisation `chiPrime d χ z = χ (primAssoc z)` is well defined modulo `4d`; the two
ingredients are that a unit modulo `4d` has *odd norm* (so that `primAssoc` is a genuine primary
associate of it) and that the primary associate of a unit modulo `4d` is again a unit modulo `4d`.
The key structural fact is that the unit `primaryUnit z ∈ μ₄` of `(1+i)³`-congruence
(`Work.FIArea5.S16Hecke.primaryUnit`) is related to `primAssoc` by

  `primAssoc z = z · star (primaryUnit z)`,

which makes the periodicity of `chiPrime` a direct consequence of
`Work.FIArea5.S16Hecke.primaryUnit_periodic`. -/

/-- `isOddG z` is "`gnorm z` is odd". -/
theorem isOddG_iff_odd_gnorm (z : GaussianInt) :
    Work.FIArea5.S16Hecke.isOddG z ↔ Odd (gnorm z) := by
  rw [Work.FIArea5.S16Hecke.GaussBasic.isOddG_iff_odd, Work.FIArea5.S16Hecke.odd_gnorm_iff]

/-- **A unit modulo `4d` has odd norm.**  Equivalently `1 + i ∤ z`: since `(1+i)³ ∣ 4d`, a
multiple of `1+i` cannot be invertible modulo `4d`. -/
theorem odd_gnorm_of_isUnitMod4d {d : ℕ} (hd : 1 ≤ d) {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z) : Odd (gnorm z) := by
  have hNe : NeZero (4 * d) := ⟨by omega⟩
  haveI := hNe
  have hcop : (gnorm z).Coprime (4 * d) :=
    (Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime (d := d) z).mp hz
  rw [← Nat.not_even_iff_odd]
  intro h2
  have h2' : 2 ∣ gnorm z := even_iff_two_dvd.mp h2
  have h4d : 2 ∣ 4 * d := dvd_mul_of_dvd_left (by norm_num : (2:ℕ) ∣ 4) d
  have hgcd : 2 ∣ Nat.gcd (gnorm z) (4 * d) := Nat.dvd_gcd h2' h4d
  rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hgcd
  norm_num at hgcd

/-- A unit of `ℤ[i]` is a unit modulo `4d`. -/
private theorem isUnitMod4d_of_isUnit {d : ℕ} {u : GaussianInt} (hu : IsUnit u) :
    Work.FIArea5.S16Hecke.IsUnitMod4d d u := by
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  exact ⟨v, by rw [mul_comm u v, hv, sub_self]; exact dvd_zero _⟩

/-- **The primary associate of a unit modulo `4d` is again a unit modulo `4d`**: it differs from
`z` by a unit of `ℤ[i]`, and the units modulo `4d` form a submonoid. -/
theorem isUnitMod4d_primAssoc {d : ℕ} {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z) :
    Work.FIArea5.S16Hecke.IsUnitMod4d d (Work.FIArea4.primAssoc z) := by
  by_cases h : z ≠ 0 ∧ Odd (gnorm z)
  · obtain ⟨hz0, hodd⟩ := h
    obtain ⟨u, hu⟩ := Work.FIArea4.primAssoc_associated hz0 hodd
    have hpu : Work.FIArea4.primAssoc z = z * ↑u⁻¹ := by
      have h1 : (Work.FIArea4.primAssoc z * (↑u : GaussianInt)) * (↑u⁻¹ : GaussianInt)
          = z * (↑u⁻¹ : GaussianInt) := by rw [hu]
      have h2 : (↑u : GaussianInt) * (↑u⁻¹ : GaussianInt) = 1 := by simp
      rwa [mul_assoc, h2, mul_one] at h1
    rw [hpu]
    exact Work.FIArea6Hecke.isUnitMod4d_mul_iff.mpr
      ⟨hz, isUnitMod4d_of_isUnit (Units.isUnit u⁻¹)⟩
  · unfold Work.FIArea4.primAssoc
    rw [dif_neg h]
    exact hz

/-- `u · star u = 1` for the four units of `ℤ[i]`. -/
private theorem star_mul_self_mem_units4 {u : GaussianInt}
    (hu : u ∈ Work.FIArea5.S16Hecke.units4) : u * star u = 1 := by
  rw [Work.FIArea5.S16Hecke.mem_units4_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl <;> decide

/-- `star u · u = 1` for the four units of `ℤ[i]`. -/
private theorem mul_comm_units4 {u : GaussianInt}
    (hu : u ∈ Work.FIArea5.S16Hecke.units4) : star u * u = 1 := by
  rw [mul_comm, star_mul_self_mem_units4 hu]

/-- **The primary associate is the `(1+i)³`-normalisation of `z`.**  For an odd `z` the unique
unit `u ∈ μ₄` with `u ≡ z (mod (1+i)³)` (`Work.FIArea5.S16Hecke.primaryUnit`) satisfies
`z · star u = primAssoc z`, since `z · star u` is a primary associate of `z`:
`z = u · p` with `p` primary, so `z · star u = p`. -/
theorem primAssoc_eq_mul_star_primaryUnit {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.isOddG z) :
    Work.FIArea4.primAssoc z = z * star (Work.FIArea5.S16Hecke.primaryUnit z) := by
  obtain ⟨a, ha, p, hp, hzp⟩ := Work.FIArea5.S16Hecke.exists_unit_primary z hz
  have hpu : Work.FIArea5.S16Hecke.primaryUnit z = a := by
    refine Work.FIArea5.S16Hecke.primaryUnit_eq_of_dvd ha ?_
    have h1 : Work.FIArea5.S16Hecke.c3 ∣ p - 1 :=
      Work.FIArea5.S16Hecke.c3_dvd_sub_one_of_isPrimary hp
    have h2 : z - a = a * (p - 1) := by rw [hzp]; ring
    rw [h2]
    exact dvd_mul_of_dvd_right h1 a
  have hsa : a * star a = 1 := star_mul_self_mem_units4 ha
  have hzp' : z * star a = p := by
    rw [hzp]
    calc (a * p) * star a = p * (a * star a) := by ring
      _ = p := by rw [hsa, mul_one]
  have hprim : IsPrimary (z * star (Work.FIArea5.S16Hecke.primaryUnit z)) := by
    rw [hpu, hzp']; exact hp
  have hodd : Odd (gnorm z) := Work.FIArea5.S16Hecke.isOddG_gnorm_odd z hz
  have hz0 : z ≠ 0 := ne_zero_of_odd_gnorm hodd
  have hassoc : Associated (z * star (Work.FIArea5.S16Hecke.primaryUnit z)) z := by
    rw [hpu]
    obtain ⟨u, hu⟩ := Work.FIArea5.S16Hecke.isUnit_of_mem_units4 ha
    refine ⟨u, ?_⟩
    rw [hu]
    calc z * star a * a = z * (star a * a) := by ring
      _ = z := by rw [mul_comm_units4 ha, mul_one]
  exact (primAssoc_unique_of_odd hz0 hodd hassoc hprim).symm

/-- **The normalised character `chiPrime d chi` attached to a self-dual strict character is a
real-valued strict character with the same Hecke eigenvalues.**
`SelfDual d chi m` says `psi chi m z = chi z * (z/|z|)^m = ±1` on the primary units modulo `4d`;
it forces `m = 0` (`m_eq_zero_of_selfDual`).  The classical fix
is to normalise an odd `z` to its primary associate before evaluating `χ`:
`chiPrime d chi z = χ (primAssoc z)` for `z` a unit modulo `4d` and `0` otherwise.  The claim is that
this is again a strict character modulo `4d`, that it is real-valued, and that it has the *same
Hecke eigenvalues* `λ(n) = Σ_{z primary, |z|²=n} psi(z)` (`heckeLam`, hence the same `L`-series) as
`(χ, m)`.

Proof route: a unit modulo `4d` has odd norm and `primAssoc z` is a primary associate of `z`;
multiplicativity uses `primAssoc`-multiplicativity on odd elements together with the character
axioms of `χ` (the primary associates of two units are themselves units modulo `4d`); periodicity
modulo `4d` uses `primAssoc z = ε_z · z` with `ε_z ∈ μ₄` and the fact that `z ≡ w (mod 4d)` forces
`ε_z = ε_w` (the four units are pairwise incongruent modulo `4`); real-valuedness uses `SelfDual`
and `m = 0` (on a primary unit `psi chi 0 z = chi z` is `±1`); the eigenvalue identity compares the
two defining sums term by term, where on a non-unit primary `z` both sides vanish since `χ` is
strict. -/
theorem chiPrimeSelfDual {d : ℕ} {chi : GaussianInt → ℂ} {m : ℤ}
    (hd : 1 ≤ d) (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hsd : Work.FIArea6Hecke.R.SelfDual d chi m) :
    Work.FIArea5.S16Hecke.IsCharMod4dStrict d (Work.FIArea6Hecke.R.chiPrime d chi) ∧
      (∀ z : GaussianInt, star (Work.FIArea6Hecke.R.chiPrime d chi z)
        = Work.FIArea6Hecke.R.chiPrime d chi z) ∧
      (∀ n : ℕ, Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiPrime d chi) 0 n
        = Work.FIArea5.S16Hecke.heckeLam chi m n) := by
  have hm0 : m = 0 := m_eq_zero_of_selfDual hd hchi hsd
  obtain ⟨hchar, hstrict⟩ := hchi
  obtain ⟨hone, hmul, hnorm, hper, hvan⟩ := hchar
  -- the five character axioms of `chiPrime`
  have h1 : Work.FIArea6Hecke.R.chiPrime d chi 1 = 1 := by
    rw [Work.FIArea6Hecke.R.chiPrime_of_unit (Work.FIArea6Hecke.isUnitMod4d_one d),
      Work.FIArea4.primAssoc_eq_self Work.FIArea5.S16Hecke.isPrimary_one, hone]
  have h2 : ∀ z w : GaussianInt,
      Work.FIArea6Hecke.R.chiPrime d chi (z * w)
        = Work.FIArea6Hecke.R.chiPrime d chi z * Work.FIArea6Hecke.R.chiPrime d chi w := by
    intro z w
    by_cases hzw : Work.FIArea5.S16Hecke.IsUnitMod4d d (z * w)
    · obtain ⟨hz, hw⟩ := Work.FIArea6Hecke.isUnitMod4d_mul_iff.mp hzw
      rw [Work.FIArea6Hecke.R.chiPrime_of_unit hzw, Work.FIArea6Hecke.R.chiPrime_of_unit hz,
        Work.FIArea6Hecke.R.chiPrime_of_unit hw,
        primAssoc_mul_odd (odd_gnorm_of_isUnitMod4d hd hz) (odd_gnorm_of_isUnitMod4d hd hw),
        hmul]
    · rw [Work.FIArea6Hecke.R.chiPrime_of_not_unit hzw]
      by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
      · have hw : ¬ Work.FIArea5.S16Hecke.IsUnitMod4d d w :=
          fun h => hzw (Work.FIArea6Hecke.isUnitMod4d_mul_iff.mpr ⟨hz, h⟩)
        rw [Work.FIArea6Hecke.R.chiPrime_of_unit hz,
          Work.FIArea6Hecke.R.chiPrime_of_not_unit hw, mul_zero]
      · rw [Work.FIArea6Hecke.R.chiPrime_of_not_unit hz, zero_mul]
  have h3 : ∀ z : GaussianInt, ‖Work.FIArea6Hecke.R.chiPrime d chi z‖ ≤ 1 := by
    intro z
    by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
    · rw [Work.FIArea6Hecke.R.chiPrime_of_unit hz]; exact hnorm _
    · rw [Work.FIArea6Hecke.R.chiPrime_of_not_unit hz]; simp
  have h4 : ∀ z w : GaussianInt, (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (z - w) →
      Work.FIArea6Hecke.R.chiPrime d chi z = Work.FIArea6Hecke.R.chiPrime d chi w := by
    intro z w hzw
    by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
    · have hw : Work.FIArea5.S16Hecke.IsUnitMod4d d w :=
        (Work.FIArea6Hecke.isUnitMod4d_congr' hzw).mp hz
      have hoddz : Odd (gnorm z) := odd_gnorm_of_isUnitMod4d hd hz
      have hoddw : Odd (gnorm w) := odd_gnorm_of_isUnitMod4d hd hw
      rw [Work.FIArea6Hecke.R.chiPrime_of_unit hz, Work.FIArea6Hecke.R.chiPrime_of_unit hw,
        primAssoc_eq_mul_star_primaryUnit ((isOddG_iff_odd_gnorm z).mpr hoddz),
        primAssoc_eq_mul_star_primaryUnit ((isOddG_iff_odd_gnorm w).mpr hoddw)]
      have hpu : Work.FIArea5.S16Hecke.primaryUnit z = Work.FIArea5.S16Hecke.primaryUnit w :=
        Work.FIArea5.S16Hecke.primaryUnit_periodic hzw
      have hzwchi : chi z = chi w := hper z w hzw
      have hstar : chi (star (Work.FIArea5.S16Hecke.primaryUnit z))
          = chi (star (Work.FIArea5.S16Hecke.primaryUnit w)) := by rw [hpu]
      calc chi (z * star (Work.FIArea5.S16Hecke.primaryUnit z))
          = chi z * chi (star (Work.FIArea5.S16Hecke.primaryUnit z)) := hmul _ _
        _ = chi w * chi (star (Work.FIArea5.S16Hecke.primaryUnit w)) := by rw [hzwchi, hstar]
        _ = chi (w * star (Work.FIArea5.S16Hecke.primaryUnit w)) := (hmul _ _).symm
    · have hw : ¬ Work.FIArea5.S16Hecke.IsUnitMod4d d w :=
        fun h => hz ((Work.FIArea6Hecke.isUnitMod4d_congr' hzw).mpr h)
      rw [Work.FIArea6Hecke.R.chiPrime_of_not_unit hz,
        Work.FIArea6Hecke.R.chiPrime_of_not_unit hw]
  have h5 : ∀ z : GaussianInt, (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ z →
      Work.FIArea6Hecke.R.chiPrime d chi z = 0 :=
    fun z hz => Work.FIArea6Hecke.R.chiPrime_of_not_unit
      (Work.FIArea6Hecke.not_isUnitMod4d_of_dvd hd hz)
  have hchar' : Work.FITop3.IsCharMod4d d (Work.FIArea6Hecke.R.chiPrime d chi) :=
    ⟨h1, h2, h3, h4, h5⟩
  have h6 : ∀ z : GaussianInt, ¬ Work.FIArea5.S16Hecke.IsUnitMod4d d z →
      Work.FIArea6Hecke.R.chiPrime d chi z = 0 :=
    fun z hz => Work.FIArea6Hecke.R.chiPrime_of_not_unit hz
  -- real-valuedness
  have hreal : ∀ z : GaussianInt, star (Work.FIArea6Hecke.R.chiPrime d chi z)
      = Work.FIArea6Hecke.R.chiPrime d chi z := by
    intro z
    by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
    · rw [Work.FIArea6Hecke.R.chiPrime_of_unit hz]
      have hodd : Odd (gnorm z) := odd_gnorm_of_isUnitMod4d hd hz
      have hz0 : z ≠ 0 := ne_zero_of_odd_gnorm hodd
      have hwp : IsPrimary (Work.FIArea4.primAssoc z) :=
        Work.FIArea4.primAssoc_primary hz0 hodd
      have hwu : Work.FIArea5.S16Hecke.IsUnitMod4d d (Work.FIArea4.primAssoc z) :=
        isUnitMod4d_primAssoc hz
      have hsq := hsd (Work.FIArea4.primAssoc z) hwp hwu
      rw [hm0] at hsq
      have hpsi : Work.FIArea5.S16Hecke.psi chi 0 (Work.FIArea4.primAssoc z)
          = chi (Work.FIArea4.primAssoc z) := by
        rw [Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one]
      rw [hpsi] at hsq
      have h0 : (chi (Work.FIArea4.primAssoc z) - 1)
          * (chi (Work.FIArea4.primAssoc z) + 1) = 0 := by
        linear_combination hsq
      rcases mul_eq_zero.mp h0 with h7 | h7
      · rw [sub_eq_zero] at h7; rw [h7]; simp
      · rw [add_eq_zero_iff_eq_neg] at h7; rw [h7]; simp
    · rw [Work.FIArea6Hecke.R.chiPrime_of_not_unit hz]; simp
  -- the Hecke eigenvalues agree
  have hev : ∀ n : ℕ, Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiPrime d chi)
        0 n = Work.FIArea5.S16Hecke.heckeLam chi m n := by
    intro n
    rw [hm0]
    refine heckeLam_eq_of_primary_agree (fun z hz => ?_) n
    by_cases hzu : Work.FIArea5.S16Hecke.IsUnitMod4d d z
    · rw [Work.FIArea6Hecke.R.chiPrime_of_unit hzu, Work.FIArea4.primAssoc_eq_self hz]
    · rw [Work.FIArea6Hecke.R.chiPrime_of_not_unit hzu, hstrict z hzu]
  exact ⟨⟨hchar', h6⟩, hreal, hev⟩

end

end Work.FIArea6Hecke.R
