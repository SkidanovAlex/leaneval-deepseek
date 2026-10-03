/-
# `Work.FIArea5.S16Hecke.twistAux`

Auxiliary arithmetic for the twisting character `twist χ m = χ · twistChar χ m` of
`(ℤ[i]/4d)∗`:

* `primaryUnit` is the unique unit `u ∈ μ₄` congruent to an *odd* `z` modulo `(1+i)³`
  (`primaryUnit_spec`), it is multiplicative on odd elements (`primaryUnit_mul`) and depends only on
  the class modulo `(1+i)³` (`primaryUnit_eq_of_dvd_sub`), in particular modulo `4d`;
* hence `twistChar χ m` and `twist χ m` are characters modulo `4d` (`twist_isCharMod4dStrict`).
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.h1166TwistDefs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.GaussBasic
import Submission.Work.FIArea5.S16Hecke.GaussFourier
import Submission.Work.FIArea5.S16Hecke.GaussChi
import Submission.Work.FIArea5.S16Hecke.thetaHol_twist_eq
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Work.FIArea5.S16Hecke.isPrimary_iff_coset
import Submission.Work.FIArea5.S16Hecke.primaryWeightDefs
import Submission.Commons.NumberTheory.GaussianInt.units_classification
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

lemma c3_eq : c3 = (⟨-2, 2⟩ : GaussianInt) := by decide

lemma gnorm_c3 : gnorm c3 = 8 := by rw [c3_eq]; decide

lemma oneAddI_dvd_c3 : oneAddI ∣ c3 :=
  ⟨(1 + (⟨0,1⟩ : GaussianInt))^2, by rw [c3, oneAddI, pow_succ']⟩

lemma mem_units4_iff {u : GaussianInt} :
    u ∈ units4 ↔ u = 1 ∨ u = -1 ∨ u = (⟨0,1⟩ : GaussianInt) ∨ u = (⟨0,-1⟩ : GaussianInt) := by
  simp [units4]

lemma one_mem_units4 : (1 : GaussianInt) ∈ units4 := by
  rw [mem_units4_iff]; exact Or.inl rfl
lemma neg_one_mem_units4 : (-1 : GaussianInt) ∈ units4 := by
  rw [mem_units4_iff]; exact Or.inr (Or.inl rfl)
lemma I_mem_units4 : (⟨0,1⟩ : GaussianInt) ∈ units4 := by
  rw [mem_units4_iff]; exact Or.inr (Or.inr (Or.inl rfl))
lemma negI_mem_units4 : (⟨0,-1⟩ : GaussianInt) ∈ units4 := by
  rw [mem_units4_iff]; exact Or.inr (Or.inr (Or.inr rfl))

lemma isOddG_of_mem_units4 {u : GaussianInt} (hu : u ∈ units4) : isOddG u := by
  rw [GaussBasic.isOddG_iff_odd]
  rw [mem_units4_iff] at hu
  rcases hu with h | h | h | h <;> (rw [h]; decide)

lemma gnorm_of_mem_units4 {u : GaussianInt} (hu : u ∈ units4) : gnorm u = 1 := by
  rw [mem_units4_iff] at hu
  rcases hu with h | h | h | h <;> (rw [h]; decide)

lemma isUnit_of_mem_units4 {u : GaussianInt} (hu : u ∈ units4) : IsUnit u :=
  (Commons.NumberTheory.GaussianInt.units_classification u).mpr (by
    rw [mem_units4_iff] at hu
    rcases hu with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h)))

/-! ## `primaryUnit` -/

lemma c3_dvd_gnorm {w : GaussianInt} (h : c3 ∣ w) : 8 ∣ gnorm w := by
  obtain ⟨t, rfl⟩ := h; rw [gnorm_mul, gnorm_c3]; exact dvd_mul_right _ _

lemma gnorm_sub_mem_units4 {u v : GaussianInt} (hu : u ∈ units4) (hv : v ∈ units4)
    (h : u ≠ v) : gnorm (u - v) = 2 ∨ gnorm (u - v) = 4 := by
  rw [mem_units4_iff] at hu hv
  rcases hu with rfl|rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl|rfl <;>
    first | (exfalso; exact h rfl) | (decide)

lemma unit_sub_unit_not_dvd {u v : GaussianInt} (hu : u ∈ units4) (hv : v ∈ units4)
    (h : u ≠ v) : ¬ (c3 ∣ u - v) := by
  intro hd
  have hg := c3_dvd_gnorm hd
  rcases gnorm_sub_mem_units4 hu hv h with hh | hh <;> rw [hh] at hg <;> norm_num at hg

lemma mul_mem_units4 {u v : GaussianInt} (hu : u ∈ units4) (hv : v ∈ units4) :
    u * v ∈ units4 := by
  rw [mem_units4_iff] at hu hv ⊢
  rcases hu with rfl|rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl|rfl <;> decide

/-- The unit `u ∈ μ₄` congruent to `z` mod `(1+i)³` is detected by the defining case distinction:
`primaryUnit z = u` whenever `u ∈ μ₄` and `(1+i)³ ∣ z - u`. -/
lemma primaryUnit_eq_of_dvd {z u : GaussianInt} (hu : u ∈ units4) (h : c3 ∣ z - u) :
    primaryUnit z = u := by
  rw [primaryUnit]
  split_ifs with h1 h2 h3 h4
  · by_contra hne
    have hd : c3 ∣ (1 : GaussianInt) - u := by convert dvd_sub h h1 using 1 <;> (ext <;> simp <;> ring)
    exact unit_sub_unit_not_dvd one_mem_units4 hu hne hd
  · by_contra hne
    have hd : c3 ∣ u - (-1 : GaussianInt) := by convert dvd_sub h2 h using 1 <;> (ext <;> simp <;> ring)
    exact unit_sub_unit_not_dvd hu neg_one_mem_units4 (fun hh => hne hh.symm) hd
  · by_contra hne
    have hd : c3 ∣ u - (⟨0,1⟩ : GaussianInt) := by convert dvd_sub h3 h using 1 <;> (ext <;> simp <;> ring)
    exact unit_sub_unit_not_dvd hu I_mem_units4 (fun hh => hne hh.symm) hd
  · by_contra hne
    have hd : c3 ∣ u - (⟨0,-1⟩ : GaussianInt) := by convert dvd_sub h4 h using 1 <;> (ext <;> simp <;> ring)
    exact unit_sub_unit_not_dvd hu negI_mem_units4 (fun hh => hne hh.symm) hd
  · rw [mem_units4_iff] at hu
    rcases hu with hu|hu|hu|hu
    · rw [hu] at h; exact absurd h h1
    · rw [hu, sub_neg_eq_add] at h; exact absurd h h2
    · rw [hu] at h; exact absurd h h3
    · rw [hu, show (⟨0,-1⟩:GaussianInt) = -(⟨0,1⟩) from by decide, sub_neg_eq_add] at h
      exact absurd h h4

lemma isOddG_of_oneAddI_dvd_sub {z u : GaussianInt} (hu : isOddG u) (h : oneAddI ∣ z - u) :
    isOddG z := by
  intro hz
  have h1 : oneAddI ∣ u := by
    have := dvd_sub hz h
    rwa [sub_sub_self] at this
  exact hu h1

lemma isOddG_of_oneAddI_dvd_add {z u : GaussianInt} (hu : isOddG u) (h : oneAddI ∣ z + u) :
    isOddG z := by
  intro hz
  have h1 : oneAddI ∣ u := by
    have := dvd_sub h hz
    rwa [add_sub_cancel_left] at this
  exact hu h1

lemma isOddG_iff_of_oneAddI_dvd_sub {z w : GaussianInt} (h : oneAddI ∣ z - w) :
    isOddG z ↔ isOddG w := by
  constructor
  · intro hz hw
    have h1 : oneAddI ∣ z := by have := dvd_add h hw; rwa [sub_add_cancel] at this
    exact hz h1
  · intro hw hz
    have h1 : oneAddI ∣ w := by have := dvd_sub hz h; rwa [sub_sub_self] at this
    exact hw h1

lemma primaryUnit_eq_zero_of_not_odd {z : GaussianInt} (hz : ¬ isOddG z) : primaryUnit z = 0 := by
  rw [primaryUnit]
  rw [if_neg (fun h => hz (isOddG_of_oneAddI_dvd_sub (isOddG_of_mem_units4 one_mem_units4)
          (dvd_trans oneAddI_dvd_c3 h))),
      if_neg (fun h => hz (isOddG_of_oneAddI_dvd_add (isOddG_of_mem_units4 one_mem_units4)
          (dvd_trans oneAddI_dvd_c3 h))),
      if_neg (fun h => hz (isOddG_of_oneAddI_dvd_sub (isOddG_of_mem_units4 I_mem_units4)
          (dvd_trans oneAddI_dvd_c3 h))),
      if_neg (fun h => hz (isOddG_of_oneAddI_dvd_add (isOddG_of_mem_units4 I_mem_units4)
          (dvd_trans oneAddI_dvd_c3 h)))]

lemma odd_gnorm_iff (z : GaussianInt) : Odd (gnorm z) ↔ Odd (z.re + z.im) := by
  show Odd (z.norm.natAbs) ↔ _
  rw [Int.natAbs_odd, Zsqrtd.norm_def]
  rw [show z.re * z.re - -1 * z.im * z.im = z.re^2 + z.im^2 by ring]
  have ha : Even (z.re^2 - z.re) := by
    obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Int.even_or_odd z.re
    · exact ⟨2*k^2 - k, by rw [hk]; ring⟩
    · exact ⟨2*k^2 + k, by rw [hk]; ring⟩
  have hb : Even (z.im^2 - z.im) := by
    obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Int.even_or_odd z.im
    · exact ⟨2*k^2 - k, by rw [hk]; ring⟩
    · exact ⟨2*k^2 + k, by rw [hk]; ring⟩
  have hd : Even ((z.re^2+z.im^2) - (z.re+z.im)) := by
    obtain ⟨p,hp⟩ := ha; obtain ⟨q,hq⟩ := hb
    refine ⟨p+q, ?_⟩
    have h1 : z.re^2+z.im^2-(z.re+z.im) = (z.re^2-z.re)+(z.im^2-z.im) := by ring
    rw [h1, hp, hq]; ring
  have h : z.re^2 + z.im^2 = (z.re+z.im) + ((z.re^2+z.im^2) - (z.re+z.im)) := by ring
  conv_lhs => rw [h]
  rw [Int.odd_add, iff_true_intro hd]
  simp

lemma isOddG_gnorm_odd (z : GaussianInt) (hz : isOddG z) : Odd (gnorm z) :=
  (odd_gnorm_iff z).mpr ((GaussBasic.isOddG_iff_odd z).mp hz)

/-- Every odd `z` is `a · p` with `a ∈ μ₄` and `p` primary. -/
lemma exists_unit_primary (z : GaussianInt) (hz : isOddG z) :
    ∃ a ∈ units4, ∃ p : GaussianInt, IsPrimary p ∧ z = a * p := by
  have hodd : Odd z.norm.natAbs := isOddG_gnorm_odd z hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [Zsqrtd.norm_def, Zsqrtd.re_zero, Zsqrtd.im_zero, mul_zero, sub_zero,
      Int.natAbs_zero] at hodd
    exact Nat.not_odd_zero hodd
  obtain ⟨w, hwP, -⟩ :=
    Commons.NumberTheory.GaussianInt.primary_associate_exists_unique hz0 hodd
  obtain ⟨ε, hε⟩ := hwP.1
  refine ⟨(↑ε : GaussianInt), ?_, w, ⟨hwP.2.1, hwP.2.2.1, ?_⟩, ?_⟩
  · rw [mem_units4_iff]
    rcases (Commons.NumberTheory.GaussianInt.units_classification (↑ε : GaussianInt)).mp
      (Units.isUnit ε) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · exact (ZMod.intCast_eq_intCast_iff w.im (w.re - 1) 4).mp (by push_cast; exact hwP.2.2.2)
  · rw [mul_comm]
    exact hε.symm

/-- **`primaryUnit z` for odd `z`**: it lies in `μ₄` and is congruent to `z` mod `(1+i)³`. -/
lemma primaryUnit_spec {z : GaussianInt} (hz : isOddG z) :
    primaryUnit z ∈ units4 ∧ c3 ∣ z - primaryUnit z := by
  obtain ⟨a, ha, p, hp, hzp⟩ := exists_unit_primary z hz
  have hpd : c3 ∣ p - 1 := c3_dvd_sub_one_of_isPrimary hp
  have hza : c3 ∣ z - a := by
    obtain ⟨t, ht⟩ := hpd
    refine ⟨a * t, ?_⟩
    rw [hzp]
    calc a * p - a = a * (p - 1) := by ring
      _ = a * (c3 * t) := by rw [ht]
      _ = c3 * (a * t) := by ring
  have hpu : primaryUnit z = a := primaryUnit_eq_of_dvd ha hza
  exact ⟨hpu ▸ ha, hpu ▸ hza⟩

lemma primaryUnit_one : primaryUnit (1 : GaussianInt) = 1 :=
  primaryUnit_of_isPrimary isPrimary_one

/-- **Multiplicativity of `primaryUnit` on odd elements.** -/
lemma primaryUnit_mul {z w : GaussianInt} (hz : isOddG z) (hw : isOddG w) :
    primaryUnit (z * w) = primaryUnit z * primaryUnit w := by
  obtain ⟨hu1, hd1⟩ := primaryUnit_spec hz
  obtain ⟨hu2, hd2⟩ := primaryUnit_spec hw
  have hd : c3 ∣ z * w - primaryUnit z * primaryUnit w := by
    have h1 : c3 ∣ (z - primaryUnit z) * w := dvd_mul_of_dvd_left hd1 w
    have h2 : c3 ∣ primaryUnit z * (w - primaryUnit w) := dvd_mul_of_dvd_right hd2 _
    have h := dvd_add h1 h2
    convert h using 1
    ring
  exact primaryUnit_eq_of_dvd (mul_mem_units4 hu1 hu2) hd

/-- **`primaryUnit` only depends on the class modulo `(1+i)³`.** -/
lemma primaryUnit_eq_of_dvd_sub {z w : GaussianInt} (h : c3 ∣ z - w) :
    primaryUnit z = primaryUnit w := by
  have hI : oneAddI ∣ z - w := dvd_trans oneAddI_dvd_c3 h
  by_cases hz : isOddG z
  · have hw : isOddG w := (isOddG_iff_of_oneAddI_dvd_sub hI).mp hz
    obtain ⟨hu, hd⟩ := primaryUnit_spec hz
    have hdw : c3 ∣ w - primaryUnit z := by
      have := dvd_sub hd h
      convert this using 1 <;> (ext <;> simp <;> ring)
    exact (primaryUnit_eq_of_dvd hu hdw).symm
  · have hw : ¬ isOddG w := fun hh => hz ((isOddG_iff_of_oneAddI_dvd_sub hI).mpr hh)
    rw [primaryUnit_eq_zero_of_not_odd hz, primaryUnit_eq_zero_of_not_odd hw]

/-- `(1+i)³ ∣ 4d`. -/
lemma c3_dvd_four_mul (d : ℕ) : c3 ∣ (((4 * d : ℕ) : ℤ) : GaussianInt) := by
  rw [c3]; exact oneAddI_pow_three_dvd_four_mul d

/-- **`primaryUnit` depends only on the class modulo `4d`.** -/
lemma primaryUnit_periodic {d : ℕ} {z w : GaussianInt}
    (h : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ z - w) : primaryUnit z = primaryUnit w :=
  primaryUnit_eq_of_dvd_sub (dvd_trans (c3_dvd_four_mul d) h)

/-! ## The twist is a character modulo `4d` -/

lemma twistChar_mul (chi : GaussianInt → ℂ) (m : ℕ) (z w : GaussianInt) :
    twistChar chi m (z * w) = twistChar chi m z * twistChar chi m w := by
  rw [twistChar, twistChar, twistChar]
  by_cases hz : isOddG z
  · by_cases hw : isOddG w
    · rw [if_pos ((GaussBasic.isOddG_mul z w).mpr ⟨hz, hw⟩), if_pos hz, if_pos hw,
        primaryUnit_mul hz hw, GaussianInt.toComplex_mul, mul_zpow]
    · rw [if_neg (fun h => hw ((GaussBasic.isOddG_mul z w).mp h).2), if_pos hz, if_neg hw,
        mul_zero]
  · rw [if_neg (fun h => hz ((GaussBasic.isOddG_mul z w).mp h).1), if_neg hz, zero_mul]

lemma norm_twistChar_le_one (chi : GaussianInt → ℂ) (m : ℕ) (z : GaussianInt) :
    ‖twistChar chi m z‖ ≤ 1 := by
  rw [twistChar]
  by_cases h : isOddG z
  · rw [if_pos h, norm_zpow]
    have hu := (primaryUnit_spec h).1
    have h1 : ‖(((primaryUnit z) : GaussianInt).toComplex)‖ = 1 := by
      rw [norm_toComplex, gnorm_of_mem_units4 hu, Nat.cast_one, Real.sqrt_one]
    rw [h1, one_zpow]
  · rw [if_neg h]; norm_num

lemma twistChar_periodic {d : ℕ} (chi : GaussianInt → ℂ) (m : ℕ) {z w : GaussianInt}
    (h : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ z - w) : twistChar chi m z = twistChar chi m w := by
  rw [twistChar, twistChar]
  have hc3 : c3 ∣ z - w := dvd_trans (c3_dvd_four_mul d) h
  have hI : oneAddI ∣ z - w := dvd_trans oneAddI_dvd_c3 hc3
  have hodd : isOddG z ↔ isOddG w := isOddG_iff_of_oneAddI_dvd_sub hI
  by_cases hz : isOddG z
  · rw [if_pos hz, if_pos (hodd.mp hz), primaryUnit_eq_of_dvd_sub hc3]
  · rw [if_neg hz, if_neg (fun hh => hz (hodd.mpr hh))]

lemma twist_one (chi : GaussianInt → ℂ) (m : ℕ) (h1 : chi 1 = 1) : twist chi m 1 = 1 := by
  rw [twist, h1, twistChar, if_pos GaussBasic.isOddG_one, primaryUnit_one, GaussianInt.toComplex_one,
    one_zpow, one_mul]

lemma twist_mul (chi : GaussianInt → ℂ) (m : ℕ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (z w : GaussianInt) :
    twist chi m (z * w) = twist chi m z * twist chi m w := by
  rw [twist, twist, twist, hmul, twistChar_mul]
  ring

lemma norm_twist_le_one (chi : GaussianInt → ℂ) (m : ℕ) (hn : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (z : GaussianInt) : ‖twist chi m z‖ ≤ 1 := by
  rw [twist, norm_mul]
  calc ‖chi z‖ * ‖twistChar chi m z‖ ≤ 1 * 1 :=
        mul_le_mul (hn z) (norm_twistChar_le_one chi m z) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma twist_periodic {d : ℕ} (chi : GaussianInt → ℂ) (m : ℕ)
    (hper : ∀ z w : GaussianInt, (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (z - w) → chi z = chi w)
    {z w : GaussianInt} (h : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ z - w) :
    twist chi m z = twist chi m w := by
  rw [twist, twist, hper z w h, twistChar_periodic chi m h]

lemma twist_eq_zero_of_dvd {d : ℕ} (chi : GaussianInt → ℂ) (m : ℕ)
    (hz : ∀ z : GaussianInt, (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ z → chi z = 0) {z : GaussianInt}
    (h : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ z) : twist chi m z = 0 := by
  rw [twist, hz z h, zero_mul]

lemma twist_eq_zero_of_not_unit {d : ℕ} (chi : GaussianInt → ℂ) (m : ℕ)
    (hoff : ∀ z : GaussianInt, ¬ IsUnitMod4d d z → chi z = 0) {z : GaussianInt}
    (h : ¬ IsUnitMod4d d z) : twist chi m z = 0 := by
  rw [twist, hoff z h, zero_mul]

/-- **The twist of a character modulo `4d` is a character modulo `4d`.** -/
theorem twist_isCharMod4dStrict (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (hchi : IsCharMod4dStrict d chi) : IsCharMod4dStrict d (twist chi m) := by
  obtain ⟨hc, hoff⟩ := hchi
  obtain ⟨hc1, hcmul, hcnorm, hcper, hczero⟩ := hc
  exact ⟨⟨twist_one chi m hc1, twist_mul chi m hcmul,
      fun z => norm_twist_le_one chi m hcnorm z,
      fun z w h => twist_periodic chi m hcper h,
      fun z h => twist_eq_zero_of_dvd chi m hczero h⟩,
    fun z h => twist_eq_zero_of_not_unit chi m hoff h⟩

end

end Work.FIArea5.S16Hecke
