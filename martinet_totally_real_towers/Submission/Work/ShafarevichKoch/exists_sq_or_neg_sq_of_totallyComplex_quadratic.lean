import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ClassFieldTower.unitTwoRank_eq_one_of_imaginaryQuadratic

/-!
# Units of a totally complex quadratic field are `±` squares

Let `F` be a totally complex quadratic number field (an imaginary quadratic field) in which `-1`
is not a square (`hneg`), and let `u` be a unit of the ring of integers `𝓞 F`.  Then `u` is,
inside `Fˣ`, a square or the negative of a square.

The mathematical content is the classical description of the unit group of an imaginary quadratic
field: such a unit is a root of unity.  Concretely:

* every unit `u` of `𝓞 F` has `|N_{F/ℚ}(u)| = 1` (`NumberField.Units.norm`), and `F` has exactly
  one infinite place, of multiplicity `2` (`IsTotallyComplex`, `finrank ℚ F = 2`); the product
  formula `∏_w w x ^ mult w = |N x|` then forces `w x = 1` for that place, i.e. every complex
  conjugate of `u` has absolute value `1`;
* by Kronecker's theorem (`NumberField.Embeddings.pow_eq_one_of_norm_eq_one`) `u` is a root of
  unity, say of order `m`;
* `minpoly ℚ u = cyclotomic m ℚ` (`Polynomial.cyclotomic_eq_minpoly_rat`), so
  `m.totient = natDegree (minpoly ℚ u) ≤ finrank ℚ F = 2`; hence `m ∣ 12` (see
  `totient_le_two_dvd_twelve`);
* if `4 ∣ m` then a suitable power of `u` squares to `-1`, contradicting `hneg`; otherwise
  `m ∈ {1,2,3,6}` and the conclusion is immediate from `u ^ m = 1`.

The statement is the general form of `Work.ShafarevichKoch.Kc_unit_eq_or_eq_neg`, which treats the
case `F = ℚ(√-30030)` by explicit coordinates.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped nonZeroDivisors
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-! ## A small arithmetic lemma on Euler's totient -/

theorem totient_eight : Nat.totient 8 = 4 := by decide

theorem totient_nine : Nat.totient 9 = 6 := by decide

/-- **If `m.totient ≤ 2` then `m ∣ 12`.**  Equivalently, every `m` not dividing `12` has at least
three units in `ℤ/m`: either `m` has a prime factor `p ≥ 5` (and `p - 1 ≥ 4` divides `m.totient`),
or `8 ∣ m` (and `4 = φ 8` divides `m.totient`), or `9 ∣ m` (and `6 = φ 9` divides `m.totient`). -/
theorem totient_le_two_dvd_twelve {m : ℕ} (hm : 0 < m) (h : m.totient ≤ 2) : m ∣ 12 := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  -- `k ≥ 1`, so `p ^ k ∣ m` forces `p ∣ m`, hence `p - 1 = φ p ∣ m.totient ≤ 2`, so `p ≤ 3`.
  have hp2 : 2 ≤ p := hp.two_le
  have hpm : p ∣ m := by simpa using (pow_dvd_pow p hk).trans hpk
  have hle : p - 1 ≤ m.totient := by
    have hdvd : p.totient ∣ m.totient := Nat.totient_dvd_of_dvd hpm
    rw [Nat.totient_prime hp] at hdvd
    exact Nat.le_of_dvd (Nat.totient_pos.mpr hm) hdvd
  have hple : p ≤ 3 := by omega
  rcases (by omega : p = 2 ∨ p = 3) with rfl | rfl
  · rcases le_or_gt k 2 with hk2 | hk2
    · exact (pow_dvd_pow 2 hk2).trans (by norm_num)
    · exfalso
      have h8 : (8 : ℕ) ∣ m := by
        have h' : (2 : ℕ) ^ 3 ∣ (2 : ℕ) ^ k := pow_dvd_pow 2 (by omega)
        exact (by simpa using h' : (8 : ℕ) ∣ (2 : ℕ) ^ k).trans hpk
      have hdvd : (8 : ℕ).totient ∣ m.totient := Nat.totient_dvd_of_dvd h8
      rw [totient_eight] at hdvd
      have hle4 : 4 ≤ m.totient := Nat.le_of_dvd (Nat.totient_pos.mpr hm) hdvd
      omega
  · rcases le_or_gt k 1 with hk1 | hk1
    · exact (pow_dvd_pow 3 hk1).trans (by norm_num)
    · exfalso
      have h9 : (9 : ℕ) ∣ m := by
        have h' : (3 : ℕ) ^ 2 ∣ (3 : ℕ) ^ k := pow_dvd_pow 3 (by omega)
        exact (by simpa using h' : (9 : ℕ) ∣ (3 : ℕ) ^ k).trans hpk
      have hdvd : (9 : ℕ).totient ∣ m.totient := Nat.totient_dvd_of_dvd h9
      rw [totient_nine] at hdvd
      have hle6 : 6 ≤ m.totient := Nat.le_of_dvd (Nat.totient_pos.mpr hm) hdvd
      omega

/-! ## The unique infinite place -/

/-- **If a number field has exactly one infinite place then every element of norm `± 1` has all its
conjugates of absolute value `1`.**  The product formula `∏_w w x ^ mult w = |N x|` collapses to
`w x ^ 2 = 1`, and `w x ≥ 0` forces `w x = 1` for the unique place `w`. -/
theorem infinitePlace_apply_eq_one_of_card_eq_one {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] {x : K}
    (hcard : Fintype.card (NumberField.InfinitePlace K) = 1)
    (h : |(Algebra.norm ℚ) x| = 1) (w : NumberField.InfinitePlace K) : w x = 1 := by
  have hsub : ∀ w' : NumberField.InfinitePlace K, w' = w :=
    fun w' => Fintype.card_le_one_iff.mp (le_of_eq hcard) w' w
  have hprod := NumberField.InfinitePlace.prod_eq_abs_norm (K := K) x
  have hcollapse :
      ∏ w' : NumberField.InfinitePlace K, w' x ^ w'.mult = w x ^ (2 : ℕ) := by
    rw [show (2 : ℕ) = w.mult from (NumberField.IsTotallyComplex.mult_eq w).symm]
    calc ∏ w' : NumberField.InfinitePlace K, w' x ^ w'.mult
        = ∏ _w' : NumberField.InfinitePlace K, w x ^ w.mult :=
          Finset.prod_congr rfl (fun w' _ => by rw [hsub w'])
      _ = (w x ^ w.mult) ^ (Finset.univ : Finset (NumberField.InfinitePlace K)).card :=
          Finset.prod_const _
      _ = w x ^ w.mult := by rw [Finset.card_univ, hcard, pow_one]
  rw [hcollapse, h] at hprod
  have h1 : w x ^ (2 : ℕ) = 1 := by simpa using hprod
  have hpos : (0 : ℝ) ≤ w x := apply_nonneg _ _
  rcases sq_eq_one_iff.mp h1 with h1' | h1'
  · exact h1'
  · linarith

/-! ## From an element of `F` to a unit of `F` -/

/-- **A nonzero element of `F` which is a square up to sign becomes a unit of `Fˣ` which is a
square up to sign.** -/
theorem exists_units_sq_of_exists_sq {F : Type*} [Field F] (xu : Fˣ) (y : F) (hy : y ≠ 0)
    (h : (xu : F) = y ^ 2 ∨ (xu : F) = - y ^ 2) :
    ∃ z : Fˣ, xu = z ^ 2 ∨ xu = - z ^ 2 := by
  rcases h with h | h
  · refine ⟨Units.mk0 y hy, Or.inl ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact h
  · refine ⟨Units.mk0 y hy, Or.inr ?_⟩
    apply Units.ext
    rw [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mk0]
    exact h

/-! ## The main theorem -/

/-- **Every unit of `𝓞 F` is `±` a square in `Fˣ`**, for `F` a totally complex quadratic number
field in which `-1` is not a square. -/
theorem exists_sq_or_neg_sq_of_totallyComplex_quadratic (F : Type*) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] (h2 : Module.finrank ℚ F = 2)
    (hneg : ∀ y : F, y * y = -1 → False)
    (u : Work.ShafarevichKoch.RingUnit F) :
    ∃ y : Fˣ, Work.ShafarevichKoch.unitEmbed F u = y ^ 2 ∨
      Work.ShafarevichKoch.unitEmbed F u = -y ^ 2 := by
  -- `F` has a unique infinite place, of multiplicity `2`.
  have hnr : NumberField.InfinitePlace.nrComplexPlaces F = 1 := by
    have h := NumberField.IsTotallyComplex.finrank F
    rw [h2] at h
    omega
  have hcard : Fintype.card (NumberField.InfinitePlace F) = 1 := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hnr]
    simp
  -- the unit, viewed in `F`.
  set xu : Fˣ := Work.ShafarevichKoch.unitEmbed F u with hxu_def
  set x : F := (xu : F) with hx_def
  have hx0 : x ≠ 0 := by
    rw [hx_def]
    exact xu.ne_zero
  -- the norm of a unit is `± 1`.
  have hnorm : |(Algebra.norm ℚ) x| = 1 := NumberField.Units.norm F u
  -- hence all conjugates of `x` have absolute value `1`.
  have hw : ∀ w : NumberField.InfinitePlace F, w x = 1 :=
    infinitePlace_apply_eq_one_of_card_eq_one hcard hnorm
  have hemb : ∀ φ : F →+* ℂ, ‖φ x‖ = 1 :=
    (NumberField.InfinitePlace.eq_iff_eq x 1).mp hw
  -- `x` is integral, since it comes from `𝓞 F`.
  have hint : IsIntegral ℤ x :=
    (Algebra.IsIntegral.isIntegral (u : NumberField.RingOfIntegers F)).algebraMap
  -- Kronecker's theorem: `x` is a root of unity.
  obtain ⟨n, hnpos, hxnpow⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_eq_one F ℂ hint hemb
  -- its order.
  obtain ⟨m, hm_eq⟩ : ∃ m : ℕ, orderOf x = m := ⟨_, rfl⟩
  have hζ : IsPrimitiveRoot x m := hm_eq ▸ IsPrimitiveRoot.orderOf x
  have hm_pos : 0 < m := by
    rw [← hm_eq]
    exact Nat.pos_of_dvd_of_pos (orderOf_dvd_iff_pow_eq_one.mpr hxnpow) hnpos
  -- `m.totient = natDegree (minpoly ℚ x) ≤ finrank ℚ F = 2`.
  have hφ : m.totient ≤ 2 := by
    have hcyc : Polynomial.cyclotomic m ℚ = minpoly ℚ x :=
      Polynomial.cyclotomic_eq_minpoly_rat hζ hm_pos
    have hdeg : (minpoly ℚ x).natDegree = m.totient := by
      rw [← hcyc, Polynomial.natDegree_cyclotomic]
    have hle : (minpoly ℚ x).natDegree ≤ Module.finrank ℚ F := minpoly.natDegree_le x
    rw [hdeg, h2] at hle
    exact hle
  have hm12 : m ∣ 12 := totient_le_two_dvd_twelve hm_pos hφ
  have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 12 := by
    have hle : m ≤ 12 := Nat.le_of_dvd (by norm_num) hm12
    interval_cases m
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exfalso; norm_num at hm12
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exfalso; norm_num at hm12
    · exfalso; norm_num at hm12
    · exfalso; norm_num at hm12
    · exfalso; norm_num at hm12
    · exfalso; norm_num at hm12
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  -- reduce to a statement about the element `x` of `F`
  suffices key : ∃ y : F, y ≠ 0 ∧ (x = y ^ 2 ∨ x = - y ^ 2) by
    obtain ⟨y, hy, hyx⟩ := key
    exact exists_units_sq_of_exists_sq xu y hy (by simpa [hx_def] using hyx)
  rcases hm_cases with h1 | h2' | h3 | h4 | h6 | h12
  · -- `m = 1`: `x = 1`
    have hx1 : x = 1 := by
      have hp := hζ.pow_eq_one
      rw [h1, pow_one] at hp
      exact hp
    exact ⟨1, one_ne_zero, Or.inl (by rw [hx1, one_pow])⟩
  · -- `m = 2`: `x = -1`
    have hx2 : x = -1 := by
      have hp : x ^ 2 = 1 := by simpa [h2'] using hζ.pow_eq_one
      rcases sq_eq_one_iff.mp hp with hx | hx
      · exfalso
        have hdvd : m ∣ 1 := (hζ.pow_eq_one_iff_dvd 1).mp (by rw [pow_one, hx])
        have : m ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
        omega
      · exact hx
    exact ⟨1, one_ne_zero, Or.inr (by rw [hx2, one_pow])⟩
  · -- `m = 3`: `x ^ 3 = 1`, so `x = (x ^ 2) ^ 2`
    have hx3 : x ^ 3 = 1 := by simpa [h3] using hζ.pow_eq_one
    have hx4 : x ^ 4 = x := by
      rw [show x ^ 4 = x ^ 3 * x by ring, hx3, one_mul]
    refine ⟨x ^ 2, pow_ne_zero 2 hx0, Or.inl ?_⟩
    rw [show (x ^ 2) ^ 2 = x ^ 4 by rw [← pow_mul], hx4]
  · -- `m = 4`: `x ^ 2 = -1`, contradicting `hneg`
    have hx4 : x ^ 4 = 1 := by simpa [h4] using hζ.pow_eq_one
    have hx2 : x ^ 2 = -1 := by
      have hp : (x ^ 2) ^ 2 = 1 := by
        rw [show (x ^ 2) ^ 2 = x ^ 4 by rw [← pow_mul], hx4]
      rcases sq_eq_one_iff.mp hp with hx | hx
      · exfalso
        have hdvd : m ∣ 2 := (hζ.pow_eq_one_iff_dvd 2).mp hx
        have : m ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
        omega
      · exact hx
    exfalso
    exact hneg x (by simpa [pow_two] using hx2)
  · -- `m = 6`: `x ^ 3 = -1`, so `x = - (x ^ 2) ^ 2`
    have hx6 : x ^ 6 = 1 := by simpa [h6] using hζ.pow_eq_one
    have hx3 : x ^ 3 = -1 := by
      have hp : (x ^ 3) ^ 2 = 1 := by
        rw [show (x ^ 3) ^ 2 = x ^ 6 by rw [← pow_mul], hx6]
      rcases sq_eq_one_iff.mp hp with hx | hx
      · exfalso
        have hdvd : m ∣ 3 := (hζ.pow_eq_one_iff_dvd 3).mp hx
        have : m ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
        omega
      · exact hx
    have hx4 : x ^ 4 = -x := by
      rw [show x ^ 4 = x ^ 3 * x by ring, hx3, neg_one_mul]
    refine ⟨x ^ 2, pow_ne_zero 2 hx0, Or.inr ?_⟩
    rw [show (x ^ 2) ^ 2 = x ^ 4 by rw [← pow_mul], hx4, neg_neg]
  · -- `m = 12`: `x ^ 6 = -1`, so `x ^ 3` squares to `-1`, contradicting `hneg`
    have hx12 : x ^ 12 = 1 := by simpa [h12] using hζ.pow_eq_one
    have hx6 : x ^ 6 = -1 := by
      have hp : (x ^ 6) ^ 2 = 1 := by
        rw [show (x ^ 6) ^ 2 = x ^ 12 by rw [← pow_mul], hx12]
      rcases sq_eq_one_iff.mp hp with hx | hx
      · exfalso
        have hdvd : m ∣ 6 := (hζ.pow_eq_one_iff_dvd 6).mp hx
        have : m ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
        omega
      · exact hx
    exfalso
    exact hneg (x ^ 3) (by rw [← pow_two, ← pow_mul]; norm_num; exact hx6)

end Work.ShafarevichKoch

