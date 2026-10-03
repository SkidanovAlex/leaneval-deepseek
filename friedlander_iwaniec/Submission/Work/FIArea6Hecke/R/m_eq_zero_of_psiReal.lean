import Mathlib
import Submission.Work.FIArea6Hecke.R.rootOfUnityRatIsFourth
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs

namespace Work.FIArea6Hecke.R

/-! ## Auxiliary lemmas for `m_eq_zero_of_psiReal`

These three lemmas isolate the two purely algebraic steps of the proof and the one arithmetic
computation of `(1 + 4d·i)/(1 - 4d·i)`.

* `zpow_eq_one_natAbs_of_zpow_eq_one` — a solution of `a^m = 1` for an *integer* `m ≠ 0` is a root
  of unity in the sense of `a ^ m.natAbs = 1`, so that `rootOfUnityRatIsFourth` applies (its
  statement only accepts a positive *natural* exponent).
* `zpow_div_conj_eq_one_of_star_eq` — realness of `(Z/c)^m` with `c` real and nonzero and `Z ≠ 0`
  forces `(Z/Z̄)^m = 1`: `Z/Z̄ ∈ ℚ(i)` is where the integrality argument can be applied.
* `div_conj_one_add_4di_rat` — the real and imaginary parts of `(1+4d·i)/(1-4d·i)` are nonzero
  rationals (explicitly `(1-16d²)/(1+16d²)` and `8d/(1+16d²)`), so that number is *not* one of
  `1, -1, i, -i`.
-/

/-- An integer power `m ≠ 0` of `a` equal to `1` gives a (natural) positive power of `a` equal
to `1`: take `a ^ m.natAbs`. -/
lemma zpow_eq_one_natAbs_of_zpow_eq_one {a : ℂ} {m : ℤ} (h : a ^ m = 1) :
    a ^ m.natAbs = 1 := by
  by_cases hm : 0 ≤ m
  · have hmz : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm
    rw [← zpow_natCast, hmz]; exact h
  · have hm' : (0:ℤ) < -m := by omega
    have h2 : (m.natAbs : ℤ) = -m := by
      rw [← Int.natAbs_neg m, Int.natAbs_of_nonneg (le_of_lt hm')]
    rw [← zpow_natCast, h2, zpow_neg, h, inv_one]

/-- **Realness of `(Z/c)^m` forces `(Z/Z̄)^m = 1`** when `c` is a nonzero real number and `Z ≠ 0`.
Indeed `star ((Z/c)^m) = ((star Z)/c)^m` (as `star c = c`), and `Z/c = (Z/star Z)·((star Z)/c)`,
so the realness hypothesis reads `A = w^m · A` with `A = ((star Z)/c)^m ≠ 0`; cancelling `A`
leaves `w^m = 1` for `w = Z/star Z`. -/
lemma zpow_div_conj_eq_one_of_star_eq {Z c : ℂ} {m : ℤ} (hc : star c = c) (hc0 : c ≠ 0)
    (hZ : Z ≠ 0) (h : star ((Z / c) ^ m) = (Z / c) ^ m) : (Z / star Z) ^ m = 1 := by
  have hZr : star Z ≠ 0 := fun hh => hZ (by simpa using congrArg star hh)
  have h1 : ((star Z) / c) ^ m = (Z / c) ^ m := by
    simpa only [star_zpow₀, star_div₀, hc] using h
  have h2 : (Z / c) = (Z / star Z) * ((star Z) / c) := by field_simp
  have h3 : ((star Z) / c) ^ m ≠ 0 := zpow_ne_zero m (div_ne_zero hZr hc0)
  rw [h2, mul_zpow] at h1
  exact mul_right_cancel₀ h3 (by rw [one_mul]; exact h1.symm)

/-- **The real and imaginary parts of `(1 + 4d·i)/(1 - 4d·i)` are nonzero rationals** for `d ≥ 1`:
explicitly `(1 - (4d)²)/(1 + (4d)²)` and `2·(4d)/(1 + (4d)²)`.  The numerators are nonzero because
`4d ≥ 4 > 1` and `4d ≠ 0`, and the common denominator `1 + (4d)²` is positive. -/
lemma div_conj_one_add_4di_rat (d : ℕ) (hd : 1 ≤ d) :
    ∃ a b : ℚ,
      (((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I) /
        star ((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I)).re = (a:ℝ) ∧
      (((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I) /
        star ((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I)).im = (b:ℝ) ∧
      a ≠ 0 ∧ b ≠ 0 := by
  have hd1 : (1:ℚ) ≤ (d:ℚ) := by exact_mod_cast hd
  set Z : ℂ := (1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I with hZ
  have h1 : Z.re = 1 := by simp [hZ]
  have h2 : Z.im = (4*(d:ℝ)) := by simp [hZ]
  have h3 : Complex.normSq (star Z) = 1 + (4*(d:ℝ))^2 := by
    simp [Complex.normSq_apply, h1, h2]
    ring
  have hre : (Z / star Z).re = (1 - (4*(d:ℝ))^2)/(1 + (4*(d:ℝ))^2) := by
    rw [Complex.div_re, h3]
    simp [h1, h2]
    ring
  have him : (Z / star Z).im = (2*(4*(d:ℝ)))/(1 + (4*(d:ℝ))^2) := by
    rw [Complex.div_im, h3]
    simp [h1, h2]
    ring
  refine ⟨(1 - (4*(d:ℚ))^2)/(1 + (4*(d:ℚ))^2), (2*(4*(d:ℚ)))/(1 + (4*(d:ℚ))^2),
    ?_, ?_, ?_, ?_⟩
  · rw [hre]; push_cast; ring
  · rw [him]; push_cast; ring
  · apply div_ne_zero
    · intro hh
      have hr : (4*(d:ℚ))^2 = 1 := by linarith
      rcases sq_eq_one_iff.mp hr with h' | h' <;> linarith
    · positivity
  · apply div_ne_zero
    · linarith
    · positivity

/-- **`PsiReal` forces `m = 0`.**  For a strict character `χ` mod `4d` (`d ≥ 1`), realness of
`ψ_m = χ·(·/|·|)^m` forces `m = 0`.

Proof sketch: for `m = 0` there is nothing to prove; assume `m ≠ 0` and put `z = 1 + 4d·i`.  Since
`4d ∣ z - 1`, periodicity gives `χ z = χ 1 = 1`, hence `psi chi m z = (z/|z|)^m`.  Realness
(`PsiReal χ m`) and `star (z/|z|) = z̄/|z|` give `(z/z̄)^m = 1`, so `w := z/z̄ ∈ ℚ(i)` is a root of
unity, hence `w ∈ {1,-1,i,-i}` by `rootOfUnityRatIsFourth`.  But
`w = (1+4d·i)/(1-4d·i) = ((1-16d²) + 8d·i)/(1+16d²)` has both real and imaginary part nonzero for
`d ≥ 1` (`16d² ≥ 16 > 1` and `8d ≠ 0`), so it is none of `1,-1,i,-i`; contradiction. -/
theorem m_eq_zero_of_psiReal {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) {m : ℤ}
    (h : Work.FIArea6Hecke.R.PsiReal chi m) : m = 0 := by
  by_contra hm0
  obtain ⟨hchar, _⟩ := hchi
  obtain ⟨h1, _, _, hper, _⟩ := hchar
  -- the test point `z = 1 + 4d·i`, which is `≡ 1` modulo `4d`
  set z : GaussianInt := ⟨1, ((4*d:ℕ):ℤ)⟩ with hz
  have hdiv : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (z - 1) := by
    rw [hz, Zsqrtd.intCast_dvd]
    exact ⟨dvd_zero _, by simpa using dvd_refl ((4 * d : ℕ) : ℤ)⟩
  have hchiz : chi z = 1 := (hper z 1 hdiv).trans h1
  have hZval : z.toComplex = (1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I := by
    rw [hz, GaussianInt.toComplex_def']
    push_cast
    ring
  have hpsi : Work.FIArea5.S16Hecke.psi chi m z =
      (z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ m := by
    rw [Work.FIArea5.S16Hecke.psi, hchiz, one_mul]
  have hc : star ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ) =
      ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ) := by simp
  have hZ0 : z.toComplex ≠ 0 := by
    rw [hZval]
    intro hh
    have := congrArg Complex.re hh
    simp at this
  have hc0 : ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    intro hh
    have h2 : ‖z.toComplex‖ = 0 := by
      rw [Work.FIArea5.S16Hecke.norm_toComplex, hh]
    exact hZ0 (norm_eq_zero.mp h2)
  have hreal : star ((z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ m) =
      (z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ m := by
    have h' := h z
    rwa [hpsi] at h'
  -- `(z/z̄)^m = 1`
  have hw1 : (z.toComplex / star z.toComplex) ^ m = 1 :=
    zpow_div_conj_eq_one_of_star_eq hc hc0 hZ0 hreal
  have hn : 0 < m.natAbs := Int.natAbs_pos.mpr hm0
  have hwn : (z.toComplex / star z.toComplex) ^ m.natAbs = 1 :=
    zpow_eq_one_natAbs_of_zpow_eq_one hw1
  have hw : z.toComplex / star z.toComplex =
      ((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I) /
        star ((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I) := by
    rw [hZval]
  rw [hw] at hwn
  -- `z/z̄` is a root of unity with rational coordinates, hence one of `1, -1, i, -i`
  obtain ⟨a, b, hre, him, ha0, hb0⟩ := div_conj_one_add_4di_rat d hd
  rcases rootOfUnityRatIsFourth
      (((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I) /
        star ((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I))
      a b hre him m.natAbs hn hwn with h' | h' | h' | h'
  · exact hb0 (by
      have hzero : (b:ℝ) = 0 := by rw [← him, h']; simp
      exact_mod_cast hzero)
  · exact hb0 (by
      have hzero : (b:ℝ) = 0 := by rw [← him, h']; simp
      exact_mod_cast hzero)
  · exact ha0 (by
      have hzero : (a:ℝ) = 0 := by rw [← hre, h']; simp
      exact_mod_cast hzero)
  · exact ha0 (by
      have hzero : (a:ℝ) = 0 := by rw [← hre, h']; simp
      exact_mod_cast hzero)

end Work.FIArea6Hecke.R
