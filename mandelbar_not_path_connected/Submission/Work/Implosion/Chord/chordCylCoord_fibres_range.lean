import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Geometry
import Submission.Work.Implosion.Chord
import Submission.Work.Implosion.Chord.chordHeight_bij

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cylinder coordinate `chordCylCoord` is a parametrisation of `ℂ*`

`chordCylCoord lam t s = exp (2πi (s + i·chordHeight lam t))` is the exponential of the
"phase + i·height" coordinate of the fundamental domain (see `Work.Implosion.Chord`).
Writing `h(t) = chordHeight lam t`, its exponent splits as

  `2πi (s + i h(t)) = 2πs·I − 2πh(t)`,

so `chordCylCoord lam t s = exp (2πs·I) · exp (−2πh(t))`; the second factor is a positive
real number, the first is a point of `S¹`.  Consequently `(t,s) ↦ chordCylCoord lam t s`:

* is `1`-periodic in `s` (`chordCylCoord lam t 1 = chordCylCoord lam t 0`);
* is injective on `(−1,1) × [0,1)`;
* is surjective onto `ℂ*`,

which is exactly the statement that the fundamental domain modulo the boundary
identification is the cylinder `(ℝ/ℤ) × ℝ ≅ ℂ*`, with `s ∈ [0,1)` the phase and
`chordHeight` the height coordinate.
-/

namespace Work.Implosion.Chord

open Complex

/-- The exponent of `chordCylCoord`, with real and imaginary parts separated:
`2πi (s + i·chordHeight lam t) = 2πs·I − 2π·chordHeight lam t`. -/
private noncomputable def cylExp (lam t s : ℝ) : ℂ :=
  ((2 * Real.pi * s : ℝ) : ℂ) * I - ((2 * Real.pi * chordHeight lam t : ℝ) : ℂ)

private lemma chordCylCoord_eq_exp (lam t s : ℝ) :
    chordCylCoord lam t s = Complex.exp (cylExp lam t s) := by
  rw [chordCylCoord, cylExp]; congr 1; push_cast; ring_nf
  rw [sq, Complex.I_mul_I]; ring

private lemma cylExp_re (lam t s : ℝ) :
    (cylExp lam t s).re = -(2 * Real.pi * chordHeight lam t) := by
  simp [cylExp]

private lemma cylExp_im (lam t s : ℝ) :
    (cylExp lam t s).im = 2 * Real.pi * s := by
  simp [cylExp]

private lemma expm_re (n : ℤ) :
    ((n : ℂ) * (2 * (Real.pi : ℂ) * I)).re = 0 := by
  simp [Complex.mul_re]

private lemma expm_im (n : ℤ) :
    ((n : ℂ) * (2 * (Real.pi : ℂ) * I)).im = (n : ℝ) * (2 * Real.pi) := by
  simp [Complex.mul_im]

private lemma two_pi_mul_div (x : ℝ) : (2 * Real.pi) * (x / (2 * Real.pi)) = x := by
  rw [mul_comm, div_mul_cancel₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]

private lemma two_pi_ne_zero : (2 * Real.pi : ℝ) ≠ 0 := by positivity

/-- `s` enters only through `exp (2πs·I)`, which is `1`-periodic. -/
private lemma cylExp_one (lam t : ℝ) :
    cylExp lam t 1 = cylExp lam t 0 + (2 * (Real.pi : ℂ) * I) := by
  rw [cylExp, cylExp]; push_cast; ring

private lemma chordCylCoord_one_eq_zero (lam t : ℝ) :
    chordCylCoord lam t 1 = chordCylCoord lam t 0 := by
  rw [chordCylCoord_eq_exp, chordCylCoord_eq_exp, cylExp_one, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

/-- Injectivity of the cylinder coordinate on `(−1,1) × [0,1)`: equality forces both the
height `chordHeight lam t` (hence `t`) and the phase `s ∈ [0,1)` to agree. -/
private lemma chordCylCoord_eq_iff (lam : ℝ) (hlam : 0 < lam) {t t' s s' : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (ht' : t' ∈ Set.Ioo (-1 : ℝ) 1)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hs' : s' ∈ Set.Ico (0 : ℝ) 1) :
    (chordCylCoord lam t s = chordCylCoord lam t' s' ↔ t = t' ∧ s = s') := by
  constructor
  · intro heq
    rw [chordCylCoord_eq_exp, chordCylCoord_eq_exp] at heq
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
    have hH : chordHeight lam t = chordHeight lam t' := by
      have hre := congrArg Complex.re hn
      simp only [cylExp_re, Complex.add_re, expm_re, add_zero] at hre
      exact mul_left_cancel₀ two_pi_ne_zero (neg_inj.mp hre)
    have htt : t = t' := (chordHeight_bij lam hlam).1.injOn ht ht' hH
    have hss : s = s' := by
      have him := congrArg Complex.im hn
      simp only [cylExp_im, Complex.add_im, expm_im] at him
      have hs_eq : s - s' = (n : ℝ) := by
        have h : (2 * Real.pi) * (s - s') = (2 * Real.pi) * (n : ℝ) := by
          rw [mul_sub, him]; ring
        exact mul_left_cancel₀ two_pi_ne_zero h
      have h_lt : (n : ℝ) < 1 := by linarith [hs_eq, hs.2, hs'.1]
      have h_gt : (-1 : ℝ) < (n : ℝ) := by linarith [hs_eq, hs.1, hs'.2]
      have hn1 : n < 1 := by exact_mod_cast h_lt
      have hn2 : (-1 : ℤ) < n := by exact_mod_cast h_gt
      have hn0 : n = 0 := by omega
      have : (n : ℝ) = 0 := by rw [hn0]; norm_num
      linarith
    exact ⟨htt, hss⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Surjectivity onto `ℂ*`: the real part of the exponent is an arbitrary real number,
realised as `−2π·chordHeight lam t` by surjectivity of the height, and the imaginary part
is adjusted to a phase `s ∈ [0,1)` via `Int.fract`. -/
private lemma chordCylCoord_surj (lam : ℝ) (hlam : 0 < lam) (z : ℂ) (hz : z ≠ 0) :
    ∃ t ∈ Set.Ioo (-1 : ℝ) 1, ∃ s ∈ Set.Ico (0 : ℝ) 1, chordCylCoord lam t s = z := by
  have hsurj : ∀ y : ℝ, ∃ t ∈ Set.Ioo (-1 : ℝ) 1, chordHeight lam t = y :=
    fun y => (chordHeight_bij lam hlam).2 (Set.mem_univ y)
  set w : ℂ := Complex.log z with hwdef
  have hw : Complex.exp w = z := by rw [hwdef]; exact Complex.exp_log hz
  obtain ⟨t, ht, htval⟩ := hsurj (-w.re / (2 * Real.pi))
  refine ⟨t, ht, Int.fract (w.im / (2 * Real.pi)),
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
  have key : cylExp lam t (Int.fract (w.im / (2 * Real.pi)))
      = w + ((-⌊w.im / (2 * Real.pi)⌋ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    have hsval : Int.fract (w.im / (2 * Real.pi))
        = w.im / (2 * Real.pi) - (⌊w.im / (2 * Real.pi)⌋ : ℝ) := by
      have := Int.self_sub_fract (w.im / (2 * Real.pi))
      linarith
    have hncast : (((-⌊w.im / (2 * Real.pi)⌋ : ℤ)) : ℝ)
        = -(⌊w.im / (2 * Real.pi)⌋ : ℝ) := by push_cast; ring
    apply Complex.ext
    · rw [cylExp_re, htval, Complex.add_re, expm_re, add_zero]
      rw [neg_div, mul_neg, neg_neg]
      exact two_pi_mul_div w.re
    · rw [cylExp_im, Complex.add_im, expm_im, hsval, hncast]
      rw [mul_sub, two_pi_mul_div]
      ring
  rw [chordCylCoord_eq_exp, key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    mul_one, hw]

theorem chordCylCoord_fibres_range (lam : ℝ) (hlam : 0 < lam) :
    (∀ t : ℝ, chordCylCoord lam t 1 = chordCylCoord lam t 0)
      ∧ (∀ t t' s s' : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 → t' ∈ Set.Ioo (-1 : ℝ) 1 →
          s ∈ Set.Ico (0 : ℝ) 1 → s' ∈ Set.Ico (0 : ℝ) 1 →
          (chordCylCoord lam t s = chordCylCoord lam t' s' ↔ t = t' ∧ s = s'))
      ∧ (∀ z : ℂ, z ≠ 0 → ∃ t ∈ Set.Ioo (-1 : ℝ) 1, ∃ s ∈ Set.Ico (0 : ℝ) 1,
          chordCylCoord lam t s = z) :=
  ⟨fun t => chordCylCoord_one_eq_zero lam t,
   fun _ _ _ _ ht ht' hs hs' => chordCylCoord_eq_iff lam hlam ht ht' hs hs',
   fun z hz => chordCylCoord_surj lam hlam z hz⟩

end Work.Implosion.Chord
