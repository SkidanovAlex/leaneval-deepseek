/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The chord foliation exhibits the fundamental domain as a cylinder

This file assembles the "cylindrical fundamental domain" of Hubbard–Schleicher §4
(`Multicorns are not Path Connected`, Prop. 4.2 and the lemma following it), in the
geometrically natural case `a = iλ` (`λ > 0`) with `h` **real-valued and non-zero on
the cut** `ℓ = [−iλ, iλ]`:

* every chord `s ↦ chordPt (iλ) h t s` is *horizontal*, `Im = t·λ`
  (`Chord.chordPt_re_im`);
* the chord parametrisation `(t,s) ↦ chordPt (iλ) h t s` is injective on
  `(−1,1) × [0,1]` (`Chord.chordPt_injective`);

and, for the **cylinder coordinate**

  `chordCylCoord lam t s = exp (2πi (s + i·chordHeight lam t))`,
  `chordHeight lam t = log((1+t)/(1−t)) / (2λ)`  (the Écalle height of `t·a`),

* the two boundary edges `s = 0` (the cut) and `s = 1` (the image arc `f(ℓ)`) are
  identified at constant height;
* the coordinate is injective on `(−1,1) × [0,1)`, i.e. it is a genuine chart;
* it is surjective onto `ℂ^*`, i.e. the quotient of the fundamental domain by the
  boundary identification *is* the cylinder `ℂ/ℤ ≅ ℂ^*`.

The height coordinate `chordHeight` maps `(−1,1)` order-isomorphically onto `ℝ`
(`Chord.chordHeight_bij`), so writing `chordCylCoord lam t s = exp (2πi(s + iH))`
with `s ∈ [0,1)` and `H ∈ ℝ` is exactly the standard fundamental-strip
parametrisation of `ℂ^*` (`Cylinder.exp_two_pi_I_strip_rep`).
-/
import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Geometry
import Submission.Work.Implosion.Chord
import Submission.Work.Implosion.Geometry.normalForm_cutPt_re
import Submission.Work.Implosion.Chord.chordPt_re_im
import Submission.Work.Implosion.Chord.chordPt_injective
import Submission.Work.Implosion.Chord.chordHeight_bij
import Submission.Work.Implosion.Cylinder.exp_two_pi_I_strip_rep

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Chord

open Complex

theorem cylindrical_fundamentalDomain (lam : ℝ) (h : ℂ → ℂ) (hlam : 0 < lam)
    (hreal : ∀ t : ℝ, (h (cutPt ((lam : ℂ) * I) t)).im = 0)
    (hne : ∀ t : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 → h (cutPt ((lam : ℂ) * I) t) ≠ 0) :
    (∀ t : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        (chordPt ((lam : ℂ) * I) h t s).im = t * lam)
      ∧ (∀ t t' s s' : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 → t' ∈ Set.Ioo (-1 : ℝ) 1 →
          s ∈ Set.Icc (0 : ℝ) 1 → s' ∈ Set.Icc (0 : ℝ) 1 →
          chordPt ((lam : ℂ) * I) h t s = chordPt ((lam : ℂ) * I) h t' s' →
          t = t' ∧ s = s')
      ∧ (∀ t : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 →
          chordCylCoord lam t 1 = chordCylCoord lam t 0)
      ∧ (∀ t t' s s' : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 → t' ∈ Set.Ioo (-1 : ℝ) 1 →
          s ∈ Set.Ico (0 : ℝ) 1 → s' ∈ Set.Ico (0 : ℝ) 1 →
          (chordCylCoord lam t s = chordCylCoord lam t' s' ↔ t = t' ∧ s = s'))
      ∧ (∀ z : ℂ, z ≠ 0 → ∃ t ∈ Set.Ioo (-1 : ℝ) 1, ∃ s ∈ Set.Ico (0 : ℝ) 1,
          chordCylCoord lam t s = z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the chords are horizontal at height `t·λ`
    intro t ht s hs
    exact (chordPt_re_im lam h t s (hreal t)).2
  · -- the chord parametrisation is injective
    intro t t' s s' ht ht' hs hs' heq
    exact chordPt_injective lam h hlam hreal hne ht ht' hs hs' heq
  · -- the two boundary edges of the fundamental domain are identified
    intro t ht
    simp only [chordCylCoord, Complex.ofReal_one, Complex.ofReal_zero]
    exact Complex.exp_eq_exp_iff_exists_int.mpr ⟨1, by ring⟩
  · -- the cylinder coordinate is injective on `(−1,1) × [0,1)`
    intro t t' s s' ht ht' hs hs'
    constructor
    · intro heq
      -- unfold the exponential and compare the exponents up to the period `2πi`
      have h := heq
      simp only [chordCylCoord] at h
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
      have hkey : ((s : ℂ) + (chordHeight lam t : ℂ) * I)
          - ((s' : ℂ) + (chordHeight lam t' : ℂ) * I) = (n : ℂ) := by
        have h2 : (2 * (Real.pi : ℂ) * I)
              * (((s : ℂ) + (chordHeight lam t : ℂ) * I)
                  - ((s' : ℂ) + (chordHeight lam t' : ℂ) * I))
            = (2 * (Real.pi : ℂ) * I) * (n : ℂ) := by
          rw [mul_sub, hn]; ring
        exact mul_left_cancel₀ Complex.two_pi_I_ne_zero h2
      -- separate the real and imaginary parts of the exponent difference
      have hsum : ((s : ℂ) - (s' : ℂ))
          + ((chordHeight lam t : ℂ) - (chordHeight lam t' : ℂ)) * I = (n : ℂ) := by
        rw [← hkey]; ring
      -- the imaginary part recovers `t`, on which the height is injective
      have hH : chordHeight lam t = chordHeight lam t' := by
        have h4 := congrArg Complex.im hsum
        have h5 : chordHeight lam t - chordHeight lam t' = 0 := by
          simpa using h4
        linarith
      have htt : t = t' := (chordHeight_bij lam hlam).1.injOn ht ht' hH
      -- the real part recovers `s` modulo `ℤ`
      have hre : s - s' = (n : ℝ) := by
        have h6 := congrArg Complex.re hsum
        simp only [Complex.add_re, Complex.sub_re, Complex.sub_im, Complex.mul_I_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, sub_zero,
          neg_zero, add_zero] at h6
        linarith
      -- but `s, s' ∈ [0,1)` force that integer to be `0`
      have hn1 : (n : ℝ) < 1 := by rw [← hre]; linarith [hs.2, hs'.1]
      have hn2 : (-1 : ℝ) < (n : ℝ) := by rw [← hre]; linarith [hs.1, hs'.2]
      have hnz : n = 0 := by
        have h1 : n < 1 := by exact_mod_cast hn1
        have h2 : -1 < n := by exact_mod_cast hn2
        omega
      refine ⟨htt, ?_⟩
      have hss : s - s' = 0 := by rw [hre, hnz]; norm_num
      linarith
    · -- conversely, equal parameters give equal cylinder coordinates
      rintro ⟨rfl, rfl⟩
      rfl
  · -- the cylinder coordinate is surjective onto `ℂ^*`
    intro z hz
    -- represent `z = exp (2πi u)` with `0 ≤ Re u < 1`
    obtain ⟨u, hu0, hu1, hue⟩ := Cylinder.exists_exp_two_pi_I_strip z hz
    -- realise the imaginary part of `u` as a chord height
    obtain ⟨t, ht, htH⟩ := (chordHeight_bij lam hlam).2 (Set.mem_univ u.im)
    refine ⟨t, ht, u.re, ⟨hu0, hu1⟩, ?_⟩
    simp only [chordCylCoord]
    rw [htH, Complex.re_add_im u, hue]

end Work.Implosion.Chord
