import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Geometry.normalForm_cutPt_re

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Geometry

open Complex

/-- For `a = λi` the cut `ℓ = [−a, a]` is a segment of the imaginary axis: every
point of it is purely imaginary. -/
theorem mem_cut_mul_I_re_eq_zero {lam : ℝ} {ζ : ℂ} (hζ : ζ ∈ cut ((lam : ℂ) * I)) :
    ζ.re = 0 := by
  obtain ⟨s, _hs, rfl⟩ := (mem_cut_iff ((lam : ℂ) * I) ζ).mp hζ
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

/-- **The image arc `f(ℓ)` leaves the cut** (Hubbard–Schleicher §4, the disjointness
behind the fundamental domain).  For `a = λi` with `λ > 0` and
`‖h − 1‖ ≤ ε ≤ 1/2` on the disc of radius `2λ`, the point `f(t·a)` of the image of
the interior of the cut lies in the open right half-plane, hence is not on the
(imaginary-axis) cut `ℓ = [−a, a]`.

Indeed `Re f(t·a) = λ²(1−t²)·Re h(t·a) > 0`: the prefactor is positive for `|t| < 1`
and `Re h(t·a) ≥ 1 − ‖h(t·a) − 1‖ ≥ 1/2`. -/
theorem imageCut_disjoint_cut (lam : ℝ) (hlam : 0 < lam) (h : ℂ → ℂ) (ε : ℝ)
    (hh : ∀ ζ : ℂ, ‖ζ‖ ≤ 2 * lam → ‖h ζ - 1‖ ≤ ε) (hε : ε ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    normalForm ((lam : ℂ) * I) h (cutPt ((lam : ℂ) * I) t) ∉ cut ((lam : ℂ) * I) := by
  intro hmem
  -- `t·a` lies in the disc where `h` is `ε`-close to `1`.
  have ht_abs : |t| < 1 := abs_lt.mpr ⟨ht.1, ht.2⟩
  have hnorm : ‖cutPt ((lam : ℂ) * I) t‖ ≤ 2 * lam := by
    rw [cutPt_mul_I]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one, abs_mul,
      abs_of_pos hlam]
    have h1 : |t| * lam < 1 * lam := mul_lt_mul_of_pos_right ht_abs hlam
    linarith
  -- hence `Re h(t·a) ≥ 1/2 > 0`.
  have hh_re : 0 < (h (cutPt ((lam : ℂ) * I) t)).re := by
    have h1 : |(h (cutPt ((lam : ℂ) * I) t)).re - 1| ≤ ε := by
      calc |(h (cutPt ((lam : ℂ) * I) t)).re - 1|
          = |(h (cutPt ((lam : ℂ) * I) t) - 1).re| := by simp [Complex.sub_re]
        _ ≤ ‖h (cutPt ((lam : ℂ) * I) t) - 1‖ := abs_re_le_norm _
        _ ≤ ε := hh _ hnorm
    have h2 := (abs_le.mp (le_trans h1 hε)).1
    linarith
  -- therefore `Re f(t·a) > 0`, while the cut is purely imaginary.
  have hpos : 0 < (normalForm ((lam : ℂ) * I) h (cutPt ((lam : ℂ) * I) t)).re := by
    rw [normalForm_cutPt_re]
    have h1t : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    exact mul_pos (mul_pos (pow_pos hlam 2) h1t) hh_re
  have hzre : (normalForm ((lam : ℂ) * I) h (cutPt ((lam : ℂ) * I) t)).re = 0 :=
    mem_cut_mul_I_re_eq_zero hmem
  linarith

end Work.Implosion.Geometry
