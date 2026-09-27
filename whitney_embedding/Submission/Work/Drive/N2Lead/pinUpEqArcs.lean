import Mathlib
import Submission.Work.Drive.N2Lead.pinSetup
import Submission.Work.Drive.N2Lead.saddlePinDefs

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

namespace SaddleChart

variable {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p}

/-- The complex square of the coordinate of a point of the upper-right arc (the `arcR` analogue of
`SaddleChart.arcU_sq`). -/
lemma arcR_sq (S : SaddleChart D) {ηs w : ℝ} (hw2 : |w| ≤ 2) (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1) :
    (S.Zc (S.arcR ηs w)) ^ 2
      = ((((D.ρ D.j / 8 : ℝ) ^ 2 * ηs) : ℝ) : ℂ)
          + ((((D.ρ D.j / 8 : ℝ) ^ 2 * w : ℝ)) : ℂ) * Complex.I := by
  rw [S.arcR_Zc hηs hηs1 hw2, mul_pow, Work.Drive.N2.complex_sqrt_sq, ← Complex.ofReal_pow]
  push_cast
  ring

end SaddleChart

open scoped Manifold ContDiff Topology in
/-- Every point of the *upper* pin (`saddlePin D (f p + λ²ηs) m`, `λ = ρ j / 8`, `m ≤ 2`) lies on one
of the two upper arcs `S.arcR ηs w`, `S.arcL ηs w` with `|w| ≤ m`.  The exact twin of
`Work.Drive.N2Lead.SaddleChart.pin_eq_arcs`; the proof repeats that argument with `arcR`/`arcL` in
place of `arcU`/`arcD`, using `arcR_Zc`, `arcL_Zc_neg` and `S.injOn_Zc`. -/
theorem pinUpEqArcs {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (S : Work.Drive.N2Lead.SaddleChart D) {ηs m : ℝ}
    (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) (hm0 : 0 ≤ m) (hm2 : m ≤ 2) {x : M}
    (hx : x ∈ Work.Drive.N2Lead.saddlePin D (f p + (D.ρ D.j / 8) ^ 2 * ηs) m) :
    ∃ w : ℝ, |w| ≤ m ∧ (x = S.arcR ηs w ∨ x = S.arcL ηs w) := by
  obtain ⟨hxsrc, _hxnorm, hxval, hxin⟩ := hx
  have hx' : x ∈ S.φ'.source := by rw [S.source_eq]; exact hxsrc
  have hlam : 0 < (D.ρ D.j / 8 : ℝ) := div_pos (D.hρ D.j) (by norm_num)
  have hlam2 : 0 < ((D.ρ D.j / 8 : ℝ)) ^ 2 := pow_pos hlam 2
  -- the real part of the squared coordinate is the prescribed level, shifted by `f p`
  have hre : ((S.Zc x) ^ 2).re = ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs := by
    have h := S.level_eq x hx'
    rw [hxval] at h
    linarith
  -- the parameter is read off the imaginary part (the level law makes `Zc x ^ 2` the only datum)
  set w : ℝ := ((S.Zc x) ^ 2).im / ((D.ρ D.j / 8 : ℝ)) ^ 2 with hwdef
  have hw_eq : ((D.ρ D.j / 8 : ℝ)) ^ 2 * w = ((S.Zc x) ^ 2).im := by
    rw [hwdef, mul_div_cancel₀ _ (ne_of_gt hlam2)]
  have himabs : |((S.Zc x) ^ 2).im| ≤ m * ((D.ρ D.j / 8 : ℝ)) ^ 2 := by
    rw [S.Zc_sq_im_abs hx']; exact hxin
  have hw : |w| ≤ m := by
    rw [hwdef, abs_div, abs_of_pos hlam2, div_le_iff₀ hlam2]
    exact himabs
  -- `Zc x ^ 2` agrees with `Zc (arcR ηs w) ^ 2`
  have hsquare : (S.Zc x) ^ 2 = (S.Zc (S.arcR ηs w)) ^ 2 := by
    have h1 := S.arcR_sq (ηs := ηs) (w := w) (le_trans hw hm2) hηs.le hηs1
    have h2 : (S.Zc x) ^ 2
        = ((((D.ρ D.j / 8 : ℝ) ^ 2 * ηs) : ℝ) : ℂ)
            + ((((S.Zc x) ^ 2).im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, hre]
        try ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    rw [h1, h2, hw_eq]
  -- `Zc` is injective on the chart source, so the sign of the square root decides the arc
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with h | h
  · exact ⟨w, hw, Or.inl (S.injOn_Zc hx' (S.arcR_source hηs.le hηs1 (le_trans hw hm2)) h)⟩
  · refine ⟨w, hw, Or.inr ?_⟩
    refine S.injOn_Zc hx' (S.arcL_source hηs.le hηs1 (le_trans hw hm2)) ?_
    rw [S.arcL_Zc_neg hηs.le hηs1 (le_trans hw hm2)]
    exact h

end Work.Drive.N2Lead
