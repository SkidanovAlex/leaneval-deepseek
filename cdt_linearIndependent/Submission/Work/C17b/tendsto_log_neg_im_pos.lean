import Mathlib

namespace Work.C17b

/-- Approaching a negative real point `-t` (`t > 0`) from below the branch cut
(`im < 0`), the principal complex logarithm tends to `log t - π i`. -/
theorem tendsto_log_neg_im_pos {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun u : ℂ => Complex.log (-u)) (nhdsWithin (t : ℂ) {u : ℂ | 0 < u.im})
      (nhds ((Real.log t : ℂ) - (Real.pi : ℂ) * Complex.I)) := by
  have hre : (-(t : ℂ)).re < 0 := by simpa using neg_lt_zero.mpr ht
  have him : (-(t : ℂ)).im = 0 := by simp
  have hmain := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him
  have hset : ⇑(Homeomorph.neg ℂ) '' {u : ℂ | 0 < u.im} = {w : ℂ | w.im < 0} := by
    ext w; simp [Complex.neg_im]
  have h1 : Filter.Tendsto (fun u : ℂ => -u) (nhdsWithin (t : ℂ) {u : ℂ | 0 < u.im})
      (nhdsWithin (-(t : ℂ)) {w : ℂ | w.im < 0}) := by
    have hh := (Homeomorph.neg ℂ).isEmbedding.map_nhdsWithin_eq {u : ℂ | 0 < u.im} (t : ℂ)
    rw [hset] at hh
    exact hh.le
  have hthis : ‖-(t : ℂ)‖ = t := by rw [norm_neg, Complex.norm_of_nonneg ht.le]
  have hmain' : Filter.Tendsto Complex.log (nhdsWithin (-(t : ℂ)) {z : ℂ | z.im < 0})
      (nhds ((Real.log t : ℂ) - (Real.pi : ℂ) * Complex.I)) := by
    simpa [hthis] using hmain
  exact hmain'.comp h1

end Work.C17b
