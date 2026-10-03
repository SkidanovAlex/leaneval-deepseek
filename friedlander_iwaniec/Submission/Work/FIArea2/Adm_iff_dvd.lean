import Mathlib
import Submission.Work.FIArea2.CCountPoissonDefs

namespace Work.FIArea2

/-- For a rational integer `d`, divisibility by the Gaussian integer `d` (i.e. by `d + 0i`) is
componentwise divisibility of `re` and `im`. -/
lemma intCast_dvd_iff_re_im (d : ℤ) (X : GaussianInt) :
    ((d : GaussianInt) ∣ X) ↔ (d ∣ X.re ∧ d ∣ X.im) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨⟨q.re, by simp only [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]; ring⟩,
           ⟨q.im, by simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]; ring⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, b⟩, by
      ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
      <;> linarith⟩

theorem Adm_iff_dvd (z1 z2 : GaussianInt) (p : ℤ × ℤ) :
    Work.FIArea2.Adm z1 z2 p ↔ (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ Work.FIArea2.Xof z1 z2 p := by
  rw [Work.FIArea2.Adm, Work.FIPlan.absDelta, intCast_dvd_iff_re_im]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Int.natAbs_dvd.mp h1, Int.natAbs_dvd.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Int.natAbs_dvd.mpr h1, Int.natAbs_dvd.mpr h2⟩

end Work.FIArea2
