import Mathlib
import Submission.Work.FIArea7.GaussUnits
import Submission.Work.FIArea7.gaussCoord_val_gaussMul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- Coordinates of a difference of products in `ℤ[i]`:
`⟨A,B⟩ - ⟨a,b⟩⟨c,d⟩ = ⟨A - (ac - bd), B - (ad + bc)⟩`. -/
lemma gaussInt_sub_mul_re_im (A B a b c d : ℤ) :
    (⟨A, B⟩ - ⟨a, b⟩ * ⟨c, d⟩ : GaussianInt)
      = ⟨A - (a * c - b * d), B - (a * d + b * c)⟩ := by
  ext
  · simp [Zsqrtd.re_mul, sub_eq_add_neg]
  · simp [Zsqrtd.im_mul, sub_eq_add_neg]

/-- A Gaussian integer is divisible by `(m : ℤ[i])` as soon as both of its coordinates
are divisible by `m`. -/
lemma gaussInt_dvd_of_dvd_re_im {m : ℤ} {z : GaussianInt} (hre : m ∣ z.re) (him : m ∣ z.im) :
    (m : GaussianInt) ∣ z := by
  obtain ⟨p, hp⟩ := hre
  obtain ⟨q, hq⟩ := him
  refine ⟨⟨p, q⟩, ?_⟩
  ext <;> simp [hp, hq]

/-- The representative of the Gaussian product `gaussMul p q` (taken in
`{0, …, n-1}²`) differs from the coordinatewise complex product of the representatives of
`p` and `q` by a Gaussian integer multiple of `n`. -/
theorem gaussMul_rep_dvd (n : ℕ) (hn : 0 < n) (p q : ZMod n × ZMod n) :
    ((n : ℤ) : GaussianInt)
      ∣ (⟨((Work.FIArea7.gaussMul p q).1.val : ℤ), ((Work.FIArea7.gaussMul p q).2.val : ℤ)⟩
          - ⟨(p.1.val : ℤ), (p.2.val : ℤ)⟩ * ⟨(q.1.val : ℤ), (q.2.val : ℤ)⟩) := by
  obtain ⟨h1, h2⟩ := gaussCoord_val_gaussMul n hn p q
  rw [gaussInt_sub_mul_re_im]
  apply gaussInt_dvd_of_dvd_re_im
  · have hx : (n : ℤ)
        ∣ ((p.1.val : ℤ) * q.1.val - p.2.val * q.2.val) - ((gaussMul p q).1.val : ℤ) :=
      Int.ModEq.dvd h1
    simpa only [neg_sub] using dvd_neg.mpr hx
  · have hx : (n : ℤ)
        ∣ ((p.1.val : ℤ) * q.2.val + p.2.val * q.1.val) - ((gaussMul p q).2.val : ℤ) :=
      Int.ModEq.dvd h2
    simpa only [neg_sub] using dvd_neg.mpr hx

end Work.FIArea7
