/-
# *FI* (19.12): the reciprocity law of the Dirichlet symbol

For primary primitive `w, z` the Dirichlet symbol of §19 is symmetric:

  `ξ_w(z) = ξ_z(w)`   (*FI* (19.12)).

The proof is the one of the paper: `ξ_w(z)ξ_z(w) = (Re(wz) | |w|²|z|²)` (this is *pure*
multiplicativity of the Jacobi symbol in the lower entry, already in `FIsymbols`), and
`|w|²|z|² = |wz|² = Re(wz)² + Im(wz)²`, so (19.8) (`jacobiSym_sq_add_sq`, applied to the pair
`(Re(wz), Im(wz))`, which is odd/even/coprime for primary `w, z` with `wz` primitive) makes the
product `1`; the value of `ξ_w(z)` is then `±1`, whence `ξ_w(z) = ξ_z(w)`.
-/
import Mathlib
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.jacobiSym_sq_add_sq

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-! ## 0. Parities of the product of two primary Gaussian integers -/

/-- `Re(wz)` is odd for primary `w, z` (`u r − v s` with `u, r` odd and `v, s` even). -/
lemma odd_re_mul_of_primary {w z : GaussianInt} (hw : Work.FIPlan.IsPrimary w)
    (hz : Work.FIPlan.IsPrimary z) : Odd (w * z).re := by
  obtain ⟨ho1, he1, _⟩ := hw
  obtain ⟨ho2, he2, _⟩ := hz
  obtain ⟨a, ha⟩ := he1
  obtain ⟨b, hb⟩ := he2
  obtain ⟨c, hc⟩ := ho1
  obtain ⟨d, hd⟩ := ho2
  rw [re_mul]
  exact ⟨2 * c * d + c + d - 2 * a * b, by rw [ha, hb, hc, hd]; ring⟩

/-- `Im(wz)` is even for primary `w, z` (`u s + v r` with `u, r` odd and `v, s` even). -/
lemma even_im_mul_of_primary {w z : GaussianInt} (hw : Work.FIPlan.IsPrimary w)
    (hz : Work.FIPlan.IsPrimary z) : Even (w * z).im := by
  obtain ⟨ho1, he1, _⟩ := hw
  obtain ⟨ho2, he2, _⟩ := hz
  obtain ⟨a, ha⟩ := he1
  obtain ⟨b, hb⟩ := he2
  obtain ⟨c, hc⟩ := ho1
  obtain ⟨d, hd⟩ := ho2
  rw [im_mul]
  exact ⟨2 * c * b + b + 2 * a * d + a, by rw [ha, hb, hc, hd]; ring⟩

/-- `|wz|² = (Re(wz)² + Im(wz)²).natAbs`. -/
lemma gnorm_eq_natAbs_sq_add_sq (z : GaussianInt) :
    Work.FIPlan.gnorm z = (z.re ^ 2 + z.im ^ 2).natAbs := by
  have h : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := norm_eq z
  rw [← h]; simp

/-! ## 1. The reciprocity law -/

/-- ***FI* (19.12).**  For primary `w, z` whose product is primitive (expressed as
`IsCoprime (Re(wz)) (Im(wz))`, the form in which (19.8) consumes it) the Dirichlet symbol is
symmetric: `ξ_w(z) = ξ_z(w)`.

(When `wz` is *not* primitive both sides vanish, by (19.10); that is the trivial case and is not
needed here.) -/
theorem dirichletSym_reciprocity {w z : GaussianInt}
    (hPw : Work.FIPlan.IsPrimary w) (hPz : Work.FIPlan.IsPrimary z)
    (hcop : IsCoprime (w * z).re (w * z).im)
    (hw : Work.FIPlan.gnorm w ≠ 0) (hz : Work.FIPlan.gnorm z ≠ 0) :
    DirichletSym w z = DirichletSym z w := by
  have hodd := odd_re_mul_of_primary hPw hPz
  have heven := even_im_mul_of_primary hPw hPz
  have hone : DirichletSym w z * DirichletSym z w = 1 := by
    rw [dirichletSym_mul_swap (w := w) (z := z) hw hz, ← gnorm_mul, gnorm_eq_natAbs_sq_add_sq]
    exact jacobiSym_sq_add_sq hodd heven hcop
  exact Int.eq_of_mul_eq_one hone

end

end Work.FIArea7
