import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm

/-!
# `isPrimitive_of_sqfree_primary`

A primary Gaussian integer `z` (`Re z` odd, `Im z` even, `Im z ≡ Re z - 1 (mod 4)`, i.e.
`z ≡ 1 (mod 2(1+i))`) whose norm `|z|²` is squarefree is **primitive**, `(z, z̄) = 1`.

The two inputs are exactly the ones of `Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm`
(squarefreeness of `gnorm z` and oddness of `gnorm z`): primitivity of the paper's polar box
(5.14) is the special case used throughout *FI* §§6–9, and the only extra ingredient here is that
the primary condition forces `gnorm z` to be odd, because
`gnorm z = (Re z)² + (Im z)²` with `Re z` odd and `Im z` even.
-/

set_option autoImplicit false

namespace Work.FITop4.Red5

/-- `gnorm z` is odd for a primary `z`: `gnorm z = (Re z)² + (Im z)²` is the sum of an odd and an
even square. -/
theorem gnorm_odd_of_primary {z : GaussianInt} (h : Work.FIPlan.IsPrimary z) :
    Odd (Work.FIPlan.gnorm z) := by
  obtain ⟨hre, him, -⟩ := h
  have hgn : Work.FIPlan.gnorm z = z.re.natAbs * z.re.natAbs + z.im.natAbs * z.im.natAbs :=
    GaussianInt.natAbs_norm_eq z
  rw [hgn]
  obtain ⟨r, hr⟩ := him.natAbs
  exact (hre.natAbs.mul hre.natAbs).add_even ⟨2 * r * r, by rw [hr]; ring⟩

/-- A primary Gaussian integer of squarefree norm is primitive (`IsPrimitive z` is
`(z, z̄) = 1`). -/
theorem isPrimitive_of_sqfree_primary {z : GaussianInt}
    (hsq : Squarefree (Work.FIPlan.gnorm z)) (hpri : Work.FIPlan.IsPrimary z) :
    Work.FIPlan.IsPrimitive z := by
  rw [Work.FIPlan.IsPrimitive]
  exact Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm hsq (gnorm_odd_of_primary hpri)

end Work.FITop4.Red5
