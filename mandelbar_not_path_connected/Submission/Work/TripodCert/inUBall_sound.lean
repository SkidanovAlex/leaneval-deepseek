/-
# TripodCert — soundness of the containment checker `inUBall`

Area `Submission/Work/TripodCert/`.  The certificate checks the *uniqueness disc* of the tripod
chain by the mantissa test `inUBall` (`Work.TripodCert.Num`), which for the disk
`(cx, cy, cr) = dskOf l q` and the ball `(zx, zy, R)` asserts

  `(cx - zx)² + (cy - zy)² ≤ (R - cr)²`   (all in mantissas, scale `MSZ = 2 ^ 40`).

This file proves that the test is *sound*: together with the radius check `cr ≤ R` extracted by
`chkUBall_sound` it implies that the disk `dskOf l q` is contained in the closed ball of radius
`R` about `zx + i zy`.

The mathematics is one triangle inequality, at scale: the mantissa inequality says that the
centre `c` of the disk is at distance `≤ R - cr` from `z₀ = zx + i zy` (`cr ≤ R` making the right
hand side nonnegative), hence `z ∈ D` gives
`‖z - z₀‖ ≤ ‖z - c‖ + ‖c - z₀‖ ≤ cr + (R - cr) = R`.

The decoding `Q m = m / 2 ^ 40` (`SeedCertRay.Q`) turns the mantissa inequality into the real
one `Q(cx - zx)² + Q(cy - zy)² ≤ Q(R - cr)²`.
-/
import Mathlib
import Submission.Work.TripodCert.Num
import Submission.Work.SeedCertRay.Q
import Submission.Work.SeedCertRay.Disk

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

open Work.SeedCertRay

/-- The decoding `Q` of a mantissa, in `ℝ`. -/
private lemma Q_real (m : ℤ) : ((Q m : ℚ) : ℝ) = (m : ℝ) / (2:ℝ)^40 := by
  simp only [Q, MS]
  push_cast
  ring

/-- **The squared mantissa inequality, decoded.**  From `a² + b² ≤ d²` in mantissas follows
`Q a² + Q b² ≤ Q d²` in `ℝ`.  (Both sides scale by the same positive factor `(2 ^ 40)⁻²`.) -/
private lemma Q_sq_sum_le {a b d : ℤ} (h : a*a + b*b ≤ d*d) :
    ((Q a : ℚ):ℝ) * ((Q a:ℚ):ℝ) + ((Q b:ℚ):ℝ) * ((Q b:ℚ):ℝ)
      ≤ ((Q d:ℚ):ℝ) * ((Q d:ℚ):ℝ) := by
  rw [Q_real, Q_real, Q_real]
  have hcast : (a:ℝ)*(a:ℝ) + (b:ℝ)*(b:ℝ) ≤ (d:ℝ)*(d:ℝ) := by
    have h' : ((a*a + b*b : ℤ) : ℝ) ≤ ((d*d : ℤ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have hM : (0:ℝ) < (2:ℝ)^40 := by positivity
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, ← add_div]
  exact div_le_div_of_nonneg_right hcast (le_of_lt (by positivity))

/-- **A point of the plane from its two squared coordinates.**  If `x² + y² ≤ D²` with `D ≥ 0`
then `‖x + i y‖ ≤ D`.  (Immediate from `‖x + i y‖² = x² + y²`.) -/
private lemma norm_add_mul_I_le {x y D : ℝ} (hD : 0 ≤ D) (h : x*x + y*y ≤ D*D) :
    ‖(x:ℂ) + (y:ℂ)*Complex.I‖ ≤ D := by
  have hsq : ‖(x:ℂ) + (y:ℂ)*Complex.I‖ ^ 2 = x*x + y*y := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
      sub_zero]
    ring
  nlinarith [norm_nonneg ((x:ℂ) + (y:ℂ)*Complex.I), hsq]

/-- **Soundness of `inUBall`.**  If the mantissa test `inUBall` passes for the disk
`dskOf l (j * NC + i)` and the ball of centre `zx + i zy` and radius `R`, and the radius
`gI l (3 * (j * NC + i) + 2)` of that disk is at most `R`, then the disk is contained in the
rational closed ball of radius `R` about `zx + i zy`. -/
theorem inUBall_sound (zx zy R : Int) (l : List Int) (j i : Nat)
    (hR : Work.SeedCertRay.gI l (3 * (j * Work.SeedCertRay.NC + i) + 2) ≤ R)
    (h : Work.TripodCert.inUBall zx zy R l j i = true) :
    (Work.SeedCertRay.dskOf l (j * Work.SeedCertRay.NC + i)).toSet ⊆
      Metric.closedBall
        ((((Work.SeedCertRay.Q zx : ℚ) : ℝ) : ℂ) + (((Work.SeedCertRay.Q zy : ℚ) : ℝ) : ℂ) * Complex.I)
        (((Work.SeedCertRay.Q R : ℚ) : ℝ)) := by
  intro z hz
  rw [Metric.mem_closedBall]
  rw [Disk.mem_toSet] at hz
  set cx : ℤ := gI l (3 * (j * NC + i)) with hcx
  set cy : ℤ := gI l (3 * (j * NC + i) + 1) with hcy
  set cr : ℤ := gI l (3 * (j * NC + i) + 2) with hcr
  -- The radius hypothesis, in the notation of the three coordinates.
  have hRcr : cr ≤ R := by rw [hcr]; exact hR
  -- The mantissa inequality of the checker.
  have hdec : (cx - zx) * (cx - zx) + (cy - zy) * (cy - zy) ≤ (R - cr) * (R - cr) := by
    have h1 := of_decide_eq_true h
    simpa only [inUBall, ← hcx, ← hcy, ← hcr] using h1
  -- The membership in the disk, at the disk's centre.
  have hz' : ‖z - ((((Q cx : ℚ):ℝ):ℂ) + (((Q cy:ℚ):ℝ):ℂ) * Complex.I)‖ ≤ ((Q cr : ℚ):ℝ) := by
    simpa only [Disk.mem, Disk.center, dskOf, ← hcx, ← hcy, ← hcr] using hz
  -- `Q (R - cr) ≥ 0`, from `cr ≤ R`.
  have hD0 : (0:ℝ) ≤ ((Q (R - cr) : ℚ) : ℝ) := by
    have : (0:ℚ) ≤ Q (R - cr) := Q_nonneg (by omega)
    exact_mod_cast this
  -- The distance from the disk's centre to `z₀` is at most `Q (R - cr)`.
  have hsq := Q_sq_sum_le hdec
  have hcenter : dist ((((Q cx:ℚ):ℝ):ℂ) + (((Q cy:ℚ):ℝ):ℂ) * Complex.I)
      ((((Q zx:ℚ):ℝ):ℂ) + (((Q zy:ℚ):ℝ):ℂ) * Complex.I) ≤ ((Q (R - cr) : ℚ) : ℝ) := by
    rw [dist_eq_norm]
    have hsplit : ((((Q cx:ℚ):ℝ):ℂ) + (((Q cy:ℚ):ℝ):ℂ) * Complex.I)
        - ((((Q zx:ℚ):ℝ):ℂ) + (((Q zy:ℚ):ℝ):ℂ) * Complex.I)
        = (((Q (cx - zx):ℚ):ℝ):ℂ) + (((Q (cy - zy):ℚ):ℝ):ℂ) * Complex.I := by
      rw [Q_sub, Q_sub]
      push_cast
      ring
    rw [hsplit]
    exact norm_add_mul_I_le hD0 hsq
  have hz'' : dist z ((((Q cx:ℚ):ℝ):ℂ) + (((Q cy:ℚ):ℝ):ℂ) * Complex.I) ≤ ((Q cr : ℚ):ℝ) := by
    rw [dist_eq_norm]; exact hz'
  -- Triangle inequality, and `Q cr + Q (R - cr) = Q R`.
  calc dist z ((((Q zx:ℚ):ℝ):ℂ) + (((Q zy:ℚ):ℝ):ℂ) * Complex.I)
      ≤ dist z ((((Q cx:ℚ):ℝ):ℂ) + (((Q cy:ℚ):ℝ):ℂ) * Complex.I)
        + dist ((((Q cx:ℚ):ℝ):ℂ) + (((Q cy:ℚ):ℝ):ℂ) * Complex.I)
            ((((Q zx:ℚ):ℝ):ℂ) + (((Q zy:ℚ):ℝ):ℂ) * Complex.I) := dist_triangle _ _ _
    _ ≤ ((Q cr : ℚ):ℝ) + ((Q (R - cr) : ℚ):ℝ) := add_le_add hz'' hcenter
    _ = ((Q R : ℚ):ℝ) := by
        rw [← Rat.cast_add, ← Q_add, show cr + (R - cr) = R by ring]

end Work.TripodCert
