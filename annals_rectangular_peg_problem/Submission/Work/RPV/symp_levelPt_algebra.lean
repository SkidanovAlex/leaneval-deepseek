import Mathlib
import Submission.Work.RPV.Defs

/-!
# The algebraic identity `symp_levelPt_algebra`

This is the purely algebraic core behind `Work.RPV.levelPt_omega`: it computes the
symplectic pairing `symp` of the two "level-point" tangent vectors

* `u = e * (Γσ - Aσ * I * z)` with data `(q₂,p₂) = (Aσ, Re(conj z * Γσ) - 1)`,
* `v = e * (Γt - At * I * z)` with data `(q₂,p₂) = (At, Re(conj z * Γt))`,

where `conj e * e = 1`.  The answer is `ωC Γσ Γt - At`.

The proof splits into three elementary real/complex-algebra facts:

* `symp` of two points of the shape `((u.im, α), (u.re, P))`, `((v.im, β), (v.re, R))`
  equals `ωC u v + P * β - α * R` (the "p₂ dq₂ - q₂ dp₂" part separates off);
* `ωC` is invariant under a common unit factor `e` (`conj e * e = 1`);
* expanding `ωC (Γσ - Aσ I z) (Γt - At I z)` in real and imaginary parts.

The `z`-terms cancel using `Re(conj Γσ * z) = Re(conj z * Γσ)`.
-/

namespace Work.RPV

/-- Splitting `symp` of two level-point-shaped vectors: the `(q₁,p₁)` part is `ωC`
and the `(q₂,p₂)` part contributes `P * β - α * R`. -/
private lemma symp_of_reIm (u v : ℂ) (α β P R : ℝ) :
    symp ((u.im, α), (u.re, P)) ((v.im, β), (v.re, R)) = ωC u v + P * β - α * R := by
  simp only [symp, ωC, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- `ωC` is invariant under multiplication of both arguments by a unit complex number
(`conj e * e = 1`). -/
private lemma ωC_rotate_unit (e u v : ℂ) (he : (starRingEnd ℂ) e * e = 1) :
    ωC (e * u) (e * v) = ωC u v := by
  simp only [ωC]
  congr 1
  calc (starRingEnd ℂ) (e * u) * (e * v)
      = ((starRingEnd ℂ) u * (starRingEnd ℂ) e) * (e * v) := by rw [map_mul]; ring
    _ = (starRingEnd ℂ) u * ((starRingEnd ℂ) e * e) * v := by ring
    _ = (starRingEnd ℂ) u * v := by rw [he]; ring

/-- Expansion of `ωC` of the two level-point directions in the plane. -/
private lemma ωC_sub_I_mul (Γσ Γt z : ℂ) (Aσ At : ℝ) :
    ωC (Γσ - (Aσ : ℂ) * Complex.I * z) (Γt - (At : ℂ) * Complex.I * z)
      = ωC Γσ Γt - At * ((starRingEnd ℂ) Γσ * z).re + Aσ * ((starRingEnd ℂ) z * Γt).re := by
  simp only [ωC, Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem symp_levelPt_algebra (z Γσ Γt : ℂ) (Aσ At : ℝ) (e : ℂ) (he : (starRingEnd ℂ) e * e = 1) :
    Work.RPV.symp (((e * (Γσ - (Aσ : ℂ) * Complex.I * z)).im, Aσ),
          ((e * (Γσ - (Aσ : ℂ) * Complex.I * z)).re, ((starRingEnd ℂ) z * Γσ).re - 1))
         (((e * (Γt - (At : ℂ) * Complex.I * z)).im, At),
          ((e * (Γt - (At : ℂ) * Complex.I * z)).re, ((starRingEnd ℂ) z * Γt).re))
      = Work.RPV.ωC Γσ Γt - At := by
  rw [symp_of_reIm, ωC_rotate_unit e _ _ he, ωC_sub_I_mul]
  have h : ((starRingEnd ℂ) Γσ * z).re = ((starRingEnd ℂ) z * Γσ).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [h]
  ring

end Work.RPV
