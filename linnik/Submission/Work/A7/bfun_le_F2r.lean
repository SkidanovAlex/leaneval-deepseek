/-
Area 7: the per-zero contribution of `bfun` with multiplicity one is bounded by the
value of `F₂` on the real axis.

For a zero `ρ` in HB's box whose multiplicity is `1` we have, writing `λ = λ(ρ) = (1 - Re ρ) log q > 0`
and `z = (1 - ρ) log q` (so `z.re = λ`), `bfun q K R χ ρ = ‖F₂ K z‖`, and

* `‖F₂ K z‖ ≤ ‖F₂ K (Re z)‖`  (Mathlib-side lemma `API.F2_norm_le_re`),
* `‖F₂ K (λ:ℂ)‖ = ((1 - e^{-Kλ})/λ)²`  since `F₂ K λ = ((1 - e^{-Kλ})/λ)²` is a square of a
  nonnegative real.

This is the `K = 3/10` case used in the assembly of Area 7.
-/
import Mathlib
import Submission.Work.A7.Integrands
import Submission.Work.LinnikContract.API.F2_norm_le_re

open scoped Classical BigOperators
open DirichletCharacter Complex

namespace Work.A7

theorem bfun_le_F2r {q : ℕ} [NeZero q] {R lam : ℝ} {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hbox : Work.LinnikContract.InBox q R ρ) (hmult : Work.LinnikContract.zeroMult χ ρ = 1)
    (hlam : Work.LinnikContract.lamOf q ρ = lam) (hlam0 : 0 < lam) :
    Work.A7.bfun q ((3:ℝ)/10) R χ ρ ≤ ((1 - Real.exp (-(((3:ℝ)/10) * lam))) / lam) ^ 2 := by
  set K : ℝ := (3:ℝ)/10 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; norm_num
  rw [bfun, if_pos hbox, hmult]
  simp only [Nat.cast_one, one_mul]
  set z : ℂ := (1 - ρ) * ((Real.log q : ℝ) : ℂ) with hz
  have hzre : z.re = lam := by
    rw [hz, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    simp only [Complex.sub_re, Complex.one_re, mul_zero, sub_zero]
    rw [← hlam]; rfl
  have hle := Work.LinnikContract.API.F2_norm_le_re K hKpos z (by rw [hzre]; exact hlam0)
  refine le_trans hle ?_
  rw [hzre]
  have hy0 : (0:ℝ) ≤ (1 - Real.exp (-(K * lam))) / lam := by
    apply div_nonneg _ hlam0.le
    rw [sub_nonneg, Real.exp_le_one_iff]
    nlinarith [hlam0, hKpos]
  have hexp : Complex.exp (-(K:ℂ) * (lam:ℂ)) = ((Real.exp (-(K * lam)) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
  have hF : Work.LinnikContract.F2 K ((lam:ℂ))
      = (((1 - Real.exp (-(K * lam))) / lam : ℝ) : ℂ) ^ 2 := by
    unfold Work.LinnikContract.F2
    rw [hexp]
    push_cast
    ring
  have hnorm : ‖(((1 - Real.exp (-(K * lam))) / lam : ℝ) : ℂ)‖
      = (1 - Real.exp (-(K * lam))) / lam := by
    rw [show ‖(((1 - Real.exp (-(K * lam))) / lam : ℝ) : ℂ)‖
          = |(1 - Real.exp (-(K * lam))) / lam| from RCLike.norm_ofReal _,
        abs_of_nonneg hy0]
  rw [hF, norm_pow, hnorm]

end Work.A7
