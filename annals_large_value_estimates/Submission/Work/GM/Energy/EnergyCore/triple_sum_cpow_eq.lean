import Mathlib
import Submission.Work.GM.Energy.Defs

/-!
# The triple-sum identity behind the `‖R‖³` term of GM Lemma 11.4

Let `R(v) = Σ_{t ∈ W} |v|^{it}` (`Submission.GM.Rfun`).  Because `|v| = v` for `v > 0`, every term
is `(v : ℂ) ^ (I t)`, and since `v` is real and positive,

* `conj ((v : ℂ) ^ (I t)) = (v : ℂ) ^ (-(I t)) = (v : ℂ) ^ (I (-t))`
  (`conj_cpow_ofReal_pureImag`), and
* `(v : ℂ) ^ (I t₁) * (v : ℂ) ^ (I t₂) * (v : ℂ) ^ (I (-t₃)) = (v : ℂ) ^ (I (t₁ + t₂ - t₃))`
  (`cpow_mul_cpow_pureImag`), because `cpow` is additive for a nonzero base.

Expanding the product `R(v) * R(v) * conj (R(v))` therefore gives exactly the triple sum
`Σ_{t₁,t₂,t₃ ∈ W} v^{I (t₁+t₂-t₃)}`; this is the identity `triple_sum_cpow_eq` below.
-/

namespace Work.GM.Energy.EnergyCore

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-- For `v > 0` and real `t`, conjugation inverts the imaginary exponent:
`conj (v ^ (I t)) = v ^ (I (-t))`. -/
lemma conj_cpow_ofReal_pureImag {v : ℝ} (hv : 0 < v) (t : ℝ) :
    (starRingEnd ℂ) (((v:ℝ):ℂ) ^ (Complex.I * (t:ℂ)))
      = ((v:ℝ):ℂ) ^ (Complex.I * ((-t:ℝ):ℂ)) := by
  have hx : (((v:ℝ):ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hv.le]; exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (((v:ℝ):ℂ)) (Complex.I * (t:ℂ)) hx
  simp only [Complex.conj_ofReal] at h
  rw [← h]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- For `v > 0`, the product of two `cpow`s with pure-imaginary exponents and the conjugate of a
third one collapses into a single `cpow`. -/
lemma cpow_mul_cpow_pureImag {v : ℝ} (hv : 0 < v) (t1 t2 t3 : ℝ) :
    (((v:ℝ):ℂ) ^ (Complex.I * (t1:ℂ)) * ((v:ℝ):ℂ) ^ (Complex.I * (t2:ℂ)))
      * ((v:ℝ):ℂ) ^ (Complex.I * ((-t3:ℝ):ℂ))
    = ((v:ℝ):ℂ) ^ (Complex.I * (((t1 + t2 - t3 : ℝ)):ℂ)) := by
  have hvne : (((v:ℝ):ℂ)) ≠ 0 := by simpa using hv.ne'
  rw [← Complex.cpow_add (Complex.I * (t1:ℂ)) (Complex.I * (t2:ℂ)) hvne,
      ← Complex.cpow_add (Complex.I * (t1:ℂ) + Complex.I * (t2:ℂ))
        (Complex.I * ((-t3:ℝ):ℂ)) hvne]
  congr 1
  push_cast
  ring

/-- Expansion of a product of three sums into an iterated sum, with the sum over the third factor
innermost (the order needed to match a triple sum written `∑ t₁, ∑ t₂, ∑ t₃`). -/
lemma sum_mul_sum_mul_sum {ι : Type*} (s : Finset ι) (f g h : ι → ℂ) :
    (∑ x ∈ s, f x) * (∑ y ∈ s, g y) * (∑ z ∈ s, h z)
      = ∑ x ∈ s, ∑ y ∈ s, ∑ z ∈ s, f x * g y * h z := by
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]

/-- **GM (11.5), the discrete third moment.** For `v > 0`,
`Σ_{t₁,t₂,t₃ ∈ W} v^{I(t₁+t₂-t₃)} = R(v)² · conj (R(v))`, where `R(v) = Σ_{t∈W} |v|^{it}`. -/
theorem triple_sum_cpow_eq (W : Finset ℝ) {v : ℝ} (hv : 0 < v) :
    (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ((v : ℂ)) ^ (Complex.I * (((t1 + t2 - t3 : ℝ)) : ℂ)))
      = Submission.GM.Rfun W v * Submission.GM.Rfun W v
          * (starRingEnd ℂ) (Submission.GM.Rfun W v) := by
  have hR : Submission.GM.Rfun W v = ∑ t ∈ W, ((v:ℝ):ℂ) ^ (Complex.I * (t:ℂ)) := by
    unfold Submission.GM.Rfun
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [abs_of_pos hv]
  rw [hR, map_sum, sum_mul_sum_mul_sum]
  refine Finset.sum_congr rfl fun t1 _ => Finset.sum_congr rfl fun t2 _ =>
    Finset.sum_congr rfl fun t3 _ => ?_
  rw [conj_cpow_ofReal_pureImag hv]
  exact (cpow_mul_cpow_pureImag hv t1 t2 t3).symm

end Work.GM.Energy.EnergyCore
