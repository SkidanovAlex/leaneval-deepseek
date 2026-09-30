import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Splitting the correlation of `n ↦ f(p·n)` into the pushed-forward correlation

For a multiplicative `1`-bounded function `f`, a prime `p` and a real polynomial `φ`, the sum
`∑_{m ∈ ℕ ∩ [x/p, (x+H)/p]} f (p·m) · e(-φ(p·m))` differs from

`f p · ∑_{m ∈ ℕ ∩ [x/p, (x+H)/p]} f m · e(-(φ(p·)) (m))`

exactly on the multiples of `p` inside the summation range: for `p ∤ m` multiplicativity gives
`f (p·m) = f p · f m` and the two phases agree, while on multiples of `p` each summand has
absolute value at most `2`.  This is the "dilation splitting" that passes from the correlation of
`f` to the correlation of `f` against the dilated phase `dil p φ`.
-/

open Polynomial Finset Real Complex

namespace Work.BMF.SD

/-- `eC` takes values on the unit circle. -/
private lemma eC_norm_one (t : ℝ) : ‖Work.BMF.eC t‖ = 1 := by
  have h : Work.BMF.eC t = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    rw [Work.BMF.eC]; congr 1; push_cast; ring
  rw [h]; exact Complex.norm_exp_ofReal_mul_I _

/-- Evaluation of a dilated polynomial: `(dil a P).eval t = P.eval (a * t)`. -/
private lemma dil_eval (a : ℝ) (P : ℝ[X]) (t : ℝ) :
    (Work.BMF.dil a P).eval t = P.eval (a * t) := by
  rw [Work.BMF.dil, Polynomial.eval_comp]
  congr 1
  simp [Polynomial.eval_mul]

/-- `(dil p P).eval m = P.eval (p * m)` for natural `p, m`. -/
private lemma dil_eval_nat (P : ℝ[X]) (p m : ℕ) :
    (Work.BMF.dil (p : ℝ) P).eval (m : ℝ) = P.eval ((p * m : ℕ) : ℝ) := by
  rw [dil_eval]
  rw [← Nat.cast_mul]

theorem corr_dil_split (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n)
    (φ : Polynomial ℝ) (p : ℕ) (hp : p.Prime) (x H : ℝ) :
    ‖(∑ m ∈ Work.BMF.natIcc (x / p) ((x + H) / p),
        f (p * m) * Work.BMF.eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) φ)))
        - f p * Work.BMF.corr f (Work.BMF.dil (p : ℝ) φ) (x / p) (H / p)‖
      ≤ 2 * (((Work.BMF.natIcc (x / p) ((x + H) / p)).filter (fun m => p ∣ m)).card : ℝ) := by
  set I : Finset ℕ := Work.BMF.natIcc (x / p) ((x + H) / p) with hI
  -- Rewrite `corr` over the common summation range `[x/p, (x+H)/p]`.
  have hcorr : Work.BMF.corr f (Work.BMF.dil (p : ℝ) φ) (x / p) (H / p)
      = ∑ m ∈ I, f m * Work.BMF.eC (-((Work.BMF.dil (p : ℝ) φ).eval (m : ℝ))) := by
    simp only [Work.BMF.corr, hI]
    rw [add_div]
  -- Pointwise bound: the difference vanishes off the multiples of `p` and is `≤ 2` on them.
  have key : ∀ m ∈ I,
      ‖f (p * m) * Work.BMF.eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) φ))
        - f p * (f m * Work.BMF.eC (-((Work.BMF.dil (p : ℝ) φ).eval (m : ℝ))))‖
      ≤ (if p ∣ m then (2 : ℝ) else 0) := by
    intro m hm
    by_cases hpm : p ∣ m
    · rw [ite_eq_left hpm]
      have h1 : ‖f (p * m) * Work.BMF.eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) φ))‖ ≤ 1 := by
        rw [norm_mul, eC_norm_one, mul_one]; exact hf (p * m)
      have h2 : ‖f p * (f m * Work.BMF.eC (-((Work.BMF.dil (p : ℝ) φ).eval (m : ℝ))))‖ ≤ 1 := by
        simp only [norm_mul, eC_norm_one, mul_one]
        refine le_of_le_of_eq
          (mul_le_mul (hf p) (hf m) (norm_nonneg (f m)) (by norm_num : (0 : ℝ) ≤ 1)) (by ring)
      linarith [norm_sub_le (f (p * m) * Work.BMF.eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) φ)))
        (f p * (f m * Work.BMF.eC (-((Work.BMF.dil (p : ℝ) φ).eval (m : ℝ)))))]
    · have hcop : Nat.Coprime p m := (hp.coprime_iff_not_dvd).mpr hpm
      have hdil : (Work.BMF.dil (p : ℝ) φ).eval (m : ℝ) = Polynomial.eval ((p * m : ℕ) : ℝ) φ :=
        dil_eval_nat φ p m
      have hzero : f (p * m) * Work.BMF.eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) φ))
          - f p * (f m * Work.BMF.eC (-((Work.BMF.dil (p : ℝ) φ).eval (m : ℝ)))) = 0 := by
        rw [hmul p m hcop, hdil]; ring
      rw [ite_eq_right hpm, hzero]
      simp
  -- Sum the pointwise bounds.
  have hsum : ‖∑ m ∈ I, (f (p * m) * Work.BMF.eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) φ))
        - f p * (f m * Work.BMF.eC (-((Work.BMF.dil (p : ℝ) φ).eval (m : ℝ)))))‖
      ≤ 2 * ((I.filter (fun m => p ∣ m)).card : ℝ) := by
    calc ‖∑ m ∈ I, (f (p * m) * Work.BMF.eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) φ))
          - f p * (f m * Work.BMF.eC (-((Work.BMF.dil (p : ℝ) φ).eval (m : ℝ)))))‖
        ≤ ∑ m ∈ I, ‖f (p * m) * Work.BMF.eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) φ))
          - f p * (f m * Work.BMF.eC (-((Work.BMF.dil (p : ℝ) φ).eval (m : ℝ))))‖ :=
            norm_sum_le _ _
      _ ≤ ∑ m ∈ I, (if p ∣ m then (2 : ℝ) else 0) := Finset.sum_le_sum key
      _ = ∑ m ∈ I.filter (fun m => p ∣ m), (2 : ℝ) := by rw [← Finset.sum_filter]
      _ = 2 * ((I.filter (fun m => p ∣ m)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- Assemble.
  rw [hcorr]
  have hsplit : (∑ m ∈ I, f (p * m) * Work.BMF.eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) φ)))
        - f p * (∑ m ∈ I, f m * Work.BMF.eC (-((Work.BMF.dil (p : ℝ) φ).eval (m : ℝ))))
      = ∑ m ∈ I, (f (p * m) * Work.BMF.eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) φ))
          - f p * (f m * Work.BMF.eC (-((Work.BMF.dil (p : ℝ) φ).eval (m : ℝ))))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsplit]
  exact hsum

end Work.BMF.SD
