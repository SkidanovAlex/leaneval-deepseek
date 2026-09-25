import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.relT_defs
import Submission.Work.LT.chi_basic
import Submission.Work.LT.chi_orth
import Submission.Work.LT.relT_sl3E_basic
import Submission.Work.LT.relT_l2

namespace Work.LT

open Finset

/-! **Averaging identity over the column subgroup.**

`∑_{s,t} ‖L_{u(s,t)} f − f‖² = 2 p² ‖f − P_U f‖²`, written in Fourier terms as
`2 p² ∑_{z ≠ 0} ‖fhat_z f‖²`.

ROUTE. Apply the Plancherel identity (first hypothesis) to the function
`h := fun g => f (colU p a b c st * g) - f g`, whose `z`-th Fourier component is
`(chi p z st - 1) • fhat p a b c z f` by linearity of `fhat` in `f` and the eigenrelation
(second hypothesis). Then swap the two finite sums, and evaluate
`∑_{st} Complex.normSq (chi p z st - 1) = ∑_{st} (2 - 2 * (chi p z st).re) = 2*p² - 2*p²*[z = 0]`,
using `Complex.normSq_eq_norm_sq`, `|chi p z st| = 1` (`chi_basic` gives `chi p z st ≠ 0` and
`star (chi p z st) = chi p (-z) st`, so `Complex.normSq (chi p z st) = 1`) and the orthogonality
sum `∑_{st} chi p z st = p² * [z = 0]` (`chi_orth`). Finally rewrite the `if z = 0 then 0 else ...`
sum as a sum over `Finset.univ.filter (fun z => z ≠ 0)`. Pure finite bookkeeping: no analysis. -/

/-! ## Elementary matrix and character bookkeeping -/

/-- The column subgroup is closed under multiplication. -/
lemma relT_avg_colU_mul (p : ℕ) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (st st' : ZMod p × ZMod p) :
    colU p a b c st * colU p a b c st' = colU p a b c (st + st') :=
  (relT_sl3E_basic).2.2.2.2 p hab hac hbc st.1 st'.1 st.2 st'.2

/-- The column subgroup is abelian. -/
lemma relT_avg_colU_comm (p : ℕ) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (st st' : ZMod p × ZMod p) :
    colU p a b c st * colU p a b c st' = colU p a b c st' * colU p a b c st := by
  rw [relT_avg_colU_mul p hab hac hbc st st', relT_avg_colU_mul p hab hac hbc st' st,
    show st + st' = st' + st from add_comm st st']

/-- Each character value `chi p z st` lies on the unit circle. -/
lemma relT_avg_normSq_chi (p : ℕ) [NeZero p] (z st : ZMod p × ZMod p) :
    Complex.normSq (chi p z st) = 1 := by
  simp only [chi, ZMod.stdAddChar_apply]
  exact Circle.normSq_coe _

/-- Averaging `‖χ_z(u(s,t)) − 1‖²` over the column subgroup:
`∑_{s,t} ‖χ_z(u(s,t)) − 1‖² = 2 p²` for `z ≠ 0`, and `= 0` for `z = 0`. -/
lemma relT_avg_chi_normSq_sum (p : ℕ) [NeZero p] (z : ZMod p × ZMod p) :
    ∑ st : ZMod p × ZMod p, Complex.normSq (chi p z st - 1)
      = if z = 0 then 0 else 2 * (p : ℝ) ^ 2 := by
  have h1 : ∀ st : ZMod p × ZMod p, Complex.normSq (chi p z st - 1) = 2 - 2 * (chi p z st).re := by
    intro st
    rw [Complex.normSq_sub, relT_avg_normSq_chi, Complex.normSq_one]
    norm_num
  rw [Finset.sum_congr rfl (fun st _ => h1 st)]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Complex.re_sum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card]
  rw [(chi_orth p).2.1 z]
  have hre : ((p : ℂ) ^ 2).re = (p : ℝ) ^ 2 := by
    have h : (p : ℂ) = ((p : ℝ) : ℂ) := by simp
    rw [h, ← Complex.ofReal_pow]
    exact Complex.ofReal_re _
  split_ifs with hz
  · rw [nsmul_eq_mul, hre]; push_cast; ring
  · rw [nsmul_eq_mul, Complex.zero_re]; push_cast; ring

/-! ## Fourier components of `L_{u(s,t)} f − f` -/

/-- `fhat` is additive in its function argument. -/
lemma relT_avg_fhat_sub (p : ℕ) [NeZero p] (a b c : Fin 3) (z : ZMod p × ZMod p)
    (h₁ h₂ : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ) :
    fhat p a b c z (h₁ - h₂) = fhat p a b c z h₁ - fhat p a b c z h₂ := by
  funext g
  simp only [fhat, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_div]

/-- Translating the function or translating the argument give the same Fourier coefficient
(the column subgroup is abelian). -/
lemma relT_avg_fhat_translate (p : ℕ) [NeZero p] {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ) (z st : ZMod p × ZMod p)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) :
    fhat p a b c z (fun x => f (colU p a b c st * x)) g
      = fhat p a b c z f (colU p a b c st * g) := by
  simp only [fhat]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [← mul_assoc, relT_avg_colU_comm p hab hac hbc st x, mul_assoc]

/-- The `z`-th Fourier component of the difference `L_{u(s,t)} f − f` is
`(chi p z st − 1) • fhat p a b c z f`. -/
lemma relT_avg_fhat_colU_sub (p : ℕ) [NeZero p] {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
    (heig : ∀ (st z : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
        fhat p a b c z f (colU p a b c st * g) = chi p z st * fhat p a b c z f g)
    (st z : ZMod p × ZMod p) :
    fhat p a b c z (fun g => f (colU p a b c st * g) - f g)
      = (chi p z st - 1) • fhat p a b c z f := by
  have hA : fhat p a b c z (fun g => f (colU p a b c st * g))
      = fun g => fhat p a b c z f (colU p a b c st * g) := by
    funext g
    exact relT_avg_fhat_translate p hab hac hbc f z st g
  have hsplit : (fun g => f (colU p a b c st * g) - f g)
      = (fun g => f (colU p a b c st * g)) - f := by
    funext g; rfl
  rw [hsplit, relT_avg_fhat_sub, hA]
  funext g
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [heig st z g]
  ring

/-! ## The averaging identity -/

theorem relT_avg_id :
    ∀ (p : ℕ) [NeZero p] {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c →
      ∀ f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ,
        (∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ),
            l2sq h = ∑ z : ZMod p × ZMod p, l2sq (fhat p a b c z h)) →
        (∀ (st z : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
            fhat p a b c z f (colU p a b c st * g) = chi p z st * fhat p a b c z f g) →
        ∑ st : ZMod p × ZMod p, l2sq (fun g => f (colU p a b c st * g) - f g)
          = 2 * (p : ℝ) ^ 2 * ∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => z ≠ 0),
              l2sq (fhat p a b c z f) := by
  intro p _ a b c hab hac hbc f hplan heig
  have hnorm : ∀ st z : ZMod p × ZMod p,
      l2sq (fhat p a b c z (fun g => f (colU p a b c st * g) - f g))
        = Complex.normSq (chi p z st - 1) * l2sq (fhat p a b c z f) := by
    intro st z
    rw [relT_avg_fhat_colU_sub p hab hac hbc f heig st z, l2sq_smul]
  calc ∑ st : ZMod p × ZMod p, l2sq (fun g => f (colU p a b c st * g) - f g)
      = ∑ st : ZMod p × ZMod p, ∑ z : ZMod p × ZMod p,
          Complex.normSq (chi p z st - 1) * l2sq (fhat p a b c z f) := by
        apply Finset.sum_congr rfl
        intro st _
        rw [hplan]
        exact Finset.sum_congr rfl fun z _ => hnorm st z
    _ = ∑ z : ZMod p × ZMod p, ∑ st : ZMod p × ZMod p,
          Complex.normSq (chi p z st - 1) * l2sq (fhat p a b c z f) := by
        rw [Finset.sum_comm]
    _ = ∑ z : ZMod p × ZMod p,
          (∑ st : ZMod p × ZMod p, Complex.normSq (chi p z st - 1))
            * l2sq (fhat p a b c z f) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.sum_mul]
    _ = ∑ z : ZMod p × ZMod p,
          (if z = 0 then 0 else 2 * (p : ℝ) ^ 2) * l2sq (fhat p a b c z f) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [relT_avg_chi_normSq_sum p z]
    _ = ∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => z ≠ 0),
          2 * (p : ℝ) ^ 2 * l2sq (fhat p a b c z f) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : z = 0
        · simp [hz]
        · simp [hz]
    _ = 2 * (p : ℝ) ^ 2 * ∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => z ≠ 0),
          l2sq (fhat p a b c z f) := by
        rw [Finset.mul_sum]

end Work.LT
