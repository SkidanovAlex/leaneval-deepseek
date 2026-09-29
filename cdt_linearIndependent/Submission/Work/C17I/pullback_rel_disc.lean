import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.lc_defs
import Submission.Work.C17I.subst_eval_abs
import Submission.Work.C17I.summable_of_rate_bound
import Submission.Work.C17I.evp_poly
import Submission.Work.C17I.evp_poly_mul
import Submission.Work.C17I.evp_sum
import Submission.Work.C17I.yC_norm_lt_fifth

/-!
# The pullback relation on the disc `‖z‖ ≤ 34/100`

Given a `ℚ`-linear relation `∑ᵢ Pᵢ · fᵢ = 0` among the seventeen power series
`fᵢ = Submission.CDTPlan.seventeen m n ra rb rab r0 i`, together with a geometric coefficient
bound `‖[yᵏ]fᵢ‖ · Rᵢᵏ ≤ Cᵢ` where every `Rᵢ > 1/5`, the relation may be *evaluated* at every
point `w = yC z` with `‖z‖ ≤ 34/100`: since `‖w‖ ≤ (34/100)²/(1 - 34/100) = 289/1650 < 1/5`
(`Work.C17I.yC_norm_lt_fifth`), the point `w` lies inside every disc of convergence
(`Work.C17I.summable_of_rate_bound`).

The content is that the evaluation functional `evp f z = ∑' k, [yᵏ]f · zᵏ` is linear over finite
sums (`Work.C17I.evp_sum`) and multiplicative against a polynomial factor
(`Work.C17I.evp_poly_mul`, from the Cauchy product formula `Work.CPull.evpMul`), so that the
double sum `∑ᵢ ∑' k` may be reorganised as `∑' k ∑ᵢ`, where the inner sum is the `k`-th
coefficient of the (vanishing) formal combination `∑ᵢ Pᵢ fᵢ`.
-/

namespace Work.C17I

open PowerSeries
open scoped BigOperators

noncomputable section

theorem pullback_rel_disc (m n : ℕ) (ra rb rab r0 : ℤ) (P : Fin 17 → Polynomial ℚ)
    (hrel : ∑ i : Fin 17, (P i : PowerSeries ℚ)
        * Submission.CDTPlan.seventeen m n ra rb rab r0 i = 0)
    (hbou : ∀ i : Fin 17, ∃ C R : ℝ, 0 < C ∧ (1 : ℝ) / 5 < R ∧ R ≤ 1 ∧ ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDTPlan.seventeen m n ra rb rab r0 i) : ℚ) : ℂ)‖ * R ^ k ≤ C) :
    ∀ z : ℂ, ‖z‖ ≤ (34 : ℝ) / 100 →
      ∑ i : Fin 17, (P i).eval₂ (algebraMap ℚ ℂ) (Work.C17.yC z)
        * (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDTPlan.seventeen m n ra rb rab r0 i) : ℚ) : ℂ)
            * (Work.C17.yC z) ^ k) = 0 := by
  intro z hz
  -- the evaluation point `yC z` lies in every disc of convergence (radii `> 1/5`)
  have hw5 : ‖Work.C17.yC z‖ < 1 / 5 := yC_norm_lt_fifth z hz
  -- hence the coefficient series of each of the seventeen functions converges at `yC z`
  have hS : ∀ i : Fin 17, Summable (fun k : ℕ =>
      ((PowerSeries.coeff k (Submission.CDTPlan.seventeen m n ra rb rab r0 i) : ℚ) : ℂ)
        * (Work.C17.yC z) ^ k) := by
    intro i
    obtain ⟨C, R, hC, hR5, _hR1, hb⟩ := hbou i
    exact summable_of_rate_bound hC (by linarith) hb (lt_trans hw5 hR5)
  -- evaluation is multiplicative against the polynomial factors
  have hprod := fun i : Fin 17 => evp_poly_mul (P i)
    (Submission.CDTPlan.seventeen m n ra rb rab r0 i) (Work.C17.yC z) (hS i)
  -- and additive over the finite sum, so the relation may be evaluated termwise
  calc ∑ i : Fin 17, (P i).eval₂ (algebraMap ℚ ℂ) (Work.C17.yC z)
        * (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDTPlan.seventeen m n ra rb rab r0 i) : ℚ) : ℂ)
            * (Work.C17.yC z) ^ k)
      = ∑ i : Fin 17, Work.CPull.evp ((P i : PowerSeries ℚ)
          * Submission.CDTPlan.seventeen m n ra rb rab r0 i) (Work.C17.yC z) :=
        Finset.sum_congr rfl (fun i _ => (hprod i).2)
    _ = Work.CPull.evp (∑ i : Fin 17, (P i : PowerSeries ℚ)
          * Submission.CDTPlan.seventeen m n ra rb rab r0 i) (Work.C17.yC z) :=
        (evp_sum Finset.univ
          (fun i : Fin 17 => (P i : PowerSeries ℚ)
            * Submission.CDTPlan.seventeen m n ra rb rab r0 i)
          (Work.C17.yC z) (fun i _ => (hprod i).1)).symm
    _ = Work.CPull.evp 0 (Work.C17.yC z) := by rw [hrel]
    _ = 0 := by simp

end

end Work.C17I
