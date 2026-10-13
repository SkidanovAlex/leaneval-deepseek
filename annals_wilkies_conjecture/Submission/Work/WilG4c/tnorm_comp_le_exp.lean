import Mathlib
import Submission.Work.WilG2.tnorm_comp_general
import Submission.Work.Wilkies.CG.Spec

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- If every derivative of `F` of order `≤ r` has norm `≤ 1` at the points `Φ x` and the jet
sum `Σ_{1≤k≤r} ‖D^k Φ x‖/k!` is bounded by `S` on the open cube, then the composite `F ∘ Φ`
has `(T,r)`-jet norm at most `exp S` on the cube. -/
theorem tnorm_comp_le_exp {N r : ℕ} (S : ℝ) (hS : 0 ≤ S)
    (F : (Fin N → ℝ) → ℝ) (Φ : (Fin N → ℝ) → (Fin N → ℝ))
    (hF : ∀ x ∈ WilkiesDesign.openCube N, ContDiffAt ℝ r F (Φ x))
    (hΦ : ∀ x ∈ WilkiesDesign.openCube N, ContDiffAt ℝ r Φ x)
    (hFb : ∀ x ∈ WilkiesDesign.openCube N, ∀ m, m ≤ r → ‖iteratedFDeriv ℝ m F (Φ x)‖ ≤ 1)
    (hΦb : ∀ x ∈ WilkiesDesign.openCube N,
      ∑ k ∈ Finset.Ico 1 (r + 1), ‖iteratedFDeriv ℝ k Φ x‖ / (k.factorial : ℝ) ≤ S) :
    ∀ x ∈ WilkiesDesign.openCube N, WilkiesDesign.CG.tnorm r (F ∘ Φ) x ≤ Real.exp S := by
  intro x hx
  -- Abbreviate the inner jet sum of `Φ` at `x`.
  set T : ℝ := ∑ k ∈ Finset.Ico 1 (r + 1), WilkiesDesign.CG.jetCoeff k Φ x with hTdef
  have hT_nonneg : 0 ≤ T :=
    Finset.sum_nonneg fun k _ => WilkiesDesign.CG.jetCoeff_nonneg k Φ x
  have hT_le : T ≤ S := by
    rw [hTdef]
    refine le_trans (Finset.sum_le_sum fun k _ => le_of_eq rfl) (hΦb x hx)
  -- Subcompositionality of the jet norm (Faà di Bruno / exponential formula).
  have hcomp := Work.WilG2.tnorm_comp_general r Φ F x (hΦ x hx) (hF x hx)
  rw [← hTdef] at hcomp
  refine le_trans hcomp ?_
  calc ∑ p ∈ Finset.range (r + 1), WilkiesDesign.CG.jetCoeff p F (Φ x) * T ^ p
      ≤ ∑ p ∈ Finset.range (r + 1), S ^ p / (p.factorial : ℝ) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp_le : p ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
        -- the `p`-th Taylor coefficient of `F` at `Φ x` is at most `1/p!`.
        have hjet : WilkiesDesign.CG.jetCoeff p F (Φ x) ≤ 1 / (p.factorial : ℝ) :=
          div_le_div_of_nonneg_right (hFb x hx p hp_le) (Nat.cast_nonneg _)
        have hpT : T ^ p ≤ S ^ p := pow_le_pow_left₀ hT_nonneg hT_le p
        calc WilkiesDesign.CG.jetCoeff p F (Φ x) * T ^ p
            ≤ (1 / (p.factorial : ℝ)) * S ^ p :=
              mul_le_mul hjet hpT (pow_nonneg hT_nonneg p) (by positivity)
          _ = S ^ p / (p.factorial : ℝ) := by ring
    _ ≤ Real.exp S := Real.sum_le_exp_of_nonneg hS (r + 1)

end Work.WilG4c
