import Mathlib
import Submission.Work.WilkiesH.Interp.V2Defs
import Submission.Work.WilkiesH.Interp.V2Params
import Submission.Work.WilkiesH.Interp.V2Lemmas
import Submission.Work.WilkiesH.Interp.V2count.monoCount_factorial_lower
import Submission.Work.WilkiesH.Interp.V2lam.lamV_ge
import Submission.Work.WilkiesH.Interp.V2dV.dV_upper
import Submission.Work.WilkiesH.Interp.V2Q.log_QV_le
import Submission.Work.WilkiesH.Interp.V2rem.remV_lt
import Submission.Work.WilkiesH.Interp.V2tay.tayV_lt
import Submission.Work.WilkiesH.Interp.V2master.master_ineq
import Submission.Work.WilkiesH.Interp.V2db.dV_lt_bV
import Submission.Work.WilkiesH.Interp.V2qb.log_QV_sharp
import Submission.Work.WilkiesH.Interp.V2qb.q_bound_b_succ
import Submission.Work.WilkiesH.Interp.V2card.cardineq
import Submission.Work.WilkiesH.Interp.V2qd.q_bound_d
import Submission.Work.WilkiesH.Interp.V2qe.q_bound_eps

/-!
# Wilkie's conjecture for Pfaffian structures — the `v2` interpolation parameters

This file proves `Work.WilkiesH.Interp.exists_params_v2`: for every `μ` there is a polynomial
`q ∈ ℝ[D, g, log H]` such that for all `D, g, H` (with `1 ≤ H`) there exist
`b, d, ρ, ε, Q` satisfying

* the Siegel cardinality condition `(Q+1)^{N₁} > (2 N₁ ⌈ρ^{-b}⌉ Q + 1)^{m}`;
* `above μ b d Q ρ ε < liou μ d Q g H`;
* `b, b+1, ⌈1/ρ⌉^μ · d, log (1/ε) ≤ q(D, g, log H)`.

All parameters are the explicit ones of `V2Params`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilkiesH.Interp

open WilkiesConjecture

/-! ## The theorem -/

theorem exists_params_v2 (μ : ℕ) :
    ∃ q : MvPolynomial (Fin 3) ℝ, ∀ D g H : ℕ, 1 ≤ H →
      ∃ (b d : ℕ) (ρ ε : ℝ) (Q : ℕ),
        1 ≤ b ∧ 1 ≤ d ∧ 1 ≤ Q ∧ 0 < ρ ∧ 0 < ε ∧ ε < 1 ∧ Real.sqrt (μ : ℝ) * ρ ≤ 1 ∧
        (Q + 1) ^ (Work.WilkiesH.monoCount (μ + 1) d)
          > (2 * (Work.WilkiesH.monoCount (μ + 1) d * Nat.ceil (ρ ^ (-(b : ℤ))) * Q) + 1)
              ^ (Work.WilkiesH.monoCount μ b) ∧
        Work.WilkiesH.Interp.above μ b d Q ρ ε < Work.WilkiesH.Interp.liou μ d Q g H ∧
        (b : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q ∧
        (((b + 1 : ℕ) : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q) ∧
        (((Nat.ceil (1 / ρ)) ^ μ * d : ℕ) : ℝ)
          ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q ∧
        Real.log (1 / ε) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q := by
  refine ⟨qPoly μ, fun D g H hH => ?_⟩
  -- the numeric facts about the explicit parameters
  have hlam8 : 8 * g + 8 ≤ lamV μ g H :=
    V2lam.lamV_ge μ g H V2count.monoCount_factorial_lower
  have hlam1 : 1 ≤ lamV μ g H := by omega
  have hd := V2dV.dV_upper μ g (bV μ g H)
  have hM := V2master.master_ineq μ g H hH hd
  have hsharp := V2qb.log_QV_sharp μ g H hlam8
  have hA := ineqA μ g H hH hlam8 hsharp hM
  have hB := ineqB μ g H hH hsharp hM
  have hdb := V2db.dV_lt_bV μ g H hH hd
  have htay := V2tay.tayV_lt μ g H hH hA
  have hrem := V2rem.remV_lt μ g H hH hdb hB
  have hqb1 := V2qb.q_bound_b_succ μ D g H hH
  have hqb2 := V2qd.q_bound_d μ D g H hH hd
  have hqb3 := V2qe.q_bound_eps μ D g H hH hlam1 hd
  refine ⟨bV μ g H, dV μ g (bV μ g H), rhoV μ, epsV μ g H, QV μ g H, ?_⟩
  refine ⟨one_le_bV μ g H, one_le_dV μ g (bV μ g H), one_le_QV μ g H, rhoV_pos μ,
    epsV_pos μ g H hH, epsV_lt_one μ g H hH, sqrt_mu_mul_rhoV_le_one μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the Siegel cardinality condition
    exact V2card.cardineq μ g H hlam8
  · -- `above < liou`
    rw [above_eq_terms]
    have hpos := liou_pos' μ (dV μ g (bV μ g H)) (QV μ g H) g H (one_le_QV μ g H) hH
    have hlip := lipV_eq μ g H
    linarith [htay, hrem, hpos]
  · -- `b ≤ q`
    linarith [hqb1]
  · -- `b+1 ≤ q`
    have hcast : (((bV μ g H + 1 : ℕ)) : ℝ) = ((bV μ g H : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact hqb1
  · -- `⌈1/ρ⌉^μ d ≤ q`
    exact hqb2
  · -- `log (1/ε) ≤ q`
    exact hqb3

end Work.WilkiesH.Interp
