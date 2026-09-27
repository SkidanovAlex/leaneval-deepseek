import Mathlib
import Submission.Work.EQ.H0_fibre_defs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.fwdC_germC
import Submission.Work.EQ.HeteroGerm
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.invBranch_ugermC_noGamma

namespace Work.EQ

open Complex Metric Filter
open scoped Topology

/-- **The backward branch word of a chain is eventually the principal one.**

Context. `chainWord a p : ℤ → Bool` (`Work.EQ.H0_fibre_defs`) is the branch word of a chain: at
index `n` it records which of the two backward local branches of `p.1 (n+1)` the point `p.1 n` is
(it is `true` iff `p.1 n = invBranch a true (p.1 (n+1))`).  `IsChain a h p` says that consecutive
points are regular pairs, `ψ₁, ψ₂ ≠ 0`, and that the two tails are the germ tails:
`p.1 n = germC a h (λ^n ψ₁)` eventually, and `p.1 n = ugermC a h (λ^(-n) ψ₂)` eventually (as
`n → -∞`).

Claim: for `n` sufficiently negative, the backward branch is the principal one (`true`).

Why: for `n ≤ -M` the backward tail gives `p.1 n = ugermC a h (λ^(-n) ψ₂)` and
`p.1 (n+1) = ugermC a h (λ^(-n-1) ψ₂)`; writing `w = λ^(-(n+1)) ψ₂` (small for `n` very negative)
this says `p.1 n = ugermC a h (λ w)`, and near `0` the principal backward branch inverts the
unstable germ scaling: `invBranch a true (ugermC a h w) = ugermC a h (λ * w)`.  That identity is
the mirror conjugate of `fwdC (germC a h u) = germC a h (λ * u)`; it is provided by the delegated
lemma `Work.EQ.invBranch_ugermC_noGamma`. -/
theorem chainWord_eventually_true_neg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {p : ChainData} (hp : IsChain a h p) :
    ∃ M : ℕ, ∀ n : ℤ, n ≤ -((M : ℤ)) → chainWord a p n = true := by
  -- the principal backward branch inverts the unstable germ scaling near `0`
  obtain ⟨rho, hrho, hInv⟩ := invBranch_ugermC_noGamma ha0 ha1 hh
  -- the backward tail of the chain
  obtain ⟨M0, hM0⟩ := isChain_tail_bwd_z hp
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlamne : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0)
  -- choose `N` with `λ^j ‖ψ₂‖ < rho` for all `j ≥ N`
  have hlim : Filter.Tendsto (fun j : ℕ => (eqLam a) ^ j * ‖p.2.2‖) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const ‖p.2.2‖
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds hrho))
  set K : ℕ := max M0 N with hK
  have hM0K : M0 ≤ K := by rw [hK]; exact le_max_left _ _
  have hNK : N ≤ K := by rw [hK]; exact le_max_right _ _
  refine ⟨K + 1, fun n hn => ?_⟩
  have hn0 : n ≤ -((M0 : ℤ)) := by omega
  have hn1 : n + 1 ≤ -((M0 : ℤ)) := by omega
  -- the unstable parameter at index `n+1`
  set w : ℂ := (eqLam a : ℂ) ^ (-n - 1) * p.2.2 with hw
  have hj : N ≤ (-n - 1).toNat := by
    have h1 : (0 : ℤ) ≤ -n - 1 := by omega
    have h2 : ((-n - 1).toNat : ℤ) = -n - 1 := Int.toNat_of_nonneg h1
    have h3 : (N : ℤ) ≤ ((-n - 1).toNat : ℤ) := by rw [h2]; omega
    exact_mod_cast h3
  have hz : (eqLam a : ℂ) ^ (-n - 1) = (eqLam a : ℂ) ^ ((-n - 1).toNat) := by
    conv_lhs => rw [← Int.toNat_of_nonneg (show (0 : ℤ) ≤ -n - 1 by omega)]
    rw [zpow_natCast]
  have hnormw : ‖w‖ < rho := by
    rw [hw, hz, norm_mul, norm_pow]
    have hnlam : ‖(eqLam a : ℂ)‖ = eqLam a := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hlam0.le]
    rw [hnlam]
    calc (eqLam a) ^ (-n - 1).toNat * ‖p.2.2‖ ≤ (eqLam a) ^ N * ‖p.2.2‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hlam0.le hlam1.le hj) (norm_nonneg _)
      _ < rho := hN N le_rfl
  have hwmem : w ∈ Metric.ball (0 : ℂ) rho := by
    rwa [Metric.mem_ball, dist_zero_right]
  -- `p.1 n` is the unstable germ at `λ w`
  have hscale : (eqLam a : ℂ) ^ (-n) * p.2.2 = (eqLam a : ℂ) * w := by
    rw [hw]
    have hsplit : (eqLam a : ℂ) ^ (-n)
        = (eqLam a : ℂ) ^ (-n - 1) * (eqLam a : ℂ) ^ (1 : ℤ) := by
      rw [← zpow_add₀ hlamne]
      congr 1
      ring
    rw [hsplit, zpow_one]
    ring
  -- `p.1 (n+1)` is the unstable germ at `w`
  have hpt1 : (eqLam a : ℂ) ^ (-(n + 1)) * p.2.2 = w := by
    rw [hw, show (-n - 1 : ℤ) = -(n + 1) by ring]
  have hstep : p.1 n = ugermC a h ((eqLam a : ℂ) * w) := by
    rw [hM0 n hn0, hscale]
  have hp1 : p.1 (n + 1) = ugermC a h w := by
    rw [hM0 (n + 1) hn1, hpt1]
  have hfinal : p.1 n = invBranch a true (p.1 (n + 1)) := by
    rw [hstep, hp1]
    exact (hInv w hwmem).symm
  show brSign a (p.1 n) (p.1 (n + 1)) = true
  rw [brSign, ite_eq_left hfinal]

end Work.EQ
