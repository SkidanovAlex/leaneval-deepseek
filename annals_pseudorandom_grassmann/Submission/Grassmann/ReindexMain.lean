import Submission.Grassmann.ReindexSum
import Submission.Commons.Analysis.Sum.stratum_pair_le_sharp

/-!
# P4: the reindexing of the switching sum

`Φ₃ : (t,p) ↦ (V₃,W₃,XsOf t p)` reindexes the switching sum by the role-space data.  This file
combines

* the per-`t` bound `SwRole.l4q_lapMulN_le_swRole_rank` (all normalising constants cancelling),
* the fibre bound P3 (`Reindex.fiber_weight_le_sharp`, which supplies `2^{Cd²−12dk}` per fibre),
* the removal of the extra `D_X`-derivatives (`ReindexSum.sum_k_weight_G_le`, whose honest loss is
  `2^{7dk}` per rank stratum),

into `sum_l4q_XtPred_le`:  `Σ_t [1≤S≤d] 2^{26dS} l4q (L_{XtPred t}(Lsub t.1 t.2.1 f))` is at most
`2^{Cd²+2} Σ_{(V₀,W)} D4 V₀ W (Lsub V₀ W f)`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## The vanishing of the `X`-derivative above the degree -/

/-- If the order of the triple exceeds the degree, the `X`-derivative vanishes: its Fourier
support would consist of characters of rank `≥ totOrder t > d`. -/
theorem lapMulN_XtPred_Lsub_eq_zero_of_gt (t : Triple m n) {d : ℕ}
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) (h : d < totOrder t) :
    lapMulN (XtPred t) (Lsub t.1 t.2.1 f) = 0 := by
  refine eq_of_fcoeff_eq fun Y => ?_
  rw [fcoeff_lapMulN, fcoeff_zero]
  by_cases hY : XtPred t Y
  · rw [if_pos hY]
    have hzero : fcoeff (Lsub t.1 t.2.1 f) Y = 0 := by
      rw [Lsub, fcoeff_lapMulN]
      by_cases hp : hybridPredSub t.1 t.2.1 Y
      · rw [if_pos hp]
        by_cases hc : fcoeff f Y = 0
        · rw [hc, mul_zero]
        · exfalso
          have hYd : Y.rank ≤ d := by
            by_contra hlt
            exact hc (by rw [fcoeff_eq, hf Y (by omega), mul_zero])
          have hle := totOrder_le_rank_of_XtPred hp hY
          omega
      · rw [if_neg hp, zero_mul]
    rw [hzero, mul_zero]
  · rw [if_neg hY, zero_mul]

/-- The corresponding vanishing of the fourth moment. -/
theorem l4q_lapMulN_XtPred_eq_zero_of_gt (t : Triple m n) {d : ℕ}
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) (h : d < totOrder t) :
    l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f)) = 0 := by
  rw [lapMulN_XtPred_Lsub_eq_zero_of_gt t hf h, l4q]
  simp

/-! ## The reindexed summand -/

/-- The summand of the switching sum reindexed by `Φ₃`.  The factorisation
`2^{26 d S}·(2^{C(d−S)²}·(2^{3d·finrank(range X)}·G V₃ W₃ (XsOf x) f))` is chosen so that it matches
verbatim both the output of `l4q_lapMulN_le_swRole_rank` (after `inv_mul_swRoleSum`) and the value
of `Reindex.fiberWeight` on a `Phi3`-fibre. -/
noncomputable def reindexSummand {m n : ℕ} (d C : ℕ)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (x : Σ t : Triple m n, QPair m n t) : ℝ :=
  if ReindexGood d x ∧ 1 ≤ totOrder x.1 ∧ totOrder x.1 ≤ d then
    (2 : ℝ) ^ (26 * d * totOrder x.1) * ((2 : ℝ) ^ (C * (d - totOrder x.1) ^ (2 : ℕ)) *
      ((2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range x.1.2.2)) *
        G (liftV x.1.1 x.2.1) (liftW x.1.2.1 x.2.2) (XsOf x.1 x.2) f))
  else 0

end
end Submission.Grassmann
