import Mathlib
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.pert2v2.end_const_le_seg
import Submission.Work.Pert.pert2v2.hornmap_segment_close

/-!
# `Work.Pert.pert2v2.Rlow_close_of_res` — the low band's `R_close` from the crux residual

`PertData.R_close` for the low piece `R = Work.Pert.Rlow f Qp' τ Φp φ m k dlow` reads

  `‖R w + 1/α - d.E w‖ < δ`.

By the definition `Rlow … w = Φp (invOn τ Qp' (f^[m] (φ w))) - m - k + dlow` this is exactly

  `‖[Φp (invOn τ Qp' (f^[m] (φ w))) - m - k - d.E w] + (dlow + k + 1/α)‖ < δ`,

so it is the sum of two independent quantities:

* the **crux residual** `‖Φp (invOn τ Qp' (f^[m] (φ w))) - m - k - d.E w‖` (`crux_limit_v3` gives
  it with `k = 0` on a compact `K`), and
* the **constant** `dlow + k + 1/α`, which with `dlow = d := cm - cp - 1/α` (the (A.4.2) constant of
  `Work.Pert.RBlock2.gate_T_relation_constant`) and `k = 0` is `cm - cp`, controlled by the **paper's
  (A.4.4)** `‖cm - cp‖ < δ/2`, which is `Work.Pert.pert2v2.end_const_le_seg` applied to the segment
  estimate produced by `Work.Pert.pert2v2.hornmap_segment_close`.

This file isolates the arithmetic; the two producers supply the hypotheses.
-/

namespace Work.Pert.pert2v2

/-- **Low-band `R_close` from the crux residual and the constant.**  General in the deck shift `k`
(the crux produces `k = 0`): if the residual at the level point is `< δ/2` and the constant
`dlow + k + 1/α` is `< δ/2` in norm, then the `R_close` inequality holds. -/
theorem Rlow_close_of_res {f Φp φ τ E : ℂ → ℂ} {Qp' : Set ℂ} {m : ℕ} {k : ℤ} {α dlow : ℂ}
    {δ : ℝ} {w : ℂ} (hδ : 0 < δ)
    (hres : ‖Φp (Work.Pert.invOn τ Qp' (f^[m] (φ w))) - (m : ℂ) - (k : ℂ) - E w‖ < δ / 2)
    (hc : ‖dlow + 1 / α‖ < δ / 2) :
    ‖Work.Pert.Rlow f Qp' τ Φp φ m k dlow w + 1 / α - E w‖ < δ := by
  have hsplit : Work.Pert.Rlow f Qp' τ Φp φ m k dlow w + 1 / α - E w
      = (Φp (Work.Pert.invOn τ Qp' (f^[m] (φ w))) - (m : ℂ) - (k : ℂ) - E w)
        + (dlow + 1 / α) := by
    rw [Work.Pert.Rlow]
    ring
  rw [hsplit]
  refine lt_of_le_of_lt (norm_add_le _ _) ?_
  linarith

/-- **The constant half of the low-band `R_close`.**  With the (A.4.2) relation
`dlow + 1/α = cm - cp` (`Work.Pert.RBlock2.gate_T_relation_constant`, i.e. `dlow` the constant
`cm - cp - 1/α`) and the paper's (A.4.4) `‖cm - cp‖ < δ/2`, the constant is `< δ/2`, so
`Rlow_close_of_res` applies with the crux residual. -/
theorem const_half_lt {α cm cp dlow : ℂ} {δ : ℝ}
    (hA42 : dlow + 1 / α = cm - cp) (h44 : ‖cm - cp‖ < δ / 2) :
    ‖dlow + 1 / α‖ < δ / 2 := by
  rw [hA42]; exact h44

end Work.Pert.pert2v2
