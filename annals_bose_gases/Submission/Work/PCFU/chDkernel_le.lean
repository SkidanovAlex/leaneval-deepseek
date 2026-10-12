import ChallengeDeps
import Submission.Work.PCFU.ChDkernelAux
import Submission.Work.PCFU.chD_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.PCFU.chDkernel_le` — the kernel bound of the `(D)`-slot

The `(D)`-slot piece is closed by

    chDslot_le_of_kernelBound   (PROVED, `PCFU/ChDpieceAsm.lean`)
      + chDkernel_le            (THIS file)                       kernel bound
      + chDslot_le_of_kernel    (delegated)                       state-side reduction
      + chDA_arith / mu_ell_bounds / chDA_budget                  arithmetic

`Work.PCFU.chDkernel_le_aux` (`PCFU/ChDkernelAux.lean`) contains the whole assembly of the kernel
bound from the two Poisson-summation identities (`chDpoisson_uvSmear`, `chDpoisson_E`), the
face-layer alias bound (`chDaliasSum_le`), the Riemann–Lebesgue smallness of `chat W1fun`
(`W1fun_chat_small`) and the lattice mass of `χ̂` (`summable_chiHat_abs`), through `chDkernel_glue`;
only two inputs were left open there, and this file supplies them:

* `PCFU.chD_split`      — the pointwise decomposition
  `KχfrU − chDC = Σ'_d (χ_ℓ ⋆ chDkerE)(z+ℓd) + Σ'_{d≠0}(χ_ℓ ⋆ W1fun)(z+ℓd)`;
* `PCFU.chDW1sum_summable` — summability of the `W1fun` family over the lattice.

The statement below is the exact interface consumed by `chDslot_le_of_kernelBound`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The kernel bound of the `(D)`-slot.**  There are `K0 > 0` and a threshold `T : ℝ → ℕ` such
that, for every admissible `μ` in the regime (`R ≤ ℓ·chiR0`, `4R ≤ ℓ`) and every lattice size
`N ≥ T μ`, the `z`-kernel of the slot is bounded by `chDA v K0 μ / ℓ³`. -/
theorem chDkernel_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < BoseGases.a v)
    (fu : Work.BoseBoxFix.LowCut) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ (K0 : ℝ) (T : ℝ → ℕ), 0 < K0 ∧
      ∀ (μ : ℝ), 0 < μ → Work.BoseBoxFix.Adm v ε₀ μ →
        R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 →
        4 * R ≤ Work.BoseBoxFock.ellH v μ →
        ∀ (N : ℕ), T μ ≤ N → ∀ z : E3,
          ‖(((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ)) : ℂ)
            * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
                - Work.BoseBoxFock.PCFU.chDC h (Work.BoseBoxFock.ellH v μ) z)‖
            ≤ Work.BoseBoxFock.PCFU.chDA v K0 μ / (Work.BoseBoxFock.ellH v μ) ^ 3 := by
  refine Work.PCFU.chDkernel_le_aux (v := v) (h := h) hv hvrad hR hv_supp hav fu hε₀ ?_ ?_
  · intro μ hμ N hN hRℓ z
    exact Work.PCFU.chD_split hR hv hvrad hv_supp hμ hav hN hRℓ z
  · intro μ hμ z
    exact Work.PCFU.chDW1sum_summable (v := v) (h := h) hR hv_supp
      (Work.BoseBoxFock.ellH_pos v μ) z

end Work.PCFU
