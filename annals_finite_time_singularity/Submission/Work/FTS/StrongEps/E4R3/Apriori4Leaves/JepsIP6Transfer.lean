import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Jeps_IP6_transfer_proof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/JepsIP6Transfer.lean` — OPEN LEAF S1 (research-low)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 S1; REVIEW (b)).
Weighted near-self-adjointness of a symmetric `J_ε` at level six, with NO derivative loss — the
bilinear twin of `HkSq_Jeps_le`.  NOTE: the tree's `HkPair_Jeps_comm` / `IP6_Jeps_diff_le` both
lose a derivative (`k+1`) and are NOT this statement.
Route: in the log coordinates `(s, ζ) = (log z, log tan θ)` `J_ε` is convolution over all of `ℝ²`
with an even kernel (exactly self-adjoint for `ds dζ`), commutes with `D_z = ∂_s`, `D_θ = 2∂_t`
(`Commute.Dz_Jeps`, `Dth_Jeps`), and every weight of `IP6 1…1` times the Jacobian `z·sin2θ/2` is
log-Lipschitz (`HkSqAux.wdiv_shift_le`, `Wt_shift_le`, `logJac_shift_le`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps

set_option autoImplicit false

/-- **LEAF (S1), proved (session 23)** `|IP6(J_ε f, h) − IP6(f, J_ε h)| ≤ C ε |f|₆ |h|₆` for an even kernel. -/
theorem Jeps_IP6_transfer {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ Ioc (0 : ℝ) 1, ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ f h : Fn,
      Work.FTS.VocabO.HQo α 6 f → Work.FTS.VocabO.HQo α 6 h →
      |IP6o α (Jeps ρ ε f) h - IP6o α f (Jeps ρ ε h)|
        ≤ C * ε * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 h :=
  Work.FTS.StrongEps.E4R3.Apriori4Proofs.Jeps_IP6_transfer_proof hρ hρs

end Work.FTS.StrongEps.EpsE4Thr.E4R4
