import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6
import Submission.Work.FTS.StrongPersist.H6Rows.NZzero6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6B
import Submission.Work.FTS.StrongPersist.H6Rows.NstarRow
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.StrongPersist.SP6.EH6
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.bt_prod_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The linking identity between the three coefficient operators -/


/-! ## The reduction of `H6Pair` to the `ℋ⁶`-bound on `dynRHS` -/


/-! ## The target

The four rows feeding the assembly `H6Rows.H6Pair_of_rows_C6` are

* `H6Rows.N0pair6` — the `N₀`-pairing row,
* `H6Rows.Npair6 Ce hCe` — the `N`-pairing row,
* `H6Rows.muBdd_of_zeroModes (H6Rows.NZzero6 Ce hCe)` — the two scalars `μ̄`, `muDyn`
  (`muBdd_of_zeroModes` is proved in `H6Rows/ScalarRows.lean` on top of the *proved*
  `H6Pair6Aux.h6pair_N0_zero` and `H6Pair6Aux.transport_zero_le'`),
* `H6Rows.piecesC6 Ce` — the `C⁶`-regularity of the two pieces, which is what `IP6AddFin`
  consumes to split the pairing (`SmoothOpen` of the pieces is *false* for honest `H6Adm`
  data — see `NOTES_L3_lin_FALSE.md` — and is not needed). -/
/-- **`H6Pair_ones3` — the level-six pairing bound for `IP6 1…1`.**

*Status.*  **Complete and `sorry`-free.**  The four inputs of the assembly
`H6Rows.H6Pair_of_rows_C6` are all proved and axiom-clean:
`H6Rows.N0pair6`, `H6Rows.Npair6B` (the `N`-pairing row, proved after the lead's ruling of
2026-10-10 — the earlier `H6Rows/Npair6.lean` stub is superseded and no longer imported),
`H6Rows.muBdd_of_zeroModes ∘ H6Rows.NZzero6` and `H6Rows.piecesC6`; this file's axioms are
`[propext, Classical.choice, Quot.sound]`.

The ruling (curric-46; `LEAD_strong_iface.md`, `REVIEW_strong_iface.md`,
`LEAD_strong_iface.lean.txt`) established that `Npair6` is derivable from `L6Ctx` exactly as
stated and that `L6Ctx` must **not** be strengthened.  The per-summand refutations that earlier
sessions recorded assume a coefficient priced through its `L²`-norms (their witness has
unbounded `∂_θA`); the row's true coefficient `-2α·Vop(Ξ)` has bounded `∂_θ`, supplied *inside*
`L6Ctx` by `Ell6Ctx.hgo.Vth` (`CoefThMem 1`, `≤ Ce α^{-1/2} Xn f`) and `Ell6Ctx.hstar.Vth`
(`CoefThMem 3`, `≤ Cs α`), and the obstructed summand `(a,b,a₁,b₁) = (1,5,1,0)` is closed by the
σ-divisibility identity `D_θA = sin(2θ)∂_θA`.  Those lemmas are in this area as
`H6Rows.mismatch_pt`, `H6Rows.mismatch_int`, `H6Rows.abs_pth_le_coefTh` and `L6Ctx.pth_Vop_le`
(`Submission/Work/FTS/StrongPersist/H6Rows/MismatchSummand.lean`).

Every other input of the assembly is *proved*:

* `H6Rows.N0pair6` — the `N₀`-row,
* `H6Rows.muBdd_of_zeroModes (H6Rows.NZzero6 Ce hCe)` — the scalars `μ̄`, `muDyn`
  (`muBdd_of_zeroModes` is in `H6Rows/ScalarRows.lean`, on top of the proved
  `H6Pair6Aux.h6pair_N0_zero` and `H6Pair6Aux.transport_zero_le'`),
* `H6Rows.piecesC6 Ce` — the `C⁶`-regularity that `IP6AddFin` consumes (`SmoothOpen` of the
  pieces is *false* for honest `H6Adm` data — `NOTES_L3_lin_FALSE.md` — and is not needed),
* `H6Rows.H6Pair_of_rows_C6` — the assembly, which additionally uses the *proved* rows
  `H6Rows.AK_pair_le` (`AK α` is a fixed `ℋ⁶`-function) and `H6Rows.nstar_pair_le` (the
  `D_z`-self-pairing; note `|μ + λ + μλ| ≤ 2|μ| + 2` for `λ = lamfun μ`, by
  `Nonlin.lamfun_add` and the totalisation `lamfun (-1) = 0`).

**Superseded as well.**  The "obstruction is certified for `α < 1/30`" paragraph that stood here is
withdrawn for the same reason as above: it is a statement about the *per-summand* estimates, whose
hypotheses price the coefficient in `L²` (witness `A` with unbounded `∂_θA`); the row's coefficient
`-2α·Vop(Ξ)` has bounded `∂_θ` inside `L6Ctx`.  The refutation records it cites
(`H6Pair6Aux/T6Gen/NOTES_T6RowGen_FALSE.md`, `H6Rows/Npair6SupAux/NOTES_SlotDzMulLe_FALSE.md`,
`N6Trans/SixAux/NOTES_supDzSix_REFUTED.md`) remain valid for *those* statements; they do not
refute the row, and they do not license any change to `L6Ctx`. -/
theorem H6Pair_ones3 : ∀ Ce : ℝ, 0 < Ce → ∃ α₂ Cp : ℝ, 0 < Cp ∧ 0 < α₂ ∧
    Work.FTS.StrongPersist.H6Pair (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) α₂ Ce Cp := by
  intro Ce hCe
  exact Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6 (Ce := Ce) hCe
    Work.FTS.StrongPersist.H6Rows.N0pair6
    (Work.FTS.StrongPersist.H6Rows.Npair6B Ce hCe)
    (muBdd_of_zeroModes (Ce := Ce) (Work.FTS.StrongPersist.H6Rows.NZzero6 Ce hCe))
    (Work.FTS.StrongPersist.H6Rows.piecesC6 Ce)

end Work.FTS.StrongPersist
