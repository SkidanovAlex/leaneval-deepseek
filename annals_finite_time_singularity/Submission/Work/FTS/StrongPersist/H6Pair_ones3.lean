/-
# `Work.FTS.StrongPersist.H6Pair_ones3` — the level-six pairing bound at the concrete `IP6`

The target is

```
theorem H6Pair_ones3 : ∀ Ce : ℝ, 0 < Ce → ∃ α₂ Cp : ℝ, 0 < Cp ∧ 0 < α₂ ∧
    H6Pair (IP6 1 1 1 1 1 1 1 1 1 1) α₂ Ce Cp
```

**State (see `H6Pair_ones3_NOTES.md` for the full analysis).**  `H6Pair` prices the nonlinear
right-hand side of the modulated `g`-equation against the `ℋ⁶`-norm (`Sq6`): for every context
`L6Ctx α M Ce Cs E Φs g Φ τ`,

`|IP6 α (dynRHS α Φ g τ) (slice g τ)| ≤ Cp · α^{-10} · (1+M)^4 · (1 + Sq6 α (slice g τ))`.

**Note on the bundle (this task ran through a repair of `Defs.lean`).**  When the statement was
reviewed, `L6Ctx` still carried the single-structure `Ell6Data`, which priced the transported
residual by its *level-four* ratios and was in fact unsatisfiable (the `F_*`-part of the
residual has `Rop = O(z)`, so no honest `ℋ⁴`-membership holds).  During this task the area
replaced it by the **split level-six context** `Ell6Ctx α Ce Cs E Φs f Φ` =
`StarPkgo2 α Cs Φs` (the `𝒲^{4,∞}` star data) + `EllPkgK α 6 Ce f (E f)` (the *level-six* ratios
for the perturbation `Rop/Uop/Vop`) + `Φ = Φs + E f`, and `H6Pair.pair` now quantifies over
`(g Φ) (τ M Cs) (E) (Φs)`.  So the statement now *does* contain the level-six elliptic data that
its conclusion needs.  The remaining obligation is exactly the level-six rows; `EllPkgK α 6`
supplies `HkNorm α 6` of the perturbation residual's three components, and the star half supplies
the `𝒲^{4,∞}`/`FlatW` data for the `F_*`-pieces.

Two facts are established below:

* `IP6_cs_coeffs` (proved, `StrongPersist/IP6_cs_coeffs.lean`) gives Cauchy–Schwarz for the
  concrete pairing, with an `α`-free constant `CC`.  Consequently **`H6Pair` follows from the
  single `ℋ⁶`-bound on `dynRHS`** — this is `H6Pair_of_Xn6Bound` below.  That bound is exactly
  the "k = 6 rows" obligation of `StrongPersist/NOTES.md` §5 item 2 (the level-six versions of
  the per-piece estimates of `FTS/NonlinRows`).
* The three coefficient operators of the self-similar vorticity equation satisfy the pointwise
  identity `ℛ(Ξ) = -2 sin²θ · (U(Ξ)/sin 2θ) + V(Ξ)` on the open quadrant
  (`Rop_eq_UopVop`), which is what lets a bound on the two fields (`EllPkgK.U`, `EllPkgK.V`,
  resp. the star `UsW`/`VW`) produce the `ℛ`-field (and conversely).

**Route (corrected — see `H6Pair_ones3_NOTES.md` §2 and §6).**  The earlier reduction
`H6Pair_of_Xn6Bound` (kept below, it is a correct *implication*) routes through an `ℋ⁶`-bound on
`dynRHS` — and that route is **dead**: `dynRHS` contains `D_z f`-terms with
`Xn6 (D_z f) ≤ Xn7 f`, while `L6Ctx` carries only `HkMem α 7 f` (no bound).  The live route is the
**slot-level pairing** of `dynRHS = -μ̄·AK + N₀ + N + N_*` against `f = slice g τ`, split over the
four pieces with `IP6AddFin` (which needs only `ContDiffOn ℝ 6` + `HkMem α 6` of the halves).
The four rows are the delegated `H6Rows/N0pair6`, `H6Rows/Npair6`, `H6Rows/NZzero6` (via
`H6Rows.muBdd_of_zeroModes`, proved) and the assembly `H6Rows/H6Pair_of_rows`; what is *proved*
here is the `ℛ`-`U`/`V` identity together with the two small rows `-μ̄·AK`
(`H6Rows.AK_pair_le`) and `N_*` (`H6Rows.NstarRow.nstar_pair_le`), the `ℋ⁶`-data of `AK α`
(`H6Rows.AK6_mem_norm`) and the scalar `rpow`-bookkeeping (`H6Rows/ScalarRows`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.IP6_cs_coeffs
import Submission.Work.FTS.StrongPersist.H6Rows.RowAux
import Submission.Work.FTS.StrongPersist.H6Rows.AK6Row
import Submission.Work.FTS.StrongPersist.H6Rows.NstarRow
import Submission.Work.FTS.StrongPersist.H6Rows.ScalarRows
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.H6Rows.FstarI12H6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.ip6_dz_self
import Submission.Work.FTS.StrongPersist.AK6.HkMem_AK6
import Submission.Work.FTS.StrongPersist.AK6.akRho_jet_bound6
import Submission.Work.FTS.StrongPersist.AK6.Sharp6
import Submission.Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6
import Submission.Work.FTS.Nonlinear.Open.Row23
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.StrongPersist.IP6Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.piecesC6
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6B
import Submission.Work.FTS.StrongPersist.H6Rows.NZzero6

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

/-- **`ℛ(Ξ) = -2 sin²θ · (U(Ξ)/sin 2θ) + V(Ξ)`** on the open quadrant.

This is the exact algebraic identity behind the `ℛ`-transfer of the elliptic chapter: the
`ℛ`-coefficient of (Relations) (tex 1320) is the combination
`ℛ(Ξ) = (2 sinθ Ξ + α sinθ z∂_zΞ + cosθ ∂_θΞ)/cosθ`, while
`U(Ξ) = -3Ξ - α z ∂_zΞ` and `V(Ξ) = ∂_θΞ - tanθ Ξ`; expanding the right-hand side reproduces
the numerator of `ℛ`.  Useful in both directions: it produces the `EllPkgK.R`-field from the
`U`/`V`-fields, and it shows that `ℛ(Ξ)` carries no singularity at `θ = 0, π/2` beyond the two
fields. -/
theorem Rop_eq_UopVop {α : ℝ} {Ξ : Fn} {z θ : ℝ} (hθ : 0 < θ)
    (hθ2 : θ < Real.pi / 2) :
    Work.Construction.Rop α Ξ z θ
      = -2 * Real.sin θ ^ 2
          * (Work.Construction.Uop α Ξ z θ / Work.Construction.s2 θ)
        + Work.Construction.Vop Ξ z θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ2⟩)
  have hsin : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [hθ2, Real.pi_pos]))
  have hs2 : Work.Construction.s2 θ = 2 * Real.sin θ * Real.cos θ := by
    rw [Work.Construction.s2_eq, Real.sin_two_mul]
  rw [Work.Construction.Rop, Work.Construction.Uop, Work.Construction.Vop, Work.Spaces.pz,
    Work.Spaces.pth, Real.tan_eq_sin_div_cos, hs2]
  field_simp
  ring

/-! ## The reduction of `H6Pair` to the `ℋ⁶`-bound on `dynRHS` -/

/-- **`H6Pair` follows from the `ℋ⁶`-bound on `dynRHS`.**  If, for the contexts of `L6Ctx`,
`|dynRHS|_{ℋ⁶}` is bounded by `K α^{-10} (1+M)^4 (1 + |slice g τ|_{ℋ⁶})`, then the level-six
pairing bound holds with `Cp = max 1 (2·CC·K)`, where `CC` is the Cauchy–Schwarz constant of
`IP6_cs_coeffs` (five lifts above `H1IP`, hence absolute).

This isolates the *only* analytic input of the level-six persistence argument: the level-six
rows (`StrongPersist/NOTES.md` §5 item 2). -/
theorem H6Pair_of_Xn6Bound {α₂ Ce K : ℝ} (hα₂ : 0 < α₂) (hK : 0 < K)
    (hbound : ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Fam) (τ M Cs : ℝ) (E : Fn → Fn) (Φs : Fn),
      0 ≤ τ → L6Ctx (IP6 1 1 1 1 1 1 1 1 1 1) α M Ce Cs E Φs g Φ τ →
      Xn6 α (dynRHS α Φ g τ)
        ≤ K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Xn6 α (slice g τ))) :
    ∃ Cp : ℝ, 0 < Cp ∧ H6Pair (IP6 1 1 1 1 1 1 1 1 1 1) α₂ Ce Cp := by
  obtain ⟨CC, hCCpos, hCS⟩ := IP6_cs_coeffs 1 1 1 1 1 1 1 1 1 1 α₂ hα₂
  refine ⟨max 1 (2 * CC * K), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  refine ⟨⟨lt_of_lt_of_le one_pos (le_max_left _ _), hα₂⟩, ?_⟩
  intro α hαIoc g Φ τ M Cs E Φs hτ hcx
  have hαpos : 0 < α := hαIoc.1
  have hrp : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hαpos.le _
  have hM4 : 0 ≤ (1 + M) ^ 4 := by positivity
  set f : Fn := slice g τ with hf
  set X : Fn := dynRHS α Φ g τ with hX
  have h1 : |IP6 1 1 1 1 1 1 1 1 1 1 α X f| ≤ CC * Xn6 α X * Xn6 α f :=
    hCS α hαIoc X f hcx.hrhs hcx.hreg.reg
  have h2 : Xn6 α X ≤ K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Xn6 α f) :=
    hbound α hαIoc g Φ τ M Cs E Φs hτ hcx
  have hf0 : 0 ≤ Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
  have hX0 : 0 ≤ Xn6 α X := Work.Spaces.HkNorm_nonneg α 6 X
  have hSq : Xn6 α f ^ 2 = Sq6 α f := by
    simp only [Work.FTS.StrongPersist.Xn6, Work.FTS.StrongPersist.Sq6, Work.Spaces.HkNorm]
    exact Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)
  have hcoef : 0 ≤ K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := by positivity
  have h3 : (1 + Xn6 α f) * Xn6 α f ≤ 2 * (1 + Sq6 α f) := by
    have hself : Xn6 α f ≤ 2 + Xn6 α f ^ 2 := by
      nlinarith [sq_nonneg (Xn6 α f - 1), hf0]
    nlinarith [hself, hSq]
  have key : Xn6 α X * Xn6 α f
      ≤ 2 * K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) := by
    have hb : Xn6 α X * Xn6 α f
        ≤ K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Xn6 α f) * Xn6 α f :=
      mul_le_mul_of_nonneg_right h2 hf0
    have h5 := mul_le_mul_of_nonneg_left h3 hcoef
    calc Xn6 α X * Xn6 α f
        ≤ K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Xn6 α f) * Xn6 α f := hb
      _ = K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * ((1 + Xn6 α f) * Xn6 α f) := by ring
      _ ≤ K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (2 * (1 + Sq6 α f)) := h5
      _ = 2 * K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) := by ring
  have h6 : CC * (Xn6 α X * Xn6 α f)
      ≤ CC * (2 * K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)) :=
    mul_le_mul_of_nonneg_left key hCCpos.le
  have h7 : CC * (2 * K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f))
      = (2 * CC * K) * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) := by ring
  have h8 : (2 * CC * K) * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)
      ≤ max 1 (2 * CC * K) * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) := by
    have hle : 2 * CC * K ≤ max 1 (2 * CC * K) := le_max_right _ _
    have hnn : 0 ≤ α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) := by
      have h1 := Work.Spaces.HkSq_nonneg α 6 f
      positivity
    calc (2 * CC * K) * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)
        = (2 * CC * K) * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)) := by ring
      _ ≤ max 1 (2 * CC * K) * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)) :=
            mul_le_mul_of_nonneg_right hle hnn
      _ = max 1 (2 * CC * K) * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) := by ring
  calc |IP6 1 1 1 1 1 1 1 1 1 1 α X f|
      ≤ CC * Xn6 α X * Xn6 α f := h1
    _ = CC * (Xn6 α X * Xn6 α f) := by ring
    _ ≤ CC * (2 * K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)) := h6
    _ = (2 * CC * K) * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) := h7
    _ ≤ max 1 (2 * CC * K) * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) := h8
    _ ≤ max 1 (2 * CC * K) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
          * (1 + Sq6 α f) := by
        have hE1 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 :=
          one_le_pow₀ (by have := abs_nonneg Ce; have := abs_nonneg Cs; linarith)
        have h0 : (0 : ℝ) ≤ max 1 (2 * CC * K) * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
            * (1 + Sq6 α f) := by
          have h1 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hαpos.le _
          have h2 : 0 ≤ (1 + M) ^ 4 := by positivity
          have h3 : 0 ≤ 1 + Sq6 α f := by have := Work.Spaces.HkSq_nonneg α 6 f; linarith
          exact mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) h1) h2) h3
        calc max 1 (2 * CC * K) * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)
            = (max 1 (2 * CC * K) * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)) * 1 := by ring
          _ ≤ (max 1 (2 * CC * K) * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f))
                * (1 + |Ce| + |Cs|) ^ 4 := mul_le_mul_of_nonneg_left hE1 h0
          _ = max 1 (2 * CC * K) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
                * (1 + Sq6 α f) := by ring

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
