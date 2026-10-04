import ChallengeDeps
import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.BPair_J_lin
import Submission.Work.Diff.STE.B3.contDiff_lamCoeff_seriesFun
import Submission.Work.Diff.STE.B3.mat_continuousOn_chi
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow
import Submission.Work.Diff.STE.B3.BPair_J_self_smooth
import Submission.Work.Diff.STE.B3.BPair_J_self
import Submission.Work.Diff.STE.B3.SymCalcStep2.R_J_contDiff
import Submission.Work.Diff.STE.B3.SymCalcStep2.R_Qk_contDiff
import Submission.Work.Diff.STE.B3.VarCoef.R_Qk_chartExpr
import Submission.Work.Diff.STE.B3.VarCoef.mat_csq_le_components
import Submission.Work.Diff.STE.B3.VarCoef.varLapPow_cut_comm_pairing
import Submission.Work.Diff.STE.B3.CPair_eq_L2re_periodisation
import Submission.Work.Diff.STE.B3.perTransferDef
import Submission.Work.Diff.STE.B3.VarCoef.R_Qk_chartExpr_sym
import Submission.Work.Diff.STE.B3.VarCoef.POp_swap_sub_star_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.perMatDefs
import Submission.Work.Diff.STE.B3.VarCoef.CPair_chart_term_eq_periodised
import Submission.Work.Diff.STE.B3.VarCoef.Rper_Qk_eq_perPhi_POp
import Submission.Work.Diff.STE.B3.VarCoef.sum_pairing_le
import Submission.Work.Diff.STE.B3.VarCoef.sum_mat_csq_le_ENormB
import Submission.Work.Diff.STE.B3.VarCoef.sum_commOp_pairing_le
import Submission.Work.Diff.STE.B3.VarCoef.sum_defect_pairing_le
import Submission.Work.Diff.STE.B3.VarCoef.POpStar_negB_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.POp_adjoint_L2re
import Submission.Work.Diff.STE.B3.SymCalcStep7.pairSharpAux
import Submission.Work.Diff.STE.B3.VarCoef.ChartCE
import Submission.Work.Diff.STE.B3.VarCoef.ChartCE_exists
import Submission.Work.Diff.STE.B3.Rper_eq_perPhi_perMat
import Submission.Work.Diff.STE.B3.VarCoef.sum_POp_sub_POpStar_isOrd
import Submission.Work.Diff.STE.B3.ENormSq_zero_le_ENormSq
import Submission.Work.Diff.STE.B3.VarCoef.perMat_contDiff
import Submission.Work.Diff.STE.B3.VarCoef.perPhiR_smooth_periodic
import Submission.Work.Diff.STE.B3.VarCoef.perMat_eq_of_eta_one
import Submission.Work.Diff.STE.B3.VarCoef.Rper_eq_perPhi_perMat_sigma
import Submission.Work.Diff.STE.B3.VarCoef.Rper_Qk_eq_perPhi_POp_sigma
import Submission.Work.Diff.STE.B3.VarCoef.mat_csq_le_components_sigma
import Submission.Work.Diff.STE.B3.VarCoef.sum_mat_csq_le_ENormB_sigma
import Submission.Work.Diff.STE.B3.VarCoef.pairTermDefs
import Submission.Work.Diff.STE.B3.VarCoef.pairTerm_decomp
import Submission.Work.Diff.STE.B3.VarCoef.chartTerm_eq_XP_sigma
import Submission.Work.Diff.STE.B3.VarCoef.pairTerm_decomp2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! ## ANALYSIS (session 5) — the statement is TRUE, but its proof needs a ΨDO commutator theorem

**Verdict: the statement is true; it is *not* provable with the tools present in this workspace.**
A full write-up is in `HANDOFF.md`, last section.  Summary of the verified facts:

* `[Qk, J] = Σ_{i,j} [Δ_i, S_j]` **exactly**, where `Δ_i := R_i* (Λ^k (R_i ·))` (order `2k`) and
  `S_j := R_j* (S_ε (R_j ·))` (order `0`) are *self-adjoint* for `BPair`; equivalently
  `J = id − K` with `K := id − J` (the chart-wise high-pass) and `[Qk,J] = −[Qk,K]`.
  The diagonal terms are the *elementary* multiplier commutators
  `[Δ_i,S_i] = R_i* ([Λ^k, M_{ψ_i²}] S_ε − [S_ε, M_{ψ_i²}] Λ^k) R_i` (Leibniz + the Friedrichs
  gain of `CSq_trunc_sub_le`, exactly as the requester's guidance describes).
* The **cross** terms `i ≠ j` are *not* multiplier commutators: at the level of components the
  operators `T_{ij} = Λ^k L_{ij} S_ε − S_ε L_{ij} Λ^k` (`L_{ij} = R_i R_j*`, the chart transfer) are
  each of order `2k`, not `2k−1`; numerically their `H^0 → H^{−k}` norm grows like `1.5/ε`.
  What *is* uniformly bounded is the section-level combination
  `R_i* T_{ij} R_j + R_j* T_{ji} R_i = [Δ_i,S_j] + [Δ_j,S_i]`, i.e. exactly the commutators.
* The mechanism is the standard order-reduction for ΨDOs with **scalar symbols on `T*M`**:
  `σ(Δ_i)(x,ξ) = ψ_i² λ(ξ_i(x,ξ))^k`, `σ(S_j)(x,ξ) = ψ_j² ρ(ε ξ_j(x,ξ))`; these commute as
  functions, so `[Δ_i,S_j]` has order `2k−1`, and since `∂_ξ ρ(εξ_j) = O(ε)` on
  `supp ρ' ⊆ {|εξ_j| ≤ 2}` the bound is **uniform in `ε ∈ (0,1]`**.  Numerical checks in a
  validated 1-D two-chart model (`τ(s)=s+δ sin(2πs)/(2π)`, `δ=0.4`, reconstruction and adjunction
  exact to `1e-14`): `‖d‖_{H^{−k}}/√(E_{k−1}f + E_0 f) ≈ 1.2` (`k=1`) and `≈ 0.03` (`k=2`), bounded
  as `1/ε` runs over `4 … 64`; diagonal-only and cross-only parts are separately bounded.
* The naive route fails and must not be attempted: `⟨Λ^k(RKf),Ru⟩` and `⟨Λ^kRf,R(Ku)⟩` are each
  `O(ε^{−k})` while their *difference* is `O(1)`: the cancellation (i.e. the pairing form, not the
  strong form) is essential.  The workspace's `STE/commutator_estimate.lean` is an energy-type
  *self-pairing* estimate `|⟨[P,∂^k]u, ∂^k u⟩| ≤ (λ/4)‖u‖²_{k+1} + C‖u‖²_k` and does not give this.
* Two concrete sub-jobs (boundary-free versions are needed in the target's context, which has
  neither `[T2Space M]` nor `[I.Boundaryless]`): `R_i* R_i = M_{ψ_i²}` / `Σ_i R_i* R_i = id`
  (cf. `B3/sum_Rstar_R_eq_id`, stated with `[I.Boundaryless]`), and the smoothness of the
  components of `J ρ ε f`, `Qk D k f` needed to invoke `ENormB_pair_J_commutator_eq_BPair`.

-/

/-! Guidance from the project lead (the requester):

This re-files Diff/STE/B3/ENormB_pair_J_commutator (H10-L2400, cancelled). The old statement assumed only ‖ρ‖ ≤ 1 and ρ 0 = 1, and in that generality it is FALSE. Take a bounded ρ with ρ(0) = 1 that oscillates wildly near 0. Then for a sequence ε_n → 0, ρ(ε_n m) alternates in sign for 1 ≤ |m| ≤ N_n with N_n → ∞. On those frequencies S_ε acts like a half-period translation, so [S_ε, M_c] gains no derivative and the ratio grows with the frequency of f. The old agent's numerical evidence only tested smooth profiles. With hρs (ρ smooth) and hρ0 (ρ supported in |y|² ≤ 2), the hypotheses are exactly those of gal_uniform_v2 (Diff/STE/Lead/gal_uniform_v2), the only consumer. Then ρ(ε·) is a symbol of order 0 uniformly in ε ∈ (0,1], and the Friedrichs commutator gain holds.
REUSE: the module Submission.Work.Diff.STE.B3.ENormB_pair_J_commutator is imported. Its theorem ENormB_pair_J_commutator_eq_BPair is PROVED (sorry-free) and reduces the left side to the pairing D.BPair ((Q_k ∘ J − J ∘ Q_k) f) u. READ that file's long header (§1–§4): it records the verified algebraic reduction, the diagonal/cross-term split, and two traps. Trap 1: the strong L² form of the commutator bound is FALSE, so only the pairing form can be proved. Do not use that module's theorem ENormB_pair_J_commutator itself (it is a sorry).
Key estimate (Friedrichs gain): for c smooth and compactly supported in the cube, |ρ(εm) − ρ(εn)| ≤ ‖∇ρ‖∞ · ε|m − n|. If |εm| ≤ √2 or |εn| ≤ √2, then ε ≤ C⟨m − n⟩/⟨n⟩ (Peetre). Hence the multiplier of [S_ε, M_c] is bounded by C⟨m − n⟩^{N}|ĉ(m − n)|/⟨n⟩, uniformly in ε ≤ 1, and Schur's test gives order −1. Existing tools: CSq_trunc_sub_le, CSq_STruncC_sub, BPair_J_self_smooth, ENormB_eq_BPair_Qk, pdVec_pair_eq_lambda.
Before writing any helper, grep Submission/Work/Diff/STE for an existing one. Before declare_proven, run python3 REFS/tools/dupcheck.py . | grep ENormB_pair_J_commutator.
-/

/-! ## SESSION 9 — DECISIVE: an *exact* two-chart model (machine precision) confirms the statement

Every numerical model used so far in this area was unreliable: the composition with a non-affine
transition was evaluated by trigonometric interpolation on a grid with **too few points**, so at the
frequencies `|ε m| ≃ 1` — the frequencies the statement is *about* — the operators were 10–100 %
wrong.  This session built a model in which the composition is evaluated by **quadrature that
resolves the integrand by a factor ≥ 4** and the operators are built in the real Fourier basis from
`∫ B_i(t) B_j(τ(t)) dt`; the transition is `τ(y) = y + 0.4 sin(2πy)/(2π)` (a diffeomorphism of the
circle, `τ' ∈ [0.6,1.4]`), the two charts are the two coordinate systems on the circle, the
densities are `dens₁ = 1`, `dens₂ = τ'`, and the weights satisfy `ψ₁² + ψ₂² = 1`.

**Sanity checks (all ≤ 1e-11 in the runs below, with the truncation diagnostic displayed):**
`Σ_j L_{ij}(R_jh) = R_ih` (reconstruction), `L_{12} = L_{21}^T` (adjunction), and the identity
`ENormB_pair k (Jf) u − ENormB_pair k f (Ju) = BPair([Qk,J]f,u)`.

⚠ **The one bug that produced all the conflicting readings of earlier sessions**: in the
*transpose* of the family operator `f ↦ R_i(Jf)` the factors `S_j` were dropped (the model computed
`(Σ_jL_{ij})^T` instead of `(Σ_jL_{ij}S_j)^T`).  With the factors in place the "linear growth in the
frequency" disappears and the ratio
`|ENormB_pair k (Jf) u − ENormB_pair k f (Ju)| / (√(E_{k−1}f + E_0 f) √(E_k u))`
is **bounded and frequency-independent** (e.g. `k = 1`: `0.93` at `ε = 1`, `0.33` at `ε = 0.3`,
`0.40` at `ε = 0.1`; `k = 2`: `31` / `3.2` / `0.91`), saturating as soon as the probe band exceeds
`1/ε`.  **The statement is TRUE.**  (The correct model is `_h2731/m5.py`, kept in the master tree.)

### The exact identity that organises the proof

Put `g := R_if`, `v := R_iu` (chart-`i` components), `Qc_i := Σ_j L_{ij}Λ_j^k(·)`,
`Jc_i := Σ_j L_{ij}S_j(·)` (the chart-`i` components of `Qk` resp. `J`), so that
`R_i(Jf) = Jc_i(Rf)`.  Since `S_j = 1 − HS_j` (high pass `HS_j = 1 − S_j`) and the reconstruction
`Σ_jL_{ij}(R_jh) = R_ih`,

  `ENormB_pair k (Jf) u − ENormB_pair k f (Ju) = Σ_i[⟨Λ_i^k(R_if), (Ku)_i⟩ − ⟨Λ_i^k(Kf)_i, R_iu⟩]`

with `K = id − J`; equivalently, with `ϑ_{ij} := S_iL_{ij}Λ_j^k − Λ_i^kL_{ij}S_j` (chart `j` →
chart `i`, **order `2k`, not `2k−1`**),

  **`Ξ(f,u) := ENormB_pair k (Jf) u − ENormB_pair k f (Ju) = Σ_{i,j} (R_if)·ϑ_{ij}(R_ju)`**,

the cleanest form of the reduction.  `ϑ_{ij}` is *antisymmetric under transposition*:
`ϑ_{ji} = −ϑ_{ij}^T` (this is why `Ξ(f,u) = −Ξ(u,f)`), so

  `Ξ = Σ_i (R_if)·ϑ_{ii}(R_iu) + Σ_{i<j} [ (R_if)·ϑ_{ij}(R_ju) + (R_jf)·ϑ_{ji}(R_iu) ]`.

### What the exact model says about the pieces (this settles the earlier dispute)

| piece | `k = 1`, band `Mp = 8,12,16,24,32` (with `ε = 1/Mp`) | verdict |
|---|---|---|
| diagonal `Σ_i(R_if)·ϑ_{ii}(R_iu)` | `3.77 3.77 3.77 3.77 3.77` | **bounded** |
| single cross `(R_if)·ϑ_{12}(R_ju)` | `2.03 3.24 4.65 7.26 9.92` | **grows linearly in the frequency** |
| cross *pair* `(0,1)+(1,0)` | `3.77 3.77 3.77 3.77 3.77` | **bounded** |
| total `Ξ` | `0.045 0.052 0.061 0.079 0.095` | **bounded** |

(and for `k = 2`: diagonal `≈ 71`, pair `≈ 71`, total `≈ 0.3`, all saturated).  So the earlier
header's claim is confirmed *in the corrected model*: **the individual cross terms are of order
`2k` and unbounded; the estimate holds only after the antisymmetrisation over the unordered pair
`{i,j}`**, and the diagonal is of order `2k−1` for the elementary Leibniz reason.

### The diagonal (provable with existing tools)

`ϑ_{ii} = S_iL_{ii}Λ_i^k − Λ_i^kL_{ii}S_i = −S_i[Λ_i^k,M_{ψ_i²}]` (because `L_{ii} = M_{ψ_i²}`, and
`S_i` commutes with `Λ_i^k`), and `[Λ_i^k,M_c]` is an order-`2k−1` differential operator with
bounded coefficients for every smooth `c` (Leibniz).  So the diagonal term is bounded by
`C‖f‖_{H^{k−1}}‖u‖_{H^k}` **provided** one uses the *physical-space* Leibniz expansion
`[Λ^k,M_c]v = Σ_{|α|≤2k−1}b_α∂^αv` (`b_α` bounded, smooth): then
`‖[Λ^k,M_c]v‖_{H^{1−k}} ≤ C‖v‖_{H^k}` because `∂^α` costs `|α| ≤ 2k−1` derivatives, and
`(1+|m|²)^{1−k} ≤ 1` for `k ≥ 1` makes the `H^{1−k}` pairing weight harmless.
⚠ Using only the **`CSq`-weighted strong form** `CSq 0([Λ^k,M_a]ψ) ≤ C·CSq(2k−1)ψ` is *not* enough:
it would produce `‖u‖_{H^{2k−1}}` on the right, and `CSq k ψ ≤ CSq (2k−1) ψ` is the wrong
direction (the weight `wt ≥ 1` grows).  **The missing tool is therefore the physical-space Leibniz
expansion with bounded coefficients** (not the already-proved weighted `CSq` version).

⚠ **The `sorry`-free tools that do exist** (verified this session with `#print axioms`):
`Work.Diff.STE.B3.SymCalcStep1.laplacian_pow_mul_comm_le` (module
`Submission/Work/Diff/STE/B3/SymCalcStep1/laplacian_pow_mul_comm_le.lean`) is proved with axioms
exactly `[propext, Classical.choice, Quot.sound]` — it does **not** use the sorried public
`SymCalcStep1.lam_pow_sub_sq_le` (it carries its own proved private pointwise bound).  Likewise
clean: `SymCalcStep1.flat_multiplier_commutator` (`[M_a,S_ε]` of order `−1`) and
`SymCalcStep6.conj_cut_comm_lapPow_le` (`[Λ^k,V]` of order `2k−1`).  The stale `sorry`s in
`B3/SymCalc.lean` (8 occurrences, *duplicates* of the same statements) must not be imported.

### ⚠ `hρs` (smoothness of `ρ`) is *essential* — independently confirmed by a reviewer this session

A reviewer built the workspace's two-chart model with the *admissible* sign square-wave
`ρ(y) = ±1` on `|y| < 1.4` (`‖ρ‖ ≤ 1`, `ρ 0 = 1`, supported in `{|y|² ≤ 2}`) and measured
`|Ξ|/(√(E_{k−1}f+E_0f)√(E_k u))`: it **grows without bound in the frequency of `f` even at fixed
`ε = 0.05`** (`k = 1`: `0.33 → 62.6`, `k = 2`: `1.8 → 169` as the band grows `4 → 48`), while a
smooth Friedrichs bump stays bounded.  This independently confirms the lead's diagnosis at the top
of this file: with only `‖ρ‖ ≤ 1` and `ρ 0 = 1` the Friedrichs gain fails, and `hρs` is what makes
`ρ(ε·)` a bounded family in `S⁰_{1,0}`.  **Any sub-lemma of the reduction must carry `hρs`** (a
first draft of the two-chart cross-pair statement without it was rejected by both reviewers for
exactly this reason).

### ⚠ The constant mode: every *sub*-piece must be regularised (found by the reviewers this session)

`ENormSq k u` (hence `E_k u`) **vanishes for a `u` whose chart components are constants** — all
`k`-th derivatives are `0`.  But `[Λ^k,M_c]u = Λ^k(cu) − c·Λ^ku = (const)·Λ^kc` is *not* zero for a
constant `u` with non-constant `c`.  So the diagonal piece `(R_if)·ϑ_{ii}(R_iu)` alone is **not**
bounded by `C‖f‖_{H^{k−1}}‖u‖_{H^k}`; it needs `√(E_k u + E_0 u)` (or `u ⟂ constants`).
This is harmless for the **target**, because the zero frequency is special: `λ(0) = 0`, so
`Λ^k` kills the mean, and for a `u` with constant components one has
`ENormB_pair k (Jf) u = ENormB_pair k f (Ju)` (`J` fixes such `u`: `S_ε` multiplies the `m = 0`
coefficient by `ρ 0 = 1`), i.e. `Ξ(f,u) = 0` while `E_k u = 0` — the target's inequality holds
trivially.  The assembly must therefore either split off the mean of `u` (`Ξ` is linear in `u` and
`Ξ(f, const) = 0`) or carry the regularised norms through and remove `E_0u` at the end.

**Delegated this session** (piece of the diagonal, statement reviewed): `Work.Diff.STE.B3.flat_diag_pairing_le`
(module `Submission/Work/Diff/STE/B3/flat_diag_pairing_le.lean`) — the flat diagonal pairing
`|⟨f, S_ε[Λ^k,M_c]u⟩| ≤ C√(E_{k−1}f+E_0f)·√(E_ku+E_0u)`, with `hk1 : 1 ≤ k` and `c` smooth
periodic.  Its proof route: the **physical-space Leibniz expansion** `[Λ^k,M_c]v = Σ_{|α|≤2k−1}b_α∂^αv`
with `b_α` bounded (compactness of the torus + smoothness of `c`), then
`∂^α : H^k → H^{1−k}` for `|α| ≤ 2k−1` and Cauchy–Schwarz.

### The cross pair (the remaining core, in flat form)

For `L := M_γ ∘ comp_σ : chart 2 → chart 1` (the transfer `L_{12}`, `σ = τ^{-1}`, `γ` smooth) and
`L^T = M_{γ'} ∘ comp_τ` its flat adjoint, and `S, Λ^k` the *own-chart* multipliers `ρ(εm)`,
`λ(m)^k = |2πm|^{2k}`, the pair to bound is

  `(R_1f)·[S_1L_{12}Λ_2^k − Λ_1^kL_{12}S_2](R_2u) + (R_2f)·[S_2L_{21}Λ_1^k − Λ_2^kL_{21}S_1](R_1u)`,

i.e. after `y = τ(x)` in the second term (all operators on chart-1 functions, `Λ̃ := comp_σΛ_2^kcomp_τ`,
`S̃ := comp_σS_2comp_τ`, `S' := comp_τS_1comp_σ`):

  `P = αf·[S_1M_γΛ̃^k − Λ^kM_γS̃](M_{β∘σ}u) + (τ'·β∘σ)f·[S'M_{γ∘τ}Λ^k − Λ̃^kM_{γ∘τ}S](M_αu)`,

with `α = ψ₁`, `β = ψ₂/√τ'` (both smooth with `Σ(α∘τ)² + (β√τ')² = 1`); the top-order symbols of
the four summands *do not* cancel separately — the cancellation happens only in the sum, which is
what the table above shows.  This is the piece that must be delegated.

### A sharper form of the cross pair (derived this session; recommended for the delegation)

Let `x := R_if`, `y := R_jf`, `v := R_iu`, `w := R_ju`, `ϑ := ϑ_{ij}`.  The pair is

  `P = x·ϑ(w) − (ϑ(y))·v`     (using `ϑ_{ji} = −ϑ^T`),

and the **reconstruction** `Σ_jL_{ij}(R_jh) = R_ih` gives, on the two charts,
`ψ_j²·x = L_{ij}y` and `ψ_j²·v = L_{ij}w` (and the mirror statements with `i`, `j` exchanged).
Substituting them (`ψ_i ≠ 0` on the support of the chart-`i` component) turns the pair into a
**single-chart bilinear form**:

  `P = x·Θ(v)`,   `Θ := ϑ_{ij} M_{ψ_i^{−2}} L_{ji} + L_{ij} M_{ψ_i^{−2}} ϑ_{ji}`  (chart `i` → chart `i`),

so the cross pair is bounded as soon as `Θ : H^k → H^{1−k}` is bounded uniformly in `ε`.  The
crux is that `Θ` is *not* the sum of two order-`2k` operators that happen to mesh: the two terms
carry the transition with `τ` resp. `τ^{−1}`, and their top-order symbols only cancel because the
**covector transformation inverts** (`B` for `L_{ij}`, `B^{−1}` for `L_{ji}`).  Anyone attacking
this should first re-derive the top symbols as functions on `T^*𝕋ⁿ` — the two summands must be
compared *after* transporting both to the chart-`i` frequency variable, which is exactly the step
that the coordinate-level algebra above (which transports only one of them) hides.

-/

/-! ## SESSION 7: the exact *component* decomposition of the commutator pairing

Read this together with the header of `B3/ENormB_pair_J_commutator.lean` (§1–§4) and of
`B3/SymCalc.lean`.  In a two-chart model on the circle (chart 1 = the circle parameter `z`,
chart 2 = the coordinate `w = τ z` with `τ x = x + 0.4 sin (2πx)/(2π)`, `ζ₁² + ζ₂² = 1`, every
`Λ^k` / `S_ε` applied in **its own chart's frequency variable**, as in the Lean definitions of
`B3Data.R`, `B3Data.STruncR` and `Qk`)

* the reconstruction `Σ_j L_{ij} R_j h = R_i h`, the adjunction `L_{12} = L_{21}^*`,
  `BPair h h = ‖h‖²_{L²}`, and the `Rstar` adjunction `BPair (Rstar_j u) k = CPair_j u (R_j k)`,
  hold to `≤ 1e-14`;
* the *individual* terms of the decompositions below are `1e3`–`1e6` times the total: the estimate
  is a cancellation, and no bound on the pieces separately can work.

### ⚠ The existing numerical models are NOT reliable at the frequencies that matter

All the two-chart models in this workspace (`B3comm/`, `B3comm2/`, and the independent one used by
the lead) evaluate the chart transition by *trigonometric interpolation on a grid*.  For a
non-affine `τ` the function `e^{2πi m σ(w)}` is **not band limited** (its instantaneous frequency
sweeps over `m·(Dσ)`), so at `|ε m| ≃ 1` — exactly the regime the statement is about — the
interpolation/quadrature error is large: in the chart-correct model the *exact* identity
`ENormB_pair k h h' = BPair (Qk D k h) h'` (`ENormB_eq_BPair_Qk`, **proved**, and for `k = 0` just
the reconstruction) fails by ≃ **13 %** at `m = 30, N = 96` and `m = 60, N = 188` (and by `1e-16` at
`m = 3, N = 64`).  In particular the observed "growth" resp. "boundedness" of the ratio
`|Δ| / (√(E_{k-1} f + E_0 f) √(E_k u))` at those frequencies is *numerical noise*, not mathematics:
both readings have been reported by different sessions with the same models.  **Do not draw any
conclusion about the truth of the target from these models**; an *exact* model (affine transition,
where the composition is diagonal in Fourier) or a fully symbolic/spectral computation is needed.
The `ΨDO` heuristic (see below) and the lead's derivative count both say the statement is TRUE, and
the *flat* pieces that they use are all proved in the workspace.

### Notation

`Δ_i := R_i^* (Λ_i^k (R_i ·))` (order `2k`), `J_j := R_j^* (S_j (R_j ·))` (order `0`), so
`Qk D k = Σ_i Δ_i`, `D.J ρ ε = Σ_j J_j` and

  `Δ := ENormB_pair k (J f) u − ENormB_pair k f (J u) = BPair ((Qk D k ∘ J − J ∘ Qk D k) f) u`

is the *proved* reduction `ENormB_pair_J_commutator_eq_BPair` (its three smoothness hypotheses are
discharged by `SymCalcStep2.R_J_contDiff` / `R_Qk_contDiff`).  Put `L_{ij} := R_i ∘ R_j^*`
(chart `j` → chart `i`; in the flat picture `L_{ij} = M_γ ∘ comp_τ` with
`γ = ψ_i (ψ_j ∘ τ) √|det Dτ|`, the *unitary* half-density transfer) and
`A_{ij} := [L_{ij}, S_ε] = L_{ij} S_j − S_i L_{ij}` (of order `0`, **not** `−1`).

### The exact identity (`⟨·,·⟩_i = CPair_i`; algebraic, and checked in a common-frequency model)

  `⟨[Δ_i, J_j] f, u⟩ = E(i,j) := ⟨Λ_i^k A_{ij} R_j f, R_i u⟩_i − ⟨Λ_i^k R_i f, A_{ij} R_j u⟩_i`,
  `Δ = Σ_{i,j} E(i,j)`;

and, pairwise,

* **diagonal** `E(i,i) = ½ (⟨B̂_{ii} R_i f, R_i u⟩_i − ⟨R_i f, B̂_{ii} R_i u⟩_i)` with
  `B̂_{ii} = 2 [M_{ψ_i²}, S_ε] Λ_i^k`, i.e. the **flat multiplier commutator** `[M_a, S_ε]` (order
  `−1`; `flat_multiplier_commutator`, proved) times `Λ^k`: order `2k−1`.  *This half is done.*
* **cross pair** `E(i,j) + E(j,i) = ⟨B̂_{ij} R_j f, R_i u⟩_i − ⟨R_i f, B̂_{ij} R_j u⟩_i` with

  `B̂_{ij} = [L_{ij}, S_ε] Λ_j^k + Λ_i^k [L_{ij}, S_ε] = [X̃_{ij}, S_ε]`,  `X̃_{ij} = L_{ij} Λ_j^k + Λ_i^k L_{ij}`

  — note the **anticommutator** `L Λ_j + Λ_i L`, *not* the commutator (the commutator form is off by
  a factor `2`).  This is where the whole difficulty sits.

### Where the gain has to come from (and where a naive bound fails)

Writing `T := comp_τ`, `V_{ij} := T S_j T^{-1}` (the *conjugated* cutoff, `= conjCut ρ ε T T'`) and
`[L, S_ε] = M_γ (V − S_i) T + [M_γ, S_ε] T`, the cross term splits into

* **good** (order `2k−1`, ε-uniform): `M_γ [Λ_i, V] T`, `[M_γ, S_ε] T Λ_j^k`, `Λ_i^k [M_γ, S_ε] T`,
  `[Λ_i, M_γ] (V − S_i) T` — each a product of one *Friedrichs gain* (`[M_a,S_ε]` order `−1`,
  proved) or of `[Λ_i,V]` (order `2k−1`: proved for `k = 1` as `conj_cut_comm_laplacian_le`, the
  exact identity for all `k` is `conjCut_lapPow_comm`, and the general-`k` estimate is delegated as
  `SymCalcStep6.conj_cut_comm_lapPow_le`) with order-`≤2k` factors;
* **bad** (order `2k`, *individually unbounded*): the pieces containing the difference of cutoffs
  `(V_{ij} − S_i)`, e.g. `M_γ (V − S_i) (Λ_i T + T Λ_j)`-type.  `V_{ij} − S_i` is a genuine order-`0`
  operator (affinely `ρ(ε m/λ) − ρ(ε m)`), so no separate bound on these pieces can hold; the
  estimate is true only after the **full antisymmetrisation**
  `⟨B̂ R_j f, R_i u⟩ − ⟨R_i f, B̂ R_j u⟩` (and `(i,j) ↔ (j,i)`) is taken — cf. Trap 1 of the sibling
  header.

### Consequence for the assembly

Any bound of the form `‖[Qk, J] f‖_{L²} ≤ C‖f‖_{H^{k−1}}` is false (Trap 1); the usable form is the
*pairing* along `CPair`, and the two halves `Q_i J_j`, `J_j Q_i` must never be bounded separately.
The remaining analytic task is exactly to show that the *sum* of the "good" and "bad" pieces above is
bounded by `C ‖f‖_{H^{k−1}} ‖u‖_{H^k}`; the flat inputs that exist are
`flat_multiplier_commutator`, `laplacian_pow_mul_comm_le`, `mulDeriv_comm_trunc_le`,
`laplacian_pow_mul_highpass_le`, `conj_cut_comm_laplacian_le`, `conjCut_lapPow_comm` and the
delegated `conj_cut_comm_lapPow_le`.
-/

/-! ## SESSION 11 — the mechanism, settled and cross-checked

The SESSION 9 `Θ`-formula is **right** and the present section only makes it precise and reduces it
to the (small) certificate list below; it uses **no** Fourier-integral-operator calculus, only
(i) the reconstruction, (ii) Friedrichs commutators `[M_a,S_ε]` (order `−1`, PROVED), (iii) the
multiplier `Λ^k` (order `2k`) and (iv) the two already-proved conjugation estimates
`conjCut_lapPow_comm` / `conj_cut_comm_lapPow_le`.

⚠ Both of the following two expressions are *correct* and equal (they differ by `BPair(Qkf,Ju) =
BPair(J(Qkf),u)`, i.e. by the self-adjointness of `J`); do not be misled into thinking one of them
is an error (I was, while writing this note):

  `Ξ = Σ_{i,l} [ ⟨Λ_i^kL_{il}S_l x_l, v_i⟩_i − ⟨Λ_i^kL_{il}S_l v_l, x_i⟩_i ]`                      (a)
  `Ξ = Σ_{i,l} [ ⟨Λ_i^kL_{il}S_l x_l, v_i⟩_i − ⟨S_iL_{il}Λ_l^k x_l, v_i⟩_i ]`                      (b)

(a) is obtained by pairing `Qk(Jf)` with `u` in the first term and `Qkf` with `Ju` in the second;
(b) by pairing `Qk(Jf)` with `u` in the first term and `J(Qkf)` with `u` in the second, using the
*definitional* expansions `R_i(Jh) = Σ_jL_{ij}S_jh_j` and `R_i(Qkh) = Σ_jL_{ij}Λ_j^kh_j`.  Form (b)
telescopes into the `ϑ`-form below; form (a) is the one in which the two halves of the *pair* are
individually visible.  ⚠ The `Λ` in (b) sits on `x_l` *inside* the sum over `l`, so the whole right
hand side is a single pairing `Σ_{il}⟨ϑ_{il}x_l,v_i⟩_i` — this is the form to use.

### Step 1 — the exact component expansion of `Ξ` (form (b))

With `x_i := R_i f`, `v_i := R_i u`, `L_{ij} := R_i ∘ R_j^*` (chart `j` ↦ chart `i`), the
reconstruction `Σ_j L_{ij} h_j = h_i` (in particular `L_{ii} = M_{ψ_i²}`) and the *definitions*

  `R_i(Jf) = Σ_j L_{ij}S_jx_j`,   `R_i(Qkf) = Σ_j L_{ij}Λ_j^kx_j`

(adjunction `BPair(R_i^* w,·) = ⟨w, R_i ·⟩_i`, `⟨·,·⟩_i` the flat `L²` pairing of the chart-`i`
components) give, exactly,

  `Ξ := ENormB_pair k (Jf) u − ENormB_pair k f (Ju) = BPair ([Qk, J] f, u)`
  `   = Σ_{i,l} ⟨ (Λ_i^k L_{il} S_l − S_i L_{il} Λ_l^k) x_l, v_i ⟩_i = − Σ_{i,l} ⟨ x_i, ϑ_{il} v_l ⟩_i`

with `ϑ_{il} := Λ_i^kL_{il}S_l − S_iL_{il}Λ_l^k` (chart `l` ↦ chart `i`), `ϑ_{li} = −ϑ_{il}^T`.

### Step 2 — the `ϑ_{ii}` (diagonal) pieces are order `2k−1` by themselves

`ϑ_{ii} = Λ_i^kM_{ψ_i²}S_i − S_iM_{ψ_i²}Λ_i^k = [Λ_i^k,M_{ψ_i²}]S_i + [M_{ψ_i²},S_i]Λ_i^k`
(the second equality uses `[Λ_i^k,S_i] = 0`; `[M_{ψ_i²}Λ_i^k,S_i] = M_{ψ_i²}[Λ_i^k,S_i] +
[M_{ψ_i²},S_i]Λ_i^k`).  Both terms are order `2k−1`: the first by the Leibniz certificate, the second
because `[M_{ψ_i²},S_i]` is a Friedrichs commutator (order `−1`) and `Λ_i^k` is order `2k`.

### Step 3 — the cross pair `{i,l}`, transported to a single chart

The two summands `⟨ϑ_{il}x_l,v_i⟩_i` and `⟨ϑ_{li}x_i,v_l⟩_l` of the pair `{i,l}` are combined by
substituting for `x_l` (in the first) and for `v_l` (in the second) the reconstruction restrictions

  `L_{li}x_i = ψ_i²x_l`,  `L_{li}v_i = ψ_i²v_l`     (⋆)

— which hold for *every* `i,l` with `ψ_i²x_l = (Σ_jL_{lj}x_j) − (Σ_{j≠i}L_{lj}x_j)`, a relation that
is exactly `L_{li}x_i = ψ_i²x_l` only when `ι₀ = {i,l}`; see the ⚠ below.  Under (⋆), and using
adjunction `L_{li} = L_{il}^*`, the pair becomes a *single-chart* bilinear form
`P_{il} = ⟨x_i, Θ_{il}v_i⟩_i` with `Θ_{il} = ϑ_{li}M_{ψ_i^{−2}}L_{il} + L_{il}M_{ψ_i^{−2}}ϑ_{il}`
(equivalently `Θ_{il} = A_{il} − A_{il}^*`, `A_{il} := ϑ_{li}M_{ψ_i^{−2}}L_{il}`).  Putting
`T := comp_{τ_{il}}` (chart `i` ↦ chart `l`), `T' := comp_{τ_{li}}`, `L_{il} = M_γ T`,
`L_{li} = M_{γ'}T'`, `Š := conjCut ρ ε T T'` (the chart-`l` cutoff in chart-`i` variables),
`Λ̌^k := conjLapPow k T T'`, and using `γγ'∘τ = ψ_i²ψ_l²` (which follows from
`L_{il}L_{li} = M_{ψ_i²ψ_l²}`), all four leading coefficients collapse to `ψ_l²` and

  **`Θ_{il} = [Λ_i^k, M_{ψ_l²}Š] + [M_{ψ_l²}Λ̌^k, S_i]`**   (exact, algebraic),


whose leading (`2k`-order) symbols cancel pairwise — at `(x,ξ)` the four pieces have symbols
`λ^kψ_l²ρ(εAξ)`, `−ρ(εξ)ψ_l²λ(Aξ)^k`, `ψ_l²λ(Aξ)^kρ(εξ)`, `−ψ_l²ρ(εAξ)λ^k` and the pairs cancel
identically.  Hence `Θ_{il}` is order `2k−1`, and expanding the two brackets
  `[Λ_i^k, M_{ψ_l²}Š] = [Λ_i^k,M_{ψ_l²}]Š + M_{ψ_l²}[Λ_i^k,Š]`,
  `[M_{ψ_l²}Λ̌^k, S_i] = M_{ψ_l²}[Λ̌^k,S_i] + [M_{ψ_l²},S_i]Λ̌^k`

exhibits the four terms as: Leibniz, `conj_cut_comm_lapPow_le` (`[Λ_i^k,Š]`), the conjugate
`[Λ̌^k,S_i]` (the same lemma with `T,T'` exchanged), and a Friedrichs commutator composed with
`Λ̌^k`.  ⚠ This last one is why the two *new* certificates below are stated for `Λ^k` and for
`conjLapPow k T T'` respectively: the Friedrichs gain for the *transported* cutoff `Š` is the
`[M_a, conjCut]` certificate, and its composition with `Λ̌^k` is handled by conjugating the
Friedrichs commutator back into the other chart.

⚠ **OPEN POINT for the assembly (do not skip it).** Step 3 uses (⋆), i.e. it eliminates `x_l` in
favour of `x_i` for a *single* `l`.  For `ι₀` with **three or more** charts the reconstruction only
gives `Σ_jL_{lj}x_j = x_l`, so `L_{li}x_i = ψ_i²x_l − Σ_{j∉{i,l}}L_{lj}x_j`: the extra summands are
absent from `Θ_{il}` and must be shown to cancel against the other pairs — the natural way is to
check that for fixed `i` the *whole* chart-`i` family
`Σ_lϑ_{il}x_l = Λ_i^kR_i(Jf) − S_iR_i(Qkf)` is order `2k−1` (this also covers the diagonal
`Σ_lϑ_{il}x_l` for `l=i`), by writing
`Λ_i^kR_i(Jf) − S_iR_i(Qkf) = S_i(Λ_i^kR_i(Jf) − R_i(Qkf)) + (1−S_i)(Λ_i^kR_i(Jf) − Λ_i^kx_i) +
(1−S_i)Λ_i^kx_i − S_i(R_i(Qkf) − Λ_i^kx_i)` and estimating each of the four pieces with the
certificates below (each is a product of *one* `Λ`/Friedrichs commutator with order-`≤2k` factors).
**The two-chart case (`ι₀ = {i,l}`) is fully accounted for by (⋆) and by the `Θ_{il}` identity.**

### Step 4 — the certificates (all flat)

| certificate | statement | status |
|---|---|---|
| Friedrichs gain | `CSq (s+1) (fourierCoeff ([M_a,S_ε]g)) ≤ K CSq s (fourierCoeff g)` | `SymCalcStep1.flat_multiplier_commutator` ✔ |
| Leibniz | `[Λ^k, M_a]` of order `2k−1` | `SymCalcStep1.laplacian_pow_mul_comm_le` ✔ |
| `Λ^k` order `2k` | `CSq s (fourierCoeff (Λ^kg)) ≤ K CSq (s+2k) (fourierCoeff g)` | `SymCalcStep6.lapPow_toolbox` ✔ |
| `Λ^k ∘ (order −1)` order `2k−1` | `CSq s (fourierCoeff (Λ^k ∘ (Friedrichs) g)) ≤ K CSq (s+2k−1) (fourierCoeff g)` | `SymCalcStep6.lapPow_Friedrichs_le` ✔ (proved this session) |
| conjugation | `[Λ^k, conjCut ρ ε T T']` of order `2k−1` | `SymCalcStep6.conj_cut_comm_lapPow_le` ✔ |
| `conjCut` Friedrichs gain | `CSq (s+1) (fourierCoeff ([M_a, conjCut ρ ε T T'] g)) ≤ K CSq s (fourierCoeff g)` | `SymCalcStep6.conjCut_multiplier_gain` ✔ (proved this session) |
| `conjLapPow` Leibniz | `[conjLapPow k T T', M_a]` of order `2k−1` | `SymCalcStep6.conjLapPow_mul_comm_le` (delegated, in flight) |
| `conjLapPow` order `2k` | `CSq s (compMap T' (conjLapPow k T T' h)) ≤ K CSq (s+2k) (fourierCoeff h)` | `conjLapPow_CSq_le` ✔ |
| diffeo transport | `CSq s (compMap T u) ≤ K CSq s (fourierCoeff u)` | `SymCalcStep1.fourierCoeff_comp_le` ✔ |

The three "delegated" rows are short corollaries of the rows above them and are stated only to
package the two *compositions* (`Λ^k` after a Friedrichs commutator, and the same for `conjLapPow`)
that Step 3 performs.  In fact — this is the most useful outcome of this session — **none of Steps
1–3 needs a certificate that is not already PROVED**: expanding `Θ_{il}` as

  `[Λ_i^k, M_{ψ_l²}Š] = M_{ψ_l²}[Λ_i^k,Š] + [Λ_i^k,M_{ψ_l²}]Š`,
  `[M_{ψ_l²}Λ̌^k, S_i] = M_{ψ_l²}[Λ̌^k,S_i] + [M_{ψ_l²},S_i]Λ̌^k`

and noting `[Λ̌^k,S_i] = T([Λ^k,Ŝ])T^{−1}` (with `Ŝ = conjCut ρ ε T' T`) gives the four terms
`conj_cut_comm_lapPow_le` (twice, with the roles of `T,T'` exchanged), `laplacian_pow_mul_comm_le`
(Leibniz) and `[M_{ψ_l²},S_i]Λ̌^k`, whose order is `−1 + 2k = 2k−1` because the Friedrichs
certificate is applied at level `s−1` and `conjLapPow_CSq_le` at level `s`.  The
"`Λ^k ∘ Friedrichs`" certificate is likewise the composition `CSq s (Λ^k h) ≤ K CSq (s+2k) h` with
`CSq (s+2k) (Friedrichs) ≤ K CSq (s+2k−1)`.

So the rest of the work is (i) the assembly of the component expansion of Step 1 against `D.R`,
`D.Rstar`, `tMapFun`, `coeffFun`, `lapow`/`STruncR` (i.e. rewriting `R_i(Qkf)` and `R_i(Jf)` in
charts) and (ii) the `Real.sqrt`/`ENormB` bookkeeping.  ⚠ Note that no `H^{1−k}`-weighted *strong*
estimate is needed for the diagonal either (Step 2 handles `ϑ_{ii}` directly), so
`Work.Diff.STE.B3.flat_diag_pairing_le` is a *sufficient* but not necessary input.
-/

/-! ## SESSION 13 — THE DECISIVE FACTS (corrected; read this before anything else)

This session (a) settled, with a *faithful* numerical model, that the statement is **TRUE**;
(b) found the structural reason — `T_{ij} = ψ_i·ψ_j·(an L²-isometry)` — and the proved library lemma
that gives it; (c) corrected two SESSION 9/11 claims that were *WRONG* and had been "verified"
numerically against a wrong expression.  Everything in this block is machine-checked or was
verified to 1e-11 in an exact model; nothing here is speculation.

### 1. The transfer factorises through the *geometric mean of the two weights*

`Submission/Work/Diff/STE/B3/dens_transition.lean` (PROVED) gives, for `p` in both chart sources,
`dens i (coord i p) = |det (tangentCoordChange x₀i x₀j p)| · dens j (coord j p)`, and in the flat
picture the transition Jacobian `det (tangentCoordChange x₀i x₀j p)` is `det D (tMapFun i j)`
(chain rule: `tMapFun i j z = coord i (pt j z)`), whose determinant is `det D(coord i ∘ pt j)`.
Combining this with the *definition* of `D.coeffFun` (`D/R_Rstar_expansion2.lean`) gives

  `coeffFun D i j a b c d z = ψ i (tMapFun i j z) · ψ j z · √(dens j z / dens i (tMapFun i j z)) · O`

with `O_{ab,cd} = ⟪e j a, e i c⟫ ⟪e j b, e i d⟫` an *orthogonal* matrix (`e i ·` and `e j ·` are both
`g₀`-orthonormal at `pt j z`), and `ζ i (pt j z) · χ i (coord i (pt j z)) = ψ i (tMapFun i j z)`
because `χ i = 1` wherever `ζ i ≠ 0` (`hζsupp` + `hχ1`).  ⚠ The convention in `dens_transition` is
`|det (tangentCoordChange x₀i x₀j p)| = |∂x_j/∂x_i|` (check it against the volume-element identity
`dens_1(z)dz = dens_2(τz)d(τz)`), so that second application of the lemma gives, on `D.Omega i j`,

  `dens j z / dens i (tMapFun i j z) = |det (D (tMapFun i j) z)|`,   hence

  **`coeffFun D i j a b c d z = ψ i (tMapFun i j z) · ψ j z · |det (D (tMapFun i j) z)|^{1/2} · O`,
  i.e.  `T_{ij} = ψ_i · ψ_j · (M_{√|det D τ|} ∘ comp_τ) · O`  with `τ = tMapFun i j`: the last factor
  is an isometry of `L²` (change of variables) and `O` is an orthogonal matrix; consequently
  `T_{ji} = T_{ij}^†` and `T_{ij}^† T_{ij} = M_{ψ_i²ψ_j²}` (a *scalar*).**

⚠ On a point where `ψ j z ≠ 0` but `ζ i (pt j z) = 0` the coefficient `coeffFun` vanishes while the
right-hand side need not (the `ψ i` there is the *junk* value of `ζ i` off the chart-`i` source); the
identity is therefore stated on `D.Omega i j`, which is where `coeffFun` can be nonzero — for the
applications multiply both sides by `ψ i (tMapFun i j ·)` (or use the `bump_expansion` localisation).

(In 1D with `ψ_1² = ψ_2² = 1/2`, `τ' > 0`: `γ₁₂ = (1/2)√τ'`, `γ₂₁(y) = (1/2)/√(τ'(τ⁻¹y))`; the
adjoint relation is `γ₂₁(τx)·τ'(x) = γ₁₂(x)`, i.e. `T_{21} = T_{12}^†` exactly.)

⚠ **Do not confuse this with the "no-Jacobian" model `γ₁₂ = γ₂₁∘σ = const`, which is NOT realizable
(a measure-preserving non-affine circle diffeo does not exist) and which *does* produce an unbounded
ratio.**  Both of the numerically "verified" claims of SESSIONS 9/11 (`Ξ = Σ⟨Λ_i𝒞_{ij}x_j,v_i⟩`,
"ratio grows like 1/ε") were produced with such non-realizable models; they are **wrong**.

### 2. The exact identity that organises the proof (verified to 1e-11 in two models)

`Ξ := ENormB_pair k (J f) u − ENormB_pair k f (J u) = BPair ([Qk,J] f, u)`.  With the transfers
`T_{ij}`, the cutoffs `S_i` (multiplier `ρ(ε·)` in chart `i`), `Λ_i = Λ_i^k`, `x_i = R_i f`,
`v_i = R_i u`, the definitions of `Qk`, `J` and the reconstruction `Σ_j T_{ij} h_j = h_i` give
**exactly** (no analysis):

  `Ξ = Σ_{i,l} CPair_i (ϑ_{il} x_l, v_i)`,  `ϑ_{il} = Λ_i T_{il} S_l − S_i T_{il} Λ_l`,
  `  = Σ_{ij} ⟨𝒞_{ij} x_j, Λ_i v_i⟩ + Σ_{ij} ⟨𝒟_{ij} x_j, S_i v_i⟩`
     with `𝒞_{ij} = T_{ij} S_j − S_i T_{ij}`,  `𝒟_{ij} = Λ_i T_{ij} − T_{ij} Λ_j`,
  `  = − Σ_j [ ⟨S_j x_j, U_j⟩ + ⟨Λ_j x_j, W_j⟩ ]`,
     with `U_j = Σ_i 𝒟_{ji} v_i = Λ_j v_j − (Qk u)_j`,  `W_j = Σ_i 𝒞_{ji} v_i`.

The two useful *exact* rewritings of the defects are
`W_j = (1−S_j) v_j − Σ_i T_{ji} (1−S_i) v_i` (uses the reconstruction on `u`), and
`U_j = Λ_j v_j − Σ_i T_{ji} Λ_i v_i`.  Note that **each of the two sums is of order `2k` on its own**
(`𝒞` is order `0`, `Λ` is order `2k`; `𝒟` is of order `2k` because the chart-`j` flat Laplacian is
*not* the transfer of the chart-`i` flat Laplacian unless the transition is affine), and the estimate
holds **only for the combination** `Σ_j[⟨S_jx_j,U_j⟩+⟨Λ_jx_j,W_j⟩]`.  In the 1D model with constant
`ψ_i² = 1/2` the combination degenerates to the *commutator*

  `Ξ = ⟨x_1, [Š − S_1, Λ_1 − Λ̌] v_1⟩`,

with `Š = U S_2 U^†`, `Λ̌ = U Λ_2 U^†` (the transferred cutoff / Laplacian), whose order is
`0 + 2k − 1 = 2k − 1` — this is the mechanism the proof has to reproduce in general.

### 3. Numerical evidence that the statement is TRUE (and why the old evidence was not)

Model: two charts on the circle, `σ(x) = x + a sin(2πx)/(2π)`, `a = 0.4` (`σ' ∈ [0.6,1.4]`),
`ψ_1² = ψ_2² = 1/2`, the **faithful** transfer `γ₁₂ = (1/2)√σ'` (i.e. the Jacobian-corrected one of
§1), `ρ(y) = exp(−1/(2−‖y‖²))` on `‖y‖² < 2`; all operators represented exactly in the Fourier basis
(composition matrices `∫ e^{2πi n σ(x)}e^{−2πi m x}dx` by quadrature; the low-band restriction of
`C·C⁻¹` is `Id` to 1e-16, and the exact identity of §2 holds to 1e-11).  Ratio
`|Ξ| / (√(E_{k−1}f + E_0f)·√(E_k u))` for single frequencies `m` with **`ε·m` fixed** (so the cutoff
is always in the transition region) and `m = 2,4,…,18`:

| `k` | `ε·m` | ratios |
|---|---|---|
| 1 | 0.7 | 0.012, 0.032, 0.039, 0.040, 0.040, 0.040, **0.039** |
| 1 | 1.2 | 0.068, 0.178, 0.329, 0.476, 0.546, **0.590**, 0.596 |
| 2 | 0.7 | 0.310, 0.103, 0.067, 0.056, 0.051, 0.047, **0.046** |
| 2 | 1.2 | 0.410, 0.813, 1.325, 1.815, 2.051, 2.193, **2.212** |

i.e. **convergent, uniformly in `ε·m`** — the statement is true (it is *not* sharp: the constant is
O(1) times the natural geometric constants).  With the *non-realizable* `γ = 1/2` (no Jacobian) the
same table grows like `m^{1}` (`Ξ/m^{2k−1}` grows linearly) — this is what made earlier sessions
doubt the statement.

### 4. Where the proof stands

Steps 1 (component expansion) and 2 (the `ϑ_{ii}` diagonal) of the SESSION 11 block remain valid.
The crux is now *pinned*: prove `|Σ_j[⟨S_jx_j,U_j⟩+⟨Λ_jx_j,W_j⟩]| ≤ C √(E_{k−1}f+E_0f)√(E_k u)`, and
the only mechanism available is the `U`/`W` cancellation of §2.  The inputs one needs are
(i) `T_{ij} = ψ_iψ_j·(isometry)` of §1, (ii) the Friedrichs commutator `[M_a,S_i]` (order `−1`,
uniform in `ε`, PROVED: `SymCalcStep1.flat_multiplier_commutator`), (iii) the Leibniz expansion of
`[Λ_i^k,M_a]` (PROVED: `laplacian_pow_mul_comm_le`), (iv) the fact that the *conjugated* cutoff
`Š_{ij} − S_i` and the *conjugated* Laplacian `Λ̌_{ij} − Λ_i` differ by the same isometric conjugation
so that only their **commutator** survives.  ⚠ The `|ι₀| ≥ 3` point of SESSION 11 is still open and
must be settled: the arguments of §2 use the reconstruction only, so they are uniform in `ι₀`; but
Step 3 of the SESSION 11 block (`L_{li}x_i = ψ_i²x_l`) is a *two-chart* statement.

### 5. The two lemmas of §1 are now PROVED (import them)

* `Work.Diff.STE.B3.coeffFun_eq_weight_mul_orth`
  (`Submission/Work/Diff/STE/B3/coeffFun_eq_weight_mul_orth.lean`, axiom-clean): on `D.Omega i j`,
  `coeffFun D i j a b c d z = ψ i (tMapFun i j z) · ψ j z · (√|det (tangentCoordChange x₀i x₀j (pt j z))|)⁻¹
   · ⟪e j a, e i c⟫ ⟪e j b, e i d⟫` — the factorisation of §1.
* `Work.Diff.STE.B3.coeffFun_adjoint`
  (`Submission/Work/Diff/STE/B3/coeffFun_adjoint.lean`, PROVED this session): on `D.Omega i j`,
  `coeffFun D i j c d a b y = |det (tangentCoordChange x₀i x₀j (pt j y))|⁻¹ · coeffFun D j i a b c d (tMapFun i j y)`
  — i.e. `T_{ji} = T_{ij}^†` at the level of coefficients (the transpose pairing).  This is the
  identity that lets one move a transfer from one side of a `CPair` to the other *with the Jacobian*.
* `Work.Diff.STE.B3.R_reconstruction_pointwise`
  (`Submission/Work/Diff/STE/B3/R_reconstruction_pointwise.lean`, PROVED this session):
  the component-level reconstruction
  `Σ_j Σ_cd coeffFun D j i a b c d z · (R j h c d)(tMapFun j i z) = R i h a b z` (pointwise, all `z`,
  arbitrary `h : Bil`).  Together with `R_Rstar_expansion_pointwise_noT2` this is the glue for every
  chart rewriting of `R_i (Qk f)`, `R_i (J f)`, `R_i (K f)`, and in particular for the `W_j`
  rewriting of §2 (`W_j = (1−S_j)v_j − Σ_i T_{ji}(1−S_i)v_i`).

⚠ Every argument must avoid `[T2Space M]` / `[I.Boundaryless]` (the target has neither).  The
reconstruction `Σ_i T_{ji} h_i = h_j` **is** available without hypotheses: use the Boundaryless-free
`Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free` (`Submission/Work/Diff/STE/B3/Rstar_R_eq_zeta_sq_free.lean`,
PROVED, together with its helper `apply_eq_sum_mat_free`), namely `R_i^*(R_i h) = ζ_i²·h` pointwise,
summed with `D.hζsq` (`Σ_i ζ_i² = 1`).  (The older `sum_Rstar_R_eq_id` carries a spurious
`[I.Boundaryless]`.)  ⚠ Other chart-level helpers *do* carry `[I.Boundaryless]`
(e.g. `R_contDiff_of_chartData`), so any use of them must be replaced by a free version.
-/

/-! ## SESSION 14 — the exact identities, the two-chart pair computation, and the `≥ 3`-chart gap

This block records (a) the *exact* algebraic forms of the left-hand side, (b) the exact two-chart
computation of one pair — including the weights, which earlier sessions only had up to "top order" —
(c) the precise mechanism of the one-derivative gain (the inverse of the covector transformation),
verified exactly in an affine model, and (d) the one point that is still open.

### (a) The exact identities (nothing here is asymptotic)

Notation: `x_i := R_i f`, `v_i := R_i u`, `L_{ij} := R_i R_j^*` (chart `j` → chart `i`),
`S_i := R_i^* (S_ε (R_i ·))`, `Λ_i := R_i^* (Λ_i^k (R_i ·))`, `S_l`/`Λ_l` also denote the *plain*
chart-`l` multipliers.  The reconstruction is `Σ_j L_{ij} h_j = h_i`, in particular `L_{ii} = M_{ψ_i²}`.

1. `Ξ := ENormB_pair k (Jf) u − ENormB_pair k f (Ju) = BPair (Jf) (Qk u) − BPair (Qk f) (Ju)`
   (`ENormB_pair_commutator_eq_BPair_JQk`, **PROVED here**).  In this form all four factors have a
   *pointwise* chart expansion: `R_i (Jh)` by `R_J_pointwise_expansion` and `R_i (Qk h)` by
   `R_Qk_pointwise_expansion` (**PROVED here**).
2. `Ξ = Σ_{i,l} CPair_i (ϑ_{il} x_l, v_i)` with `ϑ_{il} := S_i L_{il} Λ_l − Λ_i L_{il} S_l`
   (SESSION 11's form, up to the transpose), and `ϑ_{li} = −ϑ_{il}^*`.
   ⚠ This form is **chart-count independent**: it uses only the definitions of `Qk`, `J` and the
   reconstruction — there is *no* `ψ_i^{−2}` and *no* two-chart relation in it.
3. With `𝒟_{lm} := L_{lm} Λ_m − Λ_l L_{lm}` (order `2k`; note `𝒟_{mm} = L_{mm}Λ_m − Λ_mL_{mm}
   = [M_{ψ_m²}, Λ_m]`, of order `2k−1`, and `𝒟_{ml} = −𝒟_{lm}^*`),
   `Λ_lS_l = S_lΛ_l` gives **`ϑ_{lm} = S_l 𝒟_{lm}`**, whence
   **`Ξ = Σ_{l,m} ⟨x_l, S_l 𝒟_{lm} v_m⟩`**,  with  `Σ_{m} 𝒟_{lm} v_m = R_l(Qk u) − Λ_l v_l`.
   Every single term is of order `2k`; the diagonal (`m = l`) is of order `2k−1` directly.

### (b) The exact two-chart pair (this is what the SESSION 11 Step 3 *meant*)

Specialise to `ι₀ = {i, l}` and pair the terms `(i,l)` and `(l,i)` of form 2.  Write
`T := comp_τ` (chart `i` → chart `l`), `T' := comp_σ`, `σ = τ^{-1}`, so `L_{il} = M_γ T`,
`L_{li} = M_{γ'} T'`; let `ψ_i², ψ_l²` be the two chart functions and put
`c_1 := ψ_i² ψ_l²` (chart `i`), so `L_{il}L_{li} = M_{c_1}` and `γ (γ'∘τ) = c_1`.  The reconstruction
`L_{li}x_i = ψ_i² x_l` (chart-`l` function) gives `T x_l = M_{ρ_2} x_i` and `T v_l = M_{ρ_2} v_i`
with `ρ_2 := ψ_l²/γ` (both chart-`i` functions).  Putting `Š := conjCut ρ ε σ τ`,
`Λ̌ := conjLapPow k σ τ` (the chart-`l` operators read in chart-`i` variables), `S := S_ε`,
`Λ := Λ^k` (chart-`i`), an exact computation (adjoint `T_{il} = T_{li}^†`, i.e.
`⟨p, T'q⟩_l = ⟨|det Dτ|·Tp, q⟩_i`) gives

  **`CPair_i(ϑ_{il}x_l,v_i) + CPair_l(ϑ_{li}x_i,v_l) = ⟨x_i, X_{il} v_i⟩_i`**  with

  **`X_{il} = (Λ M_γ Š − S M_γ Λ̌) M_{ρ_2} + M_λ (Λ̌ M_{ψ_i²ρ_2} S − Š M_{ψ_i²ρ_2} Λ)`,
  `λ := γ/ψ_i²`**  (so that `γ ρ_2 = ψ_l² = λ·(ψ_i² ρ_2)`).

`X_{il}` is exactly `SymCalcStep7.pairOp` with `a = ρ_2`, `b = γ`, `c = λ`, `d = ψ_i²ρ_2`; the
relation `a·b = c·d (= ψ_l²)` is what the delegated lemma
`Work.Diff.STE.B3.SymCalcStep7.flat_pair_transfer_le` uses.  ⚠ The identity `Θ_{il} =
[Λ_i, M_{ψ_l²}Š] + [M_{ψ_l²}Λ̌, S_i]` asserted in the SESSION 11 block is the same up to the
lower-order pieces: for **constant** weights (`M_{ψ_l²} = ψ_l²`) both reduce to
`ψ_l²([Λ,Š] + [Λ̌,S])`, which is what the four leading symbols do after cancellation; the *exact*
operator is `X_{il}` above.

### (c) The mechanism: the covector transformation inverts

`X_{il}` is the sum of four operators of order `2k`; only the combination is of order `2k−1`.
Top symbols (chart-`i` frequency `ξ`, `B := (Dτ(x))^{-T}` the covector transport):

  `M_aΛ M_bŠ − M_{a'}SM_{b'}Λ̌ + M_cΛ̌M_dS − M_{c'}ŠM_{d'}Λ → (ab)λ(ξ)^kρ(εBξ) − (a'b')ρ(εξ)λ(Bξ)^k`
  `  + (cd)λ(Bξ)^kρ(εξ) − (c'd')ρ(εBξ)λ(ξ)^k`  (as leading symbols),

which vanishes identically when `ab = a'b' = cd = c'd' = ψ_l²`.  The two summands carry `B` resp.
`B^{-1}`, and they cancel **because `B^{-1}B = 1`** — this is the same mechanism that makes the
Mironov/Leibniz mechanism work, and it is the reason why the individual cross terms
(SESSION 9's table: ratio growing like the frequency) are order `2k` while the pair is `2k−1`.

**Exact check in an affine model.**  Take the torus `𝕋ⁿ` with a *unimodular* integer matrix `A`
(`τ(x) = Ax`, so `comp_τ` is an exact Fourier shift `η ↦ A^Tη`), two charts with constant weights
`ψ_i² = ψ_l² = 1/2` and `γ = γ' = 1/2`.  Then for every single-mode probe the pair is
`(1/2)(ρ(εξ)λ(η)^k − λ(ξ)^kρ(εη)) + (1/2)(λ(ξ)^kρ(εη) − ρ(εξ)λ(η)^k) = 0` **identically** (with
`ξ = A^Tη`), i.e. `X = 0`; likewise `Ξ = 0` for every single-mode `f, u`.  This confirms that the
gain is *not* a numerical accident and pins the exact cancellation.  (A non-affine transition is
what makes the cancellation partial, i.e. of order `2k−1` rather than `−∞`.)

### (d) ⚠ THE OPEN POINT: `|ι₀| ≥ 3`

Form (b) uses `L_{li}x_i = ψ_i²x_l`, which holds **only for two charts**; in general
`L_{il}x_l = ψ_l²x_i − Σ_{j≠i,l} L_{ij}x_j`.  So for `|ι₀| ≥ 3` the pair `{i,l}` does not close on
its own and the pair-wise estimate (b)+(c) is *not* available.  The chart-count-independent forms
(a2) and (a3) remain valid; the gain for fixed `l` must come from the whole `m`-sum, i.e. from
`Σ_m 𝒟_{lm}v_m = R_l(Qk u) − Λ_l v_l` together with `Λ_l S_l = S_l Λ_l`.  Any proof of the target
must settle this; do not assume the two-chart relation.

### (e) Practical notes

* `SymCalc.lean` contains 8 stale `sorry`s duplicating already-proved statements
  (`laplacian_pow_mul_comm_le`, `flat_multiplier_commutator`, `flatLam_pow_sub_bound`); the clean
  modules are under `SymCalcStep1/` and `SymCalcStep6/`.  Do not import the stale ones *for their
  statements*.
* `SymCalcStep6`: `conj_cut_comm_lapPow_le` (`[Λ^k,V]` order `2k−1`), `conjLapPow_mul_comm_le`
  (`[L̂,M_a]` order `2k−1`), `conjCut_multiplier_gain` (`[M_a,V]` order `−1`),
  `lapPow_Friedrichs_le`, `lapPow_toolbox`; `SymCalcStep1`: `flat_multiplier_commutator`,
  `laplacian_pow_mul_comm_le`.  All sorry-free.
* The hypothesis `hk : finrank ℝ E < 2 * k` of the target is **not used** by any of the flat
  certificates above (they need only `1 ≤ k`); it presumably belongs to the consumer
  (`gal_uniform_v2`).  It is not an obstacle.
-/

/-! ## SESSION 15 — two corrections that make the route close

### (1) `L_{li} x_i = (ζ_i²)_{(l)} · x_l` for EVERY pair: the `|ι₀| ≥ 3` "open point" of SESSION 14 is void

`R_i^* (R_i h) = ζ_i² · h` pointwise (`Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free`, PROVED, no
`[I.Boundaryless]`), and `R_l` is *pointwise linear in the section*:
`R_l (s • h) = (s ∘ pt_l) · R_l h` (`Work.Diff.STE.B3.R_fun_smul`, PROVED).  Hence for every pair
`(i,l)` and every section `f`

  `R_l (R_i^* (R_i f)) = R_l (ζ_i² • f) = (ζ_i² ∘ pt_l) · R_l f`,

i.e. in the notation of the SESSION 14 block

  **`L_{li} x_i = (ζ_i²)_{(l)} · x_l`  and  `L_{li} v_i = (ζ_i²)_{(l)} · v_l`**   (⋆⋆)

for **arbitrary `ι₀`** — the transported component `L_{li}x_i` is exactly the *localised* component
of the other chart and nothing else.  (Summing (⋆⋆) over `i` recovers the full reconstruction
`Σ_i L_{li}x_i = (Σ_i ζ_i² ∘ pt_l) x_l = x_l`, which is the consistency check: `hζsq`.)  Delegated
as `Work.Diff.STE.B3.R_L_eq_zeta_sq`.

⚠ Consequences.  (i) SESSION 14's (d) "OPEN POINT" — "for `|ι₀| ≥ 3` no pair closes" — is **wrong**:
the two-chart substitution used by the pair computation is available for every pair, so the pairwise
computation applies verbatim to an arbitrary atlas and `pairOp` / `flat_pair_transfer_le` is the
right flat core.  (ii) The same substitution was *claimed* in SESSION 13 §1 with `ψ_i²` in place of
`ζ_i²`; the correct weight is `ζ_i²` (they agree on `supp ζ_i`, which is why the numerical models
could not see the difference, but only `ζ_i²` is the *unrestricted* identity).

### (2) The sharp index: what the assembly consumes is the *pairing* form, not the strong `CSq` form

`Work.Diff.STE.B3.SymCalcStep7.flat_pair_transfer_le` (PROVED) states

  `CSq s (pairOp g hat) ≤ K · CSq (s + 2k − 1) (g hat)`   for `s : ℕ`, `s ≥ 0`,

i.e. `pairOp` is of order `2k−1` in the *strong* `H^s` sense.  The target needs the **pairing** form

  `|L2re y (pairOp g)| ≤ K · √(CSq (k−1) ŷ) · √(CSq k ĝ)`,

equivalently `‖pairOp g‖_{H^{1−k}} ≤ C‖g‖_{H^k}`, i.e. `pairOp : H^k → H^{1−k}`.  This is *not* a
consequence of the strong form at `s ≥ 0`: the strong form at `s = 0` yields only
`‖pairOp g‖_{L²} ≤ C‖g‖_{H^{2k−1}}`, and the pair `(k−1, k)` cannot be reached by interpolating the
family `(s+2k−1, s)` at `s ≥ 0` downwards.  It is the same order-`2k−1` statement read at the
*negative* index `1−k`, and it is TRUE: the single-mode tests (`y = g`, `y = 1`) are sharp up to an
ε-independent constant, the indices `(k−1)+k = 2k−1` match exactly, and the operator
`pairOp` is a ΨDO of order `2k−1` (its symbol is `Σ` of products of bounded symbols with
`wt^{(2k−1)/2}` growth).  Delegated as
`Work.Diff.STE.B3.SymCalcStep7.flat_pair_transfer_pairing_le`.

### (3) The two halves of `Ξ` and the certificates they consume

With `x_i := R_i f`, `v_i := R_i u`, `L_{ij} = R_i R_j^*`, and (SESSION 11/14)
`Ξ := ENormB_pair k (J f) u − ENormB_pair k f (J u) = BPair ([Qk, J] f) u = Σ_{i,l} CPair_i (ϑ_{il} x_l, v_i)`,
`ϑ_{il} = Λ_i L_{il} S_l − S_i L_{il} Λ_l`, `ϑ_{li} = −ϑ_{il}^*`:

* **diagonal** `i = l`.  `L_{ii} = R_i R_i^* = M_{ψ_i²}` (the dual of `Rstar_R_eq_zeta_sq_free`,
  same proof: `R_i (R_i^* w) = ψ_i² w`), so `ϑ_{ii} = Λ_i M_{ψ_i²} S_i − S_i M_{ψ_i²} Λ_i`
  `= [Λ_i, M_{ψ_i²}] S_i + [M_{ψ_i²}, S_i] Λ_i`, both of order `2k−1`.  The first is consumed by
  `Work.Diff.STE.B3.flat_diag_pairing_le_S` (the cut-*inside* variant of the PROVED
  `flat_diag_pairing_le`; delegated) and the second by `SymCalcStep6.lapPow_Friedrichs_le` (PROVED).
* **cross pair** `i ≠ l`: the pair computation of the SESSION 14 block, which is now legitimate for
  every pair by (⋆⋆), gives
  `CPair_i (ϑ_{il} x_l, v_i) + CPair_l (ϑ_{li} x_i, v_l) = CPair_i (x_i, X_{il} v_i)` with
  `X_{il} = pairOp` at the weights `a = ρ₂, b = γ, c = λ, d = ψ_i²ρ₂`, hence of order `2k−1`.  The
  pairing bound is `flat_pair_transfer_pairing_le` (delegated).
* **summation**: `Ξ = Σ_i (diagonal) + Σ_{i<l} (pair)`, and Cauchy–Schwarz over the `≤ |ι₀|²` pairs
  against `Σ_i CPair_i(x_i,x_i)`-type quantities produces the two `sqrt` factors of the target.

⚠ Two bookkeeping points the assembly must respect (both flagged by the reviewers of the flat
pieces).  (a) The **constant mode**: `ENormSq k u` vanishes for a `u` whose chart components are
constants, while `[Λ_i, M_c]u ≠ 0`; the target is still fine because `Ξ(f, u) = 0` for such `u`
(`Ju = u` and `Λ_i` kills constants, hence `pdVec k l (R_i u) = 0` kills every term of the pairing),
so the assembly must split the mean of `u` off *before* applying the regularised flat certificates.
(b) `c = ψ_i²` is *supported in the open cube* (`hχsupp`) but not literally periodic, while the flat
certificates ask for `Periodic1 c`; the pairing only sees `c` on the fundamental domain, so the
assembly must feed the *periodisation* of `c` (or restate the certificate for a compactly supported
`c`, which is an equally cheap variant of the PROVED proof).

### (4) How to avoid the division trap in the cross pair (§3 above, item 2)

The SESSION 14 pair computation substitutes `x_l = (1/ζ_i²) L_{li}x_i` (equivalently
`compMap τ x_l = ρ₂ x_i`, `ρ₂ = ζ_l²/γ`), which *divides* by functions that vanish on open sets —
the sort of step that silently invalidates an identity in Lean (`⁻¹ = 0` is a junk value, and
`M_γ M_{1/γ} = 1_{γ≠0}` is not `1`).  There is no need for it.  Write the pairing in the flat
chart-`i` variables.  With `L = L_{il} = M_γ (compMap τ)` (τ = `tMapFun i l`, chart `i` → chart
`l`), `Š := conjCut ρ ε τ' τ` (the chart-`l` cutoff read in chart-`i` variables) and
`Λ̌ := conjLapPow k τ' τ`,

  `L (S_l x_l) = M_γ (Š (compMap τ x_l))`,  `L (Λ_l x_l) = M_γ (Λ̌ (compMap τ x_l))`,

and the *only* place `compMap τ x_l` is needed is behind `M_γ`.  There, `M_γ (compMap τ x_l)` is
*known* (it is `ζ_l² x_i`, the pair relation (⋆⋆)), so

  `M_γ Š (compMap τ x_l) = M_γ Š M_{1/γ} (ζ_l² x_i)
     = 1_{γ≠0} · Š (ζ_l² x_i) + M_γ [Š, M_{1/γ}] (ζ_l² x_i)`,

and the first term is `Š(ζ_l²x_i)` *as a function on the fundamental domain* because the function
`ζ_l²x_i = γ · (compMap τ x_l)` vanishes identically on `{γ = 0}`; the second term is a Friedrichs
commutator of order `−1` (ε-uniform).  So the pair identity can be stated and proved entirely with
`M_{1/γ}`-type factors occurring only inside Friedrichs commutators — no division is ever applied to
an arbitrary function.

### (4b) ⚠ The `SymCalcStep7.pairOp` used by the SESSION 14 block is **not** the pair operator

`SymCalc.conjCut` and `SymCalcStep5.conjLapPow` conjugate *in opposite directions*:

* `conjCut ρ ε T T' = compMap T' ∘ flatCut ∘ compMap T` — the cutoff is conjugated by `compMap T'`;
* `conjLapPow k T T' = compMap T ∘ lapPow k ∘ compMap T'` — the Laplacian by `compMap T = (compMap T')^{-1}`.

So the transported cutoff and the transported Laplacian occurring in `pairOp` belong to **two
different charts** and `pairOp` cannot be the pair operator.  (Its order-`2k−1` estimate is still
true — the four leading symbols cancel *term by term*: `(ab−cd)·λ(ξ)^k·ρ(εBξ)` and
`(cd−ab)·ρ(εξ)·λ(B'ξ)^k` — which is why the proof went through; but the cancellation needed by the
pair is a different one.)

The pair `{i,l}` of `Ξ` has `L_{il} = M_γ ∘ compMap τ_{il}` (`τ_{il} = tMapFun i l`) and

  `Š_i := compMap τ_{il} ∘ S_l ∘ compMap τ_{li}`,   `Λ̌_i := compMap τ_{il} ∘ Λ_l ∘ compMap τ_{li}`,

**both conjugated by the same map** `U := compMap τ_{il}`, so that `L_{il}S_l = M_γ Š_i U` and
`L_{il}Λ_l = M_γ Λ̌_i U`.  Consequently the operator to be bounded is `pairOp` with
`conjCut ρ ε T T'` replaced by `conjCut ρ ε T' T`:

> **`Work.Diff.STE.B3.SymCalcStep7.pairOpC`**
> (`Submission/Work/Diff/STE/B3/SymCalcStep7/pairOpC_def.lean`).

The corresponding pairing estimate (`pairOpC : H^k → H^{1−k}`, ε-uniform, under `ab = cd`) is the
correct flat input of the assembly and is delegated this session as
`Work.Diff.STE.B3.SymCalcStep7.flat_pair_transfer_pairing_le_C` (the analogue for `pairOp` is
PROVED as `flat_pair_transfer_pairing_le`; the two operators differ only in the two
`conjCut`-occurrences, and they coincide when `T = T'`).

-/

/-! ## SESSION 16 — the corrected pair derivation, and the two flat lemmas it needs

This block supersedes the vague parts of SESSIONS 9/11/13/14/15.  Everything here was re-derived
from the *definitions* of the library (`D.R`, `D.Rstar`, `CPair`, `Qk`, `D.J`, `lamSection`,
`coeffFun`) and checked against the multiplier model.  Read it before touching the assembly.

### 0. Notation

`x_i := D.R i f`, `v_i := D.R i u` (chart-`i` *component families*, functions on `ℝⁿ` supported in
the open centred cube), `L_{il} := D.R i ∘ D.Rstar l` (chart `l` → chart `i`), `S_i := STruncR ρ ε`
(so `S_i x_i` is the componentwise Friedrichs cutoff), `Λ_i := lamSection D k (·) i` (the
componentwise flat Laplacian power), `CPair_i(p,q) = Σ_{ab} ∫_{centreCube} p_{ab} q_{ab}`.

### 1. The ϑ-form (re-derived; the SESSION 11/14 form is correct)

`Ξ := ENormB_pair k (Jf) u − ENormB_pair k f (Ju) = BPair (Jf) (Qk u) − BPair (Qk f) (Ju)`, and

`BPair (Jf) (Qk u) = Σ_m CPair_m (R_m(Jf), R_m(Qk u)) = Σ_{m,l,i} CPair_m (L_{ml}S_lx_l, L_{mi}Λ_iv_i)`
(the second step is the *definition*, `R_m(Jf) = Σ_l L_{ml}S_lx_l`, `R_m(Qk u) = Σ_i L_{mi}Λ_iv_i`;
note `Λ_i` acts on `v_i` in *chart `i`* — this is the point where a naive "pair `(m,l)`" argument
goes wrong).  Moving the second slot to the first by the adjunction `L_{mi}^* = L_{im}` and using
the **reconstruction** `Σ_m L_{im}L_{ml} = R_i(Σ_m ζ_m²)R_l^* = L_{il}` gives, exactly,

`Ξ = Σ_{l,m} CPair_m ((Λ_mL_{ml}S_l − S_mL_{ml}Λ_l) x_l, v_m)`.

With `ϑ_{ml} := Λ_mL_{ml}S_l − S_mL_{ml}Λ_l` this is the ϑ-form of SESSION 11 (`Λ` on the **first**
term), and `Ξ = −Ξ(u,f)`.

### 2. The exact four-term form of a pair, and the two moves

For the unordered pair `{i,l}` (`i ≠ l`) put (after using `L_{il}^* = L_{li}` and the self-adjointness
of `Λ_l, S_l` in chart `l`, so that **all four** terms are pairings in chart `i`)

`P_{il} = CPair_i (Λ_iL_{il}S_lx_l, v_i) − CPair_i (S_iL_{il}Λ_lx_l, v_i)
        + CPair_i (S_ix_i, L_{il}Λ_lv_l) − CPair_i (Λ_ix_i, L_{il}S_lv_l)  =: T1 + T2 + T3 + T4`.

Write `τ := τ_{li} := tMapFun l i` (chart-`i` coords → chart-`l` coords), `τ' := τ_{il} = τ⁻¹`,
`U := compMap τ` (so `U w = w ∘ τ`), `Š := conjCut ρ ε τ' τ` (i.e. `compMap τ ∘ flatCut ∘ compMap τ'`),
`Λ̌ := conjLapPow k τ τ'`, `S := flatCut ρ ε`, `Λ := lapPow k` — this matches `pairOpC`'s conventions
(`pairOpC k ρ ε T T' a b c d g = a(Λ(b·conjCut ρ ε T' T g) − S(b·conjLapPow k T T' g))
+ c(conjLapPow k T T'(d·S g) − conjCut ρ ε T' T(d·Λ g))`).

⚠ **The transfer is not scalar.**  Writing `c_{abcd} := coeffFun D l i a b c d` (so that
`(L_{il} w)_{ab}(z) = Σ_{cd} c_{abcd}(z) w_{cd}(τ z)`, `R_Rstar_expansion_pointwise_noT2`), the
proved `coeffFun_eq_weight_mul_orth` gives, on `D.Omega l i`,

`c(z) = γ(z)·O(z)`,  `γ(z) = ψ_i(τz)ψ_l(z)/√|det Dτ(z)|`,  `O_{ab,cd}(z) = ⟪e_l a, e_i c⟫⟪e_l b, e_i d⟫`

with `O` **pointwise orthogonal** (`Σ_{cd} O_{ab,cd}O_{a'b',cd} = δ_{aa'}δ_{bb'}`, from the two frames
being `g₀`-orthonormal at the same point).  `O` commutes with every componentwise operator
(`S, Λ, Š, Λ̌, conjCut, conjLapPow`), and the pairing is `O`-invariant.

The two ingredients of the M_γ-move are
* the **pair relation** `(⋆⋆)` (`R_L_eq_zeta_sq`, PROVED, valid for arbitrary atlases and with no
  hypotheses): `L_{il}x_l = β·x_i` and `L_{il}v_l = β·v_i` with `β := ζ_l² ∘ pt_i`, componentwise:
  `Σ_{cd} c_{abcd}(z) x_{l,cd}(τz) = β(z) x_{i,ab}(z)`;  equivalently `γ(z)·(O·(Ux_l))(z) = β(z)x_i(z)`;
* the definition of the commutator: `M_γ Š = Š M_γ + [M_γ,Š]`.

Applying these to each of the four transferred objects (`L_{il}S_lx_l`, `L_{il}Λ_lx_l`,
`L_{il}Λ_lv_l`, `L_{il}S_lv_l`), and rotating by `O^T` (`x̃ := O^Tx_i`, `ṽ := O^Tv_i`; the pairing
is `O`-invariant and `O` commutes with `Λ_i, S_i`), the pair becomes

`P_{il} = B(x̃, ṽ) + C`,   `C` = the eight commutator terms listed in §4 below,

with the **main form** (this is the object the flat lemma must bound)

`B(x,v) := L2re(Λ(β·(Šx)))(v) − L2re(S(β·(Λ̌x)))(v) + L2re(Sx)(β·(Λ̌v)) − L2re(Λx)(β·(Šv))`.

⚠ **Both M_γ and M_β appear.**  For `L_{il}S_lx_l` one gets (exactly)
`L_{il}S_lx_l = M_β Š x_i + O[Š,M_β](O^Tx_i) + O[M_γ,Š](Ux_l)`, i.e. `β` ends up **outside** `Š`
(this is forced: the first M_γ-move produces `Š(βO^Tx)`, and moving `β` out of `Š` costs the
Friedrichs commutator `[Š,M_β]`).  The same for the other three terms, so that all four main terms
of `B` carry `β` in the same position (outside the transported operator) and the leading symbols
cancel: term by term the symbols are `βρ(εBξ)λ(ξ)^k`, `−βλ(Bξ)^kρ(εξ)`, `+βρ(εξ)λ(Bξ)^k`,
`−βλ(ξ)^kρ(εBξ)`, whose sum is `0`.

⚠ A *mismatched* placement (e.g. writing the fourth term as `−L2re(Λx)(Š(β·v))` instead of
`−L2re(Λx)(β·(Šv))`) makes the four leading symbols fail to cancel and gives an expression of order
`2k` — a reviewer of the first draft of the delegated lemma found exactly this; the statement was
corrected.  **Keep the four `β`-slots exactly as in `B` above.**

### 3. The flat lemmas the pair needs (delegated this session)

* `Work.Diff.STE.B3.SymCalcStep7.flat_leibniz_pairing_le`
  (`Submission/Work/Diff/STE/B3/SymCalcStep7/flat_leibniz_pairing_le.lean`):
  `|L2re y ([Λ^k,M_a]w)| ≤ C√(CSq(k−1)ŷ)√(CSq k ŵ)` — the *negative-index* Leibniz estimate, i.e.
  `[Λ^k,M_a] : H^k → H^{1−k}`.  Not a consequence of the `s ≥ 0` CSq form
  (`laplacian_pow_mul_comm_le`), because `s = 1−k < 0`; both reviewers confirmed the route
  (endpoints `(0,2k−1)`, `(2k−1,0)` — both *positive*-index, and the second follows from the first
  by the antisymmetry `[Λ^k,M_a]^* = −[Λ^k,M_a]` — then `pairing_interpolation_family`).
* `Work.Diff.STE.B3.SymCalcStep7.pair_form_C_pairing_le`
  (`Submission/Work/Diff/STE/B3/SymCalcStep7/pair_form_C_pairing_le.lean`): the bound
  `|B(x,v)| ≤ K√(CSq(k−1)x̂)√(CSq k v̂)` for the main form `B` of §2, uniformly in `ε ∈ (0,1]`.
  Proof route (for whoever proves it): `B = L2re x (pairOpC k ρ ε T T' β 1 1 β v) + (mismatch)`,
  the first summand is the PROVED
  `SymCalcStep7.flat_pair_transfer_pairing_le_C` (`a·b = c·d = β` ✓), and the mismatch expands into
  products of the commutators `[Λ,M_β]`, `[M_β,S]`, `[M_β,Λ̌]`, `[Λ̌,M_β]`, `[Š,Λ]`, `[S,Λ̌]`,
  `[M_γ,Š]`, each of order `2k−1` (or `−1`), all of which are covered by the *proved*
  `conj_cut_comm_lapPow_le`, `conjLapPow_mul_comm_le`, `conjCut_multiplier_gain`,
  `lapPow_Friedrichs_le`, `laplacian_pow_mul_comm_le`, `flat_multiplier_commutator` — together with
  the `flat_leibniz_pairing_le` above for the two slots where the Leibniz commutator lands on the
  side carrying `k−1` derivatives.

### 4. The eight correction terms of §2 (each is bounded with the right indices)

From `T1`: `+⟨Λ_iO[Š,M_β](O^Tx_i),v_i⟩`, `+⟨Λ_iO[M_γ,Š](Ux_l),v_i⟩`.
From `T2`: `−⟨S_iO[Λ̌,M_β](O^Tx_i),v_i⟩`, `−⟨S_iO[M_γ,Λ̌](Ux_l),v_i⟩`.
From `T3`: `+⟨S_ix_i,O[Λ̌,M_β](O^Tv_i)⟩`, `+⟨S_ix_i,O[M_γ,Λ̌](Uv_l)⟩`.
From `T4`: `−⟨Λ_ix_i,O[Š,M_β](O^Tv_i)⟩`, `−⟨Λ_ix_i,O[M_γ,Š](Uv_l)⟩`.

Index bookkeeping (all use only *positive*-index certificates plus the elementary multiplier bounds
`‖Λw‖_{H^{−k}} ≤ C‖w‖_{H^k}`, `‖S w‖_{H^s} ≤ C‖w‖_{H^s}`, `‖compMap T w‖_{H^s} ≤ C‖w‖_{H^s}`,
`‖Ow‖_{H^s} ≤ C‖w‖_{H^s}` for the smooth orthogonal `O`): the first and second groups of each line
are Friedrichs commutators (`order −1`) applied to `x_i`, `v_i` or the chart-`l` functions, hence
`H^{k−1} → H^k` or `H^k → H^{k+1}`, and the bare `Λ_i`/`S_i` on the other side is absorbed by the
multiplier bounds; the *third* and *fourth* groups of `T2` (namely `[Λ̌,M_β](O^Tx_i)` and
`[M_γ,Λ̌](Ux_l)` paired with `S_iv_i`) are the only ones that need the negative-index Leibniz bound
of §3 — either directly (`flat_leibniz_pairing_le` after conjugating by `τ`), or by the same
endpoint/interpolation argument.  **The chart-`l` functions `Ux_l = x_l∘τ`, `Uv_l = v_l∘τ` are
allowed to appear** (they are bounded by the chart-`l` energies, and the final Cauchy–Schwarz runs
over all charts).

### 5. What is left after this

(a) the two flat lemmas of §3; (b) the chart-level identities of §2 (the pointwise expansion of
`L_{il}` from `R_Rstar_expansion_pointwise_noT2`, the relation `(⋆⋆)` from `R_L_eq_zeta_sq`, the
`O`-rotation and the eight commutator identities — pure algebra with the library's definitions);
(c) the summation over the `≤ |ι₀|²` pairs, the `CSq`/`ENormSq` conversions and the two `Real.sqrt`
factors of the target.  The constant-mode bookkeeping is *not* an issue in this route: the target's
right-hand side is `√(E_{k−1}f + E_0 f)·√(E_k u)` and `CSq (k−1)`, `CSq k` do **not** vanish on
constant chart components (only `ENormSq` does), so the flat statements above are applied to the
component functions `x̃`, `ṽ` directly.  ### 6. ⚠ SESSION 16 addendum — the frame matrices `O` cancel in the **main** terms; the main form is `B₀`

The `O`-rotation of §2 is *not* needed.  Doing the M_γ-move at the **matrix** level (write
`c = γO` and use that `O` is a pointwise matrix, so `O·(kw) = k(O·w) + [O,k]w` for every
componentwise operator `k ∈ {Š, Λ̌}`, and that `γ·(O·(Ux_l)) = βx_i` componentwise is exactly
`R_L_eq_zeta_sq`), one gets the four **exact** expansions

`L_{il}S_lx_l = Š(β·x_i) + γ·[O,Š](Ux_l) + [M_γ,Š](O·(Ux_l))`,
`L_{il}Λ_lx_l = Λ̌(β·x_i) + [M_γ,Λ̌](O·(Ux_l)) + γ·[O,Λ̌](Ux_l)`,
`L_{il}Λ_lv_l = Λ̌(β·v_i) + [M_γ,Λ̌](O·(Uv_l)) + γ·[O,Λ̌](Uv_l)`,
`L_{il}S_lv_l = Š(β·v_i) + γ·[O,Š](Uv_l) + [M_γ,Š](O·(Uv_l))`

(here `Š(β·x_i)` means the componentwise application of `Š = conjCut ρ ε τ' τ` to the function
`β·(x_i)_{ab}`).  Every correction has a *Friedrichs* commutator (`[O,k]` or `[M_γ,k]`, both of
order `−1`, ε-uniform, `O` and `γ` smooth) on the outside and the bare transported operator is
already evaluated — so **the mains carry no `O` and `β` sits inside `Š`/`Λ̌`**:

`B₀(x,v) := L2re(Λ(Š(β·x)))(v) − L2re(S(Λ̌(β·x)))(v) + L2re(Sx)(Λ̌(β·v)) − L2re(Λx)(Š(β·v))`.

Its four leading symbols are `λ(ξ)^kρ(εBξ)β`, `−ρ(εξ)λ(Bξ)^kβ`, `+ρ(εξ)λ(Bξ)^kβ`, `−λ(ξ)^kρ(εBξ)β`
— sum `0` ✓ (and *all four* β-slots are on the same side, which is what makes the cancellation
work).  `B₀` differs from the delegated `pair_form_C_pairing_le` form (β outside) by the bounded
terms `⟨Λ[Š,M_β]x,v⟩ + ⟨S[Λ̌,M_β]x,v⟩ − ⟨Sx,[Λ̌,M_β]v⟩ − ⟨Λx,[Š,M_β]v⟩`, each of which is a
Friedrichs commutator composed with a bare `Λ`/`S` and is bounded by `C‖x‖_{k−1}‖v‖_k` with the
elementary multiplier bound `‖Λw‖_{H^{−k}} ≤ C‖w‖_{H^k}` — so the assembly may use either form.

The correction terms of §4 are correspondingly replaced by the eight terms above; the ones that hit
the *f*-side (`[M_γ,Λ̌](O·(Ux_l))` paired with `S_iv_i`) still need the negative-index Leibniz bound
of `flat_leibniz_pairing_le`; the rest are covered by the positive-index Friedrichs certificates.

### 7. The diagonal

For `i = l` one has `L_{ii} = R_iR_i^* = M_{ψ_i²}` (`R_Rstar_eq_psi_sq`, PROVED, arbitrary atlas), so

`ϑ_{ii} = Λ_iM_{ψ_i²}S_i − S_iM_{ψ_i²}Λ_i = [Λ_i,M_{ψ_i²}]S_i + [M_{ψ_i²},S_i]Λ_i
        = [Λ_i,M_{ψ_i²}]S_i + [M_{ψ_i²},Λ_i]S_i + Λ_i[M_{ψ_i²},S_i] = Λ_i[M_{ψ_i²},S_i]`

(the first and second pieces cancel in the middle because `[M_{ψ_i²},Λ_i] = −[Λ_i,M_{ψ_i²}]`, and
`[M_{ψ_i²},S_i]Λ_i = Λ_i[M_{ψ_i²},S_i]` since `[Λ_i,S_i] = 0`).  So the diagonal is

`⟨ϑ_{ii}x_i,v_i⟩ = ⟨Λ_i([M_{ψ_i²},S_i]x_i),v_i⟩`,

bounded by `C‖x_i‖_{H^{k−1}}‖v_i‖_{H^k}` from the Friedrichs gain (`H^{k−1} → H^k`, ε-uniform) plus
the elementary `‖Λw‖_{H^{−k}} ≤ C‖w‖_{H^k}`.  The flat lemma for this is delegated this session as
`Work.Diff.STE.B3.SymCalcStep7.lapPow_friedrichs_pairing_le`.

### 8. Periodisation bookkeeping (do not skip)

`S_l = STruncR ρ ε` acts on the **periodisation** of the component (`STruncR_eq_flatCut_re`, proved
above), while `R_L_eq_zeta_sq` is an identity of the *non-periodised* components.  Both are supported
in the open centred cube, so an integral over the centred cube and over the unit cube of the
periodisation agree — this is the content of the (still to be proved) identity
`CPair_i(p,q) = Σ_{ab} L2re (per p_{ab}) (per q_{ab})`, which the final summation needs in order to
pass from `CPair` to the flat `L2re` of the lemmas of §3. -/

/-! ## SESSION 18 — three corrections that invalidate parts of SESSIONS 14–17

### (1) ⚠ `SymCalcStep7.pair_form_C_pairing_le` is FALSE as stated (β must be real)

A colleague (H2731-L3249) produced an explicit counterexample and declared the lemma FALSE: in the
*single-slot* form `L2re (Λ(β·V x)) v − L2re (S(β·P x)) v + L2re (S x) (β·P v) − L2re (Λ x) (β·V v)`
the third and fourth terms carry `β` in the **second** slot of `L2re`, hence contribute `conj β`.
Splitting `β = β_r + i β_i` one gets `B = B_r[β_r] + B_i[β_i]` with `B_i[1]` seeing the
self-adjoint completion `Θ₀ + Θ₀^*` of the pair operator, of order `2k` — so the four leading symbols
cancel **only for real β**.  (`B_r[1] = L2re((Θ₀ − Θ₀^*)x, v)` is order `2k−1`.)  Counterexample:
1-D torus, `T(x) = x + (1/2)sin(2πx)/(2π)` (lattice-equivariant), `β ≡ i`, `k = 1`.
⇒ The correct statement carries `(hβim : ∀ z, (β z).im = 0)`; it is delegated as
`Work.Diff.STE.B3.SymCalcStep7.pair_form_C_pairing_le_real`.  **In every application here β is real
and nonnegative** (`β = ζ_l²`, `β = γ = ψ_lψ_m/√|det Dτ|`), so nothing is lost.  Do **not** use the
complex-β version.

### (2) PROVED: the pair relation in its `Rper` form

`Work.Diff.STE.B3.coeffFun_transfer_Rper`
(`Submission/Work/Diff/STE/B3/coeffFun_transfer_Rper.lean`):

`(fun z ↦ Σ_{cd} coeffFun D l m a b c d z · Rper_l f c d (tMapFun l m z))`
`  = fun z ↦ (↑(ζ_l (pt_m z))² · R_m f a b z : ℂ)`.

This is the correct "`L_{ml}x_l = β x_m`" for the objects that actually occur: `Rper` and `R` agree
whenever the coefficient is nonzero (the coefficient carries `ζ_l(pt_m z)·χ_l(tMapFun l m z)`,
`hζsupp` gives `‖tMapFun l m z‖ < σ_l ≤ 1/8 < 1/2`, and `hχsupp` puts `support (χ_l)` in the open
cube).  Same statement with `u` for the `v`-side.  **This replaces the false reading
"`Š(Ux_l) = U(S_l x_l)`" of SESSION 16 §2.**

### (3) ⚠ `fourierCoeff` does NOT periodise — the chart-l objects must be the periodisations

`fourierCoeff f k = ∫_{unitCube} fourierExp(-k) x · f x` (`Torus.lean`), with **no** sum over
translates.  For a component `x_l = R_l f` supported in the *centred* cube (not in the unit cube)
one has `fourierCoeff x_l ≠ fourierCoeff (Rper_l f)`, and `flatCut x_l ≠ flatCut (Rper_l f)`.  Since
`STruncR ρ ε x_l = re ∘ flatCut (Rper_l f)` (`STruncR_eq_flatCut_re`) and `lamSection D k f l =
re ∘ lapPow (Rper_l f)` (`lamSection_eq_flatPow_re`), **every** object that the `SymCalc*` layer is
allowed to see must be built from the *periodisations* `X_l := Rper_l f`, `V_l := Rper_l u`:

* `Š(W) := compMap τ (flatCut W)` for `W` periodic is the chart-l cutoff read in chart-m variables:
  `Š(U X_l) = compMap τ (S_l X_l)` where `U = compMap τ`, `τ = tMapFun l m`.  With the *non*-periodic
  `x_l` the right-hand side would be `flatCut x_l`, which is a **different function**.
* the same for `Λ̌ := conjLapPow k τ τ'` and `Λ_l`: `Λ̌(U X_l) = compMap τ (lapPow X_l)` exactly
  (because `compMap τ' ∘ compMap τ = id`), and the Laplacian that the assembly must use on the
  chart-l side is `lapPow` applied to `X_l` (i.e. `lamSection`), **not** `lapPow x_l`.
* **Same caveat for `lapPow` itself when its argument is only cube-supported.**  The library's flat
  Laplacian of a *component* is `re ∘ lapPow (Rper ·)` (`lamSection`), i.e. the multiplier is fed the
  **`∫_{ℝⁿ}`-Fourier coefficients** of the component (equivalently the unit-cube coefficients of its
  *periodisation*), whereas `lapPow (c · Φ)` with `Φ` merely supported in the centred cube feeds
  `∫_{unitCube}` and therefore *loses the part of the support in the negative half*.  Every object of
  the form `Λ_m(c · (S_l X_l) ∘ τ)` that the assembly produces must consequently be read as
  `Λ_m (per_m (c · (S_l X_l) ∘ τ))` — i.e. the transfer operators really are operators **on the
  torus**, `Π_{ij}(W) = per_i(c_{ij}·(W ∘ τ_{ij}))`, not composition operators on `ℝⁿ`, and the two
  `Š`/`Λ̌` of §2 must be built from `Π`, e.g. `Π_{ij}(S_j W) = per_i(c_{ij}·((S_jW)∘τ_{ij}))`,
  `Π_{ij}(Λ_j W) = per_i(c_{ij}·((Λ_jW)∘τ_{ij}))` (`Λ_jW = lapPow W` with `W` periodic ✓).

### (4) ⚠⚠ THE STRUCTURAL OBSTRUCTION: every flat lemma assumes a lattice-equivariant transfer

`flat_pair_transfer_pairing_le_C`, `pair_form_C_pairing_le(_real)`, `conj_cut_comm_lapPow_le`,
`conjLapPow_mul_comm_le`, `conjCut_multiplier_gain`, `EFB_CSq_unif`, `compMap_adjoint`, … all carry
`hTper : ∀ i x, T (x + e_i) = T x + e_i` (and `T'` likewise), i.e. `T` must be a **torus
diffeomorphism**; the proofs use `compMap_adjoint` (the change of variables on `ℝⁿ/ℤⁿ`), the
fundamental-domain theory and the Fourier calculus on the torus.  The **chart transition
`τ = tMapFun l m` is not lattice-equivariant**: `τ(z) = coord_l (pt_m z)` and `pt_m (z + e) =
(extChartAt x₀m)⁻¹ (c_m + z + e)` is a different point, not a lattice translate.  Likewise the
weights `γ`, `O`, `β`, `ψ` are **not** periodic (they involve `pt_m z`).

⇒ No flat lemma of the `SymCalc*` layer can be applied to the chart pair as it stands.  Two ways out,
both unexplored and to be chosen deliberately **before** any further chart-level work:

* **(a) equivariant extension.**  For each pair `(m,l)` build a lattice-equivariant diffeomorphism
  pair `(T, T')` of the torus agreeing with `(τ, τ⁻¹)` on a neighbourhood of the (compact, cube-
  supported) region where the coefficients are nonzero, and periodise the weights.  The
  flat lemmas then apply verbatim.  This is a self-contained construction (a "local diffeo ⇒ global
  equivariant diffeo" lemma) — **not yet delegated**; it is the cheapest of the two.
* **(b) local transfer theory.**  Re-prove the pair bound for a *non*-equivariant `T` (smooth on an
  open set `U ⊇ tsupport c`, injective with invertible Jacobian there), using
  `Work.Diff.STE.B3.CSq_period_comp_arg_le_nodim_global` (which already handles the *periodisation*
  of `f · (u ∘ T)` for a *local* `T` and a *periodic* `u`) in place of `compMap_adjoint`.
  Note `flat_multiplier_commutator` (Friedrichs gain) is stated for a *periodic* `a` (it is a
  Fourier-side statement about the convolution with a rapidly decaying coefficient family), so it too
  needs redoing locally or feeding a periodic weight.

### (5) Status of the pair decomposition (what is settled and what is not)

* `Ξ = BPair(Jf, Qku) − BPair(Qkf, Ju) = Σ_m CPair_m(lamSection D k (Jf) m, R_m u) − Σ_m CPair_m(lamSection D k f m, R_m (Ju))` — PROVED (`ENormB_pair_commutator_eq_BPair_JQk`, `BPair_commutator_chart_split`).
* With `X_j := Rper_j f`, `V_j := Rper_j u`, `Π_{ij}(W) := per_i(c_{ij}·(W ∘ τ_{ij}))` (which is the
  periodisation `per_i(L_{ij} w)` for every chart-`j` function `w`), and the linearity of the flat
  multipliers: `lamSection D k (Jf) i = Σ_j Λ_i(Π_{ij}(S_j X_j))` and `lamSection D k f i =
  Σ_j Λ_i(Π_{ij}(X_j))`, so
  `Ξ = Σ_{i,j} CPair_i(Λ_i Π_{ij}(S_j X_j), R_i u) − Σ_{i,j,j'} CPair_i(Λ_i Π_{ij}(X_j), L_{ij'}(S_{j'} v_{j'}))`.
  The *second* group is a **triple** sum: `R_i(Ju) = Σ_{j'} L_{ij'}(S_{j'}v_{j'})` has not been
  collapsed.  SESSION 16's two-index form `Ξ = Σ_{m,l} CPair_m((Λ_m L_{ml} S_l − S_m L_{ml} Λ_l)x_l, v_m)`
  is obtained from this by the **section-level** adjunction `CPair_i(p, L_{ij}q) = BPair(Rstar_i p, Rstar_j q)`;
  that identity is exact and proved (`BPair_Rstar`), but it turns the single transfer into a sum over
  *all* charts, so re-deriving the two-index form from the triple sum must be done explicitly before
  the pair grouping `{i,l}` is used (`R_L_eq_zeta_sq` makes the pairwise form legitimate once the
  second index is collapsed).
* The **diagonal** `i = j` is elementary: `L_{ii} = M_{ψ_i²}` (`R_Rstar_eq_psi_sq`), `[Λ_i,S_i] = 0`,
  hence `Λ_i(M_{ψ²}S_i x_i) − S_i(M_{ψ²}Λ_ix_i) = [Λ_i,M_{ψ²}](S_ix_i)`, an order-`2k−1` Leibniz
  commutator applied to the band-limited `S_ix_i`.  Its flat form is **PROVED**:
  `Work.Diff.STE.B3.SymCalcStep7.diag_pairing_le`
  (`|L2re(Λ^k(c·S_εx) − c·Λ^k(S_εx)) v| ≤ K√(CSq(k−1)x̂)√(CSq k v̂)`, ε-uniform).
* The **cross** pairs `i ≠ l` remain the whole difficulty; per (4) they cannot be dispatched with the
  present flat layer. -/

/-! ## SESSION 19 — the framework is settled: the equivariant flat layer is *unusable*, and the
local route's primitives are the `per`-transfer, `flatCut`, `lapPow`

### (1) ⚠ Route (a) of SESSION 18 is DEAD (proof, not opinion)

An equivariant extension `T` of the transition `τ = tMapFun D l i` on `tsupport (coeffFun …)` exists
only in special cases, so no lemma of the form "replace `τ` by a torus diffeo `T`" can be true:

* every `T : ℝⁿ → ℝⁿ` with `T (z+e) = T z + e` is `id + w̃` with `w̃` `1`-periodic; if in addition
  `T` is a *torus diffeomorphism* then (for `n = 1`) `T` is a homeomorphism of the circle of degree
  `1`, hence **orientation preserving**, `T' > 0`.  But `T|_{V} = τ|_{V}` on a neighbourhood `V` of
  `tsupport (coeffFun …)`, and `D τ_{li}(z) = (finBasis)·D(extChartAt x₀i)·D(extChartAt x₀l)⁻¹·
  (finBasis)⁻¹` is the ratio of two *different* chart Jacobians; its determinant changes sign with
  no constraint at all.  Whenever `det Dτ < 0` on (a component of) `V` (e.g. `τ(x) = 2x`, or any
  orientation reversing transition, on `n = 1`) there is **no** equivariant diffeo agreeing with `τ`
  there.  ⇒ SESSION 18's option (a) must not be attempted; SESSION 18's option (b) (the local layer)
  is the only route.

### (2) ⚠ `S` and `Λ` are chart-INDEPENDENT — the transfer is the only chart-dependent ingredient

`STruncR ρ ε (D.R i h a b) = re ∘ flatCut ρ ε (Rper i h a b)` (`STruncR_eq_flatCut_re`) and
`lamSection D k h i a b = re ∘ lapPow k (Rper i h a b)` (`lamSection_eq_lapPow_re`): the *cutoff*
`S := flatCut ρ ε` and the *Laplacian power* `Λ := lapPow k` used for the chart-`i` components are
literally the SAME operator for every chart `i` (both act on `(ι → ℤ)`-Fourier coefficients).  Hence

* `[Λ, S] = 0`  (they are Fourier multipliers of the same variable), and
* the *only* chart-dependent ingredient is the transfer `L_{il} := R_i R_l^*` (`R_L_eq_zeta_sq`,
  `R_Rstar_eq_psi_sq`, `coeffFun_transfer_Rper`).

With `Qk = Σ_i R_i^* Λ R_i`, `J = Σ_i R_i^* S R_i`, `K := id − J`, the definitions give the exact
(and *symmetric-looking*) form

  `Ξ = D.BPair (Qk D k f) (K u) − D.BPair (K f) (Qk D k u)`            (**K-form**)

(check: `BPair(QkJf,u) = BPair(Jf,Qku) = BPair(f, Qku) − BPair(f, JQku)` by self-adjointness of
`Qk` (`Qk_eq_sum_Rstar`, `BPair_Rstar`) and of `J` (`BPair_J_self_smooth`)).

### (3) The exact chart-`(i,l)` decomposition, and where the gain *cannot* be

`Ξ = Σ_{i,l} CPair_i (ϑ_{il} X_l, V_i)`, `ϑ_{il} = Λ L_{il} S − S L_{il} Λ`, `X_l = R_l f`,
`V_i = R_i u`.  Expanding with `[Λ,S] = 0`,

  `ϑ_{il} = [Λ, L_{il}] S + [L_{il}, S] Λ = Λ L_{il} S − S L_{il} Λ`     (**two-term form**),

and here `[L_{il},S]` is genuinely of order **0** (its symbol is `ρ(ε B^{−T}ξ) − ρ(ε ξ)`, `B = Dτ`,
which does NOT vanish at the transition scale `|εξ| ≃ 1`), while `[Λ,L_{il}]` is of order **2k**
(its principal symbol is `λ(ξ)^k − λ(B^{−T}ξ)^k`).  Consequently

* every single `ϑ_{il}` (and hence `[Qk_i, J_l]` for `i ≠ l`) is of order **2k**, *not* `2k−1`;
* the order-`2k` pieces cancel **only** in the unordered pair `{i,l}`, i.e. in
  `ϑ_{il} + ϑ_{li}` after the two-chart closure `L_{il} X_l = ψ_l² X_i`, `L_{li} X_i = ψ_i² X_l`
  (SESSION 15's `X_{il} = pairOpC`), and in the diagonal `i = l` where `[M_{ψ²},S]`
  (`Friedrichs`, order `−1`) and `[Λ,M_{ψ²}]` (`Leibniz`, order `2k−1`) appear.

### (4) The primitive of the local layer, and the *brick* that is now delegated

In the application `L_{il} W = M_{coeffFun} ∘ comp_{τ_{il}} W`, and every object the assembly may
feed to `Λ = lapPow` / `S = flatCut` is the **periodisation** of a compactly supported function:

  `perTransfer c τ W := (fun z ↦ Σ' m, c (z + iVec m) · W (τ (z + iVec m)))`,   `W` `1`-periodic.

* `CSq_period_comp_arg_le` / `CSq_period_deriv_comp_arg_le` (PROVED) are exactly the *local*
  boundedness of `perTransfer c τ` in `H^s` — **they need only `InjOn τ U` + `det ∘ fderiv ≠ 0` on an
  open `U ⊇ tsupport c`, no equivariance**;
* the *local Friedrichs gain* `[M_{per c}, S]` is the periodic `flat_multiplier_commutator`
  (PROVED) because `per (c · Y) = per c · Y` for `Y` periodic and `S` is a Fourier multiplier;
* the *local Leibniz* `[Λ, M_{per c}]` is the periodic `laplacian_pow_mul_comm_le` (PROVED);
* what was missing is the **local adjointness of the transfer** (the equivariance-dependent
  `compMap_adjoint`), i.e. the change-of-variables identity
  `L2re (perTransfer c τ Y) W = L2re (perTransfer (c∘σ·|det Dτ∘σ|⁻¹) σ W) Y`
  (`σ = τ⁻¹` on `U`).  ⚠ It was delegated this session and the prover found the naive version
  (one-sided inverse `σ` only on `U`) **FALSE** — the periodisation of `c∘σ·|det Dτ∘σ|⁻¹` collects
  the lattice translates `σ ⁻¹' (tsupport c)` outside `τ '' U`, which have no counterpart on the left.
  The proved, axiom-clean version is `Work.Diff.STE.B3.SymCalcStep8.local_transfer_adjoint_of_preimage`
  (`Submission/Work/Diff/STE/B3/SymCalcStep8/local_transfer_adjoint.lean`), which adds the single
  hypothesis `hσpre : ∀ y, σ y ∈ U → y ∈ τ '' U`; two further sufficient forms
  (`local_transfer_adjoint_of_support`, `local_transfer_adjoint_of_rightInverse`) are proved there
  too.  ⚠ That file still contains the FALSE naive statement as a `sorry` — import it but use only
  the `_of_preimage`/`_of_support`/`_of_rightInverse` versions.

### (5) The remaining crux, in the local framework — ⚠ and the *wrong* temptation to avoid

The cross pair, in the local framework, is `Σ_i CPair_i(ϑ_{il}X_l,V_i) + CPair_l(ϑ_{li}X_i,V_l)` with
`ϑ_{il} = Λ L_{il} S − S L_{il} Λ`, `L_{il} = perTransfer (coeffFun D l i …) τ_{il}` (`Λ = lapPow k`,
`S = flatCut ρ ε` — the SAME operators in both charts by (2)).

⚠ **A *single-chart* (one-function) model of the pair is NOT of order `2k−1`**, and must not be
delegated.  The FIO symbol of `perTransfer γ τ` is `γ(z)` with phase `ξ·τ(z)`, so

* `Λ ∘ T_γ ∘ S` has symbol `λ(ξ)^k · γ · ρ(ε (Dτ)^T ξ)`,
* `S ∘ T_γ ∘ Λ` has symbol `ρ(εξ) · γ · λ((Dτ)^T ξ)^k`,

hence the group `a·(Λ(b·T_γ(Sg)) − S(b·T_γ(Λg)))` alone has symbol
`a b γ [ λ(ξ)^k ρ(εB^Tξ) − ρ(εξ) λ(B^Tξ)^k ]` with `B = Dτ` — **order `2k`**, exactly as for
`ϑ_{il}` itself.  Two such groups acting on the SAME periodic `g` (i.e. the operator `localPairOp`
below) have symbols `abγ[λ^kρ(εB^Tξ)−ρ(εξ)λ(B^Tξ)^k] + cdγ'[λ^kρ(εB'^Tξ)−ρ(εξ)λ(B'^Tξ)^k]`, which
does **not** vanish for `B' = B^{-1}` (it needs `(Dτ)^T = (Dτ)^{-T}`, i.e. `Dτ` orthogonal).

The cancellation is real but it needs the **two-chart closure**: in the application `X_l = R_l f`
and `X_i = R_i f` are the two chart components of the SAME section (`L_{il}X_l = ψ_l²X_i`,
`R_L_eq_zeta_sq`; same for `V` with `V_l = R_l u`, `V_i = R_i u`).  The pair `{i,l}` then groups as
`⟨X_i, X_{il}V_i⟩_i` (SESSION 15's `X_{il} = pairOpC`), and in the weights of SESSION 16 the two
leading symbols combine into `[a b γ − c d γ']·λ(B^{−T}ξ)^k ρ(εξ) − [a b γ − c d γ']·ρ(εB^{−T}ξ)
λ(ξ)^k` with `B = Dτ`, which vanishes **iff `a·b·γ = c·d·γ'`** (SESSION 16's relation
`γ ρ₂ = ζ_l² = λ ψ_i²ρ₂`).  ⚠ This last step has NOT been re-verified in the local (non-equivariant)
framework — the exact relation between the four weights, the two closure functions `β, β'` and the
two Jacobians must be re-derived from `coeffFun_transfer_Rper` before the crux is stated.  What IS
certain is the *shape* of the correct crux statement: (i) two *distinct* component functions
(`g_l`, `g_i`) linked by the closure relations, plus the two `V`-components, and (ii) both pairings
`CPair_i`/`CPair_l` (converted to `L2re` by `CPair_eq_L2re_periodisation`).  Stating it with a single
`g` — which is what `localPairOp` below does — makes it **false**; `localPairOp` is kept only as a
*named warning* of that temptation.  `perTransfer` (and the proved
`local_transfer_adjoint_of_preimage`) are the correct primitives. -/

/-! ## SESSION 19b — the exact weight / closure / Jacobian relations (what the pair really needs)

Written down from `coeffFun_eq_weight_mul_orth`, `coeffFun_adjoint`, `coeffFun_transfer_Rper`,
`dens_transition`, `Data.hζsq`.  Notation: `τ_{li} := tMapFun D l i` (chart-`i` → chart-`l`),
`L_{il} = R_i R_l^* = M_{coeffFun D l i} ∘ comp_{τ_{li}}` (chart-`l` → chart-`i`).

**(C) Closure** (`coeffFun_transfer_Rper`, PROVED):
`Σ_{cd} coeffFun D l i a b c d z · (Rper_l f)_{cd}(τ_{li} z) = β_{li}(z) · (R_i f)_{ab}(z)`,
with `β_{li}(z) := (ζ_l(pt_i z))²`; and symmetrically with `(l,i) ↔ (i,l)`.  Note `β_{li}` is a
*chart-i* function and the closure is exact, for an arbitrary atlas and an arbitrary section.

**(U) Partition of unity**: `Σ_i β_{li}(z) = Σ_i (ζ_i(pt_l z))² = 1` (`hζsq`) and likewise
`Σ_l β_{il}(z) = 1`.  This is the identity that makes the *main* terms cancel.

**(A) Adjunction** (`coeffFun_adjoint` + the change of variables, both already available):
`CPair_i(L_{il}Y,Z) = CPair_l(Y,L_{li}Z)` **exactly** — the Jacobian `|det Dσ|` of `z = σy` cancels
against the `|det(tangentCoordChange x₀i x₀l (pt_l y))|⁻¹` of `coeffFun_adjoint`, because
`|det D(tMapFun D i l)(y)| = |det(tangentCoordChange x₀i x₀l (pt_l y))|` and
`det(tangentCoordChange x₀l x₀i p)·det(tangentCoordChange x₀i x₀l p) = 1`.

**(W) Weight product relation** — the relation asked for: on `Ω D l i` (and hence on
`tsupport (coeffFun D l i …)`, where `τ_{li} z ∈ Ω D i l` follows from `hζsupp` + `hχ1`),

`Σ_{cd} coeffFun D l i a b c d z · coeffFun D i l c d a' b' (τ_{li} z)`
  `= ψ_i(z)² · (ψ_l(τ_{li} z))² · δ_{aa'} δ_{bb'}`.

*Proof.*  Insert the two factorisations `coeffFun_eq_weight_mul_orth` (at `z` and at `τ_{li}z`): both
carry the prefactor `ψ_l(τ_{li}z)·ψ_i(z)` and a factor `(√|det 𝒥|)⁻¹`, with `𝒥(z) =
tangentCoordChange x₀l x₀i (pt_i z)` in the first and `𝒥' = tangentCoordChange x₀i x₀l (pt_l(τ_{li}z))
= tangentCoordChange x₀i x₀l (pt_i z)` in the second; these determinants are mutually inverse, so the
two square-root factors multiply to `1`.  The frame matrices are `E_{ac} = ⟪e_i a, e_l c⟫` and
`E_{a'c}` (the same matrix, both evaluated at `pt_i z`), and `Σ_c E_{ac}E_{a'c} = δ_{aa'}` because
`(e_i ·)` is orthonormal at `pt_i z`; same in `b`.  Hence `γ_{il}(z)·γ_{li}(τ_{li}z) = ψ_i²ψ_l²(τ·)`,
**with no Jacobian factor and with the frames cancelling**.  Delegated this session as
`Work.Diff.STE.B3.coeffFun_comp_mul_relation`.

**(W') The same relation at the operator level** (three lines from the two PROVED section-level
identities `Rstar_R_eq_zeta_sq_free` — `R_l^*(R_l h) = ζ_l²·h` — and `R_Rstar_eq_psi_sq` —
`R_i(R_i^*w) = ψ_i²·w` — plus the elementary rule `R_i(a·Z)_{ab}(z) = a(pt_i z)·R_i(Z)_{ab}(z)`):

  `L_{il} ∘ L_{li} = M_{ψ_i² · (ζ_l∘pt_i)²}`,      `L_{li} ∘ L_{il} = M_{ψ_l² · (ζ_i∘pt_l)²}`,

i.e. the two transfers compose to the *multiplication* by the closure factor `β_{il} = (ζ_l∘pt_i)²`
times `ψ_i²`.  Composing (W') with (C) reproduces (W): `γ_{il}(z)·γ_{li}(τ_{li}z) = ψ_i²(z)·ψ_l²(τ_{li}z)`
on `Ω D l i` (using `χ_l(τ_{li}z) = 1`, which follows from `ζ_l(pt_i z) ≠ 0` via `hζsupp`+`hχ₁`).

**(M₀) ⚠ Hand-derived this session, NOT yet machine-checked — the `Σ_i β = 1` cancellation.**
Carrying out the computation of (M) symbolically (using (C) twice, (A), `ΛS = SΛ` and
linearity/self-adjointness of `CPair_l`) shows that for each pair the *main* (order-`2k`) bracket of
`CPair_i(ϑ_{il}X_l, V_i)` is

  `- CPair_l(X_l, [Λ, M_{β_{li}}] S V_l)`      (a single Leibniz bracket, order `2k−1`),

and that **the `i`-sum of these main brackets vanishes identically**, because the `β_{li}` are exactly the
partition of unity of (U):

  `Σ_i (- CPair_l(X_l, [Λ, M_{β_{li}}] S V_l)) = - CPair_l(X_l, [Λ, Σ_i M_{β_{li}}] S V_l)
     = - CPair_l(X_l, [Λ, 1] S V_l) = 0`.

This is a *second*, independent cancellation mechanism (session-level, over the cover, using
`hζsq`) alongside SESSION 15's pairwise four-symbol one; it also explains why the *single-chart* model
of `localPairOp` had to be false.  What survives per pair are only
(i) the Friedrichs brackets `[S, M_β]` (order −1) — the periodic `flat_multiplier_commutator`;
(ii) the Leibniz brackets `[Λ, M_β]` paired with `S V` (order `2k−1` — the periodic
`laplacian_pow_mul_comm_le`); (iii) the two defect operators `\mathcal{D} = [Λ,L]` and
`\mathcal{C} = [L,S]`, whose combination was shown by hand to reduce (via `[L,Λ]` / `[L,S]`
definitions, (C) and (A), and `ΛS = SΛ`) to *another copy* of the same main bracket — i.e. it does
not introduce a new order-`2k` object.  ⚠ All of (M₀)'s algebra is hand-derived; it must be
machine-checked (or rejected) before the pair estimate is stated.

**(M) Consequence — the main terms cancel exactly.**  With (C), (A) and (U): for the pair `{i,l}`, the
two halves of `CPair_i(ϑ_{il}X_l,V_i)` are
`CPair_l(SX_l, L_{li}(ΛV_i))` and `-CPair_l(ΛX_l, L_{li}(SV_i))`, and using (C) in the forms
`L_{li}(ΛV_i) = M_{β_{li}}ΛV_l + [Λ,M_{β_{li}}]V_l - \mathcal{D}_{li}V_i` (`\mathcal{D}_{li} :=
[Λ,L_{li}]`) and `L_{li}(SV_i) = M_{β_{li}}SV_l + \mathcal{C}_{li}V_i` (`\mathcal{C}_{li} :=
[L_{li},S]`), the *main* bracket is

  `CPair_l(SX_l, M_{β_{li}}ΛV_l) − CPair_l(ΛX_l, M_{β_{li}}SV_l) = -CPair_l(X_l, [Λ,M_{β_{li}}]SV_l)`

(an order-`2k−1` Leibniz bracket), and summing over `i` at fixed `l` the main bracket *vanishes*:
`Σ_i [Λ,M_{β_{li}}] = [Λ,M_{Σ_iβ_{li}}] = [Λ,1] = 0` by (U).  The same happens in the reversed
direction.  So `Ξ` is, exactly, a sum of
* order-`2k−1` Leibniz pieces `[Λ,M_{β}]`,
* order-`−1` Friedrichs pieces `[S,M_{β}]`,
* the two defect operators `\mathcal{D} = [Λ,L]` and `\mathcal{C} = [L,S]`,
each of which is *individually* too large only in the `\mathcal{D}`/`\mathcal{C}` combination (which
is exactly the single-chart-model falsity of (5)).  The remaining analytic work of the pair is the
bound of that combination; the weights it carries are now known: `β_{li} = (ζ_l∘pt_i)²`, `β_{il} =
(ζ_i∘pt_l)²`, with `Σ_iβ_{li} = 1`, and the transfer weights satisfy (W). -/

/-! ## SESSION 21 — ⚑ THE ROUTE CLOSES. Read this block first; it replaces SESSIONS 14–19.

Everything after this block (SESSION 19, 19b, 19j, `perTransfer`, the strip/collar layers) is
*dead*: it transports the cutoff `S` or the flat Laplacian `Λ` between charts, which is what makes
the equivariance/collar obstructions appear.  **Never transport `S` or `Λ`.  Transport the
DIFFERENTIAL OPERATOR `Q_k` instead** — its chart expression has *smooth* coefficients, and the
resulting flat estimate is the lead's `VarCoef.varLapPow_cut_comm_pairing` (H3336), which is being
proved right now by the order calculus in `Submission/Work/Diff/STE/B3/VarCoef/`.

### (1) The reduction (all of it is PROVED or a one-line adjunction)

`Ξ := ENormB_pair k (J ρ ε f) u − ENormB_pair k f (J ρ ε u) = BPair ([Qk D k, D.J ρ ε] f) u`
(`ENormB_pair_commutator_eq_BPair_JQk`, in this file).  With `J = Σ_l J_l`, `J_l := R_l^*(S_l(R_l·))`
(`S_l = STruncR ρ ε`, i.e. `flatCut ρ ε` on the chart-l torus), and the two adjunctions
`BPair(J_l X, Y) = CPair_l(S_l R_l X, R_l Y)` (`BPair_Rstar`) and `BPair(X,Y) = BPair(Y,X)`:

  `Ξ = Σ_l [ CPair_l(S_l R_l f, R_l(Qu)) − CPair_l(R_l(Qf), S_l R_l u) ]`   (**)

(use `Q`-self-adjointness on the first half and `J_l`-self-adjointness on the second).  No
`[Q,J_l]` is ever split — the pairing is kept whole.

### (2) ⚑ The chart expression of `Q` — a differential operator with SMOOTH coefficients

`Q = Σ_i Q_i`, `Q_i = R_i^*Λ_i R_i`, `Λ_i = lapPow k` on the chart-i torus.  For the chart-`l`
component:
  `R_l(Qh)_{ab}(z) = Σ_i Σ_{cd} coeffFun D l i a b c d z · Λ_i(R_i h)_{cd}(tMapFun D l i z)`
  (`R_Qk_pointwise_expansion`, in this file; `tMapFun D i l z = coord_i(pt_l z)`).
Write `coeffFun D l i a b c d z = φ_l(z)·(ζ_iχ_i/ρ_i)(τ z)·⟪e_la,e_ic⟫⟪e_lb,e_id⟫` with
`φ_l := ψ_l·√dens_l` and `τ := tMapFun D i l`, and use `ζ_iχ_i(y) = ψ_i(y)`
(`ψ_i = χ_i·(ζ_i∘pt_i)`), so the *ζ never divides*.  In terms of the CHART MATRIX `mat_l h`
(`R_l h = φ_l·mat_l h`):

  `mat_l(Qh)_{ab}(z) = Σ_{i,c,d} (ψ_i/ρ_i)(τ z)·⟪e_la,e_ic⟫(pt_lz)⟪e_lb,e_id⟫(pt_lz)
                        · [varLapPow k A_i B_i (G_{i,cd})](z)`,

where `A_i,B_i` are the chain-rule coefficients of `τ` (exactly the hypotheses `hAW`,`hBW` of the
PROVED `VarCoef.lapPow_comp_eq_varLapPow`, instantiated with `τ := tMapFun D l i`,
`σ := tMapFun D i l`), and
  `G_{i,cd}(z) = ψ_i(τ'z)ρ_i(τ'z)·Σ_{c'd'}⟪e_ic,e_lc'⟫(pt_lz)⟪e_id,e_ld'⟫(pt_lz)·mat_lh_{c'd'}(z)`
with `τ' := tMapFun D i l` (`pt_i(τ'z) = pt_l z`, so the frame change is pure bilinearity of
`h : Bil = Π p, E →L E →L ℝ` in the two orthonormal frames at the *same* point).  Both
ingredients are available: the **chain rule** `Λ_i(R_ih)(τz) = varLapPow k A_iB_i(G)`
(`VarCoef.lapPow_comp_eq_varLapPow`, `w = G∘σ`) and the **locality**
`VarCoef.lapPow_apply_eq_of_eventuallyEq` (`Λ_i` really sees the periodisation `Rper_i h`, which
agrees with `R_i h` as a germ at `τz`).

So there are **smooth `1`-periodic** families `A i, B i, ci, co` with

  `R_l(Qk D k h)_{ab}(z) = φ_l(z) · Σ_{i,c,d} co_{iabcd}(z)
        · (varLapPow k A_iB_i)(Σ_{c'd'} ci_{icdc'd'} · mat_lh_{c'd'})(z)`   (CE)

⚠⚠ **The factor `φ_l` must stay OUTSIDE the differential operator** — this is the point that two
reviewers of the first draft of (CE) caught.  `mat_l h` is *not* `R_l h/φ_l` for a smooth
`1/φ_l`: `1/φ_l` blows up on `∂{ψ_l ≠ 0}` (where `ψ_l → 0` but the core coefficient
`ψ_i(τ'·)ρ_i(τ'·)` stays bounded away from `0` when `|ι₀| ≥ 2`).  Conversely writing the inner
function as `ci·(R_l h)` also fails: no smooth `ci` reproduces `ci·R_lh = γ·mat_lh` on the whole
open set `{ψ_l ≠ 0}`.  The pair `(ci, mat_l h)` with `ci` smooth and `co` carrying `φ_l` is the
only one of the three that works.  (Delegated as `VarCoef.R_Qk_chartExpr`; both `ci, co` are
*periodisations* of honest compactly supported expressions, hence literally `1`-periodic, and
`mat_l h` is only read where the chart is honest.)

### (3) The two halves of (**) and the three estimates they consume

`S_l = STruncR ρ ε` is a *real* Fourier multiplier, hence selfadjoint for `CPair_l`.  Put
`φ_l := ψ_l·√dens_l`, `X_l := M_{φ_l} ∘ S_l ∘ M_{φ_l}`, and let `P_l` be the (matrix)
differential operator of (CE) *without* the outer `φ_l`:
`(P_l v)_{ab} = Σ_{i,c,d} co_{iabcd}·(varLapPow k A_iB_i)(Σ_{c'd'}ci_{icdc'd'}·v_{c'd'})`.
Then `R_l(Qh) = M_{φ_l}(P_l(mat_lh))`, and the selfadjointness of `S_l` and of `M_{φ_l}` gives

  (**)  `= Σ_l [ L2re( mat_lf , X_l P_l mat_lu ) − L2re( P_l mat_lf , X_l mat_lu ) ]`

(all pairings entrywise, `L2re` in the first slot convention of the flat lemma).  This is
*exactly* the shape of the flat lemma `VarCoef.varLapPow_cut_comm_pairing` with the `M_ψSM_ψ` slot
instantiated at `ψ := φ_l`, and `P := M_{co_{iabcd}}∘(varLapPow k A_iB_i)∘M_{ci_{icdc'd'}}` for a
single `(i,a,b,c,d,c',d')` — the lemma quantifies over `F` and `U` freely, so no index matching is
needed.  The two estimates:

* **(E1)** the pairing bound for each `(i,a,b,c,d,c',d')` — the lead's flat lemma
  `VarCoef.varLapPow_cut_comm_pairing` (H3336), applied with `ψ := φ_l`.  Its two inputs are
  `F = (mat_lf)_{ab}` and `U = (mat_lu)_{c'd'}`.
* **(E2)** `Φ_l − Φ_l^*` has order `≤ 2k−1`, where `Φ_l` is the matrix operator with entries
  `Φ^{ab,c'd'}_l = Σ_{i,c,d}M_{co_{iabcd}}∘(varLapPow k A_iB_i)∘M_{ci_{icdc'd'}}`.  Reason: a
  differential operator of order `2k` with real smooth coefficients whose top-order symbol is a
  REAL SCALAR (`σ(z,ξ)·Id` — which holds here because `Q`'s principal symbol is the scalar
  `Σ_cψ_c²|dτ_c^Tξ|^{2k}`) satisfies `Φ − Φ^* = (order ≤ 2k−1)` — the top-order commutator
  `a_α∂^α − ∂^α(a_α·)` drops one order **and** the top coefficient matrix is symmetric.
  ⚠ This is exactly the place where the `φ_l`-weight is essential: without it the operator is a
  *matrix* differential operator and the symmetry of the top coefficient must be proved (it is the
  identity `Σ_{i,c,d}co_{iabcd}ci_{icdc'd'} = σ δ_{(ab),(c'd')}`, i.e. the two frame changes are
  inverse to each other).
* **(E3)** the norm bookkeeping.  `CSq ↔ ENormSq` (`CSq_le_ENormSq`, `ENormSq_le_CSq`,
  monotonicity), `CPair_l ↔ L2re` (`CPair_eq_L2re_periodisation`), Cauchy–Schwarz over the finitely
  many `l`, and the two `Real.sqrt` factors.  The norms needed are
  `√(CSq(k−1)\widehat{mat_lf}) ≤ C√(E_{k-1}f+E_0f)` and `√(CSq k\widehat{mat_lu}) ≤ C√(E_k u)`,
  i.e. the **change of partition for the chart matrix**
  `mat_l h_{ab}(z) = Σ_i ζ_i(pt_lz)·(frame)·(R_i h)_{a'b'}(τ'z)/ρ_i(τ'z)`
  (from `Σ_iζ_i² = 1`; note the `ζ_i` *multiplies* `R_i h`, so there is no division by `ζ_i`:
  `ζ_i²·mat_ih(τ'z) = ζ_i·R_ih(τ'z)/ρ_i(τ'z)`), which is smooth-coefficient and controlled at every
  level `s`.  Delegated as `VarCoef.mat_csq_le_components`.  ⚠ **`hk : finrank < 2k` is not used**
  by this route.

### (4) What is still to be done (the whole remaining task)

1. (CE) — the chart expression.  **Delegated**: `VarCoef.R_Qk_chartExpr` (H3336-L3368).
2. (E1) — `VarCoef.varLapPow_cut_comm_pairing` (H3336, being finished right now by the order
   calculus in `VarCoef/VarCoefAssembly.lean`).
3. (E3) — the change of partition for the chart matrix.  **Delegated**:
   `VarCoef.mat_csq_le_components` (L3371).
4. (E2) and the assembly — mine, in this file.

⚠ Do **not** resurrect: the `ϑ_{il}` pair form, `pairOp`/`pairOpC`, `SymCalcStep7/8` transfers,
`perTransfer`, the collar/strip, `S^♯`, or the equivariance discussion.  They are all attempts to
move `S`/`Λ` between charts, and §(2) shows that the right move is to move `Q`. -/

/-! ## SESSION 22 — ⚑ THE BUILD CYCLE IS FIXED AND THE ROUTE IS UNBLOCKED. Read this first.

**Blocker (fixed this session).**  This file must import the `VarCoef` layer ((E1) = order calculus
pairing bound, (CE) = chart expression of `Qk`, (E3) = chart-matrix norm change, (E2) = defect
order bound).  That was IMPOSSIBLE: `VarCoef/Assembly.lean` imported `SymCalcStep8/pdTransferKit.lean`
(and `SymCalcStep8/perTransfer_csq_le_of_support.lean`) which imported THIS file — for the
definition `perTransfer`, which used to be defined here.  The three definitions
(`perTransfer`, `localPairOp`, `clippedInv`, `stripFun`) have been **moved to**
`Submission/Work/Diff/STE/B3/perTransferDef.lean` (same fully qualified names), and the two
`SymCalcStep8` files now import that module.  This file imports it too, so every existing user is
unaffected.  Consequently the imports below are now legal and the cycle is gone.  See
`HANDOFF.md`, SESSION 22 §A, for the exact list of edits (do not revert them).

**Everything the estimate needs is now PROVED** (all sorry-free):
`VarCoef.varLapPow_cut_comm_pairing` (E1), `VarCoef.R_Qk_chartExpr_sym` (CE + the termwise
symmetry of the coefficients on `‖z‖ ≤ 2σ_l`), `VarCoef.mat_csq_le_components` (E3),
`VarCoef.POp_swap_sub_star_isOrd` (E2), and `ENormB_pair_commutator_chart_split_pairing` (proved
above in this file), which turns `Ξ` into `Σ_l [ CPair_l(S_lR_lf, R_l(Qk u)) −
CPair_l(S_lR_l(Qk f), R_l u) ]`.

**The remaining assembly is Step 2–4 of `HANDOFF.md`, SESSION 22 §C** (written out in full there):
periodise everything (`Ml h := per(η·mat_lh)`, `Ψ_l := per(φ_l)`, `X_l := M_Ψ ∘ flatCut ρ ε ∘ M_Ψ`),
rewrite `Ξ = Σ_{l,α,β} L2re(Ml f_α, (X_lP^{αβ} − (P^{βα})^*) (Ml u)_β)`, split
`= [X_l,P^{αβ}] + (P^{αβ}−(P^{βα})^*)X_l`, bound the commutator half by (E1), the defect half by
(E2) + `L2re_le_sqrt_CSqZ`, sum with `VarCoef.sum_pairing_le`, and convert the norms with (E3)
summed over the charts (`VarCoef.sum_mat_csq_le_ENormB`). -/

namespace Work.Diff.STE.B3

set_option maxHeartbeats 6400000

/-! ## SESSION 19 — the local transfer layer (definitions used by the delegated brick)

`perTransfer c τ W` is the **periodisation** of `c · (W ∘ τ)`: for `W` `1`-periodic and `c` smooth,
compactly supported, this is the component-level chart transfer `L_{il} W` with `c` the transfer
coefficient and `τ` the transition map — and it is a *well-defined* periodic (smooth) function,
unlike `compMap τ W`.  All the objects that the assembly feeds to `Λ = lapPow k` and
`S = flatCut ρ ε` are of this shape (SESSION 19 (2)/(4) of the header).

(⚠ SESSION 22: the definitions `perTransfer`, `localPairOp`, `clippedInv`, `stripFun` that used to
live here have been moved to `Submission/Work/Diff/STE/B3/perTransferDef.lean`, because the low-level
`SymCalcStep8` files need `perTransfer` and importing this module from them created a build cycle.
The fully qualified names are unchanged.) -/

/-! ## SESSION 19j — the chart-level STRIP data of the range-inverse construction

`L^♭ := perTransfer γinv σ` is a **right inverse of `L := perTransfer γ τ` on the range of `S`**, not a
two-sided inverse on `L²` (project-lead decision, header SESSION 19h): the exact normaliser `1/perγ`
may be consumed only where `perγ ≥ c₀`, and on the boundary strip one does *not* invert pointwise —
the commutation through `S` does the killing.  The two objects below name the data of that
construction; they are the summands the assembly must carry.

* `clippedInv χ γ` is the **clipped normaliser**: `χ` is the clipping function of each chart (`1`
  where the normalisation is imposed, `0` where `perγ` is too small), and the value is `χ/perγ`.
* `stripFun γ γinv σ` is the **boundary-strip multiplier** `1 − γinv·(γ∘σ)` of the pair
  `(γ, γinv)`: it vanishes wherever the normalisation `γinv·(γ∘σ) = 1` holds, and is supported in the
  strip near `∂{γ ≠ 0}` where it cannot hold.  Its pairing against `Λ V` is of order `2k` (it is a
  *multiplication*), so it must be absorbed, not discarded — see SESSION 19h for why nothing cancels
  it inside a single `T_{il}` (the closure `L_{il}∘L_{li}` is a product, not a difference). -/

/- The **clipped normalising inverse** and the **boundary-strip multiplier** `1 − γinv·(γ∘σ)` are
defined in `Submission/Work/Diff/STE/B3/perTransferDef.lean` (SESSION 22; moved there to break a
build cycle). -/

/- **The local adjointness of the chart transfer** (SESSION 19 (4)): the change-of-variables
identity that replaces the equivariance-dependent `compMap_adjoint`.  For a smooth `τ` which is
injective with invertible Jacobian on an open `U` containing the (compact) support of `c`, and a
smooth `σ` inverting `τ` there, the `L²` pairing of the transfer with a periodic `W` equals the
pairing of the reversed transfer (with the Jacobian weight `|det Dτ∘σ|⁻¹`, `σ = τ⁻¹`) with `Y`.
It is delegated this session as
`Work.Diff.STE.B3.SymCalcStep8.local_transfer_adjoint_of_preimage`
(`Submission/Work/Diff/STE/B3/SymCalcStep8/local_transfer_adjoint.lean`), with the extra hypothesis
`hσpre : ∀ y, σ y ∈ U → y ∈ τ '' U` (the naive one-sided-inverse form is FALSE — see (4)). -/

/-- **ASSEMBLY STEP 1 (SESSION 11).**  The exact chart decomposition of the commutator pairing.

With `Ξ := ENormB_pair k (Jf) u − ENormB_pair k f (Ju) = BPair ([Qk,J]f,u)`, this lemma rewrites
the *second* form of `Ξ` obtained from the definitions solely (see the SESSION 11 block of the
header): pairing `Qk (Jf)` with `u` on the one hand, and `J (Qk f)` with `u` on the other, and using
that `J` is self-adjoint (`BPair_J_self_smooth`) plus the reconstruction
`Qk h = Σ_i R_i^* (lamSection D k h i)`, one gets

  `Ξ = Σ_i CPair_i (Λ_i^k (R_i (Jf)), R_i u) − Σ_i CPair_i (Λ_i^k (R_i f), R_i (Ju))`.

The next step is to expand `R_i (Jf) = Σ_l L_{il} (S_l x_l)` and `R_i (Ju) = Σ_l L_{il} (S_l v_l)`
(pointwise, via `D.R_Rstar_expansion_pointwise_noT2`) and to use linearity of `Λ_i^k` over that
finite sum, which produces `Σ_{i,l} CPair_i (ϑ_{il} x_l, v_i)` with
`ϑ_{il} = Λ_i^kL_{il}S_l − S_iL_{il}Λ_l^k`. -/
lemma BPair_commutator_chart_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (f u : Bil (I := I) (M := M))
    (hf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b))
    (hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b))
    (hJf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (D.J ρ ε f) a b))
    (hJu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (D.J ρ ε u) a b))
    (hQf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (Qk D k f) a b)) :
    D.BPair (Qk D k (D.J ρ ε f)) u - D.BPair (D.J ρ ε (Qk D k f)) u
      = (∑ i, B3Data.CPair i (lamSection D k (D.J ρ ε f) i) (D.R i u))
        - ∑ i, B3Data.CPair i (lamSection D k f i) (D.R i (D.J ρ ε u)) := by
  have h1 : D.BPair (Qk D k (D.J ρ ε f)) u
      = ∑ i, B3Data.CPair i (lamSection D k (D.J ρ ε f) i) (D.R i u) := by
    rw [Qk_eq_sum_Rstar D k (D.J ρ ε f)]
    exact BPair_J_lin D u (lamSection D k (D.J ρ ε f))
      (fun i a b =>
        show Continuous (fun z => (Work.Diff.STE.seriesFun
          (lamCoeff D k (D.J ρ ε f) i a b) z).re) from
          Complex.continuous_re.comp (contDiff_lamCoeff_seriesFun (I := I) (M := M) D k
            (D.J ρ ε f) i a b (hJf i a b)).continuous)
      (fun j a b => mat_continuousOn_chi (I := I) (M := M) D u hu j a b)
  have h2 : D.BPair (D.J ρ ε (Qk D k f)) u
      = ∑ i, B3Data.CPair i (lamSection D k f i) (D.R i (D.J ρ ε u)) := by
    rw [BPair_J_self_smooth (I := I) (M := M) D ρ hρ ε hε (Qk D k f) u hQf hu]
    rw [Qk_eq_sum_Rstar D k f]
    exact BPair_J_lin D (D.J ρ ε u) (lamSection D k f)
      (fun i a b =>
        show Continuous (fun z => (Work.Diff.STE.seriesFun (lamCoeff D k f i a b) z).re) from
          Complex.continuous_re.comp (contDiff_lamCoeff_seriesFun (I := I) (M := M) D k f
            i a b (hf i a b)).continuous)
      (fun j a b => mat_continuousOn_chi (I := I) (M := M) D (D.J ρ ε u) hJu j a b)
  rw [h1, h2]

/-- **ASSEMBLY STEP 1b (SESSION 11).**  The pointwise chart expansion of the chart-`i` component of
`J ρ ε f = Σ_l R_l^* (S_l (R_l f))`: it is the sum over the charts `l` of the transfer coefficient of
`(l,i)` times the cut-off component `S_ε (R_l f)_{cd}` evaluated at the transition point.  Combined
with `BPair_commutator_chart_split` and with the linearity of `Λ_i^k` over the finite sum, this is
what produces the exact identity `Ξ = Σ_{i,l} CPair_i(ϑ_{il}x_l, v_i)`. -/
lemma R_J_pointwise_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (f : Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    D.R i (D.J ρ ε f) a b z
      = ∑ l : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          Work.Diff.STE.D.coeffFun (I := I) (M := M) D l i a b c d z
            * B3Data.STruncR ρ ε (D.R l f c d)
                (Work.Diff.STE.D.tMapFun (I := I) (M := M) D l i z) := by
  have hlin : D.R i (D.J ρ ε f) a b z
      = ∑ l : ι₀, D.R i (D.Rstar l (fun a b z =>
          B3Data.STruncR ρ ε (D.R l f a b) z)) a b z := by
    simp only [B3Data.J, B3Data.R, B3Data.mat, Finset.sum_apply, sum_apply, Finset.mul_sum]
  rw [hlin]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [R_Rstar_expansion_pointwise_noT2]

/-- `L2re` is symmetric (unconditional). -/
private lemma L2re_comm' {n : ℕ} (f g : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.L2re f g = Work.Diff.STE.L2re g f := by
  simp only [Work.Diff.STE.L2re]
  have h1 : (∫ x in Work.Diff.STE.unitCube (ι := Fin n), g x * star (f x))
      = ∫ x in Work.Diff.STE.unitCube (ι := Fin n), (starRingEnd ℂ) (f x * star (g x)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [map_mul]
    simp [mul_comm]
  rw [h1, integral_conj]
  simp

/-- The physical energy pairing is symmetric. -/
private lemma ENormB_pair_comm'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (u v : Bil (I := I) (M := M)) :
    D.ENormB_pair k u v = D.ENormB_pair k v u := by
  unfold Work.Diff.STE.B3Data.ENormB_pair
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun l _ => L2re_comm' _ _))))

/-- The composite pairing is symmetric. -/
private lemma BPair_comm'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : B3Data (I := I) (M := M) ι₀ g₀)
    (h k : Bil (I := I) (M := M)) : D.BPair h k = D.BPair k h := by
  unfold Work.Diff.STE.B3Data.BPair Work.Diff.STE.B3Data.CPair
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)

/-- **ASSEMBLY STEP 1c (SESSION 14).**  The pointwise chart expansion of the chart-`i` component of
`Qk D k h = Σ_l Rstar l (lamSection D k h l)`: verbatim the analogue of `R_J_pointwise_expansion`
with the cutoff component `STruncR ρ ε (R_l h)` replaced by the *flat Laplacian* component
`lamSection D k h l`.  Together with `R_J_pointwise_expansion` this exhibits, chart by chart, all
four factors of the two pairings `D.BPair (D.J ρ ε f) (Qk D k u)` and `D.BPair (Qk D k f) (D.J ρ ε u)`
whose difference is the left-hand side of the target (see the SESSION 14 block of the header). -/
lemma R_Qk_pointwise_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (h : Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    D.R i (Qk D k h) a b z
      = ∑ l : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          Work.Diff.STE.D.coeffFun (I := I) (M := M) D l i a b c d z
            * lamSection D k h l c d
                (Work.Diff.STE.D.tMapFun (I := I) (M := M) D l i z) := by
  have hlin : D.R i (Qk D k h) a b z
      = ∑ l : ι₀, D.R i (D.Rstar l (lamSection D k h l)) a b z := by
    simp only [Qk_eq_sum_Rstar, B3Data.R, B3Data.mat, Finset.sum_apply, sum_apply, Finset.mul_sum]
  rw [hlin]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [R_Rstar_expansion_pointwise_noT2]

/-- **ASSEMBLY STEP 1d (SESSION 14).**  The bilinear form `Ξ` of the target is, *definitionally*,
the difference of the two `BPair` pairings formed with `D.J ρ ε` and `Qk D k`:

  `Ξ = BPair (J f) (Qk u) − BPair (Qk f) (J u)`

— because `Qk` and `D.J ρ ε` are self-adjoint for `D.BPair` and `BPair` is symmetric.  This is the
form in which all four factors have a *pointwise* chart expansion (`R_J_pointwise_expansion` for
`R_i (J h)` and `R_Qk_pointwise_expansion` for `R_i (Qk h)`), so it is the starting point of any
chart-level estimate; the equivalent forms of the SESSION 11/13 blocks all use the adjunctions to
move the `Λ` onto the first slot, which is what creates the `ϑ` operators. -/
lemma ENormB_pair_commutator_eq_BPair_JQk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (f u : Bil (I := I) (M := M))
    (hf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b))
    (hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b))
    (hJf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (D.J ρ ε f) a b))
    (hJu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (D.J ρ ε u) a b))
    (hQf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (Qk D k f) a b))
    (hQu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (Qk D k u) a b)) :
    D.ENormB_pair k (D.J ρ ε f) u - D.ENormB_pair k f (D.J ρ ε u)
      = D.BPair (D.J ρ ε f) (Qk D k u) - D.BPair (Qk D k f) (D.J ρ ε u) := by
  have h1 := ENormB_eq_BPair_Qk (I := I) (M := M) D k (D.J ρ ε f) u hJf hu
  have h2 := ENormB_eq_BPair_Qk (I := I) (M := M) D k f (D.J ρ ε u) hf hJu
  have h3 : D.BPair (Qk D k (D.J ρ ε f)) u = D.BPair (D.J ρ ε f) (Qk D k u) := by
    have e1 : D.BPair (Qk D k (D.J ρ ε f)) u = D.ENormB_pair k (D.J ρ ε f) u := h1.symm
    have e2 : D.ENormB_pair k (D.J ρ ε f) u = D.ENormB_pair k u (D.J ρ ε f) :=
      ENormB_pair_comm' D k (D.J ρ ε f) u
    have e3 : D.ENormB_pair k u (D.J ρ ε f) = D.BPair (Qk D k u) (D.J ρ ε f) :=
      ENormB_eq_BPair_Qk (I := I) (M := M) D k u (D.J ρ ε f) hu hJf
    have e4 : D.BPair (Qk D k u) (D.J ρ ε f) = D.BPair (D.J ρ ε f) (Qk D k u) :=
      BPair_comm' D (Qk D k u) (D.J ρ ε f)
    rw [e1, e2, e3, e4]
  rw [h1, h2, h3]

/-! ### The two "dictionary" lemmas of SESSION 16 §5(b)

The library's flat cutoff `STruncR ρ ε` and flat Laplacian power `lamSection D k · i` on a
localised component are the flat operators `flatCut ρ ε` and `lapPow k` of the `SymCalc*` layer
applied to the **periodisation** `D.Rper i h`.  These are the identities that let the chart-level
pair of SESSION 16 §2 be rewritten in the flat vocabulary of
`SymCalcStep7.pair_form_C_pairing_le`. -/

/-- **Dictionary 1**: the flat cutoff of a localised component is `flatCut` of its periodisation. -/
lemma STruncR_eq_flatCut_re
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (i : ι₀)
    (h : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    B3Data.STruncR (E := E) ρ ε (D.R i h a b)
      = fun z => (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (D.Rper i h a b) z).re := rfl

/-- **Dictionary 2**: the flat Laplacian power of a localised component is `lapPow` of its
periodisation. -/
lemma lamSection_eq_lapPow_re
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    lamSection D k h i a b
      = fun z => (Work.Diff.STE.B3.SymCalcStep5.lapPow k (D.Rper i h a b) z).re := rfl

/-- **ASSEMBLY STEP 2 (SESSION 22).**  The chart split of the commutator pairing into the single
product pairings over the charts `l`.

With `J = D.J ρ ε`, `Q = Qk D k`, `S_l = STruncR ρ ε` and `Q = Σ_l R_l^* (Λ_l (R_l ·))`, the
self-adjointness of `Q` (for `BPair`) and of `J_l = R_l^*(S_l(R_l·))`, together with the adjunction
`BPair (R_l^* w) k = CPair_l w (R_l k)`, rewrite the difference as

  `Ξ = Σ_l CPair_l (S_l (R_l f), R_l (Q u)) − Σ_l CPair_l (S_l (R_l (Q f)), R_l u)`.

This is the form in which the *cutoff* `S_l` and the *differential operator* `Q` are read in the
SAME chart `l` — the starting point of the SESSION 21 route (no transport of `S` or `Λ`). -/
lemma ENormB_pair_commutator_chart_split_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (f u : Bil (I := I) (M := M))
    (hf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b))
    (hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b)) :
    D.ENormB_pair k (D.J ρ ε f) u - D.ENormB_pair k f (D.J ρ ε u)
      = (∑ l : ι₀, B3Data.CPair l
            (fun a b z => B3Data.STruncR ρ ε (D.R l f a b) z) (D.R l (Qk D k u)))
        - ∑ l : ι₀, B3Data.CPair l
            (fun a b z => B3Data.STruncR ρ ε (D.R l (Qk D k f) a b) z) (D.R l u) := by
  have hJf := Work.Diff.STE.B3.SymCalcStep2.R_J_contDiff D ρ hρ0 ε hε f hf
  have hJu := Work.Diff.STE.B3.SymCalcStep2.R_J_contDiff D ρ hρ0 ε hε u hu
  have hQf := Work.Diff.STE.B3.SymCalcStep2.R_Qk_contDiff D k f hf
  have hQu := Work.Diff.STE.B3.SymCalcStep2.R_Qk_contDiff D k u hu
  rw [ENormB_pair_commutator_eq_BPair_JQk D ρ hρ k ε hε f u hf hu hJf hJu hQf hQu]
  congr 1
  · show D.BPair (∑ i, D.Rstar i
        (fun a b z => B3Data.STruncR ρ ε (D.R i f a b) z)) (Qk D k u) = _
    exact BPair_J_lin_smooth (I := I) (M := M) D (Qk D k u)
      (fun i a b z => B3Data.STruncR ρ ε (D.R i f a b) z)
      (fun i a b => (contDiff_STruncR' ρ hρ ε (D.R i f a b) (hf i a b)
        (support_R_subset D i f a b)).continuous)
      (fun j a b => (hQu j a b).continuous)
  · rw [← BPair_J_self_smooth (I := I) (M := M) D ρ hρ ε hε (Qk D k f) u hQf hu]
    show D.BPair (∑ i, D.Rstar i
        (fun a b z => B3Data.STruncR ρ ε (D.R i (Qk D k f) a b) z)) u = _
    exact BPair_J_lin_smooth (I := I) (M := M) D u
      (fun i a b z => B3Data.STruncR ρ ε (D.R i (Qk D k f) a b) z)
      (fun i a b => (contDiff_STruncR' ρ hρ ε (D.R i (Qk D k f) a b) (hQf i a b)
        (support_R_subset D i (Qk D k f) a b)).continuous)
      (fun j a b => (hu j a b).continuous)

/-! ### SESSION 23: the assembly helpers -/

/-- The "outer" index of the assembly: the chart `l` together with the component indices `α`, `β`
of the chart matrices. -/
private abbrev OIdx (ι₀ : Type*) (n : ℕ) := ι₀ × (Fin n × Fin n) × (Fin n × Fin n)

/-- The full index of the commutator half: the outer index together with the `(i,c,d)`-term of the
chart expression of `Qk`. -/
private abbrev CIdx (ι₀ : Type*) (n : ℕ) := OIdx ι₀ n × (ι₀ × Fin n × Fin n)

/-- **The chart cutoff.**  For every chart `l` there is a smooth cutoff `η` which is `1` on the
closed `σ l`-ball, whose topological support lies in the open centred cube *and inside the set where
the chart matrix is smooth* (the preimage of the interior of the chart target). -/
private lemma exists_chart_cut
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀) :
    ∃ η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ l → η z = 1) ∧
      tsupport η ⊆ Set.pi Set.univ
        (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, z ∈ tsupport η →
        Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
          interior ((extChartAt I (D.x₀ l)).target)) ∧
      HasCompactSupport η := by
  classical
  let U : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    {z | Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
        interior ((extChartAt I (D.x₀ l)).target)} ∩
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
  have hUopen : IsOpen U :=
    ((isOpen_interior.preimage
        (Work.Diff.STE.D.contDiff_flatToE (I := I) (D.x₀ l)).continuous).inter
      (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo))
  have hKU : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ l) ⊆ U := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    refine ⟨Work.Diff.STE.D.flatToE_mem_interior_target (I := I) (M := M) D l z hz, ?_⟩
    intro j _
    have h1 : |z j| ≤ D.σ l :=
      le_trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm z j) hz
    have h2 : D.σ l ≤ 1 / 8 := by have := D.hσ2 l; linarith
    exact abs_lt.mp (lt_of_le_of_lt h1 (by linarith))
  obtain ⟨φ, hφsm, hφone, hφtsup, -⟩ :=
    Work.Diff.STE.D.bump_smul_smooth (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ l))
      U (isCompact_closedBall _ _) hUopen hKU (fun _ : Fin (Module.finrank ℝ E) → ℝ => (1 : ℝ))
      contDiffOn_const
  refine ⟨φ, hφsm, fun z hz => hφone z (by rwa [Metric.mem_closedBall, dist_zero_right]), ?_, ?_,
    ?_⟩
  · exact hφtsup.trans Set.inter_subset_right
  · intro z hz
    exact (hφtsup hz).1
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (1 / 2)) ?_
    intro z hz
    have hz' := hφtsup (subset_tsupport φ hz)
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    intro j
    rw [Real.norm_eq_abs]
    obtain ⟨h1, h2⟩ := hz'.2 j (Set.mem_univ j)
    exact le_of_lt (abs_lt.mpr ⟨h1, h2⟩)

/-- The per-`(l,a,b)` Fourier norm of the chart-`f` matrix (`s`-th order).  It is an opaque `def`
so that the `Finset.single_le_sum` bookkeeping of the final estimate does not elaborate gigantic
terms (see the SESSION 24 note in `HANDOFF.md`). -/
private noncomputable def csqF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (η : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (s : ℕ) (l : ι₀)
    (f : Work.Diff.STE.Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) : ℝ :=
  Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
    (fun z => Work.Diff.STE.B3.perMat D (η l) l f a b z))

/-- The per-`(l,a,b)` Fourier norm of the chart-`u` matrix (`s`-th order). -/
private noncomputable def csqU {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (η : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (s : ℕ) (l : ι₀)
    (u : Work.Diff.STE.Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) : ℝ :=
  Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
    (fun z => Work.Diff.STE.B3.perMat D (η l) l u a b z))

/-- The `csqF` of a chart matrix is `≤` the total over all charts and components. -/
private lemma csqF_le_total {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (η : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (s : ℕ) (l : ι₀)
    (f : Work.Diff.STE.Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) :
    csqF (I := I) (M := M) D η s l f a b
      ≤ ∑ l' : ι₀, ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          csqF (I := I) (M := M) D η s l' f a' b' := by
  calc csqF (I := I) (M := M) D η s l f a b
      ≤ ∑ b' : Fin (Module.finrank ℝ E), csqF (I := I) (M := M) D η s l f a b' :=
        Finset.single_le_sum (f := fun b' : Fin (Module.finrank ℝ E) =>
            csqF (I := I) (M := M) D η s l f a b')
          (fun b' _ => Work.Diff.STE.CSq_nonneg _ _) (Finset.mem_univ b)
    _ ≤ ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          csqF (I := I) (M := M) D η s l f a' b' :=
        Finset.single_le_sum (f := fun a' : Fin (Module.finrank ℝ E) =>
            ∑ b' : Fin (Module.finrank ℝ E), csqF (I := I) (M := M) D η s l f a' b')
          (fun a' _ => Finset.sum_nonneg fun b' _ => Work.Diff.STE.CSq_nonneg _ _)
          (Finset.mem_univ a)
    _ ≤ ∑ l' : ι₀, ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          csqF (I := I) (M := M) D η s l' f a' b' :=
        Finset.single_le_sum (f := fun l' : ι₀ =>
            ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
              csqF (I := I) (M := M) D η s l' f a' b')
          (fun l' _ => Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ =>
            Work.Diff.STE.CSq_nonneg _ _) (Finset.mem_univ l)

/-- The `csqU` of a chart matrix is `≤` the total over all charts and components. -/
private lemma csqU_le_total {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (η : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (s : ℕ) (l : ι₀)
    (u : Work.Diff.STE.Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) :
    csqU (I := I) (M := M) D η s l u a b
      ≤ ∑ l' : ι₀, ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          csqU (I := I) (M := M) D η s l' u a' b' := by
  calc csqU (I := I) (M := M) D η s l u a b
      ≤ ∑ b' : Fin (Module.finrank ℝ E), csqU (I := I) (M := M) D η s l u a b' :=
        Finset.single_le_sum (f := fun b' : Fin (Module.finrank ℝ E) =>
            csqU (I := I) (M := M) D η s l u a b')
          (fun b' _ => Work.Diff.STE.CSq_nonneg _ _) (Finset.mem_univ b)
    _ ≤ ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          csqU (I := I) (M := M) D η s l u a' b' :=
        Finset.single_le_sum (f := fun a' : Fin (Module.finrank ℝ E) =>
            ∑ b' : Fin (Module.finrank ℝ E), csqU (I := I) (M := M) D η s l u a' b')
          (fun a' _ => Finset.sum_nonneg fun b' _ => Work.Diff.STE.CSq_nonneg _ _)
          (Finset.mem_univ a)
    _ ≤ ∑ l' : ι₀, ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          csqU (I := I) (M := M) D η s l' u a' b' :=
        Finset.single_le_sum (f := fun l' : ι₀ =>
            ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
              csqU (I := I) (M := M) D η s l' u a' b')
          (fun l' _ => Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ =>
            Work.Diff.STE.CSq_nonneg _ _) (Finset.mem_univ l)

/-- The commutator summand of the pair decomposition, at the index `(l,α,β,i,c,d)`. -/
private noncomputable def atrm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (ce : (l : ι₀) → Work.Diff.STE.B3.VarCoef.ChartCE (I := I) (M := M) D k l)
    (η : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (f u : Work.Diff.STE.Bil (I := I) (M := M)) (l : ι₀)
    (α β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) (i : ι₀)
    (c d : Fin (Module.finrank ℝ E)) : ℝ :=
  (Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
      (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
        (Work.Diff.STE.B3.VarCoef.ptOp (ce l) α β i c d
          (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2))))
    - (Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
        (Work.Diff.STE.B3.VarCoef.ptOp (ce l) α β i c d
          (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
            (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2))))

/-- The defect summand of the pair decomposition, at the index `(l,α,β,i,c,d)`. -/
private noncomputable def btrm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (ce : (l : ι₀) → Work.Diff.STE.B3.VarCoef.ChartCE (I := I) (M := M) D k l)
    (η : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (f u : Work.Diff.STE.Bil (I := I) (M := M)) (l : ι₀)
    (α β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) (i : ι₀)
    (c d : Fin (Module.finrank ℝ E)) : ℝ :=
  Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
    ((Work.Diff.STE.B3.VarCoef.ptOp (ce l) α β i c d
      - Work.Diff.STE.B3.VarCoef.ptStarOp (ce l) α β i c d)
        (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
          (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2)))

theorem ENormB_pair_J_commutator_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (k : ℕ) (hk : Module.finrank ℝ E < 2 * k) (hk1 : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ (f u : Work.Diff.STE.Bil (I := I) (M := M)),
          (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
            ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b)) →
          (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
            ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b)) →
          |D.ENormB_pair k (D.J ρ ε f) u - D.ENormB_pair k f (D.J ρ ε u)|
            ≤ C * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f) * Real.sqrt (D.ENormB k u) := by
  classical
  -- ## the per-chart cutoffs and the CE data
  have hcut : ∀ l : ι₀, ∃ η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ l → η z = 1) ∧
      tsupport η ⊆ Set.pi Set.univ
        (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, z ∈ tsupport η →
        Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
          interior ((extChartAt I (D.x₀ l)).target)) ∧
      HasCompactSupport η := fun l => exists_chart_cut D l
  choose η hηspec using hcut
  have hηsm : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (η l) := fun l => (hηspec l).1
  have hη1 : ∀ l z, ‖z‖ ≤ D.σ l → η l z = 1 := fun l => (hηspec l).2.1
  have hηcube : ∀ l, tsupport (η l) ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    fun l => (hηspec l).2.2.1
  have hηint : ∀ l z, z ∈ tsupport (η l) →
      Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
        interior ((extChartAt I (D.x₀ l)).target) := fun l => (hηspec l).2.2.2.1
  have hηc : ∀ l, HasCompactSupport (η l) := fun l => (hηspec l).2.2.2.2
  have hηtgt : ∀ l z, z ∈ tsupport (η l) →
      Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈ (extChartAt I (D.x₀ l)).target :=
    fun l z hz => interior_subset (hηint l z hz)
  have hint : ∀ l z, D.psi l z ≠ 0 →
      Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
        interior ((extChartAt I (D.x₀ l)).target) := by
    intro l z hz
    exact Work.Diff.STE.D.flatToE_mem_interior_target (I := I) (M := M) D l z
      (le_of_lt (Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (I := I) (M := M) D hz))
  let ce : (l : ι₀) → Work.Diff.STE.B3.VarCoef.ChartCE (I := I) (M := M) D k l :=
    fun l => Classical.choice (Work.Diff.STE.B3.VarCoef.ChartCE_exists (I := I) (M := M) D k l)
  -- ## the order certificate of the defect operator, chart pair by chart pair
  have hcertI : ∀ (l : ι₀) (α β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      (i : ι₀), ∃ C : ℤ → ℝ,
      Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) C
        ((∑ cd : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.B3.VarCoef.POp ((ce l).ci i cd.1 cd.2 β.1 β.2)
              ((ce l).co i α.1 α.2 cd.1 cd.2)
              (Work.Diff.STE.B3.VarCoef.varLapOp ((ce l).A i) ((ce l).B i)) k)
          - (∑ cd : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.B3.VarCoef.POpStar ((ce l).ci i cd.1 cd.2 α.1 α.2)
                ((ce l).co i β.1 β.2 cd.1 cd.2) ((ce l).A i)
                (fun a => -((ce l).B i a)) k)) := by
    intro l α β i
    refine Work.Diff.STE.B3.VarCoef.sum_POp_sub_POpStar_isOrd
      (ι := Fin (Module.finrank ℝ E)) (κ := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      k hk1 (A := (ce l).A i) (B := (ce l).B i)
      (fun a b => (ce l).hA i a b) (fun a b => (ce l).hAp i a b)
      (fun a => (ce l).hB i a) (fun a => (ce l).hBp i a)
      (fun cd => (ce l).ci i cd.1 cd.2 β.1 β.2)
      (fun cd => (ce l).co i α.1 α.2 cd.1 cd.2)
      (fun cd => (ce l).ci i cd.1 cd.2 α.1 α.2)
      (fun cd => (ce l).co i β.1 β.2 cd.1 cd.2)
      (fun cd => (ce l).hci i cd.1 cd.2 β.1 β.2)
      (fun cd => (ce l).hcip i cd.1 cd.2 β.1 β.2)
      (fun cd => (ce l).hco i α.1 α.2 cd.1 cd.2)
      (fun cd => (ce l).hcop i α.1 α.2 cd.1 cd.2)
      (fun cd => (ce l).hci i cd.1 cd.2 α.1 α.2)
      (fun cd => (ce l).hcip i cd.1 cd.2 α.1 α.2)
      (fun cd => (ce l).hco i β.1 β.2 cd.1 cd.2)
      (fun cd => (ce l).hcop i β.1 β.2 cd.1 cd.2)
      ?_
    intro z
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [(ce l).hsym i α.1 α.2 β.1 β.2 z]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  choose Ccert hCcert using fun l α β i => hcertI l α β i
  have hcert2 : ∀ (l : ι₀) (α β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) C
        (Work.Diff.STE.B3.VarCoef.pairP (ce l) α β
          - Work.Diff.STE.B3.VarCoef.pairPStar (ce l) α β) := by
    intro l α β
    have hsum := Work.Diff.STE.B3.VarCoef.IsOrd.sum (s := Finset.univ)
      (T := fun i : ι₀ =>
        ((∑ cd : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.B3.VarCoef.POp ((ce l).ci i cd.1 cd.2 β.1 β.2)
              ((ce l).co i α.1 α.2 cd.1 cd.2)
              (Work.Diff.STE.B3.VarCoef.varLapOp ((ce l).A i) ((ce l).B i)) k)
          - (∑ cd : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.B3.VarCoef.POpStar ((ce l).ci i cd.1 cd.2 α.1 α.2)
                ((ce l).co i β.1 β.2 cd.1 cd.2) ((ce l).A i)
                (fun a => -((ce l).B i a)) k)))
      (C := fun i => Ccert l α β i) (fun i _ => hCcert l α β i)
    refine ⟨_, Work.Diff.STE.B3.VarCoef.IsOrd.congr hsum (fun f hf => ?_)⟩
    funext x
    simp only [Finset.sum_apply, Pi.sub_apply, Work.Diff.STE.B3.VarCoef.pairP,
      Work.Diff.STE.B3.VarCoef.pairPStar, Finset.sum_sub_distrib, Fintype.sum_prod_type]
  -- ## the two flat constants
  obtain ⟨Ccomm, hCcomm0, hCcomm⟩ :=
    Work.Diff.STE.B3.VarCoef.sum_commOp_pairing_le (ι := Fin (Module.finrank ℝ E))
      (κ := CIdx ι₀ (Module.finrank ℝ E)) k hk1 ρ hρ hρ0 hρs hρ1
      (fun γ => Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D γ.1.1)
      (fun γ => (Work.Diff.STE.B3.VarCoef.perPhiR_smooth_periodic (I := I) (M := M) D γ.1.1
        (hint γ.1.1)).1)
      (fun γ => (Work.Diff.STE.B3.VarCoef.perPhiR_smooth_periodic (I := I) (M := M) D γ.1.1
        (hint γ.1.1)).2)
      (fun γ a b => (ce γ.1.1).A γ.2.1 a b)
      (fun γ a b => (ce γ.1.1).hA γ.2.1 a b)
      (fun γ a b => (ce γ.1.1).hAp γ.2.1 a b)
      (fun γ a => (ce γ.1.1).B γ.2.1 a)
      (fun γ a => (ce γ.1.1).hB γ.2.1 a)
      (fun γ a => (ce γ.1.1).hBp γ.2.1 a)
      (fun γ => (ce γ.1.1).ci γ.2.1 γ.2.2.1 γ.2.2.2 γ.1.2.2.1 γ.1.2.2.2)
      (fun γ => (ce γ.1.1).co γ.2.1 γ.1.2.1.1 γ.1.2.1.2 γ.2.2.1 γ.2.2.2)
      (fun γ => (ce γ.1.1).hci _ _ _ _ _)
      (fun γ => (ce γ.1.1).hcip _ _ _ _ _)
      (fun γ => (ce γ.1.1).hco _ _ _ _ _)
      (fun γ => (ce γ.1.1).hcop _ _ _ _ _)
  choose Ccert2 hCcert2 using hcert2
  have hTdef : ∀ γ : OIdx ι₀ (Module.finrank ℝ E),
      Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1)
        (fun t => ∑ δ : OIdx ι₀ (Module.finrank ℝ E), Ccert2 δ.1 δ.2.1 δ.2.2 t)
        (Work.Diff.STE.B3.VarCoef.pairP (ce γ.1) γ.2.1 γ.2.2
          - Work.Diff.STE.B3.VarCoef.pairPStar (ce γ.1) γ.2.1 γ.2.2) := by
    intro γ
    refine Work.Diff.STE.B3.VarCoef.IsOrd.mono_C (hCcert2 γ.1 γ.2.1 γ.2.2)
      (fun t => ?_)
    exact Finset.single_le_sum
      (fun δ _ => (hCcert2 δ.1 δ.2.1 δ.2.2).nonneg t) (Finset.mem_univ γ)
  obtain ⟨Cdef, hCdef0, hCdefbd⟩ :=
    Work.Diff.STE.B3.VarCoef.sum_defect_pairing_le (ι := Fin (Module.finrank ℝ E))
      (κ := OIdx ι₀ (Module.finrank ℝ E)) k hk1 ρ hρ
      (fun γ => Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D γ.1)
      (fun γ => (Work.Diff.STE.B3.VarCoef.perPhiR_smooth_periodic (I := I) (M := M) D γ.1
        (hint γ.1)).1)
      (fun γ => (Work.Diff.STE.B3.VarCoef.perPhiR_smooth_periodic (I := I) (M := M) D γ.1
        (hint γ.1)).2)
      (fun γ => Work.Diff.STE.B3.VarCoef.pairP (ce γ.1) γ.2.1 γ.2.2
        - Work.Diff.STE.B3.VarCoef.pairPStar (ce γ.1) γ.2.1 γ.2.2)
      (fun t => ∑ δ : OIdx ι₀ (Module.finrank ℝ E), Ccert2 δ.1 δ.2.1 δ.2.2 t) hTdef
  obtain ⟨Cm1, hCm10, hCm1⟩ :=
    Work.Diff.STE.B3.VarCoef.sum_mat_csq_le_ENormB_sigma (I := I) (M := M) D (k - 1) η
      hη1 hηsm hηc hηtgt
  obtain ⟨Cm2, hCm20, hCm2⟩ :=
    Work.Diff.STE.B3.VarCoef.sum_mat_csq_le_ENormB_sigma (I := I) (M := M) D k η
      hη1 hηsm hηc hηtgt
  have hCzex : ∃ Cz : ℝ, 0 ≤ Cz ∧ (Module.finrank ℝ E = 0 ∨
      ∀ (R P : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) R →
        Function.support R ⊆ Set.pi Set.univ
          (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
        ContDiff ℝ (⊤ : ℕ∞) P → Work.Diff.STE.Periodic1 P →
        (∀ z : Fin (Module.finrank ℝ E) → ℝ, P z =
          ∑' m' : Fin (Module.finrank ℝ E) → ℤ, R (z + Work.Diff.STE.iVec m')) →
        Work.Diff.STE.ENormSq 0 P ≤ Cz * Work.Diff.STE.ENormSq k P) := by
    by_cases hn : Module.finrank ℝ E = 0
    · exact ⟨0, le_refl 0, Or.inl hn⟩
    · haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      obtain ⟨Cz, h1, h2⟩ :=
        Work.Diff.STE.B3.ENormSq_zero_le_ENormSq (ι := Fin (Module.finrank ℝ E)) k hk1
      exact ⟨Cz, h1, Or.inr h2⟩
  obtain ⟨Cz, hCz0, hCzcase⟩ := hCzex
  -- ## the multiplicities of the index sets
  set Kc : ℝ := (Fintype.card (CIdx ι₀ (Module.finrank ℝ E)) : ℝ) with hKc
  set Kd : ℝ := (Fintype.card (OIdx ι₀ (Module.finrank ℝ E)) : ℝ) with hKd
  set K : ℝ := max Kc Kd with hK
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hKd0 : 0 ≤ Kd := by rw [hKd]; positivity
  have hK0 : 0 ≤ K := by rw [hK]; exact le_trans hKc0 (le_max_left _ _)
  have hKcK : Kc ≤ K := by rw [hK]; exact le_max_left _ _
  have hKdK : Kd ≤ K := by rw [hK]; exact le_max_right _ _
  have hCm10' : 0 ≤ Cm1 := hCm10
  have hCm20' : 0 ≤ Cm2 := hCm20
  refine ⟨(Ccomm + Cdef) * Real.sqrt (K * Cm1) * Real.sqrt (K * Cm2 * (2 + Cz)),
    mul_nonneg (mul_nonneg (add_nonneg hCcomm0 hCdef0) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _), ?_⟩
  intro ε hε hε1 f u hf hu
  by_cases hn : Module.finrank ℝ E = 0
  · have h1 : D.ENormB_pair k (D.J ρ ε f) u = 0 := by
      show (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ∑ l : Fin k → Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (D.Rper i (D.J ρ ε f) a b))
            (Work.Diff.STE.pdVec k l (D.Rper i u a b))) = 0
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a _ => ?_
      exact Finset.sum_eq_zero fun b _ => absurd b.2 (by have h := b.2; omega)
    have h2 : D.ENormB_pair k f (D.J ρ ε u) = 0 := by
      show (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ∑ l : Fin k → Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (D.Rper i f a b))
            (Work.Diff.STE.pdVec k l (D.Rper i (D.J ρ ε u) a b))) = 0
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a _ => ?_
      exact Finset.sum_eq_zero fun b _ => absurd b.2 (by have h := b.2; omega)
    rw [h1, h2, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (add_nonneg hCcomm0 hCdef0) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    have hCz := hCzcase.resolve_left hn
    -- ## the smoothness of the chart weight and of the chart matrices
    have hφS : ∀ l : ι₀, Work.Diff.STE.B3.VarCoef.SmoothPer
        (fun z => ((Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l z : ℝ) : ℂ)) := by
      intro l
      obtain ⟨h1, h2⟩ := Work.Diff.STE.B3.VarCoef.perPhiR_smooth_periodic (I := I) (M := M) D l
        (hint l)
      exact ⟨Complex.ofRealCLM.contDiff.comp h1, fun i x => by simp [h2 i x]⟩
    have hFS : ∀ (l : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.B3.VarCoef.SmoothPer
          (Work.Diff.STE.B3.perMat (I := I) (M := M) D (η l) l f a b) := by
      intro l a b
      exact ⟨Work.Diff.STE.B3.VarCoef.perMat_contDiff (I := I) (M := M) D (η l) (hηsm l)
          (hηcube l) l (hηint l) f hf a b,
        Work.Diff.STE.B3.VarCoef.perMat_periodic (I := I) (M := M) D (η l) l f a b⟩
    have hUS : ∀ (l : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.B3.VarCoef.SmoothPer
          (Work.Diff.STE.B3.perMat (I := I) (M := M) D (η l) l u a b) := by
      intro l a b
      exact ⟨Work.Diff.STE.B3.VarCoef.perMat_contDiff (I := I) (M := M) D (η l) (hηsm l)
          (hηcube l) l (hηint l) u hu a b,
        Work.Diff.STE.B3.VarCoef.perMat_periodic (I := I) (M := M) D (η l) l u a b⟩
    -- ## the zero-order comparison
    have hzero : D.ENormB 0 u ≤ (1 + Cz) * D.ENormB k u := by
      have hcomp : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          Work.Diff.STE.ENormSq 0 (D.Rper i u a b)
            ≤ (1 + Cz) * Work.Diff.STE.ENormSq k (D.Rper i u a b) := by
        intro i a b
        obtain ⟨hc1, hc2⟩ :=
          Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i u a b
            (hu i a b)
        have hRR : ContDiff ℝ (⊤ : ℕ∞)
            (fun z => ((D.R i u a b z : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp (hu i a b)
        have hsuppR : Function.support (fun z => ((D.R i u a b z : ℝ) : ℂ)) ⊆
            Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
          intro z hz
          refine Work.Diff.STE.B3.support_ofReal_subset
            (Work.Diff.STE.B3.support_R_subset D i u a b) ?_
          rw [Function.mem_support] at hz ⊢
          intro h0
          exact hz (by simp [h0])
        have h0 := hCz (fun z => ((D.R i u a b z : ℝ) : ℂ)) (D.Rper i u a b) hRR hsuppR hc1 hc2
          (fun z => rfl)
        have hnn : 0 ≤ Work.Diff.STE.ENormSq k (D.Rper i u a b) :=
          Work.Diff.STE.flat.ENormSq_nonneg k _
        nlinarith [h0, hnn, hCz0]
      show (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq 0 (D.Rper i u a b))
        ≤ (1 + Cz) * (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq k (D.Rper i u a b))
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun b _ => hcomp i a b
    -- ## Step 1: the chart split
    have hstep1 : D.ENormB_pair k (D.J ρ ε f) u - D.ENormB_pair k f (D.J ρ ε u)
        = ∑ l : ι₀,
            (Work.Diff.STE.B3Data.CPair l
                (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R l f a b) z)
                (D.R l (Work.Diff.STE.B3.Qk D k u))
              - Work.Diff.STE.B3Data.CPair l
                (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε
                  (D.R l (Work.Diff.STE.B3.Qk D k f) a b) z) (D.R l u)) := by
      rw [ENormB_pair_commutator_chart_split_pairing (I := I) (M := M) D ρ hρ hρ0 k ε hε f u
        hf hu, Finset.sum_sub_distrib]
    -- ## Step 2: the per-chart periodisation
    have hstep2 : (∑ l : ι₀,
            (Work.Diff.STE.B3Data.CPair l
                (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R l f a b) z)
                (D.R l (Work.Diff.STE.B3.Qk D k u))
              - Work.Diff.STE.B3Data.CPair l
                (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε
                  (D.R l (Work.Diff.STE.B3.Qk D k f) a b) z) (D.R l u)))
        = ∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ((Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
                (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                  (Work.Diff.STE.B3.VarCoef.pairP (ce l) α β
                    (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2))))
              - (Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP (ce l) β α
                    (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2))
                  (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                    (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2)))) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      exact Work.Diff.STE.B3.VarCoef.chartTerm_eq_XP_sigma (I := I) (M := M) D ρ hρ k ε hε f u
        hf hu (Work.Diff.STE.B3.SymCalcStep2.R_Qk_contDiff D k f hf)
        (Work.Diff.STE.B3.SymCalcStep2.R_Qk_contDiff D k u hu) l (η l) (hη1 l) (hηcube l)
        (hφS l) (fun a b => hFS l a b) (fun a b => hUS l a b) (ce l)
    -- ## Step 3: the per-(l,α,β) decomposition
    have hstep3 : ∀ (l : ι₀) (α β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
        ((Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
              (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                (Work.Diff.STE.B3.VarCoef.pairP (ce l) α β
                  (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2))))
          - (Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP (ce l) β α
                (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2))
              (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2))))
        = (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              atrm D k ce η ρ ε f u l α β i c d)
          + Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
              ((Work.Diff.STE.B3.VarCoef.pairP (ce l) α β
                - Work.Diff.STE.B3.VarCoef.pairPStar (ce l) α β)
                  (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                    (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2))) := by
      intro l α β
      simpa only [atrm] using
        Work.Diff.STE.B3.VarCoef.pairTerm_decomp2 (I := I) (M := M) D ρ hρ k ε hε l (η l)
          (ce l) f u (hφS l) (fun a b => hFS l a b) (fun a b => hUS l a b) α β
    -- ## Step 4: distribute the sums
    have hstep4 : (∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ((Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
                (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                  (Work.Diff.STE.B3.VarCoef.pairP (ce l) α β
                    (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2))))
              - (Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP (ce l) β α
                    (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2))
                  (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                    (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2)))))
        = (∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              atrm D k ce η ρ ε f u l α β i c d)
          + (∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
                ((Work.Diff.STE.B3.VarCoef.pairP (ce l) α β
                  - Work.Diff.STE.B3.VarCoef.pairPStar (ce l) α β)
                    (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                      (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2)))) := by
      rw [Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun α _ =>
        Finset.sum_congr rfl (fun β _ => hstep3 l α β)))]
      simp only [Finset.sum_add_distrib]
    -- ## the commutator bound
    have hAid : (∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              atrm D k ce η ρ ε f u l α β i c d)
        = ∑ γ : CIdx ι₀ (Module.finrank ℝ E),
            atrm D k ce η ρ ε f u γ.1.1 γ.1.2.1 γ.1.2.2 γ.2.1 γ.2.2.1 γ.2.2.2 := by
      simp only [Fintype.sum_prod_type]
    have hAc : |∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              atrm D k ce η ρ ε f u l α β i c d|
        ≤ Ccomm * Real.sqrt (∑ γ : CIdx ι₀ (Module.finrank ℝ E), Work.Diff.STE.CSq (k - 1)
              (Work.Diff.STE.fourierCoeff
                (fun z => Work.Diff.STE.B3.perMat D (η γ.1.1) γ.1.1 f γ.1.2.1.1 γ.1.2.1.2 z)))
          * Real.sqrt (∑ γ : CIdx ι₀ (Module.finrank ℝ E), Work.Diff.STE.CSq k
              (Work.Diff.STE.fourierCoeff
                (fun z => Work.Diff.STE.B3.perMat D (η γ.1.1) γ.1.1 u γ.1.2.2.1 γ.1.2.2.2 z))) := by
      rw [hAid]
      have hgoal : (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
            atrm D k ce η ρ ε f u γ.1.1 γ.1.2.1 γ.1.2.2 γ.2.1 γ.2.2.1 γ.2.2.2)
          = (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
              Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η γ.1.1) γ.1.1 f γ.1.2.1.1 γ.1.2.1.2)
                (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε γ.1.1
                  (Work.Diff.STE.B3.VarCoef.ptOp (ce γ.1.1) γ.1.2.1 γ.1.2.2 γ.2.1 γ.2.2.1 γ.2.2.2
                    (Work.Diff.STE.B3.perMat D (η γ.1.1) γ.1.1 u γ.1.2.2.1 γ.1.2.2.2))))
            - (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
              Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η γ.1.1) γ.1.1 f γ.1.2.1.1 γ.1.2.1.2)
                (Work.Diff.STE.B3.VarCoef.ptOp (ce γ.1.1) γ.1.2.1 γ.1.2.2 γ.2.1 γ.2.2.1 γ.2.2.2
                  (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε γ.1.1
                    (Work.Diff.STE.B3.perMat D (η γ.1.1) γ.1.1 u γ.1.2.2.1 γ.1.2.2.2)))) := by
        simp only [atrm]
        rw [Finset.sum_sub_distrib]
      rw [hgoal]
      exact hCcomm ε hε hε1
          (fun γ : CIdx ι₀ (Module.finrank ℝ E) =>
            Work.Diff.STE.B3.perMat D (η γ.1.1) γ.1.1 f γ.1.2.1.1 γ.1.2.1.2)
          (fun γ : CIdx ι₀ (Module.finrank ℝ E) =>
            Work.Diff.STE.B3.perMat D (η γ.1.1) γ.1.1 u γ.1.2.2.1 γ.1.2.2.2)
          (fun γ => hFS γ.1.1 γ.1.2.1.1 γ.1.2.1.2)
          (fun γ => hUS γ.1.1 γ.1.2.2.1 γ.1.2.2.2)
    -- ## the defect bound
    have hBsum : (∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
                ((Work.Diff.STE.B3.VarCoef.pairP (ce l) α β
                  - Work.Diff.STE.B3.VarCoef.pairPStar (ce l) α β)
                    (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                      (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2))))
        = ∑ γ : OIdx ι₀ (Module.finrank ℝ E),
            Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η γ.1) γ.1 f γ.2.1.1 γ.2.1.2)
              ((Work.Diff.STE.B3.VarCoef.pairP (ce γ.1) γ.2.1 γ.2.2
                - Work.Diff.STE.B3.VarCoef.pairPStar (ce γ.1) γ.2.1 γ.2.2)
                  (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε γ.1
                    (Work.Diff.STE.B3.perMat D (η γ.1) γ.1 u γ.2.2.1 γ.2.2.2))) := by
      simp only [Fintype.sum_prod_type]
    have hBd : |∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
                ((Work.Diff.STE.B3.VarCoef.pairP (ce l) α β
                  - Work.Diff.STE.B3.VarCoef.pairPStar (ce l) α β)
                    (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                      (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2)))|
        ≤ Cdef * Real.sqrt (∑ γ : OIdx ι₀ (Module.finrank ℝ E), Work.Diff.STE.CSq (k - 1)
              (Work.Diff.STE.fourierCoeff
                (fun z => Work.Diff.STE.B3.perMat D (η γ.1) γ.1 f γ.2.1.1 γ.2.1.2 z)))
          * Real.sqrt (∑ γ : OIdx ι₀ (Module.finrank ℝ E), Work.Diff.STE.CSq k
              (Work.Diff.STE.fourierCoeff
                (fun z => Work.Diff.STE.B3.perMat D (η γ.1) γ.1 u γ.2.2.1 γ.2.2.2 z))) := by
      rw [hBsum]
      exact hCdefbd ε hε hε1
          (fun γ : OIdx ι₀ (Module.finrank ℝ E) =>
            Work.Diff.STE.B3.perMat D (η γ.1) γ.1 f γ.2.1.1 γ.2.1.2)
          (fun γ : OIdx ι₀ (Module.finrank ℝ E) =>
            Work.Diff.STE.B3.perMat D (η γ.1) γ.1 u γ.2.2.1 γ.2.2.2)
          (fun γ => hFS γ.1 γ.2.1.1 γ.2.1.2)
          (fun γ => hUS γ.1 γ.2.2.1 γ.2.2.2)
    -- ## the four norm bounds of the index sets (SESSION 25)
    have htotF : (0 : ℝ) ≤ ∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b :=
      Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => Work.Diff.STE.CSq_nonneg _ _
    have htotU : (0 : ℝ) ≤ ∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b :=
      Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => Work.Diff.STE.CSq_nonneg _ _
    have hS1 : (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
          csqF D η (k - 1) γ.1.1 f γ.1.2.1.1 γ.1.2.1.2)
        ≤ K * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b) := by
      calc (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
            csqF D η (k - 1) γ.1.1 f γ.1.2.1.1 γ.1.2.1.2)
          ≤ ∑ _γ : CIdx ι₀ (Module.finrank ℝ E),
              (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b) :=
            Finset.sum_le_sum fun γ _ =>
              csqF_le_total (I := I) (M := M) D η (k - 1) γ.1.1 f γ.1.2.1.1 γ.1.2.1.2
        _ = (Fintype.card (CIdx ι₀ (Module.finrank ℝ E)) : ℝ)
              * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = Kc * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b) := by rw [hKc]
        _ ≤ K * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b) :=
            mul_le_mul_of_nonneg_right hKcK htotF
    have hS2 : (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
          csqU D η k γ.1.1 u γ.1.2.2.1 γ.1.2.2.2)
        ≤ K * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b) := by
      calc (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
            csqU D η k γ.1.1 u γ.1.2.2.1 γ.1.2.2.2)
          ≤ ∑ _γ : CIdx ι₀ (Module.finrank ℝ E),
              (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b) :=
            Finset.sum_le_sum fun γ _ =>
              csqU_le_total (I := I) (M := M) D η k γ.1.1 u γ.1.2.2.1 γ.1.2.2.2
        _ = (Fintype.card (CIdx ι₀ (Module.finrank ℝ E)) : ℝ)
              * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = Kc * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b) := by rw [hKc]
        _ ≤ K * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b) :=
            mul_le_mul_of_nonneg_right hKcK htotU
    have hS1' : (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
          csqF D η (k - 1) γ.1 f γ.2.1.1 γ.2.1.2)
        ≤ K * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b) := by
      calc (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
            csqF D η (k - 1) γ.1 f γ.2.1.1 γ.2.1.2)
          ≤ ∑ _γ : OIdx ι₀ (Module.finrank ℝ E),
              (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b) :=
            Finset.sum_le_sum fun γ _ =>
              csqF_le_total (I := I) (M := M) D η (k - 1) γ.1 f γ.2.1.1 γ.2.1.2
        _ = (Fintype.card (OIdx ι₀ (Module.finrank ℝ E)) : ℝ)
              * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = Kd * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b) := by rw [hKd]
        _ ≤ K * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b) :=
            mul_le_mul_of_nonneg_right hKdK htotF
    have hS2' : (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
          csqU D η k γ.1 u γ.2.2.1 γ.2.2.2)
        ≤ K * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b) := by
      calc (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
            csqU D η k γ.1 u γ.2.2.1 γ.2.2.2)
          ≤ ∑ _γ : OIdx ι₀ (Module.finrank ℝ E),
              (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b) :=
            Finset.sum_le_sum fun γ _ =>
              csqU_le_total (I := I) (M := M) D η k γ.1 u γ.2.2.1 γ.2.2.2
        _ = (Fintype.card (OIdx ι₀ (Module.finrank ℝ E)) : ℝ)
              * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = Kd * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b) := by rw [hKd]
        _ ≤ K * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b) :=
            mul_le_mul_of_nonneg_right hKdK htotU
    -- ## the four `sqrt` bounds
    have hb1 : Real.sqrt (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
          csqF D η (k - 1) γ.1.1 f γ.1.2.1.1 γ.1.2.1.2)
        ≤ Real.sqrt (K * Cm1 * (D.ENormB (k - 1) f + D.ENormB 0 f)) := by
      refine Real.sqrt_le_sqrt ?_
      have hCm1f : (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b)
          ≤ Cm1 * (D.ENormB (k - 1) f + D.ENormB 0 f) := hCm1 f hf
      calc (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
            csqF D η (k - 1) γ.1.1 f γ.1.2.1.1 γ.1.2.1.2)
          ≤ K * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b) := hS1
        _ ≤ K * (Cm1 * (D.ENormB (k - 1) f + D.ENormB 0 f)) :=
            mul_le_mul_of_nonneg_left hCm1f hK0
        _ = K * Cm1 * (D.ENormB (k - 1) f + D.ENormB 0 f) := by ring
    have hb2 : Real.sqrt (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
          csqU D η k γ.1.1 u γ.1.2.2.1 γ.1.2.2.2)
        ≤ Real.sqrt (K * Cm2 * (2 + Cz) * D.ENormB k u) := by
      refine Real.sqrt_le_sqrt ?_
      have hCm2u : (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b)
          ≤ Cm2 * (D.ENormB k u + D.ENormB 0 u) := hCm2 u hu
      have hYu : D.ENormB k u + D.ENormB 0 u ≤ (2 + Cz) * D.ENormB k u := by
        linarith [hzero]
      calc (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
            csqU D η k γ.1.1 u γ.1.2.2.1 γ.1.2.2.2)
          ≤ K * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b) := hS2
        _ ≤ K * (Cm2 * (D.ENormB k u + D.ENormB 0 u)) :=
            mul_le_mul_of_nonneg_left hCm2u hK0
        _ = K * Cm2 * (D.ENormB k u + D.ENormB 0 u) := by ring
        _ ≤ K * Cm2 * ((2 + Cz) * D.ENormB k u) :=
            mul_le_mul_of_nonneg_left hYu (mul_nonneg hK0 hCm20)
        _ = K * Cm2 * (2 + Cz) * D.ENormB k u := by ring
    have hb1' : Real.sqrt (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
          csqF D η (k - 1) γ.1 f γ.2.1.1 γ.2.1.2)
        ≤ Real.sqrt (K * Cm1 * (D.ENormB (k - 1) f + D.ENormB 0 f)) := by
      refine Real.sqrt_le_sqrt ?_
      have hCm1f : (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b)
          ≤ Cm1 * (D.ENormB (k - 1) f + D.ENormB 0 f) := hCm1 f hf
      calc (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
            csqF D η (k - 1) γ.1 f γ.2.1.1 γ.2.1.2)
          ≤ K * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E), csqF D η (k - 1) l f a b) := hS1'
        _ ≤ K * (Cm1 * (D.ENormB (k - 1) f + D.ENormB 0 f)) :=
            mul_le_mul_of_nonneg_left hCm1f hK0
        _ = K * Cm1 * (D.ENormB (k - 1) f + D.ENormB 0 f) := by ring
    have hb2' : Real.sqrt (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
          csqU D η k γ.1 u γ.2.2.1 γ.2.2.2)
        ≤ Real.sqrt (K * Cm2 * (2 + Cz) * D.ENormB k u) := by
      refine Real.sqrt_le_sqrt ?_
      have hCm2u : (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b)
          ≤ Cm2 * (D.ENormB k u + D.ENormB 0 u) := hCm2 u hu
      have hYu : D.ENormB k u + D.ENormB 0 u ≤ (2 + Cz) * D.ENormB k u := by
        linarith [hzero]
      calc (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
            csqU D η k γ.1 u γ.2.2.1 γ.2.2.2)
          ≤ K * (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E), csqU D η k l u a b) := hS2'
        _ ≤ K * (Cm2 * (D.ENormB k u + D.ENormB 0 u)) :=
            mul_le_mul_of_nonneg_left hCm2u hK0
        _ = K * Cm2 * (D.ENormB k u + D.ENormB 0 u) := by ring
        _ ≤ K * Cm2 * ((2 + Cz) * D.ENormB k u) :=
            mul_le_mul_of_nonneg_left hYu (mul_nonneg hK0 hCm20)
        _ = K * Cm2 * (2 + Cz) * D.ENormB k u := by ring
    -- ## the two half-bounds, rewritten in the `csqF`/`csqU` vocabulary
    have hAcF : |∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              atrm D k ce η ρ ε f u l α β i c d|
        ≤ Ccomm * Real.sqrt (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
              csqF D η (k - 1) γ.1.1 f γ.1.2.1.1 γ.1.2.1.2)
          * Real.sqrt (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
              csqU D η k γ.1.1 u γ.1.2.2.1 γ.1.2.2.2) := by
      simpa only [csqF, csqU] using hAc
    have hBdF : |∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
                ((Work.Diff.STE.B3.VarCoef.pairP (ce l) α β
                  - Work.Diff.STE.B3.VarCoef.pairPStar (ce l) α β)
                    (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                      (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2)))|
        ≤ Cdef * Real.sqrt (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
              csqF D η (k - 1) γ.1 f γ.2.1.1 γ.2.1.2)
          * Real.sqrt (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
              csqU D η k γ.1 u γ.2.2.1 γ.2.2.2) := by
      simpa only [csqF, csqU] using hBd
    have hstepAB : ∀ c₀ : ℝ, 0 ≤ c₀ →
        c₀ * Real.sqrt (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
            csqF D η (k - 1) γ.1.1 f γ.1.2.1.1 γ.1.2.1.2)
          * Real.sqrt (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
            csqU D η k γ.1.1 u γ.1.2.2.1 γ.1.2.2.2)
        ≤ c₀ * Real.sqrt (K * Cm1 * (D.ENormB (k - 1) f + D.ENormB 0 f))
          * Real.sqrt (K * Cm2 * (2 + Cz) * D.ENormB k u) := by
      intro c₀ hc₀
      exact mul_le_mul (mul_le_mul_of_nonneg_left hb1 hc₀) hb2 (Real.sqrt_nonneg _)
        (mul_nonneg hc₀ (Real.sqrt_nonneg _))
    have hstepAB' : ∀ c₀ : ℝ, 0 ≤ c₀ →
        c₀ * Real.sqrt (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
            csqF D η (k - 1) γ.1 f γ.2.1.1 γ.2.1.2)
          * Real.sqrt (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
            csqU D η k γ.1 u γ.2.2.1 γ.2.2.2)
        ≤ c₀ * Real.sqrt (K * Cm1 * (D.ENormB (k - 1) f + D.ENormB 0 f))
          * Real.sqrt (K * Cm2 * (2 + Cz) * D.ENormB k u) := by
      intro c₀ hc₀
      exact mul_le_mul (mul_le_mul_of_nonneg_left hb1' hc₀) hb2' (Real.sqrt_nonneg _)
        (mul_nonneg hc₀ (Real.sqrt_nonneg _))
    have hKcm1 : (0 : ℝ) ≤ K * Cm1 := mul_nonneg hK0 hCm10
    have hKcm2c : (0 : ℝ) ≤ K * Cm2 * (2 + Cz) :=
      mul_nonneg (mul_nonneg hK0 hCm20) (by linarith [hCz0])
    -- ## the split of the commutator and the final arithmetic
    have hsplit : D.ENormB_pair k (D.J ρ ε f) u - D.ENormB_pair k f (D.J ρ ε u)
        = (∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              atrm D k ce η ρ ε f u l α β i c d)
          + (∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
                ((Work.Diff.STE.B3.VarCoef.pairP (ce l) α β
                  - Work.Diff.STE.B3.VarCoef.pairPStar (ce l) α β)
                    (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                      (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2)))) := by
      rw [hstep1, hstep2, hstep4]
    calc |D.ENormB_pair k (D.J ρ ε f) u - D.ENormB_pair k f (D.J ρ ε u)|
        = |(∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                atrm D k ce η ρ ε f u l α β i c d)
            + (∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
                  ((Work.Diff.STE.B3.VarCoef.pairP (ce l) α β
                    - Work.Diff.STE.B3.VarCoef.pairPStar (ce l) α β)
                      (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                        (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2))))| := by
          rw [hsplit]
      _ ≤ |∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                atrm D k ce η ρ ε f u l α β i c d|
            + |∑ l : ι₀, ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat D (η l) l f α.1 α.2)
                  ((Work.Diff.STE.B3.VarCoef.pairP (ce l) α β
                    - Work.Diff.STE.B3.VarCoef.pairPStar (ce l) α β)
                      (Work.Diff.STE.B3.VarCoef.xOpD D ρ ε l
                        (Work.Diff.STE.B3.perMat D (η l) l u β.1 β.2)))| := abs_add_le _ _
      _ ≤ Ccomm * Real.sqrt (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
              csqF D η (k - 1) γ.1.1 f γ.1.2.1.1 γ.1.2.1.2)
            * Real.sqrt (∑ γ : CIdx ι₀ (Module.finrank ℝ E),
              csqU D η k γ.1.1 u γ.1.2.2.1 γ.1.2.2.2)
          + Cdef * Real.sqrt (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
              csqF D η (k - 1) γ.1 f γ.2.1.1 γ.2.1.2)
            * Real.sqrt (∑ γ : OIdx ι₀ (Module.finrank ℝ E),
              csqU D η k γ.1 u γ.2.2.1 γ.2.2.2) :=
          add_le_add hAcF hBdF
      _ ≤ Ccomm * Real.sqrt (K * Cm1 * (D.ENormB (k - 1) f + D.ENormB 0 f))
            * Real.sqrt (K * Cm2 * (2 + Cz) * D.ENormB k u)
          + Cdef * Real.sqrt (K * Cm1 * (D.ENormB (k - 1) f + D.ENormB 0 f))
            * Real.sqrt (K * Cm2 * (2 + Cz) * D.ENormB k u) :=
          add_le_add (hstepAB Ccomm hCcomm0) (hstepAB' Cdef hCdef0)
      _ = ((Ccomm + Cdef) * Real.sqrt (K * Cm1) * Real.sqrt (K * Cm2 * (2 + Cz)))
            * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
            * Real.sqrt (D.ENormB k u) := by
          rw [Real.sqrt_mul hKcm1, Real.sqrt_mul hKcm2c]; ring
