import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowQ2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Defs` — node **C3QAll**: FS `thm:Control3Q` at the
**windowed `All` gate** `Q3KernelFSAll`

**Port note (design item D2).**  This whole directory is a mechanical port of
`Submission/Work/BoseB7AK/C3Q` (node C3Q, where `control3QFS` is proved) to the
`All` vocabulary of `Submission/Work/BoseBoxFock/AllDefs.lean`, performed by
`_port.py` in this directory:

* `namespace Work.BoseB7AK.C3Q` ↦ `Work.BoseC3QAll` (module paths likewise);
* `Q3KernelFS` ↦ `Q3KernelFSAll` (the gate below: field-for-field the frozen
  `Work.BoseBoxFock.Q3KernelFSAll` **plus** the `kmom_neg` row that the §10
  chain needs — see F16 below; that row is in any case a field of `FockData`,
  so it costs nothing);
* `F.Q2ex` ↦ `F.Q2exAll` (`Work.BoseRowQ2.Defs`: the corrected row 3, all
  χ-labels), which is what the design asks for;
* the `q2exLowerR` row gained the **window** hypothesis `T.NWindow E.bigM Ψ`
  (its only consumer, `Est1/Assembly.lean:237`, applies it at a window state,
  where the window is a hypothesis already);
* `private` was dropped from the two split files, and files above 30 KB were
  split at declaration boundaries into `X`/`Xb`/`Xc`/`Xd` (the base name is the
  first part; imports of a base name were rewritten to the last part).

The headline of the port is `Work.BoseC3QAll.control3QFS` (`Final.lean`);
`AllStatement.lean` converts it into the frozen statement
`Work.BoseBoxFock.Control3QFSAll`.

# node **C3Q** (original text)
**corrected gate** `Q3KernelFSAll`

Re-scoped by the project lead (`BOSE_BOXFOCK_LEAD.md` §0.4,
`BOSE_BOXFOCK_STATEMENTS.lean.txt` §5–§7) after finding **F1**
(machine-checked): the old gate `Work.BoseK15.Q3Kernel'` (and its §10 port) has
`kmom_sub`/`hasKernel` with an *unguarded* high index, which is unsatisfiable on
any finite mode system that has one low mode and `P_H ≠ ∅`
(`KmomSubFalse.kmom_sub_unsat`).  So the box theorem under the old gate is
vacuous, and work on the old row list is stopped.

The corrected gate `Q3KernelFSAll` is `Q3Kernel'` with four rows repaired:

* `kmom_subW`/`hasKernelW` are guarded by `Ŵ₁ k ≠ 0` as well (every `Q₃` term
  carries the factor `Ŵ₁ k`, so the offending pairs are exactly those where the
  summand vanishes);
* `kmom_subL`, the *inner* additivity (both indices localised);
* `fL_supp2`: FS's own support `‖kmom s‖ ≤ 2·K_L√(μa)` (F7);
* `q2exLowerR`: `q2exLower` with the positive reserve `½·dNumOpR` on
  `RHi ∖ P_H^q`.

## One added row: `kmom_neg` (finding **F16**)

The verbatim gate of the statements file misses one row that the §10 chain
*needs*: `kmom (-i) = -kmom i`.  It is not derivable from the other rows.  The
first estimate evaluates the squeezed commutator `[b_{s−k},b_{−k}†]`, i.e. the
box kernel at the pairs `(s−k,−k)` and `(k,k−s)`, and the interface can supply
those only through `hasKernel_noWrap`, whose hypothesis at `(s−k,−k)` is

  `kmom ((s−k)−(−k)) = kmom (s−k) − kmom (−k)`,  i.e.  `kmom k + kmom (−k) = 0`.

`kmom_subW s k` gives `kmom (s−k) = kmom s − kmom k`, so the leftover is exactly
`kmom (−k) = −kmom k`; no combination of `kmom_subW`, `kmom_subL`, `fL_even` and
`W1_even` produces it (the only row with `−k` in the *high* slot would need
`−k ∈ P_H`, which is not known -- `P_H` is defined through `‖kmom (−k)‖` itself,
so the argument is circular).  At the honest box the row is **true**
(`valMinAbs` is odd, so the lattice momentum is odd) and it is already a field of
the honest bundle `Work.BoseK15.K15Input`; it is exactly what the bundle's own
derivation of the four `NoWrap` families uses (`Work.BoseK15.noWrap_used_pairs`,
its `hneg` line).  Adding it therefore does not lose the honest instance and does
not weaken any §10 estimate; it makes the gate sufficient.  Recorded in the
final report as F16.

## Contents

* `RHi` — the reserve region `‖k‖ ≥ ½K_L√(μa)`.
* `Q3KernelFSAll` — the corrected gate.
* `controlWordHi` — `eq:Q3Cancels`'s word with the diagonal on `RHi`.
* `controlErrA`, `Mt`, `eta`, `E0`, `e1A`, `e23A`, `e4A` — the error brackets.
* `Control3QFS` — the re-delivery request.
* `noWrap_used_pairs`, `kerA … kerE`, `kernel_pairs` — the guarded kernel API.
* `IntKernel` — the kernel interface of `lem:EstimateIntegral`.
-/

noncomputable section

open scoped BigOperators


namespace Work.BoseC3QAll

open Work.BoseB7

set_option linter.unusedVariables false

universe u v

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The θ-modes and the error brackets -/

/-- **FS's second mode family and number operators** — the *same* structure as
`Work.BoseB7A.TildeData` (imported): the θ-modes `ã_s`, the cross commutator
`ccrX`, FS's `n₊` (`N`), `n₊^H` (`NH`) and the number grading.  It is an `abbrev`
so that every statement of this chapter speaks about **FS's own** `TildeData`
(the one the honest box model uses) and no cast is ever needed. -/
abbrev TildeData {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) := Work.BoseB7A.TildeData F

/-- FS's `M̃ = ⌊M/2⌋` (decay exponent of `χ̂`). -/
def Mt (E : Q3Env Mode) : ℝ := ((E.intM / 2 : ℕ) : ℝ)

/-- `η = (K_ℓ⁻²𝓁)^{M̃}`: the size of `χ̂`, `ccrX` on `P_H^q`. -/
def eta (E : Q3Env Mode) : ℝ := (E.Kl ^ (-(2 : ℝ)) * E.lille) ^ Mt E

/-- the box energy unit `μ²aℓ³`. -/
def E0 (E : Q3Env Mode) : ℝ := E.mu ^ 2 * E.aScat * E.ell ^ 3

/-- FS `eq:EstimateQ3Tilde1`'s error bracket (absolute). -/
def e1A (E : Q3Env Mode) : ℝ :=
  E0 E * (dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * eta E ^ 2
    + dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2
    + E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b
    + E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E)

/-- FS `eq:EstimateQ3Tilde2+3`'s error bracket (absolute). -/
def e23A (E : Q3Env Mode) : ℝ :=
  E0 E * (eta E * E.KL ^ 3 * E.Kl ^ (3 / 2 : ℝ) * dil E (1 / 4))

/-- FS `eq:EstimateQ3Tilde4`'s error bracket (absolute). -/
def e4A (E : Q3Env Mode) : ℝ :=
  E.rho ^ 2 * E.aScat * E.ell ^ 3 * Real.sqrt (E.bigM / E.z ^ 2) *
      (E.KH⁻¹ + (E.Kl * E.KL) ^ (-(E.intM : ℝ)) + (E.Kl * E.KL) ^ (3 / 2 : ℝ) * eta E)
    + E0 E * E.Kl ^ 2 * E.lille ^ 4 / E.b

/-- the target of the assembled `thm:Control3Q`:
`μ²aℓ³(μa³)^{1/2+1/323}` (lower order than LHY). -/
def controlErrA (E : Q3Env Mode) : ℝ := E0 E * dil E (1 / 2 + 1 / 323)

/-! ## 2. The reserve region and the gate -/

/-- The region kept for `§10` and the `q2exLowerR` reserve: `‖k‖ ≥ ½K_L√(μa)`
(`= ½(d²ℓ)⁻¹`). -/
def RHi (F : FockData Mode) (E : Q3Env Mode) (k : Mode) : Prop :=
  E.KL * Real.sqrt (E.mu * E.aScat) / 2 ≤ ‖F.kmom k‖

instance (F : FockData Mode) (E : Q3Env Mode) : DecidablePred (RHi F E) :=
  fun k => Classical.dec _

/-- **The honest `§10` kernel interface**: `Work.BoseK15.Q3Kernel'` with the four
rows repaired by F1/F7 and the `q2exLowerR` reserve, plus the oddness of the
label `kmom_neg` (finding F16 — see the module docstring). -/
structure Q3KernelFSAll (K₀ : ℝ) (F : FockData Mode) (T : TildeData F)
    (E : Q3Env Mode) : Prop where
  W1_le : ∀ k, |E.W1 k| ≤ K₀ * E.aScat
  W1_even : ∀ k, E.W1 (-k) = E.W1 k
  A_even : ∀ k, E.A (-k) = E.A k
  B_even : ∀ k, E.B (-k) = E.B k
  B_eq : ∀ k, E.B k = E.rho * E.W1 k
  AB : ∀ k, |E.B k| ≤ E.A k
  A_ge : ∀ q, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 2 ≤ E.A q
  fL_nonneg : ∀ s, 0 ≤ E.fL s
  fL_le_one : ∀ s, E.fL s ≤ 1
  fL_even : ∀ s, E.fL (-s) = E.fL s
  fL_supp2 : ∀ s, E.fL s ≠ 0 → ‖F.kmom s‖ ≤ 2 * (E.KL * Real.sqrt (E.mu * E.aScat))
  kmom_subW : ∀ s k, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    F.kmom (s - k) = F.kmom s - F.kmom k
  kmom_subL : ∀ s s', E.fL s ≠ 0 → E.fL s' ≠ 0 → F.kmom (s - s') = F.kmom s - F.kmom s'
  /-- **the row added by F16**: the label of the inverse mode.  True at the honest
  box (`valMinAbs` is odd), a field of `Work.BoseK15.K15Input`, and *needed* for
  the two `P_L × P_H` `NoWrap` families (see the module docstring). -/
  kmom_neg : ∀ i : Mode, F.kmom (-i) = -F.kmom i
  hasKernelW : ∀ i j, E.fL i ≠ 0 → j ∈ F.PHset E → E.W1 j ≠ 0 →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  hasKernel_noWrap : ∀ i j, Work.BoseK15.NoWrap F.kmom i j →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  hatChiSq_le : ∀ s, |E.hatChiSq s| ≤ 1
  hatChi_le : ∀ s, |E.hatChi s| ≤ 1
  hatChi_even : ∀ s, E.hatChi (-s) = E.hatChi s
  hatChiSq_even : ∀ s, E.hatChiSq (-s) = E.hatChiSq s
  hatChi_small : ∀ q, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * eta E
  ccrX_small : ∀ s q, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * eta E
  hatChiSq_form : ∀ (S : Finset Mode) (c : Mode → ℝ) (w : Mode → F.H),
    (∀ s ∈ S, c s ≠ 0 → E.fL s ≠ 0) →
      0 ≤ ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s) ∧
      ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s)
        ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (w s) (w s)
  count_PL : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ)
    ≤ K₀ * (E.Kl * E.KL) ^ 3
  sum_hatChiSq : ∑ s ∈ excited Mode, |E.hatChiSq s| ≤ K₀
  tail_hatChiSq : ∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
    ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))
  sum_W1sq : E.ell ^ (-(3 : ℝ)) *
      ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
    ≤ K₀ * E.aScat
  alpha_lip : ∀ p q, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
    |E.alpha p - E.alpha q| ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖
  W1omega0_nonneg : 0 ≤ E.W1omega0
  W1omega0_le : E.W1omega0 ≤ K₀ * E.aScat
  intOne : |E.rho * E.W1omega0 - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
    ≤ K₀ * E.rho * E.aScat * E.KH⁻¹
  q2exLowerR : ∀ Ψ : F.H, T.NWindow E.bigM Ψ →
    2 * E.rho * E.W1omega0 * F.qw Ψ (T.Gop E)
    ≤ F.qw Ψ (F.Q2exAll E) + (E.b / 400) * F.qw Ψ (T.gapOpT E)
      + (1 / 2) * F.qw Ψ (F.dNumOpR E (fun k => RHi F E k ∧ ¬ F.PHq E.KH E.aScat k))

/-- `thm:Control3Q`'s word with the diagonal reserve on `RHi` (the `§10` estimates
use `P_H ⊆ P_H^q ⊆ RHi`; the `q2exLowerR` reserve lives in `RHi ∖ P_H^q`). -/
def controlWordHi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  F.dNumOpR E (RHi F E) + T.Q3T E + F.Q2exAll E + T.linOpT E + (E.b / 50) • T.gapOpT E

/-- **`thm:Control3Q` re-delivery request (node C3Q)** at the corrected gate. -/
def Control3QFS (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Prop :=
  ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
    ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : FockData.{u, v} Mode) (T : Work.BoseB7A.TildeData.{u, v} F)
      (E : Q3Env.{u} Mode) (hv : FSParamsView E),
      hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E →
      ∀ Φ : F.H, T.NWindow E.bigM Φ →
        -(C * controlErrA E) * F.normSq Φ ≤ F.qw Φ (controlWordHi T E)

/-! ## 3. The `NoWrap` families of §10, from the label rows

FS's `eq:Commutator_general` holds at a pair `(i,j)` exactly when the label of
the difference is the difference of the labels (`Work.BoseK15.NoWrap`).  On a
finite mode group the *global* additivity is impossible
(`Work.BoseK15.Obstruction`); what is honest is the guarded additivity on the
pairs §10 sums over.  Every kernel evaluation of §10 is at one of the seven
pairs below, all of which reduce to the four families of the bundle's
`Work.BoseK15.noWrap_used_pairs`, with the extra guard `Ŵ₁ k ≠ 0` that the
corrected gate carries. -/

/-- **`NoWrap` at the four pair families of §10**, from the label rows of the
interface: for `s, s'` localised (`f_L ≠ 0`), `k ∈ P_H` with `Ŵ₁ k ≠ 0`, the
labels of `s-k`, `-k`, `k-s`, `s-s'` are the differences of the labels. -/
theorem noWrap_used_pairs {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : Q3KernelFSAll K₀ F T E) :
    (∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
        Work.BoseK15.NoWrap F.kmom (s - k) (-k)) ∧
    (∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
        Work.BoseK15.NoWrap F.kmom k (k - s)) ∧
    (∀ s s' k : Mode, E.fL s ≠ 0 → E.fL s' ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
        Work.BoseK15.NoWrap F.kmom (s - k) (s' - k)) ∧
    (∀ s s' k : Mode, E.fL s ≠ 0 → E.fL s' ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
        Work.BoseK15.NoWrap F.kmom (k - s) (k - s')) := by
  have key : ∀ s s' : Mode, E.fL s ≠ 0 → E.fL s' ≠ 0 →
      F.kmom (s - s') = F.kmom s - F.kmom s' := h.kmom_subL
  have key2 : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
      F.kmom (s - k) = F.kmom s - F.kmom k := h.kmom_subW
  have hneg : ∀ i : Mode, F.kmom (-i) = -F.kmom i := h.kmom_neg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s k hs hk hW
    show F.kmom ((s - k) - (-k)) = F.kmom (s - k) - F.kmom (-k)
    rw [show (s - k) - (-k) = s by abel, key2 s k hs hk hW, hneg k]
    abel
  · intro s k hs hk hW
    have hks : F.kmom (k - s) = F.kmom k - F.kmom s := by
      have h1 : F.kmom (-(s - k)) = -F.kmom (s - k) := hneg (s - k)
      rw [show k - s = -(s - k) by abel, h1, key2 s k hs hk hW]
      abel
    show F.kmom (k - (k - s)) = F.kmom k - F.kmom (k - s)
    rw [show k - (k - s) = s by abel, hks]
    abel
  · intro s s' k hs hs' hk hW
    show F.kmom ((s - k) - (s' - k)) = F.kmom (s - k) - F.kmom (s' - k)
    rw [show (s - k) - (s' - k) = s - s' by abel, key s s' hs hs',
      key2 s k hs hk hW, key2 s' k hs' hk hW]
    abel
  · intro s s' k hs hs' hk hW
    have hks : ∀ u : Mode, E.fL u ≠ 0 → F.kmom (k - u) = F.kmom k - F.kmom u := by
      intro u hu
      have h1 : F.kmom (-(u - k)) = -F.kmom (u - k) := hneg (u - k)
      rw [show k - u = -(u - k) by abel, h1, key2 u k hu hk hW]
      abel
    show F.kmom ((k - s) - (k - s')) = F.kmom (k - s) - F.kmom (k - s')
    rw [show (k - s) - (k - s') = s' - s by abel, hks s hs, hks s' hs',
      key s' s hs' hs]
    abel

/-- **The `NoWrap` pair `(-k, s-k)`** (`s` localised, `k ∈ P_H`, `Ŵ₁ k ≠ 0`): the
transpose of the first family. -/
theorem noWrap_neg_k {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : Q3KernelFSAll K₀ F T E) (s k : Mode) (hs : E.fL s ≠ 0)
    (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    Work.BoseK15.NoWrap F.kmom (-k) (s - k) := by
  have hk2 := h.kmom_subW s k hs hk hW
  show F.kmom ((-k) - (s - k)) = F.kmom (-k) - F.kmom (s - k)
  rw [show (-k) - (s - k) = -s by abel, h.kmom_neg s, h.kmom_neg k, hk2]
  abel

/-- **The `NoWrap` pair `(k-s, k)`** (`s` localised, `k ∈ P_H`, `Ŵ₁ k ≠ 0`). -/
theorem noWrap_kms_k {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : Q3KernelFSAll K₀ F T E) (s k : Mode) (hs : E.fL s ≠ 0)
    (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    Work.BoseK15.NoWrap F.kmom (k - s) k := by
  have hks : F.kmom (k - s) = F.kmom k - F.kmom s := by
    have h1 : F.kmom (-(s - k)) = -F.kmom (s - k) := h.kmom_neg (s - k)
    rw [show k - s = -(s - k) by abel, h1, h.kmom_subW s k hs hk hW]
    abel
  show F.kmom ((k - s) - k) = F.kmom (k - s) - F.kmom k
  rw [show (k - s) - k = -s by abel, h.kmom_neg s, hks]
  abel

/-- **The `NoWrap` pair `(k-s', k-s)`** (`s, s'` localised, `k ∈ P_H`,
`Ŵ₁ k ≠ 0`) -- the transpose of the fourth family. -/
theorem noWrap_swap_inner {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : Q3KernelFSAll K₀ F T E) (s s' k : Mode) (hs : E.fL s ≠ 0)
    (hs' : E.fL s' ≠ 0) (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    Work.BoseK15.NoWrap F.kmom (k - s') (k - s) := by
  have hks : ∀ u : Mode, E.fL u ≠ 0 → F.kmom (k - u) = F.kmom k - F.kmom u := by
    intro u hu
    have h1 : F.kmom (-(u - k)) = -F.kmom (u - k) := h.kmom_neg (u - k)
    rw [show k - u = -(u - k) by abel, h1, h.kmom_subW u k hu hk hW]
    abel
  show F.kmom ((k - s') - (k - s)) = F.kmom (k - s') - F.kmom (k - s)
  rw [show (k - s') - (k - s) = s - s' by abel, hks s hs, hks s' hs',
    h.kmom_subL s s' hs hs']
  abel

/-! ## 4. The kernel identity at the pairs of §10 -/

/-- **`F.ccrK` at the pair `(s-k,-k)`** of §10 (`P_L × P_H`), for `Ŵ₁ k ≠ 0`. -/
theorem kerA {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : Q3KernelFSAll K₀ F T E) (s k : Mode) (hs : E.fL s ≠ 0)
    (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    F.ccrK (s - k) (-k) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k) := by
  obtain ⟨nwA, _, _, _⟩ := noWrap_used_pairs h
  rw [h.hasKernel_noWrap (s - k) (-k) (nwA s k hs hk hW)]
  simp only [show (s - k) - (-k) = s by abel, h.hatChi_even k]
  ring

/-- FS `eq:Commutator_general` at the transpose `(-k, s−k)`. -/
theorem kerA' {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : Q3KernelFSAll K₀ F T E) (s k : Mode) (hs : E.fL s ≠ 0)
    (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    F.ccrK (-k) (s - k) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k) := by
  rw [h.hasKernel_noWrap (-k) (s - k) (noWrap_neg_k h s k hs hk hW)]
  simp only [show (-k) - (s - k) = -s by abel, h.hatChiSq_even s, h.hatChi_even k]

/-- FS `eq:Commutator_general` at `(k, k−s)`. -/
theorem kerB {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : Q3KernelFSAll K₀ F T E) (s k : Mode) (hs : E.fL s ≠ 0)
    (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    F.ccrK k (k - s) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k) := by
  obtain ⟨_, nwB, _, _⟩ := noWrap_used_pairs h
  rw [h.hasKernel_noWrap k (k - s) (nwB s k hs hk hW)]
  have e1 : E.hatChi (k - s) = E.hatChi (s - k) := by
    rw [show k - s = -(s - k) by abel, h.hatChi_even (s - k)]
  rw [show k - (k - s) = s by abel, e1]

/-- FS `eq:Commutator_general` at the transpose `(k−s, k)`. -/
theorem kerB' {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : Q3KernelFSAll K₀ F T E) (s k : Mode) (hs : E.fL s ≠ 0)
    (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    F.ccrK (k - s) k = E.hatChiSq s - E.hatChi k * E.hatChi (s - k) := by
  rw [h.hasKernel_noWrap (k - s) k (noWrap_kms_k h s k hs hk hW)]
  have e1 : E.hatChi (k - s) = E.hatChi (s - k) := by
    rw [show k - s = -(s - k) by abel, h.hatChi_even (s - k)]
  rw [show (k - s) - k = -s by abel, h.hatChiSq_even s, e1]
  ring

/-- FS `eq:Commutator_general` at `(s−k, s'−k)`. -/
theorem kerC {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : Q3KernelFSAll K₀ F T E) (s s' k : Mode) (hs : E.fL s ≠ 0)
    (hs' : E.fL s' ≠ 0) (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    F.ccrK (s - k) (s' - k)
      = E.hatChiSq (s - s') - E.hatChi (s - k) * E.hatChi (s' - k) := by
  obtain ⟨_, _, nwC, _⟩ := noWrap_used_pairs h
  rw [h.hasKernel_noWrap (s - k) (s' - k) (nwC s s' k hs hs' hk hW)]
  simp only [show (s - k) - (s' - k) = s - s' by abel]

/-- FS `eq:Commutator_general` at `(k−s, k−s')`. -/
theorem kerD {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : Q3KernelFSAll K₀ F T E) (s s' k : Mode) (hs : E.fL s ≠ 0)
    (hs' : E.fL s' ≠ 0) (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    F.ccrK (k - s) (k - s')
      = E.hatChiSq (s - s') - E.hatChi (s - k) * E.hatChi (s' - k) := by
  obtain ⟨_, _, _, nwD⟩ := noWrap_used_pairs h
  rw [h.hasKernel_noWrap (k - s) (k - s') (nwD s s' k hs hs' hk hW)]
  have e1 : E.hatChi (k - s) = E.hatChi (s - k) := by
    rw [show k - s = -(s - k) by abel, h.hatChi_even (s - k)]
  have e2 : E.hatChi (k - s') = E.hatChi (s' - k) := by
    rw [show k - s' = -(s' - k) by abel, h.hatChi_even (s' - k)]
  rw [show (k - s) - (k - s') = -(s - s') by abel, h.hatChiSq_even (s - s'), e1, e2]

/-- FS `eq:Commutator_general` at `(k−s', k−s)`. -/
theorem kerE {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : Q3KernelFSAll K₀ F T E) (s s' k : Mode) (hs : E.fL s ≠ 0)
    (hs' : E.fL s' ≠ 0) (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    F.ccrK (k - s') (k - s)
      = E.hatChiSq (s - s') - E.hatChi (s - k) * E.hatChi (s' - k) := by
  rw [h.hasKernel_noWrap (k - s') (k - s)
    (noWrap_swap_inner h s s' k hs hs' hk hW)]
  have e1 : E.hatChi (k - s) = E.hatChi (s - k) := by
    rw [show k - s = -(s - k) by abel, h.hatChi_even (s - k)]
  have e2 : E.hatChi (k - s') = E.hatChi (s' - k) := by
    rw [show k - s' = -(s' - k) by abel, h.hatChi_even (s' - k)]
  rw [show (k - s') - (k - s) = s - s' by abel, e1, e2]
  ring

/-- The seven evaluations of `F.ccrK` of §10, as one conjunction, each under the
guard `Ŵ₁ k ≠ 0`. -/
theorem kernel_pairs {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : Q3KernelFSAll K₀ F T E) :
    (∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
        F.ccrK (s - k) (-k) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k)) ∧
    (∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
        F.ccrK (-k) (s - k) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k)) ∧
    (∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
        F.ccrK k (k - s) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k)) ∧
    (∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
        F.ccrK (k - s) k = E.hatChiSq s - E.hatChi k * E.hatChi (s - k)) ∧
    (∀ s s' k : Mode, E.fL s ≠ 0 → E.fL s' ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
        F.ccrK (s - k) (s' - k) = E.hatChiSq (s - s') - E.hatChi (s - k) * E.hatChi (s' - k)) ∧
    (∀ s s' k : Mode, E.fL s ≠ 0 → E.fL s' ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
        F.ccrK (k - s) (k - s') = E.hatChiSq (s - s') - E.hatChi (s - k) * E.hatChi (s' - k)) ∧
    (∀ s s' k : Mode, E.fL s ≠ 0 → E.fL s' ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
        F.ccrK (k - s') (k - s) = E.hatChiSq (s - s') - E.hatChi (s - k) * E.hatChi (s' - k)) :=
  ⟨kerA h, kerA' h, kerB h, kerB' h, kerC h, kerD h, kerE h⟩

/-! ## 5. The integral kernel interface of `lem:EstimateIntegral` -/

/-- the kernel inputs of `lem:EstimateIntegral` (`gHat = ĝ` on the modes,
`R` = range of `v`) -- the same interface as the retired chapter. -/
structure IntKernel (K₀ R : ℝ) (F : FockData Mode) (E : Q3Env Mode) (gHat : Mode → ℝ) : Prop where
  W1_le : ∀ k, |E.W1 k| ≤ K₀ * E.aScat
  gHat_le : ∀ k, |gHat k| ≤ K₀ * E.aScat
  B_eq : ∀ k, E.B k = E.rho * E.W1 k
  A_eq : ∀ k, E.A k = E.tau k + E.rho * E.W1 k
  A_pos : ∀ k, F.PH E.KH E.aScat k → 0 < E.A k
  AB_kernel : ∀ k, F.PH E.KH E.aScat k → 2 * |E.B k| ≤ E.A k
  kmom_ne : ∀ k ∈ excited Mode, F.kmom k ≠ 0
  tau_PH : ∀ k, F.PH E.KH E.aScat k →
    0 ≤ ‖F.kmom k‖ ^ 2 - E.tau k ∧ ‖F.kmom k‖ ^ 2 - E.tau k ≤ 2 * ‖F.kmom k‖ / (E.d * E.s * E.ell)
  omega_lattice : |E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
      ∑ k ∈ excited Mode, E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)| ≤ K₀ * E.aScat ^ 2 / E.ell
  low_sum : E.ell ^ (-(3 : ℝ)) *
      ∑ k ∈ (excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k), 1 / ‖F.kmom k‖ ^ 2
    ≤ K₀ / (E.KH * E.aScat)
  sum_inv4 : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 4 ≤ K₀ * E.KH * E.aScat
  sum_inv6 : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 6 ≤ K₀ * (E.KH * E.aScat) ^ 3
  sum_inv3 : E.ell ^ (-(3 : ℝ)) *
      ∑ k ∈ (F.PHset E).filter (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat), 1 / ‖F.kmom k‖ ^ 3
    ≤ K₀ * (1 + Real.log E.KH)
  sum_W1sq : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 ≤ K₀ * E.aScat
  sum_diff : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, (gHat k - E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2
    ≤ K₀ * E.aScat * (R / E.ell) ^ 4

end Work.BoseC3QAll
