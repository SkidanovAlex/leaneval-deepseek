import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.RadialIntegral
import Submission.Work.BoseB7.Control3Q_of_estimates_at
import Submission.Work.BoseB7.EstIntegralTwo_of_EstIntegralOne
import Submission.Work.BoseB7.FSParamsView_inhabited
import Submission.Work.BoseB7.Q3four_eq_linear
import Submission.Work.BoseB7.a_aDag_le
import Submission.Work.BoseB7.alpha_secondOrder_bound
import Submission.Work.BoseB7.bNumOp_le_spect
import Submission.Work.BoseB7.bNumOp_nonneg
import Submission.Work.BoseB7.exists_estHyp
import Submission.Work.BoseB7.linearTerm_bound
import Submission.Work.BoseB7.region_neg
import Submission.Work.BoseB7.sum_PHset_neg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Defs` — FS §10 (`thm:Control3Q`) with ABSOLUTE constants

Design: `BOSE_3Q_LEAD.md` (curric-46, 2026-10-03).  This is the *interface* of the
`BoseB7A` subproject.  Corrections to `Work.BoseB7` (the retired `B7` chapter):

* the low-momentum slot `s` of FS `eq:kroelleQ3z` carries FS's `ã_s` (the θ-modes
  `ℓ^{-3/2}a(Q e^{isx}θ)`, orthonormal, canonical), not the χ-modes `a_s`:
  `TildeData` adds them, together with FS's true `n₊` (`N`) and `n₊^H` (`NH`);
* `(2π)⁻³∫dk = ℓ⁻³ Σ_k` in `lem:EstimateIntegral` (B7 dropped the `ℓ⁻³`);
* FS's `K_H^{-1}(μa³)^{5/12}` in `eq:CompIntegrals-Final`/`eq:EstimateQ3Tilde4`/`eq:Q3Cancels`
  is `K̃_H^{-1}(μa³)^{5/12} = E.KH⁻¹` (full `K_H`); B7 wrote `E.KH⁻¹·(μa³)^{5/12}`;
* `eq:EstimateQ3Tilde2+3`'s exponent is `M̃ = ⌊M/2⌋`, not `M`;
* the `𝓁⁴a/ℓ` of `eq:EstimateQ3Tilde4` is `K_ℓ²𝓁⁴/b` (FS dropped the factor `z`);
* the `Q₃^{(1)}`/`Q₃^{(2)}` absorptions need `∫𝒟b†b` on the quarter region `P_H^q`
  (`|q| ≥ ¼K_H⁻¹a⁻¹`, which contains every `s − k`), not only on `P_H`.

**One addition to the statement file's `Q3Kernel`**: the fields `hatChi_even` and
`hatChiSq_even` (evenness of `χ̂`, `χ̂²`).  `Q3Kernel` is the *only* hypothesis of
the three estimates, and `Q3T_split` (the Bogoliubov substitution, the first step
of every estimate) needs the two squeezed commutators `[b_{s−k},b_{−k}†]` and
`[b_{−k},b_{s−k}†]` to be equal — from `hasKernel` this is exactly
`χ̂(−k) = χ̂(k)` and `χ̂²(−s) = χ̂²(s)`.  These are true facts about the honest
`χ_Λ` (a symmetric localisation), they are not derivable from the other fields,
and without them the estimates are unprovable as stated.  Recorded in the final
report.

The definitions below are copied **verbatim** from
`BOSE_3Q_STATEMENTS.lean.txt` (the typechecked design statements), with the only
change being the namespace (`Work.BoseB7A` instead of `Work.Bose3Q`) — the
`F.PHq` def stays in `Work.BoseB7.FockData`, where it is used as a method.

## The shape of the estimates (absolute constants)

Every estimate has the shape

```
∀ K₀ b₀, ∃ C t₀ > 0, ∀ Mode F T E (hv : FSParamsView E),
  t ≤ t₀ → b₀ ≤ b → Q3Kernel K₀ F T E → ∀ Φ ∈ NWindow 𝓜,
  ⟨Φ, LHS Φ⟩ ≥ −C · err · ‖Φ‖²
```

`C` and `t₀` depend **only** on `K₀` and `b₀`; `Mode`, `F`, `T`, `E` are
quantified inside the `∃`.  No constant is ever defined from an instance.

## Contents

* `FockData.PHq` — the quarter region `P_H^q = {|q| ≥ ¼K_H⁻¹a⁻¹}`.
* `TildeData` — the θ-modes `ã_s`, the cross commutator `ccrX`, FS's `n₊` (`N`),
  `n₊^H` (`NH`) and the number grading.
* `TildeData.qtermT … controlWordT`, `NWindow` — the corrected `3Q` words.
* `Mt`, `eta`, `E0`, `e1A`, `e23A`, `e4A`, `controlErrA` — the error brackets.
* `Q3Kernel`, `IntKernel` — the kernel interface (B4/B6 obligations).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7.FockData

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable (F : FockData Mode)

/-- FS's "½P_H" in the precise form used: `P_H^q = {|q| ≥ ¼K_H⁻¹a⁻¹}`; it contains `P_H`
and every `s − k` with `s ∈ supp f_L`, `k ∈ P_H` (under `con:KLKH`). -/
def PHq (KH a : ℝ) (i : Mode) : Prop := 1 / (4 * KH * a) ≤ ‖F.kmom i‖

instance (KH a : ℝ) : DecidablePred (F.PHq KH a) :=
  fun i => decidable_of_iff (1 / (4 * KH * a) ≤ ‖F.kmom i‖) Iff.rfl

end Work.BoseB7.FockData

namespace Work.BoseB7A

open Work.BoseB7

set_option linter.unusedVariables false

/-! ## 1. The θ-modes and the true number operators -/

/-- **FS's second mode family and number operators**, on top of B7's χ-mode
`FockData`: `ta s = ã_s = ℓ^{-3/2}a(Q(e^{isx}θ))` (canonical on the excited lattice),
the cross commutator `[ã_s, a_k†] = ccrX s k` (`= χ̂((k−s)ℓ)` on the lattice), and FS's
`n₊` (`N`) and `n₊^H` (`NH`) as honest operators with the number grading. -/
structure TildeData {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) where
  ta : Mode → F.H →ₗ[ℝ] F.H
  taDag : Mode → F.H →ₗ[ℝ] F.H
  taDag_adjoint : ∀ (s : Mode) (f g : F.H), F.bp (taDag s f) g = F.bp f (ta s g)
  ta_comm : ∀ s t : Mode, ta s ∘ₗ ta t = ta t ∘ₗ ta s
  taDag_comm : ∀ s t : Mode, taDag s ∘ₗ taDag t = taDag t ∘ₗ taDag s
  /-- `[ã_s, ã_t†] = δ_{st}` on the excited modes (orthonormal θ-modes). -/
  ta_ccr : ∀ s t : Mode, s ≠ 0 → t ≠ 0 →
    ta s ∘ₗ taDag t = taDag t ∘ₗ ta s + (if s = t then (1 : ℝ) else 0) • (1 : F.H →ₗ[ℝ] F.H)
  ta_a_comm : ∀ s k : Mode, ta s ∘ₗ F.a k = F.a k ∘ₗ ta s
  ccrX : Mode → Mode → ℝ
  /-- `[ã_s, a_k†] = ccrX s k`. -/
  ta_aDag : ∀ s k : Mode, ta s ∘ₗ F.aDag k = F.aDag k ∘ₗ ta s + (ccrX s k) • (1 : F.H →ₗ[ℝ] F.H)
  /-- FS's `n₊` on `𝓕(Ran Q)`. -/
  N : F.H →ₗ[ℝ] F.H
  /-- FS's `n₊^H`. -/
  NH : F.H →ₗ[ℝ] F.H
  N_symm : ∀ f g : F.H, F.bp (N f) g = F.bp f (N g)
  N_nonneg : ∀ f : F.H, 0 ≤ F.bp (N f) f
  NH_nonneg : ∀ f : F.H, 0 ≤ F.bp (NH f) f
  /-- number grading: `[n₊, a_k] = −a_k`, `[n₊, a_k†] = a_k†`, same for `ã`. -/
  N_a : ∀ k : Mode, N ∘ₗ F.a k = F.a k ∘ₗ N - F.a k
  N_aDag : ∀ k : Mode, N ∘ₗ F.aDag k = F.aDag k ∘ₗ N + F.aDag k
  N_ta : ∀ s : Mode, N ∘ₗ ta s = ta s ∘ₗ N - ta s
  N_taDag : ∀ s : Mode, N ∘ₗ taDag s = taDag s ∘ₗ N + taDag s
  /-- a finite family of orthonormal θ-modes counts at most `n₊` particles. -/
  ta_le_N : ∀ (S : Finset Mode), (∀ s ∈ S, s ≠ 0) → ∀ f : F.H,
    F.bp ((∑ s ∈ S, taDag s ∘ₗ ta s) f) f ≤ F.bp (N f) f

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 2. Regions -/

/-! ## 3. The corrected `3Q` words (ã in the `s`-slot) -/

namespace TildeData

variable {F : FockData Mode} (T : TildeData F)

/-- `ã_s† a_{s−k} a_k`, the cubic monomial of FS `eq:kroelleQ3z` (θ-mode slot). -/
def qtermT (s k : Mode) : F.H →ₗ[ℝ] F.H := T.taDag s ∘ₗ (F.a (s - k) ∘ₗ F.a k)

/-- Its formal adjoint `a_k† a_{s−k}† ã_s`. -/
def qtermDagT (s k : Mode) : F.H →ₗ[ℝ] F.H := F.aDag k ∘ₗ (F.aDag (s - k) ∘ₗ T.ta s)

/-- FS `eq:kroelleQ3z`, `ℓ³(2π)⁻⁶∬ → ℓ⁻³Σ_sΣ_k` (unchanged normalisation, B7's is right). -/
def Q3T (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) • ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
    (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k)

/-- FS `lem:EstimatesOnQ3-js`: `Q₃^{(1)}`, in the θ-mode slot. -/
def Q3oneT (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) • ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
    (E.fL s * E.W1 k * E.q3Denom s k) •
      (T.taDag s ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ F.bOp E.alpha k)
        + (E.alpha k * E.alpha (s - k)) •
            (T.taDag s ∘ₗ (F.bOpDag E.alpha (k - s) ∘ₗ F.bOpDag E.alpha (-k)))
        + F.bOpDag E.alpha k ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ T.ta s)
        + (E.alpha k * E.alpha (s - k)) •
            (F.bOp E.alpha (-k) ∘ₗ (F.bOp E.alpha (k - s) ∘ₗ T.ta s)))

/-- FS `lem:EstimatesOnQ3-js`: `Q₃^{(2)}`, in the θ-mode slot. -/
def Q3twoT (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) • ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
    (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)) •
      (T.taDag s ∘ₗ (F.bOpDag E.alpha (-k) ∘ₗ F.bOp E.alpha (s - k))
        + F.bOpDag E.alpha (s - k) ∘ₗ (F.bOp E.alpha (-k) ∘ₗ T.ta s))

/-- FS `lem:EstimatesOnQ3-js`: `Q₃^{(3)}`, in the θ-mode slot. -/
def Q3threeT (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) • ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
    (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k)) •
      (T.taDag s ∘ₗ (F.bOpDag E.alpha (k - s) ∘ₗ F.bOp E.alpha k)
        + F.bOpDag E.alpha k ∘ₗ (F.bOp E.alpha (k - s) ∘ₗ T.ta s))

/-- FS `lem:EstimatesOnQ3-js`: `Q₃^{(4)}`, in the θ-mode slot. -/
def Q3fourT (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) • ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
    (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)) •
      (F.bCommutator E s k ∘ₗ (T.taDag s + T.ta s))

/-- FS's linear term `ρ_z z Ŵ₁ω(0)(2π)⁻³∫χ̂_Λ²(s)(ã_s†+ã_s)ds = ρ_zzŴ₁ω(0)Σ_sχ̂²(sℓ)(ã_s†+ã_s)`
(no `ℓ`-factor: `χ̂_Λ²(s) = ℓ³χ̂²(sℓ)`). -/
def linOpT (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.rho * E.z * E.W1omega0) • ∑ s ∈ excited Mode, (E.hatChiSq s) • (T.taDag s + T.ta s)

/-- FS's gap `ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H` with the true `n₊`, `n₊^H`. -/
def gapOpT (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  E.ell ^ (-(2 : ℝ)) • T.N + (E.eT * (E.d * E.ell) ^ (-(2 : ℝ))) • T.NH

/-- FS `eq:RepInTermsOfatilde`: `G = Σ_{s,s'} f_L(s)f_L(s')χ̂²((s'−s)ℓ) ã_{s'}†ã_s
= Σ_j Q_{L,j}χ_Λ²Q_{L,j}`. -/
def Gop (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
    (E.fL s * E.fL s' * E.hatChiSq (s' - s)) • (T.taDag s' ∘ₗ T.ta s)

/-- FS `eq:Q3Cancels` left-hand side (corrected words). -/
def controlWordT (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  F.dNumOpR E (fun _ => True) + T.Q3T E + F.Q2ex E + T.linOpT E + (E.b / 50) • T.gapOpT E

/-- **FS's window `eq:LocalizedAftercNumber`** `Φ = 1_{[0,𝓜]}(n₊)Φ`, algebraically:
`Φ` is a finite sum of `n₊`-eigenvectors with eigenvalues `m ≤ 𝓜`. -/
def NWindow (M : ℝ) (Φ : F.H) : Prop :=
  ∃ φ : ℕ → F.H, (∀ m : ℕ, T.N (φ m) = (m : ℝ) • φ m) ∧
    Φ = ∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m

end TildeData

/-! ## 4. Error brackets (proof-shaped, `C = 1`) -/

/-- FS's `M̃ = ⌊M/2⌋` (decay exponent of `χ̂`, `lem:DecaychiHat`). -/
def Mt (E : Q3Env Mode) : ℝ := ((E.intM / 2 : ℕ) : ℝ)

/-- `η = (K_ℓ⁻²𝓁)^{M̃}`: the size of `χ̂`, `ccrX` on `P_H^q` (`eq:DecayPH`). -/
def eta (E : Q3Env Mode) : ℝ := (E.Kl ^ (-(2 : ℝ)) * E.lille) ^ Mt E

/-- the box energy unit `μ²aℓ³`. -/
def E0 (E : Q3Env Mode) : ℝ := E.mu ^ 2 * E.aScat * E.ell ^ 3

/-- FS `eq:EstimateQ3Tilde1`'s error bracket (absolute, corrected, `M̃ = ⌊M/2⌋`). -/
def e1A (E : Q3Env Mode) : ℝ :=
  E0 E * (dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * eta E ^ 2
    + dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2
    + E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b
    + E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E)

/-- FS `eq:EstimateQ3Tilde2+3`'s error bracket (absolute, corrected, `M̃ = ⌊M/2⌋`). -/
def e23A (E : Q3Env Mode) : ℝ :=
  E0 E * (eta E * E.KL ^ 3 * E.Kl ^ (3 / 2 : ℝ) * dil E (1 / 4))

/-- FS `eq:EstimateQ3Tilde4`'s error bracket (absolute, corrected: full `K_H⁻¹`,
`K_ℓ²𝓁⁴/b`). -/
def e4A (E : Q3Env Mode) : ℝ :=
  E.rho ^ 2 * E.aScat * E.ell ^ 3 * Real.sqrt (E.bigM / E.z ^ 2) *
      (E.KH⁻¹ + (E.Kl * E.KL) ^ (-(E.intM : ℝ)) + (E.Kl * E.KL) ^ (3 / 2 : ℝ) * eta E)
    + E0 E * E.Kl ^ 2 * E.lille ^ 4 / E.b

/-- the target of the assembled `thm:Control3Q`: `μ²aℓ³(μa³)^{1/2+1/323}` (lower order than
LHY by `X = (μa³)^{1/323}`). -/
def controlErrA (E : Q3Env Mode) : ℝ := E0 E * dil E (1 / 2 + 1 / 323)

/-! ## 5. The kernel interface (B4/B6 obligations, each with an absolute `K₀`) -/

/-- Everything §10 uses about the kernels, at one parameter point, with one absolute
constant `K₀`.  Every field is a fact about FS's honest data (`lem:DecaychiHat`, lattice
counting, `eq:I2-integral`, `lem:EstimateIntegral`, the first-quantised `Q₂^ex` bound). -/
structure Q3Kernel (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) : Prop where
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
  fL_supp : ∀ s, E.fL s ≠ 0 → F.PL E.KL E.mu E.aScat s
  kmom_sub : ∀ s k, E.fL s ≠ 0 → k ∈ F.PHset E → F.kmom (s - k) = F.kmom s - F.kmom k
  hasKernel : ∀ i j, F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  hatChiSq_le : ∀ s, |E.hatChiSq s| ≤ 1
  hatChi_le : ∀ s, |E.hatChi s| ≤ 1
  /-- **Deviation from `BOSE_3Q_STATEMENTS.lean.txt`** (documented in the header):
  `χ̂` is even.  It is a true fact about the honest `χ_Λ` (and is what makes the
  two squeezed commutators `[b_{s−k},b_{−k}†]` and `[b_{−k},b_{s−k}†]` *equal*,
  hence `Q3T_split` true), and it is *not* derivable from the other fields, so it
  must be part of the interface. -/
  hatChi_even : ∀ s, E.hatChi (-s) = E.hatChi s
  /-- `χ̂²` is even (same reason; `Q3Kernel` is the only hypothesis of the three
  estimates, so everything they use has to be here). -/
  hatChiSq_even : ∀ s, E.hatChiSq (-s) = E.hatChiSq s
  hatChi_small : ∀ q, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * eta E
  ccrX_small : ∀ s q, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * eta E
  /-- Bochner + `‖χ‖∞`: the kernel `χ̂²((s'−s)ℓ)` is PSD and `≤ K₀` (Schur form). -/
  hatChiSq_form : ∀ (S : Finset Mode) (c : Mode → ℝ) (v : Mode → F.H), (∀ s ∈ S, s ≠ 0) →
    0 ≤ ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s) ∧
    ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s)
      ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s)
  count_PL : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) ≤ K₀ * (E.Kl * E.KL) ^ 3
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
  /-- node `N-INT` (corrected `EstIntegralOne`). -/
  intOne : |E.rho * E.W1omega0 - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
    ≤ K₀ * E.rho * E.aScat * E.KH⁻¹
  /-- node `N-Q2` (first-quantised): `Q₂^ex` pays for the `T₂,comm` main term. -/
  q2exLower : ∀ Ψ : F.H, 2 * E.rho * E.W1omega0 * F.qw Ψ (T.Gop E)
    ≤ F.qw Ψ (F.Q2ex E) + (E.b / 400) * F.qw Ψ (T.gapOpT E)

/-- the kernel inputs of `lem:EstimateIntegral` (`gHat = ĝ` on the modes, `R` = range of `v`).

**Deviation from `BOSE_3Q_STATEMENTS.lean.txt`**: the two fields `A_pos` and
`AB_kernel` are added.  They are *derivable* from `tau_PH` + `B_eq` + the smallness
of `E.rho * E.K₀ * a * K_H²` at small `t` (indeed `𝒜_k ≥ ‖k‖²/4 > 0` on `P_H`), but
without them the statement is exposed to the (spurious) reading of `tau_PH` as an
*upper* bound on `τ` only, under which `α = ℬ/(𝒜+√(𝒜²−ℬ²))` could be unbounded
from below.  Stating them costs nothing at the honest instance and makes the
lemma robustly provable. -/
structure IntKernel (K₀ R : ℝ) (F : FockData Mode) (E : Q3Env Mode) (gHat : Mode → ℝ) : Prop where
  W1_le : ∀ k, |E.W1 k| ≤ K₀ * E.aScat
  gHat_le : ∀ k, |gHat k| ≤ K₀ * E.aScat
  B_eq : ∀ k, E.B k = E.rho * E.W1 k
  A_eq : ∀ k, E.A k = E.tau k + E.rho * E.W1 k
  /-- `𝒜_k = τ_k + ρŴ₁(k)` is positive on `P_H` (it is `≥ ‖k‖²/4` there). -/
  A_pos : ∀ k, F.PH E.KH E.aScat k → 0 < E.A k
  /-- FS `eq:BoverA`: `2|ℬ_k| ≤ 𝒜_k` on `P_H` (`⟹ 1−α² ≥ 1/2`, `𝒟 ≥ 𝒜/2`). -/
  AB_kernel : ∀ k, F.PH E.KH E.aScat k → 2 * |E.B k| ≤ E.A k
  kmom_ne : ∀ k ∈ excited Mode, F.kmom k ≠ 0
  tau_PH : ∀ k, F.PH E.KH E.aScat k →
    0 ≤ ‖F.kmom k‖ ^ 2 - E.tau k ∧ ‖F.kmom k‖ ^ 2 - E.tau k ≤ 2 * ‖F.kmom k‖ / (E.d * E.s * E.ell)
  /-- the lattice form of `Ŵ₁ω(0) = (2π)⁻³∫Ŵ₁ĝ/(2k²)` (periodic Green's function). -/
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

end Work.BoseB7A
