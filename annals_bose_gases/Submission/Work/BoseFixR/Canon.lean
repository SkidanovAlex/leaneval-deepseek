import ChallengeDeps
import Submission.Work.BoseFixR.Assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/Canon.lean` — the canonical realisation `KzCanon`

The reviewer's item: make the Fock realisation of FS §8 a **`def`** rather than an
existential over datums with free kernels, so that the residual `Prop`s
(`RB4box`, `RB5`, `RB67`) are statements about *FS's* operator and can be
dispatched.

`KzEnvFs v h μ F fc` is the canonical §10 environment: FS's scalars at the
diluteness `μa³` (`FSParamsView`), `z = √(μℓ³)` (so `ρ_z = μ`), and the kernels
pinned to FS §4's objects — `def:tau`, `Ŵ₁ = FT(W₁)`, `Ŵ₁ω = FT(W₁ω)`,
`Ŵ₁ω(0)`, normalised `χ̂`, `χ̂²` (of `χ_Λ = chiScale ℓ`; the normalisation is
forced by `KzKernels.hatChiSq_le` at the condensate mode —
`FINDING_canon_view_uninhabited.md` / `CanonViewFalse.lean`), `f_L` from a cut-off `LowCut`, and
the relations `𝒜 = τ + ρ_zŴ₁`, `ℬ = ρ_zŴ₁`.  `KzCanon v h F T fc` bundles it into
a `KzDatum` with `ĝ(0) = 8πa v`.

What is *not* fixed by these definitions is B4's Fock data `F`, the `θ`-mode
family `T` (BoseK15's instance) and the cut-off `fc`: those are the *data* of §8,
constrained by `FSParamsView`/`TildeData`/`Q3Kernel`.  The design's point — and
the reason the residual `Prop`s quantify over them — is that FS §9/§10 are
estimates that hold for **every admissible** choice of that data.

## The view of `KzCanon`

`KzDatum.view (KzCanon v h μ F T fc) v h μ` unfolds to

* `Nonempty (FSParamsView (KzEnvFs …))` — FS's parameter point; provable from
  `Work.BoseBox.paramsOK_fsParams_le_one` and the `fsXp` closed forms
  (`Work.BoseB7.fsEnv_closed` machinery), *not* done here;
* the scalar/kernel equalities — `rfl` by construction;
* `∃ K₀ b₀, 0 ≤ K₀ ∧ 0 < b₀ ∧ b₀ ≤ E.b ∧ ∀ ρ, CloseCond v μ ρ →
  Work.BoseB7A.Q3Kernel K₀ F T (KzEnvAt (KzEnvFs …) ρ)` — **BoseK15's obligation**
  (the K1–K5 instantiation of `Q3Kernel` at FS's data).

So the residual obligations *at* `KzCanon` are exactly FS §8/§9/§10 on FS's data,
with BoseK15's `Q3Kernel` and a `FSParamsView` view as the only inputs.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The canonical §10 environment**: FS's parameter point at the diluteness
`μa³` and FS §4's kernels, on the mode system `F` of B4, with the low-momentum
cut-off `fc`. -/
def KzEnvFs {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (F : Work.BoseB7.FockData Mode)
    (fc : LowCut) : Work.BoseB7.Q3Env Mode :=
  let P := paramsAt μ (a v)
  let ℓ := sideAt μ (a v)
  let t := dil v μ
  { z := Real.sqrt (μ * ℓ ^ 3)
    ell := ℓ
    mu := μ
    aScat := a v
    KH := Work.BoseB7.KH P.KH μ (a v)
    Kl := P.Kl
    KL := (P.Kl * P.d ^ 2) ^ (-(1 : ℝ))
    d := P.d
    s := P.s
    eT := P.eT
    b := P.b
    intM := P.M
    bigM := bigM P (a v) μ
    delta := 1
    fL := fun k => fLFS fc ((P.Kl * P.d ^ 2) ^ (-(1 : ℝ))) μ (a v) (F.kmom k)
    W1 := fun k => chat (W1fun v h ℓ) (F.kmom k)
    W1omega := fun k => chat (W1omegaFun v h ℓ) (F.kmom k)
    W1omega0 := chat (W1omegaFun v h ℓ) 0
    -- FS §4's kernels: `χ̂` and `χ̂²` are the Fourier transforms of
    -- `χ_ℓ = chiScale ℓ = χ(·/ℓ)` divided by the **same** normaliser
    -- `∫χ_ℓ² = ℓ³` — this is B4's box kernel (`Work.BoseB4.b7FockDataBox`), i.e.
    -- `E.hatChi k = corpusBox.hatChi (ℓ • kmom k)` and
    -- `E.hatChiSq k = corpusBox.hatChiSq (ℓ • kmom k)`; dividing `χ̂` by
    -- `∫χ_ℓ = ℓ³∫χ` instead would make the view unsatisfiable at the box data
    -- (`FINDING_bogopbound_honestfam_vacuous.md`).
    hatChi := fun k => chat (chiFun ℓ) (F.kmom k)
      / chat (fun z => chiFun ℓ z ^ 2) 0
    hatChiSq := fun k => chat (fun z => chiFun ℓ z ^ 2) (F.kmom k)
      / chat (fun z => chiFun ℓ z ^ 2) 0
    tau := fun k => tauFS P.eT P.s P.d ℓ (F.kmom k)
    A := fun k => tauFS P.eT P.s P.d ℓ (F.kmom k) + μ * chat (W1fun v h ℓ) (F.kmom k)
    B := fun k => μ * chat (W1fun v h ℓ) (F.kmom k) }

/-- **The canonical realisation**: B4's Fock data `F`, BoseK15's `θ`-mode family
`T`, FS's canonical environment and `ĝ(0) = 8πa v`. -/
def KzCanon (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ)
    (Mode' : Type) [AddCommGroup Mode'] [Fintype Mode'] [DecidableEq Mode']
    (F : Work.BoseB7.FockData.{0, 0} Mode') (T : Work.BoseB7A.TildeData F)
    (fc : LowCut) : KzDatum where
  Mode := Mode'
  F := F
  E := KzEnvFs v h μ F fc
  gHat0 := 8 * π * a v
  T := T

/-- The canonical family: one realisation per chemical potential. -/
def KzCanonFam (v : ℝ³ → ℝ) (h : ScatSol v)
    (Mode : Type) [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData.{0, 0} Mode) (T : Work.BoseB7A.TildeData F)
    (fc : LowCut) : ℝ → KzDatum :=
  fun μ => KzCanon v h μ Mode F T fc

/-! ## The node at the canonical realisation

With the three residual obligations at `KzCanonFam`, the proved assembly
(`Assembly.nodeRestrictedB_of_residuals`) gives the node directly. -/

theorem nodeRestrictedB_canon {v : ℝ³ → ℝ} {h : ScatSol v} {R J η₀ : ℝ}
    (hav : 0 < a v) (hR : 0 ≤ R) (hη₀ : 0 ≤ η₀) (hη₂ : η₀ < 2 / 323)
    (hη₃ : η₀ ≤ 1 / 1615)
    (Mode : Type) [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData.{0, 0} Mode) (T : Work.BoseB7A.TildeData F) (fc : LowCut)
    (h4 : RB4box v h R J (KzCanonFam v h Mode F T fc))
    (h5 : RB5 v h R (KzCanonFam v h Mode F T fc))
    (h67 : RB67 v h R (KzCanonFam v h Mode F T fc)) :
    ∃ C : ℝ, 0 ≤ C ∧ NodeRestrictedB v h J η₀ C :=
  nodeRestrictedB_of_residuals hav hR hη₀ hη₂ hη₃ h4 h5 h67

/-- The node `D7` at the canonical realisation, with `η₀ = 1/1800`. -/
theorem nodeRestrictedB_holds_canon {v : ℝ³ → ℝ} {h : ScatSol v} {R J' : ℝ}
    (hav : 0 < a v) (hR : 0 ≤ R) (hJ' : lhyC < J')
    (Mode : Type) [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData.{0, 0} Mode) (T : Work.BoseB7A.TildeData F) (fc : LowCut)
    (h4 : RB4box v h R J' (KzCanonFam v h Mode F T fc))
    (h5 : RB5 v h R (KzCanonFam v h Mode F T fc))
    (h67 : RB67 v h R (KzCanonFam v h Mode F T fc)) :
    ∃ η₀ : ℝ, 1 / 2000 < η₀ ∧ η₀ < 2 / 323 ∧
      ∃ C : ℝ, 0 ≤ C ∧ NodeRestrictedB v h J' η₀ C :=
  nodeRestrictedB_holds_of_residuals hav hR hJ' h4 h5 h67

end Work.BoseFixR
