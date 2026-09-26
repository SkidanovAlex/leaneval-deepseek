/-
# The rigidity statements of the paper: with the moderate-growth hypothesis

**Why this file exists.**  CKMRV's `lem:noPsolutions` is a statement about the space
`Ann_k(𝓘_±, 𝒫)`: the functions of *moderate growth* annihilated by the ideal
`(S ∓ I)R + (T − I)²R`.  The hypothesis `f ∈ 𝒫` is not decoration.  It is exactly what
excludes the infinite-dimensional space of "exotic" solutions whose `q`-expansion vanishes
to order `2` at the cusp by cancellation but which have an *essential singularity at the
cusp*.  `Submission/Work/Rigidity/Counterexample.lean` records such a function explicitly:
a nonzero `f`, holomorphic on `ℍ`, with `(T − I)² f = 0`, `f ∣[4] S = −f` and
`f(τ) = o(1)` along the strip — hence (with `g = g̃ = f/2`)

  `Work.FE.HomogeneousRigidity 8 0` is FALSE as stated in
  `Submission/Work/FunctionalEquations/Gap.lean`, and likewise
  `Work.FE.HomogeneousRigidity 24 1`.

This file therefore provides the *paper-faithful* variants, with the moderate-growth
hypothesis `Work.Kernels.InP` restored.

## Main definitions and results

* `Work.Rigidity.SingleRigidityP k ε c` : `SingleRigidity` with `f ∈ 𝒫`.
* `Work.Rigidity.HomogeneousRigidityP n c` : `HomogeneousRigidity` with `g(τ,·)`, `g̃(τ,·) ∈ 𝒫`
  for each `x` — which is what the paper's Section 8 lemma assumes.
* `Work.Rigidity.homogeneousRigidityP_of_singleRigidityP` : the eigenfunction reduction for
  the corrected statement (proved).
* `Work.Rigidity.homogeneousRigidity_of_homogeneousRigidityP` : the *uncorrected* statement
  implies the corrected one (`HomogeneousRigidity ⟹ HomogeneousRigidityP`); the converse is
  false.
-/
import Mathlib
import Submission.Work.Rigidity.Reduction

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

open Filter

/-- **`lem:noPsolutions` with its moderate-growth hypothesis.**  No nonzero `f ∈ 𝒫` that is
annihilated by `(T − I)²`, is an eigenfunction of `|_k S` with eigenvalue `ε`, and decays
like `o(e^{−2πc Im τ})` along the strip `-1 ≤ Re τ ≤ 1`.

For `k = 4`, `c = 0` and `k = 12`, `c = 1` this is exactly CKMRV Lemma `lem:noPsolutions`
at the two weights used in Section 8, one eigenvalue at a time. -/
def SingleRigidityP (k : ℤ) (ε : ℂ) (c : ℝ) : Prop :=
  ∀ f : ℍ → ℂ, Work.Kernels.InP f → AnnT2 f → SlashEigen k ε f → StripDecay c f → f = 0

/-- `SingleRigidityP` is weaker than `SingleRigidity`: the latter drops the growth
hypothesis.  (It is the latter that is false; see the module header.) -/
theorem singleRigidityP_of_singleRigidity {k : ℤ} {ε : ℂ} {c : ℝ}
    (h : SingleRigidity k ε c) : SingleRigidityP k ε c :=
  fun f hf => h f hf.1

/-- `HomogeneousRigidityP n c` : `Work.FE.HomogeneousRigidity n c` with the moderate growth
of `g(τ, x)` and `g̃(τ, x)` in `τ` (for each fixed `x`) restored; this is the paper's
Section 8 uniqueness lemma (`g, g̃ ∈ 𝒫`) at weight `n/2`. -/
def HomogeneousRigidityP (n : ℕ) [NeZero n] (c : ℝ) : Prop :=
  ∀ (g gt : ℂ → Work.FE.E n → ℂ),
    (∀ x, Work.Kernels.InP (fun τ : ℍ => g (τ : ℂ) x)) →
    (∀ x, Work.Kernels.InP (fun τ : ℍ => gt (τ : ℂ) x)) →
    (∀ (τ : ℂ) (x : Work.FE.E n), 0 < τ.im → g (τ + 2) x - 2 * g (τ + 1) x + g τ x = 0) →
    (∀ (τ : ℂ) (x : Work.FE.E n), 0 < τ.im → gt (τ + 2) x - 2 * gt (τ + 1) x + gt τ x = 0) →
    (∀ (τ : ℂ) (x : Work.FE.E n), 0 < τ.im →
      g τ x + Work.FE.slashFactor n τ * gt (-1 / τ) x = 0) →
    Work.FE.TendsToZeroInStrip n c g → Work.FE.TendsToZeroInStrip n c gt →
    ∀ (τ : ℂ) (x : Work.FE.E n), 0 < τ.im → g τ x = 0 ∧ gt τ x = 0

/-- **The corrected reduction.**  `(i/τ)^k = τ^{-k}`, `k` even, and the two weight-`k`
single-function statements *with the growth hypothesis* imply the paper-faithful
two-variable statement. -/
theorem homogeneousRigidityP_of_singleRigidityP {n : ℕ} [NeZero n] {c : ℝ} {k : ℤ}
    (hsf : ∀ τ : ℍ, Work.FE.slashFactor n (τ : ℂ) = (τ : ℂ) ^ (-k))
    (hkeven : Even k)
    (hRneg : SingleRigidityP k (-1 : ℂ) c) (hRpos : SingleRigidityP k (1 : ℂ) c) :
    HomogeneousRigidityP n c := by
  intro g gt hPg hPgt hT2g hT2gt hS hdecg hdecgt
  exact homogeneousRigidity_of_eigen (fun f => Work.Kernels.InP f)
    (fun hf hg => hf.add hg) (fun hf => hf.neg) hsf hkeven
    (fun f hP _ => hRneg f hP) (fun f hP _ => hRpos f hP)
    g gt hPg hPgt
    (fun x => differentiableOn_of_mdifferentiable (hPg x).1)
    (fun x => differentiableOn_of_mdifferentiable (hPgt x).1)
    hT2g hT2gt hS hdecg hdecgt

/-- The corrected statement is *weaker* than the one in
`Submission/Work/FunctionalEquations/Gap.lean`: the uncorrected (`InP`-free) statement
implies it.  The converse fails; see `Submission/Work/Rigidity/Counterexample.lean`. -/
theorem homogeneousRigidityP_of_homogeneousRigidity {n : ℕ} [NeZero n] {c : ℝ}
    (h : Work.FE.HomogeneousRigidity n c) : HomogeneousRigidityP n c :=
  fun g gt hPg hPgt hT2g hT2gt hS hdecg hdecgt τ x hτ =>
    h g gt (fun x => differentiableOn_of_mdifferentiable (hPg x).1)
      (fun x => differentiableOn_of_mdifferentiable (hPgt x).1) hT2g hT2gt hS hdecg hdecgt τ x hτ

/-! ## The two corrected target theorems -/

/-- **The `E₈` case, corrected.**  `HomogeneousRigidityP 8 0` from the two weight-`4`
single-function statements with the growth hypothesis. -/
theorem homogeneousRigidityP_eight_of (hneg : SingleRigidityP 4 (-1 : ℂ) 0)
    (hpos : SingleRigidityP 4 (1 : ℂ) 0) : HomogeneousRigidityP 8 0 :=
  homogeneousRigidityP_of_singleRigidityP (n := 8) (k := 4) (c := 0)
    (fun τ => slashFactor_eight (τ : ℂ)) ⟨2, by norm_num⟩ hneg hpos

/-- **The Leech case, corrected.**  `HomogeneousRigidityP 24 1` from the two weight-`12`
single-function statements with the growth hypothesis. -/
theorem homogeneousRigidityP_twentyfour_of (hneg : SingleRigidityP 12 (-1 : ℂ) 1)
    (hpos : SingleRigidityP 12 (1 : ℂ) 1) : HomogeneousRigidityP 24 1 :=
  homogeneousRigidityP_of_singleRigidityP (n := 24) (k := 12) (c := 1)
    (fun τ => slashFactor_twentyfour (τ : ℂ)) ⟨6, by norm_num⟩ hneg hpos

end Work.Rigidity
