import ChallengeDeps
import Submission.Work.BoseFixR.Canon
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/HonestFamily.lean` — FS's honest realisation as one named family

The three residuals of `Defs.lean` (`RB4box`, `RB5`, `RB67`) must be proved at **one
common family** `D : ℝ → KzDatum`, because `Assembly.nodeRestrictedB_of_residuals`
combines them at a single `D`.

The helper `Canon.lean`'s `KzCanonFam v h Mode F T fc` *fixes* `Mode`, `F`, `T`, `fc`
across `μ`.  That is an idealisation: FS's mode lattice is the dual lattice of the
box of side `ℓ(μ) = sideAt μ (a v)`, so both the mode set and the physical momenta
`kmom` depend on `μ` (`Work.BoseK15.Defs`'s dual-lattice condition
`kmom i = ℓ⁻¹ • vec n`).  The residual *defs* are already family-generic
(`KzDatum.Mode` is a field), so a μ-dependent `Mode` is expressible — but a *named*
honest family is needed so that the three obligations refer to the same objects.

`KzHonestFam` is that family, built exactly from the honest box data that BoseB4 /
BoseK15 supply:

* `Mode μ` — the mode lattice of the box of side `ℓ(μ)` (any `Mode : ℝ → Type`);
* `kmom μ` — the physical momenta `(2π/ℓ(μ))ℤ³`, i.e. `F.kmom` of the honest
  realisation (`hkmom`: odd under negation);
* `F μ = Work.BoseK15.boxFockDataBox (ell v μ) (kmom μ) …` — B4's second-quantised
  mode system `a_k = annOf (f μ k)`, with the box Gram data `hf`;
* `T μ = Work.BoseK15.tildeDataBox (ell v μ) …` — the θ-modes, `N = totNumOp`;
* `E μ = KzEnvFs v h μ (F μ) fc` — FS's scalars (`FSParamsView`) and the pinned §4
  kernels;
* `gHat0 = 8π(a v)`.

## The view at this family, and what it costs

`(KzHonestFam … μ).view v h μ` is `RView v h μ (F μ) (T μ) (KzEnvFs …) (8πa)`.  Its
22 conjuncts reduce to **four obligations**, all of which are other nodes' or the
honest model's (none is provable from `FockData`/`TildeData` alone):

1. `Nonempty (FSParamsView (KzEnvFs v h μ (F μ) fc))` — proved in this directory
   (`FSParamsViewCanon.lean`) from `ParamsOK`/`Adm`;
2. the scalar/kernel pins — `rfl` by construction of `KzEnvFs`, except the two
   density relations `E.A = τ + E.rho·E.W1`, `E.B = E.rho·E.W1`, which need
   `(KzEnvFs …).rho = μ` (`Q3Env.rho = rhoZ (√(μℓ³)) ℓ = μ`, from `hμ : 0 < μ`,
   `hℓ : 0 < ell v μ`);
3. `∀ f, ⟨f, F.nPlus f⟩ ≤ ⟨f, T.N f⟩` — the honest Bessel inequality
   (`Work.BoseB4.bessel_le_totNumOp_v2` applied to the orthonormal box χ-modes;
   `N = totNumOp m`);
4. `∃ K₀ b₀, 0 ≤ K₀ ∧ 0 < b₀ ∧ b₀ ≤ E.b ∧ ∀ ρ ∈ CloseCond, Q3Kernel' K₀ (F μ) (T μ) (KzEnvAt E ρ)`
   — BoseK15's obligation, `Work.BoseK15.Q3Kernel'_of_box` from `K15Input` +
   `FSParamsView` at `t ≤ t₀` (with the box-model equations and FS's low-momentum
   positivity of `Ŵ₁`).

Both the window inhabitation `hwin` that `RB4box` demands and the honest
`nPlus ≤ N` are consequences of 3 and of B4's model:
`Work.BoseFixR.vac_killed` + `Work.BoseB7A.TildeData.window_nonempty_of_vac`
(`HonestVacuum.lean`, `WindowInhabited.lean`).

See `FINDING_rb4box_uniform_false.md` §3 and `STATUS.md` for why a single fixed
`Mode` cannot be used here, and `RB4BOX_PLAN.md`/`RB5_PLAN.md` for the routes of
the two remaining FS chapters at this family.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **FS's honest realisation**, one `KzDatum` per chemical potential, with the
mode lattice allowed to depend on `μ` (FS's `(2π/ℓ(μ))ℤ³`). -/
noncomputable def KzHonestFam (v : ℝ³ → ℝ) (h : ScatSol v) (fc : LowCut)
    (Mode : ℝ → Type) [(μ : ℝ) → AddCommGroup (Mode μ)] [(μ : ℝ) → Fintype (Mode μ)]
    [(μ : ℝ) → DecidableEq (Mode μ)]
    (kmom : ∀ μ, Mode μ → ℝ³) (hkmom : ∀ μ (i : Mode μ), kmom μ (-i) = -kmom μ i)
    (m : ℕ) (f : ∀ μ, Mode μ → Fin m → ℝ)
    (hf : ∀ μ (i j : Mode μ), Work.BoseB4.gram (f μ i) (f μ j)
      = Work.BoseB7.ccrKernel (ell v μ) Work.BoseK15.corpusBox.hatChiSq
          Work.BoseK15.corpusBox.hatChi (kmom μ i) (kmom μ j))
    (g : ∀ μ, Mode μ → Fin m → ℝ)
    (hg : ∀ μ (s t : Mode μ), s ≠ 0 → t ≠ 0 →
      Work.BoseB4.gram (g μ s) (g μ t) = if s = t then 1 else 0) :
    ℝ → KzDatum :=
  fun μ =>
    let F μ := Work.BoseK15.boxFockDataBox (ell v μ) (kmom μ) (hkmom μ) m (f μ) (hf μ)
    { Mode := Mode μ
      instAddCommGroup := (inferInstance : AddCommGroup (Mode μ))
      instFintype := (inferInstance : Fintype (Mode μ))
      instDecidableEq := (inferInstance : DecidableEq (Mode μ))
      F := F μ
      E := KzEnvFs v h μ (F μ) fc
      gHat0 := 8 * π * a v
      T := Work.BoseK15.tildeDataBox (ell v μ) (kmom μ) (hkmom μ) m (f μ) (g μ) (hf μ) (hg μ) }

/-- **The honest family with the χ-mode family orthonormal on the excited modes.**
This is the family at which `RB4box` — whose conclusion *includes* the view, hence
FS's `∀ φ, ⟨φ, F.nPlus φ⟩ ≤ ⟨φ, T.N φ⟩` — can be stated: with only the Gram identity
`hf` (`gram (f μ i) (f μ j) = ccrKernel (ell v μ) …`) the χ-modes may be collinear
(e.g. `kmom ≡ 0`, all `f μ i` equal), and then `F.nPlus` is *not* dominated by
`T.N = totNumOp m`; the child of `RB4boxHonestFam` refuted exactly that case
(`Submission/Work/BoseFixR/RB4boxHonestFamFalse.lean`: `Mode μ = (ZMod 2)²`,
`f μ i = √c₀ • e₀`, `F.nPlus φ = 3c₀ • φ` vs `T.N φ = φ`).  For FS's box data the
excited χ-modes `Q e^{ikx}χ_Λ` *are* orthonormal, which is what makes the honest
instance satisfy the conjunct (`Work.BoseB4.bessel_le_totNumOp_v2`).

`RB5`/`RB67` do not need this argument: for them the view is an *antecedent*. -/
noncomputable def KzHonestFamOrth (v : ℝ³ → ℝ) (h : ScatSol v) (fc : LowCut)
    (Mode : ℝ → Type) [(μ : ℝ) → AddCommGroup (Mode μ)] [(μ : ℝ) → Fintype (Mode μ)]
    [(μ : ℝ) → DecidableEq (Mode μ)]
    (kmom : ∀ μ, Mode μ → ℝ³) (hkmom : ∀ μ (i : Mode μ), kmom μ (-i) = -kmom μ i)
    (m : ℕ) (f : ∀ μ, Mode μ → Fin m → ℝ)
    (hf : ∀ μ (i j : Mode μ), Work.BoseB4.gram (f μ i) (f μ j)
      = Work.BoseB7.ccrKernel (ell v μ) Work.BoseK15.corpusBox.hatChiSq
          Work.BoseK15.corpusBox.hatChi (kmom μ i) (kmom μ j))
    (hf_orth : ∀ μ (i j : Mode μ), i ≠ 0 → j ≠ 0 →
      Work.BoseB4.gram (f μ i) (f μ j) = if i = j then 1 else 0)
    (g : ∀ μ, Mode μ → Fin m → ℝ)
    (hg : ∀ μ (s t : Mode μ), s ≠ 0 → t ≠ 0 →
      Work.BoseB4.gram (g μ s) (g μ t) = if s = t then 1 else 0) :
    ℝ → KzDatum :=
  KzHonestFam v h fc Mode kmom hkmom m f hf g hg

end Work.BoseFixR
