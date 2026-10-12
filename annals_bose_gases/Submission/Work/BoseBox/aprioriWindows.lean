import ChallengeDeps
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBox.B2Reduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox

/-! # FINDING FILE (SKELETON) — the requested node is **not** FS's `eq:apriorinn+`

The theorem `aprioriWindows` below is kept verbatim (it is the requested statement); it is **not**
proved, and it should **not** be proved as written, because its *second conjunct* is strictly
stronger than the paper's theorem that it claims to render.

## The defect: the sharp coefficient `1` in front of the window

FS `thm:aprioribounds`/`thm:aprioriHLambda` (App. `SmallBoxes`) state `eq:apriorinn+` with a
**universal constant** `C` in front of the window:

    ⟨Ψ, n₊Ψ⟩ ≤ C·μℓ³K_B³K_ℓ²(μa³)^{1/2} = C·nPlusWindow·‖Ψ‖²      (C a universal constant > 0).

In the corpus the window is `nPlusWindow (paramsAt μ a) μ a = (μa³)^{-51/646)` — **with no
constant in it** (`Windows.nPlusWindow_paramsAt`).  `NodeB1`'s second conjunct therefore asks for
FS's window at the *sharp* coefficient `1` (the `+ 1` is `1 + o(1)` relative to the window as
`μa³ → 0`), i.e. `C = 1 + 1/nPlusWindow`.

## What FS's own chain delivers

FS prove `eq:apriorinn+` from `eq:appsliding` (`H_Λ(μ) ≥ (b/2ℓ²)ΣᵢQ_{Λ,i} + ∫H_{B(u)}`) together
with the large-box a-priori bound `eq:aprioriHLambda`
(`H_Λ(μ) ≥ -4πμ²aℓ³(1 + C'K_B³(μa³)^{1/2})`) and the low condition `eq:aprioriPsi`
(`⟨H_Λ(μ)⟩ ≤ -4πμ²aℓ³(1 − J(μa³)^{1/2})`, `J ≤ K_B³`), which gives

    (b/2ℓ²)·⟨n₊⟩ ≤ 4πμ²aℓ³(J + C'K_B³)(μa³)^{1/2},

i.e. the window only with the coefficient `(2ℓ²/b)·4πμ²aℓ³(J + C'K_B³)√(μa³)/nPlusWindow`.  In
this corpus that chain is machine-checked as `Work.UBB.Apriori.cnPlus_le_window_of_low`, whose
statement is the `J + K_B³` instance of exactly this inequality (its `hslide` hypothesis is FS
`eq:BSsliding2` + `thm:aprioriHLambda` in the corpus's rendering, where the error term
`4πρ²aL³K_B³(ρa³)^{1/2}` carries coefficient `1`).  Its coefficient relative to the window is
computed by `aprioriWindowCoefficient` below:

    (2ℓ²/b)·4πμ²aℓ³(J + K_B³)√(μa³) = (8π/b)(1 + J/K_B³)·nPlusWindow,

hence — since `J > 0`, `K_B³ > 0`, and `b = bValue = 1/16` is *fixed* by `paramsAt` while
`ParamsOK.bsmall` even *forces* `b ≤ 1/16` — a coefficient `≥ 8π/b = 128π > 384` in front of
`nPlusWindow`, never `1`.  (`eight_pi_div_bValue`, `paramsAt_b`, `bValue_eq` below.)

So the requested node is a `≳ 384×` strengthening of FS `eq:apriorinn+`: it does not say what was
meant.  The factor is not an artifact of FS's bookkeeping — it is the factor that `b` contributes
to the *only* budget the a-priori proof has: the word itself charges each excited particle the gap
`(½ε_T(1+π⁻²)⁻¹(dℓ)⁻² + b/ℓ²)cnPlusBox` (`Word.tKinWord`), so the low condition
`word ≤ ℓ³Θ(a v,J,μ)‖Φ‖²` against the threshold room `4πaμ²ℓ³(J + CK_B³)√(μa³)` admits
`≈ (2ℓ²/b)·4πμ²aℓ³(J + K_B³)√(μa³) = (8π/b)(1 + J/K_B³)·nPlusWindow` excited particles at the
bare gap cost — i.e. `≳ 384·nPlusWindow`, not `nPlusWindow`.  (Concretely: a state carrying
`k` particles in low-momentum modes — where the `tauSymb`-half of `tKinWord` is cut off at
`(2sℓ)^{-1}` and the pair-word is unchanged to leading order for a density modulation orthogonal
to `χ²`, which can be arranged by symmetry — is low for `k` up to that budget.)

## The corrected statement (what the requester wants, and all the §6 consumer uses)

    cnPlus ℓ Φ ≤ C₁ · nPlusWindow (paramsAt μ (a v)) μ (a v) · ‖Φ‖²      (C₁ free, as in the
    chapter's own `Work.BoseBox.B2AprioriWindow`, `Work.BoseBox.AprioriNPlusBox`,
    `b2AprioriWindow_holds`, and as `B2AprioriWindow_of_NodeB1KB` immediately converts the sharp
    form into).

That is FS's `eq:apriorinn+`.  It is *not* available in this workspace either: FS's route runs
through App. `SmallBoxes` (`thm:smallbox`, `thm:aprioriHLambda`) and Bratteli–Solovej
Thm 3.10 (`eq:BSsliding2`), and the corpus's renderings of the sliding inequality are refuted
(`Work.UBBInputs9.not_tBLocalisation*`, `Work.OneBodyPay.not_BSslidingKinAllPayments*`), so the
a-priori block is open — but with a free constant it is at least correctly stated. -/

/-- The healing-length identity at the level of the window: `μa·ℓ² = K_ℓ²` for the box side
`ℓ = boxSide P μ a = K_ℓ(μa)^{-1/2}`. -/
lemma mu_a_boxSide_sq (P : FSParams) {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    μ * a * boxSide P μ a ^ 2 = P.Kl ^ 2 := by
  have hμa : 0 < μ * a := mul_pos hμ ha
  have h1 : ((μ * a) ^ (-(1 / 2 : ℝ))) ^ 2 = (μ * a) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμa.le]
    norm_num
  have h2 : (μ * a) ^ (-(1 : ℝ)) = (μ * a)⁻¹ := Real.rpow_neg_one _
  dsimp [boxSide]
  rw [mul_pow, h1, h2]
  field_simp

/-- **The coefficient of FS's a-priori `n₊` window as delivered by FS's own chain.**  The
inequality `cnPlus ≤ (2ℓ²/b)·4πμ²aℓ³(J + K_B³)√(μa³)` (FS `eq:appsliding` + `eq:aprioriHLambda`
+ `eq:aprioriPsi` with `J ≤ K_B³`, machine-checked as `Work.UBB.Apriori.cnPlus_le_window_of_low`)
equals `(8π/b)(1 + J/K_B³)·nPlusWindow` at FS's decoupled parameters — a coefficient
`≥ 8π/b = 128π > 384`, not `1`. -/
lemma aprioriWindowCoefficient {μ a J : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    (2 * sideAt μ a ^ 2 / (paramsAt μ a).b)
        * (4 * Real.pi * μ ^ 2 * a * sideAt μ a ^ 3
            * (J + (paramsAt μ a).KB ^ 3) * (μ * a ^ 3) ^ (1 / 2 : ℝ))
      = (8 * Real.pi / (paramsAt μ a).b) * (J + (paramsAt μ a).KB ^ 3)
          * ((paramsAt μ a).Kl ^ 2 * μ * sideAt μ a ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ)) := by
  have hsq : μ * a * sideAt μ a ^ 2 = (paramsAt μ a).Kl ^ 2 := by
    dsimp [sideAt]
    exact mu_a_boxSide_sq (paramsAt μ a) hμ ha
  have h5 : μ ^ 2 * a * sideAt μ a ^ 5 = μ * sideAt μ a ^ 3 * (paramsAt μ a).Kl ^ 2 := by
    calc μ ^ 2 * a * sideAt μ a ^ 5
        = (μ * a * sideAt μ a ^ 2) * (μ * sideAt μ a ^ 3) := by ring
      _ = (paramsAt μ a).Kl ^ 2 * (μ * sideAt μ a ^ 3) := by rw [hsq]
      _ = μ * sideAt μ a ^ 3 * (paramsAt μ a).Kl ^ 2 := by ring
  rw [show (2 * sideAt μ a ^ 2 / (paramsAt μ a).b)
        * (4 * Real.pi * μ ^ 2 * a * sideAt μ a ^ 3
            * (J + (paramsAt μ a).KB ^ 3) * (μ * a ^ 3) ^ (1 / 2 : ℝ))
      = (8 * Real.pi / (paramsAt μ a).b) * (μ ^ 2 * a * sideAt μ a ^ 5)
          * (J + (paramsAt μ a).KB ^ 3) * (μ * a ^ 3) ^ (1 / 2 : ℝ) by ring]
  rw [h5]
  ring

/-- The window in factored form: `nPlusWindow = K_B³·(K_ℓ²μℓ³(μa³)^{1/2})`. -/
lemma nPlusWindow_eq_coeff {μ a : ℝ} :
    nPlusWindow (paramsAt μ a) μ a
      = (paramsAt μ a).KB ^ 3 * ((paramsAt μ a).Kl ^ 2 * μ * sideAt μ a ^ 3
          * (μ * a ^ 3) ^ (1 / 2 : ℝ)) := by
  rw [nPlusWindow]
  dsimp [sideAt, boxSide]
  ring

/-- The gap coefficient `b` of FS `eq:DefT` is fixed at `1/16` by the corpus's parameter
choice (`fsParams`), hence the coefficient `8π/b = 128π` of FS's a-priori chain is fixed. -/
lemma paramsAt_b {μ a : ℝ} : (paramsAt μ a).b = bValue := rfl

lemma bValue_eq : bValue = 1 / 16 := rfl

lemma eight_pi_div_bValue : (8 * Real.pi) / bValue = 128 * Real.pi := by
  rw [bValue]; ring

lemma eight_pi_div_bValue_gt : (384 : ℝ) < 8 * Real.pi / bValue := by
  rw [eight_pi_div_bValue]
  nlinarith [Real.pi_gt_three]

/-- **`B1` (repaired): FS §5 `thm:aprioribounds` + App. `thm:aprioriHLambda`.**

`Work.BoseBox.NodeB1 v h J` (`Submission.Work.BoseBox.Nodes`) now carries FS's full setting: there
are `C₁ ≥ 0` and `ε₀ > 0` such that for every diluteness `μa³ ≤ ε₀` with `ParamsOK` and FS's
a-priori constraint `J ≤ K_B³`, every particle number `n` and every *low* box state
`Φ : CSBox n (sideAt μ (a v))` (`IsLow`, FS `eq:aprioriPsi` at threshold `J`):

* `|n − μℓ³| ≤ C₁(1 + nWindow)` — FS `eq:apriorinn+`, first conjunct (`ℓ = sideAt μ (a v)`);
* `cnPlus ℓ Φ ≤ (nPlusWindow + 1)·‖Φ‖²` — second conjunct
  (`Work.BoseBox.Windows.nPlusWindow_paramsAt : nPlusWindow = (μa³)^{-51/646}`).

**Correction history**: the first rendering had *no* diluteness restriction (`∀ μ` with only
`ParamsOK`) and no upper bound on `J`; a prover refuted it (`nodeB1_holds.lean`, now stale:
diluteness `μa³ = 1` is admissible, `nPlusWindow = 1` there, and the three-particle mean-free state
`x ↦ x₀₁x₁₁x₂₁` with `cnPlus = 3‖·‖²` is low for large `J` while violating the window).  A reviewer
confirmed the repaired node: `J ≤ K_B³ = (μa³)^{-18/323}` forces `J√(μa³) < 1`, so `IsLow` is
genuinely restrictive in the whole admissible range.

Content: the a-priori block of the paper (FS Appendix `SmallBoxes`: `thm:smallbox` for the small
boxes of side `ℓd` + Bratteli–Solovej Thm 3.10 at `eq:BSlidingassp`), and the only place the paper's
`∫v` estimate (`eq:dvapriori`) is needed.  It is an input of the §6 replacement `NodeB2g` (via
`Work.BoseBox.B2AprioriWindow`, immediate from this node), which uses it to place the Lieb–Solovej
window at `[0,𝓜]`.  The corpus's routes at the *coupled* parameters are the blocked/refuted
residuals of `Work.UBBInputs{7,8,9,10}`; the decoupled re-instantiation is the task (the small-box
chain `SmallBox*`/`BlockBound4`/`SmallBoxSliding`/`LocRepoint` is the material to re-point).  Both
audit tests pass. -/
theorem aprioriWindows {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) : Work.BoseBox.NodeB1 v h J := by sorry

end Work.BoseBox
