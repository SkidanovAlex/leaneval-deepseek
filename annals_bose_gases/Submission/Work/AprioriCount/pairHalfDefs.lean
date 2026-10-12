import ChallengeDeps
import Submission.Work.AprioriCount.fibMass_le_chiCount
import Submission.Work.AprioriCount.flatLeChi
import Submission.Work.BoseFixB1.WB.kb_window
import Submission.Work.BoseFixB1B.boxFormB_budgetAlt
import Submission.Work.BoseFixB1B.integrableOn_oneBody_wPair
import Submission.Work.BoseFixB1B.integrableOn_pair_wPair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.AprioriCount.pairHalfDefs` — two named atoms and the pure-real ledger of a
# **new route to the node** (`ChiDysonBound`)

The node `Work.AprioriCount.ChiDysonBound v h R` is, on disk, pinned to the two caps
`ChiCountCap + EnergyFloor` (`dysonChiBound_of_caps` and the converse), and its recorded reductions
are `(E) = CrudeDyson` and `CollectedUnifCube`.  This module records a *third* route, through two
new atoms that are *cleaner* than the ones on the disk:

* **`PairHalfRigidity`** — the **pair-half rigidity** of low box states:

      (1/2)·μ·M₁(Φ) − ε·μ²(a v)ℓ³·‖Φ‖²  ≤  kinFormB + pairPartB        (for every `ε > 0`,
                                                                            some `ε₀(ε)`),

  i.e. `K + P ≥ (1/2)μM₁` up to an arbitrarily small fraction of the LHY scale `μ²(a v)ℓ³`.  In the
  word language (`wordB = K + P − μM₁`) this is the **sharp box bound**

      wordB ≥ −(1/2)·μ·M₁ − ε·μ²(a v)ℓ³‖Φ‖² ,

  whose constant is the *state's* chemical mass rather than the universal `4π(a v)μ²ℓ³` of the
  corpus's `BoxBoundB`/`LHYBoxB`; at the flat state (`n = μℓ³`) it is an **equality**.  The
  correction `ε` is unavoidable: the flat family `n = μℓ³(1−δ)` is low as soon as
  `δ ≤ √(J√(μ(a v)³))`, and there `wordB + μM₁/2 = K − 4πaμ²ℓ³·δ(1−δ)`, so the fixed-`ε`-free form
  (`K + P ≥ μM₁/2` exactly) is **false**.

* **`CountCap`** — the (one-sided, constant-free) **count cap** `n ≤ C·μℓ³` on low states.  This is
  *weaker* than every count window on disk (`NodeB1B`, `LowStateCountCapB1`, `AprioriUnif`), which
  are two-sided and sharp.

The route is assembled by `pairHalfArith` below (pure real) plus the *proved* rows
`fibMass_ge_chiSq` (the χ²-fibre lower bound, with fraction `κ₁ = C_Lip·R/ℓ`),
`chiSqMass_lowB_floorSharp` (the sharp χ²-mass floor, constant `3/8`) and
`chiCount_le_chiSup_mul_integral` (the trivial bound `X ≤ chiSup·n·‖Φ‖²`, giving `κ₂ = chiSup·C`
from `CountCap`); the assembly in the corpus's vocabulary is filed separately
(`AprioriCount/chiDysonBound_of_pairHalfRigidity`).

**Constant bookkeeping of the assembly** (this is the delicate part).  `pairHalfArith` needs
`c·κ₂² ≤ 4πκ₀ − 4πκ₁κ₂ − ε` with a *positive* right-hand side, i.e. `κ₀ > κ₁κ₂`.  Here

* `κ₂ = chiSup·C` with `C` the *given* (fixed, possibly huge) `CountCap` constant — so `κ₂` is a
  fixed number of `v`;
* `κ₁ = C_Lip·R/ℓ` with `C_Lip` the *fixed* Lipschitz constant of `χ` — and `R/ℓ` can be made
  **arbitrarily small** by shrinking the diluteness threshold, because `Work.BoseBox.sideAt_large`
  (equivalently `sideAt_eq_rpow`, `ℓ = (a v)(μ(a v)³)^{−163/323}`) gives `R ≤ ℓ·r` for every
  prescribed `r > 0` once `ε₀` is small enough.

So **do not** bound `κ₁` by the crude regime `R ≤ ℓ·chiR0` (which would produce the spurious
absolute condition `chiSup·C < 3/(16 C_Lip chiR0)`): choose `r` *after* `C` and `chiSup` are known,
with `C_Lip·r·chiSup·C < 3/8`, and then take `ε₀` below the threshold of `sideAt_large` at that `r`.
Likewise `κ₀ ≥ (3/8)(1−J√(μ(a v)³)) − κ₁κ₂ ≥ 9/32` for small `ε₀` (using `J√(μ(a v)³) ≤ KB³√(μ(a v)³)
= (μ(a v)³)^{287/646} ≤ 1/4`), so `4πκ₀ − 4πκ₁κ₂ − ε ≥ 4π·(9/32) − small − ε > 0` for `ε = 1/2`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.AprioriCount

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `potBr`-mass of a state**: `M₁ = ∫_{abox} Φ² Σᵢ potBr ℓ (g₀) 0 (xᵢ)`, the one-body
(chemical) mass in the currency of the *proved* fibre rows `fibMass_le_chiSq` / `fibMass_ge_chiSq`
(which is also the currency of `Work.AprioriCount.chemMassB`, via the fibre identity
`potBr ℓ g 0 a = ∫_y wLoc ℓ g 0 a y`). -/
noncomputable def potMass {n : ℕ} (ℓ : ℝ) (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
    * ∑ i : Fin n, Work.BoseBox.potBr ℓ (Submission.BoseGases.g0 v h) 0 (x i)

/-- **The pair-half rigidity of low box states** (the node's third named atom). -/
def PairHalfRigidity (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ J : ℝ, Work.UBB.lhyC ≤ J →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n (Φ : Submission.BoseGases.X n → ℝ) →
            (1 / 2) * μ * potMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v h
                (Φ : Submission.BoseGases.X n → ℝ)
              - ε * μ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
                  (Φ : Submission.BoseGases.X n → ℝ)
                + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Φ : Submission.BoseGases.X n → ℝ)

/-- **The (one-sided) count cap on low box states** (the node's fourth named atom, weaker than
every count window on disk).

⚠ **This `normB`-free form is FALSE as stated** and is kept only for the record.  `BoxState`
carries *no* support condition (`Work.BoseKinLoc.Defs`), and `boxFormB`, `sqNormB` and `chiCount`
all see only the box restriction of the state, so a smooth symmetric state supported *outside*
`abox n ℓ` has `wordB = 0` and `normB = 0`, hence satisfies `IsLowB` (`0 ≤ ℓ³·Theta·0`) for
*every* `n` — with no bound on `n`.  Use **`CountCapPos`** below, which is the form the corpus
itself uses everywhere (`Work.BoseBoxFix.NodeB1B`, `LowStateCountCapB1` all carry
`0 < normB v μ n Φ →`).  -/
def CountCap (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ J : ℝ, Work.UBB.lhyC ≤ J →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n (Φ : Submission.BoseGases.X n → ℝ) →
            (n : ℝ) ≤ C * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3

/-- **The (one-sided) count cap on low box states, with the corpus's nondegeneracy hypothesis
`0 < normB`** — the correct form (see the warning on `CountCap`).  Every count window on disk
(`NodeB1B`, `LowStateCountCapB1`, `AprioriUnif`) carries this hypothesis and gives this cap
(their two-sided sharp window `|n − μℓ³| ≤ C·nWindow` with `nWindow/μℓ³ → 0`). -/
def CountCapPos (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ J : ℝ, Work.UBB.lhyC ≤ J →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n (Φ : Submission.BoseGases.X n → ℝ) →
            (n : ℝ) ≤ C * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3

/-- **The pure-real ledger of the route.**  If

* the energy dominates half the chemical mass up to the LHY fraction `ε` (`hrow`),
* the χ²-mass is at least `κ₀` times the LHY scale (`hfloor`),
* the χ-mass is at most `κ₂` times the density scale (`hχb`),

then the node's inequality holds with the *explicit* constant `c`, as soon as
`c κ₂² ≤ 4πκ₀ − 4πκ₁κ₂ − ε`:

    c·a·X² ≤ (K + P)·ℓ³·‖Φ‖² .

(`κ₁` is the fibre row's Lipschitz fraction `C R/ℓ`; `a = a v`.)  Both sides are homogeneous, so
the degenerate case `‖Φ‖ = 0` is covered. -/
theorem pairHalfArith {a ℓ μ I X S2 KP κ₀ κ₁ κ₂ c ε : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hℓ : 0 < ℓ) (hμ : 0 < μ) (hI : 0 ≤ I) (hX : 0 ≤ X)
    (hκ₀ : 0 ≤ κ₀) (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (hε : 0 ≤ ε)
    (hrow : 4 * Real.pi * a * μ * (S2 - κ₁ * X) - ε * μ ^ 2 * a * ℓ ^ 3 * I ≤ KP)
    (hfloor : κ₀ * μ * ℓ ^ 3 * I ≤ S2)
    (hχb : X ≤ κ₂ * μ * ℓ ^ 3 * I)
    (hcon : c * κ₂ ^ 2 ≤ 4 * Real.pi * κ₀ - 4 * Real.pi * κ₁ * κ₂ - ε) :
    c * a * X ^ 2 ≤ KP * ℓ ^ 3 * I := by
  set Z : ℝ := a * (μ ^ 2 * ℓ ^ 3 * I) * (ℓ ^ 3 * I) with hZ
  have hZ0 : (0 : ℝ) ≤ Z := by rw [hZ]; positivity
  -- (1) the χ-bound and the χ²-floor give the energy at the explicit constant
  have hE : a * (μ ^ 2 * ℓ ^ 3 * I) * (4 * Real.pi * κ₀ - 4 * Real.pi * κ₁ * κ₂ - ε) ≤ KP := by
    have hkX : κ₁ * X ≤ κ₁ * (κ₂ * μ * ℓ ^ 3 * I) := mul_le_mul_of_nonneg_left hχb hκ₁
    have harg : κ₀ * μ * ℓ ^ 3 * I - κ₁ * (κ₂ * μ * ℓ ^ 3 * I) ≤ S2 - κ₁ * X := by linarith
    have hmul := mul_le_mul_of_nonneg_left harg (by positivity : (0 : ℝ) ≤ 4 * Real.pi * a * μ)
    have hraw : 4 * Real.pi * a * μ * (κ₀ * μ * ℓ ^ 3 * I - κ₁ * (κ₂ * μ * ℓ ^ 3 * I))
        - ε * μ ^ 2 * a * ℓ ^ 3 * I ≤ KP := by linarith [hmul, hrow]
    have e : a * (μ ^ 2 * ℓ ^ 3 * I) * (4 * Real.pi * κ₀ - 4 * Real.pi * κ₁ * κ₂ - ε)
        = 4 * Real.pi * a * μ * (κ₀ * μ * ℓ ^ 3 * I - κ₁ * (κ₂ * μ * ℓ ^ 3 * I))
          - ε * μ ^ 2 * a * ℓ ^ 3 * I := by ring
    rw [e]; exact hraw
  -- (2) the χ-mass bound
  have hkey : c * a * X ^ 2 ≤ Z * (c * κ₂ ^ 2) := by
    have hX2 : X ^ 2 ≤ (κ₂ * μ * ℓ ^ 3 * I) ^ 2 := pow_le_pow_left₀ hX hχb 2
    have hca : (0 : ℝ) ≤ c * a := mul_nonneg hc ha
    have h := mul_le_mul_of_nonneg_left hX2 hca
    have e : c * a * (κ₂ * μ * ℓ ^ 3 * I) ^ 2 = Z * (c * κ₂ ^ 2) := by rw [hZ]; ring
    rw [e] at h; exact h
  -- (3) the constant comparison
  have hmid : Z * (c * κ₂ ^ 2) ≤ Z * (4 * Real.pi * κ₀ - 4 * Real.pi * κ₁ * κ₂ - ε) :=
    mul_le_mul_of_nonneg_left hcon hZ0
  -- (4) the energy bound, multiplied by `ℓ³I ≥ 0`
  have hend : Z * (4 * Real.pi * κ₀ - 4 * Real.pi * κ₁ * κ₂ - ε) ≤ KP * ℓ ^ 3 * I := by
    have hLI : (0 : ℝ) ≤ ℓ ^ 3 * I := by positivity
    have h := mul_le_mul_of_nonneg_right hE hLI
    have e : a * (μ ^ 2 * ℓ ^ 3 * I) * (4 * Real.pi * κ₀ - 4 * Real.pi * κ₁ * κ₂ - ε) * (ℓ ^ 3 * I)
        = Z * (4 * Real.pi * κ₀ - 4 * Real.pi * κ₁ * κ₂ - ε) := by rw [hZ]; ring
    rw [e] at h
    simpa only [mul_assoc] using h
  exact le_trans hkey (le_trans hmid hend)

end Work.AprioriCount
