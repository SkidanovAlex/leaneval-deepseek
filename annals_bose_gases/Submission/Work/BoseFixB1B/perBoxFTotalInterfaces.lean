import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.perBoxFTotalDefs
import Submission.Work.BoseFixB1S.boxBogPortSliding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.perBoxFTotalInterfaces` — the two open interfaces of `PerBoxFTotal`

Definition-only module (no `sorry`, no target theorem), so that a prover of one of the two
`Prop`s below can import it *without* importing the target file
`Submission.Work.BoseFixB1B.perBoxFTotal_holds` (whose own theorem is a `sorry` and would make any
restatement of it trivially derivable).

The target `Work.BoseFixB1B.perBoxFTotal_holds` (= FS `thm:smallbox` at the sliding box with FS's
`F`-weight read at the **total** density `chiDensB = (∫Φ²·nCountB)/(chiMass·‖Φ‖²)`) is the
conjunction of the following two statements `InBoxTotal` and `SlidingBogPort` plus arithmetic; see
`Submission/Work/BoseFixB1B/FINDING_perBoxFTotal.md` for the full route and the list of the
corpus's *proved* ingredients (`Work.BoseFixB1S.a0A2PaymentAdm_holds`,
`Work.BoseFixB1.bqPotsplit`, `Work.BoseFixB1S.sbWord_ge_a0Main_add_boxA2`,
`Work.BoseFixB1.sbKin_ge_mu_av_cnPlus`). -/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The in-box form of `PerBoxFTotal`**: the target's inequality restricted to states that are
*normalised* and *localised in the sliding box* (`∀ᵐ x, Φ x ≠ 0 → ∀ i, x i ∈ B(u)`), i.e. the
hypotheses under which the corpus's proved sharp box estimates
(`Work.BoseFixB1S.sbWord_ge_a0Main_add_boxA2`, `Work.BoseFixB1S.a0A2PaymentAdm_holds`) apply.

The target `PerBoxFTotal` is this statement with the localisation hypothesis removed (the
normalisation is free: `PerBoxFTotal` is homogeneous of degree `2` in `Φ`).  The removal of the
localisation hypothesis is the sector/Fubini (`arity`) step: the word is additive over the
`n_A`-sectors (`Work.BoseFixB1.sbWordSectorAdditiveAdm`), each sector piece is localised on its
in-box slots by construction, and the total-density `F`-weight is compared sectorwise (Jensen plus
`F(λt) ≤ C(F(t) + μ²)`). -/
def InBoxTotal (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ c₁ C ε₀ : ℝ, 0 < c₁ ∧ 0 ≤ C ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
          (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
            ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = 1 →
        PerBoxFTotal v h R c₁ C μ n Φ u

/-- **The sliding Bogoliubov port in the spelling that `sbKin` can consume** (FS
`lm:appbogolubov`, `final_v2.tex` l.3762–3780, at the sliding box, box projections and localised
kernels): the pairing `bA2 = boxA2` plus the sliding spectral word `bSpectralCube` — which is
*exactly* the kinetic slot of `sbWord`'s `sbKin` (`Work.UBBInputs8.tBwordKinInd` at FS's
parameters) — dominate FS's credit

    −½(1+η)·D·((n+1)n/V²)·‖Φ‖²·χ_M − C·a·(μ + n/V)·n₊ − C·a·μ·‖Φ‖² ,   D := g0w0Mass.

**Why this spelling and not the corpus's frozen ones.**  `Work.BoseFixB1S.BogCoreProp` is FALSE
(`FINDING_boxBogCoreSliding_FALSE.md`, `FINDING_boxBogCoreSlidingRepaired_FALSE.md`): its mass row
`½(1+η)D((n+1)n/V²)χ_M` carries no state dependence, so it is *vacuous* under scaling
(`BoxState` is closed under scaling and all other rows are homogeneous of degree 2).  The repair is
the **`‖Φ‖²` factor** on the mass row (`·bI`).  `Work.BoseFixB1S.BogCoreBoxProp` has that factor
but uses `bSpectralBox = (ℓ³/V)·bSpectralCube`, i.e. `d⁻³` times too large
(`FINDING_boxBogCoreBox_normalisation.md`: the `(a³)⁻¹` of `tBdiagFormInd` is *already* the plain
one-body normalisation), so it is a strict weakening and cannot pay the pairing with the `sbKin`
that the frozen `sbWord` carries.  This `def` is the spelling that is both FS-faithful and
consumable by `sbWord`. -/
def SlidingBogPort (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ η C : ℝ, 0 < ε₀ ∧ 0 ≤ η ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        0 ≤ (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
              * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
              * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
                  (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
            + Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X n → ℝ) u
            + Work.BoseFixB1.bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u
            + C * (_root_.BoseGases.a v)
                * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u
            + C * (_root_.BoseGases.a v) * μ
                * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)

/-! ## The `F`-weight arithmetic

`PerBoxFTotal`'s mean-field slot is `c₁·W·F(chiDens)·‖Φ‖²` where `F = Work.SmallBoxSliding.psiWeight 1 μ`
and `chiDens = S/(chiMass·‖Φ‖²)` is the *state's own* `χ²`-density, whereas the corpus's proved sharp
box estimate produces the mean-field square `¼(ρ₀−μ)²·M₁` at the **box** density `ρ₀ = S/boxMass`.
Since `χ̂ := chiMass/boxMass` is a *fixed* datum, `chiDens = ρ₀/χ̂` and the two densities differ by a
constant.  The following pure-real comparison is the whole of that step; it is uniform in `t` (the
`(t−μ)²`-term dominates at large `t`, and the `μ²`-slot covers the middle), which is what the free
constants `c₁, C` need. -/

/-- **The `F`-weight comparison.**  For `0 < μ`, `c > 0` and every `t ≥ 0`,

    F(c·t) ≤ (4·max c 1)·(¼(t−μ)² + μ²) ,   F = psiWeight 1 μ ,

built from the corpus's proved `Work.BoseFixB1B.psiWeight_le_mu_add`
(`F(u) ≤ μ·u + μ²`, i.e. `μu + μ² − F(u) = 4μu/(1+u/μ)`).

In the application `c = boxMass/chiMass` and `t = S/boxMass`, so this bounds the target's
mean-field slot `c₁·F(chiDens)` by a multiple of the corpus's sharp square `¼(ρ₀−μ)²` plus the
`μ²`-slot that the target's free error constant `C·(μ²a·Γ_B·χ_M + μa)` covers.  The corpus's
cut-off comparison `Work.BoseFixB1B.psiWeight_le_mul_add` (`F(t) ≤ (8C+8)(F(s)+μ²)` for
`t ≤ Cs`) serves the same purpose when the intermediate density `s` is the sector density. -/
lemma psiWeight_density_le {μ c t : ℝ} (hμ : 0 < μ) (hc : 0 < c) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ (c * t)
      ≤ (4 * max c 1) * ((1 / 4) * (t - μ) ^ 2 + μ ^ 2) := by
  have hK1 : (1 : ℝ) ≤ max c 1 := le_max_right _ _
  have hKc : c ≤ max c 1 := le_max_left _ _
  have hKpos : (0 : ℝ) < max c 1 := lt_of_lt_of_le one_pos hK1
  have hstep1 : Work.SmallBoxSliding.psiWeight 1 μ (c * t)
      ≤ μ * (c * t + μ) :=
    Work.BoseFixB1B.psiWeight_le_mu_add hμ (mul_nonneg hc.le ht)
  have hstep2 : μ * (c * t + μ) ≤ max c 1 * (μ * (t + μ)) := by
    have h1 : c * t + μ ≤ max c 1 * (t + μ) := by
      have h2 : c * t ≤ max c 1 * t := mul_le_mul_of_nonneg_right hKc ht
      have h3 : μ ≤ max c 1 * μ := by nlinarith [hK1, hμ]
      linarith
    have h4 := mul_le_mul_of_nonneg_left h1 hμ.le
    linarith [h4]
  have hkey : μ * (t + μ) ≤ (t - μ) ^ 2 + 4 * μ ^ 2 := by
    nlinarith [sq_nonneg (t - 3 * μ / 2), sq_nonneg μ]
  have hfin : max c 1 * (μ * (t + μ)) ≤ max c 1 * ((t - μ) ^ 2 + 4 * μ ^ 2) :=
    mul_le_mul_of_nonneg_left hkey hKpos.le
  have htarget : max c 1 * ((t - μ) ^ 2 + 4 * μ ^ 2)
      = (4 * max c 1) * ((1 / 4) * (t - μ) ^ 2 + μ ^ 2) := by ring
  linarith [hstep1, hstep2, hfin, htarget.le, htarget.symm.le]


end Work.BoseFixB1B
