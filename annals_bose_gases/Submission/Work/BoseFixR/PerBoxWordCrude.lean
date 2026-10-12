import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.PerBoxWordCrudeHigh
import Submission.Work.BoseFixR.PerBoxWordCrudeLow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.PerBoxWordCrude` — the crude per-box lower bound for the sliding word

## The statement

`Work.BoseFixB1.sbWord h μ u Φ = sbKin + sbPot` (`Work.BoseFixB1.Defs`) is the
corpus's transcription of FS's per-`u` small-box energy word: the FS-faithful
kinetic word `𝒯_{B(u)}` (`Work.UBBInputs8.tBwordBInd`, FS `eq:appTB`) plus the
localised potential word `qLHSwordB` (FS `eq:HBU`).  The lemma states that this
word is bounded below, **uniformly in the particle number `n` and in the state**,
by `−C(μ²(a v)·chiMass(u) + μ(a v))·‖Φ‖²` — FS `thm:smallbox` with the
*positive* density square dropped, in the rough form FS use on the sliding band
(`final_v2.tex` l.4083: "If we use Theorem thm:smallbox and (eq:iintw1) to get
the rough estimate `H_B(4μ) ≥ −Cμ²a∫χ_B² − Cμa`").

## Why the `∃ε₀` is the whole point

The fibre (one-body) kernel of the localised word degenerates when the potential
range reaches the small-box side `ℓd`: without a *relation between `R` and the
box side* the kernel `wSmall1Pair` is not dominated by its numerator, and every
crude bound of this shape is false (see the header of
`Submission/Work/BoseFixR/CrudeWordLower.lean`, the findings in
`Submission/Work/UBBInputs8/A/exists_hlow_localised_of_bounded.lean`, and
`Submission/Work/BoseFixR/FINDING_low_particle_bound.md`).  Here the relation is
*free*: the threshold `ε₀` is existential, and shrinking it pushes the admissible
chemical potentials down, where the box side `ℓd = a·(μa³)^{−157/323}` blows up.
That is `Work.BoseFixB1.regime_sideAt_ge` (PROVED): there is `ε₀ > 0` with
`R ≤ ℓd/16` and `R ≤ ℓ·chiR0` for every admissible `μ`.

## The proof (two mechanisms, both delegated)

Split on the `χ_{B(u)}`-weighted particle count `occChi` against the threshold
`crudeThreshold v K μ … = K(μ·chiMass + 1)‖Φ‖²` of `PerBoxCrudeDefs`:

* **low occupancy** (`Work.BoseFixR.PerBoxWordCrudeLow`): below the threshold the
  pointwise fibre bound
  `|∫_y wSmall1Pair h M ℓ d u z y| ≤ (2/smallConvLower M)·chiSupAbs·chiSmallDecay M·(∫|g₀|)·χ_{B(u)}(z)`
  (PROVED as `Work.BoseFixB1B.fibre_chiB_le`, constant `∝ (a v)`) turns the
  chemical-potential term of `qLHSwordB` into `−μ·(const)(a v)·occChi`, the
  (nonnegative) pair term and the (nonnegative) kinetic word are dropped, and the
  hypothesis gives exactly `−C(μ²a·chiMass + μa)‖Φ‖²`.

* **high occupancy** (`Work.BoseFixR.PerBoxWordCrudeHigh`): above the threshold
  the *coherent* part of the state pays through the mean-field pair energy
  (FS `lm:appinteractionestimate`'s `q0`-estimate at the box projections for the
  localised kernels: the completion of squares
  `½ρ₀²∬w₂ − μρ₀∬w₁ ≥ ¼(ρ₀−μ)²∬w₁ − ½μ²∬w₁` with the *localised* masses
  `∬w_{1,B} ≈ 8π(a v)chiMass`, `∬w_{2,B} ≥ ∬w_{1,B} + ĝω(0)chiMass`), the
  *excited* part through the definitional gap payment of `sbKin`
  (`sbKin ≥ tbGapCoeff (ℓd) ε_T·cnPlusBoxInd`, FS `eq:appgapestimate`), and the
  cross terms through AM–GM against those two — no Bogoliubov layer is needed.
  The constants close because the régime forces `μ(a v)³` to be small.

The two halves are glued here with `ε₀ := min ε₀_low ε₀_high` and
`C := max C_high C_low`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

theorem PerBoxWordCrude {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          -(C * (μ ^ 2 * BoseGases.a v
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u
              + μ * BoseGases.a v))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  obtain ⟨εL, hεL, hlow⟩ := PerBoxWordCrudeLow (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εH, K, CH, hεH, hK, hCH, hhigh⟩ :=
    PerBoxWordCrudeHigh (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨CL, hCL, hLowK⟩ := hlow K hK.le
  refine ⟨min εL εH, max CH CL, lt_min hεL hεH, le_trans hCH (le_max_left _ _), ?_⟩
  intro μ hAdm n Φ u
  have hAdmH : Work.BoseBoxFix.Adm v εH μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hAdmL : Work.BoseBoxFix.Adm v εL μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  -- the nonnegative factors of the claim's coefficient
  have hV : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (BoseGases.a v)) (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hμpos : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hX : 0 ≤ μ ^ 2 * BoseGases.a v
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u
      + μ * BoseGases.a v :=
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) (le_of_lt hav)) hV)
      (mul_nonneg (le_of_lt hμpos) (le_of_lt hav))
  have hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg _
  -- gluing: if the claim holds with a smaller constant, it holds with the max
  have glue : ∀ C' : ℝ, C' ≤ max CH CL →
      -(C' * (μ ^ 2 * BoseGases.a v
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u
              + μ * BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) →
      -(max CH CL * (μ ^ 2 * BoseGases.a v
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u
              + μ * BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    intro C' hC' hb
    have hmono : (C' * (μ ^ 2 * BoseGases.a v
            * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u
          + μ * BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ (max CH CL * (μ ^ 2 * BoseGases.a v
            * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u
          + μ * BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hX) hN
    calc -(max CH CL * (μ ^ 2 * BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u
            + μ * BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        = -((max CH CL * (μ ^ 2 * BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u
            + μ * BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) :=
          neg_mul _ _
      _ ≤ -((C' * (μ ^ 2 * BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u
            + μ * BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) :=
          neg_le_neg hmono
      _ = -(C' * (μ ^ 2 * BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u
            + μ * BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
          (neg_mul _ _).symm
      _ ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := hb
  by_cases hcase : crudeThreshold v K μ (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (BoseGases.a v)) (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ)
      ≤ occChi (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
  · exact glue CH (le_max_left _ _) (hhigh μ hAdmH n Φ u hcase)
  · refine glue CL (le_max_right _ _) ?_
    exact hLowK μ hAdmL n Φ u (le_of_lt (not_le.mp hcase))

end Work.BoseFixR
