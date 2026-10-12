import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.frkCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.lowBandSqrtDefs` — the √-currency of the cubic low band

The lead-frozen repair (`Submission/Work/BoseBoxFock/LEAD_DESIGN_lowband.md`, review
`REVIEW_lowband.md`) of `FRK.PotCubicLowBandG`.  `FRK.LowBandNPlusLinear` (LB1) is **FALSE**
(`FRK/FINDING_lowBandNPlusLinear_FALSE.md`): its currency `ℓ⁻³(Σ_s|f_L s|)(Σ_{k∈LB}|Ŵ₁ k|)cnPlus`
*counts* `#LB`, while the state gains only `√#LB`.  The repaired currency (LB1√) is

    a·ℓ⁻³·√(2·μℓ³·𝓜·#LB),

which is FS's own ε-Cauchy–Schwarz bound of `lem:Q3-splitting2` (`err₂ = C√X·ℓ⁻²·n₊`), and it is
paid by the transferred gap `γ·ℓ⁻²·cnPlus` (`γ = b/4 − b/100`) with margin `√X → 0`.

* `LowBandSqrt` — the `n₊`-linear operator bound of the low band in the √-currency (the leaf
  `Work.BoseBoxFock.FRK.lowBandSqrt_exists`);
* `LowBandSqrtArith` — the arithmetic comparison of that currency with the γ-credit (PROVED,
  `Work.BoseBoxFock.FRK.lowBandSqrtArith_exists`).
-/

noncomputable section
open MeasureTheory
namespace Work.BoseBoxFock.FRK

local notation "Ω" => EuclideanSpace ℝ (Fin 3)
open Work.BoseB4 Work.BoseDict
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- (LB1√) FS's ε-Cauchy–Schwarz bound of the low band, `n₊`-linear with the √-currency
`a·ℓ⁻³·√(2μℓ³·𝓜·#LB)` (the analytic leaf of the repair). -/
noncomputable def LowBandSqrt (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut)
    (J : ℝ) (Nmin : ℝ → ℕ) (ε₀ K : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
          (Φ : Submission.BoseGases.X n → ℝ) →
        ∀ (e : Fin (HM μ).m → Ω → ℂ),
          (∀ l, Measurable (e l)) →
          (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) →
          (∀ l, Function.support (e l)
            ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) →
          (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
            = (if l = l' then (1 : ℂ) else 0)) →
          (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) →
          (∀ l, MeasureTheory.MemLp (e l) ⊤) →
          (∃ c : ℂ, (starRingEnd ℂ) c * c
              = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
            e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun
                (Work.BoseBox.sideAt μ (BoseGases.a v)) x) →
          (∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).f k l : ℝ) : ℂ)) →
          (∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).g s l : ℝ) : ℂ)) →
          (∫ z : Ω, star (e 0 z)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z)
            = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) →
          ∀ (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ)),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
                = Work.BoseB4.dGamma (HM μ).m T_NH →
            (∫ x : Submission.BoseGases.X n,
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              - (∫ x : Submission.BoseGases.X n,
                  star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                    * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                        (Work.BoseB7.excited (Lab (HM μ).N))
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                        (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ K * (BoseGases.a v * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)⁻¹
                  * Real.sqrt (2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3
                    * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
                    * (((Work.BoseB7.excited (Lab (HM μ).N)
                        \ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E).card : ℕ) : ℝ)))
                  * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Φ : Submission.BoseGases.X n → ℝ)

/-- (LB2√) the arithmetic of the √-currency against the transferred gap. -/
noncomputable def LowBandSqrtArith (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (Nmin : ℝ → ℕ) (ε₀ K : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      K * (BoseGases.a v * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)⁻¹
          * Real.sqrt (2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3
            * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
            * (((Work.BoseB7.excited (Lab (HM μ).N)
                \ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                    (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E).card : ℕ) : ℝ)))
        ≤ ((Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 4
            - (Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 100)
          * Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ)

end Work.BoseBoxFock.FRK
