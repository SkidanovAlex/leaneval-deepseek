import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PotGroupDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicResiduals` — the two residuals of the cubic (`Q̃₃`) row

`Work.BoseBoxFock.PotCubic` (`PotGroupDefs.lean`) restricts the `k`-sum of the cubic row to FS's
high-momentum set `F.PHset E = (excited).filter (PH E.KH E.aScat)`.  The two statements below split
the target `Work.BoseBoxFock.PotCubic` into

* `PotCubicFree` — **FS `lem:2ndQuand`'s last displayed row**: the same row with the `k`-sum over
  **all** excited labels (`ℓ⁻³Σ_{s∈excited}Σ_{k∈excited} f_L(s)Ŵ₁(k)(ã_s†a_{s−k}a_k + h.c.) ≤
  q3lowWord + ½errKafz`).  This is where the *dictionary* (the Poisson/`Q_L`/`w₁` matching, FS's
  omitted "standard calculation") lives;
* `PotCubicLowBand` — the **omitted low band** `excited \ PHset`: the difference of the two rows
  is dominated by `½errKafz v R μ C·normB`.

Together they give `PotCubic` (`Work.BoseBoxFock.PotCubic_of_free_low`).

⚠ Recorded in `FINDING_PotCubic_exists.md` (SESSION 6, §§6.2–6.4): a *crude* bound of the low band
of the shape `8·ℓ⁻³·(Σ_{s∈excited}f_L(s))·(Σ_{k∈low}|Ŵ₁(k)|)·∫‖Θ‖²` is **FALSE** — the triple
integral `∫_x∫_y∫_u Θ̄(x)θ(x_i)q̄_{s−k}(y)θ_s(x_j)q̄_k(u)Θ(x[i↦y][j↦u])` is *not* dominated by
`‖Θ‖₂²·(L¹ norms of the modes)` (the two `Function.update`s let `y,u` carry the whole `Θ`-mass
while `x` is unconstrained); counterexamples are on record.  The honest low-band bound must use the
*excited-count* structure of the admissible class (FS §5/§6 `thm:aprioribounds`, i.e. `NodeB1B`),
not `L¹`/`L²` mode bounds.  Hence `PotCubicLowBand` is kept as a residual rather than derived.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

open Work.BoseB4 Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **FS `lem:2ndQuand`'s last displayed row** (`PotCubic` with the `k`-sum unrestricted).

The `k`-sum runs over the whole of `excited (Lab (HM μ).N)` instead of FS's `P_H`; this is the
*dictionary* statement (`ℓ⁻³Σ_{s,k}f_L(s)Ŵ₁(k)(ã_s†a_{s−k}a_k + h.c.) = Σ_{i≠j}(P_iQ_{L,j}w₁Q_jQ_i
+ h.c.)` up to the three error slots of `FINDING_PotCubic_exists.md` §5.3). -/
noncomputable def PotCubicFree (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut)
    (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C : ℝ) : Prop :=
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
                      (Work.BoseB7.excited (Lab (HM μ).N))
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ Work.BoseBoxFix.q3lowWord fc
                    (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                    (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Submission.BoseGases.g0 v h) 0)
                    (Φ : Submission.BoseGases.X n → ℝ)
                + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ

/-- **The low band of the cubic row** (`excited \ PHset`): the difference between the restricted
row (`PotCubic`'s left-hand side) and the unrestricted one (`PotCubicFree`'s left-hand side) is
dominated by `½errKafz v R μ C·normB`, in the *one-sided* direction needed by the target.

This is the residual named in `FINDING_PotCubic_exists.md` §5.1/§5.3; a crude `L¹`/`L²` bound of
it is **false** (see the module docstring), so it is stated as a residual.

Its *truth* is delicate and NOT settled here: the crude size of the low band is
`≈ 0.44·t^(1.24)·a⁻²·𝓕` (`t = μa³`, `𝓕` the per-integral state factor) against
`errKafz v R μ 1 ≈ t·a⁻²`, so `𝓕 ≲ t^(−0.24)` is needed; FS's a-priori bound `n₊ ≲ 𝓜 = t^(−1/4)`
overshoots that by `t^(0.012)`, and FS themselves pay this band with the kinetic **gap**
`(b/100)ℓ⁻²n₊`, which the frozen node does not carry.  See `FINDING_PotCubic_exists.md` §§6.2–6.4.
Do NOT `declare_false` on the strength of the size analysis alone. -/
noncomputable def PotCubicLowBand (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut)
    (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C : ℝ) : Prop :=
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
              ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ

end Work.BoseBoxFock
