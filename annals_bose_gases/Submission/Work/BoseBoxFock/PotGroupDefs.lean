import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.FormW2B_of_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotGroupDefs` — the four row groups of the *potential half* of the row table

`Work.BoseBoxFock.FormW2Bpot` (`Submission/Work/BoseBoxFock/rowSplitDefs.lean`) is the potential
half of FS `prop:Hamilton2ndQuant`'s row table: the potential rows of the box twin `AVgen` at
`potOnlyEnv E` (i.e. rows 4..11 of `AVgen`) are dominated by FS's first-quantised second-quantised
word `W2potB = q0word + q1word + q2word + q3lowWord` plus `(1/2)·errKafz·|Phi|^2`.

This module splits that statement into the **four row groups** of FS's own proof of
`prop:Hamilton2ndQuant` (FS group `Q0,Q1` together, then `Q2`, then `Q3`), stated as four
independent `Prop`s so that the analytic content can be attacked group by group:

| group | `AVgen` rows | FS | compared with |
|---|---|---|---|
| `PotContactChem` | contact + chemical | `Q0` | `q0word` |
| `PotChiLin`      | `chi`-linear + `chi^2`-linear | `Q1` | `q1word` |
| `PotPairRows`    | `(W1+W1omega)a0dag adag a a a0` + Bogoliubov + `(L0+L1) o sum` | `Q2` | `q2word` |
| `PotCubic`       | the cubic `Q3` row | `Q3` | `q3lowWord` |

Each statement carries the *full* 35-line context of `Work.BoseBoxFock.FormW2Bpot` (so a consumer
instantiates it exactly at the ambient context), and each grants `(1/2)·errKafz v R μ C·|Phi|^2` of
the error; since `errKafz` is *linear* in `C`, the four errors sum exactly (see
`Submission/Work/BoseBoxFock/PotGroupAssembly.lean`).

The splitting identity is `AVgen_potOnly_eq_potGroups`, a regrouping of the summands of
`AVgen` (the kinetic rows `tau`, `b`, `eT` vanish at `potOnlyEnv`).

Everything here is `sorry`-free.
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

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {m : ℕ} [NeZero m]
variable {ι : Type*}

/-! ## 1. The four row-group operators -/

/-- **Group 0** (FS `Q0`): the contact row and the chemical row. -/
noncomputable def potContactChem
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ) :=
  ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ)) * (gHat0 + E.W1omega0)) •
      ((B (rankOne (evec0 m))) ∘ (B (rankOne (evec0 m)))
        - B ((rankOne (evec0 m)).comp (rankOne (evec0 m))))
    - (E.mu * gHat0) • (B (rankOne (evec0 m)))

/-- **Group 1** (FS `Q1`): the `chi`-linear and `chi^2`-linear rows. -/
noncomputable def potChiLin
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (f g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ) :=
  (∑ k : Mode, E.hatChi k •
      ((E.ell ^ (-(3 : ℝ)) * E.W1 0) •
          ((B (rankOne (evec0 m))) ∘ (B (rankOnePair (f k) (evec0 m))))
        - (E.mu * E.W1 0) • (B (rankOnePair (f k) (evec0 m)))
        + ((E.ell ^ (-(3 : ℝ)) * E.W1 0) •
            ((B (rankOnePair (evec0 m) (f k))) ∘ (B (rankOne (evec0 m))))
          - (E.mu * E.W1 0) • (B (rankOnePair (evec0 m) (f k))))))
    + ∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s •
      ((E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
          ((B (rankOne (evec0 m))) ∘ (B (rankOnePair (g s) (evec0 m))))
        + (E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
            ((B (rankOnePair (evec0 m) (g s))) ∘ (B (rankOne (evec0 m)))))

/-- **Group 2** (FS `Q2`): the `(W1+W1omega)a0dag adag a a a0` row, the Bogoliubov pair row and
the `(L0+L1) o sum_k adag a` row. -/
noncomputable def potPairRows
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ) :=
  (E.ell ^ (-(3 : ℝ))) • ∑ k : Mode, (E.W1 k + E.W1omega k) •
      ((B (rankOnePair (evec0 m) (f k))) ∘ (B (rankOnePair (f k) (evec0 m)))
        - B ((rankOnePair (evec0 m) (f k)).comp (rankOnePair (f k) (evec0 m))))
    + ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ))) • ∑ k : Mode, E.W1 k •
      (((B (rankOnePair (evec0 m) (f k))) ∘ (B (rankOnePair (evec0 m) (f (-k))))
          - B ((rankOnePair (evec0 m) (f k)).comp (rankOnePair (evec0 m) (f (-k)))))
        + ((B (rankOnePair (f k) (evec0 m))) ∘ (B (rankOnePair (f (-k)) (evec0 m)))
            - B ((rankOnePair (f k) (evec0 m)).comp (rankOnePair (f (-k)) (evec0 m)))))
    + ∑ k : Mode,
        ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
            ((B (rankOne (evec0 m))) ∘ (B (rankOne (f k))))
          - (E.mu * E.W1 0) • (B (rankOne (f k))))

/-- **Group 3** (FS `Q3`): the cubic row. -/
noncomputable def potCubic
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) :
    ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ) :=
  (E.ell ^ (-(3 : ℝ))) • ∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ PHs,
    (E.fL s * E.W1 k) •
      (((B (rankOnePair (evec0 m) (f (s - k)))) ∘ (B (rankOnePair (g s) (f k))))
          - B ((rankOnePair (evec0 m) (f (s - k))).comp (rankOnePair (g s) (f k)))
        + ((B (rankOnePair (f k) (g s))) ∘ (B (rankOnePair (f (s - k)) (evec0 m))))
          - B ((rankOnePair (f k) (g s)).comp (rankOnePair (f (s - k)) (evec0 m))))

/-- **The splitting identity**: at the potential-only environment, `AVgen` is the sum of the four
row groups (grouped as `(G0+G1) + (G2+G3)` for the integral split). -/
theorem AVgen_potOnly_eq_potGroups
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (idop : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    AVgen B idop f g T_NH PHs (potOnlyEnv E) gHat0
      = (potContactChem B E gHat0 + potChiLin B f g E)
        + (potPairRows B f E + potCubic B f g PHs E) := by
  simp only [AVgen, potContactChem, potChiLin, potPairRows, potCubic, potOnlyEnv,
    Pi.zero_apply, zero_smul, zero_div, mul_zero, Finset.sum_const, nsmul_zero]
  abel


/-! ## 2. The four group statements -/

/-- **The contact + chemical group** (FS `Q0`). -/

noncomputable def PotContactChem (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
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
                  * potContactChem (fun T => boxSlotSum e T)
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (8 * Real.pi * BoseGases.a v)
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ Submission.BoseGases.q0word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
                    (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Submission.BoseGases.g0 v h) 0)
                    (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Submission.BoseGases.g2 v h) 0)
                    (Φ : Submission.BoseGases.X n → ℝ)
                + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ

/-- **The `chi`-linear group** (FS `Q1`). -/

noncomputable def PotChiLin (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
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
                  * potChiLin (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ Submission.BoseGases.q1word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
                    (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Submission.BoseGases.g0 v h) 0)
                    (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Submission.BoseGases.g2 v h) 0)
                    (Φ : Submission.BoseGases.X n → ℝ)
                + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ

/-- **The pair-row group** (FS `Q2`). -/

noncomputable def PotPairRows (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
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
                  * potPairRows (fun T => boxSlotSum e T) (HM μ).f
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ Submission.BoseGases.q2word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
                    (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Submission.BoseGases.g0 v h) 0)
                    (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Submission.BoseGases.g2 v h) 0)
                    (Φ : Submission.BoseGases.X n → ℝ)
                + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ

/-- **The cubic group** (FS `Q3`). -/

noncomputable def PotCubic (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
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
              ≤ Work.BoseBoxFix.q3lowWord fc
                    (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                    (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Submission.BoseGases.g0 v h) 0)
                    (Φ : Submission.BoseGases.X n → ℝ)
                + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ

/-! ## 3. The integrability brick of the assembly -/

/-- **The integrability brick**: at every context, the four group integrands
`x ↦ conj (boxRestrictC ℓ Φ x) * (Gᵢ (boxRestrictC ℓ Φ)) x` are Bochner-integrable (each is a
bounded measurable function supported in a set of finite measure, because `boxRestrictC ℓ Φ` is
box-supported).  This is what lets the assembly split `∫ conj Θ · (Σᵢ Gᵢ Θ)` into the four
integrals (`MeasureTheory.integral_add`). -/
noncomputable def PotGroupsIntegrable (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) (R J : ℝ) (Nmin : ℝ → ℕ)
    (ε₀ : ℝ) : Prop :=
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
            (MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * potContactChem (fun T => boxSlotSum e T)
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (8 * Real.pi * BoseGases.a v)
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x)) ∧
            (MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * potChiLin (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x)) ∧
            (MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * potPairRows (fun T => boxSlotSum e T) (HM μ).f
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x)) ∧
            (MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x))

end Work.BoseBoxFock
