import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.rowB_reduce
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.rowSplitDefs` — the two-group split of the row table `FormW2B`

`Work.BoseBoxFock.AVgen` (`Submission/Work/BoseBoxFock/slotAVgen.lean`) is a sum of twelve
summands.  Grouping them:

* **kinetic group** — rows 1,2,3: the kinetic symbol `Σ_k τ̃(k)·B(rankOne (f k))`, the gap
  `(b/2ℓ²)·B(boxT0)` and the `n₊^H`-gap `(ε_Tb/(2d²ℓ²))·B(T_NH)`;
* **potential group** — rows 4..11: the contact, chemical, `(Ŵ₁+Ŵ₁ω)a₀†a†aa₀`, Bogoliubov,
  `χ̂`-linear, `χ̂²`-linear and cubic rows.

Every row of the kinetic group carries only the weights `E.tau`, `E.b`, `E.eT`, `E.d`, `E.ell`;
every row of the potential group only `E.W1`, `E.W1omega`, `E.W1omega0`, `E.hatChi`,
`E.hatChiSq`, `E.fL`, `E.mu`, `E.ell`.  Hence the two groups are *isolated* by zeroing the
complementary fields, which is what `kinOnlyEnv`/`potOnlyEnv` do; the identity

    AVgen B idop f g T_NH PHs E gHat0
      = AVgen B idop f g T_NH ∅ (kinOnly E) 0 + AVgen B idop f g T_NH PHs (potOnly E) gHat0

is the precise statement of that isolation (delegated as `AVgen_split_kin_pot`), and

    FormW2Bkin := (the kinetic-group form) ≤ W2kinB + (1/2)·errKafz·normB
    FormW2Bpot := (the potential-group form) ≤ W2potB + (1/2)·errKafz·normB

are the two halves of the row table (each with the *same* context as `FormW2B`).  Their sum is
`FormW2B` itself, so the analytic content of the row table is split into the two chapters that
`bf3a_kin_reserve` and `bf3a_pot` mirror on the corpus side.

`Work.BoseBoxFock.FormW2B` is stated with its own binder list (not through these two `Prop`s),
so the assembly `FormW2B ⟸ FormW2Bkin + FormW2Bpot` needs the splitting identity above; that
assembly is `Work.BoseBoxFock.FormW2B_of_split` (in `Submission/Work/BoseBoxFock/rowSplit.lean`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The environment with the *potential* weights zeroed: only the kinetic, gap and `n₊^H` rows of
`AVgen` survive. -/
def kinOnlyEnv {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) : Work.BoseB7.Q3Env Mode :=
  { E with W1 := 0, W1omega := 0, W1omega0 := 0, hatChi := 0, hatChiSq := 0, mu := 0 }

/-- The environment with the *kinetic* weights zeroed: only the potential rows of `AVgen`
survive. -/
def potOnlyEnv {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) : Work.BoseB7.Q3Env Mode :=
  { E with tau := 0, b := 0, eT := 0 }

/-- **The kinetic half of the row table** — ⛔ **FALSE** (do not delegate it): charging the kinetic
rows against `W2kinB`'s continuum τ̃-form leaves the aliasing deficit unpaid, see
`FINDING_FormW2B_linked_kinetic_row_FALSE.md` §2/§5.  `Work.BoseBoxFock.FormRowKin` below is the
corrected replacement (against the word's sharp `kinFormB`). -/
noncomputable def FormW2Bkin (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
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
                  * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                      (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                      (HM μ).f (HM μ).g T_NH
                      (∅ : Finset (Lab (HM μ).N))
                      (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      0
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ Work.BoseBoxFock.W2kinB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                  + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ

/-- **The potential half of the row table**: at the honest data and every state satisfying the
a-priori hypotheses, the potential rows (contact, chemical, `(Ŵ₁+Ŵ₁ω)a₀†a†aa₀`, Bogoliubov,
`χ̂`- and `χ̂²`-linear, cubic) of the model's first-quantised form are dominated by
`Work.BoseBoxFock.W2potB` plus half of the error.  Its continuum counterpart is `bf3a_pot`
(PROVED). -/
noncomputable def FormW2Bpot (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
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
                  * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                      (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                      (HM μ).f (HM μ).g T_NH
                      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      (8 * Real.pi * BoseGases.a v)
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ Work.BoseBoxFock.W2potB v h μ n fc (Φ : Submission.BoseGases.X n → ℝ)
                  + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ

/-- **The *corrected* kinetic half of the row table** (`Work.BoseBoxFock.FormW2Bkin` above is
**FALSE**: charging the kinetic rows against `W2kinB`'s continuum τ̃-form leaves the aliasing
deficit `3c(R₁−S₁) − (9/4+c₀)c²a₀ + C(Ψ_c)` unpaid — see
`Submission/Work/BoseBoxFock/FINDING_FormW2B_linked_kinetic_row_FALSE.md` and `BF3B_PLAN_S6.md`
§1).  The kinetic rows must instead be charged against the word's **sharp** kinetic form
`Work.BoseKinLoc.kinFormB`, whose symbol `F_c = [·−c]₊²` is what pays the aliasing
(`tauAssembly.arith_deficit_core`).

The extra `−(b/100)(…)` on the right is `bf3a_pot`'s *reserve* subsidy: `bf3a_pot` (PROVED)
spends `(b/100)(ℓ⁻²cnPlus + ε_T(dℓ)⁻²nPlusHB)` from the word's gap content, so the kinetic half
must leave that much on the table.  The assembly is then
`AV_gen = (kinetic+gaps) + potential ≤ (kinFormB − reserve + ½err) + (W2potB + ½err)
 ≤ kinFormB + chemPartB + pairPartB + (err + C₂errB)` (via `bf3a_pot`) `= wordB + …`, i.e. `RowB`
(`Work.BoseBoxFock.RowB_of_kin_pot`). -/
noncomputable def FormRowKin (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
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
                  * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                      (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                      (HM μ).f (HM μ).g T_NH
                      (∅ : Finset (Lab (HM μ).N))
                      (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      0
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
                    (Φ : Submission.BoseGases.X n → ℝ)
                  - ((Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 100) *
                      (Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ)
                          * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
                              (Φ : Submission.BoseGases.X n → ℝ)
                        + (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT *
                            ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                              * Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-2 : ℤ)
                          * Work.BoseBoxFix.nPlusHB (Work.BoseBox.sideAt μ (BoseGases.a v))
                              (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                              (Φ : Submission.BoseGases.X n → ℝ))
                  + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ


end Work.BoseBoxFock
