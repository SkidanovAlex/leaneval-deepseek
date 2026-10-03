import Mathlib
import Submission.Work.KMTPlan.A6.LowModelVarCaseBCore

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7


/-- **Operator-level integration-by-parts identity (i) of §6 for the exact-height model operator
`BtwistEx` of area A6, at `(k₁,k₂) = (k₁,0)` with `k₁ ≥ 1`.**

Port of the proved `Work.KMTPlan.A6.mdlDecayHighLow_core` (in
`Submission/Work/KMTPlan/A6/MdlDecayHighLow.lean`) with `Tle → Tm`, `Btwist → BtwistEx`,
`mdlIWKer → tmKer`, `mdlBtwK → arithKerMX`, replacing the two flat results by the exact-height ones
`MdlBtwistFreezeFlatEx`/`MdlBtwistIntervalFlatEx` of `LowModelVarCaseBCore`, and replacing the
coefficient identity `MdlKerIdentHighLow` by `tmKerIdentHighLowEx` of `LowModelVarCaseBAux`
(stated there with the `cw`-level identity (i) as the hypothesis `hcw`, carried here as well).

`arithKerMX ρ P l₁ l₂ m₁ m₂ a b = arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ a b · cw m₁ a ·
cw m₂ b`; the hypothesis `hK` is discharged by `summable_arithKerMX`, and `hcw` by
`Work.KMTPlan.A6.MdlCwIntegIdentI`. -/
theorem mdlDecayHighLowEx_core (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ N k₁ : ℕ) (hk₁ : 1 ≤ k₁)
    (hN : 1 ≤ N) (u : ℕ) (F G : ℤ → ℂ) (CF CG Cw : ℝ)
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hCw0 : 0 ≤ Cw) (hw : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ‖Work.KMTPlan.A6.mdlW3 P N t‖ ≤ Cw)
    (hwm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Work.KMTPlan.A6.mdlW3 P N t) (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hcw : ∀ i₁ i₂ : ℤ,
      (∫ t in (1 / 2 : ℝ)..1,
          Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) i₁
            * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 t) i₂)
        = (Work.KMTPlan.A6.mdlScaleF k₁ : ℂ) * Work.KMTPlan.A6.mdlIota
            * (Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphiNtj N k₁ (-1) 1) i₁
                * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 1) i₂
              - Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphiNtj N k₁ (-1) (1 / 2)) i₁
                * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 (1 / 2)) i₂)
          - (Work.KMTPlan.A6.mdlScaleFG P k₁ 0 : ℂ)
              * (∫ t in (1 / 2 : ℝ)..1, Work.KMTPlan.A6.mdlW3 P N t
                  * (Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphiNtj N k₁ (-1) t) i₁
                      * Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphitildeNtj P N 0 1 t) i₂)))
    (hK : Summable fun p : ℤ × ℤ =>
      ‖Work.KMTPlan.A6.arithKerMX ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u) p.1 p.2‖)
    (a₁ a₂ a₃ a₄ : ℤ → ℝ) (ha₁ : Summable a₁) (ha₂ : Summable a₂) (ha₃ : Summable a₃)
    (ha₄ : Summable a₄)
    (hb₁ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ, ‖Work.KMTPlan.A6.tmKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) i‖ ≤ a₁ i)
    (hb₂ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖Work.KMTPlan.A6.tmKer ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 t) i‖ ≤ a₂ i)
    (hb₃ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖Work.KMTPlan.A6.tmKer ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ (-1) t) i‖ ≤ a₃ i)
    (hb₄ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖Work.KMTPlan.A6.tmKer ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N 0 1 t) i‖ ≤ a₄ i)
    (hm₁ : ∀ i : ℤ, MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Work.KMTPlan.A6.tmKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) i) MeasureTheory.volume)
    (hm₂ : ∀ i : ℤ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => Work.KMTPlan.A6.tmKer ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 t) i) MeasureTheory.volume)
    (hm₃ : ∀ i : ℤ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => Work.KMTPlan.A6.tmKer ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ (-1) t) i) MeasureTheory.volume)
    (hm₄ : ∀ i : ℤ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => Work.KMTPlan.A6.tmKer ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N 0 1 t) i) MeasureTheory.volume)
    (x : ℤ) :
    (∫ t in (1 / 2 : ℝ)..1,
        Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
          (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) F) (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 t) G) x)
      = (Work.KMTPlan.A6.mdlScaleF k₁ : ℂ) * Work.KMTPlan.A6.mdlIota
          * (Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
                (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ (-1) 1) F)
                (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N 0 0 1) G) x
              - Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
                (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ (-1) (1 / 2)) F)
                (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N 0 0 (1 / 2)) G) x)
        - (Work.KMTPlan.A6.mdlScaleFG P k₁ 0 : ℂ)
            * (∫ t in (1 / 2 : ℝ)..1, Work.KMTPlan.A6.mdlW3 P N t
                * Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
                    (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ (-1) t) F)
                    (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N 0 1 t) G) x) := by
  classical
  have hI : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hI1 : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have ha₁0 : ∀ i : ℤ, 0 ≤ a₁ i := fun i => le_trans (norm_nonneg _) (hb₁ (1 / 2) hI i)
  have ha₂0 : ∀ i : ℤ, 0 ≤ a₂ i := fun i => le_trans (norm_nonneg _) (hb₂ (1 / 2) hI i)
  have ha₃0 : ∀ i : ℤ, 0 ≤ a₃ i := fun i => le_trans (norm_nonneg _) (hb₃ (1 / 2) hI i)
  have ha₄0 : ∀ i : ℤ, 0 ≤ a₄ i := fun i => le_trans (norm_nonneg _) (hb₄ (1 / 2) hI i)
  have hsA₁ : Summable fun i : ℤ => ‖tmKer ρ l₁ (varphiNtj N k₁ (-1) 1) i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₃ 1 hI1 i) ha₃
  have hsB₁ : Summable fun i : ℤ => ‖tmKer ρ l₁ (varphiNtj N k₁ (-1) (1 / 2)) i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₃ (1 / 2) hI i) ha₃
  have hsA₂ : Summable fun i : ℤ => ‖tmKer ρ l₂ (varphitildeNtj P N 0 0 1) i‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) ha₂
    simpa only [varphitildeNtj_zero] using hb₂ 1 hI1 i
  have hsB₂ : Summable fun i : ℤ => ‖tmKer ρ l₂ (varphitildeNtj P N 0 0 (1 / 2)) i‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) ha₂
    simpa only [varphitildeNtj_zero] using hb₂ (1 / 2) hI i
  set K : ℤ → ℤ → ℂ := arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) with hKdef
  set D : (ℤ × ℤ) × (ℤ × ℤ) → ℂ := fun q => mdlKFG K F G x q.1 q.2 with hDdef
  set cL : ℤ × ℤ → ℂ := mdlCoeff (fun _ : ℝ => (1 : ℂ))
      (fun t : ℝ => fun i : ℤ => tmKer ρ l₁ (varphiNt N k₁ t) i)
      (fun t : ℝ => fun i : ℤ => tmKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) i) with hcL
  set cA : ℤ × ℤ → ℂ := fun z => tmKer ρ l₁ (varphiNtj N k₁ (-1) 1) z.1
      * tmKer ρ l₂ (varphitildeNtj P N 0 0 1) z.2 with hcA
  set cB : ℤ × ℤ → ℂ := fun z => tmKer ρ l₁ (varphiNtj N k₁ (-1) (1 / 2)) z.1
      * tmKer ρ l₂ (varphitildeNtj P N 0 0 (1 / 2)) z.2 with hcB
  set cC : ℤ × ℤ → ℂ := mdlCoeff (fun t : ℝ => mdlW3 P N t)
      (fun t : ℝ => fun i : ℤ => tmKer ρ l₁ (varphiNtj N k₁ (-1) t) i)
      (fun t : ℝ => fun i : ℤ => tmKer ρ l₂ (varphitildeNtj P N 0 1 t) i) with hcC
  set c₁ : ℂ := (mdlScaleF k₁ : ℂ) * mdlIota with hc₁
  set c₂ : ℂ := (mdlScaleFG P k₁ 0 : ℂ) with hc₂
  have hflatL : (∫ t in (1 / 2 : ℝ)..1,
        BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
          (Tm ρ l₁ (varphiNt N k₁ t) F) (Tm ρ l₂ (varphitildeNt P P.natDegree N 0 t) G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cL q.2 * D q := by
    have h := MdlBtwistIntervalFlatEx (Cw := 1) ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (fun t : ℝ => varphiNt N k₁ t) (fun t : ℝ => varphitildeNt P P.natDegree N 0 t)
      (fun _ : ℝ => (1 : ℂ)) F G hF hG (fun t ht => by simp)
      measurable_const.aestronglyMeasurable a₁ a₂ ha₁ ha₂ hb₁ hb₂ hm₁ hm₂ hK x
    simpa only [hKdef, hDdef, hcL, Pi.one_apply, one_mul] using h
  have hfreeze1 : BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tm ρ l₁ (varphiNtj N k₁ (-1) 1) F) (Tm ρ l₂ (varphitildeNtj P N 0 0 1) G) x
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cA q.2 * D q := by
    have h := MdlBtwistFreezeFlatEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (varphiNtj N k₁ (-1) 1) (varphitildeNtj P N 0 0 1) F G (1 : ℂ) hF hG hK hsA₁ hsA₂ x
    simpa only [hKdef, hDdef, hcA, one_mul] using h
  have hfreeze2 : BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tm ρ l₁ (varphiNtj N k₁ (-1) (1 / 2)) F) (Tm ρ l₂ (varphitildeNtj P N 0 0 (1 / 2)) G) x
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cB q.2 * D q := by
    have h := MdlBtwistFreezeFlatEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (varphiNtj N k₁ (-1) (1 / 2)) (varphitildeNtj P N 0 0 (1 / 2)) F G (1 : ℂ) hF hG hK hsB₁ hsB₂ x
    simpa only [hKdef, hDdef, hcB, one_mul] using h
  have hmid : (∫ t in (1 / 2 : ℝ)..1, mdlW3 P N t
        * BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
            (Tm ρ l₁ (varphiNtj N k₁ (-1) t) F)
            (Tm ρ l₂ (varphitildeNtj P N 0 1 t) G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cC q.2 * D q := by
    have h := MdlBtwistIntervalFlatEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (fun t : ℝ => varphiNtj N k₁ (-1) t) (fun t : ℝ => varphitildeNtj P N 0 1 t)
      (fun t : ℝ => mdlW3 P N t) F G hF hG hw hwm a₃ a₄ ha₃ ha₄ hb₃ hb₄ hm₃ hm₄ hK x
    simpa only [hKdef, hDdef, hcC] using h
  have hLs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cL q.2 * D q := by
    have h := MdlFlatSummable (K := arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cL) (a := a₁) (a' := a₂) ha₁ ha₂ ha₁0 ha₂0 (Ca := 1) zero_le_one
      (fun z => by
        rw [hcL]
        exact mdl_coeff_intervalIntegral_bound (w := fun _ : ℝ => (1 : ℂ)) (Cw := 1)
          (by intro t ht; simp) zero_le_one ha₁0 ha₂0 hb₁ hb₂ z) x
    simpa only [hKdef, hDdef] using h
  have hAs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cA q.2 * D q := by
    have h := MdlFlatSummable (K := arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cA) (a := fun i : ℤ => ‖tmKer ρ l₁ (varphiNtj N k₁ (-1) 1) i‖)
      (a' := fun i : ℤ => ‖tmKer ρ l₂ (varphitildeNtj P N 0 0 1) i‖)
      hsA₁ hsA₂ (fun i => norm_nonneg _) (fun i => norm_nonneg _) (Ca := 1) zero_le_one
      (fun z => by rw [hcA, norm_mul, one_mul]) x
    simpa only [hKdef, hDdef] using h
  have hBs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cB q.2 * D q := by
    have h := MdlFlatSummable (K := arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cB) (a := fun i : ℤ => ‖tmKer ρ l₁ (varphiNtj N k₁ (-1) (1 / 2)) i‖)
      (a' := fun i : ℤ => ‖tmKer ρ l₂ (varphitildeNtj P N 0 0 (1 / 2)) i‖)
      hsB₁ hsB₂ (fun i => norm_nonneg _) (fun i => norm_nonneg _) (Ca := 1) zero_le_one
      (fun z => by rw [hcB, norm_mul, one_mul]) x
    simpa only [hKdef, hDdef] using h
  have hCs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cC q.2 * D q := by
    have h := MdlFlatSummable (K := arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cC) (a := a₃) (a' := a₄) ha₃ ha₄ ha₃0 ha₄0 (Ca := Cw) hCw0
      (fun z => by
        rw [hcC]
        exact mdl_coeff_intervalIntegral_bound (w := fun t : ℝ => mdlW3 P N t) hw hCw0
          ha₃0 ha₄0 hb₃ hb₄ z) x
    simpa only [hKdef, hDdef] using h
  have hcoef : ∀ z : ℤ × ℤ, cL z = c₁ * cA z - c₁ * cB z - c₂ * cC z := by
    intro z
    have h := tmKerIdentHighLowEx ρ P l₁ l₂ N k₁ hk₁ hN hcw z.1 z.2
    rw [hcL, hcA, hcB, hcC, hc₁, hc₂]
    simp only [mdlCoeff, one_mul, varphitildeNtj_zero]
    rw [h]
    ring
  rw [hflatL, hfreeze1, hfreeze2, hmid]
  exact mdl_tsum_linear D cA cB cC cL c₁ c₂ hAs hBs hCs hLs hcoef

end

end Work.KMTPlan.A6
