/-
# The exact-height (`BtwistEx`/`Tm`) integration-by-parts identities of §6

This module proves the two *operator-level* integration-by-parts identities (i) and (ii) of
Krause--Mirek--Tao §6 for the exact-height model operator `BtwistEx` and the exact-height
Ionescu--Wainger multipliers `Tm` of area A6, i.e. the companions of the proved
`Work.KMTPlan.A6.mdlDecayLowHigh_core` (in the `Tle`/`Btwist` vocabulary) and of
`Work.KMTPlan.A6.mdlDecayHighLow_core`.

The route is the same as in the `Tle`/`Btwist` proofs: `BtwistEx_Tm_eq_mdlNF` puts both sides into
the normal form `mdlNF`; the (generic) Fubini engine `MdlNFIntegral` interchanges the `t`-integral
with the `(p,z)`-sum; the (generic) `MdlFlatSummable` provides the summability that makes
`MdlTsumCombine` applicable; and the coefficient identity is the kernel-level identity
`tmKerIdentLowHighEx` (resp. `tmKerIdentHighLowEx`) of `LowModelVarCaseBAux`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowModelVarCaseBAux

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

/-! ## The frozen slice of `BtwistEx` in flat form -/

/-- **The frozen slice of `BtwistEx` on two `Tm`-images, in flat `(p,z)`-form.** -/
theorem MdlBtwistFreezeFlatEx (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (m₁ m₂ : ℝ → ℂ) (Φ Ψ : ℝ → ℂ) (F G : ℤ → ℂ) {CF CG : ℝ} (c : ℂ)
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hK : Summable fun p : ℤ × ℤ => ‖arithKerMX ρ P l₁ l₂ m₁ m₂ p.1 p.2‖)
    (hκ : Summable fun i : ℤ => ‖tmKer ρ l₁ Φ i‖)
    (hκ' : Summable fun i : ℤ => ‖tmKer ρ l₂ Ψ i‖) (x : ℤ) :
    c * (BtwistEx ρ P l₁ l₂ m₁ m₂ (Tm ρ l₁ Φ F) (Tm ρ l₂ Ψ G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ),
          (c * (tmKer ρ l₁ Φ q.2.1 * tmKer ρ l₂ Ψ q.2.2))
            * mdlKFG (arithKerMX ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2 := by
  have hS : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      (tmKer ρ l₁ Φ q.2.1 * tmKer ρ l₂ Ψ q.2.2)
        * mdlKFG (arithKerMX ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2 :=
    MdlFlatSummable (K := arithKerMX ρ P l₁ l₂ m₁ m₂) hF hG hK
      (c := fun z : ℤ × ℤ => tmKer ρ l₁ Φ z.1 * tmKer ρ l₂ Ψ z.2)
      (a := fun i : ℤ => ‖tmKer ρ l₁ Φ i‖)
      (a' := fun i : ℤ => ‖tmKer ρ l₂ Ψ i‖)
      hκ hκ' (fun i => norm_nonneg _) (fun i => norm_nonneg _) (Ca := 1) zero_le_one
      (fun z => by rw [norm_mul, one_mul]) x
  have hmain : BtwistEx ρ P l₁ l₂ m₁ m₂ (Tm ρ l₁ Φ F) (Tm ρ l₂ Ψ G) x
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ),
          (tmKer ρ l₁ Φ q.2.1 * tmKer ρ l₂ Ψ q.2.2)
            * mdlKFG (arithKerMX ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2 := by
    rw [BtwistEx_Tm_eq_mdlNF ρ P l₁ l₂ m₁ m₂ Φ Ψ F G hF hG hK hκ hκ' x]
    exact mdlNF_eq_tsum_prod hF hG hK hκ hκ' x
  rw [hmain]
  have hcongr : (∑' q : (ℤ × ℤ) × (ℤ × ℤ),
        (c * (tmKer ρ l₁ Φ q.2.1 * tmKer ρ l₂ Ψ q.2.2))
          * mdlKFG (arithKerMX ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ),
          c * ((tmKer ρ l₁ Φ q.2.1 * tmKer ρ l₂ Ψ q.2.2)
            * mdlKFG (arithKerMX ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2) :=
    tsum_congr (fun q => by ring)
  rw [hcongr, Summable.tsum_mul_left c hS]

/-! ## The `t`-integrated slices of the identity -/

/-- **The `t`-integral of the weighted slices of `BtwistEx`, in flat `(p,z)`-form.** -/
theorem MdlBtwistIntervalFlatEx (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (m₁ m₂ : ℝ → ℂ) (Φ Ψ : ℝ → ℝ → ℂ) (w : ℝ → ℂ) (F G : ℤ → ℂ) {CF CG Cw : ℝ}
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hw : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ‖w t‖ ≤ Cw)
    (hwm : MeasureTheory.AEStronglyMeasurable w MeasureTheory.volume)
    (a a' : ℤ → ℝ) (ha : Summable a) (ha' : Summable a')
    (hb : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ, ‖tmKer ρ l₁ (Φ t) i‖ ≤ a i)
    (hb' : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ, ‖tmKer ρ l₂ (Ψ t) i‖ ≤ a' i)
    (hm : ∀ i : ℤ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => tmKer ρ l₁ (Φ t) i) MeasureTheory.volume)
    (hm' : ∀ i : ℤ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => tmKer ρ l₂ (Ψ t) i) MeasureTheory.volume)
    (hK : Summable fun p : ℤ × ℤ => ‖arithKerMX ρ P l₁ l₂ m₁ m₂ p.1 p.2‖) (x : ℤ) :
    (∫ t in (1/2 : ℝ)..1,
        w t * BtwistEx ρ P l₁ l₂ m₁ m₂ (Tm ρ l₁ (Φ t) F) (Tm ρ l₂ (Ψ t) G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ),
          mdlCoeff w (fun t i => tmKer ρ l₁ (Φ t) i) (fun t i => tmKer ρ l₂ (Ψ t) i) q.2
            * mdlKFG (arithKerMX ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2 := by
  have hI : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hCw : 0 ≤ Cw := le_trans (norm_nonneg _) (hw (1/2) hI)
  have ha0 : ∀ i : ℤ, 0 ≤ a i := fun i => le_trans (norm_nonneg _) (hb (1/2) hI i)
  have ha0' : ∀ i : ℤ, 0 ≤ a' i := fun i => le_trans (norm_nonneg _) (hb' (1/2) hI i)
  have hS : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      mdlCoeff w (fun t i => tmKer ρ l₁ (Φ t) i) (fun t i => tmKer ρ l₂ (Ψ t) i) q.2
        * mdlKFG (arithKerMX ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2 :=
    MdlFlatSummable (K := arithKerMX ρ P l₁ l₂ m₁ m₂) hF hG hK
      (c := mdlCoeff w (fun t i => tmKer ρ l₁ (Φ t) i)
        (fun t i => tmKer ρ l₂ (Ψ t) i))
      ha ha' ha0 ha0' hCw
      (fun z => mdl_coeff_intervalIntegral_bound hw hCw ha0 ha0' hb hb' z) x
  have hpt : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      BtwistEx ρ P l₁ l₂ m₁ m₂ (Tm ρ l₁ (Φ t) F) (Tm ρ l₂ (Ψ t) G) x
        = mdlNF (arithKerMX ρ P l₁ l₂ m₁ m₂) (fun i => tmKer ρ l₁ (Φ t) i)
            (fun i => tmKer ρ l₂ (Ψ t) i) F G x := by
    intro t ht
    have hs : Summable fun i : ℤ => ‖tmKer ρ l₁ (Φ t) i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb t ht i) ha
    have hs' : Summable fun i : ℤ => ‖tmKer ρ l₂ (Ψ t) i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb' t ht i) ha'
    exact BtwistEx_Tm_eq_mdlNF ρ P l₁ l₂ m₁ m₂ (Φ t) (Ψ t) F G hF hG hK hs hs' x
  have hstep : (∫ t in (1/2 : ℝ)..1, w t * BtwistEx ρ P l₁ l₂ m₁ m₂
        (Tm ρ l₁ (Φ t) F) (Tm ρ l₂ (Ψ t) G) x)
      = ∫ t in (1/2 : ℝ)..1, w t * mdlNF (arithKerMX ρ P l₁ l₂ m₁ m₂)
          (fun i => tmKer ρ l₁ (Φ t) i) (fun i => tmKer ρ l₂ (Ψ t) i) F G x := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    rw [hpt t ht]
  rw [hstep, MdlNFIntegral (arithKerMX ρ P l₁ l₂ m₁ m₂) F G hF hG hK w hw hwm
    (fun t i => tmKer ρ l₁ (Φ t) i) (fun t i => tmKer ρ l₂ (Ψ t) i) a a' ha ha'
    hb hb' hm hm' x]
  rw [hS.tsum_prod]
  refine tsum_congr (fun p => tsum_congr (fun z => ?_))
  simp only [mdlCoeff, mdlKFG]

/-! ## The operator-level identity (ii) for `BtwistEx` -/

/-- **The operator-level integration-by-parts identity (ii) at `(k₁,k₂) = (0,k₂)`, `k₂ ≥ 1`, for
the exact-height model operator `BtwistEx`.**  This is the exact-height companion of
`Work.KMTPlan.A6.mdlDecayLowHigh_core`, with `Tm` in place of `Tle`, `BtwistEx` in place of
`Btwist` and `tmKer` in place of `mdlIWKer`. -/
theorem mdlDecayLowHighEx_core
    (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ N k₂ : ℕ) (hk₂ : 1 ≤ k₂) (hN : 1 ≤ N) (u : ℕ)
    (F G : ℤ → ℂ) (CF CG Cw₁ Cw₂ : ℝ)
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hCw₁0 : 0 ≤ Cw₁) (hw₁ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ‖mdlW1 P N t‖ ≤ Cw₁)
    (hwm₁ : AEStronglyMeasurable (fun t : ℝ => mdlW1 P N t) (volume : MeasureTheory.Measure ℝ))
    (hCw₂0 : 0 ≤ Cw₂) (hw₂ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ‖mdlW2 P N t‖ ≤ Cw₂)
    (hwm₂ : AEStronglyMeasurable (fun t : ℝ => mdlW2 P N t) (volume : MeasureTheory.Measure ℝ))
    (hP : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, PderivR P ((N : ℝ) * t) ≠ 0)
    (hK : Summable fun p : ℤ × ℤ =>
      ‖arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) p.1 p.2‖)
    (a₁ a₂ a₃ a₄ : ℤ → ℝ) (ha₁ : Summable a₁) (ha₂ : Summable a₂) (ha₃ : Summable a₃)
    (ha₄ : Summable a₄)
    (hb₁ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ, ‖tmKer ρ l₁ (varphiNt N 0 t) i‖ ≤ a₁ i)
    (hb₂ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t) i‖ ≤ a₂ i)
    (hb₃ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ, ‖tmKer ρ l₁ (varphiNtj N 0 1 t) i‖ ≤ a₃ i)
    (hb₄ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) t) i‖ ≤ a₄ i)
    (hm₁ : ∀ i : ℤ, AEStronglyMeasurable (fun t : ℝ => tmKer ρ l₁ (varphiNt N 0 t) i) volume)
    (hm₂ : ∀ i : ℤ, AEStronglyMeasurable
      (fun t : ℝ => tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t) i) volume)
    (hm₃ : ∀ i : ℤ, AEStronglyMeasurable (fun t : ℝ => tmKer ρ l₁ (varphiNtj N 0 1 t) i) volume)
    (hm₄ : ∀ i : ℤ, AEStronglyMeasurable
      (fun t : ℝ => tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) t) i) volume)
    (x : ℤ) :
    (∫ t in (1 / 2 : ℝ)..1,
        BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
          (Tm ρ l₁ (varphiNtj N 0 0 t) F) (Tm ρ l₂ (varphitildeNtj P N k₂ 0 t) G) x)
      = (mdlScale P k₂ : ℂ) * mdlIota
          * (mdlW1 P N 1 * BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
                (Tm ρ l₁ (varphiNtj N 0 0 1) F) (Tm ρ l₂ (varphitildeNtj P N k₂ (-1) 1) G) x
              - mdlW1 P N (1 / 2) * BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
                (Tm ρ l₁ (varphiNtj N 0 0 (1 / 2)) F)
                (Tm ρ l₂ (varphitildeNtj P N k₂ (-1) (1 / 2)) G) x)
        - (mdlScaleGe P 0 k₂ : ℂ)
            * (∫ t in (1 / 2 : ℝ)..1, mdlW1 P N t
                * BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
                    (Tm ρ l₁ (varphiNtj N 0 1 t) F)
                    (Tm ρ l₂ (varphitildeNtj P N k₂ (-1) t) G) x)
        + (mdlScale P k₂ : ℂ) * mdlIota
            * (∫ t in (1 / 2 : ℝ)..1, mdlW2 P N t
                * BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
                    (Tm ρ l₁ (varphiNtj N 0 0 t) F)
                    (Tm ρ l₂ (varphitildeNtj P N k₂ (-1) t) G) x) := by
  classical
  have hI : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hI1 : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have ha₁0 : ∀ i : ℤ, 0 ≤ a₁ i := fun i => le_trans (norm_nonneg _) (hb₁ (1/2) hI i)
  have ha₂0 : ∀ i : ℤ, 0 ≤ a₂ i := fun i => le_trans (norm_nonneg _) (hb₂ (1/2) hI i)
  have ha₃0 : ∀ i : ℤ, 0 ≤ a₃ i := fun i => le_trans (norm_nonneg _) (hb₃ (1/2) hI i)
  have ha₄0 : ∀ i : ℤ, 0 ≤ a₄ i := fun i => le_trans (norm_nonneg _) (hb₄ (1/2) hI i)
  have hb₁' : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖tmKer ρ l₁ (varphiNtj N 0 0 t) i‖ ≤ a₁ i := by
    intro t ht i; simpa only [varphiNtj_zero] using hb₁ t ht i
  have hb₂' : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖tmKer ρ l₂ (varphitildeNtj P N k₂ 0 t) i‖ ≤ a₂ i := by
    intro t ht i; simpa only [varphitildeNtj_zero] using hb₂ t ht i
  have hm₁' : ∀ i : ℤ, AEStronglyMeasurable
      (fun t : ℝ => tmKer ρ l₁ (varphiNtj N 0 0 t) i) volume := by
    intro i; simpa only [varphiNtj_zero] using hm₁ i
  have hm₂' : ∀ i : ℤ, AEStronglyMeasurable
      (fun t : ℝ => tmKer ρ l₂ (varphitildeNtj P N k₂ 0 t) i) volume := by
    intro i; simpa only [varphitildeNtj_zero] using hm₂ i
  have hsA₁ : Summable fun i : ℤ => ‖tmKer ρ l₁ (varphiNtj N 0 0 1) i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₁' 1 hI1 i) ha₁
  have hsA₂ : Summable fun i : ℤ => ‖tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) 1) i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₄ 1 hI1 i) ha₄
  have hsB₁ : Summable fun i : ℤ => ‖tmKer ρ l₁ (varphiNtj N 0 0 (1 / 2)) i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₁' (1/2) hI i) ha₁
  have hsB₂ : Summable fun i : ℤ => ‖tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) (1 / 2)) i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₄ (1/2) hI i) ha₄
  set K : ℤ → ℤ → ℂ := arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) with hKdef
  set kap1 : ℝ → ℤ → ℂ := fun t i => tmKer ρ l₁ (varphiNtj N 0 0 t) i with hkap1
  set kap2 : ℝ → ℤ → ℂ := fun t i => tmKer ρ l₂ (varphitildeNtj P N k₂ 0 t) i with hkap2
  set kap3 : ℝ → ℤ → ℂ := fun t i => tmKer ρ l₁ (varphiNtj N 0 1 t) i with hkap3
  set kap4 : ℝ → ℤ → ℂ := fun t i => tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) t) i with hkap4
  set D : (ℤ × ℤ) × (ℤ × ℤ) → ℂ := fun q => mdlKFG K F G x q.1 q.2 with hDdef
  set cL : ℤ × ℤ → ℂ := mdlCoeff (fun _ => (1 : ℂ)) kap1 kap2 with hcL
  set cA : ℤ × ℤ → ℂ := fun z => mdlW1 P N 1 *
      (tmKer ρ l₁ (varphiNtj N 0 0 1) z.1
        * tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) 1) z.2) with hcA
  set cB : ℤ × ℤ → ℂ := fun z => mdlW1 P N (1 / 2) *
      (tmKer ρ l₁ (varphiNtj N 0 0 (1 / 2)) z.1
        * tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) (1 / 2)) z.2) with hcB
  set cC : ℤ × ℤ → ℂ := mdlCoeff (fun t => mdlW1 P N t) kap3 kap4 with hcC
  set cE : ℤ × ℤ → ℂ := mdlCoeff (fun t => mdlW2 P N t) kap1 kap4 with hcE
  set c1 : ℂ := (mdlScale P k₂ : ℂ) * mdlIota with hc1
  set c2 : ℂ := (mdlScaleGe P 0 k₂ : ℂ) with hc2
  have hflatL : (∫ t in (1 / 2 : ℝ)..1,
        BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
          (Tm ρ l₁ (varphiNtj N 0 0 t) F) (Tm ρ l₂ (varphitildeNtj P N k₂ 0 t) G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cL q.2 * D q := by
    have h := MdlBtwistIntervalFlatEx (Cw := 1) ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (fun t : ℝ => varphiNtj N 0 0 t) (fun t : ℝ => varphitildeNtj P N k₂ 0 t)
      (fun _ : ℝ => (1 : ℂ)) F G hF hG (fun t ht => by simp)
      measurable_const.aestronglyMeasurable a₁ a₂ ha₁ ha₂ hb₁' hb₂' hm₁' hm₂' hK x
    simpa only [hKdef, hDdef, hkap1, hkap2, hcL, Pi.one_apply, one_mul] using h
  have hfreeze1 : mdlW1 P N 1 * BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tm ρ l₁ (varphiNtj N 0 0 1) F) (Tm ρ l₂ (varphitildeNtj P N k₂ (-1) 1) G) x
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cA q.2 * D q := by
    have h := MdlBtwistFreezeFlatEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (varphiNtj N 0 0 1) (varphitildeNtj P N k₂ (-1) 1) F G (mdlW1 P N 1)
      hF hG hK hsA₁ hsA₂ x
    simpa only [hKdef, hDdef, hcA] using h
  have hfreeze2 : mdlW1 P N (1 / 2) * BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tm ρ l₁ (varphiNtj N 0 0 (1 / 2)) F)
        (Tm ρ l₂ (varphitildeNtj P N k₂ (-1) (1 / 2)) G) x
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cB q.2 * D q := by
    have h := MdlBtwistFreezeFlatEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (varphiNtj N 0 0 (1 / 2)) (varphitildeNtj P N k₂ (-1) (1 / 2)) F G (mdlW1 P N (1 / 2))
      hF hG hK hsB₁ hsB₂ x
    simpa only [hKdef, hDdef, hcB] using h
  have hint1 : (∫ t in (1 / 2 : ℝ)..1, mdlW1 P N t
        * BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
            (Tm ρ l₁ (varphiNtj N 0 1 t) F)
            (Tm ρ l₂ (varphitildeNtj P N k₂ (-1) t) G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cC q.2 * D q := by
    have h := MdlBtwistIntervalFlatEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (fun t : ℝ => varphiNtj N 0 1 t) (fun t : ℝ => varphitildeNtj P N k₂ (-1) t)
      (mdlW1 P N) F G hF hG hw₁ hwm₁ a₃ a₄ ha₃ ha₄ hb₃ hb₄ hm₃ hm₄ hK x
    simpa only [hKdef, hDdef, hkap3, hkap4, hcC] using h
  have hint2 : (∫ t in (1 / 2 : ℝ)..1, mdlW2 P N t
        * BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
            (Tm ρ l₁ (varphiNtj N 0 0 t) F)
            (Tm ρ l₂ (varphitildeNtj P N k₂ (-1) t) G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cE q.2 * D q := by
    have h := MdlBtwistIntervalFlatEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (fun t : ℝ => varphiNtj N 0 0 t) (fun t : ℝ => varphitildeNtj P N k₂ (-1) t)
      (mdlW2 P N) F G hF hG hw₂ hwm₂ a₁ a₄ ha₁ ha₄ hb₁' hb₄ hm₁' hm₄ hK x
    simpa only [hKdef, hDdef, hkap1, hkap4, hcE] using h
  have hLs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cL q.2 * D q := by
    have h := MdlFlatSummable (K := arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cL) (a := a₁) (a' := a₂) ha₁ ha₂ ha₁0 ha₂0 (Ca := 1) zero_le_one
      (fun z => by
        rw [hcL]
        exact mdl_coeff_intervalIntegral_bound (w := fun _ : ℝ => (1 : ℂ)) (Cw := 1)
          (by intro t ht; simp) zero_le_one ha₁0 ha₂0 hb₁' hb₂' z) x
    simpa only [hKdef, hDdef] using h
  have hAs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cA q.2 * D q := by
    have h := MdlFlatSummable (K := arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cA) (a := fun i : ℤ => ‖tmKer ρ l₁ (varphiNtj N 0 0 1) i‖)
      (a' := fun i : ℤ => ‖tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) 1) i‖)
      hsA₁ hsA₂ (fun i => norm_nonneg _) (fun i => norm_nonneg _) (Ca := ‖mdlW1 P N 1‖)
      (norm_nonneg _) (fun z => by rw [hcA, norm_mul, norm_mul]) x
    simpa only [hKdef, hDdef] using h
  have hBs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cB q.2 * D q := by
    have h := MdlFlatSummable (K := arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cB) (a := fun i : ℤ => ‖tmKer ρ l₁ (varphiNtj N 0 0 (1 / 2)) i‖)
      (a' := fun i : ℤ => ‖tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) (1 / 2)) i‖)
      hsB₁ hsB₂ (fun i => norm_nonneg _) (fun i => norm_nonneg _) (Ca := ‖mdlW1 P N (1 / 2)‖)
      (norm_nonneg _) (fun z => by rw [hcB, norm_mul, norm_mul]) x
    simpa only [hKdef, hDdef] using h
  have hCs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cC q.2 * D q := by
    have h := MdlFlatSummable (K := arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cC) (a := a₃) (a' := a₄) ha₃ ha₄ ha₃0 ha₄0 (Ca := Cw₁) hCw₁0
      (fun z => by
        rw [hcC]
        exact mdl_coeff_intervalIntegral_bound (w := fun t : ℝ => mdlW1 P N t) hw₁ hCw₁0
          ha₃0 ha₄0 hb₃ hb₄ z) x
    simpa only [hKdef, hDdef] using h
  have hEs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cE q.2 * D q := by
    have h := MdlFlatSummable (K := arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cE) (a := a₁) (a' := a₄) ha₁ ha₄ ha₁0 ha₄0 (Ca := Cw₂) hCw₂0
      (fun z => by
        rw [hcE]
        exact mdl_coeff_intervalIntegral_bound (w := fun t : ℝ => mdlW2 P N t) hw₂ hCw₂0
          ha₁0 ha₄0 hb₁' hb₄ z) x
    simpa only [hKdef, hDdef] using h
  have hcoef : ∀ z : ℤ × ℤ, cL z = c1 * cA z - c1 * cB z - c2 * cC z + c1 * cE z := by
    intro z
    have h := tmKerIdentLowHighEx ρ P l₁ l₂ N 0 k₂ hk₂ hN hP z.1 z.2
    have hscale : ((mdlScaleGe P 0 k₂ : ℝ) : ℂ) = ((mdlScaleFe P 0 k₂ : ℝ) : ℂ) := rfl
    simp only [hcL, hcA, hcB, hcC, hcE, hc1, hc2, hkap1, hkap2, hkap3, hkap4, mdlCoeff,
      varphiNtj_zero, varphitildeNtj_zero, Pi.one_apply, one_mul] at h ⊢
    rw [h, hscale]
    ring
  rw [hflatL, hfreeze1, hfreeze2, hint1, hint2]
  exact MdlTsumCombine D cA cB cC cE cL c1 c2 hAs hBs hCs hEs hLs hcoef

end

end Work.KMTPlan.A6
