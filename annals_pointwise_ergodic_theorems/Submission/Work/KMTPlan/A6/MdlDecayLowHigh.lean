import Mathlib
import Submission.Work.KMTPlan.A6.MdlLowHighFlat
import Submission.Work.KMTPlan.A6.MdlKerIdentLowHigh

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7

/-- **The operator-level integration-by-parts identity (ii) at `(k₁,k₂) = (0,k₂)`, `k₂ ≥ 1`.**
This is the core of `MdlDecayLowHigh`: the `t`-integral of the model tuple with the modulated
bumps `(φ_{N,t}, φ̃_{N,t})` equals the weighted boundary terms of the modified bumps minus the
`W₁`-weighted `t`-integral of the modified pair, plus the `W₂`-weighted integral of
`φ_{N,t} ⊗ φ̃_{N,t,-1}`.  The four majorants `a₁, …, a₄`, the weight bounds `Cw₁`, `Cw₂` and the
`hP` non-degeneracy hypothesis are the inputs that make every series and integral absolutely
convergent. -/
theorem mdlDecayLowHigh_core
    (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ N k₂ : ℕ) (hk₂ : 1 ≤ k₂) (hN : 1 ≤ N) (u : ℕ)
    (F G : ℤ → ℂ) (CF CG Cw₁ Cw₂ : ℝ)
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hCw₁0 : 0 ≤ Cw₁) (hw₁ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ‖mdlW1 P N t‖ ≤ Cw₁)
    (hwm₁ : AEStronglyMeasurable (fun t : ℝ => mdlW1 P N t) (volume : MeasureTheory.Measure ℝ))
    (hCw₂0 : 0 ≤ Cw₂) (hw₂ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ‖mdlW2 P N t‖ ≤ Cw₂)
    (hwm₂ : AEStronglyMeasurable (fun t : ℝ => mdlW2 P N t) (volume : MeasureTheory.Measure ℝ))
    (hP : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, PderivR P ((N : ℝ) * t) ≠ 0)
    (hK : Summable fun p : ℤ × ℤ =>
      ‖mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) p.1 p.2‖)
    (a₁ a₂ a₃ a₄ : ℤ → ℝ) (ha₁ : Summable a₁) (ha₂ : Summable a₂) (ha₃ : Summable a₃)
    (ha₄ : Summable a₄)
    (hb₁ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖mdlIWKer ρ l₁ (varphiNt N 0 t) i‖ ≤ a₁ i)
    (hb₂ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t) i‖ ≤ a₂ i)
    (hb₃ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖mdlIWKer ρ l₁ (varphiNtj N 0 1 t) i‖ ≤ a₃ i)
    (hb₄ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) t) i‖ ≤ a₄ i)
    (hm₁ : ∀ i : ℤ, AEStronglyMeasurable (fun t : ℝ => mdlIWKer ρ l₁ (varphiNt N 0 t) i) volume)
    (hm₂ : ∀ i : ℤ, AEStronglyMeasurable
      (fun t : ℝ => mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t) i) volume)
    (hm₃ : ∀ i : ℤ, AEStronglyMeasurable (fun t : ℝ => mdlIWKer ρ l₁ (varphiNtj N 0 1 t) i) volume)
    (hm₄ : ∀ i : ℤ, AEStronglyMeasurable
      (fun t : ℝ => mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) t) i) volume)
    (x : ℤ) :
    (∫ t in (1 / 2 : ℝ)..1,
        Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
          (Tle ρ l₁ (varphiNtj N 0 0 t) F) (Tle ρ l₂ (varphitildeNtj P N k₂ 0 t) G) x)
      = (mdlScale P k₂ : ℂ) * mdlIota
          * (mdlW1 P N 1 * Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
                (Tle ρ l₁ (varphiNtj N 0 0 1) F)
                (Tle ρ l₂ (varphitildeNtj P N k₂ (-1) 1) G) x
              - mdlW1 P N (1 / 2) * Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
                (Tle ρ l₁ (varphiNtj N 0 0 (1 / 2)) F)
                (Tle ρ l₂ (varphitildeNtj P N k₂ (-1) (1 / 2)) G) x)
        - (mdlScaleGe P 0 k₂ : ℂ)
            * (∫ t in (1 / 2 : ℝ)..1, mdlW1 P N t
                * Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
                    (Tle ρ l₁ (varphiNtj N 0 1 t) F)
                    (Tle ρ l₂ (varphitildeNtj P N k₂ (-1) t) G) x)
        + (mdlScale P k₂ : ℂ) * mdlIota
            * (∫ t in (1 / 2 : ℝ)..1, mdlW2 P N t
                * Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
                    (Tle ρ l₁ (varphiNtj N 0 0 t) F)
                    (Tle ρ l₂ (varphitildeNtj P N k₂ (-1) t) G) x) := by
  classical
  have hI : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hI1 : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have ha₁0 : ∀ i : ℤ, 0 ≤ a₁ i := fun i => le_trans (norm_nonneg _) (hb₁ (1/2) hI i)
  have ha₂0 : ∀ i : ℤ, 0 ≤ a₂ i := fun i => le_trans (norm_nonneg _) (hb₂ (1/2) hI i)
  have ha₃0 : ∀ i : ℤ, 0 ≤ a₃ i := fun i => le_trans (norm_nonneg _) (hb₃ (1/2) hI i)
  have ha₄0 : ∀ i : ℤ, 0 ≤ a₄ i := fun i => le_trans (norm_nonneg _) (hb₄ (1/2) hI i)
  have hb₁' : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖mdlIWKer ρ l₁ (varphiNtj N 0 0 t) i‖ ≤ a₁ i := by
    intro t ht i; simpa only [varphiNtj_zero] using hb₁ t ht i
  have hb₂' : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖mdlIWKer ρ l₂ (varphitildeNtj P N k₂ 0 t) i‖ ≤ a₂ i := by
    intro t ht i; simpa only [varphitildeNtj_zero] using hb₂ t ht i
  have hm₁' : ∀ i : ℤ, AEStronglyMeasurable
      (fun t : ℝ => mdlIWKer ρ l₁ (varphiNtj N 0 0 t) i) volume := by
    intro i; simpa only [varphiNtj_zero] using hm₁ i
  have hm₂' : ∀ i : ℤ, AEStronglyMeasurable
      (fun t : ℝ => mdlIWKer ρ l₂ (varphitildeNtj P N k₂ 0 t) i) volume := by
    intro i; simpa only [varphitildeNtj_zero] using hm₂ i
  have hsA₁ : Summable fun i : ℤ => ‖mdlIWKer ρ l₁ (varphiNtj N 0 0 1) i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₁' 1 hI1 i) ha₁
  have hsA₂ : Summable fun i : ℤ => ‖mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) 1) i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₄ 1 hI1 i) ha₄
  have hsB₁ : Summable fun i : ℤ => ‖mdlIWKer ρ l₁ (varphiNtj N 0 0 (1 / 2)) i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₁' (1/2) hI i) ha₁
  have hsB₂ : Summable fun i : ℤ => ‖mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) (1 / 2)) i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₄ (1/2) hI i) ha₄
  set K : ℤ → ℤ → ℂ := mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) with hKdef
  set kap1 : ℝ → ℤ → ℂ := fun t i => mdlIWKer ρ l₁ (varphiNtj N 0 0 t) i with hkap1
  set kap2 : ℝ → ℤ → ℂ := fun t i => mdlIWKer ρ l₂ (varphitildeNtj P N k₂ 0 t) i with hkap2
  set kap3 : ℝ → ℤ → ℂ := fun t i => mdlIWKer ρ l₁ (varphiNtj N 0 1 t) i with hkap3
  set kap4 : ℝ → ℤ → ℂ := fun t i => mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) t) i with hkap4
  set D : (ℤ × ℤ) × (ℤ × ℤ) → ℂ := fun q => mdlKFG K F G x q.1 q.2 with hDdef
  set cL : ℤ × ℤ → ℂ := mdlCoeff (fun _ => (1 : ℂ)) kap1 kap2 with hcL
  set cA : ℤ × ℤ → ℂ := fun z => mdlW1 P N 1 *
      (mdlIWKer ρ l₁ (varphiNtj N 0 0 1) z.1
        * mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) 1) z.2) with hcA
  set cB : ℤ × ℤ → ℂ := fun z => mdlW1 P N (1 / 2) *
      (mdlIWKer ρ l₁ (varphiNtj N 0 0 (1 / 2)) z.1
        * mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) (1 / 2)) z.2) with hcB
  set cC : ℤ × ℤ → ℂ := mdlCoeff (fun t => mdlW1 P N t) kap3 kap4 with hcC
  set cE : ℤ × ℤ → ℂ := mdlCoeff (fun t => mdlW2 P N t) kap1 kap4 with hcE
  set c1 : ℂ := (mdlScale P k₂ : ℂ) * mdlIota with hc1
  set c2 : ℂ := (mdlScaleGe P 0 k₂ : ℂ) with hc2
  have hflatL : (∫ t in (1 / 2 : ℝ)..1,
        Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
          (Tle ρ l₁ (varphiNtj N 0 0 t) F) (Tle ρ l₂ (varphitildeNtj P N k₂ 0 t) G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cL q.2 * D q := by
    have h := MdlBtwistIntervalFlat (Cw := 1) ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (fun t : ℝ => varphiNtj N 0 0 t) (fun t : ℝ => varphitildeNtj P N k₂ 0 t)
      (fun _ : ℝ => (1 : ℂ)) F G hF hG (fun t ht => by simp)
      measurable_const.aestronglyMeasurable a₁ a₂ ha₁ ha₂ hb₁' hb₂' hm₁' hm₂' hK x
    simpa only [hKdef, hDdef, hkap1, hkap2, hcL, Pi.one_apply, one_mul] using h
  have hfreeze1 : mdlW1 P N 1 * Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tle ρ l₁ (varphiNtj N 0 0 1) F) (Tle ρ l₂ (varphitildeNtj P N k₂ (-1) 1) G) x
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cA q.2 * D q := by
    have h := MdlBtwistFreezeFlat ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (varphiNtj N 0 0 1) (varphitildeNtj P N k₂ (-1) 1) F G (mdlW1 P N 1)
      hF hG hK hsA₁ hsA₂ x
    simpa only [hKdef, hDdef, hcA] using h
  have hfreeze2 : mdlW1 P N (1 / 2) * Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tle ρ l₁ (varphiNtj N 0 0 (1 / 2)) F)
        (Tle ρ l₂ (varphitildeNtj P N k₂ (-1) (1 / 2)) G) x
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cB q.2 * D q := by
    have h := MdlBtwistFreezeFlat ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (varphiNtj N 0 0 (1 / 2)) (varphitildeNtj P N k₂ (-1) (1 / 2)) F G (mdlW1 P N (1 / 2))
      hF hG hK hsB₁ hsB₂ x
    simpa only [hKdef, hDdef, hcB] using h
  have hint1 : (∫ t in (1 / 2 : ℝ)..1, mdlW1 P N t
        * Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
            (Tle ρ l₁ (varphiNtj N 0 1 t) F)
            (Tle ρ l₂ (varphitildeNtj P N k₂ (-1) t) G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cC q.2 * D q := by
    have h := MdlBtwistIntervalFlat ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (fun t : ℝ => varphiNtj N 0 1 t) (fun t : ℝ => varphitildeNtj P N k₂ (-1) t)
      (mdlW1 P N) F G hF hG hw₁ hwm₁ a₃ a₄ ha₃ ha₄ hb₃ hb₄ hm₃ hm₄ hK x
    simpa only [hKdef, hDdef, hkap3, hkap4, hcC] using h
  have hint2 : (∫ t in (1 / 2 : ℝ)..1, mdlW2 P N t
        * Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
            (Tle ρ l₁ (varphiNtj N 0 0 t) F)
            (Tle ρ l₂ (varphitildeNtj P N k₂ (-1) t) G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cE q.2 * D q := by
    have h := MdlBtwistIntervalFlat ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (fun t : ℝ => varphiNtj N 0 0 t) (fun t : ℝ => varphitildeNtj P N k₂ (-1) t)
      (mdlW2 P N) F G hF hG hw₂ hwm₂ a₁ a₄ ha₁ ha₄ hb₁' hb₄ hm₁' hm₄ hK x
    simpa only [hKdef, hDdef, hkap1, hkap4, hcE] using h
  have hLs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cL q.2 * D q := by
    have h := MdlFlatSummable (K := mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cL) (a := a₁) (a' := a₂) ha₁ ha₂ ha₁0 ha₂0 (Ca := 1) zero_le_one
      (fun z => by
        rw [hcL]
        exact mdl_coeff_intervalIntegral_bound (w := fun _ : ℝ => (1 : ℂ)) (Cw := 1)
          (by intro t ht; simp) zero_le_one ha₁0 ha₂0 hb₁' hb₂' z) x
    simpa only [hKdef, hDdef] using h
  have hAs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cA q.2 * D q := by
    have h := MdlFlatSummable (K := mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cA) (a := fun i : ℤ => ‖mdlIWKer ρ l₁ (varphiNtj N 0 0 1) i‖)
      (a' := fun i : ℤ => ‖mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) 1) i‖)
      hsA₁ hsA₂ (fun i => norm_nonneg _) (fun i => norm_nonneg _) (Ca := ‖mdlW1 P N 1‖)
      (norm_nonneg _) (fun z => by rw [hcA, norm_mul, norm_mul]) x
    simpa only [hKdef, hDdef] using h
  have hBs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cB q.2 * D q := by
    have h := MdlFlatSummable (K := mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cB) (a := fun i : ℤ => ‖mdlIWKer ρ l₁ (varphiNtj N 0 0 (1 / 2)) i‖)
      (a' := fun i : ℤ => ‖mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) (1 / 2)) i‖)
      hsB₁ hsB₂ (fun i => norm_nonneg _) (fun i => norm_nonneg _) (Ca := ‖mdlW1 P N (1 / 2)‖)
      (norm_nonneg _) (fun z => by rw [hcB, norm_mul, norm_mul]) x
    simpa only [hKdef, hDdef] using h
  have hCs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cC q.2 * D q := by
    have h := MdlFlatSummable (K := mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cC) (a := a₃) (a' := a₄) ha₃ ha₄ ha₃0 ha₄0 (Ca := Cw₁) hCw₁0
      (fun z => by
        rw [hcC]
        exact mdl_coeff_intervalIntegral_bound (w := fun t : ℝ => mdlW1 P N t) hw₁ hCw₁0
          ha₃0 ha₄0 hb₃ hb₄ z) x
    simpa only [hKdef, hDdef] using h
  have hEs : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cE q.2 * D q := by
    have h := MdlFlatSummable (K := mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      hF hG hK (c := cE) (a := a₁) (a' := a₄) ha₁ ha₄ ha₁0 ha₄0 (Ca := Cw₂) hCw₂0
      (fun z => by
        rw [hcE]
        exact mdl_coeff_intervalIntegral_bound (w := fun t : ℝ => mdlW2 P N t) hw₂ hCw₂0
          ha₁0 ha₄0 hb₁' hb₄ z) x
    simpa only [hKdef, hDdef] using h
  have hcoef : ∀ z : ℤ × ℤ, cL z = c1 * cA z - c1 * cB z - c2 * cC z + c1 * cE z := by
    intro z
    have h := MdlKerIdentLowHigh ρ P l₁ l₂ N 0 k₂ hk₂ hN hP z.1 z.2
    have hscale : ((mdlScaleGe P 0 k₂ : ℝ) : ℂ) = ((mdlScaleFe P 0 k₂ : ℝ) : ℂ) := rfl
    simp only [hcL, hcA, hcB, hcC, hcE, hc1, hc2, hkap1, hkap2, hkap3, hkap4, mdlCoeff,
      varphiNtj_zero, varphitildeNtj_zero, Pi.one_apply, one_mul] at h ⊢
    rw [h, hscale]
    ring
  rw [hflatL, hfreeze1, hfreeze2, hint1, hint2]
  exact MdlTsumCombine D cA cB cC cE cL c1 c2 hAs hBs hCs hEs hLs hcoef

theorem MdlDecayLowHigh (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₂ : ℕ) (hk₂ : 1 ≤ k₂) (hf : ∀ x : ℤ, Complex.normSq (f x) ≤ 1)
    (hg : ∀ x : ℤ, Complex.normSq (g x) ≤ 1)
    (hN : ∀ n : ℕ, 1 ≤ Nat.floor (a n))
    (hP : ∀ n : ℕ, 1 ≤ Nat.floor (a n) → ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      Work.KMTPlan.A6.PderivR P ((Nat.floor (a n) : ℝ) * t) ≠ 0) :
    Work.KMTPlan.A6.mdlPartJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 0
      = fun n x => (Work.KMTPlan.A6.mdlScale P k₂ : ℂ) * Work.KMTPlan.A6.mdlIota
            * (Work.KMTPlan.A6.mdlSliceW ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1)
                  (fun n t => Work.KMTPlan.A6.mdlW1 P (Nat.floor (a n)) t) 1 n x
              - Work.KMTPlan.A6.mdlSliceW ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1)
                  (fun n t => Work.KMTPlan.A6.mdlW1 P (Nat.floor (a n)) t) (1 / 2) n x)
        - (Work.KMTPlan.A6.mdlScaleGe P 0 k₂ : ℂ)
            * Work.KMTPlan.A6.mdlWInt ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1)
                (fun n t => Work.KMTPlan.A6.mdlW1 P (Nat.floor (a n)) t) n x
        + (Work.KMTPlan.A6.mdlScale P k₂ : ℂ) * Work.KMTPlan.A6.mdlIota
            * Work.KMTPlan.A6.mdlWInt ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1)
                (fun n t => Work.KMTPlan.A6.mdlW2 P (Nat.floor (a n)) t) n x := by
  funext n x
  by_cases hcore : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
  · obtain ⟨CF, hCF⟩ := mdl_mdlF_bounded ρ (uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ hf
    obtain ⟨CG, hCG⟩ := mdl_mdlG_bounded ρ P (uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₂ hg
    obtain ⟨Cw₁, hCw₁0, hw₁⟩ := mdl_W1_bound P (Nat.floor (a n)) (hP n (hN n))
    obtain ⟨Cw₂, hCw₂0, hw₂⟩ := mdl_W2_bound P (Nat.floor (a n)) (hP n (hN n))
    have hwm₁ : AEStronglyMeasurable (fun t : ℝ => mdlW1 P (Nat.floor (a n)) t) volume :=
      (measurable_mdlW1 P (Nat.floor (a n))).aestronglyMeasurable
    have hwm₂ : AEStronglyMeasurable (fun t : ℝ => mdlW2 P (Nat.floor (a n)) t) volume :=
      (measurable_mdlW2 P (Nat.floor (a n))).aestronglyMeasurable
    have hK : Summable fun p : ℤ × ℤ =>
        ‖mdlBtwK ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max 0 k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max 0 k₂)))) p.1 p.2‖ :=
      mdl_summable_mdlBtwK_mStarF ρ P l₁ l₂ (uScale ρ (max (max l₁ l₂) (max 0 k₂)))
    obtain ⟨a₁, ha₁, hb₁, hm₁⟩ := MdlKerVarphiNt ρ l₁ (Nat.floor (a n)) 0
    obtain ⟨a₂, ha₂, hb₂, hm₂⟩ := MdlKerVarphitildeNt ρ l₂ P.natDegree (Nat.floor (a n)) k₂ P
    obtain ⟨_, a₃, ha₃, hb₃, hm₃⟩ := mdlKerVarphiNtjOne ρ l₁ (Nat.floor (a n)) 0
    obtain ⟨_, a₄, ha₄, hb₄, hm₄⟩ := mdlKerVarphitildeNtjNeg ρ l₂ P (Nat.floor (a n)) k₂ hk₂
    rw [mdlPartJ, if_pos hcore]
    simp only [mdlSliceW, mdlWInt, if_pos hcore]
    exact mdlDecayLowHigh_core ρ P l₁ l₂ (Nat.floor (a n)) k₂ hk₂ (hN n)
      (uScale ρ (max (max l₁ l₂) (max 0 k₂)))
      (mdlF ρ (uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ f)
      (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₂ g)
      CF CG Cw₁ Cw₂ hCF hCG hCw₁0 hw₁ hwm₁ hCw₂0 hw₂ hwm₂ (hP n (hN n)) hK
      a₁ a₂ a₃ a₄ ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃ hb₄
      (fun i => (hm₁ i).aestronglyMeasurable) (fun i => (hm₂ i).aestronglyMeasurable)
      (fun i => (hm₃ i).aestronglyMeasurable) (fun i => (hm₄ i).aestronglyMeasurable) x
  · rw [mdlPartJ_eq_zero_of_not_core ρ P C₀ a f g l₁ l₂ 0 k₂ 0 0 n x hcore]
    simp only [mdlSliceW, mdlWInt, if_neg hcore]
    ring

end Work.KMTPlan.A6
