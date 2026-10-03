/-
# Assembly of Case B of the small-scale model estimate of the low case of area A6

This module assembles `Work.KMTPlan.A6.lowModelVarCaseB` from

* the two *exact-height* integration-by-parts identities of §6
  (`Work.KMTPlan.A6.mdlDecayLowHighEx_core` and `Work.KMTPlan.A6.mdlDecayHighLowEx_core`), which
  rewrite the `t`-integral of the model slice as one/two boundary terms of the *modified* bumps
  plus the weighted `t`-integrals, with the `2^{-d·k}` (resp. `2^{-k}`) factors `mdlScale`,
  `mdlScaleGe`, `mdlScaleF`, `mdlScaleFG`;
* the single-scale estimate `hSS` (`Work.KMTPlan.A6.SSUShape`) applied to the frozen-`t` families
  with the modified (narrowly supported) bumps;
* the `ℓ²`-bounds for the randomised packets of the modified bump families
  (`Work.KMTPlan.A6.LowModRandL2F'`/`LowModRandL2G'`), which feed the Rademacher--Menshov
  reduction `Work.KMTPlan.A6.VrFull_TmBtwist_le_rand_abs`;
* the `V^r`-bounds of the weights `mdlW1`/`mdlW2`/`mdlW3`
  (`Work.KMTPlan.A6.weightVarBound`) and Minkowski's inequality in `t`.

The four families appearing in the low-high case are

* `lowDecayB … 0 (-1) 1` and `lowDecayB … 0 (-1) (1/2)`: the two boundary terms,
  `mdlW1 P N 1 · BtwistEx (φ_{N,0,0}(1), φ̃_{N,L,-1}(1))` and the same at `t = 1/2`;
* `lowDecayW … 1 (-1) (mdlW1 P N)`: the `W₁`-weighted integral of
  `BtwistEx (φ_{N,0,1}(t), φ̃_{N,L,-1}(t))`;
* `lowDecayW … 0 (-1) (mdlW2 P N)`: the `W₂`-weighted integral of
  `BtwistEx (φ_{N,0,0}(t), φ̃_{N,L,-1}(t))`,

and in the high-low case

* `lowDecayB … L 0 (-1) 0 1` and `lowDecayB … (-1) 0 (1/2)`: the boundary terms
  `BtwistEx (φ_{N,L,-1}(s), φ̃_{N,0,0}(s))`;
* `lowDecayW … (-1) 1 (mdlW3 P N)`: the `W₃`-weighted integral of
  `BtwistEx (φ_{N,L,-1}(t), φ̃_{N,0,1}(t))`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.mdlDecayHighLowEx_core
import Submission.Work.KMTPlan.A6.MdlCwIntegIdentI
import Submission.Work.KMTPlan.A6.MdlWeightVarBound
import Submission.Work.KMTPlan.A6.varNorm_integral_le
import Submission.Work.KMTPlan.A6.variationalNorm_prod_le
import Submission.Work.KMTPlan.A6.VrFull_TmBtwist_le_rand_abs

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

/-! ## The four families of the integration-by-parts decomposition -/

/-- The **frozen boundary term** of the integration-by-parts identity: the clamped family
`n ↦ mdlW1 P ⌊a n⌋ s · BtwistEx_{m_*}(Tm (φ_{N,k₁,j₁}(s)) f, Tm (φ̃_{N,k₂,j₂}(s)) g)`. -/
noncomputable def lowDecayB (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (s : ℝ) (w : ℕ → ℂ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then
      w n * BtwistEx ρ P l₁ l₂
        (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (Tm ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ s) f)
        (Tm ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ s) g) x
    else 0

/-- The **weighted `t`-integral term** of the integration-by-parts identity: the clamped family
`n ↦ ∫_{1/2}^1 w(n,t) · BtwistEx_{m_*}(Tm (φ_{N,k₁,j₁}(t)) f, Tm (φ̃_{N,k₂,j₂}(t)) g) dt`. -/
noncomputable def lowDecayW (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (w : ℕ → ℝ → ℂ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then
      ∫ t in (1 / 2 : ℝ)..1, w n t * BtwistEx ρ P l₁ l₂
        (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (Tm ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t) f)
        (Tm ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) g) x
    else 0

/-! ## The pointwise identity of the low-high case -/

/-- **The integration-by-parts identity (ii) for the model tuple in the low-high case**
`(k₁,k₂) = (0,L)`.  The model tuple is the `mdlScale P L · mdlIota`-multiple of the difference of
its two frozen boundary terms minus the `mdlScaleGe P 0 L`-multiple of the `W₁`-weighted integral
of the modified pair plus the `mdlScale P L · mdlIota`-multiple of the `W₂`-weighted integral. -/
theorem lowModel_eq_decayLowHigh (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ L : ℕ) (hL : 1 ≤ L) (hLc : lcL l₁ l₂ 0 L = L)
    (hN : ∀ n : ℕ, 1 ≤ Nat.floor (a n))
    (hP : ∀ n : ℕ, lowSmallSet ρ C₀ a l₁ l₂ 0 L n →
      ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, PderivR P ((Nat.floor (a n) : ℝ) * t) ≠ 0)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (n : ℕ) (x : ℤ) :
    lowModel ρ P C₀ a f g l₁ l₂ 0 L n x
      = (mdlScale P L : ℂ) * mdlIota
          * (lowDecayB ρ P C₀ a f g l₁ l₂ 0 L 0 (-1) 1 (fun n => mdlW1 P (Nat.floor (a n)) 1) n x
              - lowDecayB ρ P C₀ a f g l₁ l₂ 0 L 0 (-1) (1 / 2)
                  (fun n => mdlW1 P (Nat.floor (a n)) (1 / 2)) n x)
        - (mdlScaleGe P 0 L : ℂ)
            * lowDecayW ρ P C₀ a f g l₁ l₂ 0 L 1 (-1) (fun n t => mdlW1 P (Nat.floor (a n)) t) n x
        + (mdlScale P L : ℂ) * mdlIota
            * lowDecayW ρ P C₀ a f g l₁ l₂ 0 L 0 (-1) (fun n t => mdlW2 P (Nat.floor (a n)) t) n x := by
  classical
  rw [lowModel_eq_integral_slice]
  by_cases hset : lowSmallSet ρ C₀ a l₁ l₂ 0 L n
  · -- the core, instantiated at `N = ⌊a n⌋` and `u = uScale ρ L`
    obtain ⟨a₁, ha₁, hb₁, hm₁⟩ :=
      tmKerPackage_varphiNtj ρ l₁ (Nat.floor (a n)) 0 0 (jmem 0 (Or.inr (Or.inl rfl))) (Or.inr le_rfl)
    obtain ⟨a₂, ha₂, hb₂, hm₂⟩ :=
      tmKerPackage_varphitildeNtj ρ l₂ P (Nat.floor (a n)) L 0 (jmem 0 (Or.inr (Or.inl rfl))) (Or.inr le_rfl)
    obtain ⟨a₃, ha₃, hb₃, hm₃⟩ :=
      tmKerPackage_varphiNtj ρ l₁ (Nat.floor (a n)) 0 1 (jmem 1 (Or.inr (Or.inr rfl))) (Or.inr (by norm_num))
    obtain ⟨a₄, ha₄, hb₄, hm₄⟩ :=
      tmKerPackage_varphitildeNtj ρ l₂ P (Nat.floor (a n)) L (-1) (jmem (-1) (Or.inl rfl)) (Or.inl (by omega))
    have hb₁' : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
        ‖tmKer ρ l₁ (varphiNt (Nat.floor (a n)) 0 t) i‖ ≤ a₁ i :=
      fun t ht i => by simpa only [varphiNtj_zero] using hb₁ t ht i
    have hb₂' : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
        ‖tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) L t) i‖ ≤ a₂ i :=
      fun t ht i => by simpa only [varphitildeNtj_zero] using hb₂ t ht i
    have hm₁' : ∀ i : ℤ, AEStronglyMeasurable
        (fun t : ℝ => tmKer ρ l₁ (varphiNt (Nat.floor (a n)) 0 t) i) volume :=
      fun i => by simpa only [varphiNtj_zero] using (hm₁ i).aestronglyMeasurable
    have hm₂' : ∀ i : ℤ, AEStronglyMeasurable
        (fun t : ℝ => tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) L t) i) volume :=
      fun i => by simpa only [varphitildeNtj_zero] using (hm₂ i).aestronglyMeasurable
    obtain ⟨Cw₁, hCw₁0, hw₁⟩ := mdl_W1_bound P (Nat.floor (a n)) (hP n hset)
    obtain ⟨Cw₂, hCw₂0, hw₂⟩ := mdl_W2_bound P (Nat.floor (a n)) (hP n hset)
    have hwm₁ : AEStronglyMeasurable (fun t : ℝ => mdlW1 P (Nat.floor (a n)) t) volume :=
      (measurable_mdlW1 P (Nat.floor (a n))).aestronglyMeasurable
    have hwm₂ : AEStronglyMeasurable (fun t : ℝ => mdlW2 P (Nat.floor (a n)) t) volume :=
      (measurable_mdlW2 P (Nat.floor (a n))).aestronglyMeasurable
    have hK : Summable fun p : ℤ × ℤ => ‖arithKerMX ρ P l₁ l₂
        (mStarF (uScale ρ L)) (mStargF P.natDegree (uScale ρ L)) p.1 p.2‖ := by
      rw [← hLc]
      exact summable_arithKerMX ρ P l₁ l₂ (uScale ρ (lcL l₁ l₂ 0 L))
    obtain ⟨Cf, hCf⟩ : Work.KMTAreas.A5.BoundedZ f :=
      Work.KMTAreas.A5.boundedZ_of_memLp (p := 2) (by norm_num) hf
    obtain ⟨Cg, hCg⟩ : Work.KMTAreas.A5.BoundedZ g :=
      Work.KMTAreas.A5.boundedZ_of_memLp (p := 2) (by norm_num) hg
    have hcore := mdlDecayLowHighEx_core ρ P l₁ l₂ (Nat.floor (a n)) L hL (hN n)
      (uScale ρ L) f g Cf Cg Cw₁ Cw₂ hCf hCg hCw₁0 hw₁ hwm₁ hCw₂0 hw₂ hwm₂
      (hP n hset) hK a₁ a₂ a₃ a₄ ha₁ ha₂ ha₃ ha₄ hb₁' hb₂' hb₃ hb₄
      hm₁' hm₂' (fun i => (hm₃ i).aestronglyMeasurable) (fun i => (hm₄ i).aestronglyMeasurable) x
    rw [show (∫ t in (1 / 2 : ℝ)..1, lowModelSlice ρ P C₀ a f g l₁ l₂ 0 L t n x)
        = ∫ t in (1 / 2 : ℝ)..1, BtwistEx ρ P l₁ l₂
            (mStarF (uScale ρ L)) (mStargF P.natDegree (uScale ρ L))
            (Tm ρ l₁ (varphiNtj (Nat.floor (a n)) 0 0 t) f)
            (Tm ρ l₂ (varphitildeNtj P (Nat.floor (a n)) L 0 t) g) x from by
      refine intervalIntegral.integral_congr fun t _ => ?_
      (rw [lowModelSlice, if_pos hset, hLc, varphiNtj_zero, varphitildeNtj_zero])]
    rw [hcore]
    simp only [lowDecayB, lowDecayW, hset, if_true]
    rw [hLc]
  · have hz : (∫ t in (1 / 2 : ℝ)..1, lowModelSlice ρ P C₀ a f g l₁ l₂ 0 L t n x) = 0 := by
      simp only [lowModelSlice, hset, if_false, intervalIntegral.integral_zero]
    rw [hz]
    simp only [lowDecayB, lowDecayW, hset, if_false]
    ring


/-! ## The pointwise identity of the high-low case -/

/-- **The integration-by-parts identity (i) for the model tuple in the high-low case**
`(k₁,k₂) = (L,0)`. -/
theorem lowModel_eq_decayHighLow (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ L : ℕ) (hL : 1 ≤ L) (hLc : lcL l₁ l₂ L 0 = L)
    (hN : ∀ n : ℕ, 1 ≤ Nat.floor (a n))
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (n : ℕ) (x : ℤ) :
    lowModel ρ P C₀ a f g l₁ l₂ L 0 n x
      = (mdlScaleF L : ℂ) * mdlIota
          * (lowDecayB ρ P C₀ a f g l₁ l₂ L 0 (-1) 0 1 (fun _ => 1) n x
              - lowDecayB ρ P C₀ a f g l₁ l₂ L 0 (-1) 0 (1 / 2) (fun _ => 1) n x)
        - (mdlScaleFG P L 0 : ℂ)
            * lowDecayW ρ P C₀ a f g l₁ l₂ L 0 (-1) 1
                (fun n t => mdlW3 P (Nat.floor (a n)) t) n x := by
  classical
  rw [lowModel_eq_integral_slice]
  by_cases hset : lowSmallSet ρ C₀ a l₁ l₂ L 0 n
  · obtain ⟨a₁, ha₁, hb₁, hm₁⟩ :=
      tmKerPackage_varphiNtj ρ l₁ (Nat.floor (a n)) L 0 (jmem 0 (Or.inr (Or.inl rfl))) (Or.inl (by omega))
    obtain ⟨a₂, ha₂, hb₂, hm₂⟩ :=
      tmKerPackage_varphitildeNtj ρ l₂ P (Nat.floor (a n)) 0 0 (jmem 0 (Or.inr (Or.inl rfl))) (Or.inr le_rfl)
    obtain ⟨a₃, ha₃, hb₃, hm₃⟩ :=
      tmKerPackage_varphiNtj ρ l₁ (Nat.floor (a n)) L (-1) (jmem (-1) (Or.inl rfl)) (Or.inl (by omega))
    obtain ⟨a₄, ha₄, hb₄, hm₄⟩ :=
      tmKerPackage_varphitildeNtj ρ l₂ P (Nat.floor (a n)) 0 1 (jmem 1 (Or.inr (Or.inr rfl))) (Or.inr (by norm_num))
    have hb₁' : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
        ‖tmKer ρ l₁ (varphiNt (Nat.floor (a n)) L t) i‖ ≤ a₁ i :=
      fun t ht i => by simpa only [varphiNtj_zero] using hb₁ t ht i
    have hb₂' : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
        ‖tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) i‖ ≤ a₂ i :=
      fun t ht i => by simpa only [varphitildeNtj_zero] using hb₂ t ht i
    have hm₁' : ∀ i : ℤ, AEStronglyMeasurable
        (fun t : ℝ => tmKer ρ l₁ (varphiNt (Nat.floor (a n)) L t) i) volume :=
      fun i => by simpa only [varphiNtj_zero] using (hm₁ i).aestronglyMeasurable
    have hm₂' : ∀ i : ℤ, AEStronglyMeasurable
        (fun t : ℝ => tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) i) volume :=
      fun i => by simpa only [varphitildeNtj_zero] using (hm₂ i).aestronglyMeasurable
    obtain ⟨Cw, hCw0, hw⟩ := mdl_W3_bound P (Nat.floor (a n))
    have hwm : AEStronglyMeasurable (fun t : ℝ => mdlW3 P (Nat.floor (a n)) t) volume :=
      (mdl_W3_continuous P (Nat.floor (a n))).measurable.aestronglyMeasurable
    have hK : Summable fun p : ℤ × ℤ => ‖arithKerMX ρ P l₁ l₂
        (mStarF (uScale ρ L)) (mStargF P.natDegree (uScale ρ L)) p.1 p.2‖ := by
      rw [← hLc]
      exact summable_arithKerMX ρ P l₁ l₂ (uScale ρ (lcL l₁ l₂ L 0))
    obtain ⟨Cf, hCf⟩ : Work.KMTAreas.A5.BoundedZ f :=
      Work.KMTAreas.A5.boundedZ_of_memLp (p := 2) (by norm_num) hf
    obtain ⟨Cg, hCg⟩ : Work.KMTAreas.A5.BoundedZ g :=
      Work.KMTAreas.A5.boundedZ_of_memLp (p := 2) (by norm_num) hg
    have hcore := mdlDecayHighLowEx_core ρ P l₁ l₂ (Nat.floor (a n)) L hL (hN n)
      (uScale ρ L) f g Cf Cg Cw hCf hCg hCw0 hw hwm
      (MdlCwIntegIdentI P (Nat.floor (a n)) L (hN n) hL) hK
      a₁ a₂ a₃ a₄ ha₁ ha₂ ha₃ ha₄ hb₁' hb₂' hb₃ hb₄
      hm₁' hm₂' (fun i => (hm₃ i).aestronglyMeasurable) (fun i => (hm₄ i).aestronglyMeasurable) x
    rw [show (∫ t in (1 / 2 : ℝ)..1, lowModelSlice ρ P C₀ a f g l₁ l₂ L 0 t n x)
        = ∫ t in (1 / 2 : ℝ)..1, BtwistEx ρ P l₁ l₂
            (mStarF (uScale ρ L)) (mStargF P.natDegree (uScale ρ L))
            (Tm ρ l₁ (varphiNt (Nat.floor (a n)) L t) f)
            (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) g) x from by
      refine intervalIntegral.integral_congr fun t _ => ?_
      (rw [lowModelSlice, if_pos hset, hLc])]
    rw [hcore]
    simp only [lowDecayB, lowDecayW, hset, if_true]
    rw [hLc]
    ring
  · have hz : (∫ t in (1 / 2 : ℝ)..1, lowModelSlice ρ P C₀ a f g l₁ l₂ L 0 t n x) = 0 := by
      simp only [lowModelSlice, hset, if_false, intervalIntegral.integral_zero]
    rw [hz]
    simp only [lowDecayB, lowDecayW, hset, if_false]
    ring

end

end Work.KMTPlan.A6
