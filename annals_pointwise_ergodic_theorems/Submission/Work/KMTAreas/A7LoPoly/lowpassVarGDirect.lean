import Mathlib
import Submission.Work.KMTAreas.A7LoPoly.dyadicCore
import Submission.Work.KMTAreas.A7G.lowpassAlphaTransferG

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7LoPoly

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar Work.KMTContract

noncomputable section

/-- **The `g`-side low-pass variational estimate, `(1+l₂)²` loss, proved directly.**

This is the *statement* of `Work.KMTAreas.A7Hi.lowpassVarG` (the paper's `(lin-2)`, the `s₂ = -u`,
`j₂ = 0` case), obtained from the dyadic core `Work.KMTAreas.A7LoPoly.lpfVarPolyLoss` by the
lacunary reindexing (`a ↦ P.natDegree · logN ⌊a n⌋`, monotone) together with the identification
`Tle ρ l₂ (varphitildeN d N 0) = kmtProj ρ l₂ (-(d · logN N))`
(`Work.KMTAreas.A7G.Tle_varphitildeN_zero_eq_kmtProj`).

The point of proving it here (rather than using `Work.KMTAreas.A7G.lowpassVarG`) is that this route
does **not** pass through the `l`-free stubs `Work.KMTAreas.A7G.chainPartLowpass` and
`Work.KMTAreas.A7Hi2.lacunaryMaxPiece`. -/
theorem lowpassVarGDirect (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Λ : NNReal) (hΛ : 1 < Λ),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (k : ℤ) (l₂ : ℕ) (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
          (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
          Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ k →
          (∀ n : ℕ, -((P.natDegree : ℤ) *
            Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
              (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (1 + (l₂ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 r hr p hp hptop Λ hΛ
  obtain ⟨CρD, hCρD, CD, hCD, hD⟩ := lpfVarPolyLoss ρ hρ hρ1 r hr p hp hptop
  refine ⟨CρD, hCρD, CD, hCD, ?_⟩
  intro k l₂ a ha ha1 f hgood hk
  -- ## the reindexing
  set m₀ : ℕ := ((P.natDegree : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a 0))).toNat with hm₀
  have hm₀Z : (m₀ : ℤ) = (P.natDegree : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a 0)) :=
    Int.toNat_of_nonneg (mul_nonneg (Int.natCast_nonneg P.natDegree)
      (Work.Analysis.EndVar.logN_nonneg _))
  have hmonoA : Monotone a := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    have h2 : Λ < a (n + 1) / a n := ha n
    have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
    have h3 : a n ≤ Λ * a n := by simpa using mul_le_mul_of_nonneg_right hΛ.le (le_of_lt hpos)
    exact le_trans h3 h1.le
  have hmonoL : Monotone (fun n => (P.natDegree : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))) :=
    fun n m hnm => mul_le_mul_of_nonneg_left
      (Work.Analysis.EndVar.logN_mono (Nat.floor_mono (hmonoA hnm))) (Int.natCast_nonneg _)
  set σ : ℕ → ℕ := fun n =>
    (((P.natDegree : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))) - ((m₀ : ℕ) : ℤ)).toNat
    with hσdef
  have hσZ : ∀ n, (σ n : ℤ)
      = (P.natDegree : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n)) - ((m₀ : ℕ) : ℤ) := by
    intro n
    rw [hσdef]
    refine Int.toNat_of_nonneg ?_
    rw [hm₀Z]
    exact sub_nonneg.mpr (hmonoL (Nat.zero_le n))
  have hσmono : Monotone σ := by
    intro n m hnm
    rw [hσdef]
    exact Int.toNat_le_toNat (sub_le_sub_right (hmonoL hnm) _)
  have hfam : ∀ n, Work.KMTAreas.A7.Tle ρ l₂
      (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f
      = Work.KMTContract.kmtProj ρ l₂ (-(((m₀ : ℕ) : ℤ) + ((σ n : ℕ) : ℤ))) f := by
    intro n
    rw [Work.KMTAreas.A7G.Tle_varphitildeN_zero_eq_kmtProj]
    congr 1
    have hn := hσZ n
    omega
  -- ## the good-major-arcs condition at the base level
  have hkm₀ : -(((m₀ : ℕ)) : ℤ) ≤ k := by
    have h0 := hk 0
    rw [hm₀Z]
    exact h0
  have hgD : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρD l₂ (-(((m₀ : ℕ)) : ℤ)) := by
    unfold Work.Analysis.IonescuWainger.GoodMajorArcs at hgood ⊢
    exact le_trans (by exact_mod_cast hkm₀) hgood
  -- ## the dyadic bound and the pass to the subsequence
  have hdy : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₂ m₀ m f x)) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (CD * (1 + (l₂ : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
    hD l₂ m₀ hgD f
  have hsub : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTContract.kmtProj ρ l₂
          (-(((m₀ : ℕ) : ℤ) + ((σ n : ℕ) : ℤ))) f x)) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => Work.KMTContract.kmtProj ρ l₂ (-(((m₀ : ℕ) : ℤ) + (m : ℤ))) f x))
        p MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.eLpNorm_mono_ennreal
      (fun x => Work.KMTAreas.A7.variationalNorm_comp_mono_le
        (fun m : ℕ => Work.KMTContract.kmtProj ρ l₂ (-(((m₀ : ℕ) : ℤ) + (m : ℤ))) f x) hσmono)
      (lt_trans zero_lt_one hp).ne' hptop.ne
  have hcongr : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
          (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTContract.kmtProj ρ l₂
          (-(((m₀ : ℕ) : ℤ) + ((σ n : ℕ) : ℤ))) f x)) := by
    funext x
    exact congrArg (fun w : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm r w)
      (funext fun n => congrFun (hfam n) x)
  rw [hcongr]
  refine (hsub.trans ?_).trans (le_of_eq rfl)
  simpa only [Work.KMTAreas.A7Hi.lpf] using hdy

end

end Work.KMTAreas.A7LoPoly
