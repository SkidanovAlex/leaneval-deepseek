import Mathlib
import Submission.Work.KMTAreas.A7.integrable_iwSymbolSet_varphiN
import Submission.Work.KMTAreas.A7.FpieceEqTm
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded
import Submission.Work.KMTAreas.A7.varphitildeNt_support_all

namespace Work.KMTAreas.A7

open MeasureTheory

/-! ## `L^∞` membership of the periodised bumps of §6

The four symbols of the KMT §6 model tuple are rescalings of the fixed cutoff `η = kmtEta`,
modulated by characters of modulus one, and hence are continuous, bounded and compactly
supported.  `Work.Analysis.IonescuWainger.memLp_periodize` then puts their periodisations in
`L^∞(ℝ/ℤ)`, because a bounded compactly supported function has only finitely many nonzero
translates over any point of the circle.
-/

/-! ### Elementary bounds for rescalings of the cutoff -/

/-- A rescaled cutoff `ξ ↦ η (a ξ)` is `C²`. -/
private lemma kmtA7_contDiff_kmtEta_rescale (a : ℝ) :
    ContDiff ℝ 2 (fun ξ : ℝ => Work.KMTContract.kmtEta (a * ξ)) :=
  (contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id)

/-- The modulations multiply the norm by `1`, so `‖φ_{N,t}‖ = ‖φ_N‖`. -/
private lemma kmtA7_norm_varphiNt_eq (N k : ℕ) (t : ℝ) (ξ : ℝ) :
    ‖varphiNt N k t ξ‖ = ‖varphiN N k ξ‖ := by
  rw [varphiNt, norm_mul, norm_ee, mul_one]

/-- The modulated bump `φ_{N,t}` is continuous. -/
private lemma kmtA7_measurable_varphiNt (N k : ℕ) (t : ℝ) : Measurable (varphiNt N k t) :=
  (contDiff_varphiNt N k t).continuous.measurable

/-- **The periodisation of the modulated bump `φ_{N,t}` is in `L^∞(ℝ/ℤ)`.**  `φ_{N,t}` is
continuous, bounded by `2`, and vanishes off the window `[-2^{k - Log N}, 2^{k - Log N}]`. -/
theorem kmtA7_memLp_periodize_varphiNt (N k : ℕ) (t : ℝ) :
    MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize (varphiNt N k t)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure := by
  refine Work.Analysis.IonescuWainger.memLp_periodize (kmtA7_measurable_varphiNt N k t)
    (R := (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
    (Real.rpow_nonneg (by norm_num) _) ?_ (C := 2) ?_
  · intro x hx
    by_contra hne
    exact absurd (varphiNt_support N k t x hne) (not_le.mpr hx)
  · intro x
    rw [kmtA7_norm_varphiNt_eq]
    exact norm_varphiN_le_two N k x

/-! ### The `d`-fold bump `φ̃_N` -/

/-- The `d`-fold rescaled bump `φ̃_N` is `C²`. -/
private lemma kmtA7_contDiff_varphitildeN (d N k : ℕ) : ContDiff ℝ 2 (varphitildeN d N k) := by
  unfold varphitildeN
  split_ifs with hk
  · exact kmtA7_contDiff_kmtEta_rescale _
  · exact (kmtA7_contDiff_kmtEta_rescale _).sub (kmtA7_contDiff_kmtEta_rescale _)

/-- The `d`-fold rescaled bump `φ̃_N` is bounded by `2` (a single cutoff value or a difference of
two of them). -/
private lemma kmtA7_norm_varphitildeN_le_two (d N k : ℕ) (ξ : ℝ) :
    ‖varphitildeN d N k ξ‖ ≤ 2 := by
  unfold varphitildeN
  split_ifs with hk
  · exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · calc ‖Work.KMTContract.kmtEta _ - Work.KMTContract.kmtEta _‖
        ≤ ‖Work.KMTContract.kmtEta _‖ + ‖Work.KMTContract.kmtEta _‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (Work.KMTContract.norm_kmtEta_le _)
          (Work.KMTContract.norm_kmtEta_le _)
      _ = 2 := by norm_num

/-- The modulation again does not change the norm. -/
private lemma kmtA7_norm_varphitildeNt_eq (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) (ξ : ℝ) :
    ‖varphitildeNt P d N k t ξ‖ = ‖varphitildeN d N k ξ‖ := by
  rw [varphitildeNt, norm_mul, norm_ee, mul_one]

/-- The modulated `d`-fold bump `φ̃_{N,t}` is continuous. -/
private lemma kmtA7_measurable_varphitildeNt (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    Measurable (varphitildeNt P d N k t) := by
  have hcont : Continuous (varphitildeNt P d N k t) := by
    unfold varphitildeNt
    exact ((kmtA7_contDiff_varphitildeN d N k).mul
      (contDiff_ee_const_mul 2 (PevalR P ((N : ℝ) * t)))).continuous
  exact hcont.measurable

/-- **The periodisation of the modulated `d`-fold bump `φ̃_{N,t}` is in `L^∞(ℝ/ℤ)`.**  It is
continuous, bounded by `2`, and vanishes off `[-2^{d(k₂ - Log N)}, 2^{d(k₂ - Log N)}]`. -/
theorem kmtA7_memLp_periodize_varphitildeNt (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize (varphitildeNt P d N k t)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure := by
  refine Work.Analysis.IonescuWainger.memLp_periodize (kmtA7_measurable_varphitildeNt P d N k t)
    (R := (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))))
    (Real.rpow_nonneg (by norm_num) _) (C := 2) ?_ ?_
  · intro x hx
    by_contra hne
    exact absurd (varphitildeNt_support_all P d N k t x hne) (not_le.mpr hx)
  · intro x
    rw [kmtA7_norm_varphitildeNt_eq]
    exact kmtA7_norm_varphitildeN_le_two d N k x

/-! ### The §6 symbols `m_* = η_{≤-2u}` and `η_{≤-2du}` -/

/-- **The periodisation of the §6 symbols is in `L^∞(ℝ/ℤ)`**: they are rescalings of the fixed
cutoff `η`, whose periodisation is already known to be bounded (`FpieceEqTm`). -/
theorem kmtA7_memLp_periodize_mStarF (u : ℕ) :
    MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize (mStarF u)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
  memLp_periodize_etaCut (-(2 * (u : ℤ)))

/-- The `d`-fold version of the same statement, for `mStargF d u = η_{≤-2du}`. -/
theorem kmtA7_memLp_periodize_mStargF (d u : ℕ) :
    MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize (mStargF d u)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
  memLp_periodize_etaCut (-((d : ℤ) * 2 * (u : ℤ)))

/-! ### The target -/

theorem kmtA7_periodize_bumps_memLp (P : Polynomial ℤ) (N k₁ k₂ : ℕ) (t : ℝ) (u : ℕ) :
    MeasureTheory.MemLp
        (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k₁ t)) ⊤
        Work.Analysis.IonescuWainger.circleMeasure ∧
    MeasureTheory.MemLp
        (Work.Analysis.IonescuWainger.periodize
          (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)) ⊤
        Work.Analysis.IonescuWainger.circleMeasure ∧
    MeasureTheory.MemLp
        (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.mStarF u)) ⊤
        Work.Analysis.IonescuWainger.circleMeasure ∧
    MeasureTheory.MemLp
        (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.mStargF P.natDegree u)) ⊤
        Work.Analysis.IonescuWainger.circleMeasure :=
  ⟨kmtA7_memLp_periodize_varphiNt N k₁ t,
   kmtA7_memLp_periodize_varphitildeNt P P.natDegree N k₂ t,
   kmtA7_memLp_periodize_mStarF u,
   kmtA7_memLp_periodize_mStargF P.natDegree u⟩

end Work.KMTAreas.A7
