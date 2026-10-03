/-
# The modulated height-`0` "ball" family: vocabulary

This module fixes the definitions used by the target
`Submission/Work/KMTPlan/A6/ballVarBound.lean` (`Work.KMTPlan.A6.ballVarBound`) and its sibling
`Submission/Work/KMTPlan/A6/ballVarBoundBdd.lean`.

The family under study is, for a `Λ`-lacunary scale family `N_n = ⌊a n⌋`, a modulation parameter
`t ∈ [1/2,1]` and an arbitrary input `h : ℤ → ℂ`,

  `n ↦ Tle ρ 0 (φ̃_{N_n,t}) h`,  `φ̃_{N,t} = varphitildeNtj P N 0 0 t = φ̃_N · e(P(Nt)·)`.

The target is proved by splitting the bump into its *unmodulated* part `φ̃_N` (handled by the
proved lacunary dilation estimate `Work.KMTAreas.A7G.plainBumpVarG`) and the *deviation*

  `ballDev P N t = φ̃_{N,t} - φ̃_N = φ̃_N · (e(P(Nt)·) - 1)`,

whose symbol vanishes at the origin.  This module defines the deviation, its scale
`ballScale P N = 2^{d·Log N}` (the reciprocal width of `φ̃_N = η(ballScale ·)`, `d = P.natDegree`),
and the canonical representative `circRep θ ∈ [0,1)` of a point of the frequency circle, together
with the elementary consequences used downstream.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The reciprocal width of the `g`-side bump**: `ballScale P N = 2^{d·Log N}`, where
`d = P.natDegree` and `Log N = logN N = ⌊log₂ (max N 2)⌋`.  Thus the unmodulated bump is
`φ̃_N = η(ballScale P N ·)`. -/
noncomputable def ballScale (P : Polynomial ℤ) (N : ℕ) : ℝ :=
  (2 : ℝ) ^ ((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))

/-- **The deviation of the modulated bump from the unmodulated one**:
`ballDev P N t = φ̃_{N,t} - φ̃_N = varphitildeNtj P N 0 0 t - φ̃_N`. -/
noncomputable def ballDev (P : Polynomial ℤ) (N : ℕ) (t : ℝ) : ℝ → ℂ :=
  fun ξ => varphitildeNtj P N 0 0 t ξ - Work.KMTAreas.A7.varphitildeN P.natDegree N 0 ξ

/-- The canonical representative in `[0,1)` of a frequency `θ` of the circle `ℝ/ℤ`. -/
noncomputable def circRep (θ : Work.Analysis.IonescuWainger.Circle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 θ).val

/-! ## Elementary properties -/

theorem ballScale_pos (P : Polynomial ℤ) (N : ℕ) : 0 < ballScale P N :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem ballScale_nonneg (P : Polynomial ℤ) (N : ℕ) : 0 ≤ ballScale P N :=
  (ballScale_pos P N).le

/-- The reciprocal width of the bump is at least `1` (`logN N ≥ 0`). -/
theorem ballScale_one_le (P : Polynomial ℤ) (N : ℕ) : 1 ≤ ballScale P N := by
  rw [ballScale]
  refine Real.one_le_rpow (by norm_num) ?_
  have h : (0 : ℤ) ≤ Work.Analysis.EndVar.logN N := by
    simp only [Work.Analysis.EndVar.logN]; positivity
  have h' : (0 : ℝ) ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by exact_mod_cast h
  positivity

/-- The unmodulated bump is the rescaled cutoff: `φ̃_N = η(ballScale ·)`. -/
theorem varphitildeN_zero_eq_ballScale (P : Polynomial ℤ) (N : ℕ) :
    Work.KMTAreas.A7.varphitildeN P.natDegree N 0
      = fun ξ : ℝ => Work.KMTContract.kmtEta (ballScale P N * ξ) := by
  funext ξ
  simp only [Work.KMTAreas.A7.varphitildeN, if_true, ballScale]

/-- **The normal form of the deviation**: `ballDev P N t = φ̃_N · (e(P(Nt)·) - 1)`. -/
theorem ballDev_apply (P : Polynomial ℤ) (N : ℕ) (t : ℝ) (ξ : ℝ) :
    ballDev P N t ξ = Work.KMTAreas.A7.varphitildeN P.natDegree N 0 ξ *
      (Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) - 1) := by
  simp only [ballDev, Work.KMTPlan.A6.varphitildeNtj_zero]
  rw [show Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 t ξ
      = Work.KMTAreas.A7.varphitildeN P.natDegree N 0 ξ
        * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) from rfl]
  ring

/-- The function-level form of `ballDev_apply`. -/
theorem ballDev_eq (P : Polynomial ℤ) (N : ℕ) (t : ℝ) :
    ballDev P N t = fun ξ : ℝ => Work.KMTAreas.A7.varphitildeN P.natDegree N 0 ξ *
      (Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) - 1) := by
  funext ξ
  exact ballDev_apply P N t ξ

/-- **The deviation vanishes outside the support of the bump.** -/
theorem ballDev_vanish (P : Polynomial ℤ) (N : ℕ) (t : ℝ) {ξ : ℝ}
    (h : 1 ≤ ballScale P N * |ξ|) : ballDev P N t ξ = 0 := by
  rw [ballDev_apply]
  have h0 : Work.KMTAreas.A7.varphitildeN P.natDegree N 0 ξ = 0 := by
    rw [varphitildeN_zero_eq_ballScale]
    refine Work.KMTContract.kmtEta_zero ?_
    rwa [abs_mul, abs_of_pos (ballScale_pos P N)]
  rw [h0, zero_mul]

theorem circRep_mem (θ : Work.Analysis.IonescuWainger.Circle) :
    circRep θ ∈ Set.Ico (0 : ℝ) 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 θ).property
  simpa [circRep] using h

theorem circRep_nonneg (θ : Work.Analysis.IonescuWainger.Circle) : 0 ≤ circRep θ :=
  (Set.mem_Ico.mp (circRep_mem θ)).1

theorem circRep_lt_one (θ : Work.Analysis.IonescuWainger.Circle) : circRep θ < 1 :=
  (Set.mem_Ico.mp (circRep_mem θ)).2

/-- The representative represents: `circRep θ` is congruent to `θ` modulo `1`. -/
theorem circRep_coe (θ : Work.Analysis.IonescuWainger.Circle) :
    ((circRep θ : ℝ) : Work.Analysis.IonescuWainger.Circle) = θ :=
  AddCircle.coe_equivIco

/-- **The Ionescu--Wainger symbol over the singleton `{0}` is the symbol itself.** -/
theorem iwSymbolSet_singleton_zero (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) :
    Work.Analysis.IonescuWainger.iwSymbolSet ({0} : Finset _) Φ = Φ := by
  funext θ
  rw [Work.Analysis.IonescuWainger.iwSymbolSet, Finset.sum_singleton]
  simp

end

end Work.KMTPlan.A6
