import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxHiKernels
import Submission.Work.KMTAreas.A7.narrow_of_core
import Submission.Work.KMTAreas.A7.varphitildeNt_support_all

namespace Work.KMTAreas.A7

/-!
# The band `ℝ_{≤ -2u}` contains the supports of `φ_{N,t}` and `φ̃_{N,t}`

Section 6 of Krause--Mirek--Tao splits the large-scale analysis into the *main regime*
`k + 2u ≤ Log N` (with `u` the auxiliary scale of the scale split) and its complement.  On the
main regime the functional calculus of §6 applies, because the frequency windows
`ℝ_{≤ -Log N + k}` of the bumps `φ_{N,t}`, `φ̃_{N,t}` are contained in the band
`ℝ_{≤ -2u} = [-2^{-2u}, 2^{-2u}]` of the symbol `m_* = η_{≤-2u}`.

This file records precisely that containment, in the form needed by the `Large/` chapter: a
nonzero value of either bump at a frequency `θ` forces `θ ∈ realArc (-(2u))`.

The two inputs are the elementary support bounds

* `varphiNt_support_le_all`: `φ_{N,t}(θ) ≠ 0 → |θ| ≤ 2^{k₁ - Log N}` (valid at every height
  `k₁ : ℕ`, the bottom height `k₁ = 0` included), and
* `varphitildeNt_support_all`: `φ̃_{N,t}(θ) ≠ 0 → |θ| ≤ 2^{d(k₂ - Log N)}` (`d = P.natDegree`),

together with the main-regime hypotheses `k₁ + 2u ≤ Log N`, `k₂ + 2u ≤ Log N` and the fact that
`d ≥ 2` (so that `2u ≤ d·2u`).
-/

/-- **An exponential bound inside `realArc`.**  If `|θ| ≤ 2^E` and `E ≤ k` for the integer `k`,
then `θ ∈ realArc k = [-2^k, 2^k]`. -/
private lemma mem_realArc_of_abs_le_rpow {θ E : ℝ} {k : ℤ}
    (hθ : |θ| ≤ (2 : ℝ) ^ E) (hE : E ≤ (k : ℝ)) :
    θ ∈ Work.Analysis.IonescuWainger.realArc k := by
  have hfin : |θ| ≤ (2 : ℝ) ^ (k : ℝ) :=
    le_trans hθ ((Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hE)
  rw [Real.rpow_intCast] at hfin
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
  exact abs_le.mp hfin

/-- The main-regime hypothesis `k + 2u ≤ Log N` in `ℤ` gives the same inequality in `ℝ`. -/
private lemma band_cast {k u N : ℕ}
    (h : (k : ℤ) + 2 * (u : ℤ) ≤ Work.Analysis.EndVar.logN N) :
    (k : ℝ) + 2 * (u : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
  exact_mod_cast h

theorem bump_support_realArc (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (N k₁ k₂ u : ℕ)
    (hband₁ : (k₁ : ℤ) + 2 * (u : ℤ) ≤ Work.Analysis.EndVar.logN N)
    (hband₂ : (k₂ : ℤ) + 2 * (u : ℤ) ≤ Work.Analysis.EndVar.logN N) :
    (∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ θ : ℝ,
        Work.KMTAreas.A7.varphiNt N k₁ t θ ≠ 0 →
          θ ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (u : ℤ))))
    ∧ (∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ θ : ℝ,
        Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t θ ≠ 0 →
          θ ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (u : ℤ)))) := by
  refine ⟨?_, ?_⟩
  · -- the `f`-side bump: support `2^{k₁ - Log N} ⊆ 2^{-2u}`
    intro t _ θ hθ
    refine mem_realArc_of_abs_le_rpow (varphiNt_support_le_all k₁ N t θ hθ) ?_
    have hR := band_cast hband₁
    have hcast : ((-(2 * (u : ℤ)) : ℤ) : ℝ) = -(2 * (u : ℝ)) := by push_cast; ring
    rw [hcast]
    linarith
  · -- the `g`-side bump: support `2^{d(k₂ - Log N)} ⊆ 2^{-2u}` since `d ≥ 2`
    intro t _ θ hθ
    refine mem_realArc_of_abs_le_rpow
      (varphitildeNt_support_all P P.natDegree N k₂ t θ hθ) ?_
    have hR := band_cast hband₂
    have hcast : ((-(2 * (u : ℤ)) : ℤ) : ℝ) = -(2 * (u : ℝ)) := by push_cast; ring
    rw [hcast]
    have hdR : (1 : ℝ) ≤ (P.natDegree : ℝ) := by
      have : (1 : ℤ) ≤ (P.natDegree : ℤ) := by omega
      exact_mod_cast this
    have huR : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    nlinarith [hR, hdR, huR, mul_nonneg (sub_nonneg.mpr hdR) (by positivity : (0:ℝ) ≤ 2 * (u : ℝ))]

end Work.KMTAreas.A7
