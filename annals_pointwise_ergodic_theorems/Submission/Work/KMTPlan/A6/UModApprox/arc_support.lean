/-
# The arc conditions of the two modulated §5 bumps, from the strict plateau

The single-scale model approximation of the large-scale low case is applied only on the scales of
the *strict plateau*

  `max k₁ k₂ + 2 · uScale ρ (lcL l₁ l₂ k₁ k₂) + 1 ≤ logN N`,   `N = ⌊a n⌋`,

which says that the frequency window `ℝ_{≤ kᵢ - Log N}` of the two §5 bumps `φ_{N,t}`, `φ̃_{N,t}`
sits strictly inside the band `ℝ_{≤ -2u}` (`u = uScale ρ (lcL l₁ l₂ k₁ k₂)`) of the symbol
`m_* = η_{≤-2u} ⊗ η_{≤-2du}`.

This module records the four consequences of that inequality that the §6 functional calculus and
the arithmetic fibre collapse need:

* `varphiNt_realArc_support` / `varphitildeNt_realArc_support` — the real support of the two
  modulated bumps is contained in the arc `ℝ_{≤-2u}` (the hypothesis of the one-variable collapse
  `Work.KMTAreas.A7.tsumCwCollapseOfSupport` at the common scale `k = -2u`);
* `varphiNt_supportedInArc` / `varphitildeNt_supportedInArc` — the periodisations are supported in
  the *images* of the arcs `ℝ_{≤-u-1}` and `ℝ_{≤-du-1}` respectively (the plateau hypotheses of
  `Work.KMTAreas.A7.Tle_piExact_eq_convOp`, i.e. of `mdlPart_eq_bilinOp_maeKmod`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.varphiNt_support_all
import Submission.Work.KMTAreas.A7.varphitildeNt_support_all
import Submission.Work.KMTPlan.A6.supportedInArc_periodize_of_support
import Submission.Work.KMTPlan.A6.LowDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6.UModApprox

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.EndVar

/-- Membership in the arc `ℝ_{≤k}` from the absolute-value bound. -/
theorem realArc_of_abs_le {k : ℤ} {ξ : ℝ} (h : |ξ| ≤ (2 : ℝ) ^ k) :
    ξ ∈ Work.Analysis.IonescuWainger.realArc k := by
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
  exact abs_le.mp h

/-- `(logN N).toNat` cast to `ℝ` is `logN N`. -/
theorem logN_toNat_cast (N : ℕ) :
    ((Work.Analysis.EndVar.logN N).toNat : ℝ) = (Work.Analysis.EndVar.logN N : ℝ) := by
  rw [Work.Analysis.EndVar.logN, Int.toNat_natCast]
  push_cast
  ring

/-- **The plateau, in the two scalar forms used below.**  On the strict plateau
`max k₁ k₂ + 2u + 1 ≤ (logN N).toNat` one has `kᵢ + 2u + 1 ≤ logN N` for `i = 1,2`. -/
theorem plateau_le (ρ : ℝ) (N l₁ l₂ k₁ k₂ : ℕ)
    (hplat : max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat) :
    ((k₁ : ℝ) + 2 * ((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℕ) : ℝ) + 1
        ≤ (Work.Analysis.EndVar.logN N : ℝ)) ∧
    ((k₂ : ℝ) + 2 * ((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℕ) : ℝ) + 1
        ≤ (Work.Analysis.EndVar.logN N : ℝ)) := by
  have hlog : ((max k₁ k₂
      + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1 : ℕ) : ℝ)
      ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
    rw [← logN_toNat_cast N]
    exact_mod_cast hplat
  have hcast : ((max k₁ k₂
      + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1 : ℕ) : ℝ)
      = ((max k₁ k₂ : ℕ) : ℝ)
        + 2 * ((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  have hmaxR : ((max k₁ k₂ : ℕ) : ℝ)
      + 2 * ((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℕ) : ℝ) + 1
      ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
    rw [hcast] at hlog
    exact hlog
  have h1 : (k₁ : ℝ) ≤ ((max k₁ k₂ : ℕ) : ℝ) := by exact_mod_cast (le_max_left k₁ k₂)
  have h2 : (k₂ : ℝ) ≤ ((max k₁ k₂ : ℕ) : ℝ) := by exact_mod_cast (le_max_right k₁ k₂)
  exact ⟨by linarith, by linarith⟩

/-- **Real support of the first modulated bump.**  On the strict plateau, a non-zero value of
`φ_{N,t}` forces `|ξ| ≤ 2^{-2u}`, i.e. `ξ ∈ ℝ_{≤ -2u}`. -/
theorem varphiNt_realArc_support (ρ : ℝ) (N l₁ l₂ k₁ k₂ : ℕ)
    (hplat : max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat) :
    ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ ξ : ℝ, Work.KMTAreas.A7.varphiNt N k₁ t ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc
        (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))) := by
  intro t _ ξ hξ
  have h1 : |ξ| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) :=
    Work.KMTPlan.A6.varphiNt_support_all N k₁ t ξ hξ
  have hle := (plateau_le ρ N l₁ l₂ k₁ k₂ hplat).1
  have h2 : (k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)
      ≤ ((-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) : ℤ) : ℝ) := by
    push_cast
    linarith
  have h3 : (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
      ≤ (2 : ℝ) ^ ((-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) : ℤ) : ℝ) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr h2
  rw [Real.rpow_intCast] at h3
  exact realArc_of_abs_le (le_trans h1 h3)

/-- **Real support of the second modulated bump.**  On the strict plateau, a non-zero value of
`φ̃_{N,t}` forces `|ξ| ≤ 2^{-2u}`. -/
theorem varphitildeNt_realArc_support (ρ : ℝ) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (N l₁ l₂ k₁ k₂ : ℕ)
    (hplat : max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat) :
    ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ ξ : ℝ,
      Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc
        (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))) := by
  intro t _ ξ hξ
  have h1 : |ξ| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :=
    Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree N k₂ t ξ hξ
  have hle := (plateau_le ρ N l₁ l₂ k₁ k₂ hplat).2
  have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by
    have : (1 : ℕ) ≤ P.natDegree := le_trans (by norm_num) hd
    exact_mod_cast this
  have hu0 : (0 : ℝ) ≤ ((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℕ) : ℝ) := by
    positivity
  have h2 : (P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
      ≤ ((-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) : ℤ) : ℝ) := by
    have hnod : (0 : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ) := by linarith
    have hprod : (Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ)
        ≤ (P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ)) := by
      have := mul_le_mul_of_nonneg_right hd1 hnod
      simpa using this
    push_cast
    linarith
  have h3 : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
      ≤ (2 : ℝ) ^ ((-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) : ℤ) : ℝ) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr h2
  rw [Real.rpow_intCast] at h3
  exact realArc_of_abs_le (le_trans h1 h3)

/-- **Support of the periodisation of the first modulated bump.**  On the strict plateau,
`periodize (φ_{N,t})` is supported in the image of the arc `ℝ_{≤ -u-1}` (the plateau of
`η_{≤-u}`). -/
theorem varphiNt_supportedInArc (ρ : ℝ) (N l₁ l₂ k₁ k₂ : ℕ)
    (hplat : max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat) :
    ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Work.Analysis.IonescuWainger.SupportedInArc
      (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ) - 1)
      (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k₁ t)) := by
  intro t _
  refine Work.KMTPlan.A6.supportedInArc_periodize_of_arc (k :=
    -(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ) - 1) ?_
  intro ξ hξ
  have h1 : |ξ| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) :=
    Work.KMTPlan.A6.varphiNt_support_all N k₁ t ξ hξ
  have hle := (plateau_le ρ N l₁ l₂ k₁ k₂ hplat).1
  have hu0 : (0 : ℝ) ≤ ((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℕ) : ℝ) := by
    positivity
  have h2 : (k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)
      ≤ (((-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ) - 1) : ℤ) : ℝ) := by
    push_cast
    linarith
  have h3 : (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
      ≤ (2 : ℝ) ^ (((-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ) - 1) : ℤ) : ℝ) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr h2
  rw [Real.rpow_intCast] at h3
  exact realArc_of_abs_le (le_trans h1 h3)

/-- **Support of the periodisation of the second modulated bump.**  On the strict plateau,
`periodize (φ̃_{N,t})` is supported in the image of the arc `ℝ_{≤ -du-1}`. -/
theorem varphitildeNt_supportedInArc (ρ : ℝ) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (N l₁ l₂ k₁ k₂ : ℕ)
    (hplat : max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat) :
    ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Work.Analysis.IonescuWainger.SupportedInArc
      (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) - 1)
      (Work.Analysis.IonescuWainger.periodize
        (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)) := by
  intro t _
  refine Work.KMTPlan.A6.supportedInArc_periodize_of_arc (k :=
    -((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) - 1) ?_
  intro ξ hξ
  have h1 : |ξ| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :=
    Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree N k₂ t ξ hξ
  have hle := (plateau_le ρ N l₁ l₂ k₁ k₂ hplat).2
  have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by
    have : (1 : ℕ) ≤ P.natDegree := le_trans (by norm_num) hd
    exact_mod_cast this
  have hu0 : (0 : ℝ) ≤ ((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℕ) : ℝ) := by
    positivity
  have h2 : (P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
      ≤ (((-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) - 1) : ℤ) : ℝ) := by
    have hnod : (0 : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ) := by linarith
    have hmul : (P.natDegree : ℝ) * (2 * ((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℕ) : ℝ) + 1)
        ≤ (P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hkey : ((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℕ) : ℝ)
        * (P.natDegree : ℝ) + 1
        ≤ (P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ)) := by
      nlinarith [hmul, hd1, hu0]
    push_cast
    linarith
  have h3 : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
      ≤ (2 : ℝ) ^ (((-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) - 1) : ℤ) : ℝ) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr h2
  rw [Real.rpow_intCast] at h3
  exact realArc_of_abs_le (le_trans h1 h3)

end

end Work.KMTPlan.A6.UModApprox
