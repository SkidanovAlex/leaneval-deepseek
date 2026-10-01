import Mathlib
import Submission.Work.LinnikAreas.LoneLowerDefs
import Submission.Work.LinnikAreas.norm_triFun_horiz_quarter
import Submission.Work.LinnikAreas.norm_triFun_horiz_one
import Submission.Work.LinnikAreas.rpow_le_quarter_range
import Submission.Work.LinnikAreas.rpow_le_upper_range
import Submission.Work.LinnikAreas.horiz_const_fold

set_option maxHeartbeats 1600000

namespace Work.LinnikAreas

open DirichletCharacter Complex MeasureTheory intervalIntegral Filter
open scoped Real BigOperators

noncomputable section

theorem contour_horizontal_edge (CZ CL : ℝ) (hCZ : 0 < CZ) (hCL : 0 < CL)
    (hZ : ∀ σ t : ℝ, 5 / 8 ≤ σ → σ ≤ 2 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ CZ * (1 + |t|) ^ ((7 : ℝ) / 16))
    (hL : ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), ψ ≠ 1 → ψ.IsPrimitive →
      ∀ σ T : ℝ, 5 / 8 ≤ σ → σ ≤ 1 →
      ‖DirichletCharacter.LFunction ψ ((σ : ℂ) + (T : ℂ) * Complex.I)‖
        ≤ CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |T|) ^ ((1 : ℝ) / 4))
    (hLlog : ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), ψ ≠ 1 → ∀ z : ℂ, 1 ≤ z.re →
      ‖DirichletCharacter.LFunction ψ z‖
        ≤ Real.log (2 * N) + Real.log (2 + |z.im|) + 6) :
    ∃ KH : ℝ, 0 < KH ∧ ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
      (hprim : ψ.IsPrimitive) {β x T : ℝ} (hβ : 3 / 4 ≤ β) (hβ1 : β < 1) (hx : 0 < x) (hT : 1 ≤ T),
      ‖(1 / (2 * Real.pi * Complex.I)) *
          ((∫ u in ((5 / 8 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
            - (∫ u in ((5 / 8 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I)))‖
        ≤ KH * ((1 + T) ^ ((11 : ℝ) / 16) / T ^ 2 *
            ((N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
              + (Real.log (2 * N) + Real.log (2 + T)) * (x + x ^ ((1 - β : ℝ))))) := by
  obtain ⟨KH, hKHpos, hfold⟩ := horiz_const_fold CZ CL hCZ hCL
  refine ⟨KH, hKHpos, ?_⟩
  intro N _inst ψ hψ hprim β x T hβ hβ1 hx hT
  have hTnn : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have ht1 : (1 : ℝ) ≤ |T| := by rw [abs_of_nonneg hTnn]; exact hT
  have ht2 : (1 : ℝ) ≤ |-T| := by rwa [abs_neg]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    exact_mod_cast this
  have hxnn : (0 : ℝ) ≤ x := le_of_lt hx
  have hD1nn : (0 : ℝ) ≤ x + x ^ ((5 / 8 - β : ℝ)) :=
    add_nonneg hxnn (Real.rpow_nonneg hxnn _)
  have hD2nn : (0 : ℝ) ≤ x + x ^ ((1 - β : ℝ)) :=
    add_nonneg hxnn (Real.rpow_nonneg hxnn _)
  have ha1 : (5 / 8 - β : ℝ) < 1 := by linarith
  have hline : ∀ t : ℝ, 1 ≤ |t| →
      ‖∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ 2 * CZ * ((1 + |t|) ^ ((11 : ℝ) / 16) / t ^ 2) *
            (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
              + (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ)))) := by
    intro t ht
    have htpos : (0 : ℝ) < |t| := lt_of_lt_of_le one_pos ht
    have ht2pos : (0 : ℝ) < t ^ 2 := by rw [← sq_abs]; exact pow_pos htpos 2
    have hlnn : (0 : ℝ) ≤ Real.log (2 * N) + Real.log (2 + |t|) + 6 := by
      have h2 : (0 : ℝ) ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
      have h1 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
      linarith
    have hpnn : (0 : ℝ) ≤ (1 + |t|) ^ ((11 : ℝ) / 16) := Real.rpow_nonneg (by positivity) _
    have hNqnn : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    have hcc : (0 : ℝ) ≤ CZ * (1 + |t|) ^ ((11 : ℝ) / 16) / t ^ 2 :=
      div_nonneg (mul_nonneg (le_of_lt hCZ) hpnn) (le_of_lt ht2pos)
    have hp : (1 + |t|) ^ ((7 : ℝ) / 16) ≤ (1 + |t|) ^ ((11 : ℝ) / 16) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t] : (1 : ℝ) ≤ 1 + |t|)
        (by norm_num)
    have hBound : ∀ u ∈ Set.uIoc (5 / 8 - β : ℝ) 1,
        ‖triFun ψ β x ((u : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ CZ * (1 + |t|) ^ ((11 : ℝ) / 16) / t ^ 2 *
              (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
                + (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ)))) := by
      intro u hu
      rw [Set.uIoc_of_le (le_of_lt ha1)] at hu
      rcases le_or_gt u (1 - β) with hum | hum
      · have hq := norm_triFun_horiz_quarter CZ CL hCZ hCL hZ hL ψ hψ hprim
          hβ hβ1 hx ht (le_of_lt hu.1) hum
        have hxle : x ^ u ≤ x + x ^ ((5 / 8 - β : ℝ)) :=
          rpow_le_quarter_range x β u (by linarith) hβ1 hx (le_of_lt hu.1) hum
        have hstep : CZ * CL * (1 + |t|) ^ ((11 : ℝ) / 16) * (N : ℝ) ^ ((1 : ℝ) / 4) * x ^ u / t ^ 2
            ≤ CZ * CL * (1 + |t|) ^ ((11 : ℝ) / 16) * (N : ℝ) ^ ((1 : ℝ) / 4)
                * (x + x ^ ((5 / 8 - β : ℝ))) / t ^ 2 := by
          apply div_le_div_of_nonneg_right _ (le_of_lt ht2pos)
          exact mul_le_mul_of_nonneg_left hxle
            (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCZ) (le_of_lt hCL)) hpnn) hNqnn)
        refine hq.trans (hstep.trans ?_)
        have hnn : (0 : ℝ) ≤ CZ * (1 + |t|) ^ ((7 : ℝ) / 16)
            * (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ))) / t ^ 2 :=
          div_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCZ)
            (Real.rpow_nonneg (by positivity) _)) hlnn |> fun h => mul_nonneg h hD2nn)
            (le_of_lt ht2pos)
        have hkey : CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
            ≤ CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
              + (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ))) :=
          le_add_of_nonneg_right (mul_nonneg hlnn hD2nn)
        calc CZ * CL * (1 + |t|) ^ ((11 : ℝ) / 16) * (N : ℝ) ^ ((1 : ℝ) / 4)
                * (x + x ^ ((5 / 8 - β : ℝ))) / t ^ 2
            = CZ * (1 + |t|) ^ ((11 : ℝ) / 16) / t ^ 2
                * (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))) := by ring
          _ ≤ CZ * (1 + |t|) ^ ((11 : ℝ) / 16) / t ^ 2
                * (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
                  + (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ)))) :=
              mul_le_mul_of_nonneg_left hkey hcc
      · have hq := norm_triFun_horiz_one CZ hCZ hZ hLlog ψ hψ hβ hβ1 hx ht (le_of_lt hum) hu.2
        have hxle : x ^ u ≤ x + x ^ ((1 - β : ℝ)) :=
          rpow_le_upper_range x β u hx (le_of_lt hum) hu.2
        have hstep : CZ * (1 + |t|) ^ ((7 : ℝ) / 16)
              * (Real.log (2 * N) + Real.log (2 + |t|) + 6) * x ^ u / t ^ 2
            ≤ CZ * (1 + |t|) ^ ((7 : ℝ) / 16)
              * (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ))) / t ^ 2 := by
          apply div_le_div_of_nonneg_right _ (le_of_lt ht2pos)
          exact mul_le_mul_of_nonneg_left hxle
            (mul_nonneg (mul_nonneg (le_of_lt hCZ) (Real.rpow_nonneg (by positivity) _)) hlnn)
        refine hq.trans (hstep.trans ?_)
        have h7 : CZ * (1 + |t|) ^ ((7 : ℝ) / 16) * (Real.log (2 * N) + Real.log (2 + |t|) + 6)
            ≤ CZ * (1 + |t|) ^ ((11 : ℝ) / 16) * (Real.log (2 * N) + Real.log (2 + |t|) + 6) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (le_of_lt hCZ)) hlnn
        have hstep2 : CZ * (1 + |t|) ^ ((7 : ℝ) / 16)
              * (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ))) / t ^ 2
            ≤ CZ * (1 + |t|) ^ ((11 : ℝ) / 16)
              * (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ))) / t ^ 2 := by
          apply div_le_div_of_nonneg_right _ (le_of_lt ht2pos)
          exact mul_le_mul_of_nonneg_right h7 hD2nn
        refine hstep2.trans ?_
        have hnn : (0 : ℝ) ≤ CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ))) :=
          mul_nonneg (mul_nonneg (le_of_lt hCL) hNqnn) hD1nn
        calc CZ * (1 + |t|) ^ ((11 : ℝ) / 16)
                * (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ))) / t ^ 2
            = CZ * (1 + |t|) ^ ((11 : ℝ) / 16) / t ^ 2
                * ((Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ)))) := by ring
          _ ≤ CZ * (1 + |t|) ^ ((11 : ℝ) / 16) / t ^ 2
                * (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
                  + (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ)))) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hnn) hcc
    have hMnn : (0 : ℝ) ≤ CZ * (1 + |t|) ^ ((11 : ℝ) / 16) / t ^ 2 *
        (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
          + (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ)))) :=
      mul_nonneg hcc (add_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCL) hNqnn) hD1nn)
        (mul_nonneg hlnn hD2nn))
    have hmain := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun u : ℝ => triFun ψ β x ((u : ℂ) + (t : ℂ) * Complex.I)) hBound
    have habs : |1 - (5 / 8 - β : ℝ)| = 1 - (5 / 8 - β : ℝ) := abs_of_nonneg (by linarith)
    have h2le : (1 - (5 / 8 - β : ℝ)) ≤ 2 := by linarith
    calc ‖∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ CZ * (1 + |t|) ^ ((11 : ℝ) / 16) / t ^ 2 *
            (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
              + (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ))))
            * |1 - (5 / 8 - β : ℝ)| := hmain
      _ = CZ * (1 + |t|) ^ ((11 : ℝ) / 16) / t ^ 2 *
            (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
              + (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ))))
            * (1 - (5 / 8 - β : ℝ)) := by rw [habs]
      _ ≤ CZ * (1 + |t|) ^ ((11 : ℝ) / 16) / t ^ 2 *
            (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
              + (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ)))) * 2 :=
          mul_le_mul_of_nonneg_left h2le hMnn
      _ = 2 * CZ * ((1 + |t|) ^ ((11 : ℝ) / 16) / t ^ 2) *
            (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
              + (Real.log (2 * N) + Real.log (2 + |t|) + 6) * (x + x ^ ((1 - β : ℝ)))) := by ring
  have hI1 := hline T ht1
  rw [abs_of_nonneg hTnn] at hI1
  have hI2 := hline (-T) ht2
  rw [abs_neg, neg_sq, abs_of_nonneg hTnn] at hI2
  have heq : (∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I))
      = (∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    show triFun ψ β x ((u : ℂ) - (T : ℂ) * Complex.I)
        = triFun ψ β x ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
    congr 1
    push_cast
    ring
  have hI2' : ‖∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I)‖
      ≤ 2 * CZ * ((1 + T) ^ ((11 : ℝ) / 16) / T ^ 2) *
          (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
            + (Real.log (2 * N) + Real.log (2 + T) + 6) * (x + x ^ ((1 - β : ℝ)))) := by
    rw [heq]
    exact hI2
  have hfac : ‖(1 / (2 * Real.pi * Complex.I) : ℂ)‖ = 1 / (2 * Real.pi) := by
    have h2pi : ‖((2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hden : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      rw [show (2 * Real.pi * Complex.I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
            push_cast; ring, norm_mul, h2pi, Complex.norm_I, mul_one]
    rw [norm_div, norm_one, hden]
  have hT2pos : (0 : ℝ) < T ^ 2 := pow_pos (lt_of_lt_of_le one_pos hT) 2
  have hKfnn : (0 : ℝ) ≤ (1 + T) ^ ((11 : ℝ) / 16) / T ^ 2 :=
    div_nonneg (Real.rpow_nonneg (by positivity) _) (le_of_lt hT2pos)
  have hfold' := hfold (N := N) hT hD1nn hD2nn
  calc ‖(1 / (2 * Real.pi * Complex.I)) *
        ((∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + T * Complex.I))
          - (∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I)))‖
      = ‖(1 / (2 * Real.pi * Complex.I) : ℂ)‖ *
          ‖(∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + T * Complex.I))
            - (∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I))‖ :=
        norm_mul _ _
    _ ≤ (1 / (2 * Real.pi)) *
          (‖∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + T * Complex.I)‖
            + ‖∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I)‖) := by
        rw [hfac]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) *
          (2 * CZ * ((1 + T) ^ ((11 : ℝ) / 16) / T ^ 2) *
              (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
                + (Real.log (2 * N) + Real.log (2 + T) + 6) * (x + x ^ ((1 - β : ℝ))))
            + 2 * CZ * ((1 + T) ^ ((11 : ℝ) / 16) / T ^ 2) *
              (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
                + (Real.log (2 * N) + Real.log (2 + T) + 6) * (x + x ^ ((1 - β : ℝ))))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hI1 hI2'
    _ = (2 / Real.pi) * CZ * ((1 + T) ^ ((11 : ℝ) / 16) / T ^ 2) *
          (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
            + (Real.log (2 * N) + Real.log (2 + T) + 6) * (x + x ^ ((1 - β : ℝ)))) := by ring
    _ ≤ KH * ((1 + T) ^ ((11 : ℝ) / 16) / T ^ 2 *
          ((N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
            + (Real.log (2 * N) + Real.log (2 + T)) * (x + x ^ ((1 - β : ℝ))))) := by
        calc (2 / Real.pi) * CZ * ((1 + T) ^ ((11 : ℝ) / 16) / T ^ 2) *
              (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
                + (Real.log (2 * N) + Real.log (2 + T) + 6) * (x + x ^ ((1 - β : ℝ))))
            = ((2 / Real.pi) * CZ *
                (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
                  + (Real.log (2 * N) + Real.log (2 + T) + 6) * (x + x ^ ((1 - β : ℝ)))))
                * ((1 + T) ^ ((11 : ℝ) / 16) / T ^ 2) := by ring
          _ ≤ (KH * ((N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
                  + (Real.log (2 * N) + Real.log (2 + T)) * (x + x ^ ((1 - β : ℝ)))))
                * ((1 + T) ^ ((11 : ℝ) / 16) / T ^ 2) := mul_le_mul_of_nonneg_right hfold' hKfnn
          _ = KH * ((1 + T) ^ ((11 : ℝ) / 16) / T ^ 2 *
                ((N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
                  + (Real.log (2 * N) + Real.log (2 + T)) * (x + x ^ ((1 - β : ℝ))))) := by ring


end

end Work.LinnikAreas
