/-
# Moderate growth of the CKMRV cusp-expansion coefficients on the cusp-`±1` tiles

The generating function `F₂` of CKMRV (Ann. of Math. 196 (2022), (5.2)--(5.3)) is decomposed, on
each cusp tile, into a `low`, a `trunc` and a `high` piece.  Both the `trunc` and the `high` piece
consume the *cusp expansion* `K(τ, i t) ≈ Aexp G τ t` of the kernel along the contour, whose
coefficients are the functions `Gcusp ℓ d i j` of `Submission/Work/Asymptotics/GcuspDefs.lean`
(`Gcusp8` in dimension `8`, `Gcusp24` in dimension `24`).

This file proves that those coefficients are *moderate* on the cusp-`±1` tiles `±1 + E`:

  `∃ C N, 0 < C ∧ 0 ≤ N ∧ ∀ w ∈ E, ∀ n = ±1, ∀ i j : ‖Gcusp ℓ d i j (n +ᵥ w)‖ ≤ C (scale w)^N`

(`Work.Asymptotics.Gcusp_tile_bound`), via the intermediate `Work.Asymptotics.Gcusp_Bdd`
(package: `EtailE.Bdd 0`) for each of the four `(i,j)` pairs.  Since `Gcusp ℓ d i j` is a finite
combination of the atoms `E₂, E₄, E₆, E₈, E₁₀, E₁₄, Δ, phiVec 0/1/2, psi2 ℓ, psi4 ℓ` and the
constant `cuspL ℓ`, the proof is a case analysis on `d ∈ {8,24}` and on `(i,j) : Fin 2 × Fin 2`,
each case being a combination of the translated atoms recorded in
`Submission/Work/Asymptotics/tile_Bdd_atoms.lean`.

(Import caveat: this file — like `tile_Bdd_atoms` — pulls in `EtailE.Atoms`, hence `KPlusXiDefs`
and `MiddleRange.Main`, which both declare `Work.Asymptotics.continuous_jInvariantFun`; do not
import it from a file that already imports the `MiddleRange` branch.)
-/
import Mathlib
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.GcuspDefs

noncomputable section
open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm
namespace Work.Asymptotics
open Work.Kernels
open Work.Asymptotics.EtailE (Bdd)

theorem Gcusp_Bdd (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (n : ℤ)
    (hn : n = 1 ∨ n = -1) (i j : Fin 2) :
    Bdd 0 (fun w : ℍ => Gcusp ℓ d i j ((n:ℝ)+ᵥw)) := by
  have key8 : ∀ i j : Fin 2, Bdd 0 (fun w : ℍ => Gcusp8 ℓ i j ((n:ℝ)+ᵥw)) := by
    intro i j
    fin_cases i <;> fin_cases j
    · change Bdd 0 (fun w : ℍ => Gcusp8 ℓ 0 0 ((n:ℝ)+ᵥw))
      have A := (Bdd.vadd_phi0 n hn).mul_zero (Bdd.vadd_E6 n hn)
      have B := A.mul_zero (Bdd.const' (-Complex.I))
      have C := (Bdd.vadd_E4 n hn).mul_zero (Bdd.const' (cuspL ℓ * ((Real.pi:ℂ))⁻¹))
      have D := (Bdd.vadd_psi4 ℓ n hn).mul_zero (Bdd.const' ((2*(Real.pi:ℂ))⁻¹))
      have E := (B.add C).sub D
      refine Bdd.congr (funext (fun w => ?_)) (E.mul_zero (Bdd.const' ((2:ℂ)⁻¹)))
      rw [show Gcusp8 ℓ 0 0 ((n:ℝ)+ᵥw) = (phiVec ((n:ℝ)+ᵥw) 0 * E6Fun ((n:ℝ)+ᵥw) * (-Complex.I)
            + E4Fun ((n:ℝ)+ᵥw) * cuspL ℓ / (Real.pi:ℂ)
            - psi4 ℓ ((n:ℝ)+ᵥw) / (2*(Real.pi:ℂ))) / 2 from rfl]
      ring
    · change Bdd 0 (fun w : ℍ => Gcusp8 ℓ 0 1 ((n:ℝ)+ᵥw))
      have A := (Bdd.vadd_phi0 n hn).mul_zero (Bdd.vadd_E6 n hn)
      have B := (Bdd.vadd_phi1 n hn).mul_zero (Bdd.vadd_E4 n hn)
      have C := A.sub B
      have D := (Bdd.const' ((Real.pi:ℂ)/3)).mul_zero C
      have E := D.add ((Bdd.const' Complex.I).mul_zero (Bdd.vadd_E4 n hn))
      refine Bdd.congr (funext (fun w => ?_)) (E.mul_zero (Bdd.const' ((2:ℂ)⁻¹)))
      rw [show Gcusp8 ℓ 0 1 ((n:ℝ)+ᵥw) = ((Real.pi:ℂ)/3 * (phiVec ((n:ℝ)+ᵥw) 0 * E6Fun ((n:ℝ)+ᵥw)
            - phiVec ((n:ℝ)+ᵥw) 1 * E4Fun ((n:ℝ)+ᵥw))
            + Complex.I * E4Fun ((n:ℝ)+ᵥw)) / 2 from rfl]
      ring
    · change Bdd 0 (fun w : ℍ => Gcusp8 ℓ 1 0 ((n:ℝ)+ᵥw))
      exact Bdd.congr (funext (fun w => (rfl : (0:ℂ) = Gcusp8 ℓ 1 0 ((n:ℝ)+ᵥw)).symm))
        (Bdd.const' (0 : ℂ))
    · change Bdd 0 (fun w : ℍ => Gcusp8 ℓ 1 1 ((n:ℝ)+ᵥw))
      exact Bdd.congr (funext (fun w => (rfl : (0:ℂ) = Gcusp8 ℓ 1 1 ((n:ℝ)+ᵥw)).symm))
        (Bdd.const' (0 : ℂ))
  have key24 : ∀ i j : Fin 2, Bdd 0 (fun w : ℍ => Gcusp24 ℓ i j ((n:ℝ)+ᵥw)) := by
    intro i j
    fin_cases i <;> fin_cases j
    · change Bdd 0 (fun w : ℍ => Gcusp24 ℓ 0 0 ((n:ℝ)+ᵥw))
      have hE4c := ((Bdd.vadd_E4 n hn).mul_zero (Bdd.vadd_E4 n hn)).mul_zero (Bdd.vadd_E4 n hn)
      have h1 := (Bdd.const' (-(13*Complex.I/12))).mul_zero ((Bdd.vadd_phi0 n hn).mul_zero (Bdd.vadd_E14 n hn))
      have h2 := (Bdd.const' (Complex.I/6)).mul_zero ((Bdd.vadd_phi1 n hn).mul_zero hE4c)
      have h3 := (Bdd.const' (168*Complex.I)).mul_zero ((Bdd.vadd_phi1 n hn).mul_zero (Bdd.vadd_Delta n hn))
      have h4 := (Bdd.const' (Complex.I/12)).mul_zero ((Bdd.vadd_phi2 n hn).mul_zero (Bdd.vadd_E10 n hn))
      have h5 := (Bdd.const' (720/(Real.pi:ℂ))).mul_zero ((Bdd.vadd_Delta n hn).mul_zero (Bdd.const' (cuspL ℓ)))
      have h6 := (Bdd.const' (36/(Real.pi:ℂ))).mul_zero (Bdd.vadd_Delta n hn)
      have h7 := (Bdd.const' (((Real.pi:ℂ))⁻¹)).mul_zero (hE4c.mul_zero (Bdd.const' (cuspL ℓ)))
      have h8 := (Bdd.const' (7/(24*(Real.pi:ℂ)))).mul_zero ((Bdd.vadd_psi2 ℓ n hn).mul_zero (Bdd.vadd_E10 n hn))
      have h9 := (Bdd.const' (5/(24*(Real.pi:ℂ)))).mul_zero ((Bdd.vadd_psi4 ℓ n hn).mul_zero (Bdd.vadd_E8 n hn))
      have E1 := ((h1.add h2).sub h3)
      have E2 := ((E1.sub h4).sub h5)
      have E3 := ((E2.sub h6).add h7)
      have E4 := ((E3.sub h8).sub h9)
      refine Bdd.congr (funext (fun w => ?_)) (E4.mul_zero (Bdd.const' ((2:ℂ)⁻¹)))
      rw [show Gcusp24 ℓ 0 0 ((n:ℝ)+ᵥw) = (-(13 * Complex.I / 12) * (phiVec ((n:ℝ)+ᵥw) 0 * E14Fun ((n:ℝ)+ᵥw))
            + (Complex.I / 6) * (phiVec ((n:ℝ)+ᵥw) 1 * E4Fun ((n:ℝ)+ᵥw) ^ 3)
            - 168 * Complex.I * (phiVec ((n:ℝ)+ᵥw) 1 * DeltaFun ((n:ℝ)+ᵥw))
            - (Complex.I / 12) * (phiVec ((n:ℝ)+ᵥw) 2 * E10Fun ((n:ℝ)+ᵥw))
            - 720 * DeltaFun ((n:ℝ)+ᵥw) * cuspL ℓ / (Real.pi:ℂ) - 36 * DeltaFun ((n:ℝ)+ᵥw) / (Real.pi:ℂ)
            + E4Fun ((n:ℝ)+ᵥw) ^ 3 * cuspL ℓ / (Real.pi:ℂ)
            - 7 * (psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)) / (24 * (Real.pi:ℂ))
            - 5 * (psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)) / (24 * (Real.pi:ℂ))) / 2 from rfl]
      ring
    · change Bdd 0 (fun w : ℍ => Gcusp24 ℓ 0 1 ((n:ℝ)+ᵥw))
      have hE4c := ((Bdd.vadd_E4 n hn).mul_zero (Bdd.vadd_E4 n hn)).mul_zero (Bdd.vadd_E4 n hn)
      have h1 := (Bdd.vadd_phi0 n hn).mul_zero (Bdd.vadd_E14 n hn)
      have h2 := (Bdd.const' (720:ℂ)).mul_zero ((Bdd.vadd_phi1 n hn).mul_zero (Bdd.vadd_Delta n hn))
      have h3 := (Bdd.vadd_phi1 n hn).mul_zero hE4c
      have h4 := ((h1.add h2).sub h3)
      have h5 := (Bdd.const' ((Real.pi:ℂ)/3)).mul_zero h4
      have h6 := ((Bdd.const' (720:ℂ)).mul_zero (Bdd.vadd_Delta n hn)).sub hE4c
      have h7 := (Bdd.const' Complex.I).mul_zero h6
      have E4 := h5.sub h7
      refine Bdd.congr (funext (fun w => ?_)) (E4.mul_zero (Bdd.const' ((2:ℂ)⁻¹)))
      rw [show Gcusp24 ℓ 0 1 ((n:ℝ)+ᵥw) = ((Real.pi:ℂ)/3 * (phiVec ((n:ℝ)+ᵥw) 0 * E14Fun ((n:ℝ)+ᵥw)
            + 720 * (phiVec ((n:ℝ)+ᵥw) 1 * DeltaFun ((n:ℝ)+ᵥw))
            - phiVec ((n:ℝ)+ᵥw) 1 * E4Fun ((n:ℝ)+ᵥw) ^ 3)
            - Complex.I * (720 * DeltaFun ((n:ℝ)+ᵥw) - E4Fun ((n:ℝ)+ᵥw) ^ 3)) / 2 from rfl]
      ring
    · change Bdd 0 (fun w : ℍ => Gcusp24 ℓ 1 0 ((n:ℝ)+ᵥw))
      have hE4c := ((Bdd.vadd_E4 n hn).mul_zero (Bdd.vadd_E4 n hn)).mul_zero (Bdd.vadd_E4 n hn)
      have h1 := (Bdd.vadd_phi0 n hn).mul_zero (Bdd.vadd_E14 n hn)
      have h2 := (Bdd.vadd_phi2 n hn).mul_zero (Bdd.vadd_E10 n hn)
      have h3 := (Bdd.const' (-(Complex.I/288))).mul_zero (h1.add h2)
      have h4 := (Bdd.const' (Complex.I/144)).mul_zero ((Bdd.vadd_phi1 n hn).mul_zero hE4c)
      have h5 := (Bdd.const' (7*Complex.I)).mul_zero ((Bdd.vadd_phi1 n hn).mul_zero (Bdd.vadd_Delta n hn))
      have h6 := (Bdd.const' (((Real.pi:ℂ))⁻¹)).mul_zero ((Bdd.vadd_Delta n hn).mul_zero (Bdd.const' (cuspL ℓ - 1)))
      have h7 := (Bdd.const' ((1152*(Real.pi:ℂ))⁻¹)).mul_zero
        (((Bdd.vadd_psi2 ℓ n hn).mul_zero (Bdd.vadd_E10 n hn)).sub ((Bdd.vadd_psi4 ℓ n hn).mul_zero (Bdd.vadd_E8 n hn)))
      have F1 := ((h3.add h4).sub h5)
      have F2 := ((F1.add h6).add h7)
      refine Bdd.congr (funext (fun w => ?_)) (F2.mul_zero (Bdd.const' ((2:ℂ)⁻¹)))
      rw [show Gcusp24 ℓ 1 0 ((n:ℝ)+ᵥw) = (-(Complex.I / 288) * (phiVec ((n:ℝ)+ᵥw) 0 * E14Fun ((n:ℝ)+ᵥw)
              + phiVec ((n:ℝ)+ᵥw) 2 * E10Fun ((n:ℝ)+ᵥw))
            + (Complex.I / 144) * (phiVec ((n:ℝ)+ᵥw) 1 * E4Fun ((n:ℝ)+ᵥw) ^ 3)
            - 7 * Complex.I * (phiVec ((n:ℝ)+ᵥw) 1 * DeltaFun ((n:ℝ)+ᵥw))
            + DeltaFun ((n:ℝ)+ᵥw) * (cuspL ℓ - 1) / (Real.pi:ℂ)
            + (psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)
              - psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)) / (1152 * (Real.pi:ℂ))) / 2 from rfl]
      ring
    · change Bdd 0 (fun w : ℍ => Gcusp24 ℓ 1 1 ((n:ℝ)+ᵥw))
      have hE4c := ((Bdd.vadd_E4 n hn).mul_zero (Bdd.vadd_E4 n hn)).mul_zero (Bdd.vadd_E4 n hn)
      have h1 := (Bdd.vadd_phi0 n hn).mul_zero (Bdd.vadd_E14 n hn)
      have h2 := (Bdd.vadd_phi2 n hn).mul_zero (Bdd.vadd_E10 n hn)
      have h3 := (Bdd.const' (1728:ℂ)).mul_zero ((Bdd.vadd_phi1 n hn).mul_zero (Bdd.vadd_Delta n hn))
      have h4 := (Bdd.const' (2:ℂ)).mul_zero ((Bdd.vadd_phi1 n hn).mul_zero hE4c)
      have h5 := ((h1.add h2).add (h3.sub h4))
      have h6 := (Bdd.const' ((Real.pi:ℂ)/864)).mul_zero h5
      have h7 := h6.add ((Bdd.const' Complex.I).mul_zero (Bdd.vadd_Delta n hn))
      refine Bdd.congr (funext (fun w => ?_)) (h7.mul_zero (Bdd.const' ((2:ℂ)⁻¹)))
      rw [show Gcusp24 ℓ 1 1 ((n:ℝ)+ᵥw) = ((Real.pi:ℂ)/864 * (phiVec ((n:ℝ)+ᵥw) 0 * E14Fun ((n:ℝ)+ᵥw)
            + phiVec ((n:ℝ)+ᵥw) 2 * E10Fun ((n:ℝ)+ᵥw)
            + 1728 * (phiVec ((n:ℝ)+ᵥw) 1 * DeltaFun ((n:ℝ)+ᵥw))
            - 2 * (phiVec ((n:ℝ)+ᵥw) 1 * E4Fun ((n:ℝ)+ᵥw) ^ 3))
            + Complex.I * DeltaFun ((n:ℝ)+ᵥw)) / 2 from rfl]
      ring
  rcases hd with rfl | rfl
  · change Bdd 0 (fun w : ℍ => Gcusp8 ℓ i j ((n:ℝ)+ᵥw))
    exact key8 i j
  · change Bdd 0 (fun w : ℍ => Gcusp24 ℓ i j ((n:ℝ)+ᵥw))
    exact key24 i j


theorem Gcusp_tile_bound (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon →
      ∀ i j : Fin 2, ‖Gcusp ℓ d i j ((n:ℝ)+ᵥw)‖ ≤ C * (scale w) ^ N := by
  have get : ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ), w ∈ KEpsilon → ∀ i j : Fin 2, ‖Gcusp ℓ d i j ((n:ℝ)+ᵥw)‖ ≤ C * (scale w) ^ N := by
    intro n hn
    have h1 : ∀ i j : Fin 2, Bdd 0 (fun w : ℍ => Gcusp ℓ d i j ((n:ℝ)+ᵥw)) :=
      fun i j => Gcusp_Bdd ℓ d hd n hn i j
    obtain ⟨C1, N1, hC1, hN1, hb1⟩ := Bdd.exists_bound_zero (h1 0 0)
    obtain ⟨C2, N2, hC2, hN2, hb2⟩ := Bdd.exists_bound_zero (h1 0 1)
    obtain ⟨C3, N3, hC3, hN3, hb3⟩ := Bdd.exists_bound_zero (h1 1 0)
    obtain ⟨C4, N4, hC4, hN4, hb4⟩ := Bdd.exists_bound_zero (h1 1 1)
    refine ⟨C1+C2+C3+C4, max (max N1 N2) (max N3 N4), by positivity, by positivity, ?_⟩
    intro w hw i j
    have hN1' : N1 ≤ max (max N1 N2) (max N3 N4) := le_trans (le_max_left _ _) (le_max_left _ _)
    have hN2' : N2 ≤ max (max N1 N2) (max N3 N4) := le_trans (le_max_right _ _) (le_max_left _ _)
    have hN3' : N3 ≤ max (max N1 N2) (max N3 N4) := le_trans (le_max_left _ _) (le_max_right _ _)
    have hN4' : N4 ≤ max (max N1 N2) (max N3 N4) := le_trans (le_max_right _ _) (le_max_right _ _)
    fin_cases i <;> fin_cases j
    · refine le_trans (hb1 w hw) ?_
      exact mul_le_mul (by linarith [hC2.le, hC3.le, hC4.le]) (EtailE.E_rpow_mono w hN1')
        (EtailE.E_rpow_nonneg w N1) (by positivity)
    · refine le_trans (hb2 w hw) ?_
      exact mul_le_mul (by linarith [hC1.le, hC3.le, hC4.le]) (EtailE.E_rpow_mono w hN2')
        (EtailE.E_rpow_nonneg w N2) (by positivity)
    · refine le_trans (hb3 w hw) ?_
      exact mul_le_mul (by linarith [hC1.le, hC2.le, hC4.le]) (EtailE.E_rpow_mono w hN3')
        (EtailE.E_rpow_nonneg w N3) (by positivity)
    · refine le_trans (hb4 w hw) ?_
      exact mul_le_mul (by linarith [hC1.le, hC2.le, hC3.le]) (EtailE.E_rpow_mono w hN4')
        (EtailE.E_rpow_nonneg w N4) (by positivity)
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := get 1 (Or.inl rfl)
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := get (-1) (Or.inr rfl)
  refine ⟨C1+C2, max N1 N2, by positivity, by positivity, ?_⟩
  intro w n hn hw i j
  rcases hn with h | h
  · subst h
    refine le_trans (hb1 w hw i j) ?_
    exact mul_le_mul (by linarith [hC2.le]) (EtailE.E_rpow_mono w (le_max_left _ _))
      (EtailE.E_rpow_nonneg w N1) (by positivity)
  · subst h
    refine le_trans (hb2 w hw i j) ?_
    exact mul_le_mul (by linarith [hC1.le]) (EtailE.E_rpow_mono w (le_max_right _ _))
      (EtailE.E_rpow_nonneg w N2) (by positivity)

end Work.Asymptotics

