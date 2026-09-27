/-
# Step 9 of `ROUTE_LEAD.md` §5 (EKL Step 4): existence of the shear parameter `r`.

Given a probability-like measure `ν` on `ℝ` normalised by `ν[-1,1] = 1` which is `BadAt ν ρ R`
(i.e. `ν[-ρR, ρR] < ½ ν[-R, R]`, the conclusion of EKL Lemma 4.5/4.6), and two measurable sets
`P, P' ⊆ [-R, R]` each carrying all but an `ε²`-fraction of the mass of `[-R, R]`, there is a
point `r ∈ P ∩ P'` in the annulus `ρR < |r| ≤ R`.

Proof.  Since `R ≥ 1`, monotonicity of `Measure.real` together with `ν[-1,1] = 1` gives
`V := ν.real [-R,R] ≥ 1 > 0`.  Inclusion–exclusion
(`ν.real (P ∪ P') + ν.real (P ∩ P') = ν.real P + ν.real P'`) together with
`ν.real (P ∪ P') ≤ V` and the two density hypotheses gives

  `ν.real (P ∩ P') ≥ (1 - 2ε²) · V > V/2`.

If no point of `P ∩ P'` lay in the annulus, then (as `P ∩ P' ⊆ [-R,R]`)
`P ∩ P' ⊆ [-ρR, ρR]`, whence by monotonicity and `BadAt`

  `ν.real (P ∩ P') ≤ ν.real [-ρR, ρR] < V/2`,

contradiction.
-/
import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

open MeasureTheory

theorem step9_exists_r {ν : MeasureTheory.Measure ℝ} {ε ρ R : ℝ} {P P' : Set ℝ}
    (hε : 0 < ε) (hε2 : 2 * ε ^ 2 < 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R)
    (hν : ν.real (Set.Icc (-1) 1) = 1) (hfin : ν (Set.Icc (-R) R) ≠ ⊤)
    (hPm : MeasurableSet P) (hP'm : MeasurableSet P')
    (hPR : P ⊆ Set.Icc (-R) R) (hP'R : P' ⊆ Set.Icc (-R) R)
    (hP : (1 - ε ^ 2) * ν.real (Set.Icc (-R) R) ≤ ν.real P)
    (hP' : (1 - ε ^ 2) * ν.real (Set.Icc (-R) R) ≤ ν.real P')
    (hbad : BadAt ν ρ R) :
    ∃ r ∈ P ∩ P', ρ * R < |r| ∧ |r| ≤ R := by
  by_contra hcon
  -- no point of `P ∩ P'` lies in the annulus
  have hcon' : ∀ r, r ∈ P ∩ P' → ¬ (ρ * R < |r| ∧ |r| ≤ R) := by
    intro r hr h
    exact hcon ⟨r, hr, h⟩
  -- hence `P ∩ P'` is contained in the contracted interval `[-ρR, ρR]`
  have hsub : P ∩ P' ⊆ Set.Icc (-(ρ * R)) (ρ * R) := by
    intro x hx
    have hxR : |x| ≤ R := by
      have h := hPR hx.1
      simp only [Set.mem_Icc] at h
      exact abs_le.mpr h
    have hxle : |x| ≤ ρ * R := by
      by_contra hlt
      exact hcon' x hx ⟨lt_of_not_ge hlt, hxR⟩
    exact Set.mem_Icc.mpr (abs_le.mp hxle)
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  -- `V := ν.real [-R,R]` is positive
  have hVpos : 0 < ν.real (Set.Icc (-R) R) := by
    have h1 : ν.real (Set.Icc (-1) 1) ≤ ν.real (Set.Icc (-R) R) :=
      measureReal_mono (by
        intro x hx
        simp only [Set.mem_Icc] at hx ⊢
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) hfin
    rw [hν] at h1
    linarith
  have hPfin : ν P ≠ ⊤ := measure_ne_top_of_subset hPR hfin
  have hP'fin : ν P' ≠ ⊤ := measure_ne_top_of_subset hP'R hfin
  -- inclusion–exclusion
  have hIE := measureReal_union_add_inter (μ := ν) (s := P) (t := P') hP'm hPfin hP'fin
  have hunion_le : ν.real (P ∪ P') ≤ ν.real (Set.Icc (-R) R) :=
    measureReal_mono (Set.union_subset hPR hP'R) hfin
  -- the lower bound
  have hlower : (1 - 2 * ε ^ 2) * ν.real (Set.Icc (-R) R) ≤ ν.real (P ∩ P') := by
    have h : ν.real (P ∩ P') = ν.real P + ν.real P' - ν.real (P ∪ P') := by linarith
    rw [h]
    nlinarith [hP, hP', hunion_le]
  -- the upper bound, from `BadAt` and monotonicity
  have hrhoR : ν.real (Set.Icc (-(ρ * R)) (ρ * R)) < (1 / 2) * ν.real (Set.Icc (-R) R) := hbad
  have hrsub : Set.Icc (-(ρ * R)) (ρ * R) ⊆ Set.Icc (-R) R := by
    intro x hx
    simp only [Set.mem_Icc] at hx ⊢
    have hρR : ρ * R ≤ R := by nlinarith [hρ1, hRpos]
    exact ⟨by linarith [hx.1, hρR], by linarith [hx.2, hρR]⟩
  have hupper : ν.real (P ∩ P') < (1 / 2) * ν.real (Set.Icc (-R) R) :=
    lt_of_le_of_lt (measureReal_mono hsub (measure_ne_top_of_subset hrsub hfin)) hrhoR
  have hgt : (1 / 2) * ν.real (Set.Icc (-R) R) < (1 - 2 * ε ^ 2) * ν.real (Set.Icc (-R) R) :=
    mul_lt_mul_of_pos_right (by linarith) hVpos
  linarith [hlower, hupper, hgt]

end Work.EKLC8Core
