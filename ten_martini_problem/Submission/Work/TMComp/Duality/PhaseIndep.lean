import Mathlib
import Submission.Work.TMComp.Duality.Defs
import Submission.Work.TMComp.Duality.Basic
import Submission.Work.TMC7Core.Scale.spectral_continuity
import Submission.Work.TMComp.Duality.amoOp_selfAdjoint

/-!
# Aubry duality (C3): independence of the phase

For irrational `α` the spectrum of `amoOp α lam θ` is independent of the phase `θ`: shifts by
`α` and by `1` are unitary equivalences, the set of phases with a given spectrum is closed
(spectral perturbation), and `ℤα + ℤ` is dense.
-/

open LeanEval.Analysis.TenMartini

open scoped ENNReal

open Filter Topology Set

noncomputable section

namespace Work.TMComp.Duality

/-! ## 1. Translation invariance of the phase -/

theorem shiftZ_mul (k l : ℤ) : shiftZ k * shiftZ l = shiftZ (k + l) := by
  refine coord_ext fun f n => ?_
  simp only [mul_apply_eq_comp, shiftZ_coord, add_assoc]

theorem shiftZ_zero : shiftZ 0 = (1 : EllTwo →L[ℂ] EllTwo) := by
  refine coord_ext fun f n => ?_
  rw [shiftZ_coord]
  simp

/-- The shift `shiftZ 1` as a unit. -/
def shiftUnit : (EllTwo →L[ℂ] EllTwo)ˣ where
  val := shiftZ 1
  inv := shiftZ (-1)
  val_inv := by rw [shiftZ_mul, show (1 : ℤ) + -1 = 0 by norm_num, shiftZ_zero]
  inv_val := by rw [shiftZ_mul, show (-1 : ℤ) + 1 = 0 by norm_num, shiftZ_zero]

theorem amoOp_shift_conj (α lam θ : ℝ) :
    shiftZ 1 * amoOp α lam θ * shiftZ (-1) = amoOp α lam (θ + α) := by
  refine coord_ext fun f n => ?_
  simp only [mul_apply_eq_comp, shiftZ_coord, amoOp_coord, sub_eq_add_neg]
  have hc : ((2 * lam * Real.cos (2 * Real.pi * (θ + ((((n : ℤ) + 1 : ℤ)) : ℝ) * α)) : ℝ) : ℂ)
      = ((2 * lam * Real.cos (2 * Real.pi * (θ + α + (n : ℝ) * α)) : ℝ) : ℂ) := by
    congr 1
    congr 1
    push_cast
    ring
  rw [show n + 1 + 1 + -1 = n + 1 by omega, show n + 1 + -1 = n by omega, hc]

theorem amoOp_phase_shift (α lam θ : ℝ) :
    spectrum ℂ (amoOp α lam (θ + α)) = spectrum ℂ (amoOp α lam θ) := by
  have h := spectrum.units_conjugate (R := ℂ) (a := amoOp α lam θ) (u := shiftUnit)
  have hval : (↑shiftUnit : EllTwo →L[ℂ] EllTwo) = shiftZ 1 := rfl
  have hinv : (↑shiftUnit⁻¹ : EllTwo →L[ℂ] EllTwo) = shiftZ (-1) := rfl
  rw [hval, hinv, amoOp_shift_conj] at h
  exact h

theorem amoOp_period (α lam θ : ℝ) : amoOp α lam (θ + 1) = amoOp α lam θ := by
  refine coord_ext fun f n => ?_
  rw [amoOp_coord, amoOp_coord]
  have hc : ((2 * lam * Real.cos (2 * Real.pi * (θ + 1 + (n : ℝ) * α)) : ℝ) : ℂ)
      = ((2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)) : ℝ) : ℂ) := by
    congr 1
    congr 1
    rw [show 2 * Real.pi * (θ + 1 + (n : ℝ) * α)
          = 2 * Real.pi * (θ + (n : ℝ) * α) + 2 * Real.pi by ring, Real.cos_add_two_pi]
  rw [hc]

/-! ## 2. The spectrum is independent of the phase -/

theorem spectrum_gap_of_notMem {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] [Nontrivial X] (A : X →L[ℂ] X) (E : ℝ)
    (hE : (E : ℂ) ∉ spectrum ℂ A) :
    ∃ d : ℝ, 0 < d ∧ ∀ w ∈ spectrum ℂ A, d ≤ ‖w - (E : ℂ)‖ := by
  obtain ⟨w₀, hw₀mem, hw₀min⟩ := (spectrum.isCompact A).exists_isMinOn (spectrum.nonempty A)
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
  refine ⟨‖w₀ - (E : ℂ)‖, ?_, fun w hw => hw₀min hw⟩
  refine norm_pos_iff.mpr fun h => hE ?_
  have hw : w₀ = (E : ℂ) := sub_eq_zero.mp h
  rwa [hw] at hw₀mem

theorem amoOp_spectrum_phase (α lam : ℝ) (hα : Irrational α) (θ θ' : ℝ) :
    spectrum ℂ (amoOp α lam θ) = spectrum ℂ (amoOp α lam θ') := by
  set G : AddSubgroup ℝ := AddSubgroup.closure ({α, 1} : Set ℝ) with hG
  have hGmem : ∀ φ ∈ G, ∀ θ : ℝ,
      spectrum ℂ (amoOp α lam (θ + φ)) = spectrum ℂ (amoOp α lam θ) := by
    intro φ hφ
    refine AddSubgroup.closure_induction (p := fun φ _ => ∀ θ : ℝ,
      spectrum ℂ (amoOp α lam (θ + φ)) = spectrum ℂ (amoOp α lam θ)) ?_ ?_ ?_ ?_ hφ
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · intro θ; rw [hx]; exact amoOp_phase_shift α lam θ
      · intro θ; rw [hx, amoOp_period α lam θ]
    · intro θ; simp
    · intro x y _ _ hx hy θ
      rw [show θ + (x + y) = θ + x + y by ring, hy (θ + x), hx θ]
    · intro x _ hx θ
      have h := hx (θ + (-x))
      rw [show θ + -x + x = θ by ring] at h
      exact h.symm
  have hdense : Dense ((G : AddSubgroup ℝ) : Set ℝ) := by
    rw [hG]
    exact (dense_addSubgroupClosure_pair_iff (a := α) (b := 1)).mpr (by simpa using hα)
  have hsubset : ∀ (u : ℕ → ℝ) (ψ θ : ℝ), Tendsto u atTop (𝓝 ψ) →
      (∀ n, spectrum ℂ (amoOp α lam (θ + u n)) = spectrum ℂ (amoOp α lam θ)) →
      spectrum ℂ (amoOp α lam (θ + ψ)) ⊆ spectrum ℂ (amoOp α lam θ) := by
    intro u ψ θ hu hspec z hz
    have hzre : z = (z.re : ℂ) := (amoOp_selfAdjoint α lam (θ + ψ)).mem_spectrum_eq_re hz
    set E : ℝ := z.re with hEdef
    have hzE : (E : ℂ) ∈ spectrum ℂ (amoOp α lam (θ + ψ)) := by
      rw [hEdef, ← hzre]; exact hz
    have hex : ∀ n, ∃ w ∈ spectrum ℂ (amoOp α lam θ),
        ‖w - (E : ℂ)‖ ≤ 4 * Real.pi * |lam| * |ψ - u n| := by
      intro n
      have hδ : ‖amoOp α lam (θ + ψ) - amoOp α lam (θ + u n)‖
          ≤ 4 * Real.pi * |lam| * |ψ - u n| := by
        simpa only [add_sub_add_left_eq_sub] using amoOp_norm_sub_le α lam (θ + ψ) (θ + u n)
      obtain ⟨w, hw, hwle⟩ := spectrum_dist_le_of_norm_sub_le _ _
        (amoOp_selfAdjoint α lam (θ + ψ)) (amoOp_selfAdjoint α lam (θ + u n)) hδ hzE
      exact ⟨w, by rw [hspec n] at hw; exact hw, hwle⟩
    choose w hwmem hwle using hex
    have hwtend : Tendsto w atTop (𝓝 (E : ℂ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 : Tendsto (fun n => |ψ - u n|) atTop (𝓝 0) := by
        have h2 : Tendsto (fun n => ψ - u n) atTop (𝓝 (ψ - ψ)) :=
          tendsto_const_nhds.sub hu
        simpa using h2.norm
      have h3 : Tendsto (fun n => 4 * Real.pi * |lam| * |ψ - u n|) atTop (𝓝 0) := by
        simpa using h1.const_mul (4 * Real.pi * |lam|)
      exact squeeze_zero (fun n => norm_nonneg _) (fun n => hwle n) h3
    have hcl := IsClosed.mem_of_tendsto (spectrum.isClosed (amoOp α lam θ)) hwtend
      (Eventually.of_forall hwmem)
    have hzE' : z = (E : ℂ) := by rw [hzre, hEdef]
    rw [hzE']
    exact hcl
  have hsupset : ∀ (u : ℕ → ℝ) (ψ θ : ℝ), Tendsto u atTop (𝓝 ψ) →
      (∀ n, spectrum ℂ (amoOp α lam (θ + u n)) = spectrum ℂ (amoOp α lam θ)) →
      spectrum ℂ (amoOp α lam θ) ⊆ spectrum ℂ (amoOp α lam (θ + ψ)) := by
    intro u ψ θ hu hspec z hz
    have hzre : z = (z.re : ℂ) := (amoOp_selfAdjoint α lam θ).mem_spectrum_eq_re hz
    set E : ℝ := z.re with hEdef
    have hzE : (E : ℂ) ∈ spectrum ℂ (amoOp α lam θ) := by
      rw [hEdef, ← hzre]; exact hz
    have hex : ∀ n, ∃ w ∈ spectrum ℂ (amoOp α lam (θ + ψ)),
        ‖w - (E : ℂ)‖ ≤ 4 * Real.pi * |lam| * |ψ - u n| := by
      intro n
      have hδ : ‖amoOp α lam (θ + u n) - amoOp α lam (θ + ψ)‖
          ≤ 4 * Real.pi * |lam| * |ψ - u n| := by
        have h := amoOp_norm_sub_le α lam (θ + u n) (θ + ψ)
        rw [show θ + u n - (θ + ψ) = -(ψ - u n) by ring, abs_neg] at h
        exact h
      obtain ⟨w, hw, hwle⟩ := spectrum_dist_le_of_norm_sub_le _ _
        (amoOp_selfAdjoint α lam (θ + u n)) (amoOp_selfAdjoint α lam (θ + ψ)) hδ
        ((hspec n) ▸ hzE)
      exact ⟨w, hw, hwle⟩
    choose w hwmem hwle using hex
    have hwtend : Tendsto w atTop (𝓝 (E : ℂ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 : Tendsto (fun n => |ψ - u n|) atTop (𝓝 0) := by
        have h2 : Tendsto (fun n => ψ - u n) atTop (𝓝 (ψ - ψ)) :=
          tendsto_const_nhds.sub hu
        simpa using h2.norm
      have h3 : Tendsto (fun n => 4 * Real.pi * |lam| * |ψ - u n|) atTop (𝓝 0) := by
        simpa using h1.const_mul (4 * Real.pi * |lam|)
      exact squeeze_zero (fun n => norm_nonneg _) (fun n => hwle n) h3
    have hcl := IsClosed.mem_of_tendsto (spectrum.isClosed (amoOp α lam (θ + ψ))) hwtend
      (Eventually.of_forall hwmem)
    have hzE' : z = (E : ℂ) := by rw [hzre, hEdef]
    rw [hzE']
    exact hcl
  have hmain : ∀ ψ θ : ℝ, spectrum ℂ (amoOp α lam (θ + ψ)) = spectrum ℂ (amoOp α lam θ) := by
    intro ψ θ
    have hmem : ψ ∈ closure ((G : AddSubgroup ℝ) : Set ℝ) := by rw [hdense.closure_eq]; trivial
    have hex : ∀ n : ℕ, ∃ φ ∈ G, |φ - ψ| < (1 : ℝ) / ((n : ℝ) + 1) := by
      intro n
      have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨φ, hφG, hφd⟩ := Metric.mem_closure_iff.mp hmem (1 / ((n : ℝ) + 1)) hn
      exact ⟨φ, hφG, by rwa [Real.dist_eq, abs_sub_comm] at hφd⟩
    choose u huG hucl using hex
    have hutend : Tendsto u atTop (𝓝 ψ) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h1
      rw [Real.norm_eq_abs]
      exact le_of_lt (hucl n)
    refine le_antisymm (hsubset u ψ θ hutend (fun n => hGmem (u n) (huG n) θ))
      (hsupset u ψ θ hutend (fun n => hGmem (u n) (huG n) θ))
  have hfin := hmain (θ' - θ) θ
  rw [show θ + (θ' - θ) = θ' by ring] at hfin
  exact hfin.symm

end Work.TMComp.Duality
