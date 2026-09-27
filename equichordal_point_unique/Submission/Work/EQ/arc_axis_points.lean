import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.normEqCurve_periodic_and_sum
import Submission.Work.EQ.normEqCurve_structure

namespace Work.EQ

open Complex

/-- Complex conjugation of `polarPt` for real data: `conj (c + r·e^{iθ}) = c + r·e^{-iθ}`. -/
lemma conj_polarPt (c r θ : ℝ) :
    (starRingEnd ℂ) (polarPt c r θ) = polarPt c r (-θ) := by
  simp only [polarPt, map_add, Complex.conj_ofReal, map_mul]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring_nf

/-- Negation of `polarPt`: `-(c + r·e^{iθ}) = -c + r·e^{i(θ+π)}`. -/
lemma neg_polarPt (c r θ : ℝ) :
    - polarPt c r θ = polarPt (-c) r (θ + Real.pi) := by
  simp only [polarPt]
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  push_cast
  ring

/-- `-conj (polarPt c r θ) = polarPt (-c) r (π - θ)`. -/
lemma neg_conj_polarPt (c r θ : ℝ) :
    -(starRingEnd ℂ) (polarPt c r θ) = polarPt (-c) r (Real.pi - θ) := by
  rw [conj_polarPt, neg_polarPt]
  congr 1
  ring

/-- The two points where a symmetric normalised equichordal curve meets the axis are `∓1/2`.

`ρ₁ (θ+π) = 1 - ρ₁ θ` gives `P 0 - P π = 1`; `hs₁` gives `conj (P θ) = P (-θ)` and `hs₂`
gives `-(conj (P θ)) = polarPt (a/2) (ρ₂ (π-θ)) (π-θ) ∈ c`, so `-P θ ∈ c` for every `θ`: the
curve is invariant under `z ↦ -z`.  Hence `-P π` is a real point of the curve, hence (all real
points of the curve are `P 0` or `P π`) it is `P 0` or `P π`.  It cannot be `P π`, since that
would give `ρ₁ π = -a/2 < 0`.  So `P 0 = -P π`, and `P 0 - P π = 1` gives `P π = -1/2`. -/
theorem arc_axis_points {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ)
    (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) :
    polarPt (-(a / 2)) (ρ₁ Real.pi) Real.pi = (-(1 / 2) : ℂ) ∧
    polarPt (-(a / 2)) (ρ₁ 0) 0 = ((1 / 2) : ℂ) ∧
    ρ₁ Real.pi = (1 - a) / 2 ∧ ρ₁ 0 = (1 + a) / 2 := by
  obtain ⟨hcont₁, hcont₂, hpos₁, hpos₂, hchord₁, hchord₂, hrange⟩ := hC
  -- (1) `conj (P θ) = P (-θ) ∈ c`
  have hconjmem : ∀ θ, (starRingEnd ℂ) (polarPt (-(a / 2)) (ρ₁ θ) θ) ∈
      Set.range (fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ) := by
    intro θ
    rw [conj_polarPt, ← hs₁ θ]
    exact Set.mem_range_self (-θ)
  -- (2) `-conj (P θ) = polarPt (a/2) (ρ₂ (π - θ)) (π - θ) ∈ c`
  have hnegconjmem : ∀ θ, -(starRingEnd ℂ) (polarPt (-(a / 2)) (ρ₁ θ) θ) ∈
      Set.range (fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ) := by
    intro θ
    have hkey : -(starRingEnd ℂ) (polarPt (-(a / 2)) (ρ₁ θ) θ)
        = polarPt (a / 2) (ρ₂ (Real.pi - θ)) (Real.pi - θ) := by
      rw [neg_conj_polarPt]
      simp only [neg_neg]
      have hr : ρ₁ θ = ρ₂ (Real.pi - θ) := by rw [hs₂ (Real.pi - θ)]; ring_nf
      rw [hr]
    rw [hkey, hrange]
    exact Set.mem_range_self (Real.pi - θ)
  -- (3) the curve is invariant under conjugation
  have hconjimg : (starRingEnd ℂ) '' (Set.range (fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ)) ⊆
      Set.range (fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨φ, rfl⟩ := hx
    exact hconjmem φ
  -- (4) `-P θ ∈ c` for every `θ`
  have hnegmem : ∀ θ, -(polarPt (-(a / 2)) (ρ₁ θ) θ) ∈
      Set.range (fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ) := by
    intro θ
    have h2 : (starRingEnd ℂ) (-(starRingEnd ℂ) (polarPt (-(a / 2)) (ρ₁ θ) θ)) ∈
        Set.range (fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ) :=
      hconjimg ⟨-(starRingEnd ℂ) (polarPt (-(a / 2)) (ρ₁ θ) θ), hnegconjmem θ, rfl⟩
    simpa using h2
  -- `P π` and `-P π` are real
  have hPpi_im : (polarPt (-(a / 2)) (ρ₁ Real.pi) Real.pi).im = 0 := by
    rw [nec_polarPt_im, Real.sin_pi, mul_zero]
  have hnegPpi_mem : -(polarPt (-(a / 2)) (ρ₁ Real.pi) Real.pi) ∈
      Set.range (fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ) := hnegmem Real.pi
  have hnegPpi_im : (-(polarPt (-(a / 2)) (ρ₁ Real.pi) Real.pi)).im = 0 := by
    rw [Complex.neg_im, hPpi_im, neg_zero]
  -- all real points of the curve are `P 0` or `P π`
  have hcases := nec_real_pt_of_chord (c := -(a / 2)) hpos₁ hchord₁ hnegPpi_mem hnegPpi_im
  -- `-P π ≠ P π`
  have hPpi_ne : -(polarPt (-(a / 2)) (ρ₁ Real.pi) Real.pi) ≠
      polarPt (-(a / 2)) (ρ₁ Real.pi) Real.pi := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.neg_re, nec_polarPt_pi] at hre
    simp only [Complex.ofReal_re] at hre
    linarith [hpos₁ Real.pi, ha0]
  have hP0_eq : polarPt (-(a / 2)) (ρ₁ 0) 0 =
      -(polarPt (-(a / 2)) (ρ₁ Real.pi) Real.pi) := by
    rcases hcases with h | h
    · exact h.symm
    · exact absurd h hPpi_ne
  -- `P 0 - P π = 1`
  have hdiff : polarPt (-(a / 2)) (ρ₁ 0) 0 - polarPt (-(a / 2)) (ρ₁ Real.pi) Real.pi = 1 := by
    have hx : (-(a / 2) + ρ₁ 0) - (-(a / 2) - ρ₁ Real.pi) = (1 : ℝ) := by
      have h := hchord₁ 0
      simp only [zero_add] at h
      linarith
    rw [nec_polarPt_zero, nec_polarPt_pi, ← Complex.ofReal_sub, hx]
    norm_num
  -- the values
  have hPpi_val : polarPt (-(a / 2)) (ρ₁ Real.pi) Real.pi = -(1 / 2 : ℂ) := by
    have h := hdiff
    rw [hP0_eq] at h
    linear_combination (-1 / 2) * h
  have hP0_val : polarPt (-(a / 2)) (ρ₁ 0) 0 = (1 / 2 : ℂ) := by
    rw [hP0_eq, hPpi_val]
    norm_num
  have hrho_pi : ρ₁ Real.pi = (1 - a) / 2 := by
    have h := congrArg Complex.re hPpi_val
    rw [nec_polarPt_pi] at h
    simp only [Complex.ofReal_re, Complex.neg_re] at h
    norm_num at h
    linarith
  have hrho_0 : ρ₁ 0 = (1 + a) / 2 := by
    have h := congrArg Complex.re hP0_val
    rw [nec_polarPt_zero] at h
    simp only [Complex.ofReal_re] at h
    norm_num at h
    linarith
  exact ⟨hPpi_val, hP0_val, hrho_pi, hrho_0⟩

end Work.EQ
