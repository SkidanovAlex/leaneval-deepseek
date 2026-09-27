import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.exists_int_sub_mul_two_pi_mem_Ioo
import Submission.Work.EQ.polarPt_basic
import Submission.Work.EQ.polarPt_inj
import Submission.Work.EQ.normEqCurve_periodic_and_sum

namespace Work.EQ


/-- **Canonical angle for a point of a polar graph in the open upper half plane.**

Let `ρ` be `2π`-periodic and positive and let `z` lie on the polar graph of `ρ` about the real
point `c`, with `z - c` in the open upper half plane.  Then `z` has a polar representation
`z = polarPt c (ρ φ) φ` whose angle `φ` lies in the open interval `(0, π)`.

The point of the argument is the reduction modulo `2π`: if `z = polarPt c (ρ ψ) ψ` then
`(z - c).im = ρ ψ * sin ψ > 0`, so `sin ψ > 0`; replacing `ψ` by `ψ - 2πk ∈ (0, π)` leaves both
`ρ` (by periodicity) and `exp (ψ I)` (since `exp (-2πk I) = 1`) unchanged. -/
theorem exists_angle_of_mem_range {ρ : ℝ → ℝ} (hper : Function.Periodic ρ (2 * Real.pi))
    (hpos : ∀ θ, 0 < ρ θ) {c : ℝ} {z : ℂ}
    (hz : z ∈ Set.range fun θ => polarPt c (ρ θ) θ) (him : 0 < (z - (c : ℂ)).im) :
    ∃ φ, 0 < φ ∧ φ < Real.pi ∧ z = polarPt c (ρ φ) φ := by
  obtain ⟨ψ, rfl⟩ := hz
  obtain ⟨him_basic, hsub, -, -⟩ := polarPt_basic (c := c) (r := ρ ψ) (θ := ψ) (hpos ψ)
  have himψ : 0 < ρ ψ * Real.sin ψ := by
    have h1 : (polarPt c (ρ ψ) ψ - (c : ℂ)).im = (polarPt c (ρ ψ) ψ).im := by simp
    rw [h1, him_basic] at him
    exact him
  have hsin : 0 < Real.sin ψ := (mul_pos_iff_of_pos_left (hpos ψ)).mp himψ
  obtain ⟨k, hk0, hkπ⟩ := exists_int_sub_mul_two_pi_mem_Ioo hsin
  refine ⟨ψ - k * (2 * Real.pi), hk0, hkπ, ?_⟩
  have hper2 : ρ (ψ - k * (2 * Real.pi)) = ρ ψ := by
    have h1 : ψ - (k : ℝ) * (2 * Real.pi) = ψ + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [h1]
    exact hper.int_mul (-k) ψ
  have hexp : Complex.exp (((ψ - k * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((ψ : ℂ) * Complex.I) := by
    have h1 : ((ψ - k * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
        = (ψ : ℂ) * Complex.I + ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [polarPt]
  rw [← hper2, ← hexp]

/-- The open upper arc of a symmetric normalised equichordal curve is invariant under the
half-map `eqU` (which acts on it injectively) and under the bisector reflection `z ↦ -conj z`.

Write `P θ = polarPt (-(a/2)) (ρ₁ θ) θ`: the open upper arc is `{P θ : θ ∈ (0,π)}` (indeed
`(P θ).im = ρ₁ θ * sin θ` and `ρ₁ > 0`).  Facts used, from `NormEqCurve` and the two symmetry
hypotheses: `ρ₁ (θ+π) = 1 - ρ₁ θ`, `ρ₁ (-θ) = ρ₁ θ` (`hs₁`), `ρ₂ θ = ρ₁ (π-θ)` (`hs₂`), hence
`ρ₂ φ = 1 - ρ₁ φ` for all `φ`.

For any point `P = O₂ + r₂ e^{iφ}` (`O₂ = a/2`, `r₂ = |P - O₂| > 0`, `φ = arg (P - O₂)`) one has
`eqU a P = -O₂ + (1 - r₂) e^{iφ}`.  For `P = P θ`, `θ ∈ (0,π)`: `P - O₂` lies in the upper half
plane, so `φ ∈ (0,π)`, and `r₂ = ρ₂ φ`, so `eqU a (P θ) = P φ`.  `eqU a P` determines `φ` and `r₂`
and hence `P`, giving injectivity.  Finally
`-(conj (P θ)) = O₂ - ρ₁ θ e^{-iθ} = O₂ + ρ₁ θ e^{i(π-θ)}` is the point of the arc at O₁-angle
`π - θ` (its radius there is `ρ₂ (π-θ) = ρ₁ θ`). -/
theorem arc_eqU_maps {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ)
    (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) :
    (∀ θ, 0 < θ → θ < Real.pi → ∃ θ', 0 < θ' ∧ θ' < Real.pi ∧
        eqU a (polarPt (-(a/2)) (ρ₁ θ) θ) = polarPt (-(a/2)) (ρ₁ θ') θ') ∧
    (∀ θ θ', 0 < θ → θ < Real.pi → 0 < θ' → θ' < Real.pi →
        eqU a (polarPt (-(a/2)) (ρ₁ θ) θ) = eqU a (polarPt (-(a/2)) (ρ₁ θ') θ') → θ = θ') ∧
    (∀ θ, 0 < θ → θ < Real.pi → ∃ θ', 0 < θ' ∧ θ' < Real.pi ∧
        -(starRingEnd ℂ) (polarPt (-(a/2)) (ρ₁ θ) θ) = polarPt (-(a/2)) (ρ₁ θ') θ') := by
  have _ha0 := ha0
  have _ha1 := ha1
  obtain ⟨hper₁', hper₂', hρ₂_eq⟩ := normEqCurve_periodic_and_sum hC hs₁ hs₂
  obtain ⟨-, -, hρ₁pos, hρ₂pos, hper₁, hper₂, hrange⟩ := hC
  -- The key step: `P θ` is the point of the curve with `O₂`-angle `φ ∈ (0,π)` and radius
  -- `ρ₂ φ`, and `eqU` maps it to `P φ`.
  have key : ∀ θ : ℝ, 0 < θ → θ < Real.pi →
      ∃ φ : ℝ, 0 < φ ∧ φ < Real.pi ∧
        polarPt (-(a/2)) (ρ₁ θ) θ = polarPt (a/2) (ρ₂ φ) φ ∧
        eqU a (polarPt (-(a/2)) (ρ₁ θ) θ) = polarPt (-(a/2)) (ρ₁ φ) φ := by
    intro θ hθ0 hθπ
    -- `P θ` lies on the polar graph of `ρ₂` about `O₂ = a/2`
    have hmem : polarPt (-(a/2)) (ρ₁ θ) θ ∈ Set.range (fun φ => polarPt (a/2) (ρ₂ φ) φ) := by
      rw [← hrange]
      exact ⟨θ, rfl⟩
    -- and above `O₂`, since `(P θ - O₂).im = ρ₁ θ * sin θ > 0`
    have him : 0 < (polarPt (-(a/2)) (ρ₁ θ) θ - ((a/2 : ℝ) : ℂ)).im := by
      have h1 : (polarPt (-(a/2)) (ρ₁ θ) θ - ((a/2 : ℝ) : ℂ)).im
          = (polarPt (-(a/2)) (ρ₁ θ) θ).im := by simp
      have h2 := (polarPt_basic (c := -(a/2)) (r := ρ₁ θ) (θ := θ) (hρ₁pos θ)).1
      rw [h1, h2]
      exact mul_pos (hρ₁pos θ) (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ)
    obtain ⟨φ, hφ0, hφπ, hφ⟩ := exists_angle_of_mem_range hper₂' hρ₂pos hmem him
    refine ⟨φ, hφ0, hφπ, hφ, ?_⟩
    obtain ⟨-, hsub, hnorm, -⟩ := polarPt_basic (c := a/2) (r := ρ₂ φ) (θ := φ) (hρ₂pos φ)
    -- `P θ - O₂ = ρ₂ φ * exp (φ I)`
    have hz : polarPt (-(a/2)) (ρ₁ θ) θ - ((a/2 : ℝ) : ℂ)
        = (ρ₂ φ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
      rw [hφ, hsub]
    -- hence `(P θ - O₂) / |P θ - O₂| = exp (φ I)`, i.e. `eqU a (P θ) = -P θ + exp (φ I)`
    have hzdiv : (polarPt (-(a/2)) (ρ₁ θ) θ - ((a/2 : ℝ) : ℂ)) /
        ((‖polarPt (-(a/2)) (ρ₁ θ) θ - ((a/2 : ℝ) : ℂ)‖ : ℝ) : ℂ)
        = Complex.exp ((φ : ℂ) * Complex.I) := by
      have hne : ((ρ₂ φ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hρ₂pos φ))
      have hn : ‖polarPt (-(a/2)) (ρ₁ θ) θ - ((a/2 : ℝ) : ℂ)‖ = ρ₂ φ := by
        rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
          Complex.norm_of_nonneg (le_of_lt (hρ₂pos φ))]
      rw [hn, hz, div_eq_iff hne]
      ring
    have heqU : eqU a (polarPt (-(a/2)) (ρ₁ θ) θ) = polarPt (-(a/2)) (ρ₁ φ) φ := by
      have h1 : eqU a (polarPt (-(a/2)) (ρ₁ θ) θ)
          = -polarPt (-(a/2)) (ρ₁ θ) θ + Complex.exp ((φ : ℂ) * Complex.I) := by
        unfold eqU
        rw [hzdiv]
      rw [h1, hφ]
      -- `ρ₁ φ = 1 - ρ₂ φ`, so both sides are `-O₂ + (1 - ρ₂ φ) exp (φ I)`
      have hρ₂φ : ρ₁ φ = 1 - ρ₂ φ := by linarith [hρ₂_eq φ]
      rw [hρ₂φ]
      simp only [polarPt]
      push_cast
      ring_nf
    exact heqU
  refine ⟨?_, ?_, ?_⟩
  · -- invariance of the open upper arc under `eqU`
    intro θ hθ0 hθπ
    obtain ⟨φ, hφ0, hφπ, -, hU⟩ := key θ hθ0 hθπ
    exact ⟨φ, hφ0, hφπ, hU⟩
  · -- injectivity of `eqU` on the open upper arc
    intro θ θ' hθ0 hθπ hθ'0 hθ'π heq
    obtain ⟨φ, hφ0, hφπ, hPφ, hUφ⟩ := key θ hθ0 hθπ
    obtain ⟨φ', hφ'0, hφ'π, hPφ', hUφ'⟩ := key θ' hθ'0 hθ'π
    have h1 : polarPt (-(a/2)) (ρ₁ φ) φ = polarPt (-(a/2)) (ρ₁ φ') φ' := by
      rw [← hUφ, ← hUφ', heq]
    have hφeq : φ = φ' := (polarPt_inj (hρ₁pos φ) (hρ₁pos φ') hφ0 hφπ hφ'0 hφ'π h1).2
    have h2 : polarPt (-(a/2)) (ρ₁ θ) θ = polarPt (-(a/2)) (ρ₁ θ') θ' := by
      rw [hPφ, hφeq, ← hPφ']
    exact (polarPt_inj (hρ₁pos θ) (hρ₁pos θ') hθ0 hθπ hθ'0 hθ'π h2).2
  · -- invariance under the bisector reflection `z ↦ -conj z`
    intro θ hθ0 hθπ
    have hconj_exp : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
        = Complex.exp ((-(θ : ℂ)) * Complex.I) := by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hρ : ρ₂ (Real.pi - θ) = ρ₁ θ := by
      have h := hs₂ (Real.pi - θ)
      rwa [show Real.pi - (Real.pi - θ) = θ by ring] at h
    have hexpπ : Complex.exp (((Real.pi - θ : ℝ) : ℂ) * Complex.I)
        = -Complex.exp ((-(θ : ℂ)) * Complex.I) := by
      have h1 : (((Real.pi - θ : ℝ)) : ℂ) * Complex.I
          = (Real.pi : ℂ) * Complex.I + (-(θ : ℂ)) * Complex.I := by push_cast; ring
      rw [h1, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    -- `-conj (P θ) = O₂ + ρ₁ θ e^{i(π-θ)} = polarPt O₂ (ρ₂ (π-θ)) (π-θ)`
    have hW : -(starRingEnd ℂ) (polarPt (-(a/2)) (ρ₁ θ) θ)
        = polarPt (a/2) (ρ₂ (Real.pi - θ)) (Real.pi - θ) := by
      simp only [polarPt, map_add, map_mul, Complex.conj_ofReal]
      rw [hconj_exp, hexpπ, hρ]
      push_cast
      ring
    have hmem : -(starRingEnd ℂ) (polarPt (-(a/2)) (ρ₁ θ) θ)
        ∈ Set.range (fun φ => polarPt (-(a/2)) (ρ₁ φ) φ) := by
      rw [hrange]
      exact ⟨Real.pi - θ, hW.symm⟩
    have him : 0 < (-(starRingEnd ℂ) (polarPt (-(a/2)) (ρ₁ θ) θ)
        - (((-(a/2) : ℝ)) : ℂ)).im := by
      rw [hW]
      have h1 : (polarPt (a/2) (ρ₂ (Real.pi - θ)) (Real.pi - θ) - (((-(a/2) : ℝ)) : ℂ)).im
          = (polarPt (a/2) (ρ₂ (Real.pi - θ)) (Real.pi - θ)).im := by simp
      have h2 := (polarPt_basic (c := a/2) (r := ρ₂ (Real.pi - θ)) (θ := Real.pi - θ)
        (hρ₂pos _)).1
      rw [h1, h2]
      exact mul_pos (hρ₂pos _) (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    obtain ⟨φ, hφ0, hφπ, hφ⟩ := exists_angle_of_mem_range hper₁' hρ₁pos hmem him
    exact ⟨φ, hφ0, hφπ, hφ⟩

end Work.EQ
