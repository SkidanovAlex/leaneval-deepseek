import Mathlib
import Submission.GM.Interfaces

/-!
# GM §9, affine sums: setup and basic facts about the test function `f`

This file sets up the *hypotheses* of GM §9 (Proposition 9.1) as predicates and records the
elementary consequences about the test function `f : ℝ → ℝ`.

All statements are in the namespace `Work.GM.Affine`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The complex-valued Fourier transform of `f : ℝ → ℝ`, as used throughout GM §9. -/
noncomputable def Fhat (f : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) ξ

/-- The exponential `e(t) = exp (2 π i t)` used for the Fourier transform. -/
noncomputable def efun (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

lemma norm_efun (t : ℝ) : ‖efun t‖ = 1 := by
  simp [efun, Complex.norm_exp]

lemma efun_add (s t : ℝ) : efun (s + t) = efun s * efun t := by
  have h : (2 * (Real.pi : ℂ) * Complex.I) * ((s : ℂ) + (t : ℂ))
      = (2 * (Real.pi : ℂ) * Complex.I) * (s : ℂ) + (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ) := by
    ring
  simp only [efun, Complex.ofReal_add, h]
  exact Complex.exp_add _ _

lemma efun_neg (t : ℝ) : efun (-t) = (efun t)⁻¹ := by
  have h : (2 * (Real.pi : ℂ) * Complex.I) * ((-t : ℝ) : ℂ)
      = -((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
    push_cast; ring
  simp only [efun, h]
  exact Complex.exp_neg _

/-- `supf f` is the supremum of `f`. -/
noncomputable def supf (f : ℝ → ℝ) : ℝ := sSup (Set.range f)

/-- The smoothed version `f̃(u) = T ∫ ψ(T(u-u')) f(u') du'` of GM's Lemma 9.2. -/
noncomputable def smoothed (ψ : ℝ → ℝ) (T : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  T * ∫ u', ψ (T * (u - u')) * f u'

/-- The "aliasing mass" of `Fhat f` at scale `m`: `Σ_{k ∈ ℤ} ‖Fhat f (k*m)‖`. It controls the
error in the Poisson-summation formula for the lattice sums `Σ_{m₃} f ((x+m₃)/m)`. -/
noncomputable def aliasing (f : ℝ → ℝ) (m : ℝ) : ℝ := ∑' k : ℤ, ‖Fhat f ((k : ℝ) * m)‖

/-- The Fourier decay hypothesis of GM §9. -/
def DecayHyp (c : ℕ → ℝ → ℝ) (T : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
    ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * supf f

/-- The support hypothesis of GM §9: `f` is supported in `[1/C₀, C₀]`. -/
def SuppHyp (C₀ : ℝ) (f : ℝ → ℝ) : Prop := ∀ u, f u ≠ 0 → u ∈ Set.Icc (1 / C₀) C₀

section Basic

variable {f : ℝ → ℝ}

lemma bddAbove_range_of_compact (hf : Continuous f) (hcs : HasCompactSupport f) :
    BddAbove (Set.range f) :=
  (hcs.isCompact_range hf).bddAbove

lemma le_supf (hf : Continuous f) (hcs : HasCompactSupport f) (x : ℝ) : f x ≤ supf f :=
  le_csSup (bddAbove_range_of_compact hf hcs) (Set.mem_range_self x)

lemma supf_le_of_le {B : ℝ} (hf : ∀ u, f u ≤ B) : supf f ≤ B :=
  csSup_le (Set.range_nonempty f) (by rintro z ⟨u, rfl⟩; exact hf u)

lemma supf_nonneg (hf : Continuous f) (hcs : HasCompactSupport f)
    (hnn : ∀ u, 0 ≤ f u) : 0 ≤ supf f :=
  le_trans (hnn 0) (le_supf hf hcs 0)

lemma exists_eq_supf (hf : Continuous f) (hcs : HasCompactSupport f) :
    ∃ x : ℝ, f x = supf f := by
  have hK : IsCompact (Set.range f) := hcs.isCompact_range hf
  have hne : (Set.range f).Nonempty := Set.range_nonempty f
  have hmem : supf f ∈ Set.range f := hK.sSup_mem hne
  exact hmem

lemma supf_pos (hf : Continuous f) (hcs : HasCompactSupport f) (h : ∃ u, 0 < f u) :
    0 < supf f := by
  obtain ⟨u, hu⟩ := h
  exact lt_of_lt_of_le hu (le_supf hf hcs u)

end Basic

end

end Work.GM.Affine
