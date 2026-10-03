import Mathlib
import Submission.Work.KMTAreas.A7.SmallModApprox

namespace Work.KMTAreas.A7

open MeasureTheory

/-- **The composed kernel as an iterated sum in "translated" form.**  Reindexing the defining
iterated sum `∑' a', ∑' b', K (a - a') (b - b') * κ a' * κ' b'` of `kernComp` by the bijections
`j₁ ↦ a - j₁`, `j₂ ↦ b - j₂` of `ℤ` gives

`kernComp K κ κ' a b = ∑' j₁, ∑' j₂, K j₁ j₂ * κ (a - j₁) * κ' (b - j₂)`.

(The reindexing is *unconditional*: `Equiv.tsum_eq` requires no summability hypothesis.) -/
theorem kernComp_eq_iter (K : ℤ → ℤ → ℂ) (κ κ' : ℤ → ℂ) (a b : ℤ) :
    kernComp K κ κ' a b = ∑' j₁ : ℤ, ∑' j₂ : ℤ, K j₁ j₂ * κ (a - j₁) * κ' (b - j₂) := by
  rw [kernComp]
  rw [← Equiv.tsum_eq (Equiv.subLeft a)
    (fun a' => ∑' b' : ℤ, K (a - a') (b - b') * κ a' * κ' b')]
  refine tsum_congr (fun j₁ => ?_)
  simp only [Equiv.subLeft_apply, sub_sub_self]
  rw [← Equiv.tsum_eq (Equiv.subLeft b)
    (fun b' => K j₁ (b - b') * κ (a - j₁) * κ' b')]
  refine tsum_congr (fun j₂ => ?_)
  simp only [Equiv.subLeft_apply, sub_sub_self]

/-- The arithmetic-character identity `Work.KMTPlan.A6.IwKernelArithChar` in the form of the
exact-height Ionescu--Wainger kernel `tmKernel` used in §6: for an integrable symbol `φ`,

`tmKernel ρ l φ j = (∑_{α ∈ (ℚ/ℤ)_l} e(-jα)) · cw φ j`. -/
theorem tmKernel_eq (ρ : ℝ) (l : ℕ) {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) :
    tmKernel ρ l φ j = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α) * cw φ j :=
  Work.KMTPlan.A6.IwKernelArithChar (diffFreqs ρ l) hφ j

/-- The instance of `tmKernel_eq` for the modulated bump `φ_{N,t}`. -/
theorem tmKernel_varphiNt (ρ : ℝ) (l N k : ℕ) (t : ℝ) (j : ℤ) :
    tmKernel ρ l (varphiNt N k t) j
      = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α) * cw (varphiNt N k t) j :=
  tmKernel_eq ρ l (integrable_varphiNt N k t) j

/-- The instance of `tmKernel_eq` for the modulated bump `φ̃_{N,t}`. -/
theorem tmKernel_varphitildeNt (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ) (t : ℝ) (j : ℤ) :
    tmKernel ρ l (varphitildeNt P P.natDegree N k t) j
      = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α)
          * cw (varphitildeNt P P.natDegree N k t) j :=
  tmKernel_eq ρ l (integrable_varphitildeNt_aux P P.natDegree N k t) j

theorem smallKmod_coeff (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) (a b : ℤ) :
    Work.KMTAreas.A7.smallKmod ρ P l₁ l₂ k₁ k₂ N a b
      = ∫ t in (1 / 2 : ℝ)..1, ∑' j₁ : ℤ, ∑' j₂ : ℤ,
          (Work.KMTAreas.A7.smallArithKernel ρ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂
            * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂))) j₁
            * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂))) j₂)
          * ((∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, fourier (T := 1) (-(a - j₁)) α)
              * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) (a - j₁))
          * ((∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₂, fourier (T := 1) (-(b - j₂)) α)
              * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) (b - j₂)) := by
  rw [smallKmod]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [kernComp_eq_iter]
  refine tsum_congr (fun j₁ => ?_)
  refine tsum_congr (fun j₂ => ?_)
  rw [tmKernel_varphiNt ρ l₁ N k₁ t (a - j₁),
      tmKernel_varphitildeNt ρ P l₂ N k₂ t (b - j₂)]

end Work.KMTAreas.A7
