import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_fam
import Submission.Work.FTS.StrongEps.EpsProfileLip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-- **Slices are Lipschitz in the fake time as soon as the right-hand side is uniformly bounded.**
This is the body of `EpsProfileLip` with the `∀ K`-shaped bound `hbdd` replaced by a single bound
on the compact `K` at hand — which is exactly the shape produced by `EpsRHSP_slotSup_fam`.

The proof is the fundamental theorem of calculus: the integral form of the `P₀`-scheme
(`epsSol_eq_integralP`) writes the difference of two slices as the integral of `epsRHSP` between
the two times, and the mean-value estimate `‖∫‖ ≤ C · |σ - σ'|` closes the argument. -/
theorem slice_lip_of_rhsSup {α T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam}
    (hsol : ∀ n : ℕ, Work.FTS.StrongEps.IsEpsSolP α ρ (ε n) T Φs E g₀ (G n))
    (hcont : ∀ n : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
        (Set.Icc 0 T))
    {K : Set (ℝ × ℝ)} (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K,
      |Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ∀ τ' ∈ Set.Icc (0 : ℝ) T,
        |Work.FTS.Galerkin.slice (G n) τ p.1 p.2 - Work.FTS.Galerkin.slice (G n) τ' p.1 p.2|
          ≤ C * |τ - τ'| := by
  obtain ⟨C₀, hC₀nn, hC₀⟩ := hbdd
  refine ⟨C₀, hC₀nn, ?_⟩
  intro n p hp τ hτ τ' hτ'
  have hQ : (p.1, p.2) ∈ Work.FTS.EllipticEst.Q0 := hKQ hp
  have hFcont : ContinuousOn
      (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
      (Set.Icc (0 : ℝ) T) := hcont n p hQ
  have hFbd : ∀ s ∈ Set.Icc (0 : ℝ) T,
      |Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C₀ :=
    fun s hs => hC₀ n s hs p hp
  -- the integral form of the two slices and the resulting difference identity
  have key : ∀ σ σ' : ℝ, σ ∈ Set.Icc (0 : ℝ) T → σ' ∈ Set.Icc (0 : ℝ) T → σ' ≤ σ →
      |Work.FTS.Galerkin.slice (G n) σ p.1 p.2 - Work.FTS.Galerkin.slice (G n) σ' p.1 p.2|
        ≤ C₀ * |σ - σ'| := by
    intro σ σ' hσ hσ' hle
    have h1 := Work.FTS.StrongEps.epsSol_eq_integralP (hsol n)
      (fun z θ hzθ => hcont n (z, θ) hzθ) p.1 p.2 σ hQ hσ
    have h2 := Work.FTS.StrongEps.epsSol_eq_integralP (hsol n)
      (fun z θ hzθ => hcont n (z, θ) hzθ) p.1 p.2 σ' hQ hσ'
    have hi1 : IntervalIntegrable
        (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
        MeasureTheory.volume (0 : ℝ) σ' :=
      ContinuousOn.intervalIntegrable_of_Icc hσ'.1
        (hFcont.mono (Set.Icc_subset_Icc le_rfl hσ'.2))
    have hi2 : IntervalIntegrable
        (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
        MeasureTheory.volume σ' σ :=
      ContinuousOn.intervalIntegrable_of_Icc hle (hFcont.mono (Set.Icc_subset_Icc hσ'.1 hσ.2))
    have hadj := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hdiff : Work.FTS.Galerkin.slice (G n) σ p.1 p.2
          - Work.FTS.Galerkin.slice (G n) σ' p.1 p.2
        = ∫ s in σ'..σ, Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2 := by
      show (G n) p.1 p.2 σ - (G n) p.1 p.2 σ' = _
      rw [h1, h2]
      linarith
    rw [hdiff]
    have hnorm : ‖∫ s in σ'..σ,
          Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2‖
        ≤ C₀ * |σ - σ'| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      rw [Set.uIoc_of_le hle] at hx
      rw [Real.norm_eq_abs]
      exact hFbd x ⟨le_trans hσ'.1 hx.1.le, le_trans hx.2 hσ.2⟩
    simpa only [Real.norm_eq_abs] using hnorm
  rcases le_total τ' τ with hle | hle
  · exact key τ τ' hτ hτ' hle
  · have h := key τ' τ hτ' hτ hle
    rw [abs_sub_comm (Work.FTS.Galerkin.slice (G n) τ p.1 p.2)
          (Work.FTS.Galerkin.slice (G n) τ' p.1 p.2), abs_sub_comm τ τ']
    exact h

theorem EpsProfileLip_of_epsWP {α T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    (hsol : ∀ n : ℕ, Work.FTS.StrongEps.IsEpsSolP α ρ (ε n) T Φs E g₀ (G n))
    (hcont : ∀ n : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
        (Set.Icc 0 T))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hwin : ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
      (∀ n : ℕ, ∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ ε n → |q.2| ≤ ε n →
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2) ∈ K') ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc 0 T,
        ∀ p ∈ K', |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)
          p.1 p.2| ≤ C)
    (hnorm : ∃ KW : ℝ, 0 ≤ KW ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ≤ KW)
    (hreg : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ∀ τ' ∈ Set.Icc (0 : ℝ) T,
        |Work.FTS.Galerkin.slice (G n) τ p.1 p.2 - Work.FTS.Galerkin.slice (G n) τ' p.1 p.2|
          ≤ C * |τ - τ'| := by
  -- the projected right-hand side `P₀ J_ε (epsWP)` is uniformly bounded on `K` (in every
  -- mixed slot of order `≤ 4`), with a constant independent of the family index `n`
  obtain ⟨C, hC, hbound⟩ :=
    Work.FTS.StrongEps.EpsRHSP_slotSup_fam hα hρ hε hreg hK hKQ hwin hnorm
  -- the `(j, i) = (0, 0)` slot is the right-hand side itself
  refine slice_lip_of_rhsSup hsol hcont hKQ ⟨C, hC, ?_⟩
  intro n s hs p hp
  simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
    using hbound n 0 0 (by omega) s hs p hp

end Work.FTS.StrongEps
