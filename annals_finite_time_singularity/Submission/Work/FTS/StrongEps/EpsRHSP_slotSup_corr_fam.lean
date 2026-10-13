/-
# `Submission/Work/FTS/StrongEps/EpsRHSP_slotSup_corr_fam.lean`

The family version of `EpsRHSP_slotSup_corr`: uniform-in-`n` sup-bounds for the slots
`D_z^j D_θ^i (epsRHSP (ε n) (G n) s)` on a compact `K ⊆ Q0`, where the only hypothesis about the
`L₁₂`-zero-mode is the direct uniform bound `hcorr`.

The proof is the literal combination of the two siblings:

* `EpsRHSP_slotSup_fam` — threads the `n`-quantifiers through the proof of `EpsRHSP_slotSup`,
  producing a constant depending only on `ρ`, `K` and the *uniform* bounds;
* `EpsRHSP_slotSup_corr` — replaces the `ℋ⁴`-norm route to the correction scalar by the hypothesis
  `hcorr`.

So: same constant `C₀ + (Cc / pzNorm) * Cb`, same split
`epsRHSP = Pz (J_ε Ψ) - (L₁₂ (J_ε Ψ)(0) / pzNorm) • bump`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_corr
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_fam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

theorem EpsRHSP_slotSup_corr_fam {α T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    (hreg : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hsup : ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
      (∀ n : ℕ, ∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ ε n → |q.2| ≤ ε n →
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2) ∈ K') ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc (0 : ℝ) T,
        ∀ p ∈ K', |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)
          p.1 p.2| ≤ C)
    (hcorr : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (ε n)
        (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) 0| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∀ p ∈ K, |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s)
        p.1 p.2| ≤ C := by
  obtain ⟨K', hK'c, hK'Q, hKK', hshift, C₀, hC₀, hbdd⟩ := hsup
  obtain ⟨Cc, hCc0, hcorrb⟩ := hcorr
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump K hK
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  refine ⟨C₀ + (Cc / Work.FTS.StrongEps.pzNorm) * Cb, ?_, ?_⟩
  · exact add_nonneg hC₀ (mul_nonneg (div_nonneg hCc0 hpzpos.le) hCb0)
  · intro n j i hji s hs p hp
    have hpQ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
    have hz : 0 < p.1 := hpQ.1
    have hθ : p.2 ∈ Set.Ioo 0 (π / 2) := ⟨hpQ.2.1, hpQ.2.2⟩
    have hsm : ∀ m : ℕ, ContDiffOn ℝ m
        (Function.uncurry (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s))
        Work.FTS.StrongEps.Quad := (hreg n s hs).forall
    have hmain : |Work.Spaces.mixed j i
        (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s))
        p.1 p.2| ≤ C₀ := by
      rw [Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll (hε n).1 hsm hz hθ j i]
      refine Work.FTS.StrongEps.abs_Jeps_le_sup ρ hρ.moll (hε n).1 hz hθ ?_ hC₀
      intro q hq1 hq2
      exact hbdd n j i hji s hs (Work.FTS.StrongEps.zShift p.1 q.1,
        Work.FTS.StrongEps.thShift p.2 q.2) (hshift n p hp q hq1 hq2)
    have hcorrterm : |(Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ (ε n)
            (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) 0
            / Work.FTS.StrongEps.pzNorm) * Work.Spaces.mixed j i Work.FTS.StrongEps.bump
              p.1 p.2|
        ≤ (Cc / Work.FTS.StrongEps.pzNorm) * Cb := by
      rw [abs_mul]
      have hL : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ (ε n)
            (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) 0|
          ≤ Cc := hcorrb n s hs
      have hal : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ (ε n)
            (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) 0
            / Work.FTS.StrongEps.pzNorm| ≤ Cc / Work.FTS.StrongEps.pzNorm := by
        rw [abs_div, abs_of_pos hpzpos]
        exact div_le_div_of_nonneg_right hL hpzpos.le
      have hb : |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| ≤ Cb :=
        hbump j i hji p hp
      exact mul_le_mul hal hb (abs_nonneg _) (div_nonneg hCc0 hpzpos.le)
    have hsplit : Work.Spaces.mixed j i
          (Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s) p.1 p.2
        = Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ (ε n)
              (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) p.1 p.2
          - (Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ (ε n)
                (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2 := by
      rw [Work.FTS.StrongEps.epsRHSP_eq_Pz_Jeps_epsWP,
        Work.FTS.StrongEps.PZeroAux.mixed_Pz
          (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ (hε n).1 hsm) hz hθ j i]
    rw [hsplit]
    calc |Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ (ε n)
              (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) p.1 p.2
          - (Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ (ε n)
                (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
        ≤ |Work.Spaces.mixed j i
              (Work.FTS.StrongEps.Jeps ρ (ε n)
                (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) p.1 p.2|
          + |(Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ (ε n)
                (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| := by
          have h := abs_add_le (Work.Spaces.mixed j i
              (Work.FTS.StrongEps.Jeps ρ (ε n)
                (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) p.1 p.2)
            (-((Work.Construction.L12
                (Work.FTS.StrongEps.Jeps ρ (ε n)
                  (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) 0
                  / Work.FTS.StrongEps.pzNorm)
                * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2))
          simpa only [sub_eq_add_neg, abs_neg] using h
      _ ≤ C₀ + (Cc / Work.FTS.StrongEps.pzNorm) * Cb := add_le_add hmain hcorrterm

end Work.FTS.StrongEps
