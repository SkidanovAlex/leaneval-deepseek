/-
# `Submission/Work/FTS/StrongEps/EpsRHSP_slotSup_corr.lean` — sup-bounds for `epsRHSP`,
with the correction scalar taken as a hypothesis

This is the sibling of `Work.FTS.StrongEps.EpsRHSP_slotSup` in which the *only* hypothesis about
the `L₁₂`-zero-mode of the mollified right-hand side is the direct uniform bound

  `hcorr : ∃ C, 0 ≤ C ∧ ∀ s ∈ Icc 0 T, |L₁₂ (J_ε (epsWP s)) 0| ≤ C`

(in place of the `ℋ⁴`-norm hypothesis `hnorm` from which `EpsRHSP_slotSup` *derives* such a
bound).  The conclusion is the same: the projected right-hand side
`epsRHSP s = Pz (J_ε (epsWP s))` has uniformly bounded mixed derivatives `D_z^j D_θ^i`,
`j + i ≤ 4`, on a compact `K ⊆ Q0`.

The proof is the proof of `EpsRHSP_slotSup` with the chain
`|L₁₂ (J_ε Ψ) 0| ≤ CL · |Ψ|_{ℋ⁴} ≤ CL · KW` replaced by the hypothesis `hcorr`:

* **main term.**  `D_z^jD_θ^i (J_ε Ψ) = J_ε (D_z^jD_θ^i Ψ)` on the open quadrant (`mixed_Jeps`),
  and `J_ε` is the nonnegative-kernel average of the shifted values (`abs_Jeps_le_sup`); by
  `hsup` the shifted points lie in `K'`, where every slot is `≤ C₀`;
* **correction term.**  The fixed profile `bump` has uniformly bounded mixed derivatives on the
  compact `K` (`exists_bound_mixed_bump`), and the scalar is controlled by `hcorr`.

The resulting constant is `C₀ + (Cc / pzNorm) * Cb`, where `Cc` is the constant of `hcorr`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

theorem EpsRHSP_slotSup_corr {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : ε ∈ Set.Ioc 0 1)
    (hreg : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hsup : ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
      (∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ ε → |q.2| ≤ ε →
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2) ∈ K') ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K',
        |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) p.1 p.2| ≤ C)
    (hcorr : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε
        (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C := by
  obtain ⟨K', hK'c, hK'Q, hKK', hshift, C₀, hC₀, hbdd⟩ := hsup
  obtain ⟨Cc, hCc0, hcorrb⟩ := hcorr
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump K hK
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  refine ⟨C₀ + (Cc / Work.FTS.StrongEps.pzNorm) * Cb, ?_, ?_⟩
  · exact add_nonneg hC₀ (mul_nonneg (div_nonneg hCc0 hpzpos.le) hCb0)
  · intro j i hji s hs p hp
    have hpQ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
    have hz : 0 < p.1 := hpQ.1
    have hθ : p.2 ∈ Set.Ioo 0 (π / 2) := ⟨hpQ.2.1, hpQ.2.2⟩
    have hsm : ∀ n : ℕ, ContDiffOn ℝ n
        (Function.uncurry (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))
        Work.FTS.StrongEps.Quad := (hreg s hs).forall
    have hmain : |Work.Spaces.mixed j i
        (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2|
        ≤ C₀ := by
      rw [Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε.1 hsm hz hθ j i]
      refine Work.FTS.StrongEps.abs_Jeps_le_sup ρ hρ.moll hε.1 hz hθ ?_ hC₀
      intro q hq1 hq2
      exact hbdd j i hji s hs (Work.FTS.StrongEps.zShift p.1 q.1,
        Work.FTS.StrongEps.thShift p.2 q.2) (hshift p hp q hq1 hq2)
    have hcorrterm : |(Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
            / Work.FTS.StrongEps.pzNorm) * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
        ≤ (Cc / Work.FTS.StrongEps.pzNorm) * Cb := by
      rw [abs_mul]
      have hL : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0|
          ≤ Cc := hcorrb s hs
      have hal : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
            / Work.FTS.StrongEps.pzNorm| ≤ Cc / Work.FTS.StrongEps.pzNorm := by
        rw [abs_div, abs_of_pos hpzpos]
        exact div_le_div_of_nonneg_right hL hpzpos.le
      have hb : |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| ≤ Cb :=
        hbump j i hji p hp
      exact mul_le_mul hal hb (abs_nonneg _) (div_nonneg hCc0 hpzpos.le)
    have hsplit : Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2
        = Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2 := by
      rw [Work.FTS.StrongEps.epsRHSP_eq_Pz_Jeps_epsWP,
        Work.FTS.StrongEps.PZeroAux.mixed_Pz
          (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε.1 hsm) hz hθ j i]
    rw [hsplit]
    calc |Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
        ≤ |Work.Spaces.mixed j i
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2|
          + |(Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| := by
          have h := abs_add_le (Work.Spaces.mixed j i
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2)
            (-((Work.Construction.L12
                (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                  / Work.FTS.StrongEps.pzNorm)
                * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2))
          simpa only [sub_eq_add_neg, abs_neg] using h
      _ ≤ C₀ + (Cc / Work.FTS.StrongEps.pzNorm) * Cb := add_le_add hmain hcorrterm

end Work.FTS.StrongEps
