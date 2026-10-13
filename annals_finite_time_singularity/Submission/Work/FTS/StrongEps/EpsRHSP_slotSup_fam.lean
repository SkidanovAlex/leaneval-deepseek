/-
# `Submission/Work/FTS/StrongEps/EpsRHSP_slotSup_fam.lean` — the family version

`EpsRHSP_slotSup` bounds the slots of the projected right-hand side `epsRHSP` for a *single*
parameter `ε` and a *single* Galerkin family `g`.  The statement proved here is the version
needed downstream: the same bound **uniformly over a sequence** `ε n`, `G n`, with a constant
that does not depend on `n`.

The proof is the proof of `EpsRHSP_slotSup` with the `n`-quantifiers threaded through.  The point
is that the constant produced there,

  `C := C₀ + (CL * KW / pzNorm) * Cb`

depends only on the kernel `ρ`, the compact set `K` and the *uniform* bounds `C₀` (`hsup`) and
`KW` (`hnorm`) — none of which depend on `n`, `ε n`, `G n` or `s`.  So the very same `C` works for
every `n`.

The two ingredients are

* `exists_bound_mixed_bump K hK` (`Cb`, kernel-free) for the correction profile `bump`;
* `abs_L12_Jeps_le ρ hρ` (`CL`, kernel-only) for the scalar `L₁₂ (J_ε Ψ)(0)`,
  which controls the correction term by `CL * KW / pzNorm`;

and the main term is bounded by `C₀` directly through
`mixed_Jeps` (the mollifier commutes with `D_z^j D_θ^i`) and `abs_Jeps_le_sup` (the mollifier
averages the values on the shifted compact `K'`).
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

theorem EpsRHSP_slotSup_fam {α T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
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
    (hnorm : ∃ KW : ℝ, 0 ≤ KW ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ≤ KW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∀ p ∈ K, |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s)
        p.1 p.2| ≤ C := by
  obtain ⟨K', hK'c, hK'Q, hKK', hshift, C₀, hC₀, hbdd⟩ := hsup
  obtain ⟨KW, hKW, hnorm'⟩ := hnorm
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump K hK
  obtain ⟨CL, hCL0, hCL⟩ := abs_L12_Jeps_le (ρ := ρ) hρ
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  refine ⟨C₀ + (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb, ?_, ?_⟩
  · exact add_nonneg hC₀ (mul_nonneg (div_nonneg (mul_nonneg hCL0 hKW) hpzpos.le) hCb0)
  · intro n j i hji s hs p hp
    obtain ⟨hmems, hnormbs⟩ := hnorm' n s hs
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
    have hcorr : |(Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ (ε n)
            (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) 0
            / Work.FTS.StrongEps.pzNorm) * Work.Spaces.mixed j i Work.FTS.StrongEps.bump
              p.1 p.2|
        ≤ (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb := by
      rw [abs_mul]
      have hL : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ (ε n)
            (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) 0|
          ≤ CL * KW := hCL hα (hε n).1 (hε n).2 hKW hsm hmems hnormbs
      have hal : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ (ε n)
            (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) 0
            / Work.FTS.StrongEps.pzNorm| ≤ CL * KW / Work.FTS.StrongEps.pzNorm := by
        rw [abs_div, abs_of_pos hpzpos]
        exact div_le_div_of_nonneg_right hL hpzpos.le
      have hb : |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| ≤ Cb :=
        hbump j i hji p hp
      exact mul_le_mul hal hb (abs_nonneg _)
        (div_nonneg (mul_nonneg hCL0 hKW) hpzpos.le)
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
      _ ≤ C₀ + (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb := add_le_add hmain hcorr

end Work.FTS.StrongEps
