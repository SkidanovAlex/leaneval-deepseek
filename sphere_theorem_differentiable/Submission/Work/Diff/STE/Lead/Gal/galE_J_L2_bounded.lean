import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.STruncR_CSq_le
import Submission.Work.Diff.STE.B3.bump_expansion_fixed
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.BNorm_J_sub_le
import Submission.Work.Diff.STE.B3.BNorm_J_le_uniform_nodim
import Submission.Work.Diff.STE.Lead.Gal.galE_J_bounded
import Submission.Work.Diff.STE.CSq_le_ENormSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.Gal

/-- **Level-`0` (`L²`) boundedness of the Friedrichs mollifier.**  `D.ENormB 0 h` is the `L²`
energy of a section (`B3/BNorm_ENormB_equiv.lean`), `D.J ρ ε` the chartwise mollifier
(`B3/Comp.lean`).  Claim: there is `C`, depending only on `D` (the Layer B3 atlas) and the
`ε`-free bound `‖ρ‖ ≤ 1`, such that for every `ε ∈ (0,1]` and every section `h` with `C^∞`
localised components,

  `D.ENormB 0 (D.J ρ ε h) ≤ C * D.ENormB 0 h`.

Unlike the `Hᵏ` version (`galE_J_bounded`) no loss of derivatives occurs, so no `finrank < 2k`
hypothesis is needed.

PROOF ROUTE (all ingredients proved, except one new small change-of-variables lemma):
* `D.ENormB 0 h = Σ_{i,a,b} ∫_{unitCube} ‖D.Rper i h a b‖²` and the localised components are
  supported in the open centred cube (`B3Data.psi_supp`), so this is an ordinary `L²` quantity.
* `D.J ρ ε h = Σ_i D.Rstar i (D.B3Data.STruncR ρ ε (D.R i h))`, hence
  `D.R i (D.J ρ ε h) a b = Σ_j (D.R i ∘ D.Rstar j) (D.B3Data.STruncR ρ ε (D.R j h a b))`.
* `S_ε = D.B3Data.STruncR ρ ε` is an `L²`-contraction on smooth functions supported in the open
  centred cube: `Work.Diff.STE.B3.STruncR_CSq_le` with `s = 0` (it multiplies the Fourier
  coefficients by `|ρ (ε·)| ≤ 1`), with smoothness/periodicity from
  `Rper_contDiff_periodic_of_R_contDiff`.
* Each transfer `L_{ij} = D.R i ∘ D.Rstar j` is `G · (· ∘ T)` with `G` a fixed bounded function and
  `T` a chart transition diffeomorphism (`B3/bump_expansion_fixed.lean`), so
  `‖L_{ij} g‖_{L²} ≤ C_{ij} ‖g‖_{L²}`: a *new* change-of-variables estimate on the torus
  (`∫ ‖u ∘ T‖² ≤ C ∫ ‖u‖²` for `1`-periodic `u`), independent of `ε` and of `h`.
* Sum over `(i,a,b)` and Cauchy–Schwarz over the finite sum in `j` (or use
  `Finset.sum_mul_sq_le_sq_mul_sq`).

Consumer: `galE_apriori` bounds the level-`0` part of the energy derivative by Cauchy–Schwarz and
needs `E_0 (D.J ρ ε f) ≤ C · E_0 f` for `f` the DeTurck tensor of the foreground. -/
theorem galE_J_L2_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
          (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
            ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b)) →
          D.ENormB 0 (D.J ρ ε h) ≤ C * D.ENormB 0 h := by
  classical
  -- `L²`-equivalence constants: physical energy vs. weighted Fourier mass of the components.
  obtain ⟨C₁, hC₁nn, hC₁⟩ :=
    Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic (ι := Fin (Module.finrank ℝ E)) 0
  obtain ⟨C₂, hC₂nn, hC₂⟩ := Work.Diff.STE.B3.BNorm_J_le_uniform_nodim D ρ hρ 0
  obtain ⟨C₃, hC₃nn, hC₃⟩ := Work.Diff.STE.CSq_le_ENormSq (ι := Fin (Module.finrank ℝ E)) 0
  refine ⟨C₁ * (C₂ * (2 * C₃)), by positivity, ?_⟩
  intro ε hε hε1 h hsm
  -- (A) the physical energy of `J ρ ε h` is controlled by its Fourier-side norm, via the
  -- smoothness of the chart components of `J ρ ε h` (`R_J_contDiff_noInst`) and the general
  -- physical/Fourier comparison at level `0`.
  have hA : D.ENormB 0 (D.J ρ ε h) ≤ C₁ * D.BNorm 0 (D.J ρ ε h) := by
    rw [Work.Diff.STE.B3Data.ENormB, Work.Diff.STE.B3Data.BNorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have hcomp : ContDiff ℝ (⊤ : ℕ∞) (D.R i (D.J ρ ε h) a b) :=
      R_J_contDiff_noInst D ρ h hsm hρ i a b ε
    obtain ⟨hcd, hper⟩ :=
      Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i (D.J ρ ε h) a b hcomp
    exact hC₁ (D.Rper i (D.J ρ ε h) a b) hcd hper
  -- (B) the Fourier-side norm of the mollified section, uniformly in `ε ∈ (0,1]` and in `h`.
  have hB : D.BNorm 0 (D.J ρ ε h) ≤ C₂ * D.BNorm 0 h := hC₂ ε hε hε1 h hsm
  -- (C) the Fourier-side norm of the section is controlled by its physical energy.
  have hC : D.BNorm 0 h ≤ (2 * C₃) * D.ENormB 0 h := by
    have hterm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
          ≤ (2 * C₃) * Work.Diff.STE.ENormSq 0 (D.Rper i h a b) := by
      intro i a b
      obtain ⟨hcd, hper⟩ :=
        Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i h a b (hsm i a b)
      have hcd0 : ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞) (D.Rper i h a b) :=
        hcd.of_le (by
          show (((0 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
          exact WithTop.coe_le_coe.mpr le_top)
      have hbound := hC₃ (D.Rper i h a b) hcd0 hper
      calc Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
          ≤ C₃ * (Work.Diff.STE.ENormSq 0 (D.Rper i h a b)
              + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) := hbound
        _ = (2 * C₃) * Work.Diff.STE.ENormSq 0 (D.Rper i h a b) := by ring
    have hsum : D.BNorm 0 h ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          (2 * C₃) * Work.Diff.STE.ENormSq 0 (D.Rper i h a b) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
        Finset.sum_le_sum fun b _ => hterm i a b
    have hsplit : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          (2 * C₃) * Work.Diff.STE.ENormSq 0 (D.Rper i h a b))
        = (2 * C₃) * D.ENormB 0 h := by
      simp only [Work.Diff.STE.B3Data.ENormB, ← Finset.mul_sum]
    rwa [hsplit] at hsum
  calc D.ENormB 0 (D.J ρ ε h) ≤ C₁ * D.BNorm 0 (D.J ρ ε h) := hA
    _ ≤ C₁ * (C₂ * D.BNorm 0 h) := mul_le_mul_of_nonneg_left hB hC₁nn
    _ ≤ C₁ * (C₂ * ((2 * C₃) * D.ENormB 0 h)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC hC₂nn) hC₁nn
    _ = (C₁ * (C₂ * (2 * C₃))) * D.ENormB 0 h := by ring

end Work.Diff.STE.Lead.Gal
