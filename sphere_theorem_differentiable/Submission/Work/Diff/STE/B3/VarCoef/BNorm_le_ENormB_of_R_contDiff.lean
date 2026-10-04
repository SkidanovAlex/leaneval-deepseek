import Mathlib
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.CSq_le_ENormSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `BNorm ≤ C · (ENormB s + ENormB 0)` from smoothness of the local components `D.R i h a b`

The Fourier-side norm `D.BNorm s` and the physical energy `D.ENormB s` are both sums of the
per-component quantities `CSq s (fourierCoeff (D.Rper i h a b))` and
`ENormSq s (D.Rper i h a b)`; the termwise Sobolev comparison on the torus
`Work.Diff.STE.CSq_le_ENormSq` gives, *with a constant independent of the component function*,

  `CSq s (fourierCoeff g) ≤ C · (ENormSq s g + ENormSq 0 g)`,

for every `C^s`, `1`-periodic `g`.  Since the periodised component `D.Rper i h a b` is smooth and
`1`-periodic as soon as the local component `D.R i h a b` is smooth
(`Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff`, whose proof only uses that the latter is
supported in the open centred unit cube), summing the termwise bound over the finitely many indices
`(i, a, b)` produces the claim with a single constant `C` depending only on `s` and the dimension.

This is the same estimate as `Work.Diff.STE.B3Data.BNorm_le_ENormB`, with the *hypothesis on the
periodised* components (`ContDiff ℝ s (D.Rper i h a b)` together with `Periodic1`) replaced by the
hypothesis on the *local* components (`ContDiff ℝ ⊤ (D.R i h a b)`), and, importantly, with the
constant extracted *before* the section `h` is quantified, so that it is uniform in `h`.
-/

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

theorem BNorm_le_ENormB_of_R_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
        (∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a b)) →
        D.BNorm s h ≤ C * (D.ENormB s h + D.ENormB 0 h) := by
  obtain ⟨C, hC, hCb⟩ := Work.Diff.STE.CSq_le_ENormSq (ι := Fin (Module.finrank ℝ E)) s
  refine ⟨C, hC, fun h hsm => ?_⟩
  have hterm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
        ≤ C * (Work.Diff.STE.ENormSq s (D.Rper i h a b)
            + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) := by
    intro i a b
    obtain ⟨hcd, hper⟩ :=
      Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i h a b (hsm i a b)
    exact hCb (D.Rper i h a b) (hcd.of_le (by exact_mod_cast le_top)) hper
  have hsum : D.BNorm s h ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        C * (Work.Diff.STE.ENormSq s (D.Rper i h a b)
          + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
      Finset.sum_le_sum fun b _ => hterm i a b
  have hsplit : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        C * (Work.Diff.STE.ENormSq s (D.Rper i h a b)
          + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)))
      = C * (D.ENormB s h + D.ENormB 0 h) := by
    simp only [Work.Diff.STE.B3Data.ENormB, Finset.sum_add_distrib, ← Finset.mul_sum]
  rwa [hsplit] at hsum

end Work.Diff.STE.B3.VarCoef
