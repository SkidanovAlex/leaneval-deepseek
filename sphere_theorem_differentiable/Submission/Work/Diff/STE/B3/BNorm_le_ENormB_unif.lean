import Mathlib
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lead (2026-10-02): proved lemma extracted from Lead/deTurck_limit.lean (BNorm_le_ENormB_uniform, l.1002)
-- so that modules outside the deTurck_limit target (e.g. GalTame/galVF2_coeff_bound) need not import a live target.

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology

namespace Work.Diff.STE.B3

/-- **`BNorm ≤ C (ENormB + ENormB 0)`, uniformly in the section** (the `ENormB` version of
`BNorm_le_ENormB` with the constant hoisted outside the quantifier). -/
theorem BNorm_le_ENormB_unif
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ k (D.Rper i h a b))
      (hper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.Periodic1 (D.Rper i h a b)),
      D.BNorm k h ≤ C * (D.ENormB k h + D.ENormB 0 h) := by
  obtain ⟨C, hC, hCb⟩ := Work.Diff.STE.CSq_le_ENormSq (ι := Fin (Module.finrank ℝ E)) k
  refine ⟨C, hC, fun h hsm hper => ?_⟩
  have hterm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
        ≤ C * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
          + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) :=
    fun i a b => hCb _ (hsm i a b) (hper i a b)
  simp only [Work.Diff.STE.B3Data.BNorm, Work.Diff.STE.B3Data.ENormB]
  calc ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
      ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        C * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
          + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => ?_
        exact hterm i a b
    _ = C * (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (Work.Diff.STE.ENormSq k (D.Rper i h a b)
            + Work.Diff.STE.ENormSq 0 (D.Rper i h a b))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = C * (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq k (D.Rper i h a b)
        + ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) := by
        congr 1
        refine (Finset.sum_congr rfl fun i _ => ?_).trans Finset.sum_add_distrib
        refine (Finset.sum_congr rfl fun a _ => ?_).trans Finset.sum_add_distrib
        exact Finset.sum_add_distrib


end Work.Diff.STE.B3
