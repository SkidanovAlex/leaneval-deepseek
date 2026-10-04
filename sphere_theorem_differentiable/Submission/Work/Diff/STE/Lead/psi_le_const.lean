import Mathlib
import Submission.Work.Diff.STE.Lead.MatJetDefs
import Submission.Work.Diff.STE.B3.CompSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-- The localised weights `D.psi i = χ i · (ζ i ∘ pt i)` are uniformly bounded.  (Used to convert
a lower bound `c ≤ D.psi i z` into the observation that the relevant `c` is bounded above, since
`D.psi i z ≤ M`.)

Route.  `D.psi i z = D.χ i z * D.ζ i (D.pt i z)` and `0 ≤ D.ζ i (D.pt i z) ≤ 1` for every point
(from `D.hζnn` and `D.hζsq`: `ζ i p ^ 2 ≤ ∑ j, ζ j p ^ 2 = 1`).  So it remains to bound `χ i`
from above on the open cube `Set.pi Set.univ (fun _ => Set.Ioo (-(1/2) : ℝ) (1/2))`, which contains
`Function.support (D.χ i)` (`D.hχsupp`): on the compact closed cube
`Set.pi Set.univ (fun _ => Set.Icc (-(1/2) : ℝ) (1/2))` the continuous function `D.χ i` is bounded
(`IsCompact.exists_isMaxOn`, `D.hχsm i`), and off the closed cube `χ i` vanishes because it vanishes
off the open cube (`Function.support`).  Take the maximum over the finite type `ι₀`.

Note: `M = 1` is NOT provable in general — `B3Data` does not require `χ i ≤ 1`, only
`χ i = 1` on the `σ i`-ball (`D.hχ1`), so the compactness argument on the cube is needed. -/
theorem psi_le_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), D.psi i z ≤ M := by
  classical
  -- the compact closed cube on which the localised components live
  set K : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    Set.pi Set.univ (fun _ => Set.Icc (-(1/2 : ℝ)) (1/2)) with hK
  have hKcompact : IsCompact K := by
    rw [hK]
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have h0mem : (0 : Fin (Module.finrank ℝ E) → ℝ) ∈ K := by
    rw [hK, Set.mem_pi]
    intro j _
    exact ⟨by norm_num, by norm_num⟩
  have hKne : K.Nonempty := ⟨0, h0mem⟩
  -- the open cube is contained in the closed cube
  have hopenK : Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2 : ℝ)) (1/2))
      ⊆ K := by
    intro w hw
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left] at hw
    rw [hK, Set.mem_pi]
    intro j _
    exact ⟨le_of_lt (hw j).1, le_of_lt (hw j).2⟩
  -- a uniform upper bound for each `χ i` on the cube
  have hb : ∀ i : ι₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, D.χ i z ≤ C := by
    intro i
    obtain ⟨x, _, hxmax⟩ := hKcompact.exists_isMaxOn hKne (D.hχsm i).continuous.continuousOn
    have hchi0 : D.χ i (0 : Fin (Module.finrank ℝ E) → ℝ) = 1 :=
      D.hχ1 i 0 (by rw [norm_zero]; exact (D.hσ i).le)
    have hge : (0 : ℝ) ≤ D.χ i x := by
      have : (1 : ℝ) ≤ D.χ i x := by rw [← hchi0]; exact hxmax h0mem
      linarith
    exact ⟨D.χ i x, hge, fun z hz => hxmax hz⟩
  choose C hCnn hCle using hb
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hCnn i), ?_⟩
  intro i z
  have hmemi : C i ≤ ∑ j, C j :=
    Finset.single_le_sum (fun j _ => hCnn j) (Finset.mem_univ i)
  -- `0 ≤ ζ i p ≤ 1`
  have hzle : D.ζ i (D.pt i z) ≤ 1 := by
    have h1 : (D.ζ i (D.pt i z)) ^ 2 ≤ ∑ j : ι₀, (D.ζ j (D.pt i z)) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (D.ζ j (D.pt i z))) (Finset.mem_univ i)
    rw [D.hζsq (D.pt i z)] at h1
    nlinarith [D.hζnn i (D.pt i z)]
  rw [Work.Diff.STE.B3Data.psi]
  by_cases hzK : z ∈ K
  · -- inside the cube: bound both factors
    have hχ : D.χ i z ≤ C i := hCle i z hzK
    have h1 : D.χ i z * D.ζ i (D.pt i z) ≤ C i * D.ζ i (D.pt i z) :=
      mul_le_mul_of_nonneg_right hχ (D.hζnn i (D.pt i z))
    have h2 : C i * D.ζ i (D.pt i z) ≤ C i * 1 :=
      mul_le_mul_of_nonneg_left hzle (hCnn i)
    linarith
  · -- outside the cube: `χ i` vanishes
    have hχ0 : D.χ i z = 0 := by
      by_contra h
      exact hzK (hopenK (D.hχsupp i h))
    rw [hχ0, zero_mul]
    exact Finset.sum_nonneg (fun j _ => hCnn j)

end Work.Diff.STE.Lead
