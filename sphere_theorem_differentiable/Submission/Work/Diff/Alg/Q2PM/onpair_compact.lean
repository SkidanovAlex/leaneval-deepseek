import Mathlib
import Submission.Work.Diff.Alg.Q2PM.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Q2PM

open Submission.Diff.Alg

/-- The set of orthonormal pairs in `ℝⁿ × ℝⁿ` is closed: it is cut out by the continuous
conditions `⟪u,u⟫ = 1`, `⟪v,v⟫ = 1`, `⟪u,v⟫ = 0`. -/
private theorem isClosed_isONPair (n : ℕ) :
    IsClosed {p : (Fin n → ℝ) × (Fin n → ℝ) | Submission.Diff.Alg.IsONPair p.1 p.2} := by
  have hc1 : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => Submission.Diff.Alg.dot p.1 p.1 := by
    unfold Submission.Diff.Alg.dot; fun_prop
  have hc2 : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => Submission.Diff.Alg.dot p.2 p.2 := by
    unfold Submission.Diff.Alg.dot; fun_prop
  have hc3 : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => Submission.Diff.Alg.dot p.1 p.2 := by
    unfold Submission.Diff.Alg.dot; fun_prop
  rw [show {p : (Fin n → ℝ) × (Fin n → ℝ) | Submission.Diff.Alg.IsONPair p.1 p.2}
      = (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          (Submission.Diff.Alg.dot p.1 p.1, Submission.Diff.Alg.dot p.2 p.2,
            Submission.Diff.Alg.dot p.1 p.2)) ⁻¹' {((1:ℝ),1,0)} from by
    ext p; simp [Submission.Diff.Alg.IsONPair]]
  exact IsClosed.preimage (hc1.prodMk (hc2.prodMk hc3)) isClosed_singleton

/-- A unit vector in `ℝⁿ` has all coordinates in `[-1,1]`. -/
private theorem coord_mem_Icc_of_dot_self_eq_one {n : ℕ} {u : Fin n → ℝ}
    (hu : (∑ j, u j * u j) = 1) (i : Fin n) : u i ∈ Set.Icc (-1:ℝ) 1 := by
  have hle := Finset.single_le_sum (f := fun j => u j * u j) (s := Finset.univ)
      (fun j _ => mul_self_nonneg (u j)) (Finset.mem_univ i)
  have habs : |u i| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    nlinarith [hle, hu]
  exact Set.mem_Icc.mpr (abs_le.mp habs)

theorem onpair_compact (n : ℕ) :
    IsCompact {p : (Fin n → ℝ) × (Fin n → ℝ) | Submission.Diff.Alg.IsONPair p.1 p.2} := by
  -- The set of orthonormal pairs sits inside the compact box `[-1,1]ⁿ × [-1,1]ⁿ`.
  have hT : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-1:ℝ) 1) ×ˢ
      Set.pi Set.univ (fun _ : Fin n => Set.Icc (-1:ℝ) 1)) :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).prod (isCompact_univ_pi (fun _ => isCompact_Icc))
  refine hT.of_isClosed_subset (isClosed_isONPair n) ?_
  rintro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [Submission.Diff.Alg.dot] at h1 h2
  exact ⟨Set.mem_pi.mpr (fun i _ => coord_mem_Icc_of_dot_self_eq_one h1 i),
    Set.mem_pi.mpr (fun i _ => coord_mem_Icc_of_dot_self_eq_one h2 i)⟩

end Work.Diff.Alg.Q2PM
