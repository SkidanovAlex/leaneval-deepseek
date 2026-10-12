import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.exists_jointGramLab
import Submission.Work.BoseFixR.FarZPDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

/-- **The monotonicity link** (`FINDING_farLatRow_sharp.md` §8, step 3, second half): the honest
cube row is at most the full-lattice row.

`latRow v h μ N ≤ (1/2)·Σ'_{k∈ℤ³∖0}(chat W q_k)²/‖q_k‖²`, with `W = W1fun v h (ell v μ)` and
`q_k = (ell v μ)⁻¹ • vec k` (`vec k = 2πk`).

Route: `kmomLab ℓ N k = ℓ⁻¹ • vec (labVec N k)`, and `Work.BoseFixR.labVec_injective N` together with
`labVec_zero` (`Submission/Work/BoseBoxFock/exists_jointGramLab.lean`) make `excited (Lab N)` map
injectively into `ℤ³∖{0}`; every finite summand is the corresponding `tsum` summand, summands are
`≥ 0`, and `Finset.sum_le_tsum` then gives the bound (`hsum` is needed because a non-summable `∑'` is
`0` in Lean).  The same map-into-nonzero argument is already carried out verbatim in
`honest_lattice_W1sq_le.lean:351-357`. -/
theorem latRowLeTsum {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {μ : ℝ} (N : ℕ)
    (hsum : Summable (fun k : Fin 3 → ℤ => if k = 0 then 0 else
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
          ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k)) ^ 2
        / ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k‖ ^ 2)) :
    Work.BoseFixR.latRow v h μ N ≤ (1 / 2) * ∑' k : Fin 3 → ℤ, if k = 0 then 0 else
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
          ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k)) ^ 2
        / ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k‖ ^ 2 := by
  classical
  -- the summand of the full-lattice row, as a function of the lattice label
  set F : (Fin 3 → ℤ) → ℝ := fun k => if k = 0 then 0 else
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
          ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k)) ^ 2
        / ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k‖ ^ 2 with hF
  have hsumm : Summable F := by rw [hF]; exact hsum
  have hFnn : ∀ k : Fin 3 → ℤ, 0 ≤ F k := by
    intro k
    rw [hF]
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, if_false]
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hinj : Function.Injective (Work.BoseBoxFock.labVec N) :=
    Work.BoseBoxFock.GramLab.labVec_injective N
  -- the image of the excited cube labels under `labVec`, an honest subset of the lattice
  set S : Finset (Fin 3 → ℤ) :=
    (Work.BoseB7.excited (Work.BoseBoxFock.Lab N)).image (Work.BoseBoxFock.labVec N) with hS
  -- `excited (Lab N)` lands in the non-zero labels, so each finite summand is `(1/2)` of the
  -- corresponding `tsum` summand
  have hpoint : ∀ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
          (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) N k)) ^ 2
        / (2 * ‖Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) N k‖ ^ 2)
      = (1 / 2) * F (Work.BoseBoxFock.labVec N k) := by
    intro k hk
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    have hlv : Work.BoseBoxFock.labVec N k ≠ 0 := by
      intro hh
      exact hk0 (hinj (by rw [hh, Work.BoseBoxFock.GramLab.labVec_zero]))
    rw [hF]
    simp only [hlv, if_false]
    rw [Work.BoseBoxFock.GramLab.kmomLab_eq_smul_vec]
    ring
  -- rewrite the honest cube row as `(1/2)` times the finite row over those lattice labels
  have hmain : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
          (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) N k)) ^ 2
        / (2 * ‖Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) N k‖ ^ 2))
      = (1 / 2) * ∑ j ∈ S, F j := by
    rw [hS, Finset.sum_image (fun x _ y _ hxy => hinj hxy), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k hk => hpoint k hk)
  rw [Work.BoseFixR.latRow, hmain]
  exact mul_le_mul_of_nonneg_left
    (Summable.sum_le_tsum S (fun i _ => hFnn i) hsumm) (by norm_num)

end Work.BoseFixR.LatGreen
