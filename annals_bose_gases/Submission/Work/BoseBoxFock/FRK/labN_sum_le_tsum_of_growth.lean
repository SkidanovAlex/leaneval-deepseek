import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.lattice_heatSubordination
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.FRK

theorem labN_sum_le_tsum_of_growth {ℓ : ℝ} (hℓ : 0 < ℓ)
    {σ : EuclideanSpace ℝ (Fin 3) → ℝ} (hσ : ∀ p, 0 ≤ σ p)
    (hgr : ∃ A : ℝ, ∀ p, |σ p| ≤ A * (1 + ‖p‖) ^ 2)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (N : ℕ) :
    (∑ k : Work.BoseBoxFock.Lab N, (ℓ ^ 3)⁻¹ * σ (Work.BoseBoxFock.kmomLab ℓ N k) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2)
      ≤ ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * σ (Work.BoseBoxFock.kmomInt ℓ n) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 := by
  classical
  obtain ⟨A, hA⟩ := hgr
  -- the summand, indexed by the full lattice `ℤ³`
  set F : (Fin 3 → ℤ) → ℝ := fun n =>
    (ℓ ^ 3)⁻¹ * σ (Work.BoseBoxFock.kmomInt ℓ n) *
      ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 with hF
  -- nonnegativity of every term
  have hFnn : ∀ n, 0 ≤ F n := by
    intro n
    rw [hF]
    exact mul_nonneg (mul_nonneg (by positivity) (hσ _)) (by positivity)
  -- the explicit majorant of the growth bound
  set G : (Fin 3 → ℤ) → ℝ := fun n =>
    (ℓ ^ 3)⁻¹ * (1 + ‖Work.BoseBoxFock.kmomInt ℓ n‖) ^ 2 *
      ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 with hG
  have hGnn : ∀ n, 0 ≤ G n := by
    intro n
    rw [hG]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)
  -- `(1+u)² w ≤ 2w + 2u²w`
  have hGle : ∀ n, G n ≤ 2 * ((ℓ ^ 3)⁻¹ *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      + 2 * ((ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by
    intro n
    simp only [hG]
    have hq : (1 + ‖Work.BoseBoxFock.kmomInt ℓ n‖) ^ 2 ≤
        2 * (1 + ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2) := by
      nlinarith [sq_nonneg (‖Work.BoseBoxFock.kmomInt ℓ n‖ - 1)]
    have hw : 0 ≤ (ℓ ^ 3)⁻¹ *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 := by positivity
    calc (ℓ ^ 3)⁻¹ * (1 + ‖Work.BoseBoxFock.kmomInt ℓ n‖) ^ 2 *
          ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
        = (1 + ‖Work.BoseBoxFock.kmomInt ℓ n‖) ^ 2 * ((ℓ ^ 3)⁻¹ *
            ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by ring
      _ ≤ (2 * (1 + ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2)) * ((ℓ ^ 3)⁻¹ *
            ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hq hw
      _ = 2 * ((ℓ ^ 3)⁻¹ *
            ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
          + 2 * ((ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 *
            ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by ring
  -- the two lattice rows of `summable_lattice_kinFT_weight`
  have h0s : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ *
      ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by
    simpa using summable_lattice_kinFT_weight hℓ hg hgc 0
  have h2s : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 *
      ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) :=
    summable_lattice_kinFT_weight hℓ hg hgc 2
  have hGs : Summable G :=
    Summable.of_nonneg_of_le hGnn hGle ((h0s.mul_left 2).add (h2s.mul_left 2))
  -- termwise domination of `F` by the growth bound
  have hFG : ∀ n, F n ≤ A * G n := by
    intro n
    have h2 : σ (Work.BoseBoxFock.kmomInt ℓ n) ≤
        A * (1 + ‖Work.BoseBoxFock.kmomInt ℓ n‖) ^ 2 := le_trans (le_abs_self _) (hA _)
    have hw : 0 ≤ (ℓ ^ 3)⁻¹ *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 := by positivity
    simp only [hF, hG]
    calc (ℓ ^ 3)⁻¹ * σ (Work.BoseBoxFock.kmomInt ℓ n) *
          ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
        = σ (Work.BoseBoxFock.kmomInt ℓ n) * ((ℓ ^ 3)⁻¹ *
            ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by ring
      _ ≤ (A * (1 + ‖Work.BoseBoxFock.kmomInt ℓ n‖) ^ 2) * ((ℓ ^ 3)⁻¹ *
            ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h2 hw
      _ = A * ((ℓ ^ 3)⁻¹ * (1 + ‖Work.BoseBoxFock.kmomInt ℓ n‖) ^ 2 *
            ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by ring
  have hFs : Summable F :=
    Summable.of_nonneg_of_le hFnn hFG (hGs.mul_left A)
  -- the labels of `Lab N` inject into `ℤ³`
  have hinj : Set.InjOn (Work.BoseBoxFock.labVec N)
      ↑(Finset.univ : Finset (Work.BoseBoxFock.Lab N)) :=
    fun x _ y _ hxy => funext fun i => ZMod.valMinAbs_inj.mp (congrFun hxy i)
  have hsum_img := Finset.sum_image (s := (Finset.univ : Finset (Work.BoseBoxFock.Lab N)))
    (g := Work.BoseBoxFock.labVec N) (f := F) hinj
  -- the left-hand side is the sub-sum over the image of `labVec N`
  have hLHS : (∑ k : Work.BoseBoxFock.Lab N, (ℓ ^ 3)⁻¹ * σ (Work.BoseBoxFock.kmomLab ℓ N k) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2)
      = ∑ n ∈ (Finset.univ.image (Work.BoseBoxFock.labVec N)), F n := by
    rw [hsum_img]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hF]
    rw [show Work.BoseBoxFock.kmomLab ℓ N k
        = Work.BoseBoxFock.kmomInt ℓ (Work.BoseBoxFock.labVec N k) from rfl]
  rw [hLHS]
  exact hFs.sum_le_tsum _ (fun n _ => hFnn n)

end Work.BoseBoxFock.FRK
