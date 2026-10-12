import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.lattice_heatSubordination
import Submission.Work.BoseBoxFock.tauSmPhiDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.labN_sum_le_tsum`

The `Lab N`-truncated lattice kinetic sum is dominated by the *full* lattice sum over `ℤ³`:

    Σ_{k ∈ Lab N} (ℓ³)⁻¹(c²τ(‖k_k‖/c))‖ĝ(k_k)‖²  ≤  Σ'_{n ∈ ℤ³} (ℓ³)⁻¹(c²τ(‖k_n‖/c))‖ĝ(k_n)‖² .

Both sides are nonnegative and the right-hand series converges.  The finite lattice
`Lab N = (ZMod (2N+1))³` embeds into `ℤ³` through its centred representative `labVec N`
(`labVec_injective`), and `kmomLab ℓ N k = kmomInt ℓ (labVec N k)`, so the left-hand side is a
sub-sum of the right-hand side over the finite set `univ.image (labVec N)`.

The convergence is immediate from the sharp bound `c²τ(r/c) ≤ r²` (`sq_mul_tauPhi_le_sq`): the
summand is dominated *termwise* by the second-moment lattice row
`(ℓ³)⁻¹‖k_n‖²‖ĝ(k_n)‖²`, which is summable by `summable_lattice_kinFT_weight` (polynomial decay of
`kinFT g` for `g` smooth of compact support, against the lattice decay
`Work.BoseK15.sum_inv_one_add_norm_le`).
-/

namespace Work.BoseBoxFock

/-- `kmomLab` is `kmomInt` at the centred integer vector `labVec` (definitional). -/
lemma kmomLab_eq_kmomInt_labN (ℓ : ℝ) (N : ℕ) (k : Lab N) :
    kmomLab ℓ N k = kmomInt ℓ (labVec N k) := rfl

theorem labN_sum_le_tsum {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (N : ℕ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    (∑ k : Work.BoseBoxFock.Lab N, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomLab ℓ N k‖ / c)) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2)
      ≤ (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by
  classical
  -- the summand of both sides
  set F : (Fin 3 → ℤ) → ℝ := fun n =>
    (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
      ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 with hF
  -- nonnegativity of every term
  have hFnn : ∀ n, 0 ≤ F n := by
    intro n
    rw [hF]
    have h1 : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
    have h2 : 0 ≤ c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c) :=
      mul_nonneg (sq_nonneg c) (tauPhi_nonneg _)
    exact mul_nonneg (mul_nonneg h1 h2) (by positivity)
  -- `c²τ(‖k‖/c) ≤ ‖k‖²`, so the summand is termwise below the second-moment lattice row
  have hdom : ∀ n, F n ≤ (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2 *
      ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by
    intro n
    have hb := sq_mul_tauPhi_le_sq hc (norm_nonneg (kmomInt ℓ n))
    have h1 : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
    have hk : (0 : ℝ) ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by positivity
    calc F n = (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
          ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by rw [hF]
      _ ≤ (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2 *
          ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hk
          exact mul_le_mul_of_nonneg_left hb h1
  -- summability of the full lattice series
  have hsumm : Summable F :=
    Summable.of_nonneg_of_le hFnn hdom (summable_lattice_kinFT_weight hℓ hg hgc 2)
  -- the labels of `Lab N` inject into `ℤ³`
  have hinj : Set.InjOn (labVec N) ↑(Finset.univ : Finset (Lab N)) :=
    fun x _ y _ hxy => funext fun i => ZMod.valMinAbs_inj.mp (congrFun hxy i)
  have hsum_img := Finset.sum_image (s := (Finset.univ : Finset (Lab N)))
    (g := labVec N) (f := F) hinj
  -- the left-hand side is the sub-sum over the image of `labVec N`
  have hLHS : (∑ k : Lab N, (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomLab ℓ N k‖ / c)) *
        ‖Submission.BoseGases.kinFT g (kmomLab ℓ N k)‖ ^ 2)
      = ∑ n ∈ (Finset.univ.image (labVec N)), F n := by
    rw [hsum_img]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hF, kmomLab_eq_kmomInt_labN]
  rw [hLHS]
  exact hsumm.sum_le_tsum _ (fun n _ => hFnn n)

end Work.BoseBoxFock
