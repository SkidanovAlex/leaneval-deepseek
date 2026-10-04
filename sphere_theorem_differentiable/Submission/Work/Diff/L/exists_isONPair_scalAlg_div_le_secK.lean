import Mathlib
import Submission.Work.Diff.Alg.PA.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

open Finset Submission.Diff.Alg Work.Diff.Alg.PA

/-- **Some plane has sectional curvature at least the average.** For an algebraic curvature
tensor `R` on `ℝⁿ` (`n ≥ 2`), the scalar curvature is the sum of `Rᵢⱼᵢⱼ` over all ordered pairs,
the diagonal terms vanish, so the average of `secK R` over the `n(n-1)` ordered orthonormal pairs
`(eᵢ, eⱼ)`, `i ≠ j`, equals `scalAlg R / (n(n-1))`. A maximising pair therefore has sectional
curvature at least that average. -/
theorem exists_isONPair_scalAlg_div_le_secK {n : ℕ} (hn : 2 ≤ n)
    {R : Submission.Diff.Alg.Curv4 n} (hR : Submission.Diff.Alg.IsAlgCurv R) :
    ∃ u v : Fin n → ℝ, Submission.Diff.Alg.IsONPair u v ∧
      Submission.Diff.Alg.scalAlg R / ((n : ℝ) * ((n : ℝ) - 1)) ≤ Submission.Diff.Alg.secK R u v := by
  classical
  -- Diagonal curvature components vanish.
  have hdiag : ∀ i : Fin n, R i i i i = 0 := by
    intro i
    have h := hR.1 i i i i
    linarith
  -- The set of ordered pairs `(i, j)` with `i ≠ j`, as `univ.offDiag`.
  set T : Finset (Fin n × Fin n) := (Finset.univ : Finset (Fin n)).offDiag with hT
  have hTmem : ∀ p : Fin n × Fin n, p ∈ T ↔ p.1 ≠ p.2 := by
    intro p; rw [hT]; simp [Finset.mem_offDiag]
  have hTcard : T.card = n * n - n := by
    rw [hT, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  have hTpos : 0 < T.card := by
    rw [hTcard]
    have hmul : n * (n - 1) = n * n - n := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have : 2 ≤ n * n - n := by
      rw [← hmul]
      calc (2 : ℕ) = 2 * 1 := by norm_num
        _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  -- A maximising off-diagonal pair.
  obtain ⟨p0, hp0T, hp0max⟩ :=
    Finset.exists_max_image T (fun p : Fin n × Fin n => R p.1 p.2 p.1 p.2) (Finset.card_pos.mp hTpos)
  have hp0ne : p0.1 ≠ p0.2 := (hTmem p0).mp hp0T
  have hsum1 : scalAlg R = ∑ p : Fin n × Fin n, R p.1 p.2 p.1 p.2 := by
    rw [scalAlg]
    exact (Fintype.sum_prod_type (f := fun p : Fin n × Fin n => R p.1 p.2 p.1 p.2)).symm
  have hsum2 : (∑ p ∈ T, R p.1 p.2 p.1 p.2) = ∑ p : Fin n × Fin n, R p.1 p.2 p.1 p.2 := by
    apply Finset.sum_subset (Finset.subset_univ T)
    intro p _ hpT
    have hpT' : ¬ (p.1 ≠ p.2) := fun h => hpT ((hTmem p).mpr h)
    have hpp : p.1 = p.2 := not_not.mp hpT'
    have hp : p = (p.1, p.1) := Prod.ext rfl hpp.symm
    rw [hp]
    exact hdiag p.1
  have hcardR : (T.card : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [hTcard]
    rw [Nat.cast_sub (Nat.le_mul_self n)]
    push_cast
    ring
  -- The scalar curvature is at most `n(n-1)` times the maximal sectional curvature.
  have hle : scalAlg R ≤ (n : ℝ) * ((n : ℝ) - 1) * (R p0.1 p0.2 p0.1 p0.2) := by
    rw [hsum1, ← hsum2]
    calc (∑ p ∈ T, R p.1 p.2 p.1 p.2)
        ≤ ∑ _p ∈ T, R p0.1 p0.2 p0.1 p0.2 := Finset.sum_le_sum (fun p hp => hp0max p hp)
      _ = (T.card : ℝ) * (R p0.1 p0.2 p0.1 p0.2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (n : ℝ) * ((n : ℝ) - 1) * (R p0.1 p0.2 p0.1 p0.2) := by rw [hcardR]
  have hpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := by
    have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  -- The maximiser is realised by an orthonormal pair of standard basis vectors.
  refine ⟨stdB n p0.1, stdB n p0.2, isONPair_stdB hp0ne, ?_⟩
  rw [secK_stdB]
  rw [div_le_iff₀ hpos]
  nlinarith [hle]

end Work.Diff.L
