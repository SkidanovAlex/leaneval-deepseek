import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.expect_pair_sub_triple
import Submission.Work.Deep.Sparse.ncp_concentration

namespace Work.Deep.Sparse

/-- **Lower tail of `pairTerm - tripleTerm` in the naive colouring procedure.**

The statistic `X = pairTerm v - tripleTerm v` of the partial colouring `ofColoring G f` has
expectation at least `μ = (|nonAdjPairs G v|/2)·(1/k)·((k-1)/k)^(2D)·(1 - D/(3k))`
(`Work.Deep.Sparse.expect_pair_sub_triple`).  The deep input
`Work.Deep.Sparse.ncp_concentration` says that `X` is concentrated at the much smaller scale
`ω/6`, where `ω = (|nonAdjPairs G v|/2)·(1/k)·((k-1)/k)^(2D)`; since `D ≤ 2k` gives
`μ = ω(1 - D/(3k)) ≥ ω/3`, the half threshold `μ/2` lies below `ω(1-D/(3k)) - ω/6`, so the
event `X < μ/2` is contained in the deviation event of `ncp_concentration`, and the claimed
bound follows by monotonicity of `prob`. -/
theorem ncp_lower_tail {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k D : ℕ} (hk : 0 < k) (hD : 0 < D) (hDk : D ≤ 2 * k) (hkD : (k : ℝ) ≤ 2 * D)
    [Nonempty (V → Fin k)] (hdeg : ∀ x : V, G.degree x ≤ D) (v : V)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsp : (δ / 2) * (D : ℝ) ^ 2 / 2 ≤ ((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2)
    (hbig : (10 : ℝ) ^ 6 * (Real.log ((D : ℝ) + 2)) ^ 8 ≤ δ ^ 2 * (D : ℝ)) :
    (Work.Deep.Sparse.colSpace (V := V) k).prob
        {f | (((Work.Deep.Sparse.ofColoring G f).pairTerm v : ℝ)
              - ((Work.Deep.Sparse.ofColoring G f).tripleTerm v : ℝ))
            < (1 / 2) * (((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2
                * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
                * (1 - (D : ℝ) / (3 * (k : ℝ))))}
      ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000) := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hDkR : (D : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hDk
  -- the statistic `X` and the deviation scale `ω`
  set X : (V → Fin k) → ℝ := fun f =>
    (((Work.Deep.Sparse.ofColoring G f).pairTerm v : ℝ)
      - ((Work.Deep.Sparse.ofColoring G f).tripleTerm v : ℝ)) with hX
  set ω : ℝ := ((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2
      * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D)) with hω
  -- the expectation lower bound of `expect_pair_sub_triple`, in the shape `(1 - D/(3k))·ω ≤ E X`
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hbase : (0 : ℝ) ≤ (((k : ℝ) - 1) / (k : ℝ)) := div_nonneg (by linarith) (le_of_lt hkR)
  have hω0 : 0 ≤ ω := by
    rw [hω]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num))
      (mul_nonneg (div_nonneg zero_le_one (le_of_lt hkR)) (pow_nonneg hbase _))
  have hDk3 : (D : ℝ) / (3 * (k : ℝ)) ≤ 2 / 3 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (k : ℝ))]
    linarith
  have hexp : (1 - (D : ℝ) / (3 * (k : ℝ))) * ω ≤ (Work.Deep.Sparse.colSpace (V := V) k).expect X := by
    have h := Work.Deep.Sparse.expect_pair_sub_triple (V := V) G hk hD hDk hdeg v
    calc (1 - (D : ℝ) / (3 * (k : ℝ))) * ω
        = ((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2 * (1 - (D : ℝ) / (3 * (k : ℝ)))
            * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D)) := by
          rw [hω]; ring
      _ ≤ (Work.Deep.Sparse.colSpace (V := V) k).expect
            (fun f => (((Work.Deep.Sparse.ofColoring G f).pairTerm v : ℝ)
              - ((Work.Deep.Sparse.ofColoring G f).tripleTerm v : ℝ))) := h
      _ = (Work.Deep.Sparse.colSpace (V := V) k).expect X := by rw [hX]
  -- the containment of the half-threshold event in the deviation event
  have hsub : {f : V → Fin k |
        X f < (1 / 2) * (((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2
          * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
          * (1 - (D : ℝ) / (3 * (k : ℝ))))}
      ⊆ {f : V → Fin k | (1 / 6) * ω ≤ |X f - (Work.Deep.Sparse.colSpace (V := V) k).expect X|} := by
    intro f hf
    simp only [Set.mem_setOf_eq] at hf ⊢
    have hthr : (1 / 2) * (((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2
          * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
          * (1 - (D : ℝ) / (3 * (k : ℝ))))
        = (1 / 2) * ((1 - (D : ℝ) / (3 * (k : ℝ))) * ω) := by
      rw [hω]; ring
    rw [hthr] at hf
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (Work.Deep.Sparse.colSpace (V := V) k).expect X - (1 / 6) * ω < X f := by
      have := (abs_lt.mp hcon).1
      linarith
    have h2 : (1 / 2) * ((1 - (D : ℝ) / (3 * (k : ℝ))) * ω)
        ≤ (Work.Deep.Sparse.colSpace (V := V) k).expect X - (1 / 6) * ω := by
      have h3 : (1 : ℝ) / 6 ≤ (1 / 2) * (1 - (D : ℝ) / (3 * (k : ℝ))) := by linarith
      have h4 : (1 / 6) * ω ≤ (1 / 2) * ((1 - (D : ℝ) / (3 * (k : ℝ))) * ω) := by
        nlinarith [mul_le_mul_of_nonneg_right h3 hω0]
      linarith
    linarith
  refine le_trans (Work.Deep.Sparse.FinSpace.prob_mono (Work.Deep.Sparse.colSpace (V := V) k) hsub) ?_
  exact Work.Deep.Sparse.ncp_concentration G hk hD hDk hkD hdeg v hδ0 hδ1 hsp hbig

end Work.Deep.Sparse
