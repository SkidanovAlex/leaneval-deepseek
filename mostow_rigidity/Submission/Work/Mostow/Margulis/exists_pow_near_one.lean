import Mathlib

namespace Work.Mostow.Margulis

open Metric

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The coercion `V ≃ₗᵢ[ℝ] V → V →L[ℝ] V` is multiplicative (composition of maps). -/
lemma coe_clm_mul (T T' : V ≃ₗᵢ[ℝ] V) :
    ((T * T' : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) = (T : V →L[ℝ] V) * (T' : V →L[ℝ] V) := by
  ext v; simp

/-- The coercion `V ≃ₗᵢ[ℝ] V → V →L[ℝ] V` sends `1` to `1`. -/
lemma coe_clm_one : ((1 : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) = 1 := by
  ext v; simp

/-- The coercion `V ≃ₗᵢ[ℝ] V → V →L[ℝ] V` commutes with powers. -/
lemma coe_clm_pow (T : V ≃ₗᵢ[ℝ] V) (k : ℕ) :
    ((T ^ k : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) = ((T : V →L[ℝ] V)) ^ k := by
  induction k with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, coe_clm_mul, ih]

end

/-- For an orthogonal transformation `T` of a finite-dimensional real inner product space and any
`ε > 0`, some positive power of `T` is within operator norm `ε` of the identity.

Proof plan.  If `T` has finite order `n` then `T ^ n = 1` and we are done.  Otherwise consider the
sequence `k ↦ (T ^ k : V →L[ℝ] V)`; it is contained in the closed unit ball, which is compact
because `V →L[ℝ] V` is finite dimensional over `ℝ`, so two of its terms satisfy
`‖T ^ i - T ^ j‖ ≤ ε` for some `i < j`.  Then `k := j - i ≥ 1` and
`‖T ^ k - 1‖ = ‖(T ^ i : V →L[ℝ] V) * (T ^ k - 1)‖ = ‖T ^ j - T ^ i‖ ≤ ε`, the middle equality
using that left multiplication by the isometry `T ^ i` preserves the operator norm. -/
theorem exists_pow_near_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : V ≃ₗᵢ[ℝ] V) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ ‖((T ^ k : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) - 1‖ ≤ ε := by
  -- the sequence of powers, viewed as continuous linear maps
  let a : ℕ → (V →L[ℝ] V) := fun k => ((T ^ k : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)
  have haeq : ∀ k, a k = ((T : V →L[ℝ] V)) ^ k := fun k => coe_clm_pow T k
  -- every term lies in the closed unit ball of the (finite-dimensional, hence proper) operator space
  have hmem : ∀ k, a k ∈ Metric.closedBall (0 : V →L[ℝ] V) 1 := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right]
    refine ContinuousLinearMap.opNorm_le_bound (a k) zero_le_one ?_
    intro v
    rw [one_mul]
    exact le_of_eq (LinearIsometryEquiv.norm_map (T ^ k) v)
  -- compactness: pass to a convergent subsequence
  obtain ⟨x, _hx, φ, hφmono, hφlim⟩ :=
    (isCompact_closedBall (0 : V →L[ℝ] V) 1).isSeqCompact (x := a) hmem
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hφlim) (ε / 2) (by linarith)
  have hd1 : dist (a (φ N)) x < ε / 2 := hN N le_rfl
  have hd2 : dist (a (φ (N + 1))) x < ε / 2 := hN (N + 1) (Nat.le_succ N)
  have hlt : φ N < φ (N + 1) := hφmono (Nat.lt_succ_self N)
  -- two successive terms of the subsequence are `ε`-close
  have hdist : dist (a (φ N)) (a (φ (N + 1))) ≤ ε := by
    calc dist (a (φ N)) (a (φ (N + 1)))
        ≤ dist (a (φ N)) x + dist x (a (φ (N + 1))) := dist_triangle _ _ _
      _ = dist (a (φ N)) x + dist (a (φ (N + 1))) x := by
            rw [dist_comm x (a (φ (N + 1)))]
      _ ≤ ε := by linarith
  refine ⟨φ (N + 1) - φ N, by omega, ?_⟩
  change ‖a (φ (N + 1) - φ N) - 1‖ ≤ ε
  set i := φ N with hi
  set j := φ (N + 1) with hj
  have hij : i < j := hlt
  have hik : i + (j - i) = j := Nat.add_sub_of_le (le_of_lt hij)
  have hdist' : ‖a i - a j‖ ≤ ε := by
    rw [← dist_eq_norm]; exact hdist
  -- control `‖(a k - 1) v‖` pointwise, using that `a i` is an isometry
  refine ContinuousLinearMap.opNorm_le_bound (a (j - i) - 1) hε.le ?_
  intro v
  have hmul : a i * a (j - i) = a j := by
    simp only [haeq]; rw [← pow_add, hik]
  have h1 : a i (a (j - i) v - v) = a j v - a i v := by
    rw [map_sub]
    congr 1
    calc a i (a (j - i) v) = (a i * a (j - i)) v := by rw [mul_apply_eq_comp]
      _ = a j v := by rw [hmul]
  have hnorm1 : ‖a i (a (j - i) v - v)‖ = ‖a (j - i) v - v‖ :=
    LinearIsometryEquiv.norm_map (T ^ i) (a (j - i) v - v)
  have hle : ‖a j v - a i v‖ ≤ ε * ‖v‖ := by
    calc ‖a j v - a i v‖ = ‖(a j - a i) v‖ := by rw [sub_apply]
      _ ≤ ‖a j - a i‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖a i - a j‖ * ‖v‖ := by rw [norm_sub_rev]
      _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hdist' (norm_nonneg v)
  calc ‖(a (j - i) - 1) v‖ = ‖a (j - i) v - v‖ := by
        rw [sub_apply, one_apply_eq_self]
     _ = ‖a i (a (j - i) v - v)‖ := hnorm1.symm
     _ = ‖a j v - a i v‖ := by rw [h1]
     _ ≤ ε * ‖v‖ := hle

end Work.Mostow.Margulis
