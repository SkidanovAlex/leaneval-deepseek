import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Topology.Metric

open _root_.Metric

/-- **Uniform boundedness of an equicontinuous family on compact sets.**

Let `u : ℕ → X → ℝ` be a sequence of functions on a normed space `X` that vanish at a point
`x₀` and are uniformly equicontinuous at scale `ε` (i.e. with a modulus of continuity which
is uniform in `n`).  Then `u n` is uniformly bounded on every compact subset `K` of `X`.

The proof walks along the straight segment from `x₀` to a point `x ∈ K`: since `K` is bounded,
say `K ⊆ ball x₀ R`, and the family is `1`-equicontinuous at scale `δ`, splitting the segment
into `M` steps with `R / M < δ` yields `|u n x - u n x₀| ≤ M`. -/
theorem exists_bound_of_equicontinuous_compacts {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    {u : ℕ → EuclideanSpace E (Fin N) → ℝ} {x₀ : EuclideanSpace E (Fin N)}
    (h0 : ∀ n, u n x₀ = 0)
    (heq : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n (x y : EuclideanSpace E (Fin N)),
      dist x y < δ → |u n x - u n y| < ε) :
    ∀ K : Set (EuclideanSpace E (Fin N)), IsCompact K →
      ∃ C : ℝ, ∀ n, ∀ x ∈ K, |u n x| ≤ C := by
  intro K hK
  classical
  obtain ⟨δ, hδpos, hδ⟩ := heq 1 (by norm_num)
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.subset_ball_lt 0 x₀
  obtain ⟨M, hM⟩ := exists_nat_gt (R / δ)
  have hMposR : (0 : ℝ) < (M : ℝ) := (div_pos hRpos hδpos).trans hM
  have hMpos : 0 < M := Nat.cast_pos.mp hMposR
  have hRM : R / M < δ := by
    rw [div_lt_iff₀ hMposR]
    have h1 : R < (M : ℝ) * δ := (div_lt_iff₀ hδpos).mp hM
    linarith
  refine ⟨(M : ℝ), fun n x hxK => ?_⟩
  have hxR : dist x x₀ < R := mem_ball.mp (hR hxK)
  let f : ℕ → EuclideanSpace E (Fin N) := fun k => x₀ + ((k : ℝ) / M) • (x - x₀)
  have hf0 : f 0 = x₀ := by simp [f]
  have hfM : f M = x := by
    simp only [f]
    rw [div_self (by positivity : ((M : ℕ) : ℝ) ≠ 0), one_smul]
    abel
  have hdistk : ∀ k : ℕ, dist (f (k + 1)) (f k) = dist x x₀ / M := by
    intro k
    have hv : f (k + 1) - f k = (1 / (M : ℝ)) • (x - x₀) := by
      simp only [f]
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      congr 1
      push_cast
      field_simp
      ring
    rw [dist_eq_norm, hv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / M)]
    rw [one_div, inv_mul_eq_div, ← dist_eq_norm]
  have hstep : ∀ k : ℕ, |u n (f (k + 1)) - u n (f k)| < 1 := by
    intro k
    refine hδ n (f (k + 1)) (f k) ?_
    rw [hdistk k]
    exact lt_trans (div_lt_div_of_pos_right hxR hMposR) hRM
  have hkey : ∀ k : ℕ, |u n (f k) - u n (f 0)| ≤ (k : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs : |u n (f (k + 1)) - u n (f k)| < 1 := hstep k
      have htri : |u n (f (k + 1)) - u n (f 0)|
          ≤ |u n (f (k + 1)) - u n (f k)| + |u n (f k) - u n (f 0)| := by
        have : u n (f (k + 1)) - u n (f 0)
            = (u n (f (k + 1)) - u n (f k)) + (u n (f k) - u n (f 0)) := by ring
        rw [this]
        exact abs_add_le _ _
      calc |u n (f (k + 1)) - u n (f 0)|
          ≤ |u n (f (k + 1)) - u n (f k)| + |u n (f k) - u n (f 0)| := htri
        _ ≤ 1 + (k : ℝ) := by linarith [hs.le, ih]
        _ = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  have := hkey M
  rw [hfM, hf0, h0 n, sub_zero] at this
  exact this

end Commons.Topology.Metric