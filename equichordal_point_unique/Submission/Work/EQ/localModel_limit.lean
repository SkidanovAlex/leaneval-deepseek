import Mathlib
import Submission.Work.EQ.LocalModelAux

namespace Work.EQ

open Filter

/-- Norm of a difference of real embeddings in `ℂ`. -/
lemma norm_ofReal_sub (a b : ℝ) : ‖((a : ℝ) : ℂ) - ((b : ℝ) : ℂ)‖ = |a - b| := by
  have hsq : Complex.normSq (((a : ℝ) : ℂ) - ((b : ℝ) : ℂ)) = (a - b) ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [Complex.norm_def, hsq, Real.sqrt_sq_eq_abs]

/-- Norm of `b * I` for a real `b`. -/
lemma norm_ofReal_mul_I (b : ℝ) : ‖((b : ℝ) : ℂ) * Complex.I‖ = |b| := by simp

/-- A sequence of reals whose successive differences are bounded by a geometric sequence
converges: the increments form an absolutely summable series, so the partial sums converge. -/
lemma tendsto_of_geometric_step {x : ℕ → ℝ} {c r : ℝ} (_hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ n : ℕ, |x (n + 1) - x n| ≤ c * r ^ n) :
    ∃ ξ : ℝ, Tendsto x atTop (nhds ξ) := by
  have hsum : Summable fun n : ℕ => c * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left c
  have hstep : Summable fun n : ℕ => x (n + 1) - x n :=
    Summable.of_norm_bounded hsum (fun n => by rw [Real.norm_eq_abs]; exact h n)
  refine ⟨x 0 + ∑' n : ℕ, (x (n + 1) - x n), ?_⟩
  have htel : ∀ n : ℕ, x n = x 0 + ∑ k ∈ Finset.range n, (x (k + 1) - x k) := by
    intro n
    rw [Finset.sum_range_sub]
    ring
  have hlim := hstep.hasSum.tendsto_sum_nat.const_add (x 0)
  have hfun : (fun n : ℕ => x 0 + ∑ k ∈ Finset.range n, (x (k + 1) - x k)) = x := by
    funext n; exact (htel n).symm
  rw [hfun] at hlim
  exact hlim

/-- Every orbit of a `LocalModel` starting in the ball `‖P - A‖ ≤ ε` converges to a point `Q` of
the real axis (`Q.im = 0`) with `‖Q - A‖ ≤ 2 * ε`.

By `Work.EQ.dynTrap` (`Submission/Work/EQ/LocalModelAux.lean`) the coordinates
`ξ_n = dynXi A ((T^[n]) P)`, `η_n = dynEta A ((T^[n]) P)` satisfy `|ξ_n| + |η_n| ≤ 2 ε` and
`|η_n| ≤ ((1+lam)/2)^n ε`; by `Work.EQ.dynStep` one has `ξ_{n+1} = ξ_n + F ξ_n η_n` with
`|F ξ_n η_n| ≤ C η_n^2`, so `ξ_n` is the sequence of partial sums of an absolutely summable
series and converges to some `ξ` with `|ξ| ≤ 2 ε`; then `T^[n] P → A + ξ`, a real point at
distance `≤ 2 ε` from `A`. -/
theorem localModel_limit {T : ℂ → ℂ} {A : ℂ} {lam C ε : ℝ} (h : LocalModel T A lam C ε) :
    ∀ P : ℂ, ‖P - A‖ ≤ ε → ∃ Q : ℂ, Q.im = 0 ∧ ‖Q - A‖ ≤ 2 * ε ∧
      Filter.Tendsto (fun n : ℕ => (T^[n]) P) Filter.atTop (nhds Q) := by
  intro P hP
  obtain ⟨htrap, -, htrap3⟩ := dynTrap h P hP
  obtain ⟨hA, hε0, hC0, hlam0, hlam1, _hCε, _haxis, F, _G, hrep, hFb, _hGb, _hFl, _hGl⟩ := h
  -- bounds along the orbit
  have hξb : ∀ n : ℕ, |dynXi A ((T^[n]) P)| ≤ 2 * ε := fun n =>
    (le_add_of_nonneg_right (abs_nonneg _)).trans (htrap n)
  have hηb : ∀ n : ℕ, |dynEta A ((T^[n]) P)| ≤ ((1 + lam) / 2) ^ n * ε := fun n => htrap3 n
  have h4x : ∀ n : ℕ, |dynXi A ((T^[n]) P)| ≤ 4 * ε := by
    intro n; have h1 := hξb n; linarith
  have h4y : ∀ n : ℕ, |dynEta A ((T^[n]) P)| ≤ 4 * ε := by
    intro n
    have h1 := htrap n
    linarith [abs_nonneg (dynXi A ((T^[n]) P)), hε0]
  -- one step of the recursion for the horizontal coordinate
  have stepξ : ∀ n : ℕ, dynXi A ((T^[n + 1]) P) =
      dynXi A ((T^[n]) P) + F (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P)) := by
    intro n
    have hs := (dynStep hrep (h4x n) (h4y n)).1
    rw [Function.iterate_succ_apply']
    exact hs
  -- geometric bound on the increments of the horizontal coordinate
  have hf : ∀ k : ℕ, |dynXi A ((T^[k + 1]) P) - dynXi A ((T^[k]) P)| ≤
      (C * ε ^ 2) * (((1 + lam) / 2) ^ 2) ^ k := by
    intro k
    have hF := hFb _ _ (h4x k) (h4y k)
    rw [stepξ k, add_sub_cancel_left]
    calc |F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P))|
        ≤ C * (dynEta A ((T^[k]) P)) ^ 2 := hF
      _ = C * |dynEta A ((T^[k]) P)| ^ 2 := by rw [sq_abs]
      _ ≤ C * (((1 + lam) / 2) ^ k * ε) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC0)
          exact pow_le_pow_left₀ (abs_nonneg _) (hηb k) 2
      _ = (C * ε ^ 2) * (((1 + lam) / 2) ^ 2) ^ k := by
          rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm k 2]; ring
  -- hence the horizontal coordinate converges
  have hr0 : 0 ≤ ((1 + lam) / 2) ^ 2 := sq_nonneg _
  have hr1 : ((1 + lam) / 2) ^ 2 < 1 := by nlinarith [hlam0, hlam1]
  have hc0 : 0 ≤ C * ε ^ 2 := by positivity
  obtain ⟨ξ, hξ⟩ := tendsto_of_geometric_step (x := fun n : ℕ => dynXi A ((T^[n]) P))
    (c := C * ε ^ 2) (r := ((1 + lam) / 2) ^ 2) hc0 hr0 hr1 hf
  have hξ2 : |ξ| ≤ 2 * ε := le_of_tendsto' hξ.abs hξb
  -- the vertical coordinate tends to `0`
  have hη0 : Tendsto (fun n : ℕ => dynEta A ((T^[n]) P)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdec : Tendsto (fun n : ℕ => ((1 + lam) / 2) ^ n * ε) atTop (nhds 0) := by
      have hpow : Tendsto (fun n : ℕ => ((1 + lam) / 2) ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
      simpa using hpow.mul_const ε
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact hηb n) hdec
  -- the orbit converges to the real point `A + ξ`
  refine ⟨A + ((ξ : ℝ) : ℂ), ?_, ?_, ?_⟩
  · simp [hA]
  · rw [add_sub_cancel_left]
    simpa using hξ2
  · have hd : ∀ n : ℕ, (T^[n]) P - (A + ((ξ : ℝ) : ℂ)) =
        (((dynXi A ((T^[n]) P) : ℝ)) : ℂ) - ((ξ : ℝ) : ℂ) +
          (((dynEta A ((T^[n]) P) : ℝ)) : ℂ) * Complex.I := by
      intro n
      have hpt : (T^[n]) P - A = ((dynXi A ((T^[n]) P) : ℝ) : ℂ) +
          ((dynEta A ((T^[n]) P) : ℝ) : ℂ) * Complex.I := by
        have h1 : (T^[n]) P - A = (A + ((dynXi A ((T^[n]) P) : ℝ) : ℂ) +
            ((dynEta A ((T^[n]) P) : ℝ) : ℂ) * Complex.I) - A :=
          congrArg (fun z : ℂ => z - A) (dyn_point_eq A ((T^[n]) P)).symm
        rw [h1]; ring
      rw [show (T^[n]) P - (A + ((ξ : ℝ) : ℂ)) = ((T^[n]) P - A) - ((ξ : ℝ) : ℂ)
            from by ring, hpt]
      ring
    have hb : ∀ n : ℕ, ‖(T^[n]) P - (A + ((ξ : ℝ) : ℂ))‖ ≤
        |dynXi A ((T^[n]) P) - ξ| + |dynEta A ((T^[n]) P)| := by
      intro n
      rw [hd n]
      calc ‖(((dynXi A ((T^[n]) P) : ℝ)) : ℂ) - ((ξ : ℝ) : ℂ) +
              (((dynEta A ((T^[n]) P) : ℝ)) : ℂ) * Complex.I‖
          ≤ ‖(((dynXi A ((T^[n]) P) : ℝ)) : ℂ) - ((ξ : ℝ) : ℂ)‖ +
            ‖(((dynEta A ((T^[n]) P) : ℝ)) : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |dynXi A ((T^[n]) P) - ξ| + |dynEta A ((T^[n]) P)| := by
            rw [norm_ofReal_sub, norm_ofReal_mul_I]
    have hd0 : Tendsto (fun n : ℕ =>
        |dynXi A ((T^[n]) P) - ξ| + |dynEta A ((T^[n]) P)|) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => dynXi A ((T^[n]) P) - ξ) atTop (nhds 0) := by
        simpa using hξ.sub_const ξ
      have h2 : Tendsto (fun n : ℕ => |dynXi A ((T^[n]) P) - ξ|) atTop (nhds 0) := by
        simpa using h1.abs
      have h3 : Tendsto (fun n : ℕ => |dynEta A ((T^[n]) P)|) atTop (nhds 0) := by
        simpa using hη0.abs
      simpa using h2.add h3
    exact tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg _) hb hd0)

end Work.EQ
