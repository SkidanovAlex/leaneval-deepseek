import Mathlib
import Submission.Work.WilG5.Count.dominate

set_option maxHeartbeats 4000000

namespace Work.WilkiesH.Count

/-- For every real `t` one has `|t| ≤ t^2 + 1`, so `t ↦ t^2 + 1` dominates `|·|` on `ℝ`. -/
lemma abs_le_sq_add_one (t : ℝ) : |t| ≤ t ^ 2 + 1 := by
  nlinarith [sq_abs t, sq_nonneg (|t| - 1 / 2), abs_nonneg t]

/-- A `ℕ`-valued polynomial in two variables, evaluated at a pair of naturals `n1, n2` which
are both bounded by a real number `T ≥ 1`, is at most `K * T^d`. -/
theorem nat_two_var_eval_le_aux (b : MvPolynomial (Fin 2) ℕ) :
    ∃ K d : ℕ, ∀ (n1 n2 : ℕ) (T : ℝ), 1 ≤ T → (n1 : ℝ) ≤ T → (n2 : ℝ) ≤ T →
      (MvPolynomial.eval ![n1, n2] b : ℝ) ≤ (K : ℝ) * T ^ d := by
  classical
  refine ⟨∑ s ∈ b.support, b.coeff s, b.totalDegree, fun n1 n2 T hT h1 h2 => ?_⟩
  have heval : (MvPolynomial.eval ![n1, n2] b : ℝ)
      = ∑ s ∈ b.support, (b.coeff s : ℝ) * (n1 : ℝ) ^ (s 0) * (n2 : ℝ) ^ (s 1) := by
    rw [MvPolynomial.eval_eq']
    push_cast
    refine Finset.sum_congr rfl ?_
    intro s hs
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ] <;> ring
  rw [heval]
  have hK : ((∑ s ∈ b.support, b.coeff s : ℕ) : ℝ) = ∑ s ∈ b.support, (b.coeff s : ℝ) := by
    simp only [Nat.cast_sum]
  rw [hK, Finset.sum_mul]
  refine Finset.sum_le_sum (fun s hs => ?_)
  have hsdeg : s 0 + s 1 ≤ b.totalDegree := by
    have h := MvPolynomial.le_totalDegree (R := ℕ) hs
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using h
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have hpow1 : (n1 : ℝ) ^ (s 0) ≤ T ^ (s 0) := pow_le_pow_left₀ (Nat.cast_nonneg n1) h1 (s 0)
  have hpow2 : (n2 : ℝ) ^ (s 1) ≤ T ^ (s 1) := pow_le_pow_left₀ (Nat.cast_nonneg n2) h2 (s 1)
  have hmul : (n1 : ℝ) ^ (s 0) * (n2 : ℝ) ^ (s 1) ≤ T ^ (s 0 + s 1) := by
    rw [pow_add]
    exact mul_le_mul hpow1 hpow2 (pow_nonneg (Nat.cast_nonneg n2) _) (pow_nonneg hT0 _)
  have hmono : T ^ (s 0 + s 1) ≤ T ^ b.totalDegree := pow_le_pow_right₀ hT hsdeg
  calc (b.coeff s : ℝ) * (n1 : ℝ) ^ (s 0) * (n2 : ℝ) ^ (s 1)
      = (b.coeff s : ℝ) * ((n1 : ℝ) ^ (s 0) * (n2 : ℝ) ^ (s 1)) := by ring
    _ ≤ (b.coeff s : ℝ) * T ^ (s 0 + s 1) := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg _)
    _ ≤ (b.coeff s : ℝ) * T ^ b.totalDegree := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)

/-- A `ℕ`-valued univariate polynomial evaluated at a natural `n ≤ T` (with `T ≥ 1`) is at
most `K * T^d`. -/
theorem nat_poly_eval_le_real_aux (c : Polynomial ℕ) :
    ∃ K d : ℕ, ∀ (n : ℕ) (T : ℝ), 1 ≤ T → (n : ℝ) ≤ T →
      ((Polynomial.eval n c : ℕ) : ℝ) ≤ (K : ℝ) * T ^ d := by
  classical
  refine ⟨∑ k ∈ Finset.range (c.natDegree + 1), c.coeff k, c.natDegree, fun n T hT hn => ?_⟩
  have h1 : ((Polynomial.eval n c : ℕ) : ℝ)
      = ∑ k ∈ Finset.range (c.natDegree + 1), (c.coeff k : ℝ) * (n : ℝ) ^ k := by
    rw [Polynomial.eval_eq_sum_range]
    push_cast
    refine Finset.sum_congr rfl (fun k hk => ?_)
    ring
  have hK : ((∑ k ∈ Finset.range (c.natDegree + 1), c.coeff k : ℕ) : ℝ)
      = ∑ k ∈ Finset.range (c.natDegree + 1), (c.coeff k : ℝ) := by
    simp only [Nat.cast_sum]
  rw [h1, hK, Finset.sum_mul]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hk' : k ≤ c.natDegree := by
    have := Finset.mem_range.mp hk
    omega
  have hnk : (n : ℝ) ^ k ≤ T ^ k := pow_le_pow_left₀ (Nat.cast_nonneg n) hn k
  have hkd : T ^ k ≤ T ^ c.natDegree := pow_le_pow_right₀ hT hk'
  exact mul_le_mul_of_nonneg_left (le_trans hnk hkd) (Nat.cast_nonneg _)

/-- Polynomial bookkeeping for the counting induction, with the `max 0` that the summation
needs: if `mv ≤ p(D,g,log H)` and `d ≤ q(D,g,log H)`, then
`mv · pm(D+d, n+1) · max 0 (f(c(D+d), g, log H))` is bounded by a polynomial `F` in
`(D,g,log H)` alone.  (`F` may be taken with nonnegative coefficients, since all the bounds
producing it are nonnegative outside of `f`; the `max 0` handles the sign of `f.eval`.)

This is the `poly_bookkeeping_max` obligation with the fixed second coordinate `n+1` in place
of `m+1`; see `Submission/Work/WilkiesH/Count/scratch/pbmax_body.lean` for a proof body of the
analogous statement, and `Work.WilG5.Count.dominate` / `Work.WilG5.PolyEval.poly_abs_bound`
for the instruments. -/
theorem poly_bookkeeping_strat_max {n : ℕ} (pm : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ)
    (p q f : MvPolynomial (Fin 3) ℝ) :
    ∃ F : MvPolynomial (Fin 3) ℝ, ∀ D g H mv d : ℕ,
      (mv : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p →
      (d : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q →
      (mv : ℝ) * (MvPolynomial.eval ![(D + d : ℕ), (n + 1 : ℕ)] pm : ℕ) *
        max 0 (MvPolynomial.eval ![((c.eval (D + d) : ℕ) : ℝ), (g : ℝ), Real.log H] f) ≤
        MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] F := by
  obtain ⟨Kb, db, hb⟩ := nat_two_var_eval_le_aux pm
  obtain ⟨Kc, dc, hc⟩ := nat_poly_eval_le_real_aux c
  obtain ⟨Cf, Nf, hCf, hf⟩ := Work.WilG5.PolyEval.poly_abs_bound f
  -- The dominating polynomial `T`, in `(D, g, log H)`, that exceeds `D`, `g`, `log H`, `n+1`,
  -- the two bounds `p.eval`, `q.eval` supplied by the hypotheses, and `1`.
  let W : MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.C ((n + 1 : ℕ) : ℝ) + MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2
  let T : MvPolynomial (Fin 3) ℝ :=
    W + (p * p + MvPolynomial.C 1) + (q * q + MvPolynomial.C 1)
  refine ⟨MvPolynomial.C (Kb : ℝ) * T ^ (db + 1) *
      (MvPolynomial.C Cf * (MvPolynomial.C 1 + MvPolynomial.C (Kc : ℝ) * T ^ dc +
        MvPolynomial.C 2 * T) ^ Nf), ?_⟩
  intro D g H mv d hm hd
  let beta : ℝ := ((MvPolynomial.eval ![(D + d : ℕ), (n + 1 : ℕ)] pm : ℕ) : ℝ)
  let gam : ℝ := ((c.eval (D + d) : ℕ) : ℝ)
  let Tv : ℝ := MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] T
  have hbetadef : beta = ((MvPolynomial.eval ![(D + d : ℕ), (n + 1 : ℕ)] pm : ℕ) : ℝ) := rfl
  have hgamdef : gam = ((c.eval (D + d) : ℕ) : ℝ) := rfl
  have hTvdef : Tv = MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] T := rfl
  have hWdef : W = MvPolynomial.C ((n + 1 : ℕ) : ℝ) + MvPolynomial.X 0 + MvPolynomial.X 1 +
      MvPolynomial.X 2 := rfl
  have hTdef : T = W + (p * p + MvPolynomial.C 1) + (q * q + MvPolynomial.C 1) := rfl
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg g
  have hL0 : (0 : ℝ) ≤ Real.log H := Real.log_natCast_nonneg H
  have hA0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hWx : MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] W
      = ((n + 1 : ℕ) : ℝ) + (D : ℝ) + (g : ℝ) + Real.log H := by
    simp only [hWdef, MvPolynomial.eval_add, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Matrix.cons_val, Fin.isValue] <;> ring
  have hTx : MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] T
      = MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] W
        + (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p
            * MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p + 1)
        + (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q
            * MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q + 1) := by
    simp only [hTdef, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C] <;> ring
  have hTvval : Tv = ((n + 1 : ℕ) : ℝ) + (D : ℝ) + (g : ℝ) + Real.log H
      + (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p
          * MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p + 1)
      + (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q
          * MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q + 1) := by
    rw [hTvdef, hTx, hWx] <;> ring
  have hTv1 : 1 ≤ Tv := by
    rw [hTvval]
    nlinarith [hA1, hD0, hg0, hL0,
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p),
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q)]
  have hTv0 : (0 : ℝ) ≤ Tv := le_trans zero_le_one hTv1
  have hTvD : (D : ℝ) ≤ Tv := by
    rw [hTvval]
    nlinarith [hA0, hg0, hL0,
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p),
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q)]
  have hTvg : (g : ℝ) ≤ Tv := by
    rw [hTvval]
    nlinarith [hA0, hD0, hL0,
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p),
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q)]
  have hTvL : Real.log H ≤ Tv := by
    rw [hTvval]
    nlinarith [hA0, hD0, hg0,
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p),
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q)]
  have hTvp : MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p ≤ Tv := by
    have hp1 : MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p
        ≤ |MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p| := le_abs_self _
    have hp2 : |MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p|
        ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p ^ 2 + 1 := abs_le_sq_add_one _
    rw [hTvval]
    nlinarith [hp1, hp2, hA0, hD0, hg0, hL0,
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q)]
  have hTvq : MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q ≤ Tv := by
    have hq1 : MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q
        ≤ |MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q| := le_abs_self _
    have hq2 : |MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q|
        ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q ^ 2 + 1 := abs_le_sq_add_one _
    rw [hTvval]
    nlinarith [hq1, hq2, hA0, hD0, hg0, hL0,
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p)]
  have hTvA : ((n + 1 : ℕ) : ℝ) ≤ Tv := by
    rw [hTvval]
    nlinarith [hD0, hg0, hL0,
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p),
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q)]
  have hDQ : (D : ℝ) + MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q ≤ Tv := by
    have hq1 : MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q
        ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q ^ 2 + 1 :=
      le_trans (le_abs_self _) (abs_le_sq_add_one _)
    rw [hTvval]
    nlinarith [hq1, hA0, hg0, hL0,
      sq_nonneg (MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p)]
  have hTvdd : ((D + d : ℕ) : ℝ) ≤ Tv := by
    have hcast : ((D + d : ℕ) : ℝ) = (D : ℝ) + (d : ℝ) := by push_cast; ring
    rw [hcast]
    linarith [hd, hDQ]
  have hbetab : beta ≤ (Kb : ℝ) * Tv ^ db := by
    rw [hbetadef]
    exact hb (D + d) (n + 1) Tv hTv1 hTvdd hTvA
  have hgamc : gam ≤ (Kc : ℝ) * Tv ^ dc := by
    rw [hgamdef]
    exact hc (D + d) Tv hTv1 hTvdd
  have hbet0 : (0 : ℝ) ≤ beta := by rw [hbetadef]; exact Nat.cast_nonneg _
  have hgam0 : (0 : ℝ) ≤ gam := by rw [hgamdef]; exact Nat.cast_nonneg _
  have hy : ∑ i, |(![gam, (g : ℝ), Real.log H] : Fin 3 → ℝ) i|
      = gam + (g : ℝ) + Real.log H := by
    have hy0 : (![gam, (g : ℝ), Real.log H] : Fin 3 → ℝ) 0 = gam := rfl
    have hy1 : (![gam, (g : ℝ), Real.log H] : Fin 3 → ℝ) 1 = (g : ℝ) := rfl
    have hy2 : (![gam, (g : ℝ), Real.log H] : Fin 3 → ℝ) 2 = Real.log H := rfl
    rw [Fin.sum_univ_three, hy0, hy1, hy2, abs_of_nonneg hgam0, abs_of_nonneg hg0,
      abs_of_nonneg hL0]
  have hfe : |MvPolynomial.eval ![gam, (g : ℝ), Real.log H] f|
      ≤ Cf * (1 + gam + (g : ℝ) + Real.log H) ^ Nf := by
    have h := hf ![gam, (g : ℝ), Real.log H]
    rw [hy] at h
    simpa only [add_assoc, add_left_comm, add_comm] using h
  have hbase : 1 + gam + (g : ℝ) + Real.log H ≤ 1 + (Kc : ℝ) * Tv ^ dc + 2 * Tv := by
    linarith [hgamc, hTvg, hTvL]
  have hbase0 : (0 : ℝ) ≤ 1 + gam + (g : ℝ) + Real.log H := by linarith [hgam0, hg0, hL0]
  have hpow : (1 + gam + (g : ℝ) + Real.log H) ^ Nf
      ≤ (1 + (Kc : ℝ) * Tv ^ dc + 2 * Tv) ^ Nf :=
    pow_le_pow_left₀ hbase0 hbase Nf
  have hfe2 : |MvPolynomial.eval ![gam, (g : ℝ), Real.log H] f|
      ≤ Cf * (1 + (Kc : ℝ) * Tv ^ dc + 2 * Tv) ^ Nf :=
    le_trans hfe (mul_le_mul_of_nonneg_left hpow hCf)
  have hCpos : (0 : ℝ) ≤ Cf * (1 + (Kc : ℝ) * Tv ^ dc + 2 * Tv) ^ Nf := by
    have ha : (0 : ℝ) ≤ (Kc : ℝ) * Tv ^ dc :=
      mul_nonneg (Nat.cast_nonneg Kc) (pow_nonneg hTv0 dc)
    have hb0 : (0 : ℝ) ≤ 2 * Tv := by linarith
    have h2 : (0 : ℝ) ≤ 1 + (Kc : ℝ) * Tv ^ dc + 2 * Tv := by linarith
    exact mul_nonneg hCf (pow_nonneg h2 Nf)
  have hmax : max 0 (MvPolynomial.eval ![gam, (g : ℝ), Real.log H] f)
      ≤ Cf * (1 + (Kc : ℝ) * Tv ^ dc + 2 * Tv) ^ Nf :=
    max_le hCpos (le_trans (le_abs_self _) hfe2)
  have hmvb : (mv : ℝ) ≤ Tv := le_trans hm hTvp
  have hstep1 : (mv : ℝ) * beta ≤ Tv * ((Kb : ℝ) * Tv ^ db) :=
    mul_le_mul hmvb hbetab hbet0 hTv0
  have hKbTv : (0 : ℝ) ≤ (Kb : ℝ) * Tv ^ db :=
    mul_nonneg (Nat.cast_nonneg Kb) (pow_nonneg hTv0 db)
  have hstep2 : (mv : ℝ) * beta * max 0 (MvPolynomial.eval ![gam, (g : ℝ), Real.log H] f)
      ≤ Tv * ((Kb : ℝ) * Tv ^ db) * (Cf * (1 + (Kc : ℝ) * Tv ^ dc + 2 * Tv) ^ Nf) :=
    mul_le_mul hstep1 hmax (le_max_left _ _) (mul_nonneg hTv0 hKbTv)
  have hEq : Tv * ((Kb : ℝ) * Tv ^ db) * (Cf * (1 + (Kc : ℝ) * Tv ^ dc + 2 * Tv) ^ Nf)
      = (Kb : ℝ) * Tv ^ (db + 1) * (Cf * (1 + (Kc : ℝ) * Tv ^ dc + 2 * Tv) ^ Nf) := by
    rw [pow_succ]; ring
  have hFval : MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H]
      (MvPolynomial.C (Kb : ℝ) * T ^ (db + 1) *
        (MvPolynomial.C Cf * (MvPolynomial.C 1 + MvPolynomial.C (Kc : ℝ) * T ^ dc +
          MvPolynomial.C 2 * T) ^ Nf))
      = (Kb : ℝ) * Tv ^ (db + 1) * (Cf * (1 + (Kc : ℝ) * Tv ^ dc + 2 * Tv) ^ Nf) := by
    rw [hTvdef]
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_add, MvPolynomial.eval_pow,
      MvPolynomial.eval_C] <;> ring
  rw [hFval, ← hEq]
  exact hstep2

end Work.WilkiesH.Count
