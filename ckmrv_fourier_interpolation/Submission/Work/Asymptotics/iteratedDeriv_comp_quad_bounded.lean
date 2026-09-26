/-
# Growth bound on the iterated derivatives of `s ↦ J(π s²)`

Let `J : ℝ → ℂ` be smooth and suppose that, for every order `j`, the `j`-th derivative of `J`
is dominated by `C * (1 + |x|)^d * exp(-x)`.  Let `g(s) = J(π s²)` be the composition of `J`
with the quadratic map `s ↦ π s²`.  This file proves that for every `k` and `l` the function
`r ↦ |r|^k ‖g^{(l)}(r)‖` is bounded on `ℝ`.

The two ingredients are

* the *ascending chain representation* `exists_chain_repr`: the `l`-th derivative of `g` is a
  finite combination `∑ i, c i * x^{m i} * J^{(j i)}(π x²)` with `m i ≤ l` and `j i ≤ l`,
  obtained by induction from the product/chain rule (this is the special case of Faà di Bruno
  for the quadratic inner function, where only the powers `2j - l` occur);
* an elementary Gaussian bound: `(1+|x|)^A (1+π x²)^d exp(-π x²)` is bounded on `ℝ`.

Combining them, `|r|^k ‖g^{(l)}(r)‖ ≤ ∑ i ‖c i‖ C_i sup_x (1+|x|)^{k+l} (1+π x²)^d e^{-π x²}`.
-/
import Mathlib
import Submission.Work.Asymptotics.abs_pow_mul_exp_le

namespace Work.Asymptotics

noncomputable section

open scoped BigOperators

/-! ## Auxiliary calculus lemmas -/

/-- The derivative of `s ↦ J^{(j)}(π s²)`, obtained from `iteratedDeriv_succ` and the chain
rule for `ℝ → ℝ → ℂ` (`HasDerivAt.scomp`). -/
lemma hasDerivAt_iteratedDeriv_comp_quad (J : ℝ → ℂ) (hJ : ContDiff ℝ ⊤ J) (j : ℕ) (x : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedDeriv j J (Real.pi * s^2))
      (((2 * Real.pi * x : ℝ) : ℂ) * iteratedDeriv (j+1) J (Real.pi * x^2)) x := by
  have hd : Differentiable ℝ (iteratedDeriv j J) := hJ.differentiable_iteratedDeriv j (by simp)
  have hg : HasDerivAt (iteratedDeriv j J) (iteratedDeriv (j+1) J (Real.pi * x^2)) (Real.pi * x^2) := by
    rw [iteratedDeriv_succ]
    exact (hd (Real.pi * x^2)).hasDerivAt
  have hh : HasDerivAt (fun s : ℝ => Real.pi * s^2) (2 * Real.pi * x) x := by
    have h := (hasDerivAt_pow 2 x).const_mul Real.pi
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using h
  have h3 := hg.scomp x hh
  simpa [Function.comp_def] using h3

/-- The derivative of one term `s ↦ c s^m J^{(j)}(π s²)` of the chain representation. -/
lemma hasDerivAt_chain_term (J : ℝ → ℂ) (hJ : ContDiff ℝ ⊤ J) (c : ℂ) (m j : ℕ) (x : ℝ) :
    HasDerivAt (fun s : ℝ => c * (s:ℂ)^m * iteratedDeriv j J (Real.pi * s^2))
      ((c * (m:ℂ)) * (x:ℂ)^(m-1) * iteratedDeriv j J (Real.pi * x^2)
        + (c * ((2*Real.pi:ℝ):ℂ)) * (x:ℂ)^(m+1) * iteratedDeriv (j+1) J (Real.pi * x^2)) x := by
  have hp : HasDerivAt (fun s : ℝ => (s:ℂ)^m) ((m:ℂ) * (x:ℂ)^(m-1)) x := by
    have ha : HasDerivAt (fun y : ℝ => (y:ℂ)) (1:ℂ) x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have hb : HasDerivAt (fun z : ℂ => z^m) ((m:ℂ) * (x:ℂ)^(m-1)) (x:ℂ) := hasDerivAt_pow m (x:ℂ)
    have h := hb.comp x ha
    simpa [Function.comp_def] using h
  have hA : HasDerivAt (fun s : ℝ => c * (s:ℂ)^m) (c * ((m:ℂ) * (x:ℂ)^(m-1))) x := hp.const_mul c
  have hB := hasDerivAt_iteratedDeriv_comp_quad J hJ j x
  have hmul := hA.mul hB
  have hval : c * ((m:ℂ) * (x:ℂ)^(m-1)) * iteratedDeriv j J (Real.pi * x^2)
      + c * (x:ℂ)^m * (((2*Real.pi*x:ℝ):ℂ) * iteratedDeriv (j+1) J (Real.pi * x^2))
      = (c * (m:ℂ)) * (x:ℂ)^(m-1) * iteratedDeriv j J (Real.pi * x^2)
        + (c * ((2*Real.pi:ℝ):ℂ)) * (x:ℂ)^(m+1) * iteratedDeriv (j+1) J (Real.pi * x^2) := by
    have hc1 : ((2*Real.pi*x:ℝ):ℂ) = ((2*Real.pi:ℝ):ℂ) * (x:ℂ) := by push_cast; ring
    rw [hc1, pow_succ]
    ring
  rw [hval] at hmul
  exact hmul

/-! ## The ascending chain representation -/

/-- **Chain representation.**  For every order `l` the `l`-th derivative of `s ↦ J(π s²)` is a
finite combination of terms `c * x^m * J^{(j)}(π x²)` with `m ≤ l` and `j ≤ l`.  This is the
special form of Faà di Bruno's formula for the quadratic inner function; the exponents are
`m = 2j - l`.  Tracing the two summands produced by the product and chain rule, the induction
step replaces each term `(c, m, j)` by `(c * m, m - 1, j)` and `(c * 2π, m + 1, j + 1)`. -/
lemma exists_chain_repr (J : ℝ → ℂ) (hJ : ContDiff ℝ ⊤ J) (l : ℕ) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (m j : Fin n → ℕ),
      (∀ i, m i ≤ l) ∧ (∀ i, j i ≤ l) ∧
      ∀ x : ℝ, iteratedDeriv l (fun s : ℝ => J (Real.pi * s^2)) x
        = ∑ i : Fin n, c i * (x:ℂ)^(m i) * iteratedDeriv (j i) J (Real.pi * x^2) := by
  induction l with
  | zero =>
    refine ⟨1, fun _ => 1, fun _ => 0, fun _ => 0, fun i => Nat.zero_le _, fun i => Nat.zero_le _, ?_⟩
    intro x
    rw [iteratedDeriv_zero]
    simp
  | succ l ih =>
    obtain ⟨n, c, m, j, hmle, hjle, hrepr⟩ := ih
    let e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
    let c' : Fin (n + n) → ℂ := fun i =>
      Sum.elim (fun a : Fin n => c a * (m a : ℂ)) (fun b : Fin n => c b * ((2 * Real.pi : ℝ) : ℂ)) (e.symm i)
    let m' : Fin (n + n) → ℕ := fun i =>
      Sum.elim (fun a : Fin n => m a - 1) (fun b : Fin n => m b + 1) (e.symm i)
    let j' : Fin (n + n) → ℕ := fun i =>
      Sum.elim (fun a : Fin n => j a) (fun b : Fin n => j b + 1) (e.symm i)
    refine ⟨n + n, c', m', j', ?_, ?_, ?_⟩
    · intro i
      dsimp only [m']
      cases h : e.symm i with
      | inl a => rw [Sum.elim_inl]; have := hmle a; omega
      | inr b => rw [Sum.elim_inr]; have := hmle b; omega
    · intro i
      dsimp only [j']
      cases h : e.symm i with
      | inl a => rw [Sum.elim_inl]; have := hjle a; omega
      | inr b => rw [Sum.elim_inr]; have := hjle b; omega
    · intro x
      have hfun : iteratedDeriv (l+1) (fun s : ℝ => J (Real.pi * s ^ 2)) x
          = deriv (fun y : ℝ => ∑ i : Fin n, c i * (y:ℂ)^(m i) * iteratedDeriv (j i) J (Real.pi * y^2)) x := by
        rw [iteratedDeriv_succ]
        have hh : iteratedDeriv l (fun s : ℝ => J (Real.pi * s ^ 2))
            = fun y : ℝ => ∑ i : Fin n, c i * (y:ℂ)^(m i) * iteratedDeriv (j i) J (Real.pi * y^2) :=
          funext hrepr
        rw [hh]
      rw [hfun]
      have hsum : HasDerivAt (fun y : ℝ => ∑ i : Fin n, c i * (y:ℂ)^(m i) * iteratedDeriv (j i) J (Real.pi * y^2))
          (∑ i : Fin n, ((c i * (m i : ℂ)) * (x:ℂ)^(m i - 1) * iteratedDeriv (j i) J (Real.pi * x^2)
            + (c i * ((2 * Real.pi : ℝ) : ℂ)) * (x:ℂ)^(m i + 1) * iteratedDeriv (j i + 1) J (Real.pi * x^2))) x := by
        have heqfun : (∑ i : Fin n, (fun y : ℝ => c i * (y:ℂ)^(m i) * iteratedDeriv (j i) J (Real.pi * y^2)))
            = (fun y : ℝ => ∑ i : Fin n, c i * (y:ℂ)^(m i) * iteratedDeriv (j i) J (Real.pi * y^2)) := by
          funext y; rw [Finset.sum_apply]
        have key := HasDerivAt.sum (u := Finset.univ)
          (fun i (_ : i ∈ Finset.univ) => hasDerivAt_chain_term J hJ (c i) (m i) (j i) x)
        rw [heqfun] at key
        exact key
      rw [hsum.deriv]
      rw [Finset.sum_add_distrib]
      have hR : (∑ i : Fin (n + n), c' i * (x:ℂ)^(m' i) * iteratedDeriv (j' i) J (Real.pi * x^2))
          = (∑ a : Fin n, (c a * (m a : ℂ)) * (x:ℂ)^(m a - 1) * iteratedDeriv (j a) J (Real.pi * x^2))
            + (∑ b : Fin n, (c b * ((2 * Real.pi : ℝ) : ℂ)) * (x:ℂ)^(m b + 1) * iteratedDeriv (j b + 1) J (Real.pi * x^2)) := by
        rw [← Equiv.sum_comp e (fun i => c' i * (x:ℂ)^(m' i) * iteratedDeriv (j' i) J (Real.pi * x^2))]
        rw [Fintype.sum_sum_type]
        congr 1
        · refine Finset.sum_congr rfl (fun a _ => ?_)
          simp only [c', m', j', Equiv.symm_apply_apply, Sum.elim_inl]
        · refine Finset.sum_congr rfl (fun b _ => ?_)
          simp only [c', m', j', Equiv.symm_apply_apply, Sum.elim_inr]
      rw [hR]

/-! ## The elementary Gaussian bound -/

/-- `(1+|x|)^M e^{-π x²}` is bounded on `ℝ`: it is continuous and decays at infinity.  The
explicit constant `2^M (1 + K)` with `K = (M/(2πe))^{M/2}` is derived from the single-variable
maximum bound `abs_pow_mul_exp_le`. -/
private lemma one_add_abs_pow_mul_exp_neg_pi_sq_le (M : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, (1 + |x|)^M * Real.exp (-(Real.pi * x^2)) ≤ B := by
  set K : ℝ := ((M : ℝ) / (2 * Real.pi * Real.exp 1)) ^ ((M : ℝ) / 2) with hKdef
  have hKnn : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  refine ⟨2^M * (1 + K), by positivity, fun x => ?_⟩
  by_cases hle : |x| ≤ 1
  · have h1 : (1 + |x|)^M ≤ 2^M := pow_le_pow_left₀ (by positivity) (by linarith) M
    have h2 : Real.exp (-(Real.pi * x^2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [Real.pi_pos, sq_nonneg x]
    calc (1 + |x|)^M * Real.exp (-(Real.pi * x^2)) ≤ 2^M * 1 :=
          mul_le_mul h1 h2 (Real.exp_nonneg _) (by positivity)
      _ ≤ 2^M * (1 + K) := by
          apply mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ 1 + K) (by positivity)
  · have hle' : 1 < |x| := not_le.mp hle
    have h1 : (1 + |x|)^M ≤ (2 * |x|)^M := pow_le_pow_left₀ (by positivity) (by linarith) M
    have h2 : (2 * |x|)^M = 2^M * |x|^M := mul_pow 2 |x| M
    have h3 : |x|^M * Real.exp (-(Real.pi * x^2)) ≤ K := by
      have h := abs_pow_mul_exp_le M (by norm_num : (0:ℝ) < 1) x
      simpa [hKdef] using h
    calc (1 + |x|)^M * Real.exp (-(Real.pi * x^2))
        ≤ (2 * |x|)^M * Real.exp (-(Real.pi * x^2)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = 2^M * (|x|^M * Real.exp (-(Real.pi * x^2))) := by rw [h2]; ring
      _ ≤ 2^M * K := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 2^M * (1 + K) := by
          apply mul_le_mul_of_nonneg_left (by linarith : K ≤ 1 + K) (by positivity)

/-- The weighted Gaussian bound actually used below: the extra factor `(1+π x²)^d` is absorbed
into `(1+π)^d (1+|x|)^{2d}`. -/
private lemma weight_bounded (A d : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ,
      (1 + |x|)^A * (1 + Real.pi * x^2)^d * Real.exp (-(Real.pi * x^2)) ≤ B := by
  obtain ⟨B0, hB0nn, hB0⟩ := one_add_abs_pow_mul_exp_neg_pi_sq_le (A + 2*d)
  refine ⟨(1 + Real.pi)^d * B0, by positivity, fun x => ?_⟩
  have hbase : 1 + Real.pi * x^2 ≤ (1 + Real.pi) * (1 + |x|)^2 := by
    rw [show (1 + |x|)^2 = 1 + 2*|x| + x^2 by rw [add_sq, sq_abs]; ring]
    nlinarith [Real.pi_pos, abs_nonneg x, sq_nonneg x,
      mul_nonneg Real.pi_pos.le (abs_nonneg x), mul_nonneg Real.pi_pos.le (sq_nonneg x)]
  have hstep : (1 + Real.pi * x^2)^d ≤ (1 + Real.pi)^d * (1 + |x|)^(2*d) := by
    calc (1 + Real.pi * x^2)^d ≤ ((1 + Real.pi) * (1 + |x|)^2)^d :=
          pow_le_pow_left₀ (by positivity) hbase d
      _ = (1 + Real.pi)^d * (1 + |x|)^(2*d) := by rw [mul_pow, ← pow_mul]
  calc (1 + |x|)^A * (1 + Real.pi * x^2)^d * Real.exp (-(Real.pi * x^2))
      ≤ (1 + |x|)^A * ((1 + Real.pi)^d * (1 + |x|)^(2*d)) * Real.exp (-(Real.pi * x^2)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (1 + Real.pi)^d * ((1 + |x|)^(A + 2*d) * Real.exp (-(Real.pi * x^2))) := by
        rw [pow_add]; ring
    _ ≤ (1 + Real.pi)^d * B0 := mul_le_mul_of_nonneg_left (hB0 x) (by positivity)

/-! ## The main bound -/

theorem iteratedDeriv_comp_quad_bounded (J : ℝ → ℂ) (d : ℕ)
    (hJ : ContDiff ℝ ⊤ J)
    (hJ' : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖iteratedDeriv j J x‖ ≤ C * (1 + |x|) ^ d * Real.exp (-x))
    (k l : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ,
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => J (Real.pi * s ^ 2)) r‖ ≤ K := by
  classical
  obtain ⟨n, c, m, j, hmle, hjle, hrepr⟩ := exists_chain_repr J hJ l
  choose Cf hCf using fun i : Fin n => hJ' (j i)
  obtain ⟨B, hBnn, hB⟩ := weight_bounded (k + l) d
  refine ⟨B * ∑ i : Fin n, ‖c i‖ * Cf i, ?_, ?_⟩
  · exact mul_nonneg hBnn (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hCf i).1))
  · intro r
    rw [hrepr r]
    calc |r|^k * ‖∑ i : Fin n, c i * (r:ℂ)^(m i) * iteratedDeriv (j i) J (Real.pi * r^2)‖
        ≤ |r|^k * ∑ i : Fin n, ‖c i * (r:ℂ)^(m i) * iteratedDeriv (j i) J (Real.pi * r^2)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = ∑ i : Fin n, |r|^k * ‖c i * (r:ℂ)^(m i) * iteratedDeriv (j i) J (Real.pi * r^2)‖ := by
          rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin n, ‖c i‖ * Cf i * B := by
          apply Finset.sum_le_sum
          intro i _
          have hZ := (hCf i).2 (Real.pi * r^2)
          have habs : |Real.pi * r^2| = Real.pi * r^2 := abs_of_nonneg (by positivity)
          rw [habs] at hZ
          have hr : ‖(r:ℂ)‖ = |r| := RCLike.norm_ofReal r
          have hnorm : ‖c i * (r:ℂ)^(m i) * iteratedDeriv (j i) J (Real.pi * r^2)‖
              = ‖c i‖ * |r|^(m i) * ‖iteratedDeriv (j i) J (Real.pi * r^2)‖ := by
            rw [norm_mul, norm_mul, Complex.norm_pow, hr]
          rw [hnorm]
          have habsr : (0:ℝ) ≤ |r| := abs_nonneg r
          have hone : (1:ℝ) ≤ 1 + |r| := by linarith
          have hle1 : |r| ≤ 1 + |r| := by linarith
          have hpow : |r|^(k + m i) ≤ (1 + |r|)^(k + l) := by
            calc |r|^(k + m i) ≤ (1 + |r|)^(k + m i) := pow_le_pow_left₀ habsr hle1 _
              _ ≤ (1 + |r|)^(k + l) :=
                  pow_le_pow_right₀ hone (by have := hmle i; omega)
          calc |r|^k * (‖c i‖ * |r|^(m i) * ‖iteratedDeriv (j i) J (Real.pi * r^2)‖)
              ≤ |r|^k * (‖c i‖ * |r|^(m i)
                  * (Cf i * (1 + Real.pi * r^2)^d * Real.exp (-(Real.pi * r^2)))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hZ
                    (mul_nonneg (norm_nonneg _) (pow_nonneg habsr _)))
                  (by positivity)
            _ = ‖c i‖ * Cf i
                  * (|r|^(k + m i) * (1 + Real.pi * r^2)^d * Real.exp (-(Real.pi * r^2))) := by
                rw [pow_add]; ring
            _ ≤ ‖c i‖ * Cf i
                  * ((1 + |r|)^(k + l) * (1 + Real.pi * r^2)^d * Real.exp (-(Real.pi * r^2))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow (by positivity))
                    (Real.exp_nonneg _))
                  (mul_nonneg (norm_nonneg _) (hCf i).1)
            _ ≤ ‖c i‖ * Cf i * B :=
                mul_le_mul_of_nonneg_left (hB r) (mul_nonneg (norm_nonneg _) (hCf i).1)
      _ = B * ∑ i : Fin n, ‖c i‖ * Cf i := by
          rw [← Finset.sum_mul]; ring

end

end Work.Asymptotics
