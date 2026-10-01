import Mathlib

namespace Work.ZeroDensity.Huxley

/-! ### Elementary complex-power identities used in the proof

`(n : ℂ) ^ (I * t)` is well behaved for `n ≥ 1` (it is `exp (I * t * log n)`), but the degenerate
index `n = 0` also occurs, where Mathlib's `Complex.cpow` sets `0 ^ 0 = 1` and `0 ^ z = 0` for
`z ≠ 0`.  The two facts below hold for *all* `n : ℕ`. -/

/-- `star (I * t) = -(I * t)` for real `t`. -/
lemma star_I_mul_ofReal (t : ℝ) : star (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ)) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- `conj (n ^ y) = n ^ conj y` for a natural base `n` (all `n`, including `0`). -/
lemma star_natCast_cpow (n : ℕ) (y : ℂ) :
    star ((n : ℂ) ^ y) = (n : ℂ) ^ star y := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero]
    by_cases hy : y = 0
    · subst hy; simp
    · rw [Complex.zero_cpow hy, star_zero, Complex.zero_cpow (by simpa using hy)]
  · have harg : ((n : ℂ)).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
    have hh := Complex.cpow_conj (n : ℂ) y harg
    rw [Complex.conj_natCast] at hh
    exact hh.symm

/-- Additivity of `Complex.cpow` on a natural base, available as long as the total exponent does
not vanish: this covers the degenerate base `0`, where Mathlib's `Complex.cpow_add` does not
apply. -/
lemma cpow_add_of_add_ne_zero (n : ℕ) (y z : ℂ) (h : y + z ≠ 0) :
    (n : ℂ) ^ (y + z) = (n : ℂ) ^ y * (n : ℂ) ^ z := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero]
    rcases eq_or_ne y 0 with rfl | hy
    · rw [zero_add, Complex.cpow_zero, one_mul]
    · rw [Complex.zero_cpow hy, zero_mul, Complex.zero_cpow h]
  · rw [Complex.cpow_add _ _ (by exact_mod_cast hn : (n : ℂ) ≠ 0)]

/-- The key multiplicativity identity: for `t ≠ t'`,
`n ^ (I t) * conj (n ^ (I t')) = n ^ (I (t - t'))`, for **every** natural `n` (the case `n = 0`
included). -/
lemma cpow_I_mul_conj {n : ℕ} {t t' : ℝ} (h : t ≠ t') :
    (n : ℂ) ^ (Complex.I * (t : ℂ)) * star ((n : ℂ) ^ (Complex.I * (t' : ℂ)))
      = (n : ℂ) ^ (Complex.I * ((t - t' : ℝ) : ℂ)) := by
  rw [star_natCast_cpow]
  have key : Complex.I * (t : ℂ) + star (Complex.I * (t' : ℂ))
      = Complex.I * ((t - t' : ℝ) : ℂ) := by
    rw [star_I_mul_ofReal, Complex.ofReal_sub]; ring
  have hz : Complex.I * (t : ℂ) + star (Complex.I * (t' : ℂ)) ≠ 0 := by
    rw [key]
    intro hh
    rcases mul_eq_zero.mp hh with h1 | h2
    · exact Complex.I_ne_zero h1
    · exact h (sub_eq_zero.mp (by exact_mod_cast h2))
  rw [← key, cpow_add_of_add_ne_zero n _ _ hz]

/-- `‖n ^ (I t)‖ ≤ 1` for every natural `n` and real `t`. -/
lemma norm_cpow_I_le_one (n : ℕ) (t : ℝ) : ‖(n : ℂ) ^ (Complex.I * (t : ℂ))‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero]
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · rw [Complex.zero_cpow]; · simp
      · simp [Complex.I_ne_zero, ht]
  · rw [show (n : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
      Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    simp

/-! ### Elementary lemmas about `star`, norms and finite sums -/

/-- `conj z * z = ‖z‖ ^ 2` (as a complex number). -/
lemma star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  have h := Complex.conj_mul' z
  rw [show ((‖z‖ ^ 2 : ℝ) : ℂ) = ((‖z‖ : ℂ)) ^ 2 from Complex.ofReal_pow _ _]
  exact h

/-- `z * conj z = ‖z‖ ^ 2` (as a complex number). -/
lemma mul_star_self (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  have h := Complex.mul_conj' z
  rw [show ((‖z‖ ^ 2 : ℝ) : ℂ) = ((‖z‖ : ℂ)) ^ 2 from Complex.ofReal_pow _ _]
  exact h

/-- Cauchy–Schwarz for complex finite sums, phrased with `sqrt` so that it can be squared. -/
lemma norm_sum_mul_le_sqrt {ι : Type*} (s : Finset ι) (x y : ι → ℂ) :
    ‖∑ i ∈ s, x i * y i‖
      ≤ Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) := by
  have h1 : ‖∑ i ∈ s, x i * y i‖ ≤ ∑ i ∈ s, ‖x i‖ * ‖y i‖ := by
    refine (norm_sum_le s (fun i => x i * y i)).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_mul]
  have h2 : (∑ i ∈ s, ‖x i‖ * ‖y i‖) ^ 2
      ≤ (∑ i ∈ s, ‖x i‖ ^ 2) * (∑ i ∈ s, ‖y i‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖x i‖) (fun i => ‖y i‖)
  have h3 : ∑ i ∈ s, ‖x i‖ * ‖y i‖
      ≤ Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) := by
    have h4 := Real.le_sqrt_of_sq_le h2
    rwa [Real.sqrt_mul (by positivity)] at h4
  exact h1.trans h3

/-- The off-diagonal sum bound: `Σ_t Σ_{t' ≠ t ∈ S} a t · a t' ≤ |S| · Σ_t (a t)^2` for `a ≥ 0`
on `S`. -/
lemma offDiag_le_card_mul {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) :
    ∑ t ∈ S, ∑ t' ∈ S.erase t, a t * a t' ≤ (S.card : ℝ) * ∑ t ∈ S, (a t) ^ 2 := by
  have h1 : ∑ t ∈ S, ∑ t' ∈ S.erase t, a t * a t' ≤ ∑ t ∈ S, ∑ t' ∈ S, a t * a t' := by
    refine Finset.sum_le_sum (fun t ht => ?_)
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
    intro i hiS _
    exact mul_nonneg (ha t ht) (ha i hiS)
  have h2 : ∑ t ∈ S, ∑ t' ∈ S, a t * a t' = (∑ t ∈ S, a t) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have h3 : (∑ t ∈ S, a t) ^ 2 ≤ (S.card : ℝ) * ∑ t ∈ S, (a t) ^ 2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) a
    simpa using hh
  calc ∑ t ∈ S, ∑ t' ∈ S.erase t, a t * a t'
      ≤ ∑ t ∈ S, ∑ t' ∈ S, a t * a t' := h1
    _ = (∑ t ∈ S, a t) ^ 2 := h2
    _ ≤ (S.card : ℝ) * ∑ t ∈ S, (a t) ^ 2 := h3

/-- The `t' = t` (diagonal) term of the weighted Gram form: its real part is at most
`Σ_{n ∈ s} (w n)^2`, because `‖n ^ (I t)‖ ≤ 1`. -/
lemma re_sum_diag_cpow_le {s : Finset ℕ} (w : ℕ → ℝ) (t : ℝ) :
    (∑ n ∈ s, ((w n ^ 2 : ℝ) : ℂ) *
        ((n : ℂ) ^ (Complex.I * (t : ℂ)) * star ((n : ℂ) ^ (Complex.I * (t : ℂ))))).re
      ≤ ∑ n ∈ s, w n ^ 2 := by
  rw [Complex.re_sum]
  refine Finset.sum_le_sum (fun n _ => ?_)
  rw [mul_star_self, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h1 : ‖(n : ℂ) ^ (Complex.I * (t : ℂ))‖ ^ 2 ≤ 1 := by
    have h := norm_cpow_I_le_one n t
    nlinarith [norm_nonneg ((n : ℂ) ^ (Complex.I * (t : ℂ)))]
  exact mul_le_of_le_one_right (sq_nonneg (w n)) h1

/-- **The Halász–Montgomery `MM*` (Gram-matrix) bound for Dirichlet polynomials.**

Let `S` be a finite set of real points, `s` a finite set of indices, `w : ℕ → ℝ` weights and
`b : ℕ → ℂ` coefficients, and put `f t = Σ_{n ∈ s} b n · w n · n^{i t}`.  Suppose the off-diagonal
entries of the weighted Gram matrix `G t t' = Σ_{n ∈ s} (w n)^2 · n^{i (t - t')}` are bounded by
`D ≥ 0` in modulus (hypotheses `hD`, `hD0`; the diagonal entry is `G t t = Σ_{n ∈ s} (w n)^2`).
Then `Σ_{t ∈ S} ‖f t‖^2 ≤ (Σ_{n ∈ s} (w n)^2 + |S| · D) · Σ_{n ∈ s} ‖b n‖^2`.

This is the classical `M M*` inequality underlying the Halász–Montgomery method for counting large
values of Dirichlet polynomials (Montgomery, *Topics in Multiplicative Number Theory*, Ch. 7; see
also L. Guth, *Large value estimates in number theory, harmonic analysis, and computer science*,
arXiv:2503.07410, section "The Montgomery-Halasz / M M* method").  With `M` the `|S| × s` matrix
`M t n = w n · n^{i t}` one has `‖M‖^2 = ‖M M*‖`, the Gram matrix `M M*` has diagonal
`Σ_n (w n)^2` and off-diagonal entries of modulus at most `D`, so `‖M M*‖ ≤ Σ_n (w n)^2 + |S|·D`
(its off-diagonal part has Frobenius norm at most `|S|·D`), and `Σ_t ‖f t‖^2 = ‖M b‖^2`.
Elementary proof avoiding spectral theory: Cauchy-Schwarz applied twice, once with the weights
`w n`.  Suggested steps.  (1) With `f t = Σ_n (b n · w n) · n^{i t}` and
`A n = Σ_{t ∈ S} star (f t) · n^{i t}` one has `Σ_t ‖f t‖^2 = Re (Σ_n (b n · w n) · A n)`.
(2) `‖Σ_n (b n · w n) · A n‖ ≤ (Σ_n ‖b n‖^2)^{1/2} · (Σ_n (w n)^2 · ‖A n‖^2)^{1/2}`
(Cauchy-Schwarz with weights).  (3) Expanding `Σ_n (w n)^2 ‖A n‖^2` as the Hermitian form of the
Gram matrix gives the bound `(Σ_n (w n)^2 + |S| · D) · Σ_t ‖f t‖^2` (diagonal
`Σ_n (w n)^2`, off-diagonal `D`, and `(Σ_t ‖f t‖)^2 ≤ |S| · Σ_t ‖f t‖^2`).
(4) Deduce `X^2 ≤ (Σ‖b n‖^2) · (Σ (w n)^2 + |S| D) · X` for `X = Σ_t ‖f t‖^2 ≥ 0` and cancel.
Useful lemmas: `Complex.re_sum`, `Complex.normSq_eq_conj_mul_self`, `Complex.normSq_eq_norm_sq`,
`Finset.sum_mul_sq_le_sq_mul_sq`, `sq_sum_le_card_mul_sum_sq`, `Finset.sum_comm`. -/
theorem largeValuesMM {s : Finset ℕ} (w : ℕ → ℝ) (b : ℕ → ℂ) (S : Finset ℝ) {D : ℝ}
    (hD0 : 0 ≤ D)
    (hD : ∀ t ∈ S, ∀ t' ∈ S, t ≠ t' →
      ‖∑ n ∈ s, ((w n ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (Complex.I * ((t - t' : ℝ) : ℂ))‖ ≤ D) :
    ∑ t ∈ S, ‖∑ n ∈ s, (b n * (w n : ℂ)) * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ^ 2
      ≤ ((∑ n ∈ s, w n ^ 2) + (S.card : ℝ) * D) * ∑ n ∈ s, ‖b n‖ ^ 2 := by
  set m : ℕ → ℝ → ℂ := fun n t => (n : ℂ) ^ (Complex.I * (t : ℂ)) with hm
  set F : ℝ → ℂ := fun t => ∑ n ∈ s, (b n * (w n : ℂ)) * m n t with hF
  set A : ℕ → ℂ := fun n => ∑ t ∈ S, star (F t) * m n t with hA
  set X : ℝ := ∑ t ∈ S, ‖F t‖ ^ 2 with hX
  set B : ℝ := ∑ n ∈ s, ‖b n‖ ^ 2 with hB
  set Z : ℝ := ∑ n ∈ s, (w n) ^ 2 * ‖A n‖ ^ 2 with hZ
  set C : ℝ := (∑ n ∈ s, w n ^ 2) + (S.card : ℝ) * D with hC
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hCnn : 0 ≤ C := by
    rw [hC]
    have h1 : 0 ≤ (∑ n ∈ s, w n ^ 2 : ℝ) := by positivity
    have h2 : 0 ≤ (S.card : ℝ) * D := mul_nonneg (Nat.cast_nonneg _) hD0
    linarith
  -- (1) `Σ_t ‖f t‖² = Re (Σ_n (b n · w n) · A n)`
  have hkey : (∑ n ∈ s, (b n * (w n : ℂ)) * A n) = (X : ℂ) := by
    rw [hX]
    calc ∑ n ∈ s, (b n * (w n : ℂ)) * A n
        = ∑ n ∈ s, ∑ t ∈ S, (b n * (w n : ℂ)) * (star (F t) * m n t) := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [hA, Finset.mul_sum]
        _ = ∑ t ∈ S, ∑ n ∈ s, (b n * (w n : ℂ)) * (star (F t) * m n t) :=
            Finset.sum_comm
        _ = ∑ t ∈ S, star (F t) * F t := by
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [hF, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun n _ => ?_)
            ring
        _ = ∑ t ∈ S, ((‖F t‖ ^ 2 : ℝ) : ℂ) := by
            refine Finset.sum_congr rfl (fun t _ => star_mul_self (F t))
        _ = ((∑ t ∈ S, ‖F t‖ ^ 2 : ℝ) : ℂ) :=
            (Complex.ofReal_sum S (fun t => ‖F t‖ ^ 2)).symm
  have hXeq : X = (∑ n ∈ s, (b n * (w n : ℂ)) * A n).re := by
    rw [hkey, Complex.ofReal_re]
  have hXle : X ≤ ‖∑ n ∈ s, (b n * (w n : ℂ)) * A n‖ := by
    rw [hXeq]; exact Complex.re_le_norm _
  -- (2) Cauchy–Schwarz with the weights `w n`
  have hreindex : (∑ n ∈ s, b n * ((w n : ℂ) * A n))
      = ∑ n ∈ s, (b n * (w n : ℂ)) * A n :=
    Finset.sum_congr rfl (fun n _ => by ring)
  have hZsum : (∑ n ∈ s, ‖(w n : ℂ) * A n‖ ^ 2) = Z := by
    rw [hZ]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [norm_mul, mul_pow, Complex.sq_norm, Complex.normSq_ofReal]; ring
  have hXle2 : X ≤ Real.sqrt B * Real.sqrt Z := by
    calc X ≤ ‖∑ n ∈ s, (b n * (w n : ℂ)) * A n‖ := hXle
      _ = ‖∑ n ∈ s, b n * ((w n : ℂ) * A n)‖ := by rw [hreindex]
      _ ≤ Real.sqrt (∑ n ∈ s, ‖b n‖ ^ 2) * Real.sqrt (∑ n ∈ s, ‖(w n : ℂ) * A n‖ ^ 2) :=
            norm_sum_mul_le_sqrt s (fun n => b n) (fun n => (w n : ℂ) * A n)
      _ = Real.sqrt B * Real.sqrt Z := by rw [← hB, ← hZsum]
  -- (3) the Hermitian form of the (weighted) Gram matrix
  have hStep3 : Z ≤ C * X := by
    set Inner : ℝ → ℝ → ℂ := fun t t' =>
      ∑ n ∈ s, ((w n ^ 2 : ℝ) : ℂ) * (m n t * star (m n t')) with hInner
    have hInner_eq : ∀ t t', t ≠ t' → Inner t t'
        = ∑ n ∈ s, ((w n ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (Complex.I * ((t - t' : ℝ) : ℂ)) := by
      intro t t' hne
      rw [hInner]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      simp only [hm]
      rw [cpow_I_mul_conj hne]
    have hInner_diag : ∀ t, (Inner t t).re ≤ ∑ n ∈ s, w n ^ 2 := by
      intro t
      rw [hInner]
      simpa only [hm] using re_sum_diag_cpow_le w t
    set P : ℂ := ∑ n ∈ s, ((w n ^ 2 : ℝ) : ℂ) * (A n * star (A n)) with hP
    have hstarA : ∀ n, star (A n) = ∑ t ∈ S, F t * star (m n t) := by
      intro n
      rw [hA, star_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [star_mul, star_star]
      ring
    have hP_re : P.re = Z := by
      rw [hP, hZ, Complex.re_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [Complex.re_ofReal_mul, mul_star_self (A n), Complex.ofReal_re]
    have hPexpand : P = ∑ t ∈ S, ∑ t' ∈ S, star (F t) * F t' * Inner t t' := by
      rw [hP]
      have h1 : ∀ n, A n * star (A n) = ∑ t ∈ S, ∑ t' ∈ S,
          (star (F t) * m n t) * (F t' * star (m n t')) := by
        intro n
        rw [hstarA n, hA, Finset.sum_mul_sum]
      calc ∑ n ∈ s, ((w n ^ 2 : ℝ) : ℂ) * (A n * star (A n))
          = ∑ n ∈ s, ∑ t ∈ S, ∑ t' ∈ S,
              ((w n ^ 2 : ℝ) : ℂ) * ((star (F t) * m n t) * (F t' * star (m n t'))) := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [h1 n, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [Finset.mul_sum]
        _ = ∑ t ∈ S, ∑ t' ∈ S, ∑ n ∈ s,
              ((w n ^ 2 : ℝ) : ℂ) * ((star (F t) * m n t) * (F t' * star (m n t'))) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun t _ => Finset.sum_comm)
        _ = ∑ t ∈ S, ∑ t' ∈ S, star (F t) * F t' *
              (∑ n ∈ s, ((w n ^ 2 : ℝ) : ℂ) * (m n t * star (m n t'))) := by
            refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun t' _ => ?_))
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun n _ => ?_)
            ring
        _ = ∑ t ∈ S, ∑ t' ∈ S, star (F t) * F t' * Inner t t' := by
            refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun t' _ => ?_))
            simp only [hInner]
    set Pdiag : ℂ := ∑ t ∈ S, star (F t) * F t * Inner t t with hPdiag
    set Poff : ℂ := ∑ t ∈ S, ∑ t' ∈ S.erase t, star (F t) * F t' * Inner t t' with hPoff
    have hsplit : P = Poff + Pdiag := by
      rw [hPexpand, hPoff, hPdiag, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      exact (Finset.sum_erase_add S (fun t' => star (F t) * F t' * Inner t t') ht).symm
    have hPdiagle : Pdiag.re ≤ (∑ n ∈ s, w n ^ 2) * X := by
      rw [hPdiag, hX, Complex.re_sum]
      calc ∑ t ∈ S, (star (F t) * F t * Inner t t).re
          = ∑ t ∈ S, ‖F t‖ ^ 2 * (Inner t t).re := by
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [star_mul_self (F t), Complex.re_ofReal_mul]
        _ ≤ ∑ t ∈ S, ‖F t‖ ^ 2 * (∑ n ∈ s, w n ^ 2) := by
            refine Finset.sum_le_sum (fun t _ => ?_)
            exact mul_le_mul_of_nonneg_left (hInner_diag t) (by positivity)
        _ = (∑ t ∈ S, ‖F t‖ ^ 2) * (∑ n ∈ s, w n ^ 2) := by
            rw [Finset.sum_mul]
        _ = (∑ n ∈ s, w n ^ 2) * (∑ t ∈ S, ‖F t‖ ^ 2) := by ring
    have hPoffle : ‖Poff‖ ≤ D * ((S.card : ℝ) * X) := by
      rw [hPoff]
      calc ‖∑ t ∈ S, ∑ t' ∈ S.erase t, star (F t) * F t' * Inner t t'‖
          ≤ ∑ t ∈ S, ‖∑ t' ∈ S.erase t, star (F t) * F t' * Inner t t'‖ :=
              norm_sum_le S _
        _ ≤ ∑ t ∈ S, ∑ t' ∈ S.erase t, ‖star (F t) * F t' * Inner t t'‖ :=
              Finset.sum_le_sum (fun t _ => norm_sum_le _ _)
        _ = ∑ t ∈ S, ∑ t' ∈ S.erase t, ‖F t‖ * ‖F t'‖ * ‖Inner t t'‖ := by
              refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun t' _ => ?_))
              rw [norm_mul, norm_mul, norm_star]
        _ ≤ ∑ t ∈ S, ∑ t' ∈ S.erase t, ‖F t‖ * ‖F t'‖ * D := by
              refine Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun t' ht' => ?_))
              have htne : t' ≠ t := (Finset.mem_erase.mp ht').1
              have ht'S : t' ∈ S := (Finset.mem_erase.mp ht').2
              have hG : ‖Inner t t'‖ ≤ D := by
                rw [hInner_eq t t' htne.symm]; exact hD t ht t' ht'S htne.symm
              exact mul_le_mul_of_nonneg_left hG (by positivity)
        _ = (∑ t ∈ S, ∑ t' ∈ S.erase t, ‖F t‖ * ‖F t'‖) * D := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl (fun t _ => ?_)
              rw [Finset.sum_mul]
        _ ≤ ((S.card : ℝ) * X) * D := by
              refine mul_le_mul_of_nonneg_right ?_ hD0
              rw [hX]
              exact offDiag_le_card_mul S (fun t => ‖F t‖) (fun t _ => norm_nonneg _)
        _ = D * ((S.card : ℝ) * X) := by ring
    have h1 : Z = Pdiag.re + Poff.re := by
      rw [← hP_re, hsplit, Complex.add_re]
      ring
    rw [h1, hC]
    nlinarith [hPdiagle, Complex.re_le_norm Poff, hPoffle]
  -- (4) square and cancel
  have hXsq : X ^ 2 ≤ B * C * X := by
    have h1 : X ≤ Real.sqrt B * Real.sqrt (C * X) :=
      hXle2.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hStep3) (Real.sqrt_nonneg B))
    have h2 : (Real.sqrt B * Real.sqrt (C * X)) ^ 2 = B * C * X := by
      rw [mul_pow, Real.sq_sqrt hBnn, Real.sq_sqrt (mul_nonneg hCnn hXnn)]
      ring
    calc X ^ 2 ≤ (Real.sqrt B * Real.sqrt (C * X)) ^ 2 := pow_le_pow_left₀ hXnn h1 2
      _ = B * C * X := h2
  have hfin : X ≤ C * B := by
    rcases eq_or_lt_of_le hXnn with h0 | hpos
    · rw [← h0]; exact mul_nonneg hCnn hBnn
    · nlinarith [hXsq, hpos]
  simpa only [hX, hF, hm, hB, hC] using hfin

end Work.ZeroDensity.Huxley
