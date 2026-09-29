import Mathlib
import Submission.Work.TMC14Core.Assembly

/-!
# TMC14Core: a lower bound for non-zero roots of `disc p q lam` in the even case

Let `P := disc p q lam` be the discriminant of the rational approximant `p/q` with even
denominator `q = 2m+2`.  Suppose that

* `P` is even (`hEvenPoly`), that `P(a) = c` with `|c| = 2 + 2λ^q` and that
  `P(0) = ±(2 + 2λ^q)` (`hZero`, `hca`, `hcabs`);
* the second derivative at `0` has norm at least `1` (`hSecond`);
* the first derivative is bounded by `K` and the third by `K₂` on the segment between `0`
  and `a` (`hK`, `hK2`).

Then `|a| ≥ min (1/(2K)) (1/(2K₂))`.

The argument is a two-case mean value argument.  Since `P(0)` and `P(a)` are *real* numbers
of modulus `M := 2 + 2λ^q`, each of them equals `±M`, so either `P(a) = P(0)` or
`P(a) = -P(0)`.

* If `P(a) = -P(0)`, then `‖P(a) - P(0)‖ = 2M` and the mean value inequality for
  `t ↦ P(t)` on `[min 0 a, max 0 a]` with the bound `K` on `‖derivative P‖` gives
  `2M ≤ K |a|`, hence `|a| ≥ 1/(2K)`.
* If `P(a) = P(0)`, the second-order Taylor remainder bound (`even_second_deriv_bound`,
  obtained from `n` nested mean value inequalities) gives `‖P″(0)‖ ≤ 2K₂|a|`, so that
  `1 ≤ ‖P″(0)‖ ≤ 2K₂|a|`, i.e. `|a| ≥ 1/(2K₂)`.

The auxiliary bound `even_second_deriv_bound` is the only analytic input: it constructs the
polynomial `2 (P - P(0) - P′(0) X) - P″(0) X²`, whose value at `a` is `-P″(0) a²` when
`P(a) = P(0)` and whose first three derivatives at `0` vanish (the third being `2 P‴`), and
applies the iterated mean value inequality to it.
-/

open Set

namespace Work.TMC14Core

noncomputable section

/-- A point of the real segment from `0` to `a` (inside `ℂ`) is the image of a real number
in `[min 0 a, max 0 a]`. -/
private lemma mem_segment_ofReal (a : ℝ) {z : ℂ} (hz : z ∈ segment ℝ (0:ℂ) (a:ℂ)) :
    ∃ ξ : ℝ, ξ ∈ Set.Icc (min 0 a) (max 0 a) ∧ z = (ξ:ℂ) := by
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨t * a, ?_, ?_⟩
  · rcases le_total 0 a with ha | ha
    · rw [min_eq_left ha, max_eq_right ha]
      exact ⟨mul_nonneg ht.1 ha, mul_le_of_le_one_left ha ht.2⟩
    · rw [min_eq_right ha, max_eq_left ha]
      exact ⟨by simpa using mul_le_mul_of_nonpos_right ht.2 ha,
        mul_nonpos_of_nonneg_of_nonpos ht.1 ha⟩
  · simp only [zero_add, sub_zero, Complex.real_smul, Complex.ofReal_mul]

/-- An even complex polynomial has vanishing derivative at the origin. -/
private lemma deriv_eval_zero_of_even (P : Polynomial ℂ)
    (h : ∀ z : ℂ, P.eval (-z) = P.eval z) : P.derivative.eval 0 = 0 := by
  have h1 : P.comp (-Polynomial.X) = P := by
    apply Polynomial.funext; intro z
    simpa using h z
  have h2 : -P.derivative.eval 0 = P.derivative.eval 0 := by
    have := congrArg (fun q : Polynomial ℂ => q.derivative.eval 0) h1
    simpa [Polynomial.derivative_comp, Polynomial.derivative_neg, Polynomial.derivative_X,
      Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_one,
      Polynomial.eval_X, neg_one_mul] using this
  have h3 : P.derivative.eval 0 + P.derivative.eval 0 = 0 := neg_eq_iff_add_eq_zero.mp h2
  have h4 : (2:ℂ) * P.derivative.eval 0 = 0 := by rw [two_mul]; exact h3
  exact (mul_eq_zero.mp h4).resolve_left (by norm_num)

/-- Mean value inequality for a complex polynomial on the real segment between `0` and `a`:
a bound `K` for `‖derivative P‖` on `[min 0 a, max 0 a]` gives `‖P(a) - P(0)‖ ≤ K |a|`. -/
private lemma norm_eval_sub_eval_le_of_deriv_bound (P : Polynomial ℂ) (a K : ℝ)
    (h : ∀ ξ ∈ Set.Icc (min 0 a) (max 0 a), ‖P.derivative.eval (ξ:ℂ)‖ ≤ K) :
    ‖P.eval (a:ℂ) - P.eval 0‖ ≤ K * |a| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun z : ℂ => P.eval z) (s := segment ℝ (0:ℂ) (a:ℂ)) (x := 0) (y := (a:ℂ)) (C := K)
    (fun z _ => (Polynomial.hasDerivAt P z).differentiableAt)
    (fun z hz => by
      obtain ⟨ξ, hξ, rfl⟩ := mem_segment_ofReal a hz
      rw [Polynomial.deriv]; exact h ξ hξ)
    (convex_segment _ _) (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  simpa using this

/-- Iterated mean value inequality for a complex polynomial on the real segment between `0`
and `a`: if `P` and its first `n-1` derivatives vanish at `0` and `‖P⁽ⁿ⁾‖ ≤ K` on
`[min 0 a, max 0 a]`, then `‖P(a) - P(0)‖ ≤ K |a|ⁿ`. -/
private lemma norm_eval_sub_eval_zero_le_of_iterated (P : Polynomial ℂ) (a K : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (hK : 0 ≤ K)
    (h : ∀ ξ ∈ Set.Icc (min 0 a) (max 0 a),
      ‖((Polynomial.derivative^[n]) P).eval (ξ : ℂ)‖ ≤ K)
    (h0 : ∀ k < n, ((Polynomial.derivative^[k]) P).eval (0 : ℂ) = 0) :
    ‖P.eval (a : ℂ) - P.eval 0‖ ≤ K * |a| ^ n := by
  have key : ∀ m : ℕ, ∀ (P : Polynomial ℂ) (a K : ℝ), 0 ≤ K →
      (∀ ξ ∈ Set.Icc (min 0 a) (max 0 a),
        ‖((Polynomial.derivative^[m+1]) P).eval (ξ : ℂ)‖ ≤ K) →
      (∀ k ≤ m, ((Polynomial.derivative^[k]) P).eval (0 : ℂ) = 0) →
      ‖P.eval (a : ℂ) - P.eval 0‖ ≤ K * |a| ^ (m+1) := by
    intro m
    induction m with
    | zero =>
      intro P a K hK h h0
      simpa using norm_eval_sub_eval_le_of_deriv_bound P a K (fun ξ hξ => by simpa using h ξ hξ)
    | succ m ih =>
      intro P a K hK h h0
      have hiter : ∀ k : ℕ, ((Polynomial.derivative^[k]) (Polynomial.derivative P))
          = ((Polynomial.derivative^[k+1]) P) :=
        fun k => (Function.iterate_succ_apply Polynomial.derivative k P).symm
      have hb : ∀ z ∈ segment ℝ (0:ℂ) (a:ℂ),
          ‖deriv (fun z : ℂ => P.eval z) z‖ ≤ K * |a| ^ (m+1) := by
        intro z hz
        obtain ⟨ξ, hξ, rfl⟩ := mem_segment_ofReal a hz
        rw [Polynomial.deriv]
        have hsub : Set.Icc (min 0 ξ) (max 0 ξ) ⊆ Set.Icc (min 0 a) (max 0 a) := fun x hx =>
          ⟨le_trans (le_min (min_le_left 0 a) hξ.1) hx.1,
           le_trans hx.2 (max_le (le_max_left 0 a) hξ.2)⟩
        have hb2 : ∀ η ∈ Set.Icc (min 0 ξ) (max 0 ξ),
            ‖((Polynomial.derivative^[m+1]) (Polynomial.derivative P)).eval (η:ℂ)‖ ≤ K := by
          intro η hη
          rw [hiter (m+1)]
          exact h η (hsub hη)
        have h02 : ∀ k ≤ m,
            ((Polynomial.derivative^[k]) (Polynomial.derivative P)).eval (0:ℂ) = 0 := by
          intro k hk
          rw [hiter k]
          exact h0 (k+1) (by omega)
        have hih := ih (Polynomial.derivative P) ξ K hK hb2 h02
        have hq0 : P.derivative.eval (0:ℂ) = 0 := h0 1 (by omega)
        rw [hq0, sub_zero] at hih
        have hξa : |ξ| ≤ |a| := by
          have h1 : -|a| ≤ min 0 a := le_min (neg_nonpos.mpr (abs_nonneg a)) (neg_abs_le a)
          have h2 : max 0 a ≤ |a| := max_le (abs_nonneg a) (le_abs_self a)
          exact abs_le.mpr ⟨le_trans h1 hξ.1, le_trans hξ.2 h2⟩
        calc ‖P.derivative.eval (ξ:ℂ)‖ ≤ K * |ξ| ^ (m+1) := hih
          _ ≤ K * |a| ^ (m+1) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg ξ) hξa _) hK
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
        (f := fun z : ℂ => P.eval z) (s := segment ℝ (0:ℂ) (a:ℂ)) (x := 0) (y := (a:ℂ))
        (C := K * |a| ^ (m+1))
        (fun z _ => (Polynomial.hasDerivAt P z).differentiableAt) hb
        (convex_segment _ _) (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
      have hmvt2 : ‖P.eval (a:ℂ) - P.eval 0‖ ≤ K * |a| ^ (m+1) * |a| := by simpa using hmvt
      calc ‖P.eval (a:ℂ) - P.eval 0‖ ≤ K * |a| ^ (m+1) * |a| := hmvt2
        _ = K * |a| ^ (m+1+1) := by ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  exact key m P a K hK h (fun k hk => h0 k (by omega))

/-- Derivative of the auxiliary polynomial
`C 2 * P - C (2 P(0)) - C (2 P-dash(0)) X - C w₀ X²`. -/
private lemma deriv_aux_poly (P : Polynomial ℂ) (w0 a1 : ℂ) :
    (Polynomial.C (2:ℂ) * P - Polynomial.C (2 * P.eval 0) - Polynomial.C (2 * a1) * Polynomial.X
      - Polynomial.C w0 * Polynomial.X^2).derivative
    = Polynomial.C (2:ℂ) * P.derivative - Polynomial.C (2 * a1)
      - Polynomial.C (w0 * 2) * Polynomial.X := by
  repeat rw [Polynomial.derivative_sub]
  rw [Polynomial.derivative_C_mul_X_sq, Polynomial.derivative_C_mul_X, Polynomial.derivative_C_mul,
    Polynomial.derivative_C, sub_zero]

/-- Second derivative of the auxiliary polynomial. -/
private lemma deriv_aux_poly₂ (P : Polynomial ℂ) (w0 a1 : ℂ) :
    (Polynomial.C (2:ℂ) * P.derivative - Polynomial.C (2 * a1)
        - Polynomial.C (w0 * 2) * Polynomial.X).derivative
      = Polynomial.C (2:ℂ) * (Polynomial.derivative (Polynomial.derivative P))
        - Polynomial.C (w0 * 2) := by
  repeat rw [Polynomial.derivative_sub]
  rw [Polynomial.derivative_C_mul_X, Polynomial.derivative_C_mul, Polynomial.derivative_C, sub_zero]

/-- Third derivative of the auxiliary polynomial. -/
private lemma deriv_aux_poly₃ (P : Polynomial ℂ) (w0 a1 : ℂ) :
    (Polynomial.C (2:ℂ) * (Polynomial.derivative (Polynomial.derivative P))
        - Polynomial.C (w0 * 2)).derivative
      = Polynomial.C (2:ℂ)
        * (Polynomial.derivative (Polynomial.derivative (Polynomial.derivative P))) := by
  rw [Polynomial.derivative_sub, Polynomial.derivative_C_mul, Polynomial.derivative_C, sub_zero]

/-- **Second-order bound for an even polynomial.**  If `P` is even, `P(a) = P(0)` with
`a ≠ 0`, and `‖P‴‖ ≤ K₂` on the segment between `0` and `a`, then `‖P″(0)‖ ≤ 2 K₂ |a|`.

This is the analytic core of the even case of `absLowerEven`: the polynomial
`2 (P - P(0) - P-dash(0) X) - P″(0) X²` has value `-P″(0) a²` at `a` (because `P(a) = P(0)`
and `P-dash(0) = 0`) and its first three derivatives at `0` are `0, 0, 2 P‴`, so the iterated
mean value inequality gives `‖P″(0)‖ a² ≤ 2 K₂ |a|³`. -/
private lemma even_second_deriv_bound (P : Polynomial ℂ) (a K2 : ℝ) (hK2 : 0 ≤ K2) (ha : a ≠ 0)
    (heven : ∀ z : ℂ, P.eval (-z) = P.eval z)
    (hpeq : P.eval (a:ℂ) = P.eval 0)
    (h : ∀ ξ ∈ Set.Icc (min 0 a) (max 0 a),
      ‖(Polynomial.derivative (Polynomial.derivative (Polynomial.derivative P))).eval (ξ : ℂ)‖ ≤ K2) :
    ‖(Polynomial.derivative (Polynomial.derivative P)).eval 0‖ ≤ 2 * K2 * |a| := by
  set w0 : ℂ := (Polynomial.derivative (Polynomial.derivative P)).eval 0 with hw0
  have ha1z : P.derivative.eval (0:ℂ) = 0 := deriv_eval_zero_of_even P heven
  set R : Polynomial ℂ := Polynomial.C (2:ℂ) * P - Polynomial.C (2 * P.eval 0)
      - Polynomial.C (2 * P.derivative.eval 0) * Polynomial.X
      - Polynomial.C w0 * Polynomial.X^2 with hR
  have hRd : R.derivative = Polynomial.C (2:ℂ) * P.derivative
      - Polynomial.C (2 * P.derivative.eval 0) - Polynomial.C (w0 * 2) * Polynomial.X := by
    rw [hR]; exact deriv_aux_poly P w0 (P.derivative.eval 0)
  have hRdd : (R.derivative).derivative
      = Polynomial.C (2:ℂ) * (Polynomial.derivative (Polynomial.derivative P))
        - Polynomial.C (w0 * 2) := by
    rw [hRd]; exact deriv_aux_poly₂ P w0 (P.derivative.eval 0)
  have hRddd : ((R.derivative).derivative).derivative
      = Polynomial.C (2:ℂ)
        * (Polynomial.derivative (Polynomial.derivative (Polynomial.derivative P))) := by
    rw [hRdd]; exact deriv_aux_poly₃ P w0 (P.derivative.eval 0)
  have hR0 : R.eval 0 = 0 := by rw [hR]; simp
  have hR10 : R.derivative.eval 0 = 0 := by rw [hRd]; simp [ha1z]
  have hR20 : ((R.derivative).derivative).eval 0 = 0 := by
    rw [hRdd]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, ← hw0]; ring
  have hbnd : ∀ ξ ∈ Set.Icc (min 0 a) (max 0 a),
      ‖((Polynomial.derivative^[3]) R).eval (ξ:ℂ)‖ ≤ 2 * K2 := by
    intro ξ hξ
    have h3 : ((Polynomial.derivative^[3]) R)
        = Polynomial.C (2:ℂ)
          * (Polynomial.derivative (Polynomial.derivative (Polynomial.derivative P))) := by
      rw [show ((Polynomial.derivative^[3]) R) = ((R.derivative).derivative).derivative from by
        simp [Function.iterate_succ_apply']]
      exact hRddd
    rw [h3]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [norm_mul]
    norm_num
    linarith [h ξ hξ]
  have hiter := norm_eval_sub_eval_zero_le_of_iterated R a (2 * K2) 3 (by norm_num)
    (by linarith) hbnd (by
      intro k hk
      interval_cases k
      · simpa using hR0
      · simpa using hR10
      · simpa [Function.iterate_succ_apply'] using hR20)
  rw [hR0, sub_zero] at hiter
  have hRa1 : R.eval (a:ℂ) = 2 * P.eval (a:ℂ) - 2 * P.eval 0
      - (2 * P.derivative.eval 0) * (a:ℂ) - w0 * (a:ℂ)^2 := by
    rw [hR]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_X_pow, Polynomial.eval_ofNat]
  have hRa : R.eval (a:ℂ) = -(w0 * (a:ℂ)^2) := by
    rw [hRa1, hpeq, ha1z]
    ring
  rw [hRa, norm_neg, norm_mul, norm_pow] at hiter
  have hnorm : ‖(a:ℂ)‖ = |a| := by simp
  rw [hnorm] at hiter
  have ha2 : (0:ℝ) < |a|^2 := by positivity
  rw [show (2:ℝ) * K2 * |a|^3 = (2 * K2 * |a|) * |a|^2 from by ring] at hiter
  exact le_of_mul_le_mul_right hiter ha2

/-- **TMC14Core: lower bound for non-zero roots of `disc p q lam` in the even case.**

If `q = 2m+2`, `disc p q lam` is even, `P(a) = c` with `|c| = 2 + 2λ^q` and
`P(0) = ±(2 + 2λ^q)`, `‖P″(0)‖ ≥ 1`, and `‖derivative P‖ ≤ K`, `‖P‴‖ ≤ K₂` on the segment
between `0` and `a`, then `|a| ≥ min (1/(2K)) (1/(2K₂))`. -/
theorem absLowerEven (p : ℤ) (q m : ℕ) (hm : q = 2 * m + 2) (hpq : Nat.Coprime p.natAbs q)
    (lam : ℝ) (hlam : 0 < lam) {a c K K2 : ℝ} (ha : a ≠ 0)
    (hca : (disc p q lam).eval (a : ℂ) = (c : ℂ)) (hcabs : |c| = 2 + 2 * lam ^ q)
    (hZero : (disc p q lam).eval 0 = ((2 + 2 * lam ^ q : ℝ) : ℂ) ∨
      (disc p q lam).eval 0 = ((-(2 + 2 * lam ^ q) : ℝ) : ℂ))
    (hSecond : (1 : ℝ) ≤ ‖(Polynomial.derivative (Polynomial.derivative (disc p q lam))).eval 0‖)
    (hEvenPoly : ∀ z : ℂ, (disc p q lam).eval (-z) = (disc p q lam).eval z)
    (hK : ∀ ξ ∈ Set.Icc (min 0 a) (max 0 a), ‖(disc p q lam).derivative.eval (ξ : ℂ)‖ ≤ K)
    (hK2 : ∀ ξ ∈ Set.Icc (min 0 a) (max 0 a),
      ‖(Polynomial.derivative (Polynomial.derivative (Polynomial.derivative (disc p q lam)))).eval
        (ξ : ℂ)‖ ≤ K2)
    (hKpos : 0 < K) (hK2pos : 0 < K2) :
    min (1 / (2 * K)) (1 / (2 * K2)) ≤ |a| := by
  set M : ℝ := 2 + 2 * lam ^ q with hM
  have hMpos : 0 < M := by
    rw [hM]; have := pow_pos hlam q; linarith
  have hM2 : (2:ℝ) < M := by
    rw [hM]; have := pow_pos hlam q; linarith
  -- `c` is a real number of modulus `M`, hence `c = ± M`.
  have hc : c = M ∨ c = -M := by
    rcases abs_cases c with ⟨h1, _⟩ | ⟨h1, _⟩
    · left; rw [← h1, hcabs]
    · right
      have h2 : -c = M := by rw [← h1, hcabs]
      linarith
  have hp_a : (disc p q lam).eval (a:ℂ) = (M:ℂ) ∨
      (disc p q lam).eval (a:ℂ) = (↑(-M) : ℂ) := by
    rcases hc with h | h
    · left; rw [hca, h]
    · right; rw [hca, h]
  have hp_0 : (disc p q lam).eval 0 = (M:ℂ) ∨ (disc p q lam).eval 0 = (↑(-M) : ℂ) := hZero
  by_cases hsame : (disc p q lam).eval (a:ℂ) = (disc p q lam).eval 0
  · -- `P(a) = P(0)`: use the second-order bound, hence `|a| ≥ 1/(2K₂)`.
    have hb := even_second_deriv_bound (disc p q lam) a K2 hK2pos.le ha hEvenPoly hsame hK2
    have h1 : (1:ℝ) ≤ 2 * K2 * |a| := le_trans hSecond hb
    have h2 : 1 / (2 * K2) ≤ |a| := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * K2)]
      linarith
    exact le_trans (min_le_right _ _) h2
  · -- `P(a) ≠ P(0)`: the two values are `±M`, hence opposite; first-order bound.
    have hopp : (disc p q lam).eval (a:ℂ) = -(disc p q lam).eval 0 := by
      rcases hp_0 with h0 | h0 <;> rcases hp_a with hp | hp
      · exact absurd (by rw [h0, hp]) hsame
      · rw [hp, h0]; simp
      · rw [hp, h0]; simp
      · exact absurd (by rw [h0, hp]) hsame
    have hp0n : ‖(disc p q lam).eval 0‖ = M := by
      rcases hp_0 with h0 | h0 <;> rw [h0] <;> simp [abs_of_pos hMpos]
    have hnorm : ‖(disc p q lam).eval (a:ℂ) - (disc p q lam).eval 0‖ = 2 * M := by
      rw [hopp, ← hp0n]
      rw [show -(disc p q lam).eval 0 - (disc p q lam).eval 0
            = -(2 * (disc p q lam).eval 0) from by ring, norm_neg, norm_mul]
      norm_num
    have hb := norm_eval_sub_eval_le_of_deriv_bound (disc p q lam) a K hK
    have h2M : 2 * M ≤ K * |a| := by rw [← hnorm]; exact hb
    have h2 : 1 / (2 * K) ≤ |a| := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * K)]
      nlinarith [h2M, hM2, hKpos]
    exact le_trans (min_le_left _ _) h2

end

end Work.TMC14Core
