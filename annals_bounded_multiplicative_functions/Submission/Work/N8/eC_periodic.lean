import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.newton_series

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Polynomial Finset Real Complex

/-! ## Elementary properties of `eC` -/

/-- `e(t) = exp(2πit)` rewritten with the real multiplication inside. -/
private lemma eC_eq (t : ℝ) : Work.BMF.eC t = Complex.exp (((2 * Real.pi * t : ℝ)) * Complex.I) := by
  rw [Work.BMF.eC]
  congr 1
  push_cast
  ring

private lemma eC_add (t s : ℝ) : Work.BMF.eC (t + s) = Work.BMF.eC t * Work.BMF.eC s := by
  rw [eC_eq, eC_eq, eC_eq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma eC_int (m : ℤ) : Work.BMF.eC (m : ℝ) = 1 := by
  rw [eC_eq]
  have h : (((2 * Real.pi * (m:ℝ) : ℝ)) : ℂ) * Complex.I
      = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- `e` of a real multiple of `2πi` has modulus one, in particular `‖e(t)‖ = 1`. -/
private lemma eC_norm (t : ℝ) : ‖Work.BMF.eC t‖ = 1 := by
  rw [eC_eq, Complex.norm_exp_ofReal_mul_I]

private lemma eC_sub_int (t : ℝ) (m : ℤ) : Work.BMF.eC (t - (m:ℝ)) = Work.BMF.eC t := by
  have h : t - (m:ℝ) = t + ((-m : ℤ) : ℝ) := by push_cast; ring
  rw [h, eC_add, eC_int, mul_one]

/-! ## Elementary facts about `descPochhammer` and the binomial polynomials -/

/-- The falling factorial `X(X-1)···(X-i+1)` evaluated at `z` is the product `∏_{j<i}(z-j)`. -/
private lemma descPochhammer_eval_range (i : ℕ) (z : ℝ) :
    (descPochhammer ℝ i).eval z = ∏ j ∈ Finset.range i, (z - (j:ℝ)) := by
  induction i with
  | zero => simp [descPochhammer]
  | succ n ih =>
      rw [descPochhammer_succ_right, Polynomial.eval_mul, ih, Finset.prod_range_succ]
      congr 1
      simp [Polynomial.eval_sub]

/-- **The scaled binomial polynomial.**  For `c ≠ 0` and all real `y`,
`i!·c^i·C(y/c, i) = ∏_{j<i} (y - j c)`. -/
private theorem binP_eval_div {c : ℝ} (hc : c ≠ 0) (i : ℕ) (y : ℝ) :
    ((i.factorial : ℝ) * c ^ i) * (Work.BMF.binP i).eval (y / c)
      = ∏ j ∈ Finset.range i, (y - (j:ℝ) * c) := by
  rw [Work.BMF.binP, Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_range]
  have hfac : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hprod : ∏ j ∈ Finset.range i, (y - (j:ℝ) * c)
      = c ^ i * ∏ j ∈ Finset.range i, (y / c - (j:ℝ)) := by
    have h1 : ∏ j ∈ Finset.range i, (y - (j:ℝ) * c)
        = ∏ j ∈ Finset.range i, (c * (y / c - (j:ℝ))) := by
      apply Finset.prod_congr rfl
      intro j hj
      field_simp
    rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [hprod]
  have hcancel : ((i.factorial : ℝ) * c ^ i)
        * ((i.factorial : ℝ)⁻¹ * ∏ j ∈ Finset.range i, (y / c - (j:ℝ)))
      = c ^ i * ∏ j ∈ Finset.range i, (y / c - (j:ℝ)) := by
    have h1 : (i.factorial : ℝ) * (i.factorial : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hfac
    calc ((i.factorial : ℝ) * c ^ i)
            * ((i.factorial : ℝ)⁻¹ * ∏ j ∈ Finset.range i, (y / c - (j:ℝ)))
        = ((i.factorial : ℝ) * (i.factorial : ℝ)⁻¹)
            * (c ^ i * ∏ j ∈ Finset.range i, (y / c - (j:ℝ))) := by ring
      _ = c ^ i * ∏ j ∈ Finset.range i, (y / c - (j:ℝ)) := by rw [h1, one_mul]
  exact hcancel

/-! ## Divisibility helpers -/

/-- In any commutative ring, `m` divides `∏ (x_i + m) - ∏ x_i`. -/
private theorem prod_shift_dvd {ι : Type*} (s : Finset ι) (f : ι → ℤ) (m : ℤ) :
    m ∣ (∏ i ∈ s, (f i + m)) - ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      obtain ⟨k, hk⟩ := ih
      refine ⟨f a * k + ∏ i ∈ s, (f i + m), ?_⟩
      have h2 : ∏ i ∈ s, f i = (∏ i ∈ s, (f i + m)) - m * k := by
        rw [eq_sub_iff_add_eq, ← hk]; ring
      rw [h2]; ring

/-- `i! q^i` divides `k! q^k` whenever `i ≤ k`. -/
private theorem factorial_mul_pow_dvd {i k q : ℕ} (hik : i ≤ k) :
    i.factorial * q ^ i ∣ k.factorial * q ^ k :=
  Nat.mul_dvd_mul (Nat.factorial_dvd_factorial hik) (Nat.pow_dvd_pow q hik)

/-! ## The integrality lemma -/

/-- If `γ` has degree `≤ k` and is integral on `qℤ`, then `γ(n + k! q^k) - γ(n) ∈ ℤ`. -/
private lemma eval_period_int {k q : ℕ} (hq : 1 ≤ q) {γ : Polynomial ℝ}
    (hdeg : γ.natDegree ≤ k) (hint : Work.BMF.IntegralOn (q : ℝ) γ) (n : ℕ) :
    ∃ m : ℤ, γ.eval ((n : ℝ) + ((k.factorial * q ^ k : ℕ) : ℝ)) - γ.eval (n : ℝ) = (m : ℝ) := by
  set qR : ℝ := (q : ℝ) with hqR
  have hqR0 : qR ≠ 0 := by
    rw [hqR]
    have : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    exact ne_of_gt this
  -- the rescaled polynomial `g(X) = γ(qX)`, integer-valued on `ℤ`
  set g : ℝ[X] := γ.comp (C qR * X) with hgdef
  have hg_eval : ∀ x : ℝ, g.eval x = γ.eval (qR * x) := by
    intro x
    rw [hgdef, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hintg : Work.BMF.IntegralOn 1 g := by
    intro z
    obtain ⟨m, hm⟩ := hint z
    refine ⟨m, ?_⟩
    rw [hg_eval, one_mul, hqR]
    exact hm
  have hdegg : g.natDegree ≤ k := by
    rw [hgdef]
    calc (γ.comp (C qR * X)).natDegree
        ≤ γ.natDegree * (C qR * X : ℝ[X]).natDegree := Polynomial.natDegree_comp_le
      _ ≤ k * 1 := by
            apply Nat.mul_le_mul hdeg
            calc (C qR * X : ℝ[X]).natDegree ≤ (X : ℝ[X]).natDegree := Polynomial.natDegree_C_mul_le qR X
              _ = 1 := Polynomial.natDegree_X
      _ = k := mul_one k
  -- Newton expansion of `g`
  obtain ⟨c, hc⟩ := Work.BMF.newton_series k g hintg hdegg
  have heval : ∀ x : ℝ, γ.eval (qR * x)
      = ∑ i ∈ Finset.range (k+1), (c i : ℝ) * (Work.BMF.binP i).eval x := by
    intro x
    rw [← hg_eval x, hc, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.eval_mul, Polynomial.eval_C]
  set R : ℕ := k.factorial * q ^ k with hRdef
  set Rr : ℝ := (R : ℝ) with hRrdef
  change ∃ m : ℤ, γ.eval ((n : ℝ) + Rr) - γ.eval (n : ℝ) = (m : ℝ)
  have hdiff : γ.eval ((n:ℝ) + Rr) - γ.eval (n:ℝ)
      = ∑ i ∈ Finset.range (k+1),
          (c i : ℝ) * ((Work.BMF.binP i).eval (((n:ℝ) + Rr)/qR)
              - (Work.BMF.binP i).eval ((n:ℝ)/qR)) := by
    have hx1 : qR * (((n:ℝ) + Rr)/qR) = (n:ℝ) + Rr := by field_simp
    have hx2 : qR * ((n:ℝ)/qR) = (n:ℝ) := by field_simp
    calc γ.eval ((n:ℝ) + Rr) - γ.eval (n:ℝ)
        = γ.eval (qR * (((n:ℝ)+Rr)/qR)) - γ.eval (qR * ((n:ℝ)/qR)) := by rw [hx1, hx2]
      _ = (∑ i ∈ Finset.range (k+1), (c i:ℝ) * (Work.BMF.binP i).eval (((n:ℝ)+Rr)/qR))
          - (∑ i ∈ Finset.range (k+1), (c i:ℝ) * (Work.BMF.binP i).eval ((n:ℝ)/qR)) := by
            rw [heval, heval]
      _ = ∑ i ∈ Finset.range (k+1),
            (c i:ℝ) * ((Work.BMF.binP i).eval (((n:ℝ)+Rr)/qR)
              - (Work.BMF.binP i).eval ((n:ℝ)/qR)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [mul_sub]
  -- each summand is an integer
  have hΔ : ∀ i ∈ Finset.range (k+1), ∃ w : ℤ,
      (c i : ℝ) * ((Work.BMF.binP i).eval (((n:ℝ)+Rr)/qR)
          - (Work.BMF.binP i).eval ((n:ℝ)/qR)) = (w : ℝ) := by
    intro i hi
    have hik : i ≤ k := by
      have := Finset.mem_range.mp hi
      omega
    have hkey := binP_eval_div hqR0 i
    have hscale : ((i.factorial : ℝ) * qR^i) *
        ((Work.BMF.binP i).eval (((n:ℝ)+Rr)/qR) - (Work.BMF.binP i).eval ((n:ℝ)/qR))
        = (∏ j ∈ Finset.range i, (((n:ℝ)+Rr) - (j:ℝ)*qR))
          - ∏ j ∈ Finset.range i, ((n:ℝ) - (j:ℝ)*qR) := by
      rw [mul_sub, hkey ((n:ℝ)+Rr), hkey (n:ℝ)]
    obtain ⟨M, hM⟩ := prod_shift_dvd (Finset.range i)
      (fun j => (n:ℤ) - (j:ℤ)*(q:ℤ)) (R:ℤ)
    obtain ⟨s, hs⟩ := factorial_mul_pow_dvd (q := q) hik
    have hcastA : (∏ j ∈ Finset.range i, (((n:ℝ)+Rr) - (j:ℝ)*qR))
        = ((Finset.prod (Finset.range i)
            (fun j => (((n:ℤ)+(R:ℤ)) - (j:ℤ)*(q:ℤ))) : ℤ) : ℝ) := by
      rw [Int.cast_prod]
      apply Finset.prod_congr rfl
      intro j hj
      rw [hRrdef, hqR]
      push_cast
      ring
    have hcastB : (∏ j ∈ Finset.range i, ((n:ℝ) - (j:ℝ)*qR))
        = ((Finset.prod (Finset.range i)
            (fun j => ((n:ℤ) - (j:ℤ)*(q:ℤ))) : ℤ) : ℝ) := by
      rw [Int.cast_prod]
      apply Finset.prod_congr rfl
      intro j hj
      rw [hqR]
      push_cast
      ring
    have hPaeq : (∏ j ∈ Finset.range i, (((n:ℤ)+(R:ℤ)) - (j:ℤ)*(q:ℤ)))
        = ∏ j ∈ Finset.range i, (((n:ℤ) - (j:ℤ)*(q:ℤ)) + (R:ℤ)) := by
      apply Finset.prod_congr rfl
      intro j hj
      ring
    have hcombine : ((i.factorial : ℝ) * qR^i) *
        ((Work.BMF.binP i).eval (((n:ℝ)+Rr)/qR) - (Work.BMF.binP i).eval ((n:ℝ)/qR))
        = ((i.factorial : ℝ) * qR^i) * ((s:ℝ) * (M:ℝ)) := by
      rw [hscale, hcastA, hcastB, ← Int.cast_sub, hPaeq, hM, hRdef, hs]
      rw [hqR]
      push_cast
      ring
    have hfac0 : ((i.factorial : ℝ) * qR^i) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast Nat.factorial_ne_zero i
      · exact pow_ne_zero _ hqR0
    refine ⟨c i * (s * M), ?_⟩
    have hΔeq : (Work.BMF.binP i).eval (((n:ℝ)+Rr)/qR) - (Work.BMF.binP i).eval ((n:ℝ)/qR)
        = ((s*M : ℤ) : ℝ) := by
      have := mul_left_cancel₀ hfac0 hcombine
      rw [this]
      push_cast
      ring
    rw [hΔeq]
    push_cast
    ring
  -- assemble
  let w : ℕ → ℤ := fun i => if h : i ∈ Finset.range (k+1) then Classical.choose (hΔ i h) else 0
  have hw : ∀ i ∈ Finset.range (k+1),
      (c i : ℝ) * ((Work.BMF.binP i).eval (((n:ℝ)+Rr)/qR)
          - (Work.BMF.binP i).eval ((n:ℝ)/qR)) = (w i : ℝ) := by
    intro i hi
    simp only [w, dite_eq_left hi]
    exact Classical.choose_spec (hΔ i hi)
  refine ⟨∑ i ∈ Finset.range (k+1), w i, ?_⟩
  rw [hdiff, Int.cast_sum]
  exact Finset.sum_congr rfl fun i hi => hw i hi

/-- **Periodicity of `n ↦ e(-γ(n))`** for `γ` integral on `qℤ` of degree `≤ k`: the period
`k!·q^k` works, and the function is 1-bounded.  (MRTTZ: "the function `e(-γ(n))` is periodic
modulo `q₀`".) -/
theorem eC_periodic {k q : ℕ} (hq : 1 ≤ q) {γ : Polynomial ℝ} (hdeg : γ.natDegree ≤ k)
    (hint : Work.BMF.IntegralOn (q : ℝ) γ) :
    Work.BMF.IsPeriodicBdd (k.factorial * q ^ k)
      (fun n : ℕ => Work.BMF.eC (-(γ.eval (n : ℝ)))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.mul_pos (Nat.factorial_pos k) (pow_pos (by omega : 0 < q) k)
  · intro n
    obtain ⟨m, hm⟩ := eval_period_int hq hdeg hint n
    change Work.BMF.eC (-(γ.eval (((n + k.factorial * q ^ k : ℕ) : ℝ))))
      = Work.BMF.eC (-(γ.eval (n : ℝ)))
    have hnR : (((n + k.factorial * q ^ k : ℕ) : ℝ))
        = (n:ℝ) + ((k.factorial * q ^ k : ℕ) : ℝ) := by push_cast; ring
    have harg : -(γ.eval ((n:ℝ) + ((k.factorial * q ^ k : ℕ) : ℝ)))
        = -(γ.eval (n:ℝ)) - (m:ℝ) := by
      rw [show γ.eval ((n:ℝ) + ((k.factorial * q ^ k : ℕ) : ℝ))
            = γ.eval (n:ℝ) + (m:ℝ) by linarith]
      ring
    rw [hnR, harg, eC_sub_int]
  · intro n
    rw [eC_norm]

end Work.N8
