import Mathlib
import Submission.Work.TMC14Core.Rat
import Submission.Work.TMC14Core.exists_coprime_reduce
import Submission.Work.TMComp.RotBasics.Defs

/-!
# TMC14Core: reduction of `p/q` to lowest terms for the trace hypothesis

`hyps_reduce` removes the coprimality hypothesis from the rational-approximant
statements: given that

  `∀ E ∈ Ioo a b, ∃ θ, ‖trAq p q lam (E:ℂ) θ‖ ≤ 2`

for an arbitrary pair `(p,q)` (`q ≥ 1`), there is a pair `(p',q')` in lowest terms with
`q' = q / gcd p q`, `p'/q' = p/q`, and the *same* hypothesis.

The mathematical content is the classical `SL₂` trace fact: for `A` a `2×2` matrix with
`det A = 1` and **real** trace `t`, the traces of the powers satisfy the Chebyshev
recurrence `tr A^{n+2} = t·tr A^{n+1} - tr A^n`, `tr A^0 = 2`, `tr A^1 = t`; if `|t| > 2`
the sequence grows monotonically with growth rate `t` (resp. `-t` after the sign flip
`(-1)^n`), so `|tr A^m| > 2` for every `m ≥ 1`.  Hence `|tr A^m| ≤ 2 ⟹ |tr A| ≤ 2`.
-/

noncomputable section

namespace Work.TMC14Core

/-! ## 1. The real cocycle behind `trAq` -/

theorem tmR_map_ofRealHom (lam E x : ℝ) :
    (Work.TMContract.tmR lam E x).map Complex.ofRealHom = tmC lam (E : ℂ) x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tmC, Work.TMContract.tmR, Complex.ofRealHom]

theorem iterR_map_ofRealHom (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    (Work.TMComp.RotBasics.iterR α lam E n x).map Complex.ofRealHom
      = iterC α lam (E : ℂ) n x := by
  induction n with
  | zero =>
    simp only [iterC, Work.TMComp.RotBasics.iterR]
    exact Matrix.map_one Complex.ofRealHom (map_zero _) (map_one _)
  | succ n ih =>
    simp only [iterC, Work.TMComp.RotBasics.iterR]
    rw [Matrix.map_mul, tmR_map_ofRealHom, ih]

theorem trAq_norm_eq_iterR_trace (p : ℤ) (q : ℕ) (lam E θ : ℝ) :
    ‖trAq p q lam (E : ℂ) θ‖
      = |(Work.TMComp.RotBasics.iterR ((p : ℝ) / (q : ℝ)) lam E q θ).trace| := by
  have h := iterR_map_ofRealHom ((p : ℝ) / (q : ℝ)) lam E q θ
  have htr : trAq p q lam (E : ℂ) θ
      = ((Work.TMComp.RotBasics.iterR ((p : ℝ) / (q : ℝ)) lam E q θ).trace : ℂ) := by
    rw [trAq, ← Matrix.trace_fin_two, ← h]
    exact (AddMonoidHom.map_trace Complex.ofRealHom _).symm
  rw [htr]
  exact RCLike.norm_ofReal _

/-! ## 2. The real cocycle: periodicity, cocycle identity and powers -/

theorem iterR_zero_rfl (α lam E : ℝ) (x : ℝ) :
    Work.TMComp.RotBasics.iterR α lam E 0 x = 1 := rfl

theorem iterR_succ_rfl (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    Work.TMComp.RotBasics.iterR α lam E (n + 1) x
      = Work.TMContract.tmR lam E (x + (n : ℝ) * α)
        * Work.TMComp.RotBasics.iterR α lam E n x := rfl

theorem iterR_det (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    (Work.TMComp.RotBasics.iterR α lam E n x).det = 1 := by
  induction n with
  | zero => exact Matrix.det_one
  | succ n ih =>
    rw [iterR_succ_rfl, Matrix.det_mul, ih, mul_one]
    simp [Work.TMContract.tmR, Matrix.det_fin_two]

theorem tmR_add_one (lam E x : ℝ) :
    Work.TMContract.tmR lam E (x + 1) = Work.TMContract.tmR lam E x := by
  have h : Real.cos (2 * Real.pi * (x + 1)) = Real.cos (2 * Real.pi * x) := by
    have h2 : 2 * Real.pi * (x + 1) = 2 * Real.pi * x + (1 : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [h2, Real.cos_add_int_mul_two_pi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Work.TMContract.tmR, h]

theorem iterR_add_one (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    Work.TMComp.RotBasics.iterR α lam E n (x + 1)
      = Work.TMComp.RotBasics.iterR α lam E n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterR_succ_rfl, iterR_succ_rfl, ih]
    congr 1
    rw [show x + 1 + (n : ℝ) * α = (x + (n : ℝ) * α) + 1 by ring]
    exact tmR_add_one lam E (x + (n : ℝ) * α)

theorem iterR_add_int (α lam E : ℝ) (n : ℕ) (k : ℤ) (x : ℝ) :
    Work.TMComp.RotBasics.iterR α lam E n (x + (k : ℝ))
      = Work.TMComp.RotBasics.iterR α lam E n x := by
  have hper : Function.Periodic (fun y : ℝ => Work.TMComp.RotBasics.iterR α lam E n y) 1 :=
    fun y => iterR_add_one α lam E n y
  simpa using (hper.int_mul k) x

theorem iterR_add (α lam E : ℝ) (a b : ℕ) (x : ℝ) :
    Work.TMComp.RotBasics.iterR α lam E (a + b) x
      = Work.TMComp.RotBasics.iterR α lam E a (x + (b : ℝ) * α)
        * Work.TMComp.RotBasics.iterR α lam E b x := by
  induction a generalizing x with
  | zero => simp [iterR_zero_rfl]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by ring, iterR_succ_rfl, ih, iterR_succ_rfl]
    rw [show x + ((a + b : ℕ) : ℝ) * α = x + (b : ℝ) * α + (a : ℝ) * α by push_cast; ring,
      mul_assoc]

theorem iterR_mul_pow (α lam E : ℝ) (n m : ℕ) (k : ℤ) (hk : (n : ℝ) * α = (k : ℝ)) (x : ℝ) :
    Work.TMComp.RotBasics.iterR α lam E (m * n) x
      = (Work.TMComp.RotBasics.iterR α lam E n x) ^ m := by
  induction m with
  | zero => simp [iterR_zero_rfl]
  | succ m ih =>
    rw [show (m + 1) * n = n + m * n by ring, iterR_add, ih]
    have hx : Work.TMComp.RotBasics.iterR α lam E n (x + ((m * n : ℕ) : ℝ) * α)
        = Work.TMComp.RotBasics.iterR α lam E n x := by
      have harg : ((m * n : ℕ) : ℝ) * α = (((m : ℤ) * k : ℤ) : ℝ) := by
        rw [show ((m * n : ℕ) : ℝ) = (m : ℝ) * (n : ℝ) by push_cast; ring]
        rw [mul_assoc, hk]
        push_cast
        ring
      rw [harg]
      exact iterR_add_int α lam E n ((m : ℤ) * k) x
    rw [hx, pow_succ']

/-! ## 3. The `SL₂` trace lemma -/

theorem sl2_sq (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) :
    A ^ 2 = A.trace • A - 1 := by
  have h : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.sub_apply, Matrix.smul_apply] <;>
    linarith [h]

theorem trace_pow_rec (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (n : ℕ) :
    (A ^ (n + 2)).trace = A.trace * (A ^ (n + 1)).trace - (A ^ n).trace := by
  have h2 : A ^ (n + 2) = A.trace • (A ^ (n + 1)) - A ^ n := by
    calc A ^ (n + 2) = A ^ n * A ^ 2 := by rw [pow_add]
      _ = A ^ n * (A.trace • A - 1) := by rw [sl2_sq A hdet]
      _ = A.trace • (A ^ n * A) - A ^ n := by
            rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
      _ = A.trace • (A ^ (n + 1)) - A ^ n := by rw [pow_succ]
  rw [h2, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]

theorem seq_growth (t : ℝ) (ht : 2 < t) (v : ℕ → ℝ) (h0 : v 0 = 2) (h1 : v 1 = t)
    (hrec : ∀ n, v (n + 2) = t * v (n + 1) - v n) :
    ∀ m : ℕ, 1 ≤ m → 2 < v m := by
  have key : ∀ n : ℕ, 2 < v (n + 1) ∧ v n < v (n + 1) := by
    intro n
    induction n with
    | zero =>
      constructor
      · simpa [h1] using ht
      · rw [h0, h1]; linarith
    | succ n ih =>
      obtain ⟨h2, h3⟩ := ih
      have h4 : v (n + 2) = t * v (n + 1) - v n := hrec n
      have hp : 0 < v (n + 1) := by linarith
      have hkey : 0 < (t - 2) * v (n + 1) := mul_pos (by linarith) hp
      constructor
      · rw [h4]; nlinarith [h2, h3, hkey, hp]
      · rw [h4]; nlinarith [h2, h3, hkey, hp]
  intro m hm
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  exact (key j).1

theorem seq_abs_growth (t : ℝ) (ht : 2 < |t|) (v : ℕ → ℝ) (h0 : v 0 = 2) (h1 : v 1 = t)
    (hrec : ∀ n, v (n + 2) = t * v (n + 1) - v n) :
    ∀ m : ℕ, 1 ≤ m → 2 < |v m| := by
  intro m hm
  rcases le_or_gt 0 t with hpos | hneg
  · have ht' : 2 < t := by rwa [abs_of_nonneg hpos] at ht
    have h := seq_growth t ht' v h0 h1 hrec m hm
    rwa [abs_of_pos (by linarith)]
  · have ht' : 2 < -t := by
      rw [abs_of_neg hneg] at ht
      linarith
    set w : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * v n with hw
    have hw0 : w 0 = 2 := by simp [hw, h0]
    have hw1 : w 1 = -t := by simp [hw, h1]
    have hrecw : ∀ n, w (n + 2) = (-t) * w (n + 1) - w n := by
      intro n
      have hpow1 : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by rw [pow_succ]; ring
      have hpow2 : (-1 : ℝ) ^ (n + 2) = -((-1 : ℝ) ^ (n + 1)) := by rw [pow_succ]; ring
      simp only [hw]
      rw [hrec n, hpow2, hpow1]
      ring
    have h := seq_growth (-t) ht' w hw0 hw1 hrecw m hm
    have habs : |w m| = |v m| := by
      simp only [hw, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hposw : 0 < w m := by linarith
    have h2 : 2 < |w m| := by
      rw [abs_of_pos hposw]
      exact h
    rw [habs] at h2
    exact h2

theorem trace_abs_pow_growth (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1)
    (ht : 2 < |A.trace|) : ∀ n : ℕ, 1 ≤ n → 2 < |(A ^ n).trace| := by
  intro n hn
  have h0 : (fun k : ℕ => (A ^ k).trace) 0 = 2 := by
    simp
  have h1 : (fun k : ℕ => (A ^ k).trace) 1 = A.trace := by simp
  have hrec : ∀ k : ℕ,
      (fun j : ℕ => (A ^ j).trace) (k + 2)
        = A.trace * (fun j : ℕ => (A ^ j).trace) (k + 1)
          - (fun j : ℕ => (A ^ j).trace) k :=
    fun k => trace_pow_rec A hdet k
  exact seq_abs_growth A.trace ht (fun k : ℕ => (A ^ k).trace) h0 h1 hrec n hn

theorem sl2_trace_pow_reduce (m : ℕ) (hm : 1 ≤ m) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hdet : A.det = 1) (h : |(A ^ m).trace| ≤ 2) : |A.trace| ≤ 2 := by
  by_contra hcon
  rw [not_le] at hcon
  exact absurd (trace_abs_pow_growth A hdet hcon m hm) (not_lt.mpr h)

/-! ## 4. The reduction -/

set_option linter.unusedVariables false in
theorem hyps_reduce (p : ℤ) (q : ℕ) (lam : ℝ) (hlam : 0 < lam) (hq : 1 ≤ q) (a b : ℝ)
    (H : ∀ E ∈ Set.Ioo a b, ∃ θ : ℝ, ‖Work.TMC14Core.trAq p q lam (E : ℂ) θ‖ ≤ 2) :
    ∃ p' : ℤ, ∃ q' : ℕ, 1 ≤ q' ∧ Nat.Coprime p'.natAbs q' ∧
      (q' : ℝ) = ((q / Nat.gcd p.natAbs q : ℕ) : ℝ) ∧
      (p' : ℝ) / (q' : ℝ) = (p : ℝ) / (q : ℝ) ∧
      (∀ E ∈ Set.Ioo a b, ∃ θ : ℝ, ‖Work.TMC14Core.trAq p' q' lam (E : ℂ) θ‖ ≤ 2) := by
  obtain ⟨p', q', hq'1, hcop, hq'eq, hfreq⟩ := exists_coprime_reduce p q hq
  refine ⟨p', q', hq'1, hcop, hq'eq, hfreq, ?_⟩
  set g : ℕ := Nat.gcd p.natAbs q with hg
  have hgpos : 0 < g := by
    rw [hg]; exact Nat.gcd_pos_of_pos_right p.natAbs (by omega)
  have hgdvdq : g ∣ q := by rw [hg]; exact Nat.gcd_dvd_right p.natAbs q
  have hq'val : q' = q / g := by exact_mod_cast hq'eq
  have hqeq : q = g * q' := by rw [hq'val]; exact (Nat.mul_div_cancel' hgdvdq).symm
  have hg1 : 1 ≤ g := hgpos
  have hk : (q' : ℝ) * ((p' : ℝ) / (q' : ℝ)) = (p' : ℝ) := by
    have hne : (q' : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast (show 0 < q' by omega)
      exact ne_of_gt this
    field_simp
  intro E hE
  obtain ⟨θ, hθ⟩ := H E hE
  refine ⟨θ, ?_⟩
  rw [trAq_norm_eq_iterR_trace p q lam E θ] at hθ
  rw [trAq_norm_eq_iterR_trace p' q' lam E θ]
  rw [← hfreq, hqeq] at hθ
  have hpow := iterR_mul_pow ((p' : ℝ) / (q' : ℝ)) lam E q' g p' hk θ
  rw [hpow] at hθ
  have hdet : (Work.TMComp.RotBasics.iterR ((p' : ℝ) / (q' : ℝ)) lam E q' θ).det = 1 :=
    iterR_det ((p' : ℝ) / (q' : ℝ)) lam E q' θ
  exact sl2_trace_pow_reduce g hg1 _ hdet hθ

end Work.TMC14Core
