import Mathlib
import Submission.Work.TMC14Core.Weyl

/-!
# TMC14Core: the word expansion of `B ^ n` and the resulting trace identities.
-/

open Matrix

noncomputable section

namespace Work.TMC14Core

/-- Noncommutative version of `Fintype.sum_pow`. -/
theorem sum_pow_monoid {α M : Type*} [Fintype α] [DecidableEq α] [Semiring M]
    (L : α → M) (n : ℕ) :
    (∑ x, L x) ^ n = ∑ f : Fin n → α, (List.ofFn (fun i => L (f i))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) => α))
        (fun g : Fin (n + 1) → α => (List.ofFn (fun i => L (g i))).prod)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun f _ => ?_))
    rw [show (Fin.snocEquiv (fun _ : Fin (n + 1) => α)) (x, f) = Fin.snoc f x from rfl]
    rw [List.ofFn_succ', List.prod_concat]
    simp



/-- `B = U + U† + λ(V + V†)`. -/
def wB (p : ℤ) (q : ℕ) (lam θ k : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  wU q k + star (wU q k) + (lam : ℂ) • (wV p q θ + star (wV p q θ))

/-- The weighted Weyl letters: `U, U†` carry coefficient `1`, `V, V†` coefficient `λ`. -/
def wL (p : ℤ) (q : ℕ) (lam : ℝ) (θ k : ℝ) (x : Bool × Bool) : Matrix (Fin q) (Fin q) ℂ :=
  (if x.1 then (1 : ℂ) else (lam : ℂ)) • letterOf p q θ k x

theorem wB_eq_sum (p : ℤ) (q : ℕ) (lam θ k : ℝ) :
    wB p q lam θ k = ∑ x : Bool × Bool, wL p q lam θ k x := by
  simp only [wB, wL, letterOf, Fintype.sum_prod_type, Fintype.sum_bool, Prod.mk.eta]
  simp only [reduceIte, one_smul]
  rw [smul_add]
  ac_rfl

theorem wB_pow (p : ℤ) (q : ℕ) (lam θ k : ℝ) (n : ℕ) :
    wB p q lam θ k ^ n = ∑ f : Fin n → Bool × Bool,
      (List.ofFn (fun i => wL p q lam θ k (f i))).prod := by
  rw [wB_eq_sum]
  exact sum_pow_monoid (wL p q lam θ k) n

/-- Product of scaled matrices along a list. -/
theorem list_prod_smul {q : ℕ} {ι : Type*} (l : List ι) (c : ι → ℂ)
    (A : ι → Matrix (Fin q) (Fin q) ℂ) :
    (l.map (fun i => c i • A i)).prod = (l.map c).prod • (l.map A).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ih, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_comm]

/-- The product of the coefficients of a word is `λ` to the number of `V`-type letters. -/
theorem coeff_list_prod (lam : ℂ) (n : ℕ) (f : Fin n → Bool × Bool) :
    (List.map (fun x : Bool × Bool => if x.1 then (1 : ℂ) else lam) (List.ofFn f)).prod
      = lam ^ ((Finset.univ.filter (fun i : Fin n => ¬ (f i).1)).card) := by
  rw [List.map_ofFn, Fin.prod_ofFn]
  simp only [Function.comp_apply]
  rw [Finset.prod_ite (fun _ : Fin n => (1 : ℂ)) (fun _ : Fin n => lam),
    Finset.prod_const_one, one_mul, Finset.prod_eq_pow_card (fun _ _ => rfl)]

/-- Every weighted word equals its coefficient times the plain word product. -/
theorem wP_eq (p : ℤ) (q : ℕ) (lam θ k : ℝ) (n : ℕ) (f : Fin n → Bool × Bool) :
    (List.ofFn (fun i => wL p q lam θ k (f i))).prod
      = ((lam : ℂ) ^ ((Finset.univ.filter (fun i : Fin n => ¬ (f i).1)).card))
          • wordProd p q θ k n f := by
  have h1 : (List.ofFn (fun i => wL p q lam θ k (f i))).prod
      = ((List.ofFn f).map (fun x : Bool × Bool => wL p q lam θ k x)).prod := by
    rw [List.map_ofFn]
    rfl
  rw [h1]
  have h2 : (fun x : Bool × Bool => wL p q lam θ k x)
      = fun x => (if x.1 then (1 : ℂ) else (lam : ℂ)) • letterOf p q θ k x := rfl
  rw [h2, list_prod_smul, coeff_list_prod]
  rfl

theorem mod_eq_of_lt_two {q x y : ℕ} (hx : x < q) (hy : y < 2 * q) (h : x % q = y % q) :
    y = x ∨ y = x + q := by
  have hy' : y % q = if q ≤ y then y - q else y := by
    split_ifs with hq
    · conv_lhs => rw [show y = q + (y - q) by omega]
      rw [Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    · exact Nat.mod_eq_of_lt (by omega)
  rw [Nat.mod_eq_of_lt hx, hy'] at h
  split_ifs at h with hq <;> omega

theorem mod_of_dvd {a b m q : ℕ} (h : (q : ℤ) ∣ ((a : ℤ) - (b : ℤ) - (m : ℤ))) :
    a % q = (b + m) % q := by
  have h1 : (q : ℤ) ∣ ((a : ℤ) - ((b + m : ℕ) : ℤ)) := by
    rw [show ((b + m : ℕ) : ℤ) = (b : ℤ) + (m : ℤ) by push_cast; ring, ← sub_sub]
    exact h
  exact ((Nat.modEq_iff_dvd).mpr (by simpa using h1)).symm

theorem count_ge (a b m q : ℕ) (hq : q = 2*m+1) (h : a % q = (b + m) % q) (h2 : a + b ≤ q - 2) :
    m ≤ a + b := by
  have ha : a < q := by omega
  have hbm : b + m < 2 * q := by omega
  rcases mod_eq_of_lt_two ha hbm h with hy | hy <;> omega

theorem count_eq (a b c e m q : ℕ) (hq : q = 2*m+1) (h1 : a + b + c + e = q - 1)
    (ha : a % q = (b + m) % q) (hc : c % q = (e + m) % q) :
    a = m ∧ b = 0 ∧ c = m ∧ e = 0 := by
  have ha' : a < q := by omega
  have hbm : b + m < 2 * q := by omega
  have hc' : c < q := by omega
  have hem : e + m < 2 * q := by omega
  rcases mod_eq_of_lt_two ha' hbm ha with hy | hy <;>
    rcases mod_eq_of_lt_two hc' hem hc with hz | hz <;> omega

theorem cnt_sum (n : ℕ) (f : Fin n → Bool × Bool) :
    cnt true true n f + cnt true false n f + cnt false true n f + cnt false false n f = n := by
  have h : (∑ x : Bool × Bool, cnt x.1 x.2 n f) = n := by
    have h' : (∑ x : Bool × Bool, cnt x.1 x.2 n f)
        = ∑ x : Bool × Bool, ∑ i : Fin n, (if f i = x then (1 : ℕ) else 0) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [cnt, Finset.card_filter]
    rw [h', Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  have h2 : (∑ x : Bool × Bool, cnt x.1 x.2 n f)
      = cnt true true n f + cnt true false n f + cnt false true n f + cnt false false n f := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    ring
  rw [← h2]; exact h

theorem wU_pow_mul_star_pow (q : ℕ) (k : ℝ) (hq : 0 < q) (m : ℕ) :
    wU q k ^ m * star (wU q k) ^ m = 1 := by
  have hU : wU q k * star (wU q k) = 1 :=
    (Matrix.mem_unitaryGroup_iff).mp (wU_mem_unitaryGroup q k hq)
  have h1 : ∀ j : ℕ, wU q k * star (wU q k) ^ (j + 1) = star (wU q k) ^ j := by
    intro j
    induction j with
    | zero => simpa using hU
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, ← pow_succ]
  induction m with
  | zero => simp
  | succ m ih =>
    calc wU q k ^ (m + 1) * star (wU q k) ^ (m + 1)
        = wU q k ^ m * (wU q k * (star (wU q k) ^ m * star (wU q k))) := by
          rw [pow_succ, pow_succ, mul_assoc]
      _ = wU q k ^ m * (wU q k * star (wU q k) ^ (m + 1)) := by rw [pow_succ]
      _ = wU q k ^ m * star (wU q k) ^ m := by rw [h1 m]
      _ = 1 := ih

theorem star_wV (p : ℤ) (q : ℕ) (θ : ℝ) :
    star (wV p q θ) = Matrix.diagonal (fun i => star (wVd p q θ i)) := by
  rw [Matrix.star_eq_conjTranspose, wV, Matrix.diagonal_conjTranspose]
  congr 1

theorem wV_pow_mul_star_pow (p : ℤ) (q : ℕ) (θ : ℝ) (m : ℕ) :
    wV p q θ ^ m * star (wV p q θ) ^ m = 1 := by
  have hpow : ∀ k : ℕ, wV p q θ ^ k = Matrix.diagonal (fun i => wVd p q θ i ^ k) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero]
      ext i j
      rw [Matrix.one_apply, Matrix.diagonal_apply]
      by_cases h : i = j <;> simp [h]
    | succ k ih =>
      rw [pow_succ, ih, wV]
      ext i j
      rw [Matrix.diagonal_mul, Matrix.diagonal_apply, Matrix.diagonal_apply]
      by_cases h : i = j
      · rw [if_pos h, if_pos h, pow_succ]
      · rw [if_neg h, if_neg h, mul_zero]
  have hpow' : ∀ k : ℕ, star (wV p q θ) ^ k
      = Matrix.diagonal (fun i => star (wVd p q θ i) ^ k) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero]
      ext i j
      rw [Matrix.one_apply, Matrix.diagonal_apply]
      by_cases h : i = j <;> simp [h]
    | succ k ih =>
      rw [pow_succ, ih, star_wV]
      ext i j
      rw [Matrix.diagonal_mul, Matrix.diagonal_apply, Matrix.diagonal_apply]
      by_cases h : i = j
      · rw [if_pos h, if_pos h, pow_succ]
      · rw [if_neg h, if_neg h, mul_zero]
  rw [hpow m, hpow' m]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, ← mul_pow, wVd_mul_conj, one_pow]
  · rw [if_neg h, if_neg h, mul_zero]


theorem interleave_card (m : ℕ) (f : Fin (2*m) → Bool × Bool)
    (h1 : ∀ i, f i = (true,true) ∨ f i = (false,true)) :
    (Finset.univ.filter (fun i : Fin (2*m) => f i = (false,true))).card
      + (Finset.univ.filter (fun i : Fin (2*m) => f i = (true,true))).card = 2*m := by
  have hA : (Finset.univ.filter (fun i : Fin (2*m) => f i = (true,true)))
      = (Finset.univ.filter (fun i : Fin (2*m) => (f i).1)) := by
    refine Finset.filter_congr (fun i _ => ?_)
    rcases h1 i with h | h <;> simp [h]
  have hB : (Finset.univ.filter (fun i : Fin (2*m) => f i = (false,true)))
      = (Finset.univ.filter (fun i : Fin (2*m) => ¬ (f i).1)) := by
    refine Finset.filter_congr (fun i _ => ?_)
    rcases h1 i with h | h <;> simp [h]
  rw [hA, hB]
  have hcf := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2*m)))) (p := fun i => (f i).1)
  rw [Finset.card_univ, Fintype.card_fin] at hcf
  omega

theorem vcount_of_interleave (m : ℕ) (f : Fin (2*m) → Bool × Bool)
    (h1 : ∀ i, f i = (true,true) ∨ f i = (false,true))
    (h2 : (Finset.univ.filter (fun i : Fin (2*m) => f i = (true,true))).card = m) :
    (Finset.univ.filter (fun i : Fin (2*m) => ¬ (f i).1)).card = m := by
  have hvc : (Finset.univ.filter (fun i : Fin (2*m) => ¬ (f i).1))
      = (Finset.univ.filter (fun i : Fin (2*m) => f i = (false,true))) := by
    refine Finset.filter_congr (fun i _ => ?_)
    rcases h1 i with h | h <;> simp [h]
  rw [hvc]
  have := interleave_card m f h1
  omega

theorem word_trace_eq (p : ℤ) (q m : ℕ) (θ k : ℝ) (n : ℕ) (f : Fin n → Bool × Bool) (u : ℂ)
    (hNF : wordProd p q θ k n f = u • ((wV p q θ) ^ (cnt false true n f) *
        (star (wV p q θ)) ^ (cnt false false n f) * (wU q k) ^ (cnt true true n f) *
        (star (wU q k)) ^ (cnt true false n f))) :
    (wordProd p q θ k n f * ((star (wU q k)) ^ m * (star (wV p q θ)) ^ m)).trace
      = u * (((((wV p q θ) ^ (cnt false true n f) * (star (wV p q θ)) ^ (cnt false false n f) *
          (wU q k) ^ (cnt true true n f) * (star (wU q k)) ^ (cnt true false n f)) *
          (star (wU q k)) ^ m) * (star (wV p q θ)) ^ m).trace) := by
  rw [hNF, Matrix.smul_mul, Matrix.trace_smul]
  simp only [mul_assoc, smul_eq_mul]

theorem trace_pow_eq_zero (p : ℤ) (q m : ℕ) (hm : q = 2*m+1) (hpq : Nat.Coprime p.natAbs q)
    (lam θ k : ℝ) (n : ℕ) (hn : n + 1 < q)
    (hNF : ∀ f : Fin n → Bool × Bool, ∃ u : ℂ, u ≠ 0 ∧ wordProd p q θ k n f = u •
        ((wV p q θ) ^ (cnt false true n f) * (star (wV p q θ)) ^ (cnt false false n f) *
         (wU q k) ^ (cnt true true n f) * (star (wU q k)) ^ (cnt true false n f)))
    (hTR : ∀ a b c e : ℕ, (¬ ((q : ℤ) ∣ ((a : ℤ) - (b : ℤ) - (m : ℤ))) ∨
        ¬ ((q : ℤ) ∣ ((c : ℤ) - (e : ℤ) - (m : ℤ)))) →
        ((((wV p q θ) ^ a * (star (wV p q θ)) ^ b * (wU q k) ^ c * (star (wU q k)) ^ e) *
          (star (wU q k)) ^ m) * (star (wV p q θ)) ^ m).trace = 0) :
    (wB p q lam θ k ^ n * ((star (wU q k)) ^ m * (star (wV p q θ)) ^ m)).trace = 0 := by
  rw [wB_pow, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_eq_zero (fun f _ => ?_)
  obtain ⟨u, hu, hNFf⟩ := hNF f
  rw [wP_eq, Matrix.smul_mul, Matrix.trace_smul, word_trace_eq p q m θ k n f u hNFf]
  have hsum := cnt_sum n f
  have hcond : ¬ ((q : ℤ) ∣ (((cnt false true n f : ℕ) : ℤ)
        - ((cnt false false n f : ℕ) : ℤ) - (m : ℤ))) ∨
      ¬ ((q : ℤ) ∣ (((cnt true true n f : ℕ) : ℤ)
        - ((cnt true false n f : ℕ) : ℤ) - (m : ℤ))) := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    have h1' := count_ge (cnt false true n f) (cnt false false n f) m q hm
      (mod_of_dvd h1) (by omega)
    have h2' := count_ge (cnt true true n f) (cnt true false n f) m q hm
      (mod_of_dvd h2) (by omega)
    omega
  rw [hTR _ _ _ _ hcond]
  simp

theorem trace_pow_eq_top (p : ℤ) (q m : ℕ) (hm : q = 2*m+1) (hpq : Nat.Coprime p.natAbs q)
    (lam θ k : ℝ)
    (hNF : ∀ f : Fin (2*m) → Bool × Bool, ∃ u : ℂ, u ≠ 0 ∧ wordProd p q θ k (2*m) f = u •
        ((wV p q θ) ^ (cnt false true (2*m) f) * (star (wV p q θ)) ^ (cnt false false (2*m) f) *
         (wU q k) ^ (cnt true true (2*m) f) * (star (wU q k)) ^ (cnt true false (2*m) f)))
    (hTR : ∀ a b c e : ℕ, (¬ ((q : ℤ) ∣ ((a : ℤ) - (b : ℤ) - (m : ℤ))) ∨
        ¬ ((q : ℤ) ∣ ((c : ℤ) - (e : ℤ) - (m : ℤ)))) →
        ((((wV p q θ) ^ a * (star (wV p q θ)) ^ b * (wU q k) ^ c * (star (wU q k)) ^ e) *
          (star (wU q k)) ^ m) * (star (wV p q θ)) ^ m).trace = 0)
    (hIL : ∀ f : Fin (2*m) → Bool × Bool,
        ((∀ i, f i = (true,true) ∨ f i = (false,true)) ∧
          (Finset.univ.filter (fun i : Fin (2*m) => f i = (true,true))).card = m) →
        wordProd p q θ k (2*m) f = (om p q) ^ (invCount (2*m) f) •
          ((wV p q θ) ^ m * (wU q k) ^ m))
    (hIS : ∑ f ∈ (Finset.univ : Finset (Fin (2*m) → Bool × Bool)).filter
          (fun f => (∀ i, f i = (true,true) ∨ f i = (false,true)) ∧
            (Finset.univ.filter (fun i : Fin (2*m) => f i = (true,true))).card = m),
        (om p q) ^ (invCount (2*m) f) = (-1)^m * (om p q) ^ (m * (3*m+1) / 2)) :
    (wB p q lam θ k ^ (2*m) * ((star (wU q k)) ^ m * (star (wV p q θ)) ^ m)).trace
      = (q : ℂ) * (lam : ℂ) ^ m * ((-1)^m * (om p q) ^ (m * (3*m+1) / 2)) := by
  rw [wB_pow, Finset.sum_mul, Matrix.trace_sum]
  have hterm : ∀ f : Fin (2*m) → Bool × Bool,
      (((List.ofFn (fun i => wL p q lam θ k (f i))).prod) *
        ((star (wU q k)) ^ m * (star (wV p q θ)) ^ m)).trace
      = (if ((∀ i, f i = (true,true) ∨ f i = (false,true)) ∧
            (Finset.univ.filter (fun i : Fin (2*m) => f i = (true,true))).card = m)
          then (lam : ℂ) ^ m * (((om p q) ^ (invCount (2*m) f)) * (q : ℂ)) else 0) := by
    intro f
    by_cases hf : ((∀ i, f i = (true,true) ∨ f i = (false,true)) ∧
            (Finset.univ.filter (fun i : Fin (2*m) => f i = (true,true))).card = m)
    · rw [if_pos hf, wP_eq]
      have hvc := vcount_of_interleave m f hf.1 hf.2
      rw [hvc, Matrix.smul_mul, Matrix.trace_smul, hIL f hf]
      rw [Matrix.smul_mul, Matrix.trace_smul]
      have hW : (wV p q θ ^ m * wU q k ^ m) *
          ((star (wU q k)) ^ m * (star (wV p q θ)) ^ m) = 1 := by
        rw [show (wV p q θ ^ m * wU q k ^ m) *
              ((star (wU q k)) ^ m * (star (wV p q θ)) ^ m)
            = wV p q θ ^ m * ((wU q k ^ m * (star (wU q k)) ^ m) * (star (wV p q θ)) ^ m)
          from by simp only [mul_assoc],
          wU_pow_mul_star_pow q k (by omega) m, one_mul, wV_pow_mul_star_pow]
      rw [hW, Matrix.trace_one, Fintype.card_fin]
      ring
    · rw [if_neg hf, wP_eq, Matrix.smul_mul, Matrix.trace_smul]
      obtain ⟨u, hu, hNFf⟩ := hNF f
      rw [word_trace_eq p q m θ k (2*m) f u hNFf]
      have hsum := cnt_sum (2*m) f
      have hcond : ¬ ((q : ℤ) ∣ (((cnt false true (2*m) f : ℕ) : ℤ)
            - ((cnt false false (2*m) f : ℕ) : ℤ) - (m : ℤ))) ∨
          ¬ ((q : ℤ) ∣ (((cnt true true (2*m) f : ℕ) : ℤ)
            - ((cnt true false (2*m) f : ℕ) : ℤ) - (m : ℤ))) := by
        by_contra hc
        push_neg at hc
        obtain ⟨h1, h2⟩ := hc
        have h1' := mod_of_dvd h1
        have h2' := mod_of_dvd h2
        obtain ⟨ha, hb, hc, he⟩ := count_eq (cnt false true (2*m) f) (cnt false false (2*m) f)
          (cnt true true (2*m) f) (cnt true false (2*m) f) m q hm (by omega) h1' h2'
        simp only [cnt] at hb he
        apply hf
        constructor
        · intro i
          have h1n : f i ≠ (false, false) := by
            intro hfi
            have hmem : i ∈ (Finset.univ.filter (fun j : Fin (2*m) => f j = (false,false))) := by
              simp [hfi]
            rw [Finset.card_eq_zero.mp hb] at hmem
            exact absurd hmem (by simp)
          have h2n : f i ≠ (true, false) := by
            intro hfi
            have hmem : i ∈ (Finset.univ.filter (fun j : Fin (2*m) => f j = (true,false))) := by
              simp [hfi]
            rw [Finset.card_eq_zero.mp he] at hmem
            exact absurd hmem (by simp)
          rcases hfi : f i with ⟨b1, b2⟩
          cases b1 <;> cases b2 <;> simp_all
        · exact hc
      rw [hTR _ _ _ _ hcond]
      simp
  rw [Finset.sum_congr rfl (fun f _ => hterm f)]
  rw [← Finset.sum_filter, ← Finset.mul_sum, ← Finset.sum_mul, hIS]
  ring


theorem ceyTraceOdd_cond (p : ℤ) (q m : ℕ) (hm : q = 2*m+1) (hpq : Nat.Coprime p.natAbs q)
    (lam θ k : ℝ) (z : ℂ)
    (hWN : ∀ n : ℕ, ∀ f : Fin n → Bool × Bool, ∃ u : ℂ, u ≠ 0 ∧ wordProd p q θ k n f = u •
        ((wV p q θ) ^ (cnt false true n f) * (star (wV p q θ)) ^ (cnt false false n f) *
         (wU q k) ^ (cnt true true n f) * (star (wU q k)) ^ (cnt true false n f)))
    (hTR : ∀ a b c e : ℕ, (¬ ((q : ℤ) ∣ ((a : ℤ) - (b : ℤ) - (m : ℤ))) ∨
        ¬ ((q : ℤ) ∣ ((c : ℤ) - (e : ℤ) - (m : ℤ)))) →
        ((((wV p q θ) ^ a * (star (wV p q θ)) ^ b * (wU q k) ^ c * (star (wU q k)) ^ e) *
          (star (wU q k)) ^ m) * (star (wV p q θ)) ^ m).trace = 0)
    (hIL : ∀ f : Fin (2*m) → Bool × Bool,
        ((∀ i, f i = (true,true) ∨ f i = (false,true)) ∧
          (Finset.univ.filter (fun i : Fin (2*m) => f i = (true,true))).card = m) →
        wordProd p q θ k (2*m) f = (om p q) ^ (invCount (2*m) f) •
          ((wV p q θ) ^ m * (wU q k) ^ m))
    (hIS : ∑ f ∈ (Finset.univ : Finset (Fin (2*m) → Bool × Bool)).filter
          (fun f => (∀ i, f i = (true,true) ∨ f i = (false,true)) ∧
            (Finset.univ.filter (fun i : Fin (2*m) => f i = (true,true))).card = m),
        (om p q) ^ (invCount (2*m) f) = (-1)^m * (om p q) ^ (m * (3*m+1) / 2))
    (hAdj : ∀ (B W : Matrix (Fin q) (Fin q) ℂ),
        (∀ n : ℕ, n + 1 < q → ((B ^ n) * W).trace = 0) →
        ∀ z : ℂ, (Matrix.adjugate (z • (1 : Matrix (Fin q) (Fin q) ℂ) - B) * W).trace
          = (B ^ (q - 1) * W).trace)
    (hBl : blochMat p q lam θ k = wB p q lam θ k) :
    ∃ W : Matrix (Fin q) (Fin q) ℂ, W ∈ Matrix.unitaryGroup (Fin q) ℂ ∧
      ‖Matrix.trace (Matrix.adjugate (z • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMat p q lam θ k) * W)‖
        = (q : ℝ) * |lam| ^ m := by
  have hq : 0 < q := by omega
  refine ⟨(star (wU q k)) ^ m * (star (wV p q θ)) ^ m, ?_, ?_⟩
  · have hU : star (wU q k) ∈ Matrix.unitaryGroup (Fin q) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, star_star]
      exact mul_eq_one_comm.mp ((Matrix.mem_unitaryGroup_iff).mp (wU_mem_unitaryGroup q k hq))
    have hV : star (wV p q θ) ∈ Matrix.unitaryGroup (Fin q) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, star_star]
      exact mul_eq_one_comm.mp ((Matrix.mem_unitaryGroup_iff).mp (wV_mem_unitaryGroup p q θ))
    exact mul_mem (pow_mem hU m) (pow_mem hV m)
  · rw [hBl]
    have hzero : ∀ n : ℕ, n + 1 < q → ((wB p q lam θ k ^ n) *
        ((star (wU q k)) ^ m * (star (wV p q θ)) ^ m)).trace = 0 := by
      intro n hn
      exact trace_pow_eq_zero p q m hm hpq lam θ k n hn (fun f => hWN n f) hTR
    rw [hAdj (wB p q lam θ k) _ hzero z]
    have hqm : q - 1 = 2 * m := by omega
    rw [hqm]
    rw [trace_pow_eq_top p q m hm hpq lam θ k (fun f => hWN (2*m) f) hTR hIL hIS]
    have hom : ‖om p q‖ = 1 := by rw [om_eq_wPh]; exact wPh_norm _
    have h1 : ‖((-1 : ℂ) ^ m * (om p q) ^ (m * (3*m+1) / 2))‖ = 1 := by
      rw [norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, hom]
      simp
    have h2 : ‖(q : ℂ)‖ = (q : ℝ) := by
      rw [RCLike.norm_natCast]
    have h3 : ‖((lam : ℂ)) ^ m‖ = |lam| ^ m := by
      rw [norm_pow]
      congr 1
      exact RCLike.norm_ofReal lam
    rw [norm_mul, norm_mul, h1, h2, h3]
    ring

theorem wPh_nat_mul (x : ℝ) (n : ℕ) : wPh ((n : ℝ) * x) = (wPh x) ^ n := by
  induction n with
  | zero => simp [wPh_zero]
  | succ n ih =>
    have h : ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x := by push_cast; ring
    rw [h, wPh_add, ih, pow_succ]

theorem wPh_eq_one_iff (x : ℝ) : wPh x = 1 ↔ ∃ n : ℤ, x = n := by
  have h1 : wPh x = Complex.exp (((2 * Real.pi * x : ℝ)) * Complex.I) := by
    rw [wPh]; congr 1; push_cast; ring
  rw [h1, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have h3 : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = ((n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
      ring
    rw [h3] at hn
    have h4 : (((2 * Real.pi * x : ℝ)) : ℂ) = (n : ℂ) * (2 * Real.pi) :=
      mul_right_cancel₀ Complex.I_ne_zero hn
    refine ⟨n, ?_⟩
    have h5 : 2 * Real.pi * x = (n : ℝ) * (2 * Real.pi) := by
      have := congrArg Complex.re h4
      simpa [Complex.ofReal_re, Complex.ofReal_mul] using this
    have hp : (2 * Real.pi) ≠ 0 := by positivity
    have h6 : (2 * Real.pi) * x = (2 * Real.pi) * (n : ℝ) := by
      rw [h5]; ring
    exact mul_left_cancel₀ hp h6
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    push_cast
    ring

theorem om_pow_q' (p : ℤ) (q : ℕ) : (om p q) ^ q = 1 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp
  · rw [om_eq_wPh, ← wPh_nat_mul]
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have h : (q : ℝ) * ((p : ℝ) / (q : ℝ)) = (p : ℝ) := by field_simp
    rw [h, wPh_int]


theorem om_pow_eq_one_iff (p : ℤ) (q : ℕ) (hpq : Nat.Coprime p.natAbs q) (hq : 0 < q)
    (j : ℕ) : (om p q) ^ j = 1 ↔ q ∣ j := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  constructor
  · intro h
    rw [om_eq_wPh, ← wPh_nat_mul, wPh_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have h5 : (j : ℂ) * ((p : ℂ) / (q : ℂ)) = (n : ℂ) := by
      exact_mod_cast hn
    have h7 : (j : ℂ) * (p : ℂ) = (n : ℂ) * (q : ℂ) := by
      have h' := congrArg (· * (q : ℂ)) h5
      rw [mul_assoc, div_mul_cancel₀ _ hq0] at h'
      exact h'
    have h8 : ((j : ℤ) * p) = (n * (q : ℤ)) := by
      have h' : (((j : ℤ) * p : ℤ) : ℂ) = ((n * (q : ℤ) : ℤ) : ℂ) := by
        push_cast
        rw [h7]
      exact Int.cast_injective h'
    have h9 : (q : ℤ) ∣ (j : ℤ) * (p.natAbs : ℤ) := by
      have hd : (q : ℤ) ∣ (j : ℤ) * p := ⟨n, by rw [mul_comm (q : ℤ) n]; exact h8⟩
      rcases Int.natAbs_eq p with hp | hp
      · rwa [hp] at hd
      · obtain ⟨c, hc⟩ := hd
        rw [hp] at hc
        refine ⟨-c, ?_⟩
        linear_combination -hc
    have h10 : (q : ℕ) ∣ j * p.natAbs := by
      rw [← Int.natCast_dvd_natCast]
      simpa using h9
    exact hpq.symm.dvd_of_dvd_mul_left (by rwa [mul_comm] at h10)
  · intro h
    obtain ⟨k, hk⟩ := h
    rw [hk, pow_mul, om_pow_q']
    simp


end Work.TMC14Core
