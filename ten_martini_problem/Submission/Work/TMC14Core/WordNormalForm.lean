import Mathlib
import Submission.Work.TMC14Core.Weyl

/-!
# TMC14Core: normal form of a Weyl word

`wordProd p q θ k n f` is the product of the letters `U, U†, V, V†` (the clock-and-shift
Weyl pair of `Weyl.lean`) prescribed by the word `f`.  This file proves that it is
always a non-zero scalar multiple of the canonical monomial
`V^a · (V†)^b · U^c · (U†)^d` where `a = #{(false,true)}`, `b = #{(false,false)}`,
`c = #{(true,true)}`, `d = #{(true,false)}` are the letter multiplicities of the word.

The proof is the standard Weyl-algebra normal form: `U` and `U†` are mutually inverse
(as are `V` and `V†`), and `U V = ω V U` with `ω = om p q`.  Hence a letter can be
moved through any normal form at the cost of a power of `ω`.
-/

noncomputable section

namespace Work.TMC14Core

open Matrix

/-! ## 1. The phase `ω = e^{2πi p/q}` -/

theorem wnf_om_mul_star (p : ℤ) (q : ℕ) : om p q * star (om p q) = 1 := by
  rw [om_eq_wPh, wPh_conj, ← wPh_add, add_neg_cancel, wPh_zero]

theorem wnf_om_ne_zero (p : ℤ) (q : ℕ) : om p q ≠ 0 := by
  intro h
  have h1 := wnf_om_mul_star p q
  rw [h, star_zero, mul_zero] at h1
  exact zero_ne_one h1

theorem wnf_star_om (p : ℤ) (q : ℕ) : star (om p q) = (om p q)⁻¹ :=
  (inv_eq_of_mul_eq_one_right (wnf_om_mul_star p q)).symm

/-! ## 2. Unitarity of the two Weyl generators, in both directions -/

theorem wnf_star_wU_mul_wU (q : ℕ) (k : ℝ) : star (wU q k) * wU q k = 1 := by
  rcases q with _ | n
  · ext i; exact Fin.elim0 i
  · exact Matrix.mem_unitaryGroup_iff'.mp (wU_mem_unitaryGroup (n + 1) k (Nat.succ_pos n))

theorem wnf_wU_mul_star_wU (q : ℕ) (k : ℝ) : wU q k * star (wU q k) = 1 := by
  rcases q with _ | n
  · ext i; exact Fin.elim0 i
  · exact Matrix.mem_unitaryGroup_iff.mp (wU_mem_unitaryGroup (n + 1) k (Nat.succ_pos n))

theorem wnf_star_wV_mul_wV (p : ℤ) (q : ℕ) (θ : ℝ) : star (wV p q θ) * wV p q θ = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (wV_mem_unitaryGroup p q θ)

theorem wnf_wV_mul_star_wV (p : ℤ) (q : ℕ) (θ : ℝ) : wV p q θ * star (wV p q θ) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (wV_mem_unitaryGroup p q θ)

/-! ## 3. The three remaining cross commutation relations (entrywise) -/

/-- `star (wV p q θ)` is the diagonal matrix of the conjugates of the entries of `wV`. -/
theorem wnf_star_wV_eq_diagonal (p : ℤ) (q : ℕ) (θ : ℝ) :
    star (wV p q θ) = Matrix.diagonal (star (wVd p q θ)) := by
  rw [Matrix.star_eq_conjTranspose, wV, Matrix.diagonal_conjTranspose]

theorem wnf_wU_mul_star_wV (p : ℤ) (q : ℕ) (θ k : ℝ) :
    wU q k * star (wV p q θ) = (om p q)⁻¹ • (star (wV p q θ) * wU q k) := by
  rcases q with _ | q'
  · ext i; exact Fin.elim0 i
  · ext i j
    rw [wnf_star_wV_eq_diagonal, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_mul]
    simp only [Pi.star_apply]
    by_cases h : (i.val + 1) % (q' + 1) = j.val
    · rw [wU_apply, if_pos h]
      have hidx : (om p (q' + 1))⁻¹ * star (wVd p (q' + 1) θ i)
          = star (wVd p (q' + 1) θ j) := by
        rw [wVd_succ p (q' + 1) θ (Nat.succ_pos q') i j h.symm, star_mul, wnf_star_om]
        ring
      by_cases hlt : i.val + 1 < q' + 1
      · rw [if_pos hlt, ← mul_assoc, hidx]; ring
      · rw [if_neg hlt, ← mul_assoc, hidx]; ring
    · rw [wU_apply, if_neg h]; simp

theorem wnf_star_wU_mul_wV (p : ℤ) (q : ℕ) (θ k : ℝ) :
    star (wU q k) * wV p q θ = (om p q)⁻¹ • (wV p q θ * star (wU q k)) := by
  rcases q with _ | q'
  · ext i; exact Fin.elim0 i
  · ext i j
    rw [wV, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul,
      Matrix.star_apply]
    by_cases h : (j.val + 1) % (q' + 1) = i.val
    · rw [wU_apply, if_pos h]
      have hidx : (om p (q' + 1))⁻¹ * wVd p (q' + 1) θ i = wVd p (q' + 1) θ j := by
        rw [wVd_succ p (q' + 1) θ (Nat.succ_pos q') j i h.symm, ← mul_assoc,
          inv_mul_cancel₀ (wnf_om_ne_zero p (q' + 1)), one_mul]
      by_cases hlt : j.val + 1 < q' + 1
      · rw [if_pos hlt, ← mul_assoc, hidx]; ring
      · rw [if_neg hlt, ← mul_assoc, hidx]; ring
    · rw [wU_apply, if_neg h]; simp

theorem wnf_star_wU_mul_star_wV (p : ℤ) (q : ℕ) (θ k : ℝ) :
    star (wU q k) * star (wV p q θ) = om p q • (star (wV p q θ) * star (wU q k)) := by
  rcases q with _ | q'
  · ext i; exact Fin.elim0 i
  · ext i j
    rw [wnf_star_wV_eq_diagonal, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_mul]
    simp only [Pi.star_apply]
    rw [Matrix.star_apply]
    by_cases h : (j.val + 1) % (q' + 1) = i.val
    · rw [wU_apply, if_pos h]
      have hidx : om p (q' + 1) * star (wVd p (q' + 1) θ i) = star (wVd p (q' + 1) θ j) := by
        have h1 : star (wVd p (q' + 1) θ i)
            = (om p (q' + 1))⁻¹ * star (wVd p (q' + 1) θ j) := by
          rw [wVd_succ p (q' + 1) θ (Nat.succ_pos q') j i h.symm, star_mul, wnf_star_om]
          ring
        rw [h1, ← mul_assoc, mul_inv_cancel₀ (wnf_om_ne_zero p (q' + 1)), one_mul]
      by_cases hlt : j.val + 1 < q' + 1
      · rw [if_pos hlt, ← mul_assoc, hidx]; ring
      · rw [if_neg hlt, ← mul_assoc, hidx]; ring
    · rw [wU_apply, if_neg h]; simp

/-! ## 4. Powers: `X * Y^n = γ^n • (Y^n * X)` when `X * Y = γ • (Y * X)` -/

theorem wnf_mul_pow_of_mul_eq_smul_mul {q : ℕ} {X Y : Matrix (Fin q) (Fin q) ℂ} {γ : ℂ}
    (h : X * Y = γ • (Y * X)) (n : ℕ) : X * Y ^ n = γ ^ n • (Y ^ n * X) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, Matrix.smul_mul, mul_assoc, h, Matrix.mul_smul, smul_smul,
      pow_succ, mul_assoc]

/-! ## 5. The canonical monomial and the "move a letter through" lemmas -/

/-- The canonical monomial `V^a · (V†)^b · U^c · (U†)^d`, in right-nested form. -/
def wnfNorm (p : ℤ) (q : ℕ) (θ k : ℝ) (a b c d : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  (wV p q θ) ^ a * ((star (wV p q θ)) ^ b * ((wU q k) ^ c * (star (wU q k)) ^ d))

/-- `wnfNorm` unfolds to the left-nested monomial of the statement. -/
theorem wnfNorm_eq_expanded (p : ℤ) (q : ℕ) (θ k : ℝ) (a b c d : ℕ) :
    wnfNorm p q θ k a b c d =
      (wV p q θ) ^ a * (star (wV p q θ)) ^ b * (wU q k) ^ c * (star (wU q k)) ^ d := by
  simp only [wnfNorm, mul_assoc]

/-- `X * (X^n * Z) = X^{n+1} * Z`. -/
theorem wnf_ctx_pow_self {M : Type*} [Monoid M] (X : M) (n : ℕ) (Z : M) :
    X * (X ^ n * Z) = X ^ (n + 1) * Z := by
  rw [← mul_assoc, ← pow_succ']

/-- `Y * (X^n * Z) = X^n * (Y * Z)` when `Y` is the inverse of `X`. -/
theorem wnf_ctx_of_inv {M : Type*} [Monoid M] {X Y : M} (hXY : X * Y = 1) (hYX : Y * X = 1)
    (n : ℕ) (Z : M) : Y * (X ^ n * Z) = X ^ n * (Y * Z) := by
  have h : Y * X ^ n = X ^ n * Y := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hYX, mul_one, mul_assoc, hXY, mul_one]
  rw [← mul_assoc, h, mul_assoc]

theorem wnf_ctx_star_wV_wV (p : ℤ) (q : ℕ) (θ : ℝ) (a : ℕ) (Z : Matrix (Fin q) (Fin q) ℂ) :
    star (wV p q θ) * ((wV p q θ) ^ a * Z) = (wV p q θ) ^ a * (star (wV p q θ) * Z) :=
  wnf_ctx_of_inv (wnf_wV_mul_star_wV p q θ) (wnf_star_wV_mul_wV p q θ) a Z

theorem wnf_ctx_star_wU_wU (q : ℕ) (k : ℝ) (c : ℕ) (Z : Matrix (Fin q) (Fin q) ℂ) :
    star (wU q k) * ((wU q k) ^ c * Z) = (wU q k) ^ c * (star (wU q k) * Z) :=
  wnf_ctx_of_inv (wnf_wU_mul_star_wU q k) (wnf_star_wU_mul_wU q k) c Z

theorem wnf_ctx_wU_wV (p : ℤ) (q : ℕ) (θ k : ℝ) (a : ℕ) (Z : Matrix (Fin q) (Fin q) ℂ) :
    wU q k * ((wV p q θ) ^ a * Z)
      = (om p q) ^ a • ((wV p q θ) ^ a * (wU q k * Z)) := by
  rw [← mul_assoc, wnf_mul_pow_of_mul_eq_smul_mul (wU_mul_wV p q θ k) a, Matrix.smul_mul,
    mul_assoc]

theorem wnf_ctx_wU_star_wV (p : ℤ) (q : ℕ) (θ k : ℝ) (b : ℕ) (Z : Matrix (Fin q) (Fin q) ℂ) :
    wU q k * ((star (wV p q θ)) ^ b * Z)
      = ((om p q)⁻¹) ^ b • ((star (wV p q θ)) ^ b * (wU q k * Z)) := by
  rw [← mul_assoc, wnf_mul_pow_of_mul_eq_smul_mul (wnf_wU_mul_star_wV p q θ k) b, Matrix.smul_mul,
    mul_assoc]

theorem wnf_ctx_star_wU_wV (p : ℤ) (q : ℕ) (θ k : ℝ) (a : ℕ) (Z : Matrix (Fin q) (Fin q) ℂ) :
    star (wU q k) * ((wV p q θ) ^ a * Z)
      = ((om p q)⁻¹) ^ a • ((wV p q θ) ^ a * (star (wU q k) * Z)) := by
  rw [← mul_assoc, wnf_mul_pow_of_mul_eq_smul_mul (wnf_star_wU_mul_wV p q θ k) a, Matrix.smul_mul,
    mul_assoc]

theorem wnf_ctx_star_wU_star_wV (p : ℤ) (q : ℕ) (θ k : ℝ) (b : ℕ)
    (Z : Matrix (Fin q) (Fin q) ℂ) :
    star (wU q k) * ((star (wV p q θ)) ^ b * Z)
      = (om p q) ^ b • ((star (wV p q θ)) ^ b * (star (wU q k) * Z)) := by
  rw [← mul_assoc, wnf_mul_pow_of_mul_eq_smul_mul (wnf_star_wU_mul_star_wV p q θ k) b, Matrix.smul_mul,
    mul_assoc]

/-! ## 6. The four letters moved through the canonical monomial -/

theorem wnf_step_wV (p : ℤ) (q : ℕ) (θ k : ℝ) (a b c d : ℕ) :
    ∃ w : ℂ, w ≠ 0 ∧ wV p q θ * wnfNorm p q θ k a b c d = w • wnfNorm p q θ k (a + 1) b c d := by
  refine ⟨1, one_ne_zero, ?_⟩
  rw [one_smul]
  conv_lhs => rw [wnfNorm]
  rw [wnf_ctx_pow_self]
  rfl

theorem wnf_step_star_wV (p : ℤ) (q : ℕ) (θ k : ℝ) (a b c d : ℕ) :
    ∃ w : ℂ,
      w ≠ 0 ∧ star (wV p q θ) * wnfNorm p q θ k a b c d = w • wnfNorm p q θ k a (b + 1) c d := by
  refine ⟨1, one_ne_zero, ?_⟩
  rw [one_smul]
  conv_lhs => rw [wnfNorm]
  rw [wnf_ctx_star_wV_wV, wnf_ctx_pow_self]
  rfl

theorem wnf_step_wU (p : ℤ) (q : ℕ) (θ k : ℝ) (a b c d : ℕ) :
    ∃ w : ℂ,
      w ≠ 0 ∧ wU q k * wnfNorm p q θ k a b c d = w • wnfNorm p q θ k a b (c + 1) d := by
  refine ⟨(om p q) ^ a * ((om p q)⁻¹) ^ b,
    mul_ne_zero (pow_ne_zero _ (wnf_om_ne_zero p q)) (pow_ne_zero _ (inv_ne_zero (wnf_om_ne_zero p q))),
    ?_⟩
  conv_lhs => rw [wnfNorm]
  rw [wnf_ctx_wU_wV, wnf_ctx_wU_star_wV, Matrix.mul_smul, smul_smul, wnf_ctx_pow_self]
  rfl

theorem wnf_step_star_wU (p : ℤ) (q : ℕ) (θ k : ℝ) (a b c d : ℕ) :
    ∃ w : ℂ,
      w ≠ 0 ∧ star (wU q k) * wnfNorm p q θ k a b c d = w • wnfNorm p q θ k a b c (d + 1) := by
  refine ⟨((om p q)⁻¹) ^ a * (om p q) ^ b,
    mul_ne_zero (pow_ne_zero _ (inv_ne_zero (wnf_om_ne_zero p q))) (pow_ne_zero _ (wnf_om_ne_zero p q)),
    ?_⟩
  conv_lhs => rw [wnfNorm]
  rw [wnf_ctx_star_wU_wV, wnf_ctx_star_wU_star_wV, Matrix.mul_smul, smul_smul, wnf_ctx_star_wU_wU,
    ← pow_succ']
  rfl

/-! ## 7. Counting letters of a list -/

/-- Number of entries of `l` equal to `x`. -/
def wnf_cntL (x : Bool × Bool) (l : List (Bool × Bool)) : ℕ := (l.filter (fun y => y = x)).length

theorem wnf_cntL_cons (x y : Bool × Bool) (l : List (Bool × Bool)) :
    wnf_cntL x (y :: l) = wnf_cntL x l + (if y = x then 1 else 0) := by
  by_cases h : y = x
  · rw [wnf_cntL, List.filter_cons_of_pos (by simpa using h), wnf_cntL, List.length_cons]
    simp [h]
  · rw [wnf_cntL, List.filter_cons_of_neg (by simpa using h), wnf_cntL]
    simp [h]

theorem wnf_cnt_eq_cntL (b c : Bool) (n : ℕ) (f : Fin n → Bool × Bool) :
    cnt b c n f = wnf_cntL (b, c) (List.ofFn f) := by
  induction n with
  | zero => simp [cnt, wnf_cntL]
  | succ n ih =>
    have hsum : ∀ (m : ℕ) (g : Fin m → Bool × Bool),
        cnt b c m g = ∑ i : Fin m, (if g i = (b, c) then 1 else 0) := by
      intro m g
      rw [cnt, Finset.card_filter]
    rw [hsum (n + 1) f, Fin.sum_univ_succ, ← hsum n (fun i => f i.succ), List.ofFn_succ,
      wnf_cntL_cons, ih]
    omega

/-! ## 8. The normal form for lists, and the theorem -/

theorem wnf_letterOf_ff (p : ℤ) (q : ℕ) (θ k : ℝ) :
    letterOf p q θ k (false, false) = star (wV p q θ) := by
  simp [letterOf, Matrix.star_eq_conjTranspose]

theorem wnf_letterOf_ft (p : ℤ) (q : ℕ) (θ k : ℝ) :
    letterOf p q θ k (false, true) = wV p q θ := by
  simp [letterOf]

theorem wnf_letterOf_tf (p : ℤ) (q : ℕ) (θ k : ℝ) :
    letterOf p q θ k (true, false) = star (wU q k) := by
  simp [letterOf, Matrix.star_eq_conjTranspose]

theorem wnf_letterOf_tt (p : ℤ) (q : ℕ) (θ k : ℝ) :
    letterOf p q θ k (true, true) = wU q k := by
  simp [letterOf]

theorem wnf_list (p : ℤ) (q : ℕ) (θ k : ℝ) (l : List (Bool × Bool)) :
    ∃ u : ℂ, u ≠ 0 ∧ (l.map (letterOf p q θ k)).prod =
      u • wnfNorm p q θ k (wnf_cntL (false, true) l) (wnf_cntL (false, false) l)
        (wnf_cntL (true, true) l) (wnf_cntL (true, false) l) := by
  induction l with
  | nil =>
    refine ⟨1, one_ne_zero, ?_⟩
    simp [wnfNorm, wnf_cntL]
  | cons x xs ih =>
    obtain ⟨u, hu, h⟩ := ih
    rw [List.map_cons, List.prod_cons, h, Matrix.mul_smul]
    rcases x with ⟨b1, b2⟩
    rcases b1 <;> rcases b2
    · obtain ⟨w, hw, hstep⟩ :=
        wnf_step_star_wV p q θ k (wnf_cntL (false, true) xs) (wnf_cntL (false, false) xs)
          (wnf_cntL (true, true) xs) (wnf_cntL (true, false) xs)
      refine ⟨u * w, mul_ne_zero hu hw, ?_⟩
      rw [wnf_letterOf_ff, hstep, smul_smul]
      congr 1
    · obtain ⟨w, hw, hstep⟩ :=
        wnf_step_wV p q θ k (wnf_cntL (false, true) xs) (wnf_cntL (false, false) xs)
          (wnf_cntL (true, true) xs) (wnf_cntL (true, false) xs)
      refine ⟨u * w, mul_ne_zero hu hw, ?_⟩
      rw [wnf_letterOf_ft, hstep, smul_smul]
      congr 1
    · obtain ⟨w, hw, hstep⟩ :=
        wnf_step_star_wU p q θ k (wnf_cntL (false, true) xs) (wnf_cntL (false, false) xs)
          (wnf_cntL (true, true) xs) (wnf_cntL (true, false) xs)
      refine ⟨u * w, mul_ne_zero hu hw, ?_⟩
      rw [wnf_letterOf_tf, hstep, smul_smul]
      congr 1
    · obtain ⟨w, hw, hstep⟩ :=
        wnf_step_wU p q θ k (wnf_cntL (false, true) xs) (wnf_cntL (false, false) xs)
          (wnf_cntL (true, true) xs) (wnf_cntL (true, false) xs)
      refine ⟨u * w, mul_ne_zero hu hw, ?_⟩
      rw [wnf_letterOf_tt, hstep, smul_smul]
      congr 1

theorem WordNormalForm (p : ℤ) (q : ℕ) (θ k : ℝ) (n : ℕ) (f : Fin n → Bool × Bool) :
    ∃ u : ℂ, u ≠ 0 ∧ wordProd p q θ k n f =
      u • ((wV p q θ) ^ (cnt false true n f) * (star (wV p q θ)) ^ (cnt false false n f) *
           (wU q k) ^ (cnt true true n f) * (star (wU q k)) ^ (cnt true false n f)) := by
  obtain ⟨u, hu, h⟩ := wnf_list p q θ k (List.ofFn f)
  refine ⟨u, hu, ?_⟩
  have hwp : wordProd p q θ k n f = ((List.ofFn f).map (letterOf p q θ k)).prod := rfl
  rw [hwp, h, wnfNorm_eq_expanded, ← wnf_cnt_eq_cntL false true n f, ← wnf_cnt_eq_cntL false false n f,
    ← wnf_cnt_eq_cntL true true n f, ← wnf_cnt_eq_cntL true false n f]

end Work.TMC14Core
