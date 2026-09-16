import Submission.ZagierHoffmanProof.CoeffSupport

/-!
# The `θ`-support of the coefficients of `W^w`, `W = X - C(θ^q)`

The two-term endgame (§`Submission/PLAN.md` §«SESSION 354» §«continued 28», identity (R′)) reads the
`θ`-coefficients of the products `P·W^w·δ₁` and `W^w·(-A₂L^q + A₁P² + A₁(w-q)·P·L^q)`, where
`W := X - C(θ^q)`.  The input `coeffNu_mul_of_support_le` needs for its factor `B := W^w` (read
coefficientwise in `X`) the vanishing

  `coeffNu F 0 m ((W^w).coeff n) = 0`   for `m > w·q`,

i.e. "the `θ`-support of every `X`-coefficient of `W^w` lies in `{0, q, …, w·q}`".

This is proved here by **induction on `w`**, using only the two-term `X`-recursion of `W`
(`W.coeff 0 = -θ^q`, `W.coeff 1 = 1`, all other coefficients `0`), and tracking the `θ`-degree
`degNu F 0` (which is the natural `A_0 = F_q[θ]`-degree).  No binomial expansion of `(X - C(θ^q))^w`
is needed (and no `Polynomial.coeff_X_sub_C_pow`, which does not exist in Mathlib).

Main results:

* `coeff_X_mul_eq` — `(X * p).coeff n = if n = 0 then 0 else p.coeff (n-1)`;
* `Wpow_coeff_mem_degNu` — `(W^w).coeff n ∈ A_0` and `degNu F 0 ((W^w).coeff n) ≤ q·w`;
* ★★★ `coeffNu_W_pow_of_lt` — the input `hBle` of `coeffNu_mul_of_support_le`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The two-term `X`-recursion of a product with `X` -/

/-- `(X * p).coeff 0 = 0`: the lowest `X`-coefficient of a left-multiple of `X`. -/
lemma coeff_X_mul_eq_zero (p : Polynomial (Ambient F)) : (Polynomial.X * p).coeff 0 = 0 := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero fun b hb => ?_
  have h1 : b.1 = 0 := by
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hb; omega
  rw [h1, Polynomial.coeff_X, if_neg (by norm_num : ¬ (1:ℕ) = 0), zero_mul]

lemma coeff_X_mul_eq_of_ne (p : Polynomial (Ambient F)) {n : ℕ} (hn : n ≠ 0) :
    (Polynomial.X * p).coeff n = p.coeff (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Polynomial.coeff_X_mul]
  simp

/-- ★ The two-term `X`-recursion: `X * p` has the coefficients of `p` shifted by one, with a `0` at
`X`-degree `0`. -/
lemma coeff_X_mul_eq (p : Polynomial (Ambient F)) (n : ℕ) :
    (Polynomial.X * p).coeff n = if n = 0 then 0 else p.coeff (n - 1) := by
  rcases eq_or_ne n 0 with h | h
  · subst h; rw [coeff_X_mul_eq_zero, if_pos rfl]
  · rw [coeff_X_mul_eq_of_ne F p h, if_neg h]

/-! ## §2. Level-`0` atoms for the endgame's `θ`-constants -/

lemma ambTheta_mem_ambA0 : ambTheta F ∈ ambA F 0 := by
  rw [← ambThetaNu_zero F]
  exact ambThetaNu_mem_ambA F 0

lemma theta_pow_card_mem_ambA0 : (ambTheta F) ^ Nat.card F ∈ ambA F 0 :=
  (ambASub F 0).pow_mem (ambTheta_mem_ambA0 F) _

/-- `degNu` is subadditive for a difference (the `A_0`-case of `degNu_add_le`). -/
lemma degNu_sub_le {x y : Ambient F} (hx : x ∈ ambA F 0) (hy : y ∈ ambA F 0) :
    degNu F 0 (x - y) ≤ max (degNu F 0 x) (degNu F 0 y) := by
  have h := degNu_add_le F hx ((ambASub F 0).neg_mem hy)
  simpa [sub_eq_add_neg, degNu_neg F hy] using h

/-- ★★ **The vanishing of `coeffNu` above a `degNu` bound, with no membership hypothesis** (the
junk-`0` convention of `coeffNu` outside `A_0` makes the membership case split disappear). -/
lemma coeffNu_eq_zero_of_degNu_lt (x : Ambient F) {m : ℕ} (h : degNu F 0 x < m) :
    coeffNu F 0 m x = 0 := by
  by_cases hx : x ∈ ambA F 0
  · exact coeffNu_degNu_lt F hx h
  · rw [coeffNu, dif_neg hx]

/-! ## §3. The `θ`-degree bound for the coefficients of `W^w` -/

/-- ★★★ **The `θ`-degree of every `X`-coefficient of `W^w = (X - C(θ^q))^w` is at most `q·w`.**

Proof by induction on `w`: `W^{w+1} = W * W^w = X * W^w - C(θ^q) * W^w`, so

  `(W^{w+1}).coeff n = (if n = 0 then 0 else (W^w).coeff (n-1)) - θ^q * (W^w).coeff n`,

whose two summands have `θ`-degrees at most `q·w` and `q + q·w = q·(w+1)`. -/
theorem Wpow_coeff_mem_degNu (w : ℕ) : ∀ n : ℕ,
    ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 ∧
    degNu F 0 (((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
      Polynomial (Ambient F)).coeff n) ≤ Nat.card F * w := by
  induction w with
  | zero =>
      intro n
      rw [pow_zero, Polynomial.coeff_one]
      split_ifs with hn
      · exact ⟨(ambASub F 0).one_mem, by rw [degNu_one]; simp⟩
      · exact ⟨(ambASub F 0).zero_mem, by rw [degNu_zero]; simp⟩
  | succ w ih =>
      intro n
      have key : ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (w+1) :
          Polynomial (Ambient F)).coeff n
          = (if n = 0 then 0 else ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
              Polynomial (Ambient F)).coeff (n - 1))
            - ((ambTheta F) ^ Nat.card F)
                * ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
                    Polynomial (Ambient F)).coeff n := by
        rw [pow_succ', sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_X_mul_eq]
      have hu : (if n = 0 then 0 else ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
            Polynomial (Ambient F)).coeff (n - 1)) ∈ ambA F 0 ∧
          degNu F 0 (if n = 0 then 0 else ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
            Polynomial (Ambient F)).coeff (n - 1)) ≤ Nat.card F * w := by
        by_cases hn : n = 0
        · rw [if_pos hn]; exact ⟨(ambASub F 0).zero_mem, by rw [degNu_zero]; simp⟩
        · rw [if_neg hn]; exact ih (n - 1)
      rw [key]
      refine ⟨ambA_sub_mem F hu.1
        (ambA_mul_mem F (theta_pow_card_mem_ambA0 F) (ih n).1), ?_⟩
      refine (degNu_sub_le F hu.1
        (ambA_mul_mem F (theta_pow_card_mem_ambA0 F) (ih n).1)).trans ?_
      rw [max_le_iff]
      refine ⟨hu.2.trans (Nat.mul_le_mul_left _ (Nat.le_succ w)), ?_⟩
      by_cases h0 : ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
          Polynomial (Ambient F)).coeff n = 0
      · rw [h0, mul_zero, degNu_zero]; simp
      · rw [degNu_mul F (theta_pow_card_mem_ambA0 F) (ih n).1
            (pow_ne_zero _ (ambTheta_ne_zero F)) h0, degNu_theta_pow_card F 0]
        have hq : (Nat.card F) ^ (0 + 1) = Nat.card F := by simp
        rw [hq]
        have := (ih n).2
        nlinarith [Nat.zero_le (Nat.card F)]

/-- ★★★ **The `hBle` input of `coeffNu_mul_of_support_le` for `B := W^w`**: above `θ`-degree `w·q`,
every `X`-coefficient of `W^w` has vanishing `coeffNu`. -/
theorem coeffNu_W_pow_of_lt {w m : ℕ} (hm : w * Nat.card F < m) (n : ℕ) :
    coeffNu F 0 m (((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
      Polynomial (Ambient F)).coeff n) = 0 := by
  refine coeffNu_eq_zero_of_degNu_lt F _ ?_
  have := (Wpow_coeff_mem_degNu F w n).2
  rw [Nat.mul_comm (Nat.card F) w] at this
  omega

end ZagierHoffmanPositiveChar
