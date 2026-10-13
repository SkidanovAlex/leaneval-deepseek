/-
  WilG4a -- a count/degree comparison lemma for the `Ω`-calculus.

  `count_poly_comp` is the "polynomial growth" bookkeeping behind the substitution of a
  degree bound into another: whenever a polynomial `bp` over `ℕ` is evaluated at a pair of
  natural numbers of which the first is the value `B(D,r)` of a further `ℕ`-polynomial and the
  second is `2 * (k * (r + 3))`, the result (read in `ℝ`) is dominated by the evaluation at
  `(D,r,k)` of a *single* real polynomial `cc` in three variables.

  The proof is completely explicit.  Structural induction (`nat_poly_bound₂`, the `Fin 2`
  instance of the crude polynomial-growth bound) exhibits for each `ℕ`-polynomial `b` constants
  `C ≥ 0`, `N` with `(b.eval ![x, y] : ℝ) ≤ C * (1 + x + y)^N`.  Applying this to `B` bounds the
  first argument, and applying it to `bp` bounds the value; finally everything is dominated by a
  power of `1 + D + r + k`, which is the evaluation of `X 0 + X 1 + X 2 + 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Work.WilG4a

/-- Crude polynomial growth for `ℕ`-polynomials in two variables read in `ℝ`: there are
`C ≥ 0` and `N` with `(b.eval x : ℝ) ≤ C * (1 + x 0 + x 1) ^ N` for every `x : Fin 2 → ℕ`.

(Instance for two variables of the general bound proved by structural induction below; the
weight `S x = 1 + x 0 + x 1` satisfies `S x ≥ 1` and dominates both coordinates.) -/
theorem nat_poly_bound₂ (b : MvPolynomial (Fin 2) ℕ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ x : Fin 2 → ℕ,
      (b.eval x : ℝ) ≤ C * (1 + (x 0 : ℝ) + (x 1 : ℝ)) ^ N := by
  classical
  let S : (Fin 2 → ℕ) → ℝ := fun x => 1 + (x 0 : ℝ) + (x 1 : ℝ)
  have hS1 : ∀ x, 1 ≤ S x := by
    intro x; simp only [S]
    have h0 : (0 : ℝ) ≤ (x 0 : ℝ) := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ (x 1 : ℝ) := Nat.cast_nonneg _
    linarith
  suffices H : ∀ b : MvPolynomial (Fin 2) ℕ,
      ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ x : Fin 2 → ℕ, (b.eval x : ℝ) ≤ C * S x ^ N by
    obtain ⟨C, N, hC, h⟩ := H b
    exact ⟨C, N, hC, fun x => by simpa [S] using h x⟩
  intro b
  induction b using MvPolynomial.induction_on with
  | C a => exact ⟨(a : ℝ), 0, by positivity, fun x => by simp [S]⟩
  | add p q hp hq =>
      obtain ⟨C₁, N₁, hC₁, h₁⟩ := hp
      obtain ⟨C₂, N₂, hC₂, h₂⟩ := hq
      refine ⟨C₁ + C₂, max N₁ N₂, add_nonneg hC₁ hC₂, fun x => ?_⟩
      have hx1 : 1 ≤ S x := hS1 x
      have hx0 : 0 ≤ S x := le_trans zero_le_one hx1
      calc (MvPolynomial.eval x (p + q) : ℝ)
          = (MvPolynomial.eval x p : ℝ) + (MvPolynomial.eval x q : ℝ) := by
            simp [MvPolynomial.eval_add]
        _ ≤ C₁ * S x ^ N₁ + C₂ * S x ^ N₂ := add_le_add (h₁ x) (h₂ x)
        _ ≤ C₁ * S x ^ (max N₁ N₂) + C₂ * S x ^ (max N₁ N₂) :=
            add_le_add
              (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 (le_max_left _ _)) hC₁)
              (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 (le_max_right _ _)) hC₂)
        _ = (C₁ + C₂) * S x ^ (max N₁ N₂) := by ring
  | mul_X p n hp =>
      obtain ⟨C, N, hC, h⟩ := hp
      refine ⟨C, N + 1, hC, fun x => ?_⟩
      have hx1 : 1 ≤ S x := hS1 x
      have hx0 : 0 ≤ S x := le_trans zero_le_one hx1
      have hxn : (x n : ℝ) ≤ S x := by
        have h : (x n : ℝ) ≤ ∑ i, (x i : ℝ) :=
          Finset.single_le_sum (fun i _ => Nat.cast_nonneg (x i)) (Finset.mem_univ n)
        have hsum : (∑ i : Fin 2, (x i : ℝ)) = (x 0 : ℝ) + (x 1 : ℝ) := by
          simp [Fin.sum_univ_two]
        simp only [S]
        linarith
      calc (MvPolynomial.eval x (p * MvPolynomial.X n) : ℝ)
          = (MvPolynomial.eval x p : ℝ) * (x n : ℝ) := by
            simp [MvPolynomial.eval_mul, MvPolynomial.eval_X]
        _ ≤ (C * S x ^ N) * S x :=
            mul_le_mul (h x) hxn (by positivity) (mul_nonneg hC (pow_nonneg hx0 N))
        _ = C * S x ^ (N + 1) := by rw [pow_succ]; ring

theorem count_poly_comp (bp : MvPolynomial (Fin 2) ℕ) (B : MvPolynomial (Fin 2) ℕ) :
    ∃ cc : MvPolynomial (Fin 3) ℝ, ∀ D r k : ℕ,
      (MvPolynomial.eval ![MvPolynomial.eval ![D, r] B, 2 * (k * (r + 3))] bp : ℝ)
        ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] cc := by
  classical
  obtain ⟨CB, NB, hCB, hB⟩ := nat_poly_bound₂ B
  obtain ⟨Cbp, Nbp, hCbp, hbp⟩ := nat_poly_bound₂ bp
  let cc : MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.C (Cbp * (7 + CB) ^ Nbp) *
      (MvPolynomial.X (0 : Fin 3) + MvPolynomial.X 1 + MvPolynomial.X 2 + 1) ^
        (max NB 2 * Nbp)
  refine ⟨cc, ?_⟩
  intro D r k
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  set S : ℝ := (D : ℝ) + (r : ℝ) + (k : ℝ) + 1 with hS
  set n1 : ℕ := MvPolynomial.eval ![D, r] B with hn1
  set n2 : ℕ := 2 * (k * (r + 3)) with hn2
  have hS1 : 1 ≤ S := by rw [hS]; linarith
  have hS0 : 0 ≤ S := le_trans zero_le_one hS1
  have hSM1 : 1 ≤ S ^ max NB 2 := one_le_pow₀ hS1
  -- the first argument `B (D, r)` grows at most polynomially in `(D, r)`
  have h1 : (n1 : ℝ) ≤ CB * S ^ max NB 2 := by
    have hD : 1 + (D : ℝ) + (r : ℝ) ≤ S := by rw [hS]; linarith
    calc (n1 : ℝ) ≤ CB * (1 + (D : ℝ) + (r : ℝ)) ^ NB := by
          rw [hn1]; simpa using hB ![D, r]
      _ ≤ CB * S ^ NB := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hD NB) hCB
      _ ≤ CB * S ^ max NB 2 := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hS1 (le_max_left NB 2)) hCB
  -- the second argument `2 * (k * (r + 3))` grows at most quadratically
  have h2 : (n2 : ℝ) ≤ 6 * S ^ max NB 2 := by
    have hk : (k : ℝ) ≤ S := by rw [hS]; linarith
    have hr : (r : ℝ) + 3 ≤ 3 * S := by rw [hS]; linarith
    have hmul : (k : ℝ) * ((r : ℝ) + 3) ≤ S * (3 * S) :=
      mul_le_mul hk hr (by positivity) hS0
    have h2' : (n2 : ℝ) ≤ 6 * S ^ 2 := by
      rw [hn2]; push_cast; nlinarith [hmul]
    calc (n2 : ℝ) ≤ 6 * S ^ 2 := h2'
      _ ≤ 6 * S ^ max NB 2 := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hS1 (le_max_right NB 2)) (by norm_num)
  have hSsum : 1 + (n1 : ℝ) + (n2 : ℝ) ≤ (7 + CB) * S ^ max NB 2 := by
    nlinarith [h1, h2, hSM1]
  have hbp' : (MvPolynomial.eval ![n1, n2] bp : ℝ) ≤
      Cbp * (1 + (n1 : ℝ) + (n2 : ℝ)) ^ Nbp := by
    simpa using hbp ![n1, n2]
  -- the value of `cc` at `(D, r, k)`
  have hcc : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] cc
      = Cbp * (7 + CB) ^ Nbp * S ^ (max NB 2 * Nbp) := by
    simp only [cc, MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_add,
      MvPolynomial.eval_X, MvPolynomial.eval_C, map_one, hS]
    try simp
    try ring
  calc (MvPolynomial.eval ![n1, n2] bp : ℝ)
      ≤ Cbp * (1 + (n1 : ℝ) + (n2 : ℝ)) ^ Nbp := hbp'
    _ ≤ Cbp * ((7 + CB) * S ^ max NB 2) ^ Nbp := by
        apply mul_le_mul_of_nonneg_left _ hCbp
        exact pow_le_pow_left₀ (by positivity) hSsum Nbp
    _ = Cbp * (7 + CB) ^ Nbp * S ^ (max NB 2 * Nbp) := by
        rw [mul_pow, pow_mul]; ring
    _ = MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] cc := hcc.symm

end Work.WilG4a
