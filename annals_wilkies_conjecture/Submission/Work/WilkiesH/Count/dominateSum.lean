import Mathlib
import Submission.Work.WilG5.Count.dominate

namespace Work.WilkiesH.Count

/-! ## Domination of a finite sum of shifted polynomials

We prove `Work.WilkiesH.Count.dominateSum`: for a finite family `f : ι → MvPolynomial (Fin 3) ℝ`
and shifts `b : ι → ℕ`, the function

  `(D, g, s) ↦ ∑ i, (f i).eval ![D + b i, g, s]`  (`D, g : ℕ`, `s : ℝ`, `s ≥ 0`)

is dominated by the evaluation of a *single* real polynomial `p` in the variables `(D, g, s)`.

The argument is elementary.  By the crude growth bound `WilG5.PolyEval.poly_abs_bound`, applied
to each `f i`, there are `C i ≥ 0` and `N i` with
`|(f i).eval x| ≤ C i * (1 + ∑ j, |x j|) ^ (N i)` for all `x : Fin 3 → ℝ`.  At the point
`x = ![D + b i, g, s]` (all coordinates nonnegative, using `s ≥ 0`) the weight equals
`S + b i` with `S = D + g + s + 1`, and `S + b i ≤ (b i + 2) * S` because
`(b i + 2) * S - (S + b i) = (b i + 1) * (D + g + s) + 1 ≥ 1`.  Hence, since `S ≥ 1`,

  `(f i).eval ![D + b i, g, s] ≤ C i * ((b i : ℝ) + 2) ^ (N i) * S ^ (∑ j, N j)`.

Summing over `i` and taking `p := C M * (X 0 + X 1 + X 2 + 1) ^ (∑ j, N j)` with
`M := ∑ i, C i * ((b i : ℝ) + 2) ^ (N i)` finishes the proof, since
`p.eval ![D, g, s] = M * S ^ (∑ j, N j)`. -/
theorem dominateSum {ι : Type*} [Fintype ι] (f : ι → MvPolynomial (Fin 3) ℝ) (b : ι → ℕ) :
    ∃ p : MvPolynomial (Fin 3) ℝ, ∀ (D g : ℕ) (s : ℝ), 0 ≤ s →
      ∑ i, (f i).eval ![((D + b i : ℕ) : ℝ), (g : ℝ), s] ≤
        MvPolynomial.eval ![(D : ℝ), (g : ℝ), s] p := by
  classical
  choose C N hCN using fun i => Work.WilG5.PolyEval.poly_abs_bound (f i)
  let M : ℝ := ∑ i, C i * ((b i : ℝ) + 2) ^ N i
  let Nt : ℕ := ∑ i, N i
  let p : MvPolynomial (Fin 3) ℝ := MvPolynomial.C M *
      ((MvPolynomial.X (0 : Fin 3)) + (MvPolynomial.X (1 : Fin 3)) +
        (MvPolynomial.X (2 : Fin 3)) + MvPolynomial.C 1) ^ Nt
  refine ⟨p, ?_⟩
  intro D g s hs
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg g
  have hS1 : (1 : ℝ) ≤ (D : ℝ) + (g : ℝ) + s + 1 := by linarith
  have hEval : MvPolynomial.eval ![(D : ℝ), (g : ℝ), s] p
      = M * ((D : ℝ) + (g : ℝ) + s + 1) ^ Nt := by
    simp only [p]
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_C]
    congr 1
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_X, MvPolynomial.eval_C]
    simp
  rw [hEval]
  have hterm : ∀ i, (f i).eval ![((D + b i : ℕ) : ℝ), (g : ℝ), s]
      ≤ C i * ((b i : ℝ) + 2) ^ N i * ((D : ℝ) + (g : ℝ) + s + 1) ^ Nt := by
    intro i
    have hbi0 : (0 : ℝ) ≤ (b i : ℝ) := Nat.cast_nonneg _
    have hx := (hCN i).2 ![((D + b i : ℕ) : ℝ), (g : ℝ), s]
    have hsum : 1 + ∑ j : Fin 3, |(![((D + b i : ℕ) : ℝ), (g : ℝ), s] : Fin 3 → ℝ) j|
        = (D : ℝ) + (b i : ℝ) + (g : ℝ) + s + 1 := by
      rw [Fin.sum_univ_three]
      rw [show (![((D + b i : ℕ) : ℝ), (g : ℝ), s] : Fin 3 → ℝ) 0 = ((D + b i : ℕ) : ℝ)
            from by simp,
          show (![((D + b i : ℕ) : ℝ), (g : ℝ), s] : Fin 3 → ℝ) 1 = (g : ℝ) from by simp,
          show (![((D + b i : ℕ) : ℝ), (g : ℝ), s] : Fin 3 → ℝ) 2 = s from by simp]
      rw [abs_of_nonneg (Nat.cast_nonneg (D + b i)), abs_of_nonneg (Nat.cast_nonneg g),
        abs_of_nonneg hs]
      push_cast
      ring
    rw [hsum] at hx
    have hbase : (0 : ℝ) ≤ (D : ℝ) + (b i : ℝ) + (g : ℝ) + s + 1 := by linarith
    have hle : (D : ℝ) + (b i : ℝ) + (g : ℝ) + s + 1
        ≤ ((b i : ℝ) + 2) * ((D : ℝ) + (g : ℝ) + s + 1) := by
      nlinarith [hbi0, hD0, hg0, hs]
    have hpowa : ((D : ℝ) + (b i : ℝ) + (g : ℝ) + s + 1) ^ (N i)
        ≤ (((b i : ℝ) + 2) * ((D : ℝ) + (g : ℝ) + s + 1)) ^ (N i) :=
      pow_le_pow_left₀ hbase hle (N i)
    have hNi : N i ≤ Nt := by
      simp only [Nt]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hc0 : (0 : ℝ) ≤ C i * ((b i : ℝ) + 2) ^ N i :=
      mul_nonneg (hCN i).1 (pow_nonneg (by linarith) _)
    calc (f i).eval ![((D + b i : ℕ) : ℝ), (g : ℝ), s]
        ≤ |(f i).eval ![((D + b i : ℕ) : ℝ), (g : ℝ), s]| := le_abs_self _
      _ ≤ C i * ((D : ℝ) + (b i : ℝ) + (g : ℝ) + s + 1) ^ (N i) := hx
      _ ≤ C i * (((b i : ℝ) + 2) * ((D : ℝ) + (g : ℝ) + s + 1)) ^ (N i) :=
            mul_le_mul_of_nonneg_left hpowa (hCN i).1
      _ = C i * ((b i : ℝ) + 2) ^ N i * ((D : ℝ) + (g : ℝ) + s + 1) ^ (N i) := by
            rw [mul_pow]; ring
      _ ≤ C i * ((b i : ℝ) + 2) ^ N i * ((D : ℝ) + (g : ℝ) + s + 1) ^ Nt :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS1 hNi) hc0
  calc ∑ i, (f i).eval ![((D + b i : ℕ) : ℝ), (g : ℝ), s]
      ≤ ∑ i, C i * ((b i : ℝ) + 2) ^ N i * ((D : ℝ) + (g : ℝ) + s + 1) ^ Nt :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = M * ((D : ℝ) + (g : ℝ) + s + 1) ^ Nt := by
        simp only [M]
        rw [Finset.sum_mul]

end Work.WilkiesH.Count
