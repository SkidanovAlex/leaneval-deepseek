import Mathlib

/-!
# A Schwartz–Zippel bound over the integer box `{-(H-1), …, H-1}`

We bound the number of integer lattice points in the box `Ioo (-H) H` in each of `n`
coordinates at which a nonzero polynomial `p ∈ ℤ[x₁,…,xₙ]` of total degree at most `D`
vanishes, by `D * (2H-1)^(n-1)`.

The proof is the standard Schwartz–Zippel argument, which is available in Mathlib in the
form

`MvPolynomial.schwartz_zippel_totalDegree : (↑#{f ∈ piFinset fun _ ↦ S | eval f p = 0}) / (↑S.card)^n ≤ ↑p.totalDegree / ↑S.card`,

together with the cardinality computation `Int.card_Ioo` for the interval.
-/

namespace Work.Peluse.Prop36SW

/-- Number of zeros, in a box of side `2H-1` per coordinate, of a nonzero polynomial of total
degree at most `D`. -/
theorem szZeroCardLe {n D H : ℕ} (p : MvPolynomial (Fin n) ℤ) (hp : p ≠ 0) (hdeg : p.totalDegree ≤ D) (hH : 1 ≤ H) : ((Fintype.piFinset (fun _ : Fin n => Finset.Ioo (-(H : ℤ)) (H : ℤ))).filter (fun a => MvPolynomial.eval a p = 0)).card ≤ D * (2 * H - 1) ^ (n - 1) := by
  set S : Finset ℤ := Finset.Ioo (-(H : ℤ)) (H : ℤ) with hS
  -- The box has `2 * H - 1` elements in every coordinate.
  have hcard : S.card = 2 * H - 1 := by
    rw [hS, Int.card_Ioo]
    have h2 : (1 : ℕ) ≤ 2 * H := by omega
    rw [show (H : ℤ) - (-(H : ℤ)) - 1 = ((2 * H - 1 : ℕ) : ℤ) from by
      rw [Nat.cast_sub h2]
      push_cast
      ring]
    simp
  have hmpos : 0 < S.card := by rw [hcard]; omega
  have hmne : (S.card : ℚ≥0) ≠ 0 := by
    have : (0 : ℚ≥0) < (S.card : ℚ≥0) := by exact_mod_cast hmpos
    exact ne_of_gt this
  -- Schwartz–Zippel for the box `S`, with the degree bound `p.totalDegree ≤ D` inserted.
  have hsz := MvPolynomial.schwartz_zippel_totalDegree (R := ℤ) hp S
  have hmain :
      (↑((Fintype.piFinset (fun _ : Fin n => S)).filter
            (fun a => MvPolynomial.eval a p = 0)).card : ℚ≥0) / (↑S.card : ℚ≥0) ^ n
        ≤ (↑D : ℚ≥0) / (↑S.card : ℚ≥0) := by
    refine le_trans hsz ?_
    gcongr
  -- Clear denominators: `#zeros * #S ≤ D * #S ^ n`.
  have hZ :
      ((Fintype.piFinset (fun _ : Fin n => S)).filter
            (fun a => MvPolynomial.eval a p = 0)).card * S.card ≤ D * S.card ^ n := by
    have key := mul_le_mul_of_nonneg_right hmain
      (le_of_lt (show (0 : ℚ≥0) < (S.card : ℚ≥0) ^ n * (S.card : ℚ≥0) by positivity))
    have e1 :
        ((↑((Fintype.piFinset (fun _ : Fin n => S)).filter
              (fun a => MvPolynomial.eval a p = 0)).card : ℚ≥0) / (↑S.card : ℚ≥0) ^ n)
            * ((↑S.card : ℚ≥0) ^ n * ↑S.card)
          = (↑((Fintype.piFinset (fun _ : Fin n => S)).filter
              (fun a => MvPolynomial.eval a p = 0)).card : ℚ≥0) * ↑S.card := by
      rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hmne)]
    have e2 :
        ((↑D : ℚ≥0) / (↑S.card : ℚ≥0)) * ((↑S.card : ℚ≥0) ^ n * ↑S.card)
          = (↑D : ℚ≥0) * (↑S.card : ℚ≥0) ^ n := by
      rw [mul_comm ((↑S.card : ℚ≥0) ^ n) (↑S.card), ← mul_assoc,
        div_mul_cancel₀ _ hmne]
    rw [e1, e2] at key
    exact_mod_cast key
  -- Remove the extra factor `#S ≥ 1`.
  suffices hfin :
      ((Fintype.piFinset (fun _ : Fin n => S)).filter
            (fun a => MvPolynomial.eval a p = 0)).card ≤ D * S.card ^ (n - 1) by
    rwa [hcard] at hfin
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: the box is a single point and there are no zeros.
    subst hn
    simp only [Nat.reduceSub, pow_zero, mul_one]
    calc ((Fintype.piFinset (fun _ : Fin 0 => S)).filter
            (fun a => MvPolynomial.eval a p = 0)).card
        ≤ ((Fintype.piFinset (fun _ : Fin 0 => S)).filter
            (fun a => MvPolynomial.eval a p = 0)).card * S.card :=
          Nat.le_mul_of_pos_right _ hmpos
      _ ≤ D * S.card ^ 0 := hZ
      _ = D := by ring
  · -- `n ≥ 1`: cancel one factor of `#S`.
    have hmn : S.card ^ n = S.card ^ (n - 1) * S.card := by
      nth_rewrite 1 [← Nat.sub_add_cancel hn]
      rw [pow_succ', mul_comm]
    refine Nat.le_of_mul_le_mul_right ?_ hmpos
    calc ((Fintype.piFinset (fun _ : Fin n => S)).filter
            (fun a => MvPolynomial.eval a p = 0)).card * S.card
        ≤ D * S.card ^ n := hZ
      _ = D * (S.card ^ (n - 1) * S.card) := by rw [hmn]
      _ = (D * S.card ^ (n - 1)) * S.card := by ring

end Work.Peluse.Prop36SW
