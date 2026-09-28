import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.evaldefs

/-!
# Uniform two-sided bounds for `ν_{d,n}` under the Euclidean norm

The Veronese map `ν_{d,n} : K^{n+1} → K^{N_{d,n}}` is homogeneous of degree `d` and injective
(for `d ≥ 1`), so on the unit sphere `‖ν(u)‖` is bounded above and below by positive constants,
and hence `‖ν(x)‖ ≍ ‖x‖^d` for *all* `x`.  Here we prove the two explicit elementary bounds

* `c₁ ‖x‖^d ≤ ‖ν(x)‖` with `c₁ = (1 / √(n+1))^d`, using that the largest coordinate
  `M = max_i |x_i|` satisfies `M^d = |ν(x)_{d·e_j}|` (a single monomial!) and `‖x‖ ≤ √(n+1) M`;
* `‖ν(x)‖ ≤ c₂ ‖x‖^d` with `c₂ = √(N_{d,n})`, using `|ν(x)_m| ≤ ‖x‖^d` monomial by monomial.

Both bounds hold for real vectors, and the integer case follows because `eNorm = rNorm ∘ toR`
and `toR ∘ ν_{d,n} = ν_{d,n} ∘ toR`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP

/-! ## The Euclidean norm of an integer vector is the real norm of its image -/

lemma eNorm_eq_rNorm_toR {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    eNorm v = rNorm (toR v) := rfl

lemma eNorm_toR_nonneg {ι : Type*} [Fintype ι] (v : ι → ℤ) : 0 ≤ eNorm v := by
  rw [eNorm_eq_rNorm_toR]; exact rNorm_nonneg _

/-- The change of scalars commutes with the Veronese map. -/
lemma toR_veronese (d n : ℕ) (x : Fin (n + 1) → ℤ) :
    toR (veronese d n x) = veronese d n (toR x) := by
  funext m
  simp only [toR, veronese]
  push_cast
  rfl

/-! ## The "pure power" monomial `d · e_j` -/

/-- The exponent vector of the monomial `x_j ^ d`. -/
def powMon (d n : ℕ) (j : Fin (n + 1)) : Mon d n :=
  ⟨fun i => ⟨if i = j then d else 0, by split <;> omega⟩, by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h⟩

/-- Evaluation of the pure-power monomial. -/
lemma veronese_powMon (d n : ℕ) (u : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    veronese d n u (powMon d n j) = u j ^ d := by
  simp only [veronese, powMon]
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ## A vector is controlled by the largest coordinate -/

lemma rNorm_le_sqrt_card_mul {ι : Type*} [Fintype ι] (u : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i, |u i| ≤ M) : rNorm u ≤ Real.sqrt (Fintype.card ι) * M := by
  have h2 : ∑ i, (u i) ^ 2 ≤ (Fintype.card ι : ℝ) * M ^ 2 := by
    calc ∑ i, (u i) ^ 2 ≤ ∑ _i : ι, M ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = (Fintype.card ι : ℝ) * M ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h3 : (Fintype.card ι : ℝ) * M ^ 2 = (Real.sqrt (Fintype.card ι) * M) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  calc rNorm u = Real.sqrt (∑ i, (u i) ^ 2) := rfl
    _ ≤ Real.sqrt ((Real.sqrt (Fintype.card ι) * M) ^ 2) := by
          rw [← h3]; exact Real.sqrt_le_sqrt h2
    _ = Real.sqrt (Fintype.card ι) * M := Real.sqrt_sq (by positivity)

/-! ## The two real bounds -/

/-- Lower bound: `(1/√(n+1))^d · ‖u‖^d ≤ ‖ν(u)‖`. -/
lemma veronese_rNorm_lower (d n : ℕ) (u : Fin (n + 1) → ℝ) :
    (1 / Real.sqrt ((n : ℝ) + 1)) ^ d * rNorm u ^ d ≤ rNorm (veronese d n u) := by
  classical
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_max_image Finset.univ (fun i => |u i|) Finset.univ_nonempty
  set M := |u j| with hMdef
  have hM0 : 0 ≤ M := abs_nonneg _
  have hcoord : ∀ i, |u i| ≤ M := fun i => hj i (Finset.mem_univ i)
  have hlow : M ^ d ≤ rNorm (veronese d n u) := by
    have h1 : |veronese d n u (powMon d n j)| = M ^ d := by
      rw [veronese_powMon, abs_pow]
    rw [← h1]
    exact abs_coord_le_rNorm (veronese d n u) (powMon d n j)
  have hup : rNorm u ≤ Real.sqrt ((n : ℝ) + 1) * M := by
    have h := rNorm_le_sqrt_card_mul u hM0 hcoord
    simpa using h
  have hx : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
  have hsd : (1 / Real.sqrt ((n : ℝ) + 1)) * (Real.sqrt ((n : ℝ) + 1) * M) = M := by
    rw [one_div, inv_mul_cancel_left₀ hx M]
  calc (1 / Real.sqrt ((n : ℝ) + 1)) ^ d * rNorm u ^ d
      ≤ (1 / Real.sqrt ((n : ℝ) + 1)) ^ d * (Real.sqrt ((n : ℝ) + 1) * M) ^ d := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (rNorm_nonneg u) hup d
    _ = ((1 / Real.sqrt ((n : ℝ) + 1)) * (Real.sqrt ((n : ℝ) + 1) * M)) ^ d := by
        rw [← mul_pow]
    _ = M ^ d := by rw [hsd]
    _ ≤ rNorm (veronese d n u) := hlow

/-- Upper bound: `‖ν(u)‖ ≤ √(N_{d,n}) · ‖u‖^d`. -/
lemma veronese_rNorm_upper (d n : ℕ) (u : Fin (n + 1) → ℝ) :
    rNorm (veronese d n u) ≤ Real.sqrt (NN d n) * rNorm u ^ d := by
  set R := rNorm u with hR
  have hR0 : 0 ≤ R := rNorm_nonneg u
  have hcoord : ∀ i, |u i| ≤ R := fun i => abs_coord_le_rNorm u i
  have hbnd : ∀ m : Mon d n, |veronese d n u m| ≤ R ^ d := by
    intro m
    have h := abs_prod_pow_le (fun i => (m.1 i : ℕ)) u hcoord
    rw [m.2] at h
    simpa [veronese] using h
  have hsum : ∑ m, (veronese d n u m) ^ 2 ≤ (NN d n : ℝ) * (R ^ d) ^ 2 := by
    calc ∑ m, (veronese d n u m) ^ 2 ≤ ∑ _m : Mon d n, (R ^ d) ^ 2 := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hbnd m) 2
      _ = (NN d n : ℝ) * (R ^ d) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc rNorm (veronese d n u) = Real.sqrt (∑ m, (veronese d n u m) ^ 2) := rfl
    _ ≤ Real.sqrt ((NN d n : ℝ) * (R ^ d) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (NN d n) * Real.sqrt ((R ^ d) ^ 2) := by
        rw [Real.sqrt_mul (by positivity)]
    _ = Real.sqrt (NN d n) * R ^ d := by rw [Real.sqrt_sq (pow_nonneg hR0 d)]

/-! ## The stated result -/

theorem eNorm_veronese_bounds (d n : ℕ) (hd : 1 ≤ d) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ x : Fin (n + 1) → ℤ,
      c₁ * eNorm x ^ d ≤ eNorm (veronese d n x) ∧
      eNorm (veronese d n x) ≤ c₂ * eNorm x ^ d := by
  refine ⟨(1 / Real.sqrt ((n : ℝ) + 1)) ^ d, Real.sqrt (NN d n), ?_, ?_, ?_⟩
  · positivity
  · have : (0 : ℝ) < NN d n := by
      have h := one_le_NN d n
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h)
    exact Real.sqrt_pos_of_pos this
  · intro x
    rw [eNorm_eq_rNorm_toR (veronese d n x), toR_veronese, eNorm_eq_rNorm_toR x]
    exact ⟨veronese_rNorm_lower d n (toR x), veronese_rNorm_upper d n (toR x)⟩

end Work.HP
