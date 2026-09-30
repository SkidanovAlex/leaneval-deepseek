import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ## `Mu_lower_bound`: the number of unknowns of the BW §13 system

With `d = [K : ℚ]`, `D = pD r d σ = 2 r^r (32d)^{r+1} log(2rd) ∏σ`,
`D₀ = ⌊rD/(2 log(2rd))⌋` and `D_j = ⌊D/(r d σ_j)⌋`, the two elementary floor estimates

* `D₀ + 1 > r^{r+1} (32d)^{r+1} ∏_j σ_j`   (since `rD/(2 log(2rd))` equals that number)
* `D_j + 1 > D/(r d σ_j)`

give, after multiplying the `r` inequalities for the `D_j` and cancelling `∏_j σ_j`,

`r d 32^{r+1} D^r ≤ (D₀+1) ∏_j (D_j+1)`,

and multiplying by `h ≥ 0` yields the statement (which therefore holds with equality
asymptotically, the floors being the only loss). -/

/-- Pure algebra: the product of the "large" factor `r^{r+1}(32d)^{r+1}∏σ` with the `r`
factors `D/(rdσ_j)` equals `r d 32^{r+1} D^r`. -/
theorem Mu_algebra_key {r d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, σ j ≠ 0) (D : ℝ) :
    (r : ℝ) * (d : ℝ) * (32 : ℝ) ^ (r + 1) * D ^ r
      = ((r : ℝ) ^ (r + 1) * (32 * d : ℝ) ^ (r + 1) * ∏ j, σ j)
          * ∏ j, (D / ((r : ℝ) * (d : ℝ) * σ j)) := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hPW : (∏ j : Fin r, (D / ((r : ℝ) * (d : ℝ) * σ j))) * (∏ j : Fin r, σ j)
      = (D / ((r : ℝ) * (d : ℝ))) ^ r := by
    rw [← Finset.prod_mul_distrib]
    have hterm : ∀ j : Fin r,
        D / ((r : ℝ) * (d : ℝ) * σ j) * σ j = D / ((r : ℝ) * (d : ℝ)) := by
      intro j
      have hj : σ j ≠ 0 := hσ j
      field_simp
    simp only [hterm]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show ((r : ℝ) ^ (r + 1) * (32 * d : ℝ) ^ (r + 1) * ∏ j, σ j)
        * ∏ j, (D / ((r : ℝ) * (d : ℝ) * σ j))
      = (r : ℝ) ^ (r + 1) * (32 * d : ℝ) ^ (r + 1)
        * ((∏ j, σ j) * ∏ j, (D / ((r : ℝ) * (d : ℝ) * σ j))) from by ring]
  rw [show (∏ j : Fin r, σ j) * (∏ j : Fin r, (D / ((r : ℝ) * (d : ℝ) * σ j)))
        = (D / ((r : ℝ) * (d : ℝ))) ^ r from by rw [mul_comm]; exact hPW]
  simp only [mul_pow, div_pow, pow_succ]
  field_simp

/-- Floor-and-product combination: if `x ≤ N₀` and `y i ≤ N i` where the `N` are natural
numbers and `x, y` are nonnegative reals, then `x · ∏ y ≤ (N₀ · ∏ N : ℕ)`. -/
theorem mul_prod_le_cast_aux {ι : Type*} [Fintype ι] (x : ℝ) (N0 : ℕ) (y : ι → ℝ)
    (N : ι → ℕ) (hx : x ≤ (N0 : ℝ)) (hy : ∀ i, y i ≤ (N i : ℝ))
    (hy0 : ∀ i, 0 ≤ y i) :
    x * ∏ i, y i ≤ (((N0 * ∏ i, N i) : ℕ) : ℝ) := by
  have h1 : ∏ i, y i ≤ ∏ i, (N i : ℝ) :=
    Finset.prod_le_prod₀ (fun i _ => hy0 i) (fun i _ => hy i)
  have h2 : x * ∏ i, y i ≤ (N0 : ℝ) * ∏ i, (N i : ℝ) :=
    mul_le_mul hx h1 (Finset.prod_nonneg (fun i _ => hy0 i)) (Nat.cast_nonneg N0)
  rwa [← Nat.cast_prod, ← Nat.cast_mul] at h2

/-- The core inequality, with `d` an explicit natural number (the degree of `K`). -/
theorem Mu_lower_bound_core {r h d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    (h : ℝ) * (r : ℝ) * (d : ℝ) * (32 : ℝ) ^ (r + 1) * (pD r d σ) ^ r
      ≤ ((h * (pD0 r d σ + 1) * ∏ j, (pDj r d σ j + 1) : ℕ) : ℝ) := by
  have hr1 : 1 ≤ r := by omega
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hσpos : ∀ j : Fin r, (0 : ℝ) < σ j := by
    intro j
    have h1 : (0 : ℝ) < 1 / (d : ℝ) := by positivity
    linarith [hσ j]
  have hlog : (0 : ℝ) < Real.log (2 * (r : ℝ) * (d : ℝ)) := by
    apply Real.log_pos
    nlinarith
  have hWpos : (0 : ℝ) < ∏ j : Fin r, σ j := Finset.prod_pos (fun j _ => hσpos j)
  have hDpos : (0 : ℝ) < pD r d σ := by
    rw [pD]
    positivity
  have hx0 : 0 ≤ (r : ℝ) * pD r d σ / (2 * Real.log (2 * (r : ℝ) * (d : ℝ))) := by
    positivity
  have hx : (r : ℝ) * pD r d σ / (2 * Real.log (2 * (r : ℝ) * (d : ℝ)))
      ≤ ((pD0 r d σ + 1 : ℕ) : ℝ) := by
    have h : (r : ℝ) * pD r d σ / (2 * Real.log (2 * (r : ℝ) * (d : ℝ)))
        ≤ ((pD0 r d σ : ℕ) : ℝ) + 1 := by
      simpa only [pD0] using (Nat.lt_floor_add_one
        ((r : ℝ) * pD r d σ / (2 * Real.log (2 * (r : ℝ) * (d : ℝ))))).le
    push_cast
    linarith
  have hy : ∀ j : Fin r, pD r d σ / ((r : ℝ) * (d : ℝ) * σ j)
      ≤ ((pDj r d σ j + 1 : ℕ) : ℝ) := by
    intro j
    have h : pD r d σ / ((r : ℝ) * (d : ℝ) * σ j)
        ≤ ((pDj r d σ j : ℕ) : ℝ) + 1 := by
      simpa only [pDj] using (Nat.lt_floor_add_one
        (pD r d σ / ((r : ℝ) * (d : ℝ) * σ j))).le
    push_cast
    linarith
  have hy0 : ∀ j : Fin r, 0 ≤ pD r d σ / ((r : ℝ) * (d : ℝ) * σ j) := by
    intro j
    have h2 : (0 : ℝ) < (r : ℝ) * (d : ℝ) * σ j := by
      have := hσpos j
      positivity
    exact le_of_lt (div_pos hDpos h2)
  have hcore := mul_prod_le_cast_aux
    ((r : ℝ) * pD r d σ / (2 * Real.log (2 * (r : ℝ) * (d : ℝ))))
    (pD0 r d σ + 1) (fun j : Fin r => pD r d σ / ((r : ℝ) * (d : ℝ) * σ j))
    (fun j : Fin r => pDj r d σ j + 1) hx hy hy0
  have halg := Mu_algebra_key hr1 hd σ (fun j => ne_of_gt (hσpos j)) (pD r d σ)
  have hx_eq : (r : ℝ) * pD r d σ / (2 * Real.log (2 * (r : ℝ) * (d : ℝ)))
      = (r : ℝ) ^ (r + 1) * (32 * (d : ℝ)) ^ (r + 1) * ∏ j : Fin r, σ j := by
    have h2L : 2 * Real.log (2 * (r : ℝ) * (d : ℝ)) ≠ 0 := by
      have h : (0 : ℝ) < 2 * Real.log (2 * (r : ℝ) * (d : ℝ)) := by linarith
      exact ne_of_gt h
    rw [pD, div_eq_iff h2L, pow_succ']
    ring
  have hcore' : (r : ℝ) * (d : ℝ) * (32 : ℝ) ^ (r + 1) * (pD r d σ) ^ r
      ≤ (((pD0 r d σ + 1) * ∏ j : Fin r, (pDj r d σ j + 1) : ℕ) : ℝ) := by
    calc (r : ℝ) * (d : ℝ) * (32 : ℝ) ^ (r + 1) * (pD r d σ) ^ r
        = ((r : ℝ) ^ (r + 1) * (32 * (d : ℝ)) ^ (r + 1) * ∏ j : Fin r, σ j)
            * ∏ j : Fin r, (pD r d σ / ((r : ℝ) * (d : ℝ) * σ j)) := halg
      _ = ((r : ℝ) * pD r d σ / (2 * Real.log (2 * (r : ℝ) * (d : ℝ))))
            * ∏ j : Fin r, (pD r d σ / ((r : ℝ) * (d : ℝ) * σ j)) := by rw [← hx_eq]
      _ ≤ (((pD0 r d σ + 1) * ∏ j : Fin r, (pDj r d σ j + 1) : ℕ) : ℝ) := hcore
  have hmain := mul_le_mul_of_nonneg_left hcore' (Nat.cast_nonneg h)
  calc (h : ℝ) * (r : ℝ) * (d : ℝ) * (32 : ℝ) ^ (r + 1) * (pD r d σ) ^ r
      = (h : ℝ) * ((r : ℝ) * (d : ℝ) * (32 : ℝ) ^ (r + 1) * (pD r d σ) ^ r) := by ring
    _ ≤ (h : ℝ) * ((((pD0 r d σ + 1) * ∏ j : Fin r, (pDj r d σ j + 1) : ℕ) : ℝ)) := hmain
    _ = (((h * (pD0 r d σ + 1) * ∏ j : Fin r, (pDj r d σ j + 1) : ℕ) : ℝ)) := by
          push_cast
          ring

theorem Mu_lower_bound {K : Type*} [Field K] [NumberField K] (r h : ℕ) (hr : 2 ≤ r) (σ : Fin r → ℝ) (hσ : ∀ j, 1 / (Module.finrank ℚ K : ℝ) ≤ σ j) : (h : ℝ) * (r : ℝ) * (Module.finrank ℚ K : ℝ) * (32 : ℝ) ^ (r + 1) * (pD r (Module.finrank ℚ K) σ) ^ r ≤ ((h * (pD0 r (Module.finrank ℚ K) σ + 1) * ∏ j, (pDj r (Module.finrank ℚ K) σ j + 1) : ℕ) : ℝ) := by
  exact Mu_lower_bound_core hr
    (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨1, one_ne_zero⟩) σ hσ

end Work.BW
