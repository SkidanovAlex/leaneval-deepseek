import Mathlib

namespace NK.LocalReciprocityLubinTate.Unramified

/-- **Order-theoretic core of the Eisenstein valuation computation.**

Let `Γ₀` be a linearly ordered commutative group with zero (`ℤᵐ⁰` in the application). Suppose
`a ^ D = c * s` with `c < 1` and `D ≥ 1`, and that the factor `s` is bounded in the three regimes
of `a`: by `a ^ (D - 1)` when `1 < a`, by `1` when `a = 1`, and equal to `1` when `a < 1`.

Then `a ^ D = c` and `a < 1`.

This is the numerical heart of the computation of the valuation of a root of an Eisenstein
polynomial: `a = w y` is the value of the root, `c = w π` the value of the constant term, and
`s = w (Σ_{i<D} (E.coeff i / π) y^i)` the value of the normalised "rest" of the polynomial. -/
theorem pow_eq_of_bounds {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (a c s : Γ₀) (D : ℕ) (hD : 1 ≤ D) (hc : c < 1) (h : a ^ D = c * s)
    (hs1 : 1 < a → s ≤ a ^ (D - 1)) (hs2 : a = 1 → s ≤ 1) (hs3 : a < 1 → s = 1) :
    a ^ D = c ∧ a < 1 := by
  -- Step 1: `a ≤ 1`.  If `a > 1`, all the terms of `s` are bounded by `a ^ (D-1)`, so
  -- `a ^ D = c * s ≤ a ^ (D-1) < a ^ D`.
  have ha_le : a ≤ 1 := by
    by_contra hcon
    have hcon' : 1 < a := not_le.mp hcon
    have hs := hs1 hcon'
    have hlt : a ^ (D - 1) < a ^ D := by
      have h' := mul_lt_mul_of_pos_left hcon' (pow_pos (zero_lt_one.trans hcon') (D - 1))
      rwa [mul_one, ← pow_succ, Nat.sub_add_cancel hD] at h'
    have hle : a ^ D ≤ a ^ (D - 1) := by
      calc a ^ D = c * s := h
        _ ≤ 1 * a ^ (D - 1) :=
            mul_le_mul (le_of_lt hc) hs (zero_le : (0 : Γ₀) ≤ s) (zero_le : (0 : Γ₀) ≤ 1)
        _ = a ^ (D - 1) := one_mul _
    exact absurd hle (not_le.mpr hlt)
  -- Step 2: `a ≠ 1`, since otherwise `1 = a ^ D = c * s ≤ c < 1`.
  have ha_ne : a ≠ 1 := by
    intro ha1
    have hs := hs2 ha1
    have hcontra : (1 : Γ₀) < 1 := by
      calc (1 : Γ₀) = c * s := by rw [← h, ha1, one_pow]
        _ ≤ c * 1 := mul_le_mul (le_refl c) hs (zero_le : (0 : Γ₀) ≤ s) (zero_le : (0 : Γ₀) ≤ c)
        _ = c := mul_one c
        _ < 1 := hc
    exact absurd hcontra (lt_irrefl 1)
  -- Step 3: `a < 1`, and then `s = 1`, so `a ^ D = c`.
  have ha_lt : a < 1 := lt_of_le_of_ne ha_le ha_ne
  exact ⟨by rw [h, hs3 ha_lt, mul_one], ha_lt⟩

/-- **The valuation of a root of an Eisenstein polynomial.**

Let `w : Valuation S ℤᵐ⁰` be a valuation on a field `S`, `E ∈ S[X]` a monic polynomial of degree
`D ≥ 1`, `y ∈ S` with `E(y) = 0`, and `π = E.coeff 0` with `w π < 1`.  Suppose moreover that all the
coefficients of `E` below the leading one have `w`-value at most `w π` (the "`E ≡ X^D` modulo `π`"
condition, i.e. `E` is Eisenstein at `π`).  Then `w (y^D) = w π`; in particular `w y < 1`, i.e. `y`
lies in the maximal ideal.

PROOF ROUTE.  Write `b_i := E.coeff i / π` for `i < D`, so `E = X^D + π·Σ_{i<D} b_i X^i`,
`b_0 = 1`, and `w (b_i) ≤ 1` (this is exactly the hypothesis `w (E.coeff i) ≤ w π`), and
`E(y) = 0` gives `y^D = -π·Σ_{i<D} b_i y^i` with `Σ_{i<D} b_i y^i = 1 + y·(Σ_{0<i<D} b_i y^{i-1})`.

* First `w y ≤ 1`: if `w y > 1`, then (working in the linearly ordered group `ℤᵐ⁰`)
  `w y ^ D = w (Σ_{i<D} π b_i y^i) ≤ max_i w π · w b_i · w y ^ i ≤ w y ^ (D-1)` (as `w π ≤ 1`),
  whence `w y ≤ 1`, a contradiction.
* Then `w y ≠ 1`: otherwise `1 = w y ^ D = w π · w (Σ_i b_i y^i) ≤ w π < 1`.
* So `w y < 1` and hence `w (y·Σ_{0<i<D} b_i y^{i-1}) ≤ w y < 1 = w 1`, so
  `w (Σ_{i<D} b_i y^i) = 1` (standard `Valuation.map_add_eq_of_lt_left` argument), giving
  `w y ^ D = w π`. -/
theorem valuation_root_pow_eq {S : Type*} [Field S] (w : Valuation S (WithZero (Multiplicative ℤ)))
    (y π : S) (E : Polynomial S) (D : ℕ) (hD : 1 ≤ D) (hEmon : E.Monic)
    (hEdeg : E.natDegree = D) (hEy : (Polynomial.aeval y) E = 0) (hπ : w π < 1)
    (hπ0 : π ≠ 0) (hcoeff : ∀ i, i < D → w (E.coeff i) ≤ w π) (hcoeff0 : E.coeff 0 = π) :
    w y ^ D = w π ∧ w y < 1 := by
  -- `E(y) = 0` for the ordinary evaluation.
  have hEy' : E.eval y = 0 := by
    rw [Polynomial.aeval_def] at hEy
    simpa [Polynomial.eval₂_id] using hEy
  -- Expand `E(y)` along the coefficient range and isolate the leading term.
  have hEval : ∑ i ∈ Finset.range (D + 1), E.coeff i * y ^ i = 0 := by
    rw [← hEdeg, ← Polynomial.eval_eq_sum_range y]
    exact hEy'
  have hcoeffD : E.coeff D = 1 := by
    rw [← hEdeg, Polynomial.coeff_natDegree, hEmon.leadingCoeff]
  have hsplit : ∑ i ∈ Finset.range (D + 1), E.coeff i * y ^ i
      = (∑ i ∈ Finset.range D, E.coeff i * y ^ i) + y ^ D := by
    rw [Finset.sum_range_succ, hcoeffD, one_mul]
  -- The normalised coefficients `b i = E.coeff i / π` and the "rest" `sg = Σ_{i<D} b i y^i`.
  set b : ℕ → S := fun i => E.coeff i / π with hb_def
  set sg : S := ∑ i ∈ Finset.range D, b i * y ^ i with hsg_def
  have hb0 : b 0 = 1 := by
    simp only [hb_def, hcoeff0, div_self hπ0]
  have hb : ∀ i, E.coeff i = π * b i := by
    intro i
    simp only [hb_def]
    rw [mul_comm, div_mul_cancel₀ (E.coeff i) hπ0]
  have hsum_eq : ∑ i ∈ Finset.range D, E.coeff i * y ^ i = π * sg := by
    rw [hsg_def, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hb i]
    ring
  -- The key identity `π * sg = - y ^ D`.
  have hkey : π * sg = -(y ^ D) := by
    have h1 : π * sg + y ^ D = 0 := by
      rw [← hsum_eq, ← hsplit]
      exact hEval
    exact eq_neg_of_add_eq_zero_left h1
  have hmain : w y ^ D = w π * w sg := by
    have h1 : w (π * sg) = w (y ^ D) := by rw [hkey, Valuation.map_neg]
    rw [Valuation.map_mul, Valuation.map_pow] at h1
    exact h1.symm
  -- `w (b i) ≤ 1`: divide `w (E.coeff i) ≤ w π` by `w π ≠ 0`.
  have hwπ_ne : w π ≠ 0 := (Valuation.ne_zero_iff w).mpr hπ0
  have hb_le : ∀ i, i < D → w (b i) ≤ 1 := by
    intro i hi
    have hmul : w (b i) * w π = w (E.coeff i) := by
      rw [← Valuation.map_mul]
      congr 1
      simp only [hb_def]
      exact div_mul_cancel₀ (E.coeff i) hπ0
    have hle : w (b i) * w π ≤ 1 * w π := by
      rw [hmul, one_mul]
      exact hcoeff i hi
    have h2 := mul_le_mul_left hle ((w π)⁻¹)
    simpa only [mul_assoc, mul_inv_cancel₀ hwπ_ne, mul_one, one_mul] using h2
  -- `sg = 1 + y * U` with `U = Σ_{0<i<D} b i y^{i-1}`.
  set U : S := ∑ k ∈ Finset.range (D - 1), b (k + 1) * y ^ k with hU_def
  have hsg_eq : sg = 1 + y * U := by
    have hD' : D = (D - 1) + 1 := (Nat.sub_add_cancel hD).symm
    calc sg = ∑ i ∈ Finset.range D, b i * y ^ i := hsg_def
      _ = ∑ i ∈ Finset.range ((D - 1) + 1), b i * y ^ i :=
            congrArg (fun n => ∑ i ∈ Finset.range n, b i * y ^ i) hD'
      _ = (∑ k ∈ Finset.range (D - 1), b (k + 1) * y ^ (k + 1)) + b 0 * y ^ 0 :=
            Finset.sum_range_succ' (fun i => b i * y ^ i) (D - 1)
      _ = (∑ k ∈ Finset.range (D - 1), y * (b (k + 1) * y ^ k)) + 1 := by
            rw [hb0, pow_zero, mul_one]
            congr 1
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [pow_succ']
            ring
      _ = y * U + 1 := by rw [hU_def, Finset.mul_sum]
      _ = 1 + y * U := by ring
  -- The three regime bounds on `w sg` demanded by `pow_eq_of_bounds`.
  have hs1 : 1 < w y → w sg ≤ w y ^ (D - 1) := by
    intro ha
    rw [hsg_def]
    apply Valuation.map_sum_le
    intro i hi
    have hi' : i < D := Finset.mem_range.mp hi
    rw [Valuation.map_mul, Valuation.map_pow]
    calc w (b i) * w y ^ i ≤ 1 * w y ^ i := mul_le_mul_left (hb_le i hi') _
      _ = w y ^ i := one_mul _
      _ ≤ w y ^ (D - 1) := pow_le_pow_right₀ (le_of_lt ha) (by omega)
  have hs2 : w y = 1 → w sg ≤ 1 := by
    intro ha
    rw [hsg_def]
    apply Valuation.map_sum_le
    intro i hi
    have hi' : i < D := Finset.mem_range.mp hi
    rw [Valuation.map_mul, Valuation.map_pow, ha, one_pow, mul_one]
    exact hb_le i hi'
  have hs3 : w y < 1 → w sg = 1 := by
    intro ha
    have hU_le : w U ≤ 1 := by
      rw [hU_def]
      apply Valuation.map_sum_le
      intro k hk
      have hk' : k + 1 < D := by
        have : k < D - 1 := Finset.mem_range.mp hk
        omega
      rw [Valuation.map_mul, Valuation.map_pow]
      calc w (b (k + 1)) * w y ^ k ≤ 1 * 1 :=
            mul_le_mul (hb_le (k + 1) hk')
              (pow_le_one₀ (zero_le : (0 : WithZero (Multiplicative ℤ)) ≤ w y) (le_of_lt ha))
              (zero_le : (0 : WithZero (Multiplicative ℤ)) ≤ w y ^ k)
              (zero_le : (0 : WithZero (Multiplicative ℤ)) ≤ 1)
        _ = 1 := one_mul 1
    have hyU : w (y * U) < w (1 : S) := by
      rw [Valuation.map_mul, Valuation.map_one]
      calc w y * w U ≤ w y * 1 :=
            mul_le_mul (le_refl (w y)) hU_le
              (zero_le : (0 : WithZero (Multiplicative ℤ)) ≤ w U)
              (zero_le : (0 : WithZero (Multiplicative ℤ)) ≤ w y)
        _ = w y := mul_one _
        _ < 1 := ha
    rw [hsg_eq, Valuation.map_add_eq_of_lt_left w hyU, Valuation.map_one w]
  exact pow_eq_of_bounds (w y) (w π) (w sg) D hD hπ hmain hs1 hs2 hs3

end NK.LocalReciprocityLubinTate.Unramified
