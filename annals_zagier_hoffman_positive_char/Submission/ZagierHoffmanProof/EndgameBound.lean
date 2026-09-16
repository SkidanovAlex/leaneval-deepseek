import Submission.ZagierHoffmanProof.EndgameRow

/-!
# §3.3 of the two-term endgame: the divisibilities coming from the two rows

With `L := X - C θ` (linear), `W := X - C (θ^q) = σ(L)`, `E := L^q = X^q - θ^q = σ`-image of `W^q`,
`P := X^q - X` and `q := Nat.card F`, this module proves

* ★ **`W^k ∣ σ(Z) → L^k ∣ Z`** (`frobenius_multiplicity`) — the "Frobenius multiplicity identity":
  the multiplicity of `θ^q` as a root of `σ(Z)` equals the multiplicity of `θ` as a root of `Z`;
* `tw_k_row_factor` ⟹ **`L^q ∣ Y`** (using `IsCoprime (L^q) P`);
* the empty row `Q·σ(Z) = σ(Q)·W^w·(Z + Y + Q·A₁·H_w)` (with `IsCoprime W Q`) ⟹ **`L^w ∣ Z`**.

These are exactly the two divisibilities that the `θ`-degree estimate of `PLAN.md` §«SESSION 352»
needs: they let one write `Z = L^w·u` and `Y = E·v`, clear the row to the polynomial identity
`Q·σ(u·P) = σ(Q)·(L^w·u·P + E·(k·A₁·P - A₂)·Q - A₁·W·P·Q)`, and compare `degPoly`s.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial
open scoped WithZero

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The Frobenius multiplicity identity -/

/-- `σ(L) = W`, i.e. `polyTwist 1 (X - C θ) = X - C (θ^q)`. -/
lemma polyTwist_X_sub_C_theta :
    polyTwist (q := Nat.card F) 1 (Polynomial.X - Polynomial.C (ambTheta F))
      = Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) := by
  rw [polyTwist_sub, polyTwist_X, polyTwist_C, pow_one]

/-- ★ **`σ(p)(x^q) = p(x)^q`.**  Evaluating the Frobenius twist at the `q`-th power of `x` is the
`q`-th power of the evaluation. -/
lemma eval_polyTwist_one_pow (p : Polynomial (Ambient F)) (x : Ambient F) :
    (polyTwist (q := Nat.card F) 1 p).eval (x ^ Nat.card F) = (p.eval x) ^ Nat.card F := by
  rw [polyTwist, polyTwistHom_apply, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range,
    Polynomial.eval_eq_sum_range, FrobPow.sum_pow_finset]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [frobPowHom_apply, pow_one, mul_pow, ← pow_mul, Nat.mul_comm]

/-- `L ∣ Z ↔ Z(θ) = 0`. -/
lemma dvd_X_sub_C_theta_iff (Z : Polynomial (Ambient F)) :
    (Polynomial.X - Polynomial.C (ambTheta F)) ∣ Z ↔ Z.eval (ambTheta F) = 0 :=
  Polynomial.dvd_iff_isRoot

/-- ★★ **The Frobenius multiplicity identity**: `W^k ∣ σ(Z)` implies `L^k ∣ Z`, where
`L = X - C θ` and `W = σ(L) = X - C (θ^q)`. -/
theorem frobenius_multiplicity (k : ℕ) (Z : Polynomial (Ambient F))
    (h : (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ k
      ∣ polyTwist (q := Nat.card F) 1 Z) :
    (Polynomial.X - Polynomial.C (ambTheta F)) ^ k ∣ Z := by
  induction k generalizing Z with
  | zero => exact one_dvd Z
  | succ k ih =>
      obtain ⟨S, hS⟩ := h
      have hW : (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F))
          ∣ polyTwist (q := Nat.card F) 1 Z :=
        ⟨(Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ k * S, by
          rw [hS]; ring⟩
      have hev : (polyTwist (q := Nat.card F) 1 Z).eval ((ambTheta F) ^ Nat.card F) = 0 := by
        obtain ⟨T, hT⟩ := hW
        rw [hT, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
          sub_self, zero_mul]
      have hL : (Polynomial.X - Polynomial.C (ambTheta F)) ∣ Z := by
        rw [dvd_X_sub_C_theta_iff F Z]
        rw [eval_polyTwist_one_pow F Z (ambTheta F)] at hev
        exact (pow_eq_zero_iff (by have := carlitz_card_ge_two F; omega :
          Nat.card F ≠ 0)).mp hev
      obtain ⟨Z₁, hZ₁⟩ := hL
      have h1 : polyTwist (q := Nat.card F) 1 Z
          = (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F))
            * polyTwist (q := Nat.card F) 1 Z₁ := by
        rw [hZ₁, polyTwist_mul, polyTwist_X_sub_C_theta F]
      have hW0 : (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) :
          Polynomial (Ambient F)) ≠ 0 := Polynomial.X_sub_C_ne_zero _
      have h2 : (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ k
          ∣ polyTwist (q := Nat.card F) 1 Z₁ :=
        ⟨S, mul_left_cancel₀ hW0 (by rw [← h1, hS]; ring)⟩
      obtain ⟨Z₂, hZ₂⟩ := ih Z₁ h2
      exact ⟨Z₂, by rw [hZ₁, hZ₂]; ring⟩

/-- The same, for a direct input `W^w ∣ σ Z`. -/
theorem dvd_X_sub_C_theta_pow_of_dvd_twist (w : ℕ) (Z : Polynomial (Ambient F))
    (h : (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
      ∣ polyTwist (q := Nat.card F) 1 Z) :
    (Polynomial.X - Polynomial.C (ambTheta F)) ^ w ∣ Z :=
  frobenius_multiplicity F w Z h

/-! ## §2. The two divisibilities coming from the rows -/

/-- ★ **`(X - θ)^q ∣ Y`**, from the `(k)`-row.  `tw_k_row_factor` gives
`Y·(X^q - X) = A₂·(θ^q - X^q)·Q = -A₂·(X-θ)^q·Q`, and `(X-θ)^q` is coprime to `X^q - X`
(`isCoprime_X_sub_C_theta`). -/
theorem dvd_theta_pow_of_tw_k_row {A₂ Q Y : Polynomial (Ambient F)}
    (hQ0 : Q ≠ 0) (hA₂ : ∀ n, A₂.coeff n ∈ ambF F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Y
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
        * (Y + Q * A₂)) :
    (Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F ∣ Y := by
  have hfac := tw_k_row_factor F hQ0 hA₂ hrow
  have hE : (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F :
      Polynomial (Ambient F)) = -((Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F) := by
    rw [X_sub_C_pow_card F (ambTheta F)]; ring
  have hLq : (Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F
      ∣ Y * (Polynomial.X ^ Nat.card F - Polynomial.X) :=
    ⟨-A₂ * Q, by rw [hfac, hE]; ring⟩
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F)
      (Polynomial.X ^ Nat.card F - Polynomial.X) :=
    (isCoprime_X_sub_C_theta F (Nat.card F) rfl).symm.pow_left
  exact hcop.dvd_of_dvd_mul_right hLq

/-- ★★ **`(X - θ)^w ∣ Z`**, from the empty row: `W^w = σ((X-θ)^w)` divides `Q·σ(Z)`, `W` is
coprime to `Q`, so `W^w ∣ σ(Z)`, and the Frobenius multiplicity identity gives `(X-θ)^w ∣ Z`. -/
theorem dvd_theta_pow_w_of_empty_row {A₁ A₂ Q Y Z : Polynomial (Ambient F)} {w : ℕ}
    (hcop : IsCoprime (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) Q)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    (Polynomial.X - Polynomial.C (ambTheta F)) ^ w ∣ Z := by
  have h1 : (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
      ∣ polyTwist (q := Nat.card F) 1 Z * Q := by
    have h : (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        ∣ Q * polyTwist (q := Nat.card F) 1 Z :=
      ⟨polyTwist (q := Nat.card F) 1 Q * (Z + Y + Q * A₁ * ambH F w), by rw [hrow]; ring⟩
    rwa [mul_comm] at h
  exact frobenius_multiplicity F w Z (hcop.pow_left.dvd_of_dvd_mul_right h1)

/-! ## §3. Killing the hypothesis: the common-denominator normalisation

`dvd_theta_pow_w_of_empty_row` above needs `IsCoprime W Q`.  That hypothesis is **not** implied by
`Q(θ) = 1`: the polynomial `Q = (X - C (θ^q))/(θ - θ^q)` has `Q(θ) = 1` and `Q(θ^q) = 0`, i.e.
`W ∣ Q`.  So no argument from the row alone can remove it.

The paper avoids it by changing normalisation: its unknowns are `δ_t = b·Z_t/Q` with `b ∈ F_q[t]` a
**common denominator** (CPY19 Prop. 2.2.1), so that the `Q` disappears from the recursion.  The two
lemmas below carry out exactly that change, and *reduce the residual input to the single
common-denominator hypothesis* `Q ∣ b·Z` and `Q ∣ b·Y`:

* `exists_dvd_theta_pow_of_empty_row`: if `b` clears the two denominators, then **`(X-θ)^w ∣ b·Z`**
  (and even: `b·Z = Q·η` with `(X-θ)^w ∣ η`);
* `frobenius_multiplicity` in the converse direction, so that `(X-θ)^w ∣ b·Z` together with
  `IsCoprime ((X-θ)^w) b` returns `(X-θ)^w ∣ Z`. -/

/-- The converse of `frobenius_multiplicity`: `(X-θ)^k ∣ Z` implies `W^k ∣ σ Z`. -/
theorem dvd_twist_of_dvd_X_sub_C_theta_pow (k : ℕ) (Z : Polynomial (Ambient F))
    (h : (Polynomial.X - Polynomial.C (ambTheta F)) ^ k ∣ Z) :
    (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ k
      ∣ polyTwist (q := Nat.card F) 1 Z := by
  obtain ⟨Z₁, rfl⟩ := h
  exact ⟨polyTwist (q := Nat.card F) 1 Z₁,
    by rw [polyTwist_mul, polyTwist_pow, polyTwist_X_sub_C_theta]⟩

/-- ★★ **The empty row in the common-denominator normalisation.**  If `b` (with `F_q`-coefficients)
clears the denominators of `Z/Q` and of `Y/Q`, then the two dividers `Q` and `σ(Q)` cancel in the
row and one is left with `σ(η) = W^w·(η + R₁ + b·A₁·H_w)` for the polynomial `η = b·Z/Q`; hence
`(X-θ)^w ∣ η` and `(X-θ)^w ∣ b·Z`. -/
theorem exists_dvd_theta_pow_of_empty_row {A₁ A₂ Q Y Z b : Polynomial (Ambient F)} {w : ℕ}
    (hQ0 : Q ≠ 0) (hb : ∀ n, b.coeff n ∈ ambF F)
    (hQZ : Q ∣ b * Z) (hQY : Q ∣ b * Y)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    ∃ η : Polynomial (Ambient F),
      b * Z = Q * η ∧ (Polynomial.X - Polynomial.C (ambTheta F)) ^ w ∣ η := by
  obtain ⟨η, hη⟩ := hQZ
  obtain ⟨R₁, hR₁⟩ := hQY
  have hσb : polyTwist (q := Nat.card F) 1 b = b := polyTwist_one_fixed F b hb
  have hσQ : polyTwist (q := Nat.card F) 1 Q ≠ 0 := by
    intro h
    exact hQ0 (polyTwist_one_injective F (by simpa using h))
  set W : Polynomial (Ambient F) := Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)
    with hW
  have hC : b * (Z + Y + Q * A₁ * ambH F w) = Q * (η + R₁ + b * A₁ * ambH F w) := by
    rw [mul_add, mul_add, hη, hR₁]; ring
  have hbσ : b * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q * polyTwist (q := Nat.card F) 1 η := by
    have h : polyTwist (q := Nat.card F) 1 (b * Z) = polyTwist (q := Nat.card F) 1 (Q * η) := by
      rw [hη]
    rwa [polyTwist_mul, polyTwist_mul, hσb] at h
  have hL : Q * (polyTwist (q := Nat.card F) 1 Q * polyTwist (q := Nat.card F) 1 η)
      = b * (Q * polyTwist (q := Nat.card F) 1 Z) := by
    rw [← hbσ]; ring
  have hR : b * (Q * polyTwist (q := Nat.card F) 1 Z)
      = Q * (polyTwist (q := Nat.card F) 1 Q * W ^ w * (η + R₁ + b * A₁ * ambH F w)) := by
    rw [hrow]
    rw [show b * (polyTwist (q := Nat.card F) 1 Q * W ^ w * (Z + Y + Q * A₁ * ambH F w))
        = (polyTwist (q := Nat.card F) 1 Q * W ^ w)
          * (b * (Z + Y + Q * A₁ * ambH F w)) from by ring, hC]
    ring
  have h4 := mul_left_cancel₀ hQ0 (hL.trans hR)
  have h5 : polyTwist (q := Nat.card F) 1 η = W ^ w * (η + R₁ + b * A₁ * ambH F w) := by
    rw [mul_assoc] at h4
    exact mul_left_cancel₀ hσQ h4
  refine ⟨η, hη, frobenius_multiplicity F w η ⟨η + R₁ + b * A₁ * ambH F w, h5⟩⟩

/-! ## §4. The `IsCoprime ((X-θ)^w) b` input for `b ∈ F_q[X]`

`exists_dvd_theta_pow_of_empty_row` produces `(X-θ)^w ∣ b·Z` for the common denominator `b`.  To
return `(X-θ)^w ∣ Z` one needs `IsCoprime ((X-θ)^w) b`, which holds because `b`, having
`F_q`-coefficients, does not vanish at the transcendental `θ`:

`b ≠ 0 → b(θ) ≠ 0 → (X - C θ) ∤ b → IsCoprime (X - C θ) b → IsCoprime ((X - C θ)^w) b`.

The first two steps are proved here (`degPoly_eq_zero_of_coeff_mem_ambF`,
`eval_theta_ne_zero_of_coeff_mem_ambF`); the last two are `Polynomial.dvd_iff_isRoot` /
`Polynomial.prime_X_sub_C` / `IsCoprime.pow_left`, modelled on `Solve64.isCoprime_X_sub_C_theta`.
-/

/-- A polynomial with `F_q`-coefficients has `θ`-degree `0`. -/
lemma degPoly_eq_zero_of_coeff_mem_ambF {b : Polynomial (Ambient F)}
    (hb : ∀ n, b.coeff n ∈ ambF F) : degPoly F b = 0 := by
  refine le_antisymm (degPoly_le_of_coeff_le F fun n => ?_) (Nat.zero_le _)
  rcases eq_or_ne (b.coeff n) 0 with h | h
  · rw [h, degTheta_zero]
  · rw [degTheta_of_mem_ambF F (hb n) h]

/-- ★ **`b(θ) ≠ 0` for `b ∈ F_q[X]`, `b ≠ 0`** — the transcendence of `θ` over `F_q`, applied to
the `F`-avatar `b₀` of `b` obtained coefficientwise from `eq_range_ambCoeff_of_mem_ambF`. -/
lemma eval_theta_ne_zero_of_coeff_mem_ambF {b : Polynomial (Ambient F)}
    (hb : ∀ n, b.coeff n ∈ ambF F) (hb0 : b ≠ 0) : b.eval (ambTheta F) ≠ 0 := by
  classical
  intro h
  set c : ℕ → F := fun n => Classical.choose (eq_range_ambCoeff_of_mem_ambF F (hb n)) with hc
  have hcoe : ∀ n, ambCoeff F (c n) = b.coeff n := fun n =>
    Classical.choose_spec (eq_range_ambCoeff_of_mem_ambF F (hb n))
  set b₀ : Polynomial F := b.sum (fun n _ => Polynomial.C (c n) * Polynomial.X ^ n) with hb₀
  have hcoeff : ∀ m, b₀.coeff m = if m ∈ b.support then c m else 0 := by
    intro m
    rw [hb₀, Polynomial.coeff_sum, Polynomial.sum_def]
    have h1 : ∀ n ∈ b.support, (Polynomial.C (c n) * Polynomial.X ^ n).coeff m
        = (if m = n then c n else 0) := by
      intro n _
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hmn : m = n
      · simp [hmn]
      · simp [hmn]
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq]
  have hmap : b₀.map (algebraMap F (Ambient F)) = b := by
    ext m
    rw [Polynomial.coeff_map, hcoeff m, algebraMap_ambient_eq]
    by_cases hm : m ∈ b.support
    · rw [if_pos hm, hcoe m]
    · rw [if_neg hm, map_zero]
      have hzero : b.coeff m = 0 := by
        by_contra hc
        exact hm (Polynomial.mem_support_iff.mpr hc)
      exact hzero.symm
  have hb₀0 : b₀ = 0 :=
    ambTheta_transcendental F b₀ (by rw [← (show b.eval (ambTheta F)
      = b₀.eval₂ (algebraMap F (Ambient F)) (ambTheta F) from by
        rw [← Polynomial.eval_map, hmap])]; exact h)
  have hb0' : b = 0 := by rw [← hmap, hb₀0, Polynomial.map_zero]
  exact hb0 hb0'

/-- **`(X - C θ) ∤ b`** for `b ∈ F_q[X]`, `b ≠ 0`. -/
lemma not_dvd_X_sub_C_theta_of_coeff_mem_ambF {b : Polynomial (Ambient F)}
    (hb : ∀ n, b.coeff n ∈ ambF F) (hb0 : b ≠ 0) :
    ¬ (Polynomial.X - Polynomial.C (ambTheta F)) ∣ b := by
  intro hdiv
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def] at hdiv
  exact eval_theta_ne_zero_of_coeff_mem_ambF F hb hb0 hdiv

/-- ★★ **Euclid's lemma for `L = X - C θ`**: a power of the prime `L` dividing `b·Z` with
`b ∈ F_q[X]`, `b ≠ 0` already divides `Z`.  This is what turns
`exists_dvd_theta_pow_of_empty_row`'s output `(X-θ)^w ∣ b·Z` into `(X-θ)^w ∣ Z`, with **no**
`IsCoprime` input. -/
theorem dvd_theta_pow_of_dvd_mul_of_coeff_mem_ambF {b Z : Polynomial (Ambient F)} {w : ℕ}
    (hb : ∀ n, b.coeff n ∈ ambF F) (hb0 : b ≠ 0)
    (h : (Polynomial.X - Polynomial.C (ambTheta F)) ^ w ∣ b * Z) :
    (Polynomial.X - Polynomial.C (ambTheta F)) ^ w ∣ Z := by
  induction w generalizing Z with
  | zero => exact one_dvd Z
  | succ w ih =>
      have hprime : Prime (Polynomial.X - Polynomial.C (ambTheta F)) :=
        Polynomial.prime_X_sub_C (ambTheta F)
      have hL0 : (Polynomial.X - Polynomial.C (ambTheta F) : Polynomial (Ambient F)) ≠ 0 :=
        Polynomial.X_sub_C_ne_zero _
      have hdvd : (Polynomial.X - Polynomial.C (ambTheta F)) ∣ b * Z :=
        dvd_trans (dvd_pow_self _ (by omega)) h
      rcases hprime.dvd_or_dvd hdvd with hb' | hZ
      · exact absurd hb' (not_dvd_X_sub_C_theta_of_coeff_mem_ambF F hb hb0)
      · obtain ⟨Z₁, hZ₁⟩ := hZ
        obtain ⟨c, hc⟩ := h
        have h2 : (Polynomial.X - Polynomial.C (ambTheta F)) ^ w ∣ b * Z₁ := by
          refine ⟨c, mul_left_cancel₀ hL0 ?_⟩
          calc (Polynomial.X - Polynomial.C (ambTheta F)) * (b * Z₁)
              = b * Z := by rw [hZ₁]; ring
            _ = (Polynomial.X - Polynomial.C (ambTheta F)) ^ (w + 1) * c := hc
            _ = (Polynomial.X - Polynomial.C (ambTheta F))
                  * ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w * c) := by
                  rw [pow_succ]; ring
        obtain ⟨Z₂, hZ₂⟩ := ih h2
        exact ⟨Z₂, by rw [hZ₁, hZ₂]; ring⟩

/-! ## §6. `Y/Q` needs no denominator theory at all: `P = X^q - X` clears it -/

/-- ★ **`(X^q - X)` clears the denominator of `Y/Q`.**  `tw_k_row_factor` gives
`Y·P = A₂·(θ^q - X^q)·Q`, and `P = X^q - X` has `F_q`-coefficients, so it is a legitimate
common denominator for `Y/Q` with no CPY19 input at all.  Hence only `Z/Q` needs the
denominator theorem. -/
theorem dvd_mul_of_tw_k_row_factor {A₂ Q Y : Polynomial (Ambient F)}
    (hfac : Y * (Polynomial.X ^ Nat.card F - Polynomial.X)
      = A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F) * Q) :
    Q ∣ (Polynomial.X ^ Nat.card F - Polynomial.X) * Y :=
  ⟨A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F), by
    rw [mul_comm (Polynomial.X ^ Nat.card F - Polynomial.X) Y, hfac]
    ring⟩

/-! ## §7. `W` does not divide `σ(Q)`: a free coprimality from `Q(θ) = 1` -/

/-- ★ **`X - C(θ^q)` does not divide `σ(Q)`** whenever `Q(θ) = 1`.  `(σQ)(θ^q) = Q(θ)^q = 1 ≠ 0`
by `eval_polyTwist_one_pow`, and `T ∣ σQ ↔ (σQ)(θ^q) = 0` since `T = X - C(θ^q)` is linear monic.
⚠ Contrast: `W ∣ Q` itself is **not** implied by `Q(θ) = 1` (counterexample in `PLAN.md`
§«SESSION 352» §«continued 4»), so this gives coprimality of `W` with `σ(Q)`, not with `Q`. -/
lemma not_dvd_X_sub_C_theta_pow_of_eval {Q : Polynomial (Ambient F)}
    (hQθ : Q.eval (ambTheta F) = 1) (hq : 2 ≤ Nat.card F) :
    ¬ (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ∣
      polyTwist (q := Nat.card F) 1 Q := by
  intro hdiv
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def] at hdiv
  rw [eval_polyTwist_one_pow F Q (ambTheta F), hQθ] at hdiv
  have hq0 : Nat.card F ≠ 0 := by omega
  rw [show (1 : Ambient F) ^ Nat.card F = 1 from one_pow _] at hdiv
  exact one_ne_zero hdiv

/-! ## §8. The two rows evaluated at `X = θ`, and the relation they force -/

/-- ★ **The two rows at `X = θ`.**  At `X = θ` (unlike at `X = θ^q`, where `W^w` kills everything)
the two rows give, using `Q(θ) = 1` and `Z(θ) = Y(θ) = 0` (the ABP criterion's `P_t(θ) = 0`),

```
(σY)(θ) = (σQ)(θ) · (θ - θ^q)^(q-1) · A₂(θ)
(σZ)(θ) = (σQ)(θ) · (θ - θ^q)^w   · A₁(θ) · H_w(θ)
```

Eliminating `(σQ)(θ)` and using `w = k + (q-1)` gives the recorded relation below. -/
theorem eval_theta_relation {A₁ A₂ Q Y Z : Polynomial (Ambient F)} {w k : ℕ}
    (hQθ : Q.eval (ambTheta F) = 1) (hYθ : Y.eval (ambTheta F) = 0)
    (hZθ : Z.eval (ambTheta F) = 0) (hw : w = k + (Nat.card F - 1))
    (hrowY : Q * polyTwist (q := Nat.card F) 1 Y
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
        * (Y + Q * A₂))
    (hrowZ : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    (polyTwist (q := Nat.card F) 1 Z).eval (ambTheta F) * A₂.eval (ambTheta F)
      = (polyTwist (q := Nat.card F) 1 Y).eval (ambTheta F)
        * ((ambTheta F) - (ambTheta F) ^ Nat.card F) ^ k
        * (A₁.eval (ambTheta F) * (ambH F w).eval (ambTheta F)) := by
  have hYrow : (polyTwist (q := Nat.card F) 1 Y).eval (ambTheta F)
      = (polyTwist (q := Nat.card F) 1 Q).eval (ambTheta F)
        * ((ambTheta F) - (ambTheta F) ^ Nat.card F) ^ (Nat.card F - 1)
        * A₂.eval (ambTheta F) := by
    have h := congrArg (Polynomial.eval (ambTheta F)) hrowY
    simpa only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hQθ, hYθ, one_mul, zero_add,
      add_zero] using h
  have hZrow : (polyTwist (q := Nat.card F) 1 Z).eval (ambTheta F)
      = (polyTwist (q := Nat.card F) 1 Q).eval (ambTheta F)
        * ((ambTheta F) - (ambTheta F) ^ Nat.card F) ^ w
        * (A₁.eval (ambTheta F) * (ambH F w).eval (ambTheta F)) := by
    have h := congrArg (Polynomial.eval (ambTheta F)) hrowZ
    simpa only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hQθ, hYθ, hZθ, one_mul, zero_add,
      add_zero] using h
  rw [hZrow, hYrow, hw, pow_add]
  ring

/-! ## §9. `X = θ^q` is vacuous for *every* row: the durable negative -/

/-- ★ **If `P(θ) = 0` then `(σ P)(θ^q) = 0`.**  Immediate from `eval_polyTwist_one_pow`
(`(σP)(θ^q) = P(θ)^q`).  Since the ABP criterion gives `P_j(θ) = 0` for **every** entry of the row,
and every `tmAOpt`-entry carries a *positive* power of `W = X - C(θ^q)` (the `tmI`-indexed `j` are
*proper* prefixes, so `w - w(j) ≥ 1`), **both sides of every row vanish at `X = θ^q`**.  So the
evaluation at `θ^q` is `0 = 0` for every row, always, and can never carry information.
⚠ Do not look for `Q(θ^q) ≠ 0` (or anything else) at `X = θ^q`. -/
lemma eval_polyTwist_theta_pow_eq_zero {P : Polynomial (Ambient F)}
    (h : P.eval (ambTheta F) = 0) :
    (polyTwist (q := Nat.card F) 1 P).eval ((ambTheta F) ^ Nat.card F) = 0 := by
  rw [eval_polyTwist_one_pow F P (ambTheta F), h,
    zero_pow (by have := carlitz_card_ge_two F; omega : Nat.card F ≠ 0)]

/-! ## §10. Handle (i): `L` divides every `P_t`, and `L ∤ Q` -/

/-- ★ `P(θ) = 0` gives `L = X - C θ ∣ P`.  The ABP criterion gives this for **every** row entry
`P_t` (its `P(θ) = tmRho`, which vanishes off the `none`-component). -/
theorem dvd_X_sub_C_theta_of_eval_eq_zero {P : Polynomial (Ambient F)}
    (h : P.eval (ambTheta F) = 0) :
    (Polynomial.X - Polynomial.C (ambTheta F)) ∣ P := by
  rwa [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]

/-- ★ `P(θ) = 1` gives `L = X - C θ ∤ P`.  Applied to `Q = P none` (`Q(θ) = tmRho none = 1`):
**`Q` is the unique row entry not divisible by `L`** — while every other entry is. -/
theorem not_dvd_X_sub_C_theta_of_eval_eq_one {P : Polynomial (Ambient F)}
    (h : P.eval (ambTheta F) = 1) :
    ¬ (Polynomial.X - Polynomial.C (ambTheta F)) ∣ P := by
  intro hd
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, h] at hd
  exact one_ne_zero hd

/-! ## §11. The descent, stated exactly — and the verdict of the `m = q-1` check

Peeling `L = X - C θ` off `Y` spends exactly one power of `W = σ(L)` per step: with
`Y = L^(q-1)·R` the `(k)`-row becomes (cancel `W^(q-1) = σ(L^(q-1))`) the lemma below. -/
theorem tw_k_row_descent {A₂ Q R : Polynomial (Ambient F)}
    (hrow : Q * polyTwist (q := Nat.card F) 1
        ((Polynomial.X - Polynomial.C (ambTheta F)) ^ (Nat.card F - 1) * R)
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
        * ((Polynomial.X - Polynomial.C (ambTheta F)) ^ (Nat.card F - 1) * R + Q * A₂)) :
    Q * polyTwist (q := Nat.card F) 1 R
      = polyTwist (q := Nat.card F) 1 Q
        * ((Polynomial.X - Polynomial.C (ambTheta F)) ^ (Nat.card F - 1) * R + Q * A₂) := by
  have hL : polyTwist (q := Nat.card F) 1 ((Polynomial.X - Polynomial.C (ambTheta F))
      ^ (Nat.card F - 1) * R)
      = (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
        * polyTwist (q := Nat.card F) 1 R := by
    rw [polyTwist_mul, polyTwist_pow, polyTwist_X_sub_C_theta]
  have hW : (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) : Polynomial (Ambient F))
      ≠ 0 := Polynomial.X_sub_C_ne_zero _
  rw [hL] at hrow
  refine mul_left_cancel₀ (pow_ne_zero (Nat.card F - 1) hW) ?_
  calc (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
        * (Q * polyTwist (q := Nat.card F) 1 R)
      = Q * ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
          * polyTwist (q := Nat.card F) 1 R) := by ring
    _ = polyTwist (q := Nat.card F) 1 Q
          * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
          * ((Polynomial.X - Polynomial.C (ambTheta F)) ^ (Nat.card F - 1) * R + Q * A₂) := hrow
    _ = (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
          * (polyTwist (q := Nat.card F) 1 Q
              * ((Polynomial.X - Polynomial.C (ambTheta F)) ^ (Nat.card F - 1) * R + Q * A₂)) := by
          ring

/-! ## §12. The transfer lemma: the two σ-values at `θ` vanish together -/

/-- ★★ **The transfer.**  Every factor of `eval_theta_relation` but `(σY)(θ)` and `(σZ)(θ)` is
non-zero (`A₂(θ)`, `A₁(θ)` by transcendence; `H_w(θ) = θ^q - θ`; `θ - θ^q`), so
`(σZ)(θ)·A₂(θ) = (σY)(θ)·(θ-θ^q)^k·(A₁(θ)·H_w(θ))` is equivalent to `(σZ)(θ) = 0 ↔ (σY)(θ) = 0`.
With the row-evaluations at `θ` this gives the three-way equivalence
`(σQ)(θ) ≠ 0 ⟺ (σY)(θ) ≠ 0 ⟺ (σZ)(θ) ≠ 0` — a *transfer*, not a reduction.

⚠ Proof notes (both banked this session): normalise associativity with `rw [mul_assoc] at h`
**before** splitting a product — `mul_eq_zero.mp` on `((a*b)*c)` hands every later
`resolve_right` the wrong conjunct; and prefer `simp only […] at h` over explicit `rw` chains when
collapsing several `zero_mul`s, since the intermediate shapes are associativity-dependent. -/
theorem eval_theta_relation_zero_iff {A₁ A₂ Y Z : Polynomial (Ambient F)} {w k : ℕ}
    (h : (polyTwist (q := Nat.card F) 1 Z).eval (ambTheta F) * A₂.eval (ambTheta F)
      = (polyTwist (q := Nat.card F) 1 Y).eval (ambTheta F)
        * ((ambTheta F) - (ambTheta F) ^ Nat.card F) ^ k
        * (A₁.eval (ambTheta F) * (ambH F w).eval (ambTheta F)))
    (hA₂ : A₂.eval (ambTheta F) ≠ 0) (hA₁ : A₁.eval (ambTheta F) ≠ 0)
    (hH : (ambH F w).eval (ambTheta F) ≠ 0)
    (hd : (ambTheta F) - (ambTheta F) ^ Nat.card F ≠ 0) :
    (polyTwist (q := Nat.card F) 1 Z).eval (ambTheta F) = 0
      ↔ (polyTwist (q := Nat.card F) 1 Y).eval (ambTheta F) = 0 := by
  have hC : ((ambTheta F) - (ambTheta F) ^ Nat.card F) ^ k
      * (A₁.eval (ambTheta F) * (ambH F w).eval (ambTheta F)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero k hd) (mul_ne_zero hA₁ hH)
  constructor
  · intro hZ
    rw [hZ, zero_mul] at h
    rw [mul_assoc] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hC
  · intro hY
    simp only [hY, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hA₂

/-- Coefficientwise q-th roots give a sigma-preimage: if every coefficient of Q has a q-th root in
the ambient field then Q = polyTwist 1 Qt for some Qt. -/
theorem exists_polyTwist_eq_of_roots {Q : Polynomial (Ambient F)}
    (h : ∀ n, ∃ y : Ambient F, y ^ Nat.card F = Q.coeff n) :
    ∃ Qt : Polynomial (Ambient F), polyTwist (q := Nat.card F) 1 Qt = Q := by
  classical
  choose y hy using h
  set Q₀ : Polynomial (Ambient F) := Q.sum (fun n _ => Polynomial.C (y n) * Polynomial.X ^ n)
    with hQ₀
  refine ⟨Q₀, ?_⟩
  ext m
  rw [polyTwist_one_coeff]
  have hcoeff : Q₀.coeff m = if m ∈ Q.support then y m else 0 := by
    rw [hQ₀, Polynomial.coeff_sum, Polynomial.sum_def]
    have h1 : ∀ n ∈ Q.support, (Polynomial.C (y n) * Polynomial.X ^ n).coeff m
        = (if m = n then y n else 0) := by
      intro n _
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hmn : m = n
      · simp [hmn]
      · simp [hmn]
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq]
  rw [hcoeff]
  by_cases hm : m ∈ Q.support
  · rw [if_pos hm]
    exact hy m
  · rw [if_neg hm]
    have hq0 : Nat.card F ≠ 0 := by
      have h2 := carlitz_card_ge_two F
      omega
    rw [zero_pow hq0]
    have hz : Q.coeff m = 0 := by
      by_contra hc
      exact hm (Polynomial.mem_support_iff.mpr hc)
    exact hz.symm

/-- The ladder relation: the q-th power of the (q^(v+1))-th root of theta is the (q^v)-th root.
Immediate from `ambThetaNu_pow_add` at `M = 1` (no induction needed). -/
theorem ambThetaNu_succ_pow (ν : ℕ) :
    (ambThetaNu F (ν + 1)) ^ Nat.card F = ambThetaNu F ν := by
  simpa using ambThetaNu_pow_add F ν 1

/-- Ladder relation at the level of evaluation: (p(theta_(v+1)))^q = p(theta_v). This is
`DegTheta.eval₂_theta_pow_card` with the base of the power swapped (the theta^q side becomes
`ambThetaNu_succ_pow`). -/
theorem eval_ambThetaNu_succ_pow (ν : ℕ) (p : Polynomial F) :
    (p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F (ν + 1))) ^ Nat.card F
      = p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) := by
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range, FrobPow.sum_pow_finset]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hq : (ambCoeff F (p.coeff i)) ^ Nat.card F = ambCoeff F (p.coeff i) :=
    (mem_ambF_iff F _).mp (ambCoeff_mem_ambF F _)
  simp only [algebraMap_ambient_eq]
  rw [mul_pow, ← pow_mul, Nat.mul_comm i (Nat.card F), pow_mul, ambThetaNu_succ_pow, hq]

end ZagierHoffmanPositiveChar
