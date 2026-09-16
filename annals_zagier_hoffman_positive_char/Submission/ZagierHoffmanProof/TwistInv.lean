import Submission.ZagierHoffmanProof.RowDen
import Submission.Commons.Algebra.Polynomial.map_prod_range_iterate_eq_self
import Submission.Commons.Algebra.GCD.associated_of_forall_dvd_of_dvd
import Submission.Commons.Algebra.Polynomial.dvd_pow_natDegree_of_forall_monic_irreducible_dvd

/-!
# The inverse Frobenius `σ⁻¹` on `K^{perf}[X]`

`PLAN.md` §«SESSION 358» §10.6 / the ORBIT programme.  Everything in the two-term endgame needs the
operator going *against* `polyTwist 1 p = p.map (·^q)`; the build has its atoms
(`AmbRootLevel.ambRootAt` realises the `q`-th roots of elements of `A_ν`, and
`RowDen.exists_root_of_mem_ambKperf` assembles them into roots of elements of `K^{perf}`), but no
packaged function.  This module provides it, with a **total** definition using the junk-value
convention that `DegNu` uses for `degNu` (`0` off `K^{perf}`):

* `qRoot x` — a `q`-th root of `x` when `x ∈ K^{perf}` (and `0` otherwise);
* `qRoot_pow`, `qRoot_mem`, `qRoot_eq_of_pow_eq`, `qRoot_mul`, `qRoot_add`, `qRoot_ne_zero`;
* `polyTwistInv p` — the coefficientwise root of `p`;
* `polyTwist_polyTwistInv : σ (σ⁻¹ p) = p` for `p` with `K^{perf}`-coefficients, plus
  `polyTwistInv_coeff_mem`, and the ring laws `polyTwistInv_add` / `polyTwistInv_mul` (proved through
  `polyTwist_one_injective`, hence with no support bookkeeping at all).

With this, the ORBIT statement of §10.6 becomes literal: `Q ∣ σ⁻ʲ(Q) · Z`, i.e.
`Q ∣ (polyTwistInv^[j] Q) * Z`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
open Polynomial
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

/-! ## §1. The `q`-th root in `K^{perf}` -/

/-- The `q`-th power map is injective on the ambient field, so `q`-th roots are unique. -/
lemma qPow_injective : Function.Injective (fun x : Ambient F => x ^ Nat.card F) := by
  have h := ambPow_injective F 1
  simpa using h

/-- A `q`-th root of `x`, for `x ∈ K^{perf}` (and `0` off `K^{perf}`). -/
noncomputable def qRoot (x : Ambient F) : Ambient F :=
  if hx : x ∈ ambKperf F then Classical.choose (exists_root_of_mem_ambKperf (F := F) hx) else 0

lemma qRoot_pow {x : Ambient F} (hx : x ∈ ambKperf F) : qRoot x ^ Nat.card F = x := by
  rw [qRoot, dif_pos hx]
  exact (Classical.choose_spec (exists_root_of_mem_ambKperf (F := F) hx)).2

lemma qRoot_mem {x : Ambient F} (hx : x ∈ ambKperf F) : qRoot x ∈ ambKperf F := by
  rw [qRoot, dif_pos hx]
  exact (Classical.choose_spec (exists_root_of_mem_ambKperf (F := F) hx)).1

/-- The defining property of `qRoot`: it is the unique `q`-th root. -/
lemma qRoot_eq_of_pow_eq {x y : Ambient F} (hx : x ∈ ambKperf F)
    (h : y ^ Nat.card F = x) : qRoot x = y :=
  qPow_injective (by show qRoot x ^ Nat.card F = y ^ Nat.card F; rw [qRoot_pow hx, h])

@[simp] lemma qRoot_zero : qRoot (F := F) 0 = 0 :=
  qRoot_eq_of_pow_eq (ambKperf F).zero_mem
    (by rw [zero_pow (FrobPow.ne_zero (Ambient F) (q := Nat.card F))])

@[simp] lemma qRoot_one : qRoot (F := F) 1 = 1 :=
  qRoot_eq_of_pow_eq (ambKperf F).one_mem (by rw [one_pow])

lemma qRoot_mul {x y : Ambient F} (hx : x ∈ ambKperf F) (hy : y ∈ ambKperf F) :
    qRoot (x * y) = qRoot x * qRoot y :=
  qRoot_eq_of_pow_eq ((ambKperf F).mul_mem hx hy) (by rw [mul_pow, qRoot_pow hx, qRoot_pow hy])

lemma qRoot_add {x y : Ambient F} (hx : x ∈ ambKperf F) (hy : y ∈ ambKperf F) :
    qRoot (x + y) = qRoot x + qRoot y :=
  qRoot_eq_of_pow_eq ((ambKperf F).add_mem hx hy)
    (by rw [FrobPow.add_pow, qRoot_pow hx, qRoot_pow hy])

lemma qRoot_ne_zero {x : Ambient F} (hx : x ∈ ambKperf F) (hx0 : x ≠ 0) : qRoot x ≠ 0 := by
  intro h
  have h1 := qRoot_pow hx
  rw [h, zero_pow (FrobPow.ne_zero (Ambient F) (q := Nat.card F))] at h1
  exact hx0 h1.symm

/-! ## §2. `σ⁻¹` on polynomials with `K^{perf}`-coefficients -/

/-- The coefficientwise `q`-th root of a polynomial. -/
noncomputable def polyTwistInv (p : Polynomial (Ambient F)) : Polynomial (Ambient F) :=
  p.sum fun n _ => Polynomial.C (qRoot (p.coeff n)) * Polynomial.X ^ n

lemma polyTwistInv_coeff (p : Polynomial (Ambient F)) (m : ℕ) :
    (polyTwistInv p).coeff m = if m ∈ p.support then qRoot (p.coeff m) else 0 := by
  rw [polyTwistInv, Polynomial.coeff_sum, Polynomial.sum_def]
  have h1 : ∀ n ∈ p.support, (Polynomial.C (qRoot (p.coeff n)) * Polynomial.X ^ n).coeff m
      = (if m = n then qRoot (p.coeff n) else 0) := by
    intro n _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hmn : m = n
    · simp [hmn]
    · simp [hmn]
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq]

@[simp] lemma polyTwistInv_zero : polyTwistInv (F := F) 0 = 0 := by
  ext m
  rw [polyTwistInv_coeff, Polynomial.coeff_zero]
  simp

/-- ★★★ **`σ` is a left inverse of `polyTwistInv`** on polynomials with `K^{perf}`-coefficients. -/
theorem polyTwist_polyTwistInv {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambKperf F) :
    polyTwist (q := Nat.card F) 1 (polyTwistInv p) = p := by
  ext m
  rw [polyTwist_one_coeff, polyTwistInv_coeff]
  by_cases hm : m ∈ p.support
  · rw [if_pos hm]; exact qRoot_pow (hp m)
  · rw [if_neg hm]
    have h0 : p.coeff m = 0 := by
      by_contra hc
      exact hm (Polynomial.mem_support_iff.mpr hc)
    rw [h0]
    exact zero_pow (FrobPow.ne_zero (Ambient F) (q := Nat.card F))

/-- `polyTwistInv` keeps `K^{perf}`-coefficients. -/
lemma polyTwistInv_coeff_mem {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambKperf F) : ∀ n, (polyTwistInv p).coeff n ∈ ambKperf F := by
  intro n
  rw [polyTwistInv_coeff]
  by_cases h : n ∈ p.support
  · rw [if_pos h]; exact qRoot_mem (hp n)
  · rw [if_neg h]; exact (ambKperf F).zero_mem

/-- `polyTwistInv` is additive, on polynomials with `K^{perf}`-coefficients. -/
lemma polyTwistInv_add (p q : Polynomial (Ambient F))
    (hp : ∀ n, p.coeff n ∈ ambKperf F) (hq : ∀ n, q.coeff n ∈ ambKperf F) :
    polyTwistInv (p + q) = polyTwistInv p + polyTwistInv q := by
  refine polyTwist_one_injective F ?_
  rw [polyTwist_add, polyTwist_polyTwistInv fun n => (ambKperf F).add_mem (hp n) (hq n),
    polyTwist_polyTwistInv hp, polyTwist_polyTwistInv hq]

/-- Coefficients of a product of `K^{perf}[X]`-polynomials are in `K^{perf}`. -/
lemma coeff_mul_mem_ambKperf {p q : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambKperf F) (hq : ∀ n, q.coeff n ∈ ambKperf F) :
    ∀ n, (p * q).coeff n ∈ ambKperf F := by
  intro n
  rw [Polynomial.coeff_mul]
  exact Subring.sum_mem (ambKperf F).toSubring fun x _ =>
    (ambKperf F).toSubring.mul_mem (hp x.1) (hq x.2)

/-- The coefficients of `p.map (ambCoeff F)` lie in `K^{perf}`. -/
lemma coeff_map_ambCoeff_mem_ambKperf (p : Polynomial F) :
    ∀ n, (p.map (ambCoeff F)).coeff n ∈ ambKperf F := by
  intro n
  rw [Polynomial.coeff_map]
  exact ambCoeff_mem_ambKperf F _

/-- `polyTwistInv` is multiplicative, on polynomials with `K^{perf}`-coefficients. -/
lemma polyTwistInv_mul (p q : Polynomial (Ambient F))
    (hp : ∀ n, p.coeff n ∈ ambKperf F) (hq : ∀ n, q.coeff n ∈ ambKperf F) :
    polyTwistInv (p * q) = polyTwistInv p * polyTwistInv q := by
  refine polyTwist_one_injective F ?_
  rw [polyTwist_mul, polyTwist_polyTwistInv (coeff_mul_mem_ambKperf hp hq),
    polyTwist_polyTwistInv hp, polyTwist_polyTwistInv hq]

/-- `polyTwistInv` is `K^{perf}`-linear: it fixes polynomials with `F_q`-coefficients. -/
lemma polyTwistInv_map_ambCoeff (p : Polynomial F) :
    polyTwistInv (p.map (ambCoeff F)) = p.map (ambCoeff F) := by
  refine polyTwist_one_injective F ?_
  rw [polyTwist_polyTwistInv (coeff_map_ambCoeff_mem_ambKperf p)]
  exact ((polyTwist_one_eq_self_iff F (p.map (ambCoeff F))).mpr fun n => by
    rw [Polynomial.coeff_map]
    exact ambCoeff_mem_ambF F _).symm

/-! ## §3. `σ⁻¹` of a row: the level-shift (the ORBIT mechanism, step 1)

`PLAN.md` §«SESSION 358» §10.6 asked for the shape-preservation statement: *the `σ⁻¹`-image of the
row system is again a row system of the same shape*.  In explicit form (the `polyTwistInv`-image of
the `(R)`-row), it reads

  `σ⁻¹Q · Z = Q · L^w · σ⁻¹G`     (`L = X − C θ`, `G = Z + Y + Q·A₁·H_w`),

and its *content* is the divisibility `Q ∣ σ⁻¹(Q)·Z` (`RowDen.dvd_twistInv_mul_of_R_row`).  Iterating
`polyTwistInv` on the *same* row gives the level-`j` identity
`Q⁽ʲ⁾·Z⁽ʲ⁻¹⁾ = Q⁽ʲ⁻¹⁾·(L⁽ʲ⁾)^w·G⁽ʲ⁾` — note it is now a *literal* statement, which is what the
ORBIT induction needs. -/

/-- Coefficients of `polyTwist 1 p` are in `K^{perf}` when those of `p` are. -/
lemma polyTwist_coeff_mem_ambKperf {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambKperf F) : ∀ n, (polyTwist (q := Nat.card F) 1 p).coeff n ∈ ambKperf F := by
  intro n
  rw [polyTwist_one_coeff]
  exact (ambKperf F).pow_mem (hp n) _

/-- ★★ **The inverse law**: `σ⁻¹ (σ p) = p`. -/
theorem polyTwistInv_polyTwist {p : Polynomial (Ambient F)}
    (hp : ∀ n, (polyTwist (q := Nat.card F) 1 p).coeff n ∈ ambKperf F) :
    polyTwistInv (polyTwist (q := Nat.card F) 1 p) = p := by
  refine polyTwist_one_injective F ?_
  rw [polyTwist_polyTwistInv hp]

/-- Coefficients of `W^w = (X − C(θ^q))^w` lie in `K^{perf}` — they lie in `A_0`. -/
lemma coeff_pow_X_sub_C_theta_pow_mem_ambKperf (w n : ℕ) :
    ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
      Polynomial (Ambient F)).coeff n ∈ ambKperf F :=
  ambA_subset_ambKperf F 0 (coeff_X_sub_C_theta_pow_pow_mem_ambA (F := F) 0 w n)

/-- `σ⁻¹(W^w) = L^w`, `W = X − C(θ^q)`, `L = X − C θ`. -/
lemma polyTwistInv_pow_X_sub_C_theta_pow (w : ℕ) :
    polyTwistInv ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w)
      = (Polynomial.X - Polynomial.C (ambTheta F)) ^ w := by
  refine polyTwist_one_injective F ?_
  rw [polyTwist_polyTwistInv (coeff_pow_X_sub_C_theta_pow_mem_ambKperf w), polyTwist_pow,
    polyTwist_X_sub_C_theta]

/-- ★★★ **The level-shift of the `(R)`-row** (`j = 1`): applying `σ⁻¹` to the row gives
`σ⁻¹Q · Z = Q · L^w · σ⁻¹G`.  This is the shape-preservation statement of §10.6 in explicit form. -/
theorem polyTwistInv_row_R {w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F) (hZ : ∀ n, Z.coeff n ∈ ambKperf F)
    (hG : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambKperf F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    polyTwistInv Q * Z
      = Q * (Polynomial.X - Polynomial.C (ambTheta F)) ^ w
        * polyTwistInv (Z + Y + Q * A₁ * ambH F w) := by
  have h1 : polyTwistInv (Q * polyTwist (q := Nat.card F) 1 Z)
      = polyTwistInv (polyTwist (q := Nat.card F) 1 Q
          * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
          * (Z + Y + Q * A₁ * ambH F w)) := congrArg polyTwistInv hrow
  have hL : polyTwistInv (Q * polyTwist (q := Nat.card F) 1 Z) = polyTwistInv Q * Z := by
    rw [polyTwistInv_mul Q (polyTwist (q := Nat.card F) 1 Z) hQ
        (polyTwist_coeff_mem_ambKperf hZ),
      polyTwistInv_polyTwist (polyTwist_coeff_mem_ambKperf hZ)]
  have hR : polyTwistInv (polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w))
      = Q * (Polynomial.X - Polynomial.C (ambTheta F)) ^ w
        * polyTwistInv (Z + Y + Q * A₁ * ambH F w) := by
    rw [polyTwistInv_mul (polyTwist (q := Nat.card F) 1 Q
          * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w)
        (Z + Y + Q * A₁ * ambH F w)
        (coeff_mul_mem_ambKperf (polyTwist_coeff_mem_ambKperf hQ)
          (coeff_pow_X_sub_C_theta_pow_mem_ambKperf w)) hG,
      polyTwistInv_mul (polyTwist (q := Nat.card F) 1 Q)
        ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w)
        (polyTwist_coeff_mem_ambKperf hQ) (coeff_pow_X_sub_C_theta_pow_mem_ambKperf w),
      polyTwistInv_polyTwist (polyTwist_coeff_mem_ambKperf hQ),
      polyTwistInv_pow_X_sub_C_theta_pow w]
  rw [hL, hR] at h1
  exact h1

/-- ★★★ **The ORBIT divisibility at level `1`**, restated in `polyTwistInv` form: `Q ∣ σ⁻¹(Q)·Z`. -/
theorem dvd_twistInv_mul_of_R_row' {w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F) (hZ : ∀ n, Z.coeff n ∈ ambKperf F)
    (hG : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambKperf F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    Q ∣ polyTwistInv Q * Z := by
  refine ⟨(Polynomial.X - Polynomial.C (ambTheta F)) ^ w
      * polyTwistInv (Z + Y + Q * A₁ * ambH F w), ?_⟩
  rw [polyTwistInv_row_R hQ hZ hG hrow]
  ring

/-! ## §4. The level-`j` iteration (ORBIT, in its correct form)

`PLAN.md` §11.3: iterating `σ⁻¹` on the row gives, at level `j ≥ 1`,

  **(CHAIN-j)**  `Q⁽ʲ⁾ · Z⁽ʲ⁻¹⁾ = Q⁽ʲ⁻¹⁾ · (L⁽ʲ⁻¹⁾)^w · G⁽ʲ⁾`,   `X⁽ʲ⁾ := (σ⁻¹)^j X`,

whence `Q⁽ʲ⁻¹⁾ ∣ Q⁽ʲ⁾ · Z⁽ʲ⁻¹⁾` — one `Q`-step at the cost of one *twisted* `Z`.  This is the
correction of §11.3: the pure orbit `Q ∣ σ⁻ʲ(Q)·Z` is **not** available.  Everything below is
mechanical bookkeeping for the two operators, each lemma carrying the `K^{perf}`-coefficient
hypotheses that make the *next* level legal. -/

/-- Coefficients of a `K^{perf}[X]`-polynomial's `k`-th power stay in `K^{perf}`. -/
lemma coeff_pow_mem_ambKperf {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambKperf F) (k : ℕ) : ∀ n, (p ^ k).coeff n ∈ ambKperf F := by
  induction k with
  | zero =>
      intro n
      rw [pow_zero, Polynomial.coeff_one]
      split_ifs with h
      · exact (ambKperf F).one_mem
      · exact (ambKperf F).zero_mem
  | succ m ih => intro n; rw [pow_succ]; exact coeff_mul_mem_ambKperf ih hp n

/-- `σ⁻¹ (p^k) = (σ⁻¹ p)^k`. -/
theorem polyTwistInv_pow {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambKperf F) (k : ℕ) :
    polyTwistInv (p ^ k) = (polyTwistInv p) ^ k := by
  refine polyTwist_one_injective F ?_
  rw [polyTwist_polyTwistInv (coeff_pow_mem_ambKperf hp k), polyTwist_pow,
    polyTwist_polyTwistInv hp]

/-- `σ` (as an iterate) is multiplicative. -/
lemma polyTwist_iterate_mul (j : ℕ) (p q : Polynomial (Ambient F)) :
    ((polyTwist (q := Nat.card F) 1)^[j]) (p * q)
      = ((polyTwist (q := Nat.card F) 1)^[j]) p * ((polyTwist (q := Nat.card F) 1)^[j]) q := by
  revert p q
  induction j with
  | zero => intro p q; simp
  | succ m ih =>
      intro p q
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        polyTwist_mul]
      exact ih _ _

/-- `σ` (as an iterate) respects powers. -/
lemma polyTwist_iterate_pow (j : ℕ) (p : Polynomial (Ambient F)) (k : ℕ) :
    ((polyTwist (q := Nat.card F) 1)^[j]) (p ^ k)
      = (((polyTwist (q := Nat.card F) 1)^[j]) p) ^ k := by
  revert p
  induction j with
  | zero => intro p; simp
  | succ m ih =>
      intro p
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, polyTwist_pow]
      exact ih _

/-- `σ⁻¹` (as an iterate) is multiplicative, on `K^{perf}[X]`. -/
lemma polyTwistInv_iterate_mul : ∀ (j : ℕ) {p q : Polynomial (Ambient F)},
    (∀ n, p.coeff n ∈ ambKperf F) → (∀ n, q.coeff n ∈ ambKperf F) →
    (polyTwistInv^[j]) (p * q) = (polyTwistInv^[j]) p * (polyTwistInv^[j]) q := by
  intro j
  induction j with
  | zero => intro p q hp hq; simp
  | succ m ih =>
      intro p q hp hq
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        polyTwistInv_mul p q hp hq]
      exact ih (polyTwistInv_coeff_mem hp) (polyTwistInv_coeff_mem hq)

/-- `σ⁻¹` (as an iterate) respects powers, on `K^{perf}[X]`. -/
lemma polyTwistInv_iterate_pow : ∀ (j : ℕ) {p : Polynomial (Ambient F)},
    (∀ n, p.coeff n ∈ ambKperf F) → ∀ k : ℕ,
    (polyTwistInv^[j]) (p ^ k) = ((polyTwistInv^[j]) p) ^ k := by
  intro j
  induction j with
  | zero => intro p hp k; simp
  | succ m ih =>
      intro p hp k
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, polyTwistInv_pow hp k]
      exact ih (polyTwistInv_coeff_mem hp) k

/-- ★★★ **`σ^j ∘ (σ⁻¹)^j = id`** on `K^{perf}[X]`. -/
theorem polyTwist_iterate_polyTwistInv : ∀ (j : ℕ) {p : Polynomial (Ambient F)},
    (∀ n, p.coeff n ∈ ambKperf F) →
    ((polyTwist (q := Nat.card F) 1)^[j]) ((polyTwistInv^[j]) p) = p := by
  intro j
  induction j with
  | zero => intro p hp; simp
  | succ m ih =>
      intro p hp
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply,
        ih (polyTwistInv_coeff_mem hp)]
      exact polyTwist_polyTwistInv hp

/-- ★★★ **`(σ⁻¹)^(j+1) ∘ σ = (σ⁻¹)^j`**. -/
theorem polyTwistInv_iterate_polyTwist (j : ℕ) {p : Polynomial (Ambient F)}
    (hp : ∀ n, (polyTwist (q := Nat.card F) 1 p).coeff n ∈ ambKperf F) :
    (polyTwistInv^[j + 1]) (polyTwist (q := Nat.card F) 1 p) = (polyTwistInv^[j]) p := by
  rw [Function.iterate_succ_apply, polyTwistInv_polyTwist hp]

/-- The `σ^(j+1)`-image of the **left** side of (CHAIN-j) is the left side of the row. -/
theorem polyTwist_iterate_row_LHS (j : ℕ) {Z Q : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F) (hZ : ∀ n, Z.coeff n ∈ ambKperf F) :
    ((polyTwist (q := Nat.card F) 1)^[j + 1])
        ((polyTwistInv^[j + 1]) Q * (polyTwistInv^[j]) Z)
      = Q * polyTwist (q := Nat.card F) 1 Z := by
  have hσZ : ∀ n, (polyTwist (q := Nat.card F) 1 Z).coeff n ∈ ambKperf F :=
    polyTwist_coeff_mem_ambKperf hZ
  rw [polyTwist_iterate_mul, polyTwist_iterate_polyTwistInv (j + 1) hQ]
  congr 1
  rw [← polyTwistInv_iterate_polyTwist j hσZ, polyTwist_iterate_polyTwistInv (j + 1) hσZ]

/-- The `σ^(j+1)`-image of the **right** side of (CHAIN-j) is the right side of the row. -/
theorem polyTwist_iterate_row_RHS (j : ℕ) {w : ℕ} {G Q : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F) (hG : ∀ n, G.coeff n ∈ ambKperf F) :
    ((polyTwist (q := Nat.card F) 1)^[j + 1])
        ((polyTwistInv^[j]) Q
          * ((polyTwistInv^[j]) (Polynomial.X - Polynomial.C (ambTheta F))) ^ w
          * (polyTwistInv^[j + 1]) G)
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * G := by
  have hL : ∀ n, (Polynomial.X - Polynomial.C (ambTheta F) : Polynomial (Ambient F)).coeff n
      ∈ ambKperf F := fun n =>
    ambA_subset_ambKperf F 0 (coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero n)
  have hσQ : ∀ n, (polyTwist (q := Nat.card F) 1 Q).coeff n ∈ ambKperf F :=
    polyTwist_coeff_mem_ambKperf hQ
  have hσL : ∀ n, (polyTwist (q := Nat.card F) 1
      (Polynomial.X - Polynomial.C (ambTheta F))).coeff n ∈ ambKperf F :=
    polyTwist_coeff_mem_ambKperf hL
  rw [polyTwist_iterate_mul, polyTwist_iterate_mul, polyTwist_iterate_pow,
    ← polyTwistInv_iterate_polyTwist j hσQ, polyTwist_iterate_polyTwistInv (j + 1) hσQ,
    ← polyTwistInv_iterate_polyTwist j hσL, polyTwist_iterate_polyTwistInv (j + 1) hσL,
    polyTwist_iterate_polyTwistInv (j + 1) hG]
  rw [polyTwist_X_sub_C_theta]

/-- ★★★★ **THE LEVEL-`j` LEVEL-SHIFT** (`PLAN.md` §11.3, (CHAIN-j)): applying `(σ⁻¹)^(j+1)` to the
`(R)`-row gives `Q⁽ʲ⁺¹⁾ · Z⁽ʲ⁾ = Q⁽ʲ⁾ · (L⁽ʲ⁾)^w · G⁽ʲ⁺¹⁾`. -/
theorem polyTwistInv_iterate_row_R (j : ℕ) {w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F) (hZ : ∀ n, Z.coeff n ∈ ambKperf F)
    (hG : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambKperf F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    (polyTwistInv^[j + 1]) Q * (polyTwistInv^[j]) Z
      = (polyTwistInv^[j]) Q
        * (((polyTwistInv^[j]) (Polynomial.X - Polynomial.C (ambTheta F))) ^ w)
        * (polyTwistInv^[j + 1]) (Z + Y + Q * A₁ * ambH F w) := by
  refine (polyTwist_one_injective F).iterate (j + 1) ?_
  rw [polyTwist_iterate_row_LHS j hQ hZ, polyTwist_iterate_row_RHS j hQ hG, hrow]

/-- ★★★★ **THE ORBIT CHAIN (correct form)** (`PLAN.md` §11.3): `Q⁽ʲ⁾ ∣ Q⁽ʲ⁺¹⁾ · Z⁽ʲ⁾`. -/
theorem dvd_polyTwistInv_iterate_row_R (j : ℕ) {w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F) (hZ : ∀ n, Z.coeff n ∈ ambKperf F)
    (hG : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambKperf F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    (polyTwistInv^[j]) Q ∣ (polyTwistInv^[j + 1]) Q * (polyTwistInv^[j]) Z := by
  refine ⟨((polyTwistInv^[j]) (Polynomial.X - Polynomial.C (ambTheta F))) ^ w
      * (polyTwistInv^[j + 1]) (Z + Y + Q * A₁ * ambH F w), ?_⟩
  rw [polyTwistInv_iterate_row_R j hQ hZ hG hrow]
  ring

/-- ★★★★ **The `Z`-side extraction at level `j`** (`PLAN.md` §11.3): from (CHAIN-j) there is `D`
with `D ∣ Q⁽ʲ⁾`, `Q⁽ʲ⁾ ∣ D·Z⁽ʲ⁾` (so `D` is `Q⁽ʲ⁾/gcd(Q⁽ʲ⁾, Z⁽ʲ⁾)`), and **`D ∣ Q⁽ʲ⁺¹⁾`** — the
factor of `Q⁽ʲ⁾` not caught by `Z⁽ʲ⁾` is caught by the *next* `Q`-level.  The `j = 0` case is
`RowDen.exists_den_dvd_of_R_row`; this is the form that the gluing argument consumes, at every level. -/
theorem exists_den_iterate_of_R_row (j : ℕ) {w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F) (hZ : ∀ n, Z.coeff n ∈ ambKperf F)
    (hG : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambKperf F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    ∃ D : Polynomial (Ambient F),
      D ∣ (polyTwistInv^[j]) Q ∧ (polyTwistInv^[j]) Q ∣ D * (polyTwistInv^[j]) Z
        ∧ D ∣ (polyTwistInv^[j + 1]) Q := by
  have h := dvd_polyTwistInv_iterate_row_R (F := F) j hQ hZ hG hrow
  obtain ⟨D, hD1, hD2, hD3⟩ := exists_den_dvd_of_dvd_mul (a := (polyTwistInv^[j]) Q)
    (b := (polyTwistInv^[j]) Z) (c := (polyTwistInv^[j + 1]) Q) (by rwa [mul_comm] at h)
  exact ⟨D, hD1, hD2, hD3⟩

/-! ## §5. The collapse: a periodic irreducible has an `F_q[X]`-denominator

`PLAN.md` §11.3 step "(collapse)": if a monic irreducible `r` is fixed by `σ^M`, then the product of
its `σ`-orbit is `σ`-fixed — hence has `F_q`-coefficients (`polyTwist_one_eq_self_iff`) — and is
divisible by `r`.  ⚠ **No rescaling by a constant is needed**: `r` is *monic*, so `σ^M(r) = c·r` with
`c` a unit forces `c = 1` (compare leading coefficients), and the associate-collapse of the orbit then
gives `σ^M(r) = r` directly.

The fixedness of the orbit-product is `Commons.Algebra.Polynomial.map_prod_range_iterate_eq_self`
(generic: for any ring endomorphism); the bridge between the function `polyTwist 1` and the ring hom
`polyTwistHom 1` is `polyTwist_iterate_eq_polyTwistHom_iterate` below. -/

/-- The function `polyTwist 1` and the ring hom `polyTwistHom 1` have the same iterates. -/
lemma polyTwist_iterate_eq_polyTwistHom_iterate (M : ℕ) :
    ((polyTwist (q := Nat.card F) 1)^[M]) = ((polyTwistHom (K := Ambient F) (q := Nat.card F) 1)^[M]) := by
  funext p
  induction M with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl

/-- ★★★ **The collapse**: a monic polynomial fixed by an iterate of `σ` has a nonzero `F_q[X]`-multiple.
The product of its `σ`-orbit is `σ`-fixed, hence in `F_q[X]`, and `r` divides it. -/
theorem exists_ambF_dvd_of_monic_iterate_eq_self {r : Polynomial (Ambient F)} (hr : r.Monic) {M : ℕ}
    (hM : 1 ≤ M) (hper : ((polyTwist (q := Nat.card F) 1)^[M]) r = r) :
    ∃ b : Polynomial (Ambient F), b ≠ 0 ∧ (∀ n, b.coeff n ∈ ambF F) ∧ r ∣ b := by
  have hper' : ((polyTwistHom (K := Ambient F) (q := Nat.card F) 1)^[M]) r = r := by
    rw [← polyTwist_iterate_eq_polyTwistHom_iterate M]; exact hper
  have hzero : ∀ i : ℕ, ((polyTwistHom (K := Ambient F) (q := Nat.card F) 1)^[i])
      (0 : Polynomial (Ambient F)) = 0 := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]; exact map_zero _
  refine ⟨∏ i ∈ Finset.range M, ((polyTwistHom (K := Ambient F) (q := Nat.card F) 1)^[i]) r, ?_, ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.mpr fun i _ h0 => hr.ne_zero ?_
    have hinj : Function.Injective ((polyTwistHom (K := Ambient F) (q := Nat.card F) 1)^[i]) :=
      ((polyTwist_one_injective F).iterate i)
    exact hinj (by rw [h0, hzero i])
  · have hfix := Commons.Algebra.Polynomial.map_prod_range_iterate_eq_self
      (polyTwistHom (K := Ambient F) (q := Nat.card F) 1) r M hper'
    intro n
    exact (polyTwist_one_eq_self_iff F _).mp hfix n
  · have h0 : (((polyTwistHom (K := Ambient F) (q := Nat.card F) 1) :
        Polynomial (Ambient F) → Polynomial (Ambient F))^[0]) r = r := rfl
    rw [← h0]
    exact Finset.dvd_prod_of_mem (fun i =>
      (((polyTwistHom (K := Ambient F) (q := Nat.card F) 1) :
        Polynomial (Ambient F) → Polynomial (Ambient F))^[i]) r) (Finset.mem_range.mpr hM)

/-! ## §6. The statement (γ) and its base cases

`PLAN.md` §13.2: with the *backward* pigeonhole, the crux reduces to finding a denominator supported
on the stabilised gcd of the backward `σ`-orbit of `Q`:

  **(γ)**  `∃E, E ∣ G_K ∧ Q ∣ E·Z`,   `G_K := gcd(Q, σ⁻¹Q, …, σ⁻ᴷQ)`.

Below: the `G_K` recursion with its API, the statement of (γ) as `GammaRow Q Z K`, the **`K = 0` base
case** (there `G_0 = Q`, and the witness is the `j = 0` instance of the level-wise extraction), and the
**level-`j` family** `E_j := σ^j(D_j)`, which satisfies (γ) at `K = 0` and `K = 1` for **every** `j`
with a single (untwisted) `Z` — the family that the matching step must upgrade to the stabilised gcd. -/

/-- `G_K = gcd(Q, σ⁻¹Q, …, σ⁻ᴷQ)`, defined by the recursion `G_0 = Q`,
`G_{k+1} = gcd(G_k, (σ⁻¹)^{k+1} Q)`. -/
noncomputable def orbitGcd (Q : Polynomial (Ambient F)) : ℕ → Polynomial (Ambient F)
  | 0 => Q
  | k + 1 => gcd (orbitGcd Q k) ((polyTwistInv^[k + 1]) Q)

@[simp] lemma orbitGcd_zero (Q : Polynomial (Ambient F)) : orbitGcd Q 0 = Q := rfl

lemma orbitGcd_succ (Q : Polynomial (Ambient F)) (k : ℕ) :
    orbitGcd Q (k + 1) = gcd (orbitGcd Q k) ((polyTwistInv^[k + 1]) Q) := rfl

/-- `G_K` is decreasing in divisibility. -/
lemma orbitGcd_succ_dvd (Q : Polynomial (Ambient F)) (k : ℕ) :
    orbitGcd Q (k + 1) ∣ orbitGcd Q k := by
  rw [orbitGcd_succ]; exact gcd_dvd_left _ _

/-- Every orbit element with index `≤ K` is divisible by `G_K`. -/
lemma orbitGcd_dvd_orbit (Q : Polynomial (Ambient F)) {m k : ℕ} (h : m ≤ k) :
    orbitGcd Q k ∣ (polyTwistInv^[m]) Q := by
  induction k with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero h
      subst hm; simp
  | succ n ih =>
      rcases Nat.lt_or_eq_of_le h with hlt | heq
      · exact dvd_trans (orbitGcd_succ_dvd Q n) (ih (Nat.lt_succ_iff.mp hlt))
      · subst heq
        rw [orbitGcd_succ]; exact gcd_dvd_right _ _

/-- **(γ)** at level `K`: a denominator for `Q ∣ E·Z` supported on `G_K`. -/
def GammaRow (Q Z : Polynomial (Ambient F)) (K : ℕ) : Prop :=
  ∃ E : Polynomial (Ambient F), E ∣ orbitGcd Q K ∧ Q ∣ E * Z

/-- ★★★★ **(γ) at `K = 0`** (`G_0 = Q`) — the base case, straight out of the level-wise extraction at
`j = 0`: its witness `D_0 = Q/gcd(Q,Z)` satisfies `D_0 ∣ Q` and `Q ∣ D_0·Z`. -/
theorem gammaRow_zero {w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F) (hZ : ∀ n, Z.coeff n ∈ ambKperf F)
    (hG : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambKperf F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    GammaRow Q Z 0 := by
  obtain ⟨D, hD1, hD2, -⟩ := exists_den_iterate_of_R_row (F := F) 0 hQ hZ hG hrow
  exact ⟨D, by simpa using hD1, by simpa using hD2⟩

/-- ★★★★ **The level-`j` family**: `E_j := σ^j(D_j)` satisfies `E_j ∣ Q`, `E_j ∣ σ⁻¹Q` and
`Q ∣ E_j·Z` — so (γ) holds at `K = 0` **and** `K = 1` for every `j`, with an untwisted `Z`. -/
theorem gammaRow_one_of_level {j w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F) (hZ : ∀ n, Z.coeff n ∈ ambKperf F)
    (hG : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambKperf F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    ∃ E : Polynomial (Ambient F),
      E ∣ Q ∧ E ∣ (polyTwistInv^[1]) Q ∧ Q ∣ E * Z := by
  obtain ⟨D, hD1, hD2, hD3⟩ := exists_den_iterate_of_R_row (F := F) j hQ hZ hG hrow
  have hΨQ : ∀ n, ((polyTwistInv^[1]) Q).coeff n ∈ ambKperf F := polyTwistInv_coeff_mem hQ
  refine ⟨((polyTwist (q := Nat.card F) 1)^[j]) D, ?_, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hD1
    refine ⟨((polyTwist (q := Nat.card F) 1)^[j]) c, ?_⟩
    rw [← polyTwist_iterate_polyTwistInv j hQ, hc]
    simp only [polyTwist_iterate_mul]
  · obtain ⟨c, hc⟩ := hD3
    have hc' : (polyTwistInv^[j]) ((polyTwistInv^[1]) Q) = D * c := by
      rw [Function.iterate_one, ← Function.iterate_succ_apply]
      exact hc
    refine ⟨((polyTwist (q := Nat.card F) 1)^[j]) c, ?_⟩
    change (polyTwistInv^[1]) Q = ((polyTwist (q := Nat.card F) 1)^[j]) D
      * ((polyTwist (q := Nat.card F) 1)^[j]) c
    rw [← polyTwist_iterate_polyTwistInv j hΨQ, hc']
    simp only [polyTwist_iterate_mul]
  · obtain ⟨c, hc⟩ := hD2
    refine ⟨((polyTwist (q := Nat.card F) 1)^[j]) c, ?_⟩
    have h := congrArg (((polyTwist (q := Nat.card F) 1)^[j])) hc
    simp only [polyTwist_iterate_mul, polyTwist_iterate_polyTwistInv j hQ,
      polyTwist_iterate_polyTwistInv j hZ] at h
    exact h

/-- ★★★ **The orbit gcd stabilises**: `G_k` is eventually constant up to associates (a
divisibility-decreasing sequence in the PID `K^{perf}[X]`).  This is the "forward tower" input: for
`r ∣ G_K` at the stabilisation index, `r ∣ G_k ~ G_K` for all `k ≥ K`, so `r ∣ (σ⁻¹)^m Q` for **every**
`m ≥ 0` — which is exactly the hypothesis of the (backward) pigeonhole. -/
theorem exists_associated_orbitGcd (Q : Polynomial (Ambient F)) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → Associated (orbitGcd Q k) (orbitGcd Q K) :=
  Commons.Algebra.GCD.associated_of_forall_dvd_of_dvd (orbitGcd Q) (orbitGcd_succ_dvd Q)

/-- The consequence we need: at the stabilisation index, a divisor of `G_K` divides the whole backward
orbit of `Q`. -/
theorem orbitGcd_dvd_orbit_of_stable (Q : Polynomial (Ambient F)) {K : ℕ}
    (hK : ∀ k : ℕ, K ≤ k → Associated (orbitGcd Q k) (orbitGcd Q K)) {r : Polynomial (Ambient F)}
    (hr : r ∣ orbitGcd Q K) (m : ℕ) : r ∣ (polyTwistInv^[m]) Q := by
  rcases lt_or_ge m K with h | h
  · exact dvd_trans hr (orbitGcd_dvd_orbit Q (le_of_lt h))
  · exact dvd_trans hr (dvd_trans (hK m h).symm.dvd (orbitGcd_dvd_orbit Q (le_refl m)))

/-! ## §7. Monicity is preserved by `σ⁻¹` — the last bookkeeping step of the reduction

`PLAN.md` §15.2 step 3: two *associates* that are both monic are equal.  Since `qRoot 1 = 1` and
`qRoot x ≠ 0` for `0 ≠ x ∈ K^{perf}`, the coefficientwise root preserves the `X`-degree and the
leading coefficient.  (Both statements carry the `K^{perf}`-membership explicitly: `qRoot` is junk
off `K^{perf}`.) -/

/-- `σ⁻¹` preserves the `X`-degree (for `K^{perf}`-coefficients). -/
lemma polyTwistInv_natDegree {p : Polynomial (Ambient F)} (hmem : ∀ n, p.coeff n ∈ ambKperf F) :
    (polyTwistInv p).natDegree = p.natDegree := by
  have hle : (polyTwistInv p).natDegree ≤ p.natDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [polyTwistInv_coeff]
    by_cases h : m ∈ p.support
    · rw [if_pos h, Polynomial.coeff_eq_zero_of_natDegree_lt hm, qRoot_zero]
    · rw [if_neg h]
  rcases eq_or_ne p 0 with h0 | h0
  · rw [h0, polyTwistInv_zero]
  have htop : (polyTwistInv p).coeff p.natDegree ≠ 0 := by
    rw [polyTwistInv_coeff,
      if_pos (Polynomial.mem_support_iff.mpr (by
        rw [← Polynomial.leadingCoeff]
        exact Polynomial.leadingCoeff_ne_zero.mpr h0)),
      ← Polynomial.leadingCoeff]
    exact qRoot_ne_zero (hmem _) (Polynomial.leadingCoeff_ne_zero.mpr h0)
  exact le_antisymm hle (Polynomial.le_natDegree_of_ne_zero htop)

/-- ★★★ **`σ⁻¹` preserves the leading coefficient `1`** (for `K^{perf}`-coefficients).  This is
`PLAN.md` §15.2 step 3's content: two *associates* that both have leading coefficient `1` are equal,
since they have the same `X`-degree and are equal up to a unit. -/
lemma polyTwistInv_leadingCoeff {p : Polynomial (Ambient F)} (hlead : p.leadingCoeff = 1)
    (hmem : ∀ n, p.coeff n ∈ ambKperf F) : (polyTwistInv p).leadingCoeff = 1 := by
  have hsupp : p.natDegree ∈ p.support := by
    rw [Polynomial.mem_support_iff, ← Polynomial.leadingCoeff, hlead]
    exact one_ne_zero
  rw [Polynomial.leadingCoeff, polyTwistInv_natDegree (F := F) hmem, polyTwistInv_coeff,
    if_pos hsupp, ← Polynomial.leadingCoeff, hlead, qRoot_one]

/-! ## §8. The two families of the matching (`PLAN.md` §14.2)

**(γ)** asks for `∃E ∣ G_K, Q ∣ E·Z`.  The two families that must be matched are:

* **level-wise** (`exists_den_iterate_of_R_row`): for each `j`, a `D_j` with `D_j ∣ Q⁽ʲ⁾`,
  `Q⁽ʲ⁾ ∣ D_j·Z⁽ʲ⁾`, `D_j ∣ Q⁽ʲ⁺¹⁾` — pushed forward by `σ^j` this gives the right `Z`-shape
  (`Q ∣ E_j·Z`, one untwisted `Z`) but only **two** orbit levels (`Q`, `σ⁻¹Q`);
* **chain-wise** (below): with `P_k := Z·(σ⁻¹)Z⋯(σ⁻¹)^{k-1}Z`,

  > **(CHAIN-k)**  `Q ∣ Q⁽ᵏ⁾ · P_k`  for **every** `k`,

  which gives all the levels but with the `Z`-product `P_k` attached.

The next section proves (CHAIN-k) and its extraction, i.e. the whole chain family, so that the
matching statement has both sides available as theorems. -/

/-- `P_k := Z · (σ⁻¹)Z ⋯ (σ⁻¹)^{k-1}Z`, the `Z`-product of the chain family. -/
noncomputable def orbitZProd (Z : Polynomial (Ambient F)) (k : ℕ) : Polynomial (Ambient F) :=
  ∏ j ∈ Finset.range k, (polyTwistInv^[j]) Z

@[simp] lemma orbitZProd_zero (Z : Polynomial (Ambient F)) : orbitZProd Z 0 = 1 := by
  simp [orbitZProd]

/-- The `k → k+1` recursion of `P_k`. -/
lemma orbitZProd_succ (Z : Polynomial (Ambient F)) (k : ℕ) :
    orbitZProd Z (k + 1) = orbitZProd Z k * (polyTwistInv^[k]) Z := by
  rw [orbitZProd, Finset.prod_range_succ, orbitZProd]

/-- ★★★★ **THE CHAIN FAMILY** (`PLAN.md` §14.2, (CHAIN-k)): `Q ∣ Q⁽ᵏ⁾ · P_k` for every `k`.  The
induction multiplies the level-`k` level-shift `Q⁽ᵏ⁾ ∣ Q⁽ᵏ⁺¹⁾Z⁽ᵏ⁾` (i.e. `(CHAIN-k)`) by the
chain product of the previous level. -/
theorem dvd_chain_of_R_row (k : ℕ) {w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F) (hZ : ∀ n, Z.coeff n ∈ ambKperf F)
    (hG : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambKperf F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    Q ∣ (polyTwistInv^[k]) Q * orbitZProd Z k := by
  induction k with
  | zero => simp
  | succ n ih =>
      obtain ⟨c, hc⟩ := dvd_polyTwistInv_iterate_row_R (F := F) n hQ hZ hG hrow
      obtain ⟨e, he⟩ := ih
      refine ⟨c * e, ?_⟩
      rw [orbitZProd_succ]
      calc (polyTwistInv^[n + 1]) Q * (orbitZProd Z n * (polyTwistInv^[n]) Z)
          = ((polyTwistInv^[n + 1]) Q * (polyTwistInv^[n]) Z) * orbitZProd Z n := by ring
        _ = ((polyTwistInv^[n]) Q * c) * orbitZProd Z n := by rw [hc]
        _ = c * ((polyTwistInv^[n]) Q * orbitZProd Z n) := by ring
        _ = c * (Q * e) := by rw [he]
        _ = Q * (c * e) := by ring

/-- ★★★★ **The chain-denominator**: the factor `D_k := Q/gcd(Q, P_k)` satisfies `D_k ∣ Q`,
`Q ∣ D_k·P_k`, and **`D_k ∣ Q⁽ᵏ⁾`** — the levels-property that the level-wise family lacks. -/
theorem exists_den_chain_of_R_row (k : ℕ) {w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F) (hZ : ∀ n, Z.coeff n ∈ ambKperf F)
    (hG : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambKperf F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    ∃ D : Polynomial (Ambient F),
      D ∣ Q ∧ Q ∣ D * orbitZProd Z k ∧ D ∣ (polyTwistInv^[k]) Q := by
  have h := dvd_chain_of_R_row (F := F) k hQ hZ hG hrow
  exact exists_den_dvd_of_dvd_mul (a := Q) (b := orbitZProd Z k) (c := (polyTwistInv^[k]) Q)
    (by rwa [mul_comm] at h)

/-- ★★★★ **The forward tower for the chain family**: pushing a divisor of `Q⁽ᵏ⁾` forward by `σ^k`
lands in the divisors of `Q`.  This is the half of the matching that the *chain* supplies for every
level (`σ^k(D_k) ∣ Q` for all `k`), whereas the level-wise family supplies the `Z`-shape. -/
theorem dvd_iterate_of_dvd_iterate_orbit {D : Polynomial (Ambient F)} {Q : Polynomial (Ambient F)}
    {k : ℕ} (hQ : ∀ n, Q.coeff n ∈ ambKperf F)
    (h : D ∣ (polyTwistInv^[k]) Q) :
    ((polyTwist (q := Nat.card F) 1)^[k]) D ∣ Q := by
  obtain ⟨c, hc⟩ := h
  refine ⟨((polyTwist (q := Nat.card F) 1)^[k]) c, ?_⟩
  rw [← polyTwist_iterate_polyTwistInv k hQ, hc]
  simp only [polyTwist_iterate_mul]

end ZagierHoffmanPositiveChar
