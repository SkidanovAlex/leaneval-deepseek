import Submission.ZagierHoffmanProof.EndgameFinal
import Submission.ZagierHoffmanProof.AmbRootLevel
import Submission.ZagierHoffmanProof.CoeffNu

/-!
# SESSION 361 — the last case `w = 2q-2`: the `q`-th root `V` of `num + N·D`

`PLAN.md` §«SESSION 361».  The integral recursion of `EndgameFinal.dvd_pred_of_data` reads
`σ num = W^w·(num + N·D)` with `num, N ∈ A_0[X] = F_q[θ][X]`, `D ∈ F_q[X]`, `W = X - C(θ^q)`,
`w = 2q-2`.  Applying `σ^{-1}` turns it into the **polynomial** identity

  `num = L^w·V`,   `L := X - C θ`,   **`σ V = num + N·D`**,

where `V ∈ A_1[X]`, `A_1 = F_q[θ_1]`, `θ_1 = θ^{1/q}`.  `V` is built coefficientwise from the
`q`-th roots realised by `AmbRootLevel.ambRootAt F 0 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial
open scoped WithZero Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The coefficientwise `q`-th root -/

/-- ★★★★ **The coefficientwise `q`-th root, in `A_1`.**  For `p ∈ A_0[X]` this is the (unique)
polynomial `V ∈ A_1[X]` with `σ V = p`. -/
noncomputable def qthRootPoly (p : Polynomial (Ambient F))
    (hp : ∀ n, p.coeff n ∈ ambA F 0) : Polynomial (Ambient F) :=
  p.sum (fun n _ => Polynomial.C (ambRootAt F 0 1 (p.coeff n) (hp n)) * Polynomial.X ^ n)

/-- The coefficients of `qthRootPoly`. -/
lemma qthRootPoly_coeff {p : Polynomial (Ambient F)} (hp : ∀ n, p.coeff n ∈ ambA F 0) (m : ℕ) :
    (qthRootPoly F p hp).coeff m
      = if m ∈ p.support then ambRootAt F 0 1 (p.coeff m) (hp m) else 0 := by
  classical
  rw [qthRootPoly, Polynomial.coeff_sum, Polynomial.sum_def]
  have h1 : ∀ n ∈ p.support,
      ((Polynomial.C (ambRootAt F 0 1 (p.coeff n) (hp n)) * Polynomial.X ^ n :
        Polynomial (Ambient F)).coeff m)
        = if m = n then ambRootAt F 0 1 (p.coeff n) (hp n) else 0 := by
    intro n _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hmn : m = n
    · rw [if_pos hmn, if_pos hmn, mul_one]
    · rw [if_neg hmn, if_neg hmn, mul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq]

/-- `σ` of the coefficientwise `q`-th root is the original polynomial. -/
theorem polyTwist_qthRootPoly {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F 0) :
    polyTwist (q := Nat.card F) 1 (qthRootPoly F p hp) = p := by
  ext m
  rw [polyTwist_one_coeff, qthRootPoly_coeff F hp m]
  by_cases hm : m ∈ p.support
  · rw [if_pos hm]
    have h := ambRootAt_pow F 0 1 (p.coeff m) (hp m)
    rw [pow_one] at h
    exact h
  · rw [if_neg hm, zero_pow (FrobPow.ne_zero (Ambient F) (q := Nat.card F))]
    rw [Polynomial.mem_support_iff] at hm
    exact (not_not.mp hm).symm

/-- The coefficients of `qthRootPoly` lie in `A_1 = F_q[θ^{1/q}]`. -/
lemma qthRootPoly_coeff_mem {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (m : ℕ) :
    (qthRootPoly F p hp).coeff m ∈ ambA F 1 := by
  classical
  rw [qthRootPoly_coeff F hp m]
  by_cases hm : m ∈ p.support
  · rw [if_pos hm]
    have := ambRootAt_mem F 0 1 (p.coeff m) (hp m)
    simpa using this
  · rw [if_neg hm]
    exact (ambASub F 1).zero_mem

/-! ## §2. The `θ_1`-support of `A_0 = F_q[θ]` is `qℤ` -/

/-- ★★★ Since `θ = θ_1^q`, every element of `A_0 = F_q[θ]` has `θ_1`-support in `qℤ`. -/
lemma coeffNu_one_eq_zero_of_mem_ambA_zero {x : Ambient F} (hx : x ∈ ambA F 0) {t : ℕ}
    (ht : ¬ Nat.card F ∣ t) : coeffNu F 1 t x = 0 := by
  obtain ⟨pp, hp⟩ := (mem_ambA_iff F 0 x).mp hx
  have htheta : (ambThetaNu F 1) ^ Nat.card F = ambTheta F := by
    simpa using ambThetaNu_pow F 1
  have hcomp : (pp.comp (Polynomial.X ^ Nat.card F)).eval₂ (algebraMap F (Ambient F))
      (ambThetaNu F 1) = x := by
    rw [Polynomial.eval₂_comp, Polynomial.eval₂_pow, Polynomial.eval₂_X, htheta]
    simpa [ambThetaNu_zero] using hp
  rw [coeffNu_eq_of_eval F (ambA_mono F (Nat.zero_le 1) hx) hcomp t,
    ← Polynomial.expand_eq_comp_X_pow,
    Polynomial.coeff_expand (p := Nat.card F)
      (Nat.pos_of_ne_zero (FrobPow.ne_zero (Ambient F) (q := Nat.card F))) pp t,
    if_neg ht, map_zero]

/-! ## §3. `num = L^w · V` -/

/-- ★★★★ **The recursion becomes a *polynomial* identity**: `num = L^w·V` with `L = X - C θ`.
This is the `σ^{-1}` of `σ num = W^w·(num + N·D)`, with no fraction field. -/
theorem num_eq_L_pow_mul_qthRoot {w : ℕ} {N num D : Polynomial (Ambient F)}
    (hrec : polyTwist (q := Nat.card F) 1 num
      = (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w * (num + N * D))
    (hmem : ∀ n, (num + N * D).coeff n ∈ ambA F 0) :
    num = (Polynomial.X - Polynomial.C (ambTheta F)) ^ w * qthRootPoly F (num + N * D) hmem := by
  have h1 : polyTwist (q := Nat.card F) 1 num
      = polyTwist (q := Nat.card F) 1 ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w
          * qthRootPoly F (num + N * D) hmem) := by
    rw [polyTwist_mul, polyTwist_pow, polyTwist_X_sub_C_theta, polyTwist_qthRootPoly, hrec]
  exact polyTwist_one_injective F h1

/-! ## §4. The `θ_1`-read atoms -/

/-- `coeffNu F 1 0` of a `θ_1`-monomial with an `F_q`-coefficient. -/
lemma coeffNu_one_zero_monomial (c : F) (m : ℕ) :
    coeffNu F 1 0 (ambCoeff F c * (ambThetaNu F 1) ^ m)
      = if m = 0 then ambCoeff F c else 0 := by
  have hcmem : ambCoeff F c ∈ ambA F 1 :=
    ambA_mono F (Nat.zero_le 1) (mem_ambA_zero_of_mem_ambF (ambCoeff_mem_ambF F c))
  have hmem : ambCoeff F c * (ambThetaNu F 1) ^ m ∈ ambA F 1 :=
    ambA_mul_mem F hcmem (ambA_pow_mem F 1 (ambThetaNu_mem_ambA F 1) m)
  rw [coeffNu_eq_of_eval F hmem (p := Polynomial.C c * Polynomial.X ^ m) (by
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      algebraMap_ambient_eq]), Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hm : m = 0
  · rw [if_pos (show 0 = m from hm.symm), mul_one, ← algebraMap_ambient_eq, if_pos hm]
  · rw [if_neg (show ¬ (0 = m) from by omega), mul_zero, map_zero, if_neg hm]

/-! ## §5. The `L^w`-coefficient read, and the `θ_1`-read of `V` -/

/-- ★★★ **The `X^a`-coefficient of `(X - Cθ)^w`**, as an `F_q`-multiple of `θ^(w-a)`. -/
lemma coeff_X_sub_C_theta_pow (w a : ℕ) :
    ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff a
      = ambCoeff F ((-1 : F) ^ (w - a) * (w.choose a : F)) * (ambTheta F) ^ (w - a) := by
  have hX : (Polynomial.X - Polynomial.C (ambTheta F) : Polynomial (Ambient F))
      = Polynomial.X + Polynomial.C (-(ambTheta F)) := by
    rw [Polynomial.C_neg]; ring
  have hneg : (-(ambTheta F) : Ambient F) = ambCoeff F (-1) * ambTheta F := by
    rw [map_neg, map_one]; ring
  rw [hX, Polynomial.coeff_X_add_C_pow, hneg, mul_pow, map_mul, map_pow, map_natCast]
  ring

/-- ★★★★ **The `θ_1^0`-coefficient of `(X - Cθ)^w`'s coefficients**: `1` on the leading term `a = w`
and `0` elsewhere. -/
lemma coeffNu_one_zero_coeff_L_pow {w a : ℕ} :
    coeffNu F 1 0 (((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff a)
      = if a = w then 1 else 0 := by
  have htheta : (ambTheta F) = (ambThetaNu F 1) ^ Nat.card F := by
    simpa using (ambThetaNu_pow F 1).symm
  rcases lt_trichotomy a w with h | h | h
  · have hm : 0 < w - a := by omega
    rw [coeff_X_sub_C_theta_pow,
      show (ambTheta F) ^ (w - a) = (ambThetaNu F 1) ^ (Nat.card F * (w - a)) from by
        rw [htheta, ← pow_mul],
      coeffNu_one_zero_monomial,
      if_neg (Nat.mul_ne_zero (by have := two_le_ambCard F; omega) (by omega)),
      if_neg (by omega : ¬ a = w)]
  · subst h
    rw [coeff_X_sub_C_pow_self, if_pos rfl]
    conv_lhs => rw [show (1 : Ambient F) = ambCoeff F 1 * (ambThetaNu F 1) ^ 0 by
      rw [pow_zero, mul_one, map_one]]
    rw [coeffNu_one_zero_monomial, if_pos rfl]
    exact map_one (ambCoeff F)
  · have h0 : ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff a = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
        exact h)
    rw [h0, if_neg (by omega : ¬ a = w), coeffNu_zero]

/-! ## §6. The term-level step of the `θ₁`-read -/

/-- ★★★★★ **The term-level `θ₁`-read.**  For `x ∈ A_0 = F_q[θ]`, `y ∈ A_1` and `1 ≤ t < q`, the
`θ_1^t`-coefficient of `x·y` is `c·(θ_1^t-coefficient of y)` where `c := coeffNu F 1 0 x` is the
`θ_1^0`-coefficient of `x`: all the other antidiagonal terms die because `x` has `θ_1`-support in
`qℤ` (`coeffNu_one_eq_zero_of_mem_ambA_zero`) and `a' ≤ t < q`.

The conclusion is deliberately free of `Polynomial (Ambient F)`: the two polynomials of the endgame
enter only through the *scalars* `x`, `y` and the membership hypotheses. -/
lemma coeffNu_theta_one_mul_of_mem_ambA_zero {t : ℕ} {x y : Ambient F}
    (hx : x ∈ ambA F 0) (hy : y ∈ ambA F 1) (htq : ¬ Nat.card F ∣ t) (ht1 : 1 ≤ t)
    (htq2 : t < Nat.card F) (c : Ambient F) (hc : coeffNu F 1 0 x = c) :
    coeffNu F 1 t (x * y) = c * coeffNu F 1 t y := by
  have hx1 : x ∈ ambA F 1 := ambA_mono F (Nat.zero_le 1) hx
  rw [coeffNu_mul (F := F) hx1 hy t, Finset.sum_eq_single (0, t)]
  · rw [hc]
  · intro z hz hzne
    have hz1 : z.1 ≠ 0 := by
      rintro h0
      exact hzne (Prod.ext h0 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hz; omega))
    have hzq : ¬ Nat.card F ∣ z.1 := by
      rintro ⟨k, hk⟩
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hz
      have hk0 : k = 0 := by
        by_contra hk0
        have h1 : Nat.card F ≤ Nat.card F * k := by
          calc Nat.card F = Nat.card F * 1 := (mul_one _).symm
            _ ≤ Nat.card F * k :=
                Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0))
        have h2 : Nat.card F * k ≤ t := by omega
        omega
      exact hz1 (by rw [hk, hk0, mul_zero])
    rw [coeffNu_one_eq_zero_of_mem_ambA_zero (F := F) hx hzq, zero_mul]
  · intro hnot
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega : 0 + t = t)) hnot

/-! ## §7. The `θ₁`-read of `V` -/

/-- ★★★★★ **The `θ₁`-read of `V`** (`PLAN.md` §«SESSION 361» §3.1).  If `V ∈ A_1[X]`, `L^w·V ∈ A_0[X]`
(`L = X - C θ`) and `1 ≤ t < q`, then the `θ₁^t`-coefficient of every coefficient of `V` vanishes:
only the `θ_1`-levels `∈ qℤ` survive. -/
theorem V_theta_one_reads {w t : ℕ} {V num : Polynomial (Ambient F)}
    (hV : ∀ n, V.coeff n ∈ ambA F 1)
    (hnum : ∀ n, num.coeff n ∈ ambA F 0)
    (hprod : num = (Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V)
    (htq : ¬ Nat.card F ∣ t) (ht1 : 1 ≤ t) (htq2 : t < Nat.card F) :
    ∀ j, coeffNu F 1 t (V.coeff j) = 0 := by
  classical
  have hL0 : ∀ a, ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff a ∈ ambA F 0 := fun a =>
    coeff_pow_mem_ambA (fun i => coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero i) w a
  have hL1 : ∀ a, ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff a ∈ ambA F 1 :=
    fun a => ambA_mono F (Nat.zero_le 1) (hL0 a)
  intro j
  have h0 : coeffNu F 1 t (num.coeff (j + w)) = 0 :=
    coeffNu_one_eq_zero_of_mem_ambA_zero (F := F) (hnum _) htq
  have hexp : num.coeff (j + w)
      = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (j + w),
          ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff x.1 * V.coeff x.2 := by
    rw [hprod, Polynomial.coeff_mul]
  rw [hexp] at h0
  have hsum := coeffNu_sum (F := F)
      (s := Finset.HasAntidiagonal.antidiagonal (j + w))
      (f := fun x => ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff x.1 * V.coeff x.2)
      (fun x _ => ambA_mul_mem F (hL1 x.1) (hV x.2)) t
  rw [hsum] at h0
  have hterm : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (j + w),
      coeffNu F 1 t (((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff x.1 * V.coeff x.2)
        = (coeffNu F 1 0 (((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff x.1))
            * coeffNu F 1 t (V.coeff x.2) :=
    fun x _ => coeffNu_theta_one_mul_of_mem_ambA_zero (F := F) (hL0 x.1) (hV x.2) htq ht1 htq2
      _ rfl
  rw [Finset.sum_congr rfl hterm] at h0
  have hterm2 : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (j + w),
      (coeffNu F 1 0 (((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff x.1))
          * coeffNu F 1 t (V.coeff x.2)
        = (if x.1 = w then coeffNu F 1 t (V.coeff x.2) else 0) := by
    intro x _
    rw [coeffNu_one_zero_coeff_L_pow]
    by_cases hxw : x.1 = w
    · rw [if_pos hxw, one_mul, if_pos hxw]
    · rw [if_neg hxw, zero_mul, if_neg hxw]
  rw [Finset.sum_congr rfl hterm2] at h0
  rw [Finset.sum_eq_single (w, j)] at h0
  · rwa [if_pos rfl] at h0
  · intro x hx hxne
    rw [if_neg]
    intro hxw
    refine hxne (Prod.ext hxw ?_)
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega
  · intro hnot
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega : w + j = j + w)) hnot

/-! ## §8. The `θ₁^(q+t)`-read of `V` -/

/-- ★★★★★ **The term-level `θ₁^(q+t)`-read.**  For `x ∈ A_0`, `y ∈ A_1`, `t < q` and
`coeffNu F 1 t y = 0`, the `θ₁^(q+t)`-coefficient of `x·y` is `c₀` times that of `y`, where
`c₀ = coeffNu F 1 0 x`.  (The only other surviving antidiagonal term is the `a' = q` one, i.e.
`coeffNu F 1 q x · coeffNu F 1 t y`, which the hypothesis kills.) -/
lemma coeffNu_theta_one_mul_add {t : ℕ} {x y : Ambient F}
    (hx : x ∈ ambA F 0) (hy : y ∈ ambA F 1) (ht : t < Nat.card F)
    (c0 : Ambient F) (hc0 : coeffNu F 1 0 x = c0) (hy0 : coeffNu F 1 t y = 0) :
    coeffNu F 1 (Nat.card F + t) (x * y) = c0 * coeffNu F 1 (Nat.card F + t) y := by
  have hx1 : x ∈ ambA F 1 := ambA_mono F (Nat.zero_le 1) hx
  rw [coeffNu_mul (F := F) hx1 hy (Nat.card F + t),
    Finset.sum_eq_single (0, Nat.card F + t)]
  · rw [hc0]
  · intro z hz hzne
    by_cases hzq : Nat.card F ∣ z.1
    · obtain ⟨k, hk⟩ := hzq
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hz
      have h1 : Nat.card F * k ≤ t + Nat.card F := by omega
      have h2 : t + Nat.card F < Nat.card F * 2 := by omega
      have hlt : Nat.card F * k < Nat.card F * 2 := lt_of_le_of_lt h1 h2
      have hk2 : k < 2 :=
        (Nat.mul_lt_mul_left (by have := two_le_ambCard F; omega : 0 < Nat.card F)).mp hlt
      interval_cases k
      · exact absurd (Prod.ext (by omega) (by omega)) hzne
      · rw [show z = (Nat.card F, t) from Prod.ext (by omega) (by omega)]
        show coeffNu F 1 (Nat.card F) x * coeffNu F 1 t y = 0
        rw [hy0, mul_zero]
    · rw [coeffNu_one_eq_zero_of_mem_ambA_zero (F := F) hx hzq, zero_mul]
  · intro hnot
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr
      (by omega : 0 + (Nat.card F + t) = Nat.card F + t)) hnot

/-- ★★★★★ **The `θ₁^(q+t)`-read of `V`** (`PLAN.md` §«SESSION 361» §3.1, second batch): for
`1 ≤ t < q`, the levels `q+t` of `V` vanish as well — using the first-batch read at levels `t`. -/
theorem V_theta_one_reads_add {w t : ℕ} {V num : Polynomial (Ambient F)}
    (hV : ∀ n, V.coeff n ∈ ambA F 1)
    (hnum : ∀ n, num.coeff n ∈ ambA F 0)
    (hprod : num = (Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V)
    (htq : ¬ Nat.card F ∣ t) (ht1 : 1 ≤ t) (htq2 : t < Nat.card F)
    (hfirst : ∀ j, coeffNu F 1 t (V.coeff j) = 0) :
    ∀ j, coeffNu F 1 (Nat.card F + t) (V.coeff j) = 0 := by
  classical
  have hL0 : ∀ a, ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff a ∈ ambA F 0 := fun a =>
    coeff_pow_mem_ambA (fun i => coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero i) w a
  have hL1 : ∀ a, ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff a ∈ ambA F 1 :=
    fun a => ambA_mono F (Nat.zero_le 1) (hL0 a)
  have htq' : ¬ Nat.card F ∣ Nat.card F + t := fun h =>
    htq (Nat.dvd_add_self_left.mp h)
  intro j
  have h0 : coeffNu F 1 (Nat.card F + t) (num.coeff (j + w)) = 0 :=
    coeffNu_one_eq_zero_of_mem_ambA_zero (F := F) (hnum _) htq'
  have hexp : num.coeff (j + w)
      = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (j + w),
          ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff x.1 * V.coeff x.2 := by
    rw [hprod, Polynomial.coeff_mul]
  rw [hexp] at h0
  have hsum := coeffNu_sum (F := F)
      (s := Finset.HasAntidiagonal.antidiagonal (j + w))
      (f := fun x => ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff x.1 * V.coeff x.2)
      (fun x _ => ambA_mul_mem F (hL1 x.1) (hV x.2)) (Nat.card F + t)
  rw [hsum] at h0
  have hterm : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (j + w),
      coeffNu F 1 (Nat.card F + t)
          (((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff x.1 * V.coeff x.2)
        = (coeffNu F 1 0 (((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff x.1))
            * coeffNu F 1 (Nat.card F + t) (V.coeff x.2) :=
    fun x _ => coeffNu_theta_one_mul_add (F := F) (hL0 x.1) (hV x.2) htq2 _ rfl (hfirst x.2)
  rw [Finset.sum_congr rfl hterm] at h0
  have hterm2 : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (j + w),
      (coeffNu F 1 0 (((Polynomial.X - Polynomial.C (ambTheta F)) ^ w).coeff x.1))
          * coeffNu F 1 (Nat.card F + t) (V.coeff x.2)
        = (if x.1 = w then coeffNu F 1 (Nat.card F + t) (V.coeff x.2) else 0) := by
    intro x _
    rw [coeffNu_one_zero_coeff_L_pow]
    by_cases hxw : x.1 = w
    · rw [if_pos hxw, one_mul, if_pos hxw]
    · rw [if_neg hxw, zero_mul, if_neg hxw]
  rw [Finset.sum_congr rfl hterm2] at h0
  rw [Finset.sum_eq_single (w, j)] at h0
  · rwa [if_pos rfl] at h0
  · intro x hx hxne
    rw [if_neg]
    intro hxw
    refine hxne (Prod.ext hxw ?_)
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega
  · intro hnot
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega : w + j = j + w)) hnot

end ZagierHoffmanPositiveChar
