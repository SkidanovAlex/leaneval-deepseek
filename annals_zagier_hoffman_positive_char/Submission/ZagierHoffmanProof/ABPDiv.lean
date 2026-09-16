import Submission.ZagierHoffmanProof.GenEvalEntire
import Submission.Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le_general
import Submission.Commons.RingTheory.PowerSeries.coeff_mul_X

/-!
# Division of a power series by a linear factor (the Schwarz–Jensen step of ABP)

Let `K` be a complete nonarchimedean field with archimedean value group (`GammaArchimedean`),
`c ∈ K` with `v c < 1` and `f ∈ K⟦t⟧` a series whose coefficients are bounded by `a` and which
*vanishes* at `c` (i.e. `∑' n, f_n c^n = 0`).

Then `f = (t - c)·g` for an explicit `g` (`tailQuot f c`) whose coefficients are **again bounded
by `a`**:

  `g_n = (c^(n+1))⁻¹ · ∑_{j≥0} f_{n+1+j} c^(n+1+j)`

(collapsing the finite recursion `g_n = (g_{n-1} - f_n)/c` using the vanishing of `f(c)` — this
is where the vanishing hypothesis enters, and it is what makes the bound *constant* rather than
`a·(v c)^{-n}`).

Iterating this over a finite set of points `ω_1, …, ω_M` gives the **Schwarz–Jensen inequality**
of PLAN §8: if `f ⟼ λ_f` is the lowest non-vanishing coefficient of `f`, then

  `v λ_f = ∑_i v ω_i + v (g_M)_0  ≤  ∑_i v ω_i + a`,

i.e. in Gauss-norm language `|λ_f|·∏(r/|ω_i|) ≤ |f|_r` (with `r = (v ω)^{-1}`).

## Main results

* `summable_of_v_le_mul_pow` — summability from a geometric valuation bound.
* `tailQuot`, `coeff_tailQuot`.
* ★★★ `exists_quot_X_sub_C` — the division with the constant coefficient bound.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- Summability from a geometric valuation bound: if `v (f n) ≤ C · γ ^ n` with `γ < 1` and the
value group archimedean, then `f` is summable. -/
lemma summable_of_v_le_mul_pow {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {C : Γ₀} {f : ℕ → K} (h : ∀ n : ℕ, Valued.v (f n) ≤ C * γ ^ n) : Summable f := by
  rcases eq_or_ne C 0 with hC | hC
  · refine summable_of_v_tendsto_zero (fun ε hε => ?_)
    refine Filter.Eventually.of_forall (fun n => ?_)
    simp only [hC, zero_mul] at h
    exact lt_of_le_of_lt (h n) (zero_lt_of_ne_zero hε)
  · have hCpos : 0 < C := zero_lt_of_ne_zero hC
    refine summable_of_v_tendsto_zero (fun ε hε => ?_)
    obtain ⟨N, hN⟩ := harch γ hγ (ε * C⁻¹) (by simp [hε, hC])
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    refine lt_of_le_of_lt (h n) ?_
    calc C * γ ^ n ≤ C * γ ^ N :=
          mul_le_mul_right (pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ.le hn) C
      _ < C * (ε * C⁻¹) := mul_lt_mul_of_pos_left hN hCpos
      _ = ε := by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hC, mul_one]

section div

variable {c : K} {f : PowerSeries K} {a : Γ₀}

/-- The coefficientwise valuation of the `N`-th tail of `f` at `c`. -/
lemma summable_tail_mul (harch : GammaArchimedean Γ₀) (hc : Valued.v c < 1)
    (hf : ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a) (N : ℕ) :
    Summable fun j : ℕ => PowerSeries.coeff (N + j) f * c ^ (N + j) := by
  refine summable_of_v_le_mul_pow hc harch (C := a * (Valued.v c) ^ N) (fun j => ?_)
  rw [map_mul, map_pow, pow_add]
  calc Valued.v (PowerSeries.coeff (N + j) f) * ((Valued.v c) ^ N * (Valued.v c) ^ j)
      = (Valued.v (PowerSeries.coeff (N + j) f) * (Valued.v c) ^ N) * (Valued.v c) ^ j :=
        (mul_assoc _ _ _).symm
    _ ≤ (a * (Valued.v c) ^ N) * (Valued.v c) ^ j :=
        mul_le_mul (mul_le_mul (hf (N + j)) le_rfl (zero_le : (0 : Γ₀) ≤ _)
          (zero_le : (0 : Γ₀) ≤ _)) le_rfl (zero_le : (0 : Γ₀) ≤ _) (zero_le : (0 : Γ₀) ≤ _)

/-- The valuation of the `N`-th tail sum is bounded by `a · (v c) ^ N`. -/
lemma v_tail_le (harch : GammaArchimedean Γ₀) (hc : Valued.v c < 1)
    (hf : ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a) (N : ℕ) :
    Valued.v (∑' j : ℕ, PowerSeries.coeff (N + j) f * c ^ (N + j))
      ≤ a * (Valued.v c) ^ N := by
  refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le_general
    (summable_tail_mul harch hc hf N) (fun j => ?_)
  rw [map_mul, map_pow, pow_add]
  calc Valued.v (PowerSeries.coeff (N + j) f) * ((Valued.v c) ^ N * (Valued.v c) ^ j)
      = (Valued.v (PowerSeries.coeff (N + j) f) * (Valued.v c) ^ N) * (Valued.v c) ^ j :=
        (mul_assoc _ _ _).symm
    _ ≤ (a * (Valued.v c) ^ N) * (Valued.v c) ^ j :=
        mul_le_mul (mul_le_mul (hf (N + j)) le_rfl (zero_le : (0 : Γ₀) ≤ _)
          (zero_le : (0 : Γ₀) ≤ _)) le_rfl (zero_le : (0 : Γ₀) ≤ _) (zero_le : (0 : Γ₀) ≤ _)
    _ ≤ a * (Valued.v c) ^ N := by
        conv_rhs => rw [← mul_one (a * (Valued.v c) ^ N)]
        exact mul_le_mul le_rfl (pow_le_one₀ (zero_le : (0 : Γ₀) ≤ _) hc.le)
          (zero_le : (0 : Γ₀) ≤ _) (zero_le : (0 : Γ₀) ≤ _)

/-- The coefficient of the quotient `f/(t - c)` obtained by collapsing the recursion
`g_n = (g_{n-1} - f_n)/c` with the vanishing of `f(c)`. -/
noncomputable def tailQuotCoeff (f : PowerSeries K) (c : K) (n : ℕ) : K :=
  (c ^ (n + 1))⁻¹ * ∑' j : ℕ, PowerSeries.coeff (n + 1 + j) f * c ^ (n + 1 + j)

/-- The quotient `f/(t - c)` of a series vanishing at `c`. -/
noncomputable def tailQuot (f : PowerSeries K) (c : K) : PowerSeries K :=
  PowerSeries.mk (tailQuotCoeff f c)

lemma coeff_tailQuot (n : ℕ) : PowerSeries.coeff n (tailQuot f c) = tailQuotCoeff f c n :=
  PowerSeries.coeff_mk n _

/-- The recursion of the tail sums: `T N = f_N c^N + T (N+1)`. -/
lemma tail_rec (harch : GammaArchimedean Γ₀) (hc : Valued.v c < 1)
    (hf : ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a) (N : ℕ) :
    (∑' j : ℕ, PowerSeries.coeff (N + j) f * c ^ (N + j))
      = PowerSeries.coeff N f * c ^ N
        + ∑' j : ℕ, PowerSeries.coeff (N + 1 + j) f * c ^ (N + 1 + j) := by
  have hg : Summable fun j : ℕ => PowerSeries.coeff (N + j) f * c ^ (N + j) :=
    summable_tail_mul harch hc hf N
  have h := hg.tsum_eq_zero_add
  have h1 : PowerSeries.coeff (N + 0) f * c ^ (N + 0) = PowerSeries.coeff N f * c ^ N := by
    rw [Nat.add_zero]
  rw [h, h1]
  refine congrArg (fun x => PowerSeries.coeff N f * c ^ N + x) ?_
  refine tsum_congr (fun j => ?_)
  rw [show N + (j + 1) = N + 1 + j from by omega]

/-- The coefficients of the quotient are bounded by `a`. -/
lemma v_coeff_tailQuot_le (harch : GammaArchimedean Γ₀) (hc0 : c ≠ 0)
    (hc : Valued.v c < 1)
    (hf : ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a) (n : ℕ) :
    Valued.v (PowerSeries.coeff n (tailQuot f c)) ≤ a := by
  rw [coeff_tailQuot, tailQuotCoeff, map_mul, Valuation.map_inv, Valuation.map_pow]
  have hcne : (Valued.v c) ^ (n + 1) ≠ 0 :=
    pow_ne_zero _ ((Valuation.ne_zero_iff Valued.v).mpr hc0)
  calc ((Valued.v c) ^ (n + 1))⁻¹
        * Valued.v (∑' j : ℕ, PowerSeries.coeff (n + 1 + j) f * c ^ (n + 1 + j))
      ≤ ((Valued.v c) ^ (n + 1))⁻¹ * (a * (Valued.v c) ^ (n + 1)) :=
        mul_le_mul le_rfl (v_tail_le harch hc hf (n + 1))
          (zero_le : (0 : Γ₀) ≤ _) (zero_le : (0 : Γ₀) ≤ _)
    _ = a := by rw [mul_comm a, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul]

/-- **Division of a power series by a linear factor** (the Schwarz–Jensen step of ABP).

If `c ≠ 0` has `v c < 1` and the series `f` has coefficients bounded by `a` and vanishes at `c`
(`∑' n, f_n c^n = 0`), then `f = (t - c)·(tailQuot f c)` and the quotient again has coefficients
bounded by `a`. -/
theorem tailQuot_spec (harch : GammaArchimedean Γ₀) (hc0 : c ≠ 0) (hc : Valued.v c < 1)
    (hf : ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a)
    (hroot : (∑' n : ℕ, PowerSeries.coeff n f * c ^ n) = 0) :
    f = (PowerSeries.X - PowerSeries.C c) * tailQuot f c := by
  set T : ℕ → K := fun N => ∑' j : ℕ, PowerSeries.coeff (N + j) f * c ^ (N + j) with hT
  have hrec : ∀ N, T N = PowerSeries.coeff N f * c ^ N + T (N + 1) := fun N => by
    rw [hT]; exact tail_rec harch hc hf N
  have hT0 : T 0 = 0 := by
    simp only [hT]
    rw [show (∑' j : ℕ, PowerSeries.coeff (0 + j) f * c ^ (0 + j))
        = ∑' n : ℕ, PowerSeries.coeff n f * c ^ n from
        tsum_congr (fun j => by rw [Nat.zero_add])]
    exact hroot
  have hgcoeff : ∀ n, PowerSeries.coeff n (tailQuot f c) = (c ^ (n + 1))⁻¹ * T (n + 1) :=
    fun n => by rw [coeff_tailQuot, tailQuotCoeff, hT]
  have hcne : c ^ 1 ≠ 0 := pow_ne_zero 1 hc0
  ext n
  symm
  rw [sub_mul, mul_comm (PowerSeries.X) (tailQuot f c), map_sub,
    Commons.RingTheory.PowerSeries.coeff_mul_X, PowerSeries.coeff_C_mul]
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    rw [if_neg (by omega : ¬ (1 ≤ 0)), hgcoeff 0]
    have hr := hrec 0
    rw [hT0, pow_zero, mul_one] at hr
    have hr' : PowerSeries.coeff 0 f + T 1 = 0 := by simpa using hr.symm
    have hT1 : T 1 = -PowerSeries.coeff 0 f := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hr'
    rw [hT1, pow_one]
    field_simp
    ring
  · have h1 : PowerSeries.coeff (n - 1) (tailQuot f c) = (c ^ n)⁻¹ * T n := by
      rw [hgcoeff (n - 1), Nat.sub_add_cancel hn]
    rw [if_pos (show 1 ≤ n from hn), h1, hgcoeff n, hrec n]
    have h2 : c * (c ^ (n + 1))⁻¹ = (c ^ n)⁻¹ := by
      rw [pow_succ]
      field_simp
    rw [← mul_assoc, h2, mul_add,
      show (c ^ n)⁻¹ * (PowerSeries.coeff n f * c ^ n)
        = PowerSeries.coeff n f * ((c ^ n)⁻¹ * c ^ n) from by ring,
      inv_mul_cancel₀ (pow_ne_zero n hc0), mul_one]
    ring

/-- **Existence form of the division**: a series with coefficients bounded by `a` vanishing at
`c` (`c ≠ 0`, `v c < 1`) is `(t - c)` times a series with coefficients still bounded by `a`. -/
theorem exists_quot_X_sub_C (harch : GammaArchimedean Γ₀) (hc0 : c ≠ 0) (hc : Valued.v c < 1)
    (hf : ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a)
    (hroot : (∑' n : ℕ, PowerSeries.coeff n f * c ^ n) = 0) :
    ∃ g : PowerSeries K, f = (PowerSeries.X - PowerSeries.C c) * g ∧
      ∀ n : ℕ, Valued.v (PowerSeries.coeff n g) ≤ a :=
  ⟨tailQuot f c, tailQuot_spec harch hc0 hc hf hroot,
    v_coeff_tailQuot_le harch hc0 hc hf⟩

/-- The same with the vanishing hypothesis stated as the evaluation `evalSeriesGen f c = 0`. -/
theorem exists_quot_X_sub_C_of_eval (harch : GammaArchimedean Γ₀) (hc0 : c ≠ 0)
    (hc : Valued.v c < 1) (hf : ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a)
    (hroot : evalSeriesGen f c = 0) :
    ∃ g : PowerSeries K, f = (PowerSeries.X - PowerSeries.C c) * g ∧
      ∀ n : ℕ, Valued.v (PowerSeries.coeff n g) ≤ a :=
  exists_quot_X_sub_C harch hc0 hc hf hroot

end div

end ZagierHoffmanPositiveChar
