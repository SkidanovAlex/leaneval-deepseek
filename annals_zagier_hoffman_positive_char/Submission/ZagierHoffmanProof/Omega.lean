import Mathlib.RingTheory.PowerSeries.Basic
import Submission.ZagierHoffmanProof.Entire
import Submission.ZagierHoffmanProof.EntireTwist
import Submission.Commons.Topology.Algebra.Valued.summable_of_tendsto_v_zero
import Submission.Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le
import Submission.Commons.RingTheory.PowerSeries.coeff_mul_X
import Submission.Commons.RingTheory.PowerSeries.isUnit_iff_constantCoeff

/-!
# The Anderson–Thakur period function `Ω`

For a field `K` with a `ℤᵐ⁰`-valued valuation and an element `θ` with `v θ = exp 1`, the
Anderson–Thakur period function is the infinite product

  `Ω(t) = ∏_{i ≥ 1} (1 - t / θ^{q^i})`

considered as a power series in the variable `t` with coefficients in `K`.  (In the
application, `K = F(t)_∞` is the completion of `F(t)` at infinity and `θ = X`; the full
period function of the literature also carries the constant `(-θ)^{-q/(q-1)}`, which is a
fractional power of `θ` and does not lie in `K`.)

Rather than an infinite product, `Ω` is defined here as the limit of its partial products
`omPartial N = ∏_{i=1}^N (1 - x_i t)`, `x_i = θ^{-q^i}`, via the telescoping series

  `omCoeff m = ∑' N, (coeff m (omPartial (N+1)) - coeff m (omPartial N)) + coeff m (omPartial 0)`

so that the coefficients of `Ω` are the limits of the coefficients of the partial products
(`tendsto_coeff_omPartial`).

## Main results

* `v_coeff_omPartial_le` — the uniform bound `v (coeff m (omPartial N)) ≤ exp (-m)`.
* `tendsto_coeff_omPartial` — the coefficients of the partial products converge to those of `Ω`.
* `atOmega_twist` — the functional equation `(1 - t/θ^q) · Ω^{(1)} = Ω`, where `Ω^{(1)}` is
  the (`q`-th power) Frobenius twist of the coefficients of `Ω`.
* `atOmega_bounded`, `atOmega_entire` — `Ω` is a Tate (bounded coefficient) and entire series.
* `constantCoeff_atOmega` — `Ω` has constant term `1` (so it is a unit of the Tate algebra).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- The elements `x_i = θ ^ (-q^i) = (θ ^ (q^i))⁻¹` whose elementary symmetric functions
are the coefficients of the partial products of the Anderson–Thakur period function. -/
noncomputable def omX (q : ℕ) (θ : K) (i : ℕ) : K := (θ ^ (q ^ i))⁻¹

/-- The partial products `∏_{i=1}^{N} (1 - x_i t)` of the Anderson–Thakur period function. -/
noncomputable def omPartial (q : ℕ) (θ : K) (N : ℕ) : PowerSeries K :=
  ∏ i ∈ Finset.range N, (1 - PowerSeries.C (omX q θ (i + 1)) * PowerSeries.X)

lemma omX_pow (q : ℕ) (θ : K) (i : ℕ) : (omX q θ i) ^ q = omX q θ (i + 1) := by
  rw [omX, omX, inv_pow, ← pow_mul, ← pow_succ]

lemma omPartial_zero (q : ℕ) (θ : K) : omPartial q θ 0 = 1 := by
  simp [omPartial]

lemma omPartial_succ (q : ℕ) (θ : K) (N : ℕ) :
    omPartial q θ (N + 1)
      = omPartial q θ N * (1 - PowerSeries.C (omX q θ (N + 1)) * PowerSeries.X) := by
  simp only [omPartial, Finset.prod_range_succ]

lemma v_omX (q : ℕ) (θ : K) (hθ : Valued.v θ = WithZero.exp 1) (i : ℕ) :
    Valued.v (omX q θ i) = WithZero.exp (-(((q ^ i : ℕ)) : ℤ)) := by
  rw [omX, Valuation.map_inv, Valuation.map_pow, hθ, expmul 1 (q ^ i), one_mul,
    ← WithZero.exp_neg]

lemma omX_ne_zero (q : ℕ) (θ : K) (hθ : Valued.v θ = WithZero.exp 1) (i : ℕ) :
    omX q θ i ≠ 0 := by
  intro h
  have := v_omX q θ hθ i
  rw [h, map_zero] at this
  exact absurd this.symm (WithZero.exp_ne_zero)

/-- The coefficient recursion for a product with a linear factor `1 - c t`. -/
lemma coeff_mul_one_sub_C_mul_X {f : PowerSeries K} (c : K) (m : ℕ) :
    PowerSeries.coeff m (f * (1 - PowerSeries.C c * PowerSeries.X))
      = PowerSeries.coeff m f
        - (if 1 ≤ m then PowerSeries.coeff (m - 1) f * c else 0) := by
  rw [mul_sub, mul_one, ← mul_assoc, map_sub (PowerSeries.coeff m),
    Commons.RingTheory.PowerSeries.coeff_mul_X, PowerSeries.coeff_mul_C]

lemma coeff_omPartial_succ (q : ℕ) (θ : K) (N m : ℕ) :
    PowerSeries.coeff m (omPartial q θ (N + 1))
      = PowerSeries.coeff m (omPartial q θ N)
        - (if 1 ≤ m then PowerSeries.coeff (m - 1) (omPartial q θ N) * omX q θ (N + 1)
            else 0) := by
  rw [omPartial_succ]
  exact coeff_mul_one_sub_C_mul_X (omX q θ (N + 1)) m

lemma constantCoeff_omPartial (q : ℕ) (θ : K) (N : ℕ) :
    PowerSeries.constantCoeff (omPartial q θ N) = 1 := by
  rw [omPartial, map_prod]
  simp

lemma coeff_zero_omPartial (q : ℕ) (θ : K) (N : ℕ) :
    PowerSeries.coeff 0 (omPartial q θ N) = 1 := by
  have h : PowerSeries.coeff 0 (omPartial q θ N) = PowerSeries.constantCoeff (omPartial q θ N) :=
    congrFun PowerSeries.coeff_zero_eq_constantCoeff _
  rw [h, constantCoeff_omPartial]

/-- The uniform coefficient bound `v (coeff m (omPartial N)) ≤ exp (-m)`. -/
lemma v_coeff_omPartial_le (q : ℕ) (θ : K) (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    ∀ (N m : ℕ), Valued.v (PowerSeries.coeff m (omPartial q θ N))
      ≤ WithZero.exp (-(m : ℤ)) := by
  intro N
  induction N with
  | zero =>
    intro m
    rw [omPartial_zero, PowerSeries.coeff_one]
    by_cases h : m = 0
    · subst h
      rw [if_pos rfl, map_one]
      simp
    · rw [if_neg h, map_zero]
      exact bot_le
  | succ N ih =>
    intro m
    rw [coeff_omPartial_succ]
    refine Valuation.map_sub_le _ (ih m) ?_
    by_cases h : 1 ≤ m
    · rw [if_pos h, Valuation.map_mul, v_omX q θ hθ (N + 1)]
      have hm : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := Nat.cast_sub h
      calc Valued.v ((PowerSeries.coeff (m - 1)) (omPartial q θ N))
              * WithZero.exp (-(((q ^ (N + 1) : ℕ)) : ℤ))
          ≤ WithZero.exp (-(((m - 1 : ℕ)) : ℤ))
              * WithZero.exp (-(((q ^ (N + 1) : ℕ)) : ℤ)) :=
            mul_le_mul' (ih (m - 1)) le_rfl
        _ = WithZero.exp (-(((m - 1 : ℕ)) : ℤ) + -(((q ^ (N + 1) : ℕ)) : ℤ)) := by
            rw [← WithZero.exp_add]
        _ ≤ WithZero.exp (-(m : ℤ)) := by
            apply WithZero.exp_le_exp.mpr
            rw [hm]
            have h1 : 1 ≤ q ^ (N + 1) := Nat.one_le_pow (N + 1) q (by omega)
            have h1' : (1 : ℤ) ≤ ((q ^ (N + 1) : ℕ) : ℤ) := by exact_mod_cast h1
            omega
    · rw [if_neg h, map_zero]
      exact bot_le

lemma coeff_telescope_eq (q : ℕ) (θ : K) (N m : ℕ) :
    PowerSeries.coeff m (omPartial q θ (N + 1)) - PowerSeries.coeff m (omPartial q θ N)
      = -((if 1 ≤ m then PowerSeries.coeff (m - 1) (omPartial q θ N) * omX q θ (N + 1)
            else 0)) := by
  rw [coeff_omPartial_succ]
  ring

lemma v_coeff_telescope_le (q : ℕ) (θ : K) (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q)
    (m N : ℕ) (hm : 1 ≤ m) :
    Valued.v (PowerSeries.coeff m (omPartial q θ (N + 1)) - PowerSeries.coeff m (omPartial q θ N))
      ≤ WithZero.exp (-(((q ^ (N + 1) : ℕ)) : ℤ) + -(((m - 1 : ℕ)) : ℤ)) := by
  rw [coeff_telescope_eq, if_pos hm, Valuation.map_neg, Valuation.map_mul,
    v_omX q θ hθ (N + 1)]
  calc Valued.v ((PowerSeries.coeff (m - 1)) (omPartial q θ N))
          * WithZero.exp (-(((q ^ (N + 1) : ℕ)) : ℤ))
      ≤ WithZero.exp (-(((m - 1 : ℕ)) : ℤ))
          * WithZero.exp (-(((q ^ (N + 1) : ℕ)) : ℤ)) :=
        mul_le_mul' (v_coeff_omPartial_le q θ hθ hq N (m - 1)) le_rfl
    _ = WithZero.exp (-(((m - 1 : ℕ)) : ℤ) + -(((q ^ (N + 1) : ℕ)) : ℤ)) := by
        rw [← WithZero.exp_add]
    _ = WithZero.exp (-(((q ^ (N + 1) : ℕ)) : ℤ) + -(((m - 1 : ℕ)) : ℤ)) := by
        rw [add_comm]

section omegaCont

variable (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

lemma summable_telescope (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) (m : ℕ) :
    Summable (fun N : ℕ => PowerSeries.coeff m (omPartial q θ (N + 1))
      - PowerSeries.coeff m (omPartial q θ N)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine (summable_zero : Summable (fun _ : ℕ => (0 : K))).congr fun N => ?_
    simp [constantCoeff_omPartial]
  · refine Commons.Topology.Algebra.Valued.summable_of_tendsto_v_zero (fun n => ?_)
    rw [Filter.eventually_atTop]
    refine ⟨(n.natAbs + m + 1), fun N hN => ?_⟩
    refine lt_of_le_of_lt (v_coeff_telescope_le q θ hθ hq m N hm) ?_
    rw [WithZero.exp_lt_exp]
    have hN' : n.natAbs + m + 1 ≤ q ^ N := by
      have h1 : N < q ^ N := Nat.lt_pow_self (by omega : 1 < q)
      omega
    have hN'' : q ^ N ≤ q ^ (N + 1) := Nat.pow_le_pow_right (by omega : 1 ≤ q) (by omega)
    have hcast : ((n.natAbs + m + 1 : ℕ) : ℤ) ≤ ((q ^ (N + 1) : ℕ) : ℤ) := by
      exact_mod_cast le_trans hN' hN''
    have hn : (n : ℤ) ≤ (n.natAbs : ℤ) := Int.le_natAbs
    have hm1 : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := Nat.cast_sub hm
    rw [hm1]; omega

/-- The `m`-th coefficient of the Anderson–Thakur period function: the limit of the `m`-th
coefficients of the partial products, written as a telescoping series. -/
noncomputable def omCoeff (m : ℕ) : K :=
  (∑' N : ℕ, (PowerSeries.coeff m (omPartial q θ (N + 1))
      - PowerSeries.coeff m (omPartial q θ N)))
    + PowerSeries.coeff m (omPartial q θ 0)

/-- The Anderson–Thakur period function `Ω = ∏_{i ≥ 1} (1 - t/θ^{q^i})`. -/
noncomputable def atOmega : PowerSeries K := PowerSeries.mk (omCoeff q θ)

lemma coeff_atOmega (m : ℕ) :
    PowerSeries.coeff m (atOmega q θ) = omCoeff q θ m := PowerSeries.coeff_mk m _

lemma constantCoeff_atOmega :
    PowerSeries.constantCoeff (atOmega q θ) = 1 := by
  have h : PowerSeries.constantCoeff (atOmega q θ) = PowerSeries.coeff 0 (atOmega q θ) :=
    (congrFun PowerSeries.coeff_zero_eq_constantCoeff _).symm
  rw [h, coeff_atOmega, omCoeff]
  simp only [coeff_zero_omPartial, sub_self]
  simp

@[simp] lemma coeff_zero_atOmega :
    PowerSeries.coeff 0 (atOmega q θ) = 1 :=
  (congrFun PowerSeries.coeff_zero_eq_constantCoeff (atOmega q θ)).trans
    (constantCoeff_atOmega q θ)

/-- The coefficients of the partial products converge to the coefficients of `Ω`. -/
lemma tendsto_coeff_omPartial (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) (m : ℕ) :
    Tendsto (fun N => PowerSeries.coeff m (omPartial q θ N)) atTop (𝓝 (omCoeff q θ m)) := by
  have hs := (summable_telescope q θ hθ hq m).hasSum
  have h1 := hs.tendsto_sum_nat
  have h2 : ∀ N : ℕ, ∑ i ∈ Finset.range N,
        (PowerSeries.coeff m (omPartial q θ (i + 1)) - PowerSeries.coeff m (omPartial q θ i))
      = PowerSeries.coeff m (omPartial q θ N) - PowerSeries.coeff m (omPartial q θ 0) :=
    fun N => Finset.sum_range_sub (fun i => PowerSeries.coeff m (omPartial q θ i)) N
  have h3 : Tendsto (fun N => PowerSeries.coeff m (omPartial q θ N)
        - PowerSeries.coeff m (omPartial q θ 0)) atTop
      (𝓝 (∑' N : ℕ, (PowerSeries.coeff m (omPartial q θ (N + 1))
        - PowerSeries.coeff m (omPartial q θ N)))) :=
    Tendsto.congr' (Eventually.of_forall h2) h1
  have h4 := h3.add_const (PowerSeries.coeff m (omPartial q θ 0))
  have h5 : Tendsto (fun N => PowerSeries.coeff m (omPartial q θ N)) atTop
      (𝓝 ((∑' N : ℕ, (PowerSeries.coeff m (omPartial q θ (N + 1))
        - PowerSeries.coeff m (omPartial q θ N))) + PowerSeries.coeff m (omPartial q θ 0))) :=
    Tendsto.congr' (Eventually.of_forall (fun N => sub_add_cancel _ _)) h4
  exact h5

/-- The coefficients of the shifted partial products converge to those of `Ω`. -/
lemma tendsto_coeff_omPartial_succ (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) (m : ℕ) :
    Tendsto (fun N => PowerSeries.coeff m (omPartial q θ (N + 1))) atTop
      (𝓝 (PowerSeries.coeff m (atOmega q θ))) := by
  rw [coeff_atOmega]
  exact (tendsto_coeff_omPartial q θ hθ hq m).comp (tendsto_add_atTop_nat 1)

end omegaCont

section limit

variable (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- Coefficientwise convergence is preserved by multiplication on the right by a fixed
power series. -/
lemma tendsto_coeff_mul_right {P : ℕ → PowerSeries K} {g : PowerSeries K}
    (h : ∀ k : ℕ, Tendsto (fun N => PowerSeries.coeff k (P N)) atTop
      (𝓝 (PowerSeries.coeff k g))) (f : PowerSeries K) (m : ℕ) :
    Tendsto (fun N => PowerSeries.coeff m (P N * f)) atTop
      (𝓝 (PowerSeries.coeff m (g * f))) := by
  simp only [PowerSeries.coeff_mul]
  refine tendsto_finsetSum (Finset.antidiagonal m) (fun p hp => ?_)
  exact (h p.1).mul tendsto_const_nhds

/-- Coefficientwise convergence is preserved by the coefficientwise `q`-th power twist. -/
lemma tendsto_coeff_frobTwist [FrobPow K q] {P : ℕ → PowerSeries K} {g : PowerSeries K}
    (h : ∀ k : ℕ, Tendsto (fun N => PowerSeries.coeff k (P N)) atTop
      (𝓝 (PowerSeries.coeff k g))) (m : ℕ) :
    Tendsto (fun N => PowerSeries.coeff m (frobTwist (R := K) (p := q) 1 (P N))) atTop
      (𝓝 (PowerSeries.coeff m (frobTwist (R := K) (p := q) 1 g))) := by
  simp only [frobTwist_coeff, pow_one]
  exact (h m).pow q

/-- Coefficientwise convergence in the form of an `∀ m` statement. -/
lemma tendsto_coeff_all {P : ℕ → PowerSeries K} {g : PowerSeries K}
    (h : ∀ k : ℕ, Tendsto (fun N => PowerSeries.coeff k (P N)) atTop
      (𝓝 (PowerSeries.coeff k g))) :
    ∀ m : ℕ, Tendsto (fun N => PowerSeries.coeff m (P N)) atTop (𝓝 (PowerSeries.coeff m g)) := h

/-- If the coefficients of a sequence of power series converge to the coefficients of both
`g` and `g'`, then `g = g'`. -/
lemma powerSeries_eq_of_tendsto_coeff {P : ℕ → PowerSeries K} {g g' : PowerSeries K}
    (h : ∀ k : ℕ, Tendsto (fun N => PowerSeries.coeff k (P N)) atTop
      (𝓝 (PowerSeries.coeff k g)))
    (h' : ∀ k : ℕ, Tendsto (fun N => PowerSeries.coeff k (P N)) atTop
      (𝓝 (PowerSeries.coeff k g'))) : g = g' := by
  ext m
  exact tendsto_nhds_unique (h m) (h' m)

end limit

section twist

variable (q : ℕ) [FrobPow K q] (θ : K)

lemma frobTwist_zero_iter (f : PowerSeries K) : frobTwist (R := K) (p := q) 0 f = f := by
  ext k
  rw [frobTwist_coeff, pow_zero, pow_one]

lemma frobTwist_X :
    frobTwist (R := K) (p := q) 1 (PowerSeries.X : PowerSeries K) = PowerSeries.X := by
  ext k
  rw [frobTwist_coeff, PowerSeries.coeff_X]
  by_cases h : k = 1
  · subst h; simp
  · rw [if_neg h]
    exact zero_pow (M₀ := K) (pow_ne_zero 1 (FrobPow.ne_zero K (q := q)))

lemma frobTwist_one_sub_C_mul_X (c : K) :
    frobTwist (R := K) (p := q) 1 (1 - PowerSeries.C c * PowerSeries.X : PowerSeries K)
      = 1 - PowerSeries.C (c ^ q) * PowerSeries.X := by
  rw [frobTwist_sub, frobTwist_one, frobTwist_mul, frobTwist_C, frobTwist_X, pow_one]

lemma frobTwist_omPartial (N : ℕ) :
    frobTwist (R := K) (p := q) 1 (omPartial q θ N)
      = ∏ i ∈ Finset.range N, (1 - PowerSeries.C (omX q θ (i + 2)) * PowerSeries.X) := by
  rw [omPartial]
  change (frobTwistHom (R := K) (p := q) 1)
      (∏ i ∈ Finset.range N, (1 - PowerSeries.C (omX q θ (i + 1)) * PowerSeries.X))
    = ∏ i ∈ Finset.range N, (1 - PowerSeries.C (omX q θ (i + 2)) * PowerSeries.X)
  rw [map_prod]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  change frobTwist (R := K) (p := q) 1
      (1 - PowerSeries.C (omX q θ (i + 1)) * PowerSeries.X)
    = 1 - PowerSeries.C (omX q θ (i + 2)) * PowerSeries.X
  rw [frobTwist_one_sub_C_mul_X, omX_pow]

/-- The key partial-product identity: multiplying the twisted partial product by the missing
factor `1 - t/θ^q` gives the next partial product. -/
lemma omPartial_twist_succ (N : ℕ) :
    (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X) * frobTwist (R := K) (p := q) 1
        (omPartial q θ N)
      = omPartial q θ (N + 1) := by
  rw [frobTwist_omPartial, omPartial, Finset.prod_range_succ']
  ring

end twist

section main

variable (q : ℕ) [FrobPow K q] (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- **The functional equation of the Anderson–Thakur period function**:
`(1 - t/θ^q) · Ω^{(1)} = Ω`, where `Ω^{(1)}` is the coefficientwise `q`-th power (Frobenius)
twist of `Ω`. -/
theorem atOmega_twist (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
        * frobTwist (R := K) (p := q) 1 (atOmega q θ)
      = atOmega q θ := by
  have hlim1 : ∀ m : ℕ, Tendsto (fun N => PowerSeries.coeff m
        ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
          * frobTwist (R := K) (p := q) 1 (omPartial q θ N)))
      atTop (𝓝 (PowerSeries.coeff m ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
        * frobTwist (R := K) (p := q) 1 (atOmega q θ)))) := by
    intro m
    have h := tendsto_coeff_mul_right
      (fun k => tendsto_coeff_frobTwist (q := q) (g := atOmega q θ)
        (fun k => by rw [coeff_atOmega]; exact tendsto_coeff_omPartial q θ hθ hq k) k)
      (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X) m
    simpa only [mul_comm] using h
  have hlim2 : ∀ m : ℕ, Tendsto (fun N => PowerSeries.coeff m
        ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
          * frobTwist (R := K) (p := q) 1 (omPartial q θ N)))
      atTop (𝓝 (PowerSeries.coeff m (atOmega q θ))) := by
    intro m
    refine Tendsto.congr' (Eventually.of_forall (fun N => ?_))
      (tendsto_coeff_omPartial_succ q θ hθ hq m)
    simp only [omPartial_twist_succ]
  exact powerSeries_eq_of_tendsto_coeff hlim1 hlim2

/-- **The coefficient form of the functional equation**: the coefficients of `Ω` satisfy the
Frobenius recursion `b_m = b_m^q - x_1 b_{m-1}^q` (`x_1 = θ^{-q}`). -/
lemma coeff_atOmega_frobenius (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) (m : ℕ) :
    PowerSeries.coeff m (atOmega q θ)
      = (PowerSeries.coeff m (atOmega q θ)) ^ q
        - (if 1 ≤ m then (PowerSeries.coeff (m - 1) (atOmega q θ)) ^ q * omX q θ 1
            else 0) := by
  have h := congrArg (PowerSeries.coeff m) (atOmega_twist q θ hθ hq)
  have h2 : PowerSeries.coeff m ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
        * frobTwist (R := K) (p := q) 1 (atOmega q θ))
      = (PowerSeries.coeff m (atOmega q θ)) ^ q
        - (if 1 ≤ m then (PowerSeries.coeff (m - 1) (atOmega q θ)) ^ q * omX q θ 1
            else 0) := by
    rw [show (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
          * frobTwist (R := K) (p := q) 1 (atOmega q θ)
        = frobTwist (R := K) (p := q) 1 (atOmega q θ)
          * (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X) from by ring,
      coeff_mul_one_sub_C_mul_X, frobTwist_coeff, frobTwist_coeff, pow_one]
  rw [h2] at h
  exact h.symm

/-- **The general functional equation**: `Ω = (∏_{i=1}^{N}(1 - t/θ^{q^i})) · Ω^{(N)}`, where
`Ω^{(N)}` is the `N`-fold coefficientwise Frobenius twist of `Ω`. -/
theorem atOmega_eq_omPartial_mul_frobTwist (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q)
    (N : ℕ) :
    atOmega q θ = omPartial q θ N * frobTwist (R := K) (p := q) N (atOmega q θ) := by
  induction N with
  | zero => rw [omPartial_zero, frobTwist_zero_iter, one_mul]
  | succ N ih =>
    have h1 : frobTwist (R := K) (p := q) 1 (atOmega q θ)
        = frobTwist (R := K) (p := q) 1 (omPartial q θ N)
          * frobTwist (R := K) (p := q) (N + 1) (atOmega q θ) := by
      have h2 := congrArg (frobTwist (R := K) (p := q) 1) ih
      rw [frobTwist_mul, frobTwist_comp, Nat.one_add] at h2
      exact h2
    calc atOmega q θ
        = (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
            * frobTwist (R := K) (p := q) 1 (atOmega q θ) :=
          (atOmega_twist q θ hθ hq).symm
      _ = (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
            * (frobTwist (R := K) (p := q) 1 (omPartial q θ N)
              * frobTwist (R := K) (p := q) (N + 1) (atOmega q θ)) := by rw [h1]
      _ = ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
            * frobTwist (R := K) (p := q) 1 (omPartial q θ N))
            * frobTwist (R := K) (p := q) (N + 1) (atOmega q θ) := by ring
      _ = omPartial q θ (N + 1) * frobTwist (R := K) (p := q) (N + 1) (atOmega q θ) := by
          rw [omPartial_twist_succ]

/-- The sharper functional equation `(t - θ^q) · Ω^{(1)} = -θ^q · Ω`. -/
theorem atOmega_twist' (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    (PowerSeries.X - PowerSeries.C (θ ^ q)) * frobTwist (R := K) (p := q) 1 (atOmega q θ)
      = -PowerSeries.C (θ ^ q) * atOmega q θ := by
  have hθ0 : θ ≠ 0 := by
    intro h; rw [h, map_zero] at hθ
    exact absurd hθ.symm (WithZero.exp_ne_zero)
  have h1 : (PowerSeries.X - PowerSeries.C (θ ^ q) : PowerSeries K)
      = -PowerSeries.C (θ ^ q) * (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X) := by
    have hx : θ ^ (q ^ 1) * omX q θ 1 = 1 := by
      rw [omX]
      exact mul_inv_cancel₀ (pow_ne_zero _ hθ0)
    have h2 : (PowerSeries.C (θ ^ q) : PowerSeries K) * PowerSeries.C (omX q θ 1) = 1 := by
      rw [← map_mul]
      have h3 : θ ^ q * omX q θ 1 = 1 := by
        simpa only [pow_one] using hx
      rw [h3, map_one]
    calc (PowerSeries.X - PowerSeries.C (θ ^ q) : PowerSeries K)
        = -PowerSeries.C (θ ^ q)
            + (PowerSeries.C (θ ^ q) * PowerSeries.C (omX q θ 1)) * PowerSeries.X := by
          rw [h2]; ring
      _ = -PowerSeries.C (θ ^ q)
            * (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X) := by ring
  rw [h1, mul_assoc, atOmega_twist q θ hθ hq]

end main

section bounds

variable (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The coefficientwise bound `v (coeff m Ω) ≤ exp (-m)`. -/
lemma v_coeff_atOmega_le (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) (m : ℕ) :
    Valued.v (PowerSeries.coeff m (atOmega q θ)) ≤ WithZero.exp (-(m : ℤ)) := by
  rw [coeff_atOmega, omCoeff]
  refine Valuation.map_add_le _ ?_ (v_coeff_omPartial_le q θ hθ hq 0 m)
  refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le
    (summable_telescope q θ hθ hq m) (fun N => ?_)
  by_cases hm : 1 ≤ m
  · refine le_trans (v_coeff_telescope_le q θ hθ hq m N hm) ?_
    apply WithZero.exp_le_exp.mpr
    have h1 : 1 ≤ q ^ (N + 1) := Nat.one_le_pow (N + 1) q (by omega)
    have h1' : (1 : ℤ) ≤ ((q ^ (N + 1) : ℕ) : ℤ) := by exact_mod_cast h1
    have hm1 : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := Nat.cast_sub hm
    rw [hm1]; omega
  · have h0 : m = 0 := by omega
    subst h0
    have hz : PowerSeries.coeff 0 (omPartial q θ (N + 1))
        - PowerSeries.coeff 0 (omPartial q θ N) = 0 := by
      simp only [coeff_zero_omPartial, sub_self]
    rw [hz, map_zero]
    exact bot_le

lemma atOmega_bounded (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    SeriesBounded (atOmega q θ) :=
  ⟨0, fun m => le_trans (v_coeff_atOmega_le q θ hθ hq m)
    (WithZero.exp_le_exp.mpr (by omega))⟩

lemma atOmega_entire (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    Entire (atOmega q θ) := by
  refine Entire.of_nat (fun N => ?_)
  refine Filter.eventually_atTop.mpr ⟨N + 1, fun m hm => ?_⟩
  exact lt_of_le_of_lt (v_coeff_atOmega_le q θ hθ hq m)
    (WithZero.exp_lt_exp.mpr (by omega))

end bounds

section powers

variable (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

@[simp] lemma coeff_zero_pow_atOmega (s : ℕ) :
    PowerSeries.coeff 0 (atOmega q θ ^ s) = 1 := by
  rw [show PowerSeries.coeff 0 (atOmega q θ ^ s)
      = PowerSeries.constantCoeff (atOmega q θ ^ s) from
        congrFun PowerSeries.coeff_zero_eq_constantCoeff _, map_pow, constantCoeff_atOmega, one_pow]

/-- The sharp coefficient bound for the powers of `Ω`: `v (coeff n (Ω^s)) ≤ exp (-1)` for
`n ≥ 1`.  All the non-constant coefficients of a power of `Ω` lie in the maximal ideal of the
Tate algebra; this is the input to the convergence of Chang's `L`-series. -/
lemma v_coeff_pow_atOmega_le (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    ∀ (s n : ℕ), 1 ≤ n →
      Valued.v (PowerSeries.coeff n (atOmega q θ ^ s)) ≤ WithZero.exp (-1) := by
  intro s
  induction s with
  | zero =>
    intro n hn
    rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega : n ≠ 0), map_zero]
    exact bot_le
  | succ s ih =>
    intro n hn
    rw [pow_succ, PowerSeries.coeff_mul]
    refine Valued.v.map_sum_le (fun p hp => ?_)
    obtain ⟨a, b⟩ := p
    rw [Valuation.map_mul]
    have hp' : a + b = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rcases Nat.eq_zero_or_pos a with h1 | h1
    · subst h1
      have h2 : 1 ≤ b := by omega
      calc Valued.v (PowerSeries.coeff 0 (atOmega q θ ^ s))
              * Valued.v (PowerSeries.coeff b (atOmega q θ))
          ≤ 1 * WithZero.exp (-(((b : ℕ)) : ℤ)) := by
            rw [coeff_zero_pow_atOmega, map_one]
            exact mul_le_mul' le_rfl (v_coeff_atOmega_le q θ hθ hq b)
        _ ≤ WithZero.exp (-1) := by
            rw [one_mul]
            apply WithZero.exp_le_exp.mpr
            omega
    · rcases Nat.eq_zero_or_pos b with h2 | h2
      · subst h2
        have hb : a = n := by omega
        rw [hb]
        calc Valued.v (PowerSeries.coeff n (atOmega q θ ^ s))
                * Valued.v (PowerSeries.coeff 0 (atOmega q θ))
            ≤ WithZero.exp (-1) * 1 :=
              mul_le_mul' (ih n hn) (by rw [coeff_zero_atOmega, map_one])
          _ = WithZero.exp (-1) := mul_one _
      · calc Valued.v (PowerSeries.coeff a (atOmega q θ ^ s))
                * Valued.v (PowerSeries.coeff b (atOmega q θ))
            ≤ WithZero.exp (-1) * WithZero.exp (-1) :=
              mul_le_mul' (ih a h1)
                (le_trans (v_coeff_atOmega_le q θ hθ hq b)
                  (WithZero.exp_le_exp.mpr (by omega)))
          _ = WithZero.exp (-1 + -1) := by rw [← WithZero.exp_add]
          _ ≤ WithZero.exp (-1) := WithZero.exp_le_exp.mpr (by omega)

/-- The sharper coefficient bound for `Q * Ω^s` when all the coefficients of `Q` are bounded by
`exp M`: `v (coeff n (Q * Ω^s)) ≤ exp M` for `n ≥ 1`. -/
lemma v_coeff_mul_pow_atOmega_le (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q)
    (Q : PowerSeries K) (M : ℤ) (hQ : ∀ n : ℕ, Valued.v (PowerSeries.coeff n Q) ≤ WithZero.exp M)
    (s n : ℕ) (hn : 1 ≤ n) :
    Valued.v (PowerSeries.coeff n (Q * atOmega q θ ^ s)) ≤ WithZero.exp M := by
  rw [PowerSeries.coeff_mul]
  refine Valued.v.map_sum_le (fun p hp => ?_)
  obtain ⟨a, b⟩ := p
  rw [Valuation.map_mul]
  have hp' : a + b = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rcases Nat.eq_zero_or_pos a with h1 | h1
  · subst h1
    have h2 : 1 ≤ b := by omega
    calc Valued.v (PowerSeries.coeff 0 Q) * Valued.v (PowerSeries.coeff b (atOmega q θ ^ s))
        ≤ WithZero.exp M * WithZero.exp (-1) :=
          mul_le_mul' (hQ 0) (v_coeff_pow_atOmega_le q θ hθ hq s b h2)
      _ = WithZero.exp (M + -1) := by rw [← WithZero.exp_add]
      _ ≤ WithZero.exp M := WithZero.exp_le_exp.mpr (by omega)
  · rcases Nat.eq_zero_or_pos b with h2 | h2
    · subst h2
      rw [coeff_zero_pow_atOmega, map_one, mul_one]
      exact hQ a
    · calc Valued.v (PowerSeries.coeff a Q)
              * Valued.v (PowerSeries.coeff b (atOmega q θ ^ s))
          ≤ WithZero.exp M * WithZero.exp (-1) :=
            mul_le_mul' (hQ a) (v_coeff_pow_atOmega_le q θ hθ hq s b h2)
        _ = WithZero.exp (M + -1) := by rw [← WithZero.exp_add]
        _ ≤ WithZero.exp M := WithZero.exp_le_exp.mpr (by omega)

end powers

section powersTwist

variable (q : ℕ) [FrobPow K q] (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The Frobenius twist of `Q * Ω^s` stays bounded when `Q` is bounded (this is the shape of
the terms of Chang's `L`-series, and of the entries of the trivialisation `Ψ`). -/
lemma frobTwist_mul_pow_atOmega_bounded (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q)
    (Q : PowerSeries K) (hQ : SeriesBounded Q) (s i : ℕ) :
    SeriesBounded (frobTwist (R := K) (p := q) i (Q * atOmega q θ ^ s)) :=
  SeriesBounded.frobTwist (hQ.mul (SeriesBounded.pow (atOmega_bounded q θ hθ hq) s)) i

end powersTwist

section sanity

variable (q : ℕ) (θ : K)

/-- The coefficient of `t` in the partial product is the negative of the sum of the `x_i`. -/
lemma coeff_one_omPartial (N : ℕ) :
    PowerSeries.coeff 1 (omPartial q θ N) = -∑ i ∈ Finset.range N, omX q θ (i + 1) := by
  induction N with
  | zero => simp [omPartial_zero]
  | succ N ih =>
    rw [omPartial_succ, coeff_mul_one_sub_C_mul_X, ih, coeff_zero_omPartial,
      Finset.sum_range_succ]
    norm_num
    ring

end sanity

section sanityCont

variable (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

lemma summable_omX_succ (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    Summable (fun N : ℕ => omX q θ (N + 1)) := by
  refine Commons.Topology.Algebra.Valued.summable_of_tendsto_v_zero (fun n => ?_)
  rw [Filter.eventually_atTop]
  refine ⟨n.natAbs + 1, fun N hN => ?_⟩
  rw [v_omX q θ hθ (N + 1), WithZero.exp_lt_exp]
  have h1 : n.natAbs + 1 ≤ q ^ (N + 1) := by
    have h2 : N + 1 < q ^ (N + 1) := Nat.lt_pow_self (by omega : 1 < q)
    omega
  have hcast : ((n.natAbs + 1 : ℕ) : ℤ) ≤ ((q ^ (N + 1) : ℕ) : ℤ) := by exact_mod_cast h1
  have hn : (n : ℤ) ≤ (n.natAbs : ℤ) := Int.le_natAbs
  omega

/-- **The coefficient of `t` in `Ω`**: `-∑_{i ≥ 1} θ^{-q^i}`.  A sanity check of the
definition of `Ω` as the limit of the partial products. -/
lemma coeff_one_atOmega (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    PowerSeries.coeff 1 (atOmega q θ) = -∑' N : ℕ, omX q θ (N + 1) := by
  have hlim1 : Tendsto (fun N => PowerSeries.coeff 1 (omPartial q θ N)) atTop
      (𝓝 (-∑' N : ℕ, omX q θ (N + 1))) := by
    have h := (summable_omX_succ q θ hθ hq).hasSum.tendsto_sum_nat
    simpa only [coeff_one_omPartial] using h.neg
  have hlim2 : Tendsto (fun N => PowerSeries.coeff 1 (omPartial q θ N)) atTop
      (𝓝 (PowerSeries.coeff 1 (atOmega q θ))) := by
    rw [coeff_atOmega]
    exact tendsto_coeff_omPartial q θ hθ hq 1
  exact tendsto_nhds_unique hlim2 hlim1

end sanityCont

section unit

variable (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- `Ω` is a unit of the power series ring (its constant term is `1`). -/
lemma isUnit_atOmega : IsUnit (atOmega q θ) :=
  (Commons.RingTheory.PowerSeries.isUnit_iff_constantCoeff (atOmega q θ)).mpr
    (by rw [constantCoeff_atOmega]; exact isUnit_one)

end unit



section inverse

variable (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The coefficients of the inverse of `Ω` (whose constant term is `1`), defined by the
recursion `c_0 = 1`, `c_{m+1} = -∑_{k ≤ m} b_{k+1} c_{m-k}` where `b_j = coeff j Ω`, so that
`Ω * mk c = 1`. -/
noncomputable def omInvCoeff : ℕ → K
  | 0 => 1
  | (m + 1) => -∑ k ∈ Finset.range (m + 1),
      PowerSeries.coeff (k + 1) (atOmega q θ) * omInvCoeff (m - k)
termination_by n => n
decreasing_by omega

@[simp] lemma omInvCoeff_zero : omInvCoeff q θ 0 = 1 := by
  rw [omInvCoeff]

lemma omInvCoeff_succ (m : ℕ) : omInvCoeff q θ (m + 1) =
    -∑ k ∈ Finset.range (m + 1),
      PowerSeries.coeff (k + 1) (atOmega q θ) * omInvCoeff q θ (m - k) := by
  rw [omInvCoeff]

/-- The coefficients of the inverse of `Ω` are bounded: `v (c_m) ≤ 1`. -/
lemma v_omInvCoeff_le (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) (m : ℕ) :
    Valued.v (omInvCoeff q θ m) ≤ WithZero.exp 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => rw [omInvCoeff_zero, map_one, WithZero.exp_zero]
    | succ m' =>
      rw [omInvCoeff_succ, Valuation.map_neg]
      refine Valued.v.map_sum_le (fun k hk => ?_)
      rw [Valuation.map_mul]
      calc Valued.v (PowerSeries.coeff (k + 1) (atOmega q θ))
              * Valued.v (omInvCoeff q θ (m' - k))
          ≤ WithZero.exp (-(((k + 1 : ℕ)) : ℤ)) * WithZero.exp 0 :=
            mul_le_mul' (v_coeff_atOmega_le q θ hθ hq (k + 1)) (ih (m' - k) (by omega))
        _ = WithZero.exp (-(((k + 1 : ℕ)) : ℤ) + 0) := by rw [← WithZero.exp_add]
        _ ≤ WithZero.exp 0 := WithZero.exp_le_exp.mpr (by omega)

lemma omInvCoeff_bounded (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    SeriesBounded (PowerSeries.mk (omInvCoeff q θ)) :=
  ⟨0, fun m => by rw [PowerSeries.coeff_mk]; exact v_omInvCoeff_le q θ hθ hq m⟩

/-- The inverse of `Ω` is indeed the inverse: `Ω * mk (omInvCoeff) = 1`. -/
lemma antidiagonal_sum_eq (a b : ℕ → K) (m : ℕ) :
    (∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2)
      = ∑ k ∈ Finset.range (m + 1), a k * b (m - k) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma atOmega_mul_omInvCoeff :
    atOmega q θ * PowerSeries.mk (omInvCoeff q θ) = 1 := by
  ext m
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rw [antidiagonal_sum_eq (fun k => PowerSeries.coeff k (atOmega q θ)) (omInvCoeff q θ) m]
  cases m with
  | zero =>
    rw [Finset.sum_range_one, if_pos rfl, coeff_zero_atOmega, omInvCoeff_zero, mul_one]
  | succ m' =>
    rw [Finset.sum_range_succ', if_neg (by omega : ¬ (m' + 1 = 0))]
    simp only [coeff_zero_atOmega, one_mul, Nat.add_sub_add_right, Nat.sub_zero]
    rw [omInvCoeff_succ]
    ring

end inverse

section tateunit

variable (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- `Ω` as an element of the Tate algebra `T`. -/
noncomputable def atOmegaTate (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) : TateAlg K :=
  ⟨atOmega q θ, atOmega_bounded q θ hθ hq⟩

/-- The inverse of `Ω` as an element of the Tate algebra. -/
noncomputable def atOmegaInvTate (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) : TateAlg K :=
  ⟨PowerSeries.mk (omInvCoeff q θ), omInvCoeff_bounded q θ hθ hq⟩

/-- **`Ω` is a unit of the Tate algebra `T`**: `Ω ∈ T^×`. -/
theorem isUnit_atOmegaTate (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    IsUnit (atOmegaTate q θ hθ hq) := by
  refine ⟨⟨atOmegaTate q θ hθ hq, atOmegaInvTate q θ hθ hq, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (atOmega_mul_omInvCoeff q θ)
  · refine Subtype.ext ?_
    show (atOmegaInvTate q θ hθ hq : PowerSeries K) * (atOmegaTate q θ hθ hq : PowerSeries K) = 1
    rw [mul_comm]
    exact atOmega_mul_omInvCoeff q θ

end tateunit

end ZagierHoffmanPositiveChar
