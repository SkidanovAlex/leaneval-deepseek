import Submission.ZagierHoffmanProof.GenSpecialisation
import Submission.ZagierHoffmanProof.Omega
import Submission.Commons.RingTheory.PowerSeries.coeff_mul_X
import Submission.Commons.RingTheory.PowerSeries.isUnit_iff_constantCoeff

/-!
# The Anderson–Thakur period function `Ω` over an arbitrary value group

Generic version (arbitrary value group `Γ₀`, fixed small `γ`) of `Omega.lean`.  For a field `K`
with `[Valued K Γ₀]`, a "small" element `γ < 1` and `θ ∈ K` with `(v θ)⁻¹ ≤ γ`, the
Anderson–Thakur period function is the infinite product

  `Ω(t) = ∏_{i ≥ 1} (1 - t / θ^{q^i})`,

realised as the limit of its partial products `omPartial N = ∏_{i=1}^{N}(1 - x_i t)`
(`x_i = θ^{-q^i}`) via the telescoping series

  `omCoeffGen m = ∑' N, (coeff m (omPartial (N+1)) - coeff m (omPartial N)) + coeff m (omPartial 0)`.

The defining objects `omX`/`omPartial` are re-used from `Omega.lean` (they do not involve the
valuation); all the *analytic* statements are reproved here for an arbitrary value group.

## Main results

* `v_omX_gen`, `v_coeff_omPartial_le_gen` — the coefficient bounds.
* `summable_telescope_gen`, `tendsto_coeff_omPartial_gen`.
* `atOmegaGen_twist`, `atOmegaGen_eq_omPartial_mul_frobTwist` — the functional equation.
* `atOmegaGen_bounded`, `v_coeff_atOmegaGen_le`, `gSuperEntire_atOmegaGen` — `Ω ∈ T`, `Ω ∈ ε`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

section basic

variable (q : ℕ) (θ : K)

lemma omPartial_zero_gen : omPartial q θ 0 = 1 := by
  simp [omPartial]

lemma omPartial_succ_gen (N : ℕ) :
    omPartial q θ (N + 1)
      = omPartial q θ N * (1 - PowerSeries.C (omX q θ (N + 1)) * PowerSeries.X) := by
  simp only [omPartial, Finset.prod_range_succ]

lemma omX_pow_gen (i : ℕ) : (omX q θ i) ^ q = omX q θ (i + 1) := by
  rw [omX, omX, inv_pow, ← pow_mul, ← pow_succ]

lemma coeff_mul_one_sub_C_mul_X_gen {f : PowerSeries K} (c : K) (m : ℕ) :
    PowerSeries.coeff m (f * (1 - PowerSeries.C c * PowerSeries.X))
      = PowerSeries.coeff m f
        - (if 1 ≤ m then PowerSeries.coeff (m - 1) f * c else 0) := by
  rw [mul_sub, mul_one, ← mul_assoc, map_sub (PowerSeries.coeff m),
    Commons.RingTheory.PowerSeries.coeff_mul_X, PowerSeries.coeff_mul_C]

lemma coeff_omPartial_succ_gen (N m : ℕ) :
    PowerSeries.coeff m (omPartial q θ (N + 1))
      = PowerSeries.coeff m (omPartial q θ N)
        - (if 1 ≤ m then PowerSeries.coeff (m - 1) (omPartial q θ N) * omX q θ (N + 1)
            else 0) := by
  rw [omPartial_succ_gen]
  exact coeff_mul_one_sub_C_mul_X_gen (omX q θ (N + 1)) m

lemma constantCoeff_omPartial_gen (N : ℕ) :
    PowerSeries.constantCoeff (omPartial q θ N) = 1 := by
  rw [omPartial, map_prod]
  simp

lemma coeff_zero_omPartial_gen (N : ℕ) : PowerSeries.coeff 0 (omPartial q θ N) = 1 := by
  have h : PowerSeries.coeff 0 (omPartial q θ N)
      = PowerSeries.constantCoeff (omPartial q θ N) :=
    congrFun PowerSeries.coeff_zero_eq_constantCoeff _
  rw [h, constantCoeff_omPartial_gen]

end basic

section bounds

variable (q : ℕ) (θ : K)

/-- The valuation of `x_i = θ ^ (-q^i)`: `(v θ) ^ (-q^i)`. -/
lemma v_omX_gen (i : ℕ) :
    Valued.v (omX q θ i) = ((Valued.v θ)⁻¹) ^ (q ^ i) := by
  rw [omX, Valuation.map_inv, Valuation.map_pow, inv_pow]

/-- Every `x_i` with `i ≥ 1` is bounded by `γ`, provided `(v θ)⁻¹ ≤ γ ≤ 1`. -/
lemma v_omX_le {γ : Γ₀} (hq : 2 ≤ q) (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ ≤ 1)
    {i : ℕ} (hi : 1 ≤ i) :
    Valued.v (omX q θ i) ≤ γ := by
  rw [v_omX_gen]
  have h1 : (Valued.v θ)⁻¹ ≤ 1 := le_trans hγθ hγ1
  calc ((Valued.v θ)⁻¹) ^ (q ^ i) ≤ ((Valued.v θ)⁻¹) ^ 1 :=
        pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ _) h1 (Nat.one_le_pow i q (by omega))
    _ = (Valued.v θ)⁻¹ := pow_one _
    _ ≤ γ := hγθ

/-- The coefficient recursion for the telescoping differences of the partial products. -/
lemma coeff_telescope_eq_gen (N m : ℕ) :
    PowerSeries.coeff m (omPartial q θ (N + 1)) - PowerSeries.coeff m (omPartial q θ N)
      = -((if 1 ≤ m then PowerSeries.coeff (m - 1) (omPartial q θ N) * omX q θ (N + 1)
            else 0)) := by
  rw [coeff_omPartial_succ_gen]
  ring

/-- **The uniform coefficient bound** `v (coeff m (omPartial N)) ≤ γ ^ m`, valid for every `N`. -/
lemma v_coeff_omPartial_le_gen {γ : Γ₀} (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ ≤ 1)
    (hq : 2 ≤ q) :
    ∀ (N m : ℕ), Valued.v (PowerSeries.coeff m (omPartial q θ N)) ≤ γ ^ m := by
  intro N
  induction N with
  | zero =>
    intro m
    rw [omPartial_zero_gen, PowerSeries.coeff_one]
    by_cases h : m = 0
    · subst h
      rw [if_pos rfl, map_one]
      simp
    · rw [if_neg h, map_zero]
      exact (zero_le : (0 : Γ₀) ≤ _)
  | succ N ih =>
    intro m
    rw [coeff_omPartial_succ_gen]
    refine Valuation.map_sub_le _ (ih m) ?_
    by_cases h : 1 ≤ m
    · rw [if_pos h, Valuation.map_mul]
      calc Valued.v ((PowerSeries.coeff (m - 1)) (omPartial q θ N)) * Valued.v (omX q θ (N + 1))
          ≤ γ ^ (m - 1) * γ := mul_le_mul' (ih (m - 1)) (v_omX_le q θ hq hγθ hγ1 (by omega))
        _ = γ ^ m := by
            conv_rhs => rw [← Nat.sub_add_cancel h]
            rw [pow_add, pow_one]
    · rw [if_neg h, map_zero]
      exact (zero_le : (0 : Γ₀) ≤ _)

/-- The telescope increment is bounded by `γ ^ (m-1) · (v θ) ^ (-q^(N+1))`. -/
lemma v_coeff_telescope_le_gen {γ : Γ₀} (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ ≤ 1)
    (hq : 2 ≤ q) (m N : ℕ) (hm : 1 ≤ m) :
    Valued.v (PowerSeries.coeff m (omPartial q θ (N + 1)) - PowerSeries.coeff m (omPartial q θ N))
      ≤ γ ^ (m - 1) * ((Valued.v θ)⁻¹) ^ (q ^ (N + 1)) := by
  rw [coeff_telescope_eq_gen, if_pos hm, Valuation.map_neg, Valuation.map_mul, v_omX_gen]
  exact mul_le_mul' (v_coeff_omPartial_le_gen q θ hγθ hγ1 hq N (m - 1)) le_rfl

end bounds

section omegaCont

variable (q : ℕ) (θ : K) {γ : Γ₀} [CompleteSpace K] [NonarchimedeanAddGroup K]

lemma summable_telescope_gen (hγ0 : 0 < γ) (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) (m : ℕ) :
    Summable (fun N : ℕ => PowerSeries.coeff m (omPartial q θ (N + 1))
      - PowerSeries.coeff m (omPartial q θ N)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine (summable_zero : Summable (fun _ : ℕ => (0 : K))).congr fun N => ?_
    simp [constantCoeff_omPartial_gen]
  · refine summable_of_v_le_mul_gamma_pow (q := q) (N := 1) hγ1 harch hq
      (C := γ ^ (m - 1)) (f := fun N : ℕ => PowerSeries.coeff m (omPartial q θ (N + 1))
        - PowerSeries.coeff m (omPartial q θ N)) (fun N => ?_)
    have := mul_le_mul_right (pow_le_pow_left' hγθ (q ^ (N + 1))) (γ ^ (m - 1))
    refine le_trans (v_coeff_telescope_le_gen q θ hγθ hγ1.le hq m N hm) ?_
    simpa [Nat.add_comm] using this

/-- The `m`-th coefficient of the Anderson–Thakur period function: the limit of the `m`-th
coefficients of the partial products, written as a telescoping series. -/
noncomputable def omCoeffGen (m : ℕ) : K :=
  (∑' N : ℕ, (PowerSeries.coeff m (omPartial q θ (N + 1))
      - PowerSeries.coeff m (omPartial q θ N)))
    + PowerSeries.coeff m (omPartial q θ 0)

/-- The Anderson–Thakur period function `Ω = ∏_{i ≥ 1} (1 - t/θ^{q^i})` (generic value group). -/
noncomputable def atOmegaGen : PowerSeries K := PowerSeries.mk (omCoeffGen q θ)

lemma coeff_atOmegaGen (m : ℕ) :
    PowerSeries.coeff m (atOmegaGen q θ) = omCoeffGen q θ m := PowerSeries.coeff_mk m _

lemma constantCoeff_atOmegaGen :
    PowerSeries.constantCoeff (atOmegaGen q θ) = 1 := by
  have h : PowerSeries.constantCoeff (atOmegaGen q θ) = PowerSeries.coeff 0 (atOmegaGen q θ) :=
    (congrFun PowerSeries.coeff_zero_eq_constantCoeff _).symm
  rw [h, coeff_atOmegaGen, omCoeffGen]
  simp only [coeff_zero_omPartial_gen, sub_self]
  simp

@[simp] lemma coeff_zero_atOmegaGen :
    PowerSeries.coeff 0 (atOmegaGen q θ) = 1 :=
  (congrFun PowerSeries.coeff_zero_eq_constantCoeff (atOmegaGen q θ)).trans
    (constantCoeff_atOmegaGen q θ)

/-- The coefficients of the partial products converge to the coefficients of `Ω`. -/
lemma tendsto_coeff_omPartial_gen (hγ0 : 0 < γ) (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) (m : ℕ) :
    Tendsto (fun N => PowerSeries.coeff m (omPartial q θ N)) atTop (𝓝 (omCoeffGen q θ m)) := by
  have hs := (summable_telescope_gen q θ hγ0 hγθ hγ1 harch hq m).hasSum
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
lemma tendsto_coeff_omPartial_succ_gen (hγ0 : 0 < γ) (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) (m : ℕ) :
    Tendsto (fun N => PowerSeries.coeff m (omPartial q θ (N + 1))) atTop
      (𝓝 (PowerSeries.coeff m (atOmegaGen q θ))) := by
  rw [coeff_atOmegaGen]
  exact (tendsto_coeff_omPartial_gen q θ hγ0 hγθ hγ1 harch hq m).comp
    (tendsto_add_atTop_nat 1)

end omegaCont

section limit

variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- Coefficientwise convergence is preserved by multiplication on the right by a fixed
power series. -/
lemma tendsto_coeff_mul_right_gen {P : ℕ → PowerSeries K} {g : PowerSeries K}
    (h : ∀ k : ℕ, Tendsto (fun N => PowerSeries.coeff k (P N)) atTop
      (𝓝 (PowerSeries.coeff k g))) (f : PowerSeries K) (m : ℕ) :
    Tendsto (fun N => PowerSeries.coeff m (P N * f)) atTop
      (𝓝 (PowerSeries.coeff m (g * f))) := by
  simp only [PowerSeries.coeff_mul]
  refine tendsto_finsetSum (Finset.antidiagonal m) (fun p hp => ?_)
  exact (h p.1).mul tendsto_const_nhds

/-- Coefficientwise convergence is preserved by the coefficientwise `q`-th power twist. -/
lemma tendsto_coeff_frobTwist_gen (q : ℕ) [FrobPow K q] {P : ℕ → PowerSeries K}
    {g : PowerSeries K}
    (h : ∀ k : ℕ, Tendsto (fun N => PowerSeries.coeff k (P N)) atTop
      (𝓝 (PowerSeries.coeff k g))) (m : ℕ) :
    Tendsto (fun N => PowerSeries.coeff m (frobTwist (R := K) (p := q) 1 (P N))) atTop
      (𝓝 (PowerSeries.coeff m (frobTwist (R := K) (p := q) 1 g))) := by
  simp only [frobTwist_coeff, pow_one]
  exact (h m).pow q

/-- If the coefficients of a sequence of power series converge to the coefficients of both
`g` and `g'`, then `g = g'`. -/
lemma powerSeries_eq_of_tendsto_coeff_gen {P : ℕ → PowerSeries K} {g g' : PowerSeries K}
    (h : ∀ k : ℕ, Tendsto (fun N => PowerSeries.coeff k (P N)) atTop
      (𝓝 (PowerSeries.coeff k g)))
    (h' : ∀ k : ℕ, Tendsto (fun N => PowerSeries.coeff k (P N)) atTop
      (𝓝 (PowerSeries.coeff k g'))) : g = g' := by
  ext m
  exact tendsto_nhds_unique (h m) (h' m)

end limit

section twist

variable (q : ℕ) [FrobPow K q] (θ : K)

lemma frobTwist_zero_iter_gen (f : PowerSeries K) :
    frobTwist (R := K) (p := q) 0 f = f := by
  ext k
  rw [frobTwist_coeff, pow_zero, pow_one]

lemma frobTwist_X_gen :
    frobTwist (R := K) (p := q) 1 (PowerSeries.X : PowerSeries K) = PowerSeries.X := by
  ext k
  rw [frobTwist_coeff, PowerSeries.coeff_X]
  by_cases h : k = 1
  · subst h; simp
  · rw [if_neg h]
    exact zero_pow (pow_ne_zero 1 (FrobPow.ne_zero K (q := q)))

lemma frobTwist_one_sub_C_mul_X_gen (c : K) :
    frobTwist (R := K) (p := q) 1 (1 - PowerSeries.C c * PowerSeries.X : PowerSeries K)
      = 1 - PowerSeries.C (c ^ q) * PowerSeries.X := by
  rw [frobTwist_sub, frobTwist_one, frobTwist_mul, frobTwist_C, frobTwist_X_gen, pow_one]

lemma frobTwist_omPartial_gen (N : ℕ) :
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
  rw [frobTwist_one_sub_C_mul_X_gen, omX_pow_gen]

/-- The key partial-product identity: multiplying the twisted partial product by the missing
factor `1 - t/θ^q` gives the next partial product. -/
lemma omPartial_twist_succ_gen (N : ℕ) :
    (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
        * frobTwist (R := K) (p := q) 1 (omPartial q θ N)
      = omPartial q θ (N + 1) := by
  rw [frobTwist_omPartial_gen, omPartial, Finset.prod_range_succ']
  ring

end twist

section main

variable (q : ℕ) [FrobPow K q] (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- **The functional equation of the Anderson–Thakur period function** (generic value group):
`(1 - t/θ^q) · Ω^{(1)} = Ω`. -/
theorem atOmegaGen_twist {γ : Γ₀} (hγ0 : 0 < γ) (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) :
    (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
        * frobTwist (R := K) (p := q) 1 (atOmegaGen q θ)
      = atOmegaGen q θ := by
  have hlim1 : ∀ m : ℕ, Tendsto (fun N => PowerSeries.coeff m
        ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
          * frobTwist (R := K) (p := q) 1 (omPartial q θ N)))
      atTop (𝓝 (PowerSeries.coeff m ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
        * frobTwist (R := K) (p := q) 1 (atOmegaGen q θ)))) := by
    intro m
    have hbase : ∀ k : ℕ, Tendsto (fun N => PowerSeries.coeff k (omPartial q θ N)) atTop
        (𝓝 (PowerSeries.coeff k (atOmegaGen q θ))) := by
      intro k
      rw [coeff_atOmegaGen]
      exact tendsto_coeff_omPartial_gen q θ hγ0 hγθ hγ1 harch hq k
    have h := tendsto_coeff_mul_right_gen (K := K)
      (fun k => tendsto_coeff_frobTwist_gen (K := K) q (g := atOmegaGen q θ) hbase k)
      (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X) m
    simpa only [mul_comm] using h
  have hlim2 : ∀ m : ℕ, Tendsto (fun N => PowerSeries.coeff m
        ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
          * frobTwist (R := K) (p := q) 1 (omPartial q θ N)))
      atTop (𝓝 (PowerSeries.coeff m (atOmegaGen q θ))) := by
    intro m
    refine Tendsto.congr' (Eventually.of_forall (fun N => ?_))
      (tendsto_coeff_omPartial_succ_gen q θ hγ0 hγθ hγ1 harch hq m)
    simp only [omPartial_twist_succ_gen]
  exact powerSeries_eq_of_tendsto_coeff_gen (K := K) hlim1 hlim2

/-- **The general functional equation**: `Ω = (∏_{i=1}^{N}(1 - t/θ^{q^i})) · Ω^{(N)}`. -/
theorem atOmegaGen_eq_omPartial_mul_frobTwist {γ : Γ₀} (hγ0 : 0 < γ)
    (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    (N : ℕ) :
    atOmegaGen q θ = omPartial q θ N * frobTwist (R := K) (p := q) N (atOmegaGen q θ) := by
  have htw := atOmegaGen_twist q θ hγ0 hγθ hγ1 harch hq
  induction N with
  | zero => rw [omPartial_zero_gen, frobTwist_zero_iter_gen, one_mul]
  | succ N ih =>
    have h1 : frobTwist (R := K) (p := q) 1 (atOmegaGen q θ)
        = frobTwist (R := K) (p := q) 1 (omPartial q θ N)
          * frobTwist (R := K) (p := q) (N + 1) (atOmegaGen q θ) := by
      have h2 := congrArg (frobTwist (R := K) (p := q) 1) ih
      rw [frobTwist_mul, frobTwist_comp, Nat.one_add] at h2
      exact h2
    calc atOmegaGen q θ
        = (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
            * frobTwist (R := K) (p := q) 1 (atOmegaGen q θ) := htw.symm
      _ = (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
            * (frobTwist (R := K) (p := q) 1 (omPartial q θ N)
              * frobTwist (R := K) (p := q) (N + 1) (atOmegaGen q θ)) := by rw [h1]
      _ = ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
            * frobTwist (R := K) (p := q) 1 (omPartial q θ N))
            * frobTwist (R := K) (p := q) (N + 1) (atOmegaGen q θ) := by ring
      _ = omPartial q θ (N + 1) * frobTwist (R := K) (p := q) (N + 1) (atOmegaGen q θ) := by
          rw [omPartial_twist_succ_gen]

/-- The sharper functional equation `(t - θ^q) · Ω^{(1)} = -θ^q · Ω`. -/
theorem atOmegaGen_twist' {γ : Γ₀} (hθ0 : θ ≠ 0) (hγ0 : 0 < γ)
    (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) :
    (PowerSeries.X - PowerSeries.C (θ ^ q)) * frobTwist (R := K) (p := q) 1 (atOmegaGen q θ)
      = -PowerSeries.C (θ ^ q) * atOmegaGen q θ := by
  have h1 : (PowerSeries.X - PowerSeries.C (θ ^ q) : PowerSeries K)
      = -PowerSeries.C (θ ^ q) * (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X) := by
    have hx : θ ^ (q ^ 1) * omX q θ 1 = 1 := by
      rw [omX]; exact mul_inv_cancel₀ (pow_ne_zero _ hθ0)
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
  rw [h1, mul_assoc, atOmegaGen_twist q θ hγ0 hγθ hγ1 harch hq]

end main

section boundOmega

variable (q : ℕ) (θ : K) {γ : Γ₀} [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The coefficientwise bound `v (coeff m Ω) ≤ γ ^ m`. -/
lemma v_coeff_atOmegaGen_le (hγ0 : 0 < γ) (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) (m : ℕ) :
    Valued.v (PowerSeries.coeff m (atOmegaGen q θ)) ≤ γ ^ m := by
  rw [coeff_atOmegaGen, omCoeffGen]
  refine Valuation.map_add_le _ ?_ (v_coeff_omPartial_le_gen q θ hγθ hγ1.le hq 0 m)
  refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le_general
    (summable_telescope_gen q θ hγ0 hγθ hγ1 harch hq m) (fun N => ?_)
  by_cases hm : 1 ≤ m
  · refine le_trans (v_coeff_telescope_le_gen q θ hγθ hγ1.le hq m N hm) ?_
    refine le_trans (mul_le_mul_right (pow_le_pow_left' hγθ (q ^ (N + 1))) (γ ^ (m - 1))) ?_
    rw [← pow_add]
    refine pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ1.le ?_
    have : 1 ≤ q ^ (N + 1) := Nat.one_le_pow (N + 1) q (by omega)
    omega
  · have h0 : m = 0 := by omega
    subst h0
    have hz : PowerSeries.coeff 0 (omPartial q θ (N + 1))
        - PowerSeries.coeff 0 (omPartial q θ N) = 0 := by
      simp only [coeff_zero_omPartial_gen, sub_self]
    rw [hz, map_zero]
    exact (zero_le : (0 : Γ₀) ≤ _)

/-- The period function is a Tate series (bounded coefficients). -/
theorem atOmegaGen_bounded (hγ0 : 0 < γ) (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) : GBounded (atOmegaGen q θ) :=
  ⟨1, fun m => le_trans (v_coeff_atOmegaGen_le q θ hγ0 hγθ hγ1 harch hq m)
    (pow_le_one₀ hγ0.le hγ1.le)⟩

/-- The period function is entire (coefficients tending to `0`). -/
theorem atOmegaGen_entire (hγ0 : 0 < γ) (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) : GEntire (atOmegaGen q θ) := by
  intro u hu
  obtain ⟨n, hn⟩ := harch γ hγ1 u hu
  refine Filter.eventually_atTop.mpr ⟨n, fun m hm => ?_⟩
  exact lt_of_le_of_lt (le_trans (v_coeff_atOmegaGen_le q θ hγ0 hγθ hγ1 harch hq m)
    (pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ1.le hm)) hn

end boundOmega

section superEntire

variable (q : ℕ) (θ : K)

/-- The exponent `q + q² + ⋯ + q^m` of the sharp bound for the coefficients of the partial
products of `Ω`. -/
def sharpExpGen (q m : ℕ) : ℕ := ∑ i ∈ Finset.range m, q ^ (i + 1)

lemma sharpExpGen_zero (q : ℕ) : sharpExpGen q 0 = 0 := by
  simp [sharpExpGen]

lemma sharpExpGen_succ (q m : ℕ) :
    sharpExpGen q (m + 1) = sharpExpGen q m + q ^ (m + 1) := by
  rw [sharpExpGen, Finset.sum_range_succ, sharpExpGen]

/-- The partial product `omPartial q θ N` has degree at most `N`. -/
lemma coeff_omPartial_eq_zero_of_lt_gen (N m : ℕ) (h : N < m) :
    PowerSeries.coeff m (omPartial q θ N) = 0 := by
  induction N generalizing m with
  | zero =>
    rw [omPartial_zero_gen, PowerSeries.coeff_one, if_neg (by omega)]
  | succ N ih =>
    rw [coeff_omPartial_succ_gen]
    have h1 : PowerSeries.coeff m (omPartial q θ N) = 0 := ih m (by omega)
    have h2 : PowerSeries.coeff (m - 1) (omPartial q θ N) = 0 := ih (m - 1) (by omega)
    rw [h1]
    by_cases hm : 1 ≤ m
    · rw [if_pos hm, h2, zero_mul, sub_zero]
    · rw [if_neg hm, sub_zero]

/-- Squares grow slower than powers of two. -/
lemma sq_le_two_pow_gen : ∀ m : ℕ, 4 ≤ m → m ^ 2 ≤ 2 ^ m := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 4 with h | h
    · have hm3 : m = 3 := by omega
      rw [hm3]; norm_num
    · have hm4 : 4 ≤ m := h
      have h1 : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
      have h2 : 2 * m + 1 ≤ m ^ 2 := by nlinarith
      have h3 : m ^ 2 ≤ 2 ^ m := ih hm4
      calc (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := h1
        _ ≤ m ^ 2 + m ^ 2 := Nat.add_le_add_left h2 _
        _ = 2 * m ^ 2 := by ring
        _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 h3
        _ = 2 ^ (m + 1) := by ring

lemma mul_le_two_pow_gen (M m : ℕ) (h : max M 4 ≤ m) : M * m ≤ 2 ^ m := by
  have h4 : 4 ≤ m := le_trans (le_max_right _ _) h
  have hM : M ≤ m := le_trans (le_max_left _ _) h
  calc M * m ≤ m * m := Nat.mul_le_mul_right m hM
    _ = m ^ 2 := (pow_two m).symm
    _ ≤ 2 ^ m := sq_le_two_pow_gen m h4

/-- **The sharp coefficient bound for the partial products of `Ω`**: the dominant term is the
elementary symmetric function `x_1⋯x_m` of `x_i = θ^{-q^i}`, so with `δ = (v θ)⁻¹`,

  `v (coeff m (omPartial q θ N)) ≤ δ ^ (q + q² + ⋯ + q^m)`. -/
lemma v_coeff_omPartial_le_sharp_gen {γ : Γ₀} (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ ≤ 1)
    (hq : 2 ≤ q) :
    ∀ (N m : ℕ), Valued.v (PowerSeries.coeff m (omPartial q θ N))
      ≤ ((Valued.v θ)⁻¹) ^ (sharpExpGen q m) := by
  intro N
  induction N with
  | zero =>
    intro m
    rw [omPartial_zero_gen, PowerSeries.coeff_one]
    by_cases h : m = 0
    · subst h
      rw [if_pos rfl, map_one, sharpExpGen_zero, pow_zero]
    · rw [if_neg h, map_zero]
      exact (zero_le : (0 : Γ₀) ≤ _)
  | succ N ih =>
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [coeff_omPartial_succ_gen, if_neg (by omega : ¬ (1 ≤ 0)), sub_zero]
      exact ih 0
    · have hm1 : 1 ≤ m := hm
      by_cases hcase : m ≤ N + 1
      · rw [coeff_omPartial_succ_gen]
        refine Valuation.map_sub_le _ (ih m) ?_
        rw [if_pos hm1, Valuation.map_mul, v_omX_gen]
        calc Valued.v (PowerSeries.coeff (m - 1) (omPartial q θ N))
                * ((Valued.v θ)⁻¹) ^ (q ^ (N + 1))
            ≤ ((Valued.v θ)⁻¹) ^ (sharpExpGen q (m - 1))
                * ((Valued.v θ)⁻¹) ^ (q ^ (N + 1)) := mul_le_mul' (ih (m - 1)) le_rfl
          _ = ((Valued.v θ)⁻¹) ^ (sharpExpGen q (m - 1) + q ^ (N + 1)) := by rw [← pow_add]
          _ ≤ ((Valued.v θ)⁻¹) ^ (sharpExpGen q m) := by
              refine pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ _)
                (le_trans hγθ hγ1) ?_
              have hsp : sharpExpGen q m = sharpExpGen q (m - 1) + q ^ m := by
                conv_lhs => rw [← Nat.sub_add_cancel hm1]
                rw [sharpExpGen_succ, Nat.sub_add_cancel hm1]
              rw [hsp]
              exact Nat.add_le_add_left (Nat.pow_le_pow_right (by omega) hcase) _
      · rw [coeff_omPartial_eq_zero_of_lt_gen q θ (N + 1) m (by omega), map_zero]
        exact (zero_le : (0 : Γ₀) ≤ _)

/-- **The sharp coefficient bound for `Ω`**: `v (coeff m Ω) ≤ δ ^ (q + ⋯ + q^m)`. -/
lemma v_coeff_atOmegaGen_le_sharp_gen {γ : Γ₀} (hγ0 : 0 < γ)
    (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    [CompleteSpace K] [NonarchimedeanAddGroup K] (m : ℕ) :
    Valued.v (PowerSeries.coeff m (atOmegaGen q θ))
      ≤ ((Valued.v θ)⁻¹) ^ (sharpExpGen q m) := by
  rw [coeff_atOmegaGen, omCoeffGen]
  refine Valuation.map_add_le _ ?_ (v_coeff_omPartial_le_sharp_gen q θ hγθ hγ1.le hq 0 m)
  refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le_general
    (summable_telescope_gen q θ hγ0 hγθ hγ1 harch hq m) (fun N => ?_)
  exact Valuation.map_sub_le _
    (v_coeff_omPartial_le_sharp_gen q θ hγθ hγ1.le hq (N + 1) m)
    (v_coeff_omPartial_le_sharp_gen q θ hγθ hγ1.le hq N m)

/-- **The Anderson–Thakur period function is super-entire**: `Ω ∈ ε`. -/
theorem gSuperEntire_atOmegaGen {γ : Γ₀} (hγ0 : 0 < γ) (hγθ : (Valued.v θ)⁻¹ ≤ γ)
    (hγ1 : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    [CompleteSpace K] [NonarchimedeanAddGroup K] :
    GSuperEntire γ (atOmegaGen q θ) := by
  intro M
  refine ⟨(γ ^ (M * max M 4))⁻¹, fun m => ?_⟩
  refine le_trans (v_coeff_atOmegaGen_le_sharp_gen q θ hγ0 hγθ hγ1 harch hq m) ?_
  have hδ1 : (Valued.v θ)⁻¹ ≤ 1 := le_trans hγθ hγ1.le
  rcases le_or_gt m (max M 4) with h | h
  · have h1 : γ ^ (M * max M 4) ≤ γ ^ (M * m) :=
      pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ1.le (Nat.mul_le_mul_left M h)
    have h2 : (γ ^ (M * max M 4))⁻¹ * γ ^ (M * max M 4) = 1 :=
      inv_mul_cancel₀ (pow_ne_zero _ hγ0.ne')
    have h3 : 1 ≤ (γ ^ (M * max M 4))⁻¹ * γ ^ (M * m) := by
      rw [← h2]
      exact mul_le_mul_right h1 _
    refine le_trans (pow_le_one₀ (zero_le : (0 : Γ₀) ≤ _) hδ1) h3
  · have h1 : ((Valued.v θ)⁻¹) ^ (sharpExpGen q m) ≤ γ ^ (sharpExpGen q m) :=
      pow_le_pow_left' hγθ _
    refine le_trans h1 ?_
    have h2 : sharpExpGen q m + M * max M 4 ≥ M * m := by
      have h3 : M * m ≤ 2 ^ m := mul_le_two_pow_gen M m (le_of_lt h)
      have h4 : 2 ^ m ≤ q ^ m := Nat.pow_le_pow_left hq m
      have h5 : q ^ m ≤ sharpExpGen q m := by
        have hm1 : 1 ≤ m := by omega
        conv_rhs => rw [← Nat.sub_add_cancel hm1]
        rw [sharpExpGen_succ, Nat.sub_add_cancel hm1]
        exact Nat.le_add_left _ _
      omega
    have h6 : γ ^ (sharpExpGen q m + M * max M 4) ≤ γ ^ (M * m) :=
      pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ1.le h2
    have h9 : γ ^ (sharpExpGen q m) * γ ^ (M * max M 4) ≤ γ ^ (M * m) := by
      rw [← pow_add]; exact h6
    have heq : (γ ^ (M * max M 4))⁻¹ * (γ ^ (sharpExpGen q m) * γ ^ (M * max M 4))
        = γ ^ (sharpExpGen q m) := by
      rw [mul_comm (γ ^ (sharpExpGen q m)), ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ hγ0.ne'), one_mul]
    have hh := mul_le_mul_right h9 ((γ ^ (M * max M 4))⁻¹)
    rwa [heq] at hh

end superEntire

end ZagierHoffmanPositiveChar
