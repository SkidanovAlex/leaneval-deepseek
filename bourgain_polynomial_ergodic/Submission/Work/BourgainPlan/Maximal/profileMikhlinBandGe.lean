import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.contDiff_polyProfile

/-!
# The Mikhlin band bound for the polynomial profile, with a general band constant

For `P ∈ ℤ[X]`, `N ≥ 1`, the oscillatory profile is
`Φ_N(β) = ∫₀¹ e(β P(N s)) ds`, and we prove the *band* estimate

  `N^{deg P} · |β| ≤ c  ⟹  |β|^k · ‖Φ_N^{(k)}(β)‖ ≤ C(P, k, c)`

with a constant `C` **independent of `N`**.  This is the elementary "trivial bound" on the band:
`Φ_N` is the characteristic function of the pushforward of Lebesgue measure on `(0,1]` under the
real phase `s ↦ 2π P(N s)`, so Mathlib's `iteratedDeriv_charFun` gives

  `Φ_N^{(k)}(β) = I^k ∫ x^k e^{β x I} dν_N`  with `ν_N` the pushforward measure,

and on the band `|x| ≤ 2π A N^{deg P}` with `A = Σ_i |p_i|`, so

  `|β|^k ‖Φ_N^{(k)}(β)‖ ≤ (2π A |β| N^{deg P})^k ≤ (2π A c)^k`.

The constant produced is `max 1 ((2π · (Σ_i |p_i|) · max c 0)^k)` (the `max c 0` only matters for
`c ≤ 0`, where the band hypothesis is empty in any case).

This is the brick used in MST §4's band-localised Mikhlin discharge; cf.
`WINDOW_WEAK_TYPE_STATUS_S8.md` §1 and §3.
-/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace Work.BourgainPlan.Maximal

noncomputable section

/-- The `ℓ¹`-norm of the coefficients of `P` read in `ℝ`.  (Summed over `range (natDegree + 1)`;
this is `≥` the sum over the support, and both bound `|P|` on `[-N,N]` by `A·N^{deg P}`.) -/
private noncomputable def polyCoeffAbsSum (P : Polynomial ℤ) : ℝ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), |((P.coeff i : ℤ) : ℝ)|

/-- The real phase `s ↦ 2π P(N s)` of the profile; the profile is the characteristic function of
its pushforward measure. -/
private noncomputable def profilePhase (P : Polynomial ℤ) (N : ℕ) : ℝ → ℝ :=
  fun s => 2 * Real.pi * (toRealPoly P).eval ((N : ℝ) * s)

/-- The pushforward of Lebesgue measure on `(0,1]` under the phase `s ↦ 2π P(N s)`. -/
private noncomputable def profileMeasure (P : Polynomial ℤ) (N : ℕ) : Measure ℝ :=
  Measure.map (profilePhase P N) (volume.restrict (Set.Ioc (0 : ℝ) 1))

private lemma continuous_profilePhase (P : Polynomial ℤ) (N : ℕ) :
    Continuous (profilePhase P N) := by
  unfold profilePhase
  fun_prop

private instance instFiniteRestrictIoc : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioc, sub_zero]
        exact ENNReal.ofReal_one ▸ ENNReal.one_ne_top)

private instance instFiniteProfileMeasure (P : Polynomial ℤ) (N : ℕ) :
    IsFiniteMeasure (profileMeasure P N) := by
  unfold profileMeasure
  infer_instance

/-- A polynomial of degree `d` is bounded by `(Σ_i |p_i|)·N^d` on `[-N,N]`. -/
private lemma abs_eval_toRealPoly_le (P : Polynomial ℤ) (N : ℕ) (hN : 1 ≤ N)
    (x : ℝ) (hx : |x| ≤ N) :
    |(toRealPoly P).eval x| ≤ polyCoeffAbsSum P * (N : ℝ) ^ P.natDegree := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hkey : |(toRealPoly P).eval x| ≤
      (∑ i ∈ Finset.range (P.natDegree + 1), |((P.coeff i : ℤ) : ℝ)|)
        * (N : ℝ) ^ P.natDegree := by
    rw [toRealPoly, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
    calc |∑ i ∈ Finset.range (P.natDegree + 1), (Int.castRingHom ℝ) (P.coeff i) * x ^ i|
        ≤ ∑ i ∈ Finset.range (P.natDegree + 1),
            |(Int.castRingHom ℝ) (P.coeff i) * x ^ i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range (P.natDegree + 1), |((P.coeff i : ℤ) : ℝ)| * |x| ^ i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_pow]
          rfl
      _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1),
            |((P.coeff i : ℤ) : ℝ)| * (N : ℝ) ^ P.natDegree := by
          apply Finset.sum_le_sum
          intro i hi
          have hid : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hxi : |x| ^ i ≤ (N : ℝ) ^ i := pow_le_pow_left₀ (abs_nonneg x) hx i
          have hNd : (N : ℝ) ^ i ≤ (N : ℝ) ^ P.natDegree := pow_le_pow_right₀ hN1 hid
          exact mul_le_mul_of_nonneg_left (hxi.trans hNd) (abs_nonneg _)
      _ = (∑ i ∈ Finset.range (P.natDegree + 1), |((P.coeff i : ℤ) : ℝ)|)
            * (N : ℝ) ^ P.natDegree :=
          (Finset.sum_mul ..).symm
  simpa [polyCoeffAbsSum] using hkey

/-- The phase is bounded by `2π·(Σ_i|p_i|)·N^d` on `(0,1]`. -/
private lemma abs_profilePhase_le (P : Polynomial ℤ) (N : ℕ) (hN : 1 ≤ N) (s : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    |profilePhase P N s| ≤ 2 * Real.pi * polyCoeffAbsSum P * (N : ℝ) ^ P.natDegree := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNs : |(N : ℝ) * s| ≤ N := by
    rw [abs_mul, abs_of_nonneg hN0]
    have hs1 : |s| ≤ 1 := by rw [abs_of_pos hs.1]; exact hs.2
    nlinarith
  have h := abs_eval_toRealPoly_le P N hN ((N : ℝ) * s) hNs
  calc |profilePhase P N s| = |2 * Real.pi| * |(toRealPoly P).eval ((N : ℝ) * s)| :=
        abs_mul ..
    _ = 2 * Real.pi * |(toRealPoly P).eval ((N : ℝ) * s)| := by
        rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    _ ≤ 2 * Real.pi * (polyCoeffAbsSum P * (N : ℝ) ^ P.natDegree) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * Real.pi * polyCoeffAbsSum P * (N : ℝ) ^ P.natDegree := by ring

/-- **The profile is the characteristic function of the phase pushforward.** -/
private lemma polyProfile_eq_charFun_profileMeasure (P : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    polyProfile P N β = charFun (profileMeasure P N) β := by
  have hc := continuous_profilePhase P N
  rw [MeasureTheory.charFun_apply_real, polyProfile,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [profileMeasure,
    integral_map (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (φ := profilePhase P N)
      (f := fun v : ℝ => Complex.exp (↑β * ↑v * Complex.I))
      hc.measurable.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with s
  congr 1
  simp only [profilePhase]
  push_cast
  ring

/-- The identity has all moments for the phase pushforward measure (it is a finite measure
supported on a bounded set, namely the image of `[0,1]` under the continuous phase). -/
private lemma memLp_id_profileMeasure (P : Polynomial ℤ) (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (profileMeasure P N) := by
  have hc := continuous_profilePhase P N
  have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖profilePhase P N t‖ ≤ 2 * Real.pi * polyCoeffAbsSum P * (N : ℝ) ^ P.natDegree := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    exact abs_profilePhase_le P N hN t ht
  have hmem : MemLp (profilePhase P N) (k : ℝ≥0∞) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound hc.aestronglyMeasurable _ hb
  refine (memLp_map_measure_iff (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (f := profilePhase P N) (g := (id : ℝ → ℝ)) (p := (k : ℝ≥0∞))
    (by fun_prop) hc.aemeasurable).mpr ?_
  simpa using hmem

/-- The `k`-th moment of the phase pushforward measure is bounded by `(2π A N^d)^k`. -/
private lemma integral_norm_pow_profileMeasure_le (P : Polynomial ℤ) (N : ℕ) (hN : 1 ≤ N)
    (k : ℕ) :
    ∫ y, ‖y‖ ^ k ∂(profileMeasure P N) ≤
      (2 * Real.pi * polyCoeffAbsSum P * (N : ℝ) ^ P.natDegree) ^ k := by
  set B : ℝ := 2 * Real.pi * polyCoeffAbsSum P * (N : ℝ) ^ P.natDegree with hBdef
  have hAc : (0 : ℝ) ≤ polyCoeffAbsSum P := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  have hc := continuous_profilePhase P N
  rw [profileMeasure, integral_map (φ := profilePhase P N) (f := fun y : ℝ => ‖y‖ ^ k)
        hc.measurable.aemeasurable (by fun_prop)]
  have hle : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖profilePhase P N s‖ ^ k ≤ B ^ k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ k
    rw [Real.norm_eq_abs]
    exact abs_profilePhase_le P N hN s hs
  have h2 : ∫ s, (B : ℝ) ^ k ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = B ^ k := by
    rw [integral_const]
    simp
  calc ∫ s, ‖profilePhase P N s‖ ^ k ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
      ≤ ∫ s, (B : ℝ) ^ k ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
        refine integral_mono_ae ?_ ?_ hle
        · refine Integrable.of_bound (by fun_prop) (B ^ k) ?_
          filter_upwards [hle] with s hs
          rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        · exact integrable_const _
    _ = B ^ k := h2

/-- **The Mikhlin band bound on `N^{deg P}|β| ≤ c`, uniformly in `N`.**

This is the lemma `profileMikhlinBandGe` of the plan; the constant produced is
`max 1 ((2π · (Σ_i |p_i|) · max c 0)^k)`. -/
theorem profileMikhlinBandGe (P : Polynomial ℤ) (k : ℕ) (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (β : ℝ),
      ((N : ℝ) ^ P.natDegree) * |β| ≤ c →
      |β| ^ k * ‖iteratedDeriv k (fun γ : ℝ => Work.BourgainPlan.Maximal.polyProfile P N γ) β‖ ≤ C := by
  refine ⟨max 1 ((2 * Real.pi * polyCoeffAbsSum P * max c 0) ^ k),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro N hN β hβ
  have hfun : (fun γ : ℝ => polyProfile P N γ) = fun γ => charFun (profileMeasure P N) γ :=
    funext (polyProfile_eq_charFun_profileMeasure P N)
  rw [hfun, iteratedDeriv_charFun (memLp_id_profileMeasure P N hN k),
    norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  have hInt : ‖∫ x, (x : ℂ) ^ k * Complex.exp (↑β * ↑x * Complex.I) ∂(profileMeasure P N)‖ ≤
      (2 * Real.pi * polyCoeffAbsSum P * (N : ℝ) ^ P.natDegree) ^ k := by
    calc ‖∫ x, (x : ℂ) ^ k * Complex.exp (↑β * ↑x * Complex.I) ∂(profileMeasure P N)‖
        ≤ ∫ x, ‖(x : ℂ) ^ k * Complex.exp (↑β * ↑x * Complex.I)‖
            ∂(profileMeasure P N) :=
          norm_integral_le_integral_norm _
      _ = ∫ x, ‖x‖ ^ k ∂(profileMeasure P N) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [norm_mul, norm_pow]
          have h1 : (↑β : ℂ) * ↑x * Complex.I = ((β * x : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rw [h1, Complex.norm_exp_ofReal_mul_I, mul_one]
          congr 1
          simp
      _ ≤ _ := integral_norm_pow_profileMeasure_le P N hN k
  have hAc : (0 : ℝ) ≤ polyCoeffAbsSum P := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hB : (0 : ℝ) ≤ 2 * Real.pi * polyCoeffAbsSum P * (N : ℝ) ^ P.natDegree := by positivity
  have hfin : |β| ^ k * (2 * Real.pi * polyCoeffAbsSum P * (N : ℝ) ^ P.natDegree) ^ k
      ≤ (2 * Real.pi * polyCoeffAbsSum P * max c 0) ^ k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (abs_nonneg β) hB)
    have hdec : (N : ℝ) ^ P.natDegree * |β| ≤ max c 0 := hβ.trans (le_max_left c 0)
    have hA : (0 : ℝ) ≤ 2 * Real.pi * polyCoeffAbsSum P := by positivity
    calc |β| * (2 * Real.pi * polyCoeffAbsSum P * (N : ℝ) ^ P.natDegree)
        = (2 * Real.pi * polyCoeffAbsSum P) * ((N : ℝ) ^ P.natDegree * |β|) := by ring
      _ ≤ (2 * Real.pi * polyCoeffAbsSum P) * max c 0 := mul_le_mul_of_nonneg_left hdec hA
  exact le_trans (mul_le_mul_of_nonneg_left hInt (pow_nonneg (abs_nonneg β) k))
    (le_trans hfin (le_max_right _ _))

end

end Work.BourgainPlan.Maximal
