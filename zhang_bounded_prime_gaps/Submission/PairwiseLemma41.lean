import Submission.PairwiseTruncation
import Submission.PairwiseMainTerm
import Submission.PairwiseKernel

open scoped BigOperators Topology FourierTransform SchwartzMap
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# The pairwise P8 Lemma 4.1 (the `k`-coordinate Polymath8 divisor sum)

This module assembles the asymptotic evaluation of the pairwise-restricted
divisor sum of Polymath8a Lemma 4.1:

  * `pairKernelP_bound_eventually` — the crude bound `‖K‖ ≪ log^{3k}x`, uniform
    in the modulus;
  * `prefactor_nonneg`, `inv_log_le_prefactor` — elementary facts about the
    pole prefactor;
  * `integrable_pairKernelP_mul_pairPhase`,
    `integrable_pairPoleP_mul_pairPhase` — integrability of the kernel and the
    pole integrands (via `measurable_pairKernelP`/`measurable_pairPoleP`);
  * `pairOffCube_pole_le` — the off-cube estimate for the pole part;
  * `tendsto_log_pow_div_sqrt_log_pow` — the elementary vanishing limit;
  * `pairKernelIntegral_asymptotic` — the `ξ`-integral form of Lemma 4.1;
  * `pairwiseLemma41` — the divisor-sum form, obtained from the Fubini identity
    `pairwiseDivisorSum_eq_kernelIntegral`.

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

lemma continuous_coordLocalK {k : ℕ} (p : ℕ) (hp : p ≠ 0) :
    Continuous fun z : (Fin k → ℂ) × (Fin k → ℂ) => coordLocalK p z.1 z.2 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hz : (fun z : (Fin k → ℂ) × (Fin k → ℂ) => coordLocalK p z.1 z.2) =
      fun z : (Fin k → ℂ) × (Fin k → ℂ) =>
        1 + ∑ j : Fin k, (-((p : ℂ) ^ (-(1 + z.1 j))) - ((p : ℂ) ^ (-(1 + z.2 j))) +
          ((p : ℂ) ^ (-(1 + z.1 j + z.2 j)))) := by
    funext z
    exact coordLocalK_eq p hp z.1 z.2
  rw [hz]
  refine continuous_const.add (continuous_finsetSum _ (fun j _ => ?_))
  have h1 : Continuous fun z : (Fin k → ℂ) × (Fin k → ℂ) => -(1 + z.1 j) := by fun_prop
  have h2 : Continuous fun z : (Fin k → ℂ) × (Fin k → ℂ) => -(1 + z.2 j) := by fun_prop
  have h3 : Continuous fun z : (Fin k → ℂ) × (Fin k → ℂ) => -(1 + z.1 j + z.2 j) := by fun_prop
  exact ((h1.const_cpow (Or.inl hp0)).neg.sub (h2.const_cpow (Or.inl hp0))).add
    (h3.const_cpow (Or.inl hp0))

/-- The partial products of the pairwise kernel are strongly measurable in `p`. -/
lemma stronglyMeasurable_pairKernelP_step {k : ℕ} (W N : ℕ → ℕ) (x n : ℕ) :
    StronglyMeasurable fun p : Fin k → ℝ × ℝ =>
      ∏ pr ∈ Sfilter (W x * N x) n, coordLocalK (k := k) pr
        (fun j => logZ (-(2 * Real.pi * (p j).1)) x)
        (fun j => logZ (-(2 * Real.pi * (p j).2)) x) := by
  have hξ : Continuous fun p : Fin k → ℝ × ℝ =>
      (fun j : Fin k => logZ (-(2 * Real.pi * (p j).1)) x) := by
    refine continuous_pi (fun j => ?_)
    show Continuous fun p : Fin k → ℝ × ℝ => logZ (-(2 * Real.pi * (p j).1)) x
    unfold logZ
    fun_prop
  have hξ' : Continuous fun p : Fin k → ℝ × ℝ =>
      (fun j : Fin k => logZ (-(2 * Real.pi * (p j).2)) x) := by
    refine continuous_pi (fun j => ?_)
    show Continuous fun p : Fin k → ℝ × ℝ => logZ (-(2 * Real.pi * (p j).2)) x
    unfold logZ
    fun_prop
  have hpairs : Continuous fun p : Fin k → ℝ × ℝ =>
      ((fun j : Fin k => logZ (-(2 * Real.pi * (p j).1)) x),
        (fun j : Fin k => logZ (-(2 * Real.pi * (p j).2)) x)) := hξ.prodMk hξ'
  have hcont : Continuous fun p : Fin k → ℝ × ℝ =>
      ∏ pr ∈ Sfilter (W x * N x) n, coordLocalK (k := k) pr
        (fun j => logZ (-(2 * Real.pi * (p j).1)) x)
        (fun j => logZ (-(2 * Real.pi * (p j).2)) x) := by
    refine continuous_finsetProd _ (fun pr hpr => ?_)
    have h := (continuous_coordLocalK (k := k) pr
      (Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_filter pr hpr)).ne_zero).comp hpairs
    exact h
  exact hcont.stronglyMeasurable

lemma measurable_pairKernelP {k : ℕ} (W N : ℕ → ℕ) (x : ℕ) :
    Measurable (pairKernelP (k := k) W N x) := by
  have hstep := stronglyMeasurable_pairKernelP_step (k := k) W N x
  have heq : pairKernelP (k := k) W N x = fun p : Fin k → ℝ × ℝ =>
      (atTop : Filter ℕ).limUnder (fun n : ℕ =>
        ∏ pr ∈ Sfilter (W x * N x) n, coordLocalK (k := k) pr
          (fun j => logZ (-(2 * Real.pi * (p j).1)) x)
          (fun j => logZ (-(2 * Real.pi * (p j).2)) x)) := rfl
  rw [heq]
  exact (StronglyMeasurable.limUnder hstep).measurable

lemma measurable_pairPhase {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j)) :
    Measurable (pairPhase (k := k) F G) := by
  have hfac : ∀ j : Fin k, Measurable fun p : Fin k → ℝ × ℝ =>
      fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2 := by
    intro j
    have h1 : Continuous fun p : Fin k → ℝ × ℝ => fourierCut (F j) (p j).1 := by
      have h := (schwartzCut (F j) (hcsF j) (hsmF j)).continuous
      rw [schwartzCut_coe (F j) (hcsF j) (hsmF j)] at h
      exact h.comp ((continuous_apply j).fst)
    have h2 : Continuous fun p : Fin k → ℝ × ℝ => fourierCut (G j) (p j).2 := by
      have h := (schwartzCut (G j) (hcsG j) (hsmG j)).continuous
      rw [schwartzCut_coe (G j) (hcsG j) (hsmG j)] at h
      exact h.comp ((continuous_apply j).snd)
    exact (h1.mul h2).measurable
  have heq : pairPhase (k := k) F G = fun p : Fin k → ℝ × ℝ =>
      ∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2) := rfl
  rw [heq]
  exact Finset.measurable_prod _ (fun j _ => hfac j)

lemma measurable_pairPoleP {k : ℕ} (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (x : ℕ) (hlog : Real.log (x : ℝ) ≠ 0) :
    Measurable (pairPoleP (k := k) W N x) := by
  have hfac : ∀ j : Fin k, Measurable fun p : Fin k → ℝ × ℝ =>
      (poleFactor (W x) (N x) (-(2 * Real.pi * (p j).1)) (-(2 * Real.pi * (p j).2)) x)⁻¹ := by
    intro j
    have heq : (fun p : Fin k → ℝ × ℝ =>
        (poleFactor (W x) (N x) (-(2 * Real.pi * (p j).1)) (-(2 * Real.pi * (p j).2)) x)⁻¹) =
        fun p : Fin k → ℝ × ℝ => poleInv (W x) (N x) x (p j).1 (p j).2 := rfl
    rw [heq]
    have heq2 : (fun p : Fin k → ℝ × ℝ => poleInv (W x) (N x) x (p j).1 (p j).2) =
        fun p : Fin k → ℝ × ℝ =>
          (((N x : ℂ) / (((W x).totient : ℂ) / (W x : ℂ) * (Real.log (x : ℝ) : ℂ) *
              ((N x).totient : ℂ))) *
            ((1 - 2 * Real.pi * Complex.I * (p j).1) * (1 - 2 * Real.pi * Complex.I * (p j).2) /
              (2 - 2 * Real.pi * Complex.I * ((p j).1 + (p j).2)))) := by
      funext p
      exact poleInv_eq (W x) (N x) (hW x) (hN x) hlog (p j).1 (p j).2
    rw [heq2]
    fun_prop
  have heq : pairPoleP (k := k) W N x = fun p : Fin k → ℝ × ℝ =>
      ∏ j : Fin k, (poleFactor (W x) (N x) (-(2 * Real.pi * (p j).1)) (-(2 * Real.pi * (p j).2)) x)⁻¹ := rfl
  rw [heq]
  exact Finset.measurable_prod _ (fun j _ => hfac j)


/-! ## The crude kernel bound and integrability -/

/-- **The crude pointwise bound for the pairwise kernel**, uniform in the modulus. -/
lemma pairKernelP_bound_eventually (k : ℕ) :
    ∃ x₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, x₀ ≤ x →
      ∀ (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0) (p : Fin k → ℝ × ℝ),
        ‖pairKernelP (k := k) W N x p‖ ≤ C * (Real.log (x : ℝ)) ^ (3 * k) := by
  obtain ⟨C, hC, hxC⟩ := crudeKernelCoord_eventually_uniform k
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp (hxC.and (eventually_ge_atTop 2))
  refine ⟨x₀, C, hC, fun x hx W N hW hN p => ?_⟩
  obtain ⟨hP, hx2⟩ := hx₀ x hx
  have hx1 : 1 < x := by omega
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  have hq : W x * N x ≠ 0 := mul_ne_zero (hW x) (hN x)
  have ha : ∀ j : Fin k, 0 < (logZ (-(2 * Real.pi * (p j).1)) x).re := by
    intro j; rw [logZ_re]; positivity
  have hb : ∀ j : Fin k, 0 < (logZ (-(2 * Real.pi * (p j).2)) x).re := by
    intro j; rw [logZ_re]; positivity
  have hCd : ∀ n : ℕ, ‖∏ pr ∈ Sfilter (W x * N x) n, coordLocalK (k := k) pr
      (fun j => logZ (-(2 * Real.pi * (p j).1)) x)
      (fun j => logZ (-(2 * Real.pi * (p j).2)) x)‖ ≤ C * (Real.log (x : ℝ)) ^ (3 * k) := by
    intro n
    have h := hP (W x * N x) n (fun j => logZ (-(2 * Real.pi * (p j).1)) x)
      (fun j => logZ (-(2 * Real.pi * (p j).2)) x)
      (fun j => logZ_re _ x) (fun j => logZ_re _ x)
    simpa [Sfilter] using h
  have hres := norm_pairKernel_le (q := W x * N x) hq ha hb hCd
  simpa [pairKernelP] using hres

/-- Nonnegativity of the prefactor. -/
lemma prefactor_nonneg (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    {x : ℕ} (hx2 : 2 ≤ x) : 0 ≤ prefactor W N x := by
  have hx1 : 1 < x := by omega
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  have hφN : (0 : ℝ) < ((N x).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hN x))
  have hφW : (0 : ℝ) < ((W x).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hW x))
  have hN1 : 1 ≤ (N x : ℝ) / ((N x).totient : ℝ) := by
    rw [le_div_iff₀ hφN]
    simpa using (Nat.cast_le (α := ℝ)).mpr (Nat.totient_le (N x))
  have hW1 : 1 ≤ (W x : ℝ) / ((W x).totient : ℝ) := by
    rw [le_div_iff₀ hφW]
    simpa using (Nat.cast_le (α := ℝ)).mpr (Nat.totient_le (W x))
  rw [prefactor]
  exact mul_nonneg (mul_nonneg (le_trans zero_le_one hN1) (le_trans zero_le_one hW1))
    (inv_nonneg.mpr hL.le)

/-- The prefactor dominates `(log x)⁻¹`. -/
lemma inv_log_le_prefactor (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    {x : ℕ} (hx2 : 2 ≤ x) : (Real.log (x : ℝ))⁻¹ ≤ prefactor W N x := by
  have hx1 : 1 < x := by omega
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  have hφN : (0 : ℝ) < ((N x).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hN x))
  have hφW : (0 : ℝ) < ((W x).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hW x))
  have hN1 : 1 ≤ (N x : ℝ) / ((N x).totient : ℝ) := by
    rw [le_div_iff₀ hφN]
    simpa using (Nat.cast_le (α := ℝ)).mpr (Nat.totient_le (N x))
  have hW1 : 1 ≤ (W x : ℝ) / ((W x).totient : ℝ) := by
    rw [le_div_iff₀ hφW]
    simpa using (Nat.cast_le (α := ℝ)).mpr (Nat.totient_le (W x))
  rw [prefactor]
  calc (Real.log (x : ℝ))⁻¹ = 1 * 1 * (Real.log (x : ℝ))⁻¹ := by ring
    _ ≤ ((N x : ℝ) / ((N x).totient : ℝ)) * ((W x : ℝ) / ((W x).totient : ℝ)) *
          (Real.log (x : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul hN1 hW1 zero_le_one (le_trans zero_le_one hN1))
          (inv_nonneg.mpr hL.le)

/-- Integrability of the pairwise kernel integrand. -/
lemma integrable_pairKernelP_mul_pairPhase {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) {x : ℕ} {C : ℝ}
    (hC : ∀ p : Fin k → ℝ × ℝ,
      ‖pairKernelP (k := k) W N x p‖ ≤ C * (Real.log (x : ℝ)) ^ (3 * k)) :
    Integrable fun p : Fin k → ℝ × ℝ =>
      pairKernelP (k := k) W N x p * pairPhase (k := k) F G p := by
  have hbase : Integrable fun p : Fin k → ℝ × ℝ =>
      C * (Real.log (x : ℝ)) ^ (3 * k) * pairDom F G p :=
    (integrable_pairDom F G hcsF hsmF hcsG hsmG).const_mul _
  refine Integrable.mono' hbase ?_ (Filter.Eventually.of_forall (fun p => ?_))
  · exact ((measurable_pairKernelP (k := k) W N x).mul
      (measurable_pairPhase F G hcsF hsmF hcsG hsmG)).aestronglyMeasurable
  · rw [norm_mul, norm_pairPhase_eq F G p]
    have h1 := hC p
    have h2 := pairPhaseNorm_le_pairDom F G p
    have h3 : 0 ≤ C * (Real.log (x : ℝ)) ^ (3 * k) :=
      le_trans (norm_nonneg _) h1
    exact mul_le_mul h1 h2 (pairPhaseNorm_nonneg F G p) h3

/-- Integrability of the pole integrand. -/
lemma integrable_pairPoleP_mul_pairPhase {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0) {x : ℕ} (hx2 : 2 ≤ x) :
    Integrable fun p : Fin k → ℝ × ℝ =>
      pairPoleP (k := k) W N x p * pairPhase (k := k) F G p := by
  have hx1 : 1 < x := by omega
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  have hpre0 := prefactor_nonneg W N hW hN hx2
  have hbase : Integrable fun p : Fin k → ℝ × ℝ =>
      prefactor W N x ^ k * pairDom F G p :=
    (integrable_pairDom F G hcsF hsmF hcsG hsmG).const_mul _
  refine Integrable.mono' hbase ?_ (Filter.Eventually.of_forall (fun p => ?_))
  · exact ((measurable_pairPoleP W N hW hN x hlogpos.ne').mul
      (measurable_pairPhase F G hcsF hsmF hcsG hsmG)).aestronglyMeasurable
  · rw [norm_mul, norm_pairPhase_eq F G p]
    calc ‖pairPoleP (k := k) W N x p‖ * pairPhaseNorm F G p
        ≤ (prefactor W N x ^ k * ∏ j : Fin k, (pairW (p j).1 * pairW (p j).2)) *
            pairPhaseNorm F G p :=
          mul_le_mul_of_nonneg_right (norm_pairPoleP_le W N hW hN hlogpos p)
            (pairPhaseNorm_nonneg F G p)
      _ = prefactor W N x ^ k * pairDom F G p := by
          rw [← prodW_mul_phaseNorm_eq_pairDom F G p]; ring

/-- **Off-cube bound for the pole part of the pairwise kernel.** -/
theorem pairOffCube_pole_le {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
      ∀ (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0),
      (∫ p in (truncCubeK k x)ᶜ, ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖) ≤
        C * prefactor W N x ^ k /
          (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m := by
  obtain ⟨C, hC, hdom⟩ := pairOffCube_pairDom_le F G hcsF hsmF hcsG hsmG m
  refine ⟨C, hC, fun x hx2 W N hW hN => ?_⟩
  have hx1 : 1 < x := by omega
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  have hpre0 := prefactor_nonneg W N hW hN hx2
  have hset_meas : MeasurableSet (truncCubeK k x)ᶜ := (measurableSet_truncCubeK k x).compl
  have hDomInt : Integrable (pairDom F G) := integrable_pairDom F G hcsF hsmF hcsG hsmG
  have hpt : ∀ p : Fin k → ℝ × ℝ,
      ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖ ≤
        prefactor W N x ^ k * pairDom F G p := by
    intro p
    rw [norm_mul, norm_pairPhase_eq F G p]
    calc ‖pairPoleP (k := k) W N x p‖ * pairPhaseNorm F G p
        ≤ (prefactor W N x ^ k * ∏ j : Fin k, (pairW (p j).1 * pairW (p j).2)) *
            pairPhaseNorm F G p :=
          mul_le_mul_of_nonneg_right (norm_pairPoleP_le W N hW hN hlogpos p)
            (pairPhaseNorm_nonneg F G p)
      _ = prefactor W N x ^ k * pairDom F G p := by
          rw [← prodW_mul_phaseNorm_eq_pairDom F G p]; ring
  have hstep : (∫ p in (truncCubeK k x)ᶜ, ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖)
      ≤ ∫ p, prefactor W N x ^ k * ((truncCubeK k x)ᶜ.indicator (pairDom F G) p) := by
    rw [← integral_indicator hset_meas]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun p => ?_))
      ((hDomInt.indicator hset_meas).const_mul _) (Filter.Eventually.of_forall (fun p => ?_))
    · exact Set.indicator_nonneg (fun q _ => norm_nonneg _) p
    · dsimp only
      by_cases hp : p ∈ (truncCubeK k x)ᶜ
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
        exact hpt p
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, mul_zero]
  calc (∫ p in (truncCubeK k x)ᶜ, ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖)
      ≤ ∫ p, prefactor W N x ^ k * ((truncCubeK k x)ᶜ.indicator (pairDom F G) p) := hstep
    _ = prefactor W N x ^ k * (∫ p in (truncCubeK k x)ᶜ, pairDom F G p) := by
        rw [integral_const_mul, integral_indicator hset_meas]
    _ ≤ prefactor W N x ^ k * (C / (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m) :=
        mul_le_mul_of_nonneg_left (hdom x hx2) (pow_nonneg hpre0 k)
    _ = C * prefactor W N x ^ k / (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m := by ring


/-- `(log x)^a / (√(log x))^m → 0` when `2a < m`. -/
lemma tendsto_log_pow_div_sqrt_log_pow (a m : ℕ) (h : 2 * a < m) :
    Tendsto (fun x : ℕ =>
      (Real.log (x : ℝ)) ^ a / (Real.sqrt (Real.log (x : ℝ))) ^ m) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun x : ℕ => Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hatTop : Tendsto (fun t : ℝ => t ^ (m - 2 * a)) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (max b 1)] with t ht
    have h1 : 1 ≤ t := le_trans (le_max_right _ _) ht
    have h2 : b ≤ t := le_trans (le_max_left _ _) ht
    exact le_trans h2 (le_self_pow₀ h1 (by omega))
  have hpow : Tendsto (fun x : ℕ =>
      (Real.sqrt (Real.log (x : ℝ))) ^ (m - 2 * a)) atTop atTop :=
    hatTop.comp hsqrt
  refine Filter.Tendsto.congr' ?_ (tendsto_inv_atTop_zero.comp hpow)
  filter_upwards [eventually_ge_atTop 2] with x hx
  dsimp only [Function.comp_apply]
  have hx1 : 1 < x := by omega
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  have hrootpos : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.mpr hlogpos
  have hsq : (Real.sqrt (Real.log (x : ℝ))) ^ 2 = Real.log (x : ℝ) := Real.sq_sqrt hlogpos.le
  have hnum : (Real.log (x : ℝ)) ^ a = (Real.sqrt (Real.log (x : ℝ))) ^ (2 * a) := by
    rw [show (Real.sqrt (Real.log (x : ℝ))) ^ (2 * a) = (Real.log (x : ℝ)) ^ a from by
      rw [pow_mul, hsq]]
  have hsplit : (Real.sqrt (Real.log (x : ℝ))) ^ m =
      (Real.sqrt (Real.log (x : ℝ))) ^ (2 * a) *
        (Real.sqrt (Real.log (x : ℝ))) ^ (m - 2 * a) := by
    rw [← pow_add]; congr 1; omega
  rw [hnum, hsplit, div_eq_mul_inv, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hrootpos.ne'), one_mul]

/-- **The `ξ`-integral form of the pairwise P8 Lemma 4.1.**  The divisor-sum
integral equals `prefactor^k·∏_j∫₀^∞F_j′G_j′` up to a relative error `o(1)`. -/
theorem pairKernelIntegral_asymptotic {k : ℕ} (hk : 1 ≤ k)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ j, HasCompactSupport (F j))
    (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j)) (hcsG : ∀ j, HasCompactSupport (G j))
    (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x →
        ‖(∫ p : Fin k → ℝ × ℝ, pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) -
            ((prefactor W N x : ℝ) : ℂ) ^ k * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
              ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))‖ ≤
          ε x * prefactor W N x ^ k := by
  classical
  set m : ℕ := 8 * k + 2 with hmdef
  obtain ⟨x₀c, εc, hεc, hcube⟩ :=
    pairCube_integral_le hk F G hcsF hsmF hcsG hsmG W N hW hN hcop w hw hsmall hlq
  obtain ⟨x₀k, Ck, hCk, hoffk⟩ := pairOffCube_le hk F G hcsF hsmF hcsG hsmG W N hW hN m
  obtain ⟨x₀K, CK, hCK, hKbd⟩ := pairKernelP_bound_eventually k
  obtain ⟨Cp, hCp, hoffp⟩ := pairOffCube_pole_le F G hcsF hsmF hcsG hsmG m
  set Cfg : ℝ := ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) with hCfgdef
  refine ⟨max (max x₀c (max x₀k x₀K)) 2,
    fun x : ℕ => |εc x| * Cfg +
      Ck * (2 * Real.pi) ^ m * (Real.log (x : ℝ)) ^ (4 * k) / (Real.sqrt (Real.log (x : ℝ))) ^ m +
      Cp * (2 * Real.pi) ^ m / (Real.sqrt (Real.log (x : ℝ))) ^ m, ?_, ?_⟩
  · -- the error sequence tends to zero
    have h1 : Tendsto (fun x : ℕ => |εc x| * Cfg) atTop (𝓝 0) := by
      simpa using hεc.abs.mul_const Cfg
    have h2 : Tendsto (fun x : ℕ => Ck * (2 * Real.pi) ^ m *
        ((Real.log (x : ℝ)) ^ (4 * k) / (Real.sqrt (Real.log (x : ℝ))) ^ m)) atTop (𝓝 0) := by
      simpa using (tendsto_log_pow_div_sqrt_log_pow (4 * k) m (by omega)).const_mul
        (Ck * (2 * Real.pi) ^ m)
    have h3 : Tendsto (fun x : ℕ => Cp * (2 * Real.pi) ^ m *
        ((Real.log (x : ℝ)) ^ 0 / (Real.sqrt (Real.log (x : ℝ))) ^ m)) atTop (𝓝 0) := by
      simpa using (tendsto_log_pow_div_sqrt_log_pow 0 m (by omega)).const_mul
        (Cp * (2 * Real.pi) ^ m)
    have h3' : Tendsto (fun x : ℕ => Cp * (2 * Real.pi) ^ m /
        (Real.sqrt (Real.log (x : ℝ))) ^ m) atTop (𝓝 0) := by
      refine Filter.Tendsto.congr (fun x => ?_) h3
      simp only [pow_zero, one_div, mul_one, one_mul, div_eq_mul_inv]
    have h12 := h1.add h2
    have h123 : Tendsto (fun x : ℕ => |εc x| * Cfg +
        Ck * (2 * Real.pi) ^ m *
          ((Real.log (x : ℝ)) ^ (4 * k) / (Real.sqrt (Real.log (x : ℝ))) ^ m) +
        Cp * (2 * Real.pi) ^ m / (Real.sqrt (Real.log (x : ℝ))) ^ m) atTop (𝓝 0) := by
      simpa using h12.add h3'
    refine Filter.Tendsto.congr (fun x => ?_) h123
    ring
  · intro x hx
    have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
    have hxc : x₀c ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hkk : max x₀k x₀K ≤ x :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hxk : x₀k ≤ x := le_trans (le_max_left _ _) hkk
    have hxK : x₀K ≤ x := le_trans (le_max_right _ _) hkk
    have hx1 : 1 < x := by omega
    have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
    have hpre0 : 0 ≤ prefactor W N x := prefactor_nonneg W N hW hN hx2
    have hinvlog : (Real.log (x : ℝ))⁻¹ ≤ prefactor W N x := inv_log_le_prefactor W N hW hN hx2
    have hprepow : ((Real.log (x : ℝ))⁻¹) ^ k ≤ prefactor W N x ^ k :=
      pow_le_pow_left₀ (inv_nonneg.mpr hlogpos.le) hinvlog k
    have h2pi : 0 < 2 * Real.pi := by positivity
    have hrootpos : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.mpr hlogpos
    have hrootm : 0 < (Real.sqrt (Real.log (x : ℝ))) ^ m := pow_pos hrootpos m
    have hrho_inv : ((Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m)⁻¹ =
        (2 * Real.pi) ^ m / (Real.sqrt (Real.log (x : ℝ))) ^ m := by
      rw [div_pow, inv_div]
    -- the three integral pieces
    set A : ℂ := ∫ p in truncCubeK k x,
      (pairKernelP (k := k) W N x p - pairPoleP (k := k) W N x p) * pairPhase (k := k) F G p
      with hAdef
    set B : ℂ := ∫ p in (truncCubeK k x)ᶜ,
      pairKernelP (k := k) W N x p * pairPhase (k := k) F G p with hBdef
    set Cs : ℂ := ∫ p in (truncCubeK k x)ᶜ,
      pairPoleP (k := k) W N x p * pairPhase (k := k) F G p with hCsdef
    have hIntK := integrable_pairKernelP_mul_pairPhase F G hcsF hsmF hcsG hsmG W N
      (hKbd x hxK W N hW hN)
    have hIntP := integrable_pairPoleP_mul_pairPhase F G hcsF hsmF hcsG hsmG W N hW hN hx2
    have hset_meas : MeasurableSet (truncCubeK k x) := measurableSet_truncCubeK k x
    have hsplitK : (∫ p : Fin k → ℝ × ℝ, pairKernelP (k := k) W N x p * pairPhase (k := k) F G p)
        = (∫ p in truncCubeK k x, pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) +
          (∫ p in (truncCubeK k x)ᶜ,
            pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) :=
      (MeasureTheory.integral_add_compl hset_meas hIntK).symm
    have hsplitP : (∫ p : Fin k → ℝ × ℝ, pairPoleP (k := k) W N x p * pairPhase (k := k) F G p)
        = (∫ p in truncCubeK k x, pairPoleP (k := k) W N x p * pairPhase (k := k) F G p) +
          (∫ p in (truncCubeK k x)ᶜ,
            pairPoleP (k := k) W N x p * pairPhase (k := k) F G p) :=
      (MeasureTheory.integral_add_compl hset_meas hIntP).symm
    have hmain : (∫ p : Fin k → ℝ × ℝ, pairPoleP (k := k) W N x p * pairPhase (k := k) F G p) =
        ((prefactor W N x : ℝ) : ℂ) ^ k * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
          ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)) := by
      simpa only [pairPoleP, pairPhase] using
        pairPoleMainTerm F G hcsF hsmF hcsG hsmG W N hW hN x hlogpos.ne' hlogpos
    have hcubeSub : (∫ p in truncCubeK k x, pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) -
        (∫ p in truncCubeK k x, pairPoleP (k := k) W N x p * pairPhase (k := k) F G p) =
        ∫ p in truncCubeK k x,
          (pairKernelP (k := k) W N x p - pairPoleP (k := k) W N x p) *
            pairPhase (k := k) F G p := by
      rw [← MeasureTheory.integral_sub hIntK.integrableOn hIntP.integrableOn]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      dsimp only
      ring
    have hEq : (∫ p : Fin k → ℝ × ℝ, pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) -
        (∫ p : Fin k → ℝ × ℝ, pairPoleP (k := k) W N x p * pairPhase (k := k) F G p) =
        A + B - Cs := by
      rw [hAdef, hBdef, hCsdef]
      rw [hsplitK, hsplitP,
        show (∫ p in truncCubeK k x, pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) +
              (∫ p in (truncCubeK k x)ᶜ,
                pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) -
              ((∫ p in truncCubeK k x, pairPoleP (k := k) W N x p * pairPhase (k := k) F G p) +
                (∫ p in (truncCubeK k x)ᶜ,
                  pairPoleP (k := k) W N x p * pairPhase (k := k) F G p)) =
            ((∫ p in truncCubeK k x, pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) -
                (∫ p in truncCubeK k x,
                  pairPoleP (k := k) W N x p * pairPhase (k := k) F G p)) +
              ((∫ p in (truncCubeK k x)ᶜ,
                  pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) -
                (∫ p in (truncCubeK k x)ᶜ,
                  pairPoleP (k := k) W N x p * pairPhase (k := k) F G p)) from by ring]
      rw [hcubeSub]
      ring
    -- norm bounds for the three pieces
    have hAnorm : ‖A‖ ≤ |εc x| * prefactor W N x ^ k * Cfg := by
      rw [hAdef]
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [hCfgdef]
      exact hcube x hxc
    have hBnorm : ‖B‖ ≤ Ck * (Real.log (x : ℝ)) ^ (3 * k) /
        (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m := by
      rw [hBdef]
      exact (norm_integral_le_integral_norm _).trans (hoffk x hxk)
    have hCnorm : ‖Cs‖ ≤ Cp * prefactor W N x ^ k /
        (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m := by
      rw [hCsdef]
      exact (norm_integral_le_integral_norm _).trans (hoffp x hx2 W N hW hN)
    have htri : ‖A + B - Cs‖ ≤ ‖A‖ + ‖B‖ + ‖Cs‖ := by
      calc ‖A + B - Cs‖ ≤ ‖A + B‖ + ‖Cs‖ := norm_sub_le _ _
        _ ≤ (‖A‖ + ‖B‖) + ‖Cs‖ := add_le_add (norm_add_le A B) le_rfl
        _ = ‖A‖ + ‖B‖ + ‖Cs‖ := by ring
    -- arithmetic for the off-cube terms
    have h1 : 1 ≤ (Real.log (x : ℝ)) ^ k * prefactor W N x ^ k := by
      have h := mul_le_mul_of_nonneg_left hprepow (pow_nonneg hlogpos.le k)
      rwa [← mul_pow, mul_inv_cancel₀ hlogpos.ne', one_pow] at h
    have hfac : (0 : ℝ) ≤ Ck * (2 * Real.pi) ^ m / (Real.sqrt (Real.log (x : ℝ))) ^ m := by
      positivity
    have h2 : Ck * (Real.log (x : ℝ)) ^ (3 * k) /
          (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m ≤
        Ck * (2 * Real.pi) ^ m * (Real.log (x : ℝ)) ^ (4 * k) /
            (Real.sqrt (Real.log (x : ℝ))) ^ m * prefactor W N x ^ k := by
      calc Ck * (Real.log (x : ℝ)) ^ (3 * k) /
            (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m
          = (Ck * (2 * Real.pi) ^ m / (Real.sqrt (Real.log (x : ℝ))) ^ m) *
              (Real.log (x : ℝ)) ^ (3 * k) := by
            rw [div_eq_mul_inv, hrho_inv]; ring
        _ ≤ (Ck * (2 * Real.pi) ^ m / (Real.sqrt (Real.log (x : ℝ))) ^ m) *
              ((Real.log (x : ℝ)) ^ (4 * k) * prefactor W N x ^ k) := by
            refine mul_le_mul_of_nonneg_left ?_ hfac
            calc (Real.log (x : ℝ)) ^ (3 * k) = (Real.log (x : ℝ)) ^ (3 * k) * 1 := by ring
              _ ≤ (Real.log (x : ℝ)) ^ (3 * k) *
                    ((Real.log (x : ℝ)) ^ k * prefactor W N x ^ k) :=
                  mul_le_mul_of_nonneg_left h1 (pow_nonneg hlogpos.le _)
              _ = ((Real.log (x : ℝ)) ^ (3 * k) * (Real.log (x : ℝ)) ^ k) *
                    prefactor W N x ^ k := by ring
              _ = (Real.log (x : ℝ)) ^ (4 * k) * prefactor W N x ^ k := by
                  rw [← pow_add]; congr 1; ring
        _ = Ck * (2 * Real.pi) ^ m * (Real.log (x : ℝ)) ^ (4 * k) /
              (Real.sqrt (Real.log (x : ℝ))) ^ m * prefactor W N x ^ k := by ring
    have h3 : Cp * prefactor W N x ^ k /
          (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m =
        Cp * (2 * Real.pi) ^ m / (Real.sqrt (Real.log (x : ℝ))) ^ m * prefactor W N x ^ k := by
      rw [div_eq_mul_inv, hrho_inv]; ring
    have h4 : |εc x| * prefactor W N x ^ k * Cfg = (|εc x| * Cfg) * prefactor W N x ^ k := by
      ring
    -- assemble
    calc ‖(∫ p : Fin k → ℝ × ℝ, pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) -
          ((prefactor W N x : ℝ) : ℂ) ^ k * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
            ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))‖
        = ‖(∫ p : Fin k → ℝ × ℝ, pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) -
            (∫ p : Fin k → ℝ × ℝ, pairPoleP (k := k) W N x p * pairPhase (k := k) F G p)‖ := by
          rw [hmain]
      _ = ‖A + B - Cs‖ := by rw [hEq]
      _ ≤ ‖A‖ + ‖B‖ + ‖Cs‖ := htri
      _ ≤ |εc x| * prefactor W N x ^ k * Cfg +
            Ck * (Real.log (x : ℝ)) ^ (3 * k) /
              (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m +
            Cp * prefactor W N x ^ k / (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m := by
          linarith [hAnorm, hBnorm, hCnorm]
      _ ≤ (|εc x| * Cfg +
            Ck * (2 * Real.pi) ^ m * (Real.log (x : ℝ)) ^ (4 * k) /
              (Real.sqrt (Real.log (x : ℝ))) ^ m +
            Cp * (2 * Real.pi) ^ m / (Real.sqrt (Real.log (x : ℝ))) ^ m) *
          prefactor W N x ^ k := by
          rw [h4, h3]
          linarith [h2]


/-- **The pairwise P8 Lemma 4.1.**  For a family of moduli `W, N` (coprime, with
all primes up to `w x → ∞` dividing `W x·N x` and `log(W x·N x) = o(√(log x))`),
the pairwise-restricted divisor sum

    Σ_{d_j,d'_j pairwise good} ∏_j μ(d_j)μ(d'_j)/[d_j,d'_j]·F_j(log_x d_j)·G_j(log_x d'_j)

equals `prefactor^k·∏_j ∫₀^∞ F_j′G_j′` up to a relative error `o(1)`. -/
theorem pairwiseLemma41 {k : ℕ} (hk : 1 ≤ k)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ j, HasCompactSupport (F j))
    (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j)) (hcsG : ∀ j, HasCompactSupport (G j))
    (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x →
        ‖(∑' d : Fin k → ℕ × ℕ, pairWeightDiv F G (W x * N x) x d) -
            ((prefactor W N x : ℝ) : ℂ) ^ k * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
              ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))‖ ≤
          ε x * prefactor W N x ^ k := by
  classical
  obtain ⟨x₀, ε, hε, hbd⟩ :=
    pairKernelIntegral_asymptotic hk F G hcsF hsmF hcsG hsmG W N hW hN hcop w hw hsmall hlq
  refine ⟨max x₀ 2, ε, hε, fun x hx => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : 1 < x := by omega
  have hq : W x * N x ≠ 0 := mul_ne_zero (hW x) (hN x)
  rw [pairwiseDivisorSum_eq_kernelIntegral F G hcsF hsmF hcsG hsmG (W x * N x) x hq hx1]
  exact hbd x hx0

end Commons.NumberTheory.MaynardSieve
