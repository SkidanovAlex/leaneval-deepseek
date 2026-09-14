import Submission.NBody.LimitShape
import Submission.NBody.Identification
import Submission.Commons.MeasureTheory.Integral.log_le_integral_inv_of_le_mul
import Submission.Commons.MeasureTheory.Integral.integral_const_div_mul_eq
import Submission.Commons.Analysis.Real.first_crossing_strict
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_lipschitzWith

/-!
# The limit shape of a calibrating curve has no collisions

Maderna--Venturelli's proof (§4.3, step 2) that the limit shape `b` of the calibrating curve of a
horofunction directed by `a` is collision free.  The proof is by contradiction: assuming that `b`
has a collision, one replaces a long piece of the `h`-minimisers `γ_k` by a competitor built from
a minimiser and the *homothetic* curve `t ↦ (ρ_k(t)/ρ_k(T_k)) • γ_k(T_k)` (where
`ρ_k(t) = ‖γ_k(t)‖_[m]` is the radial function), whose action is smaller because the
configurational measure `μ = ‖·‖_[m] U` blows up near `b`.

This file contains:
* the mass-norm calculus of the radial function (`kinetic = ½‖·‖_[m]²`, the a.e. bound
  `(deriv ρ)² ≤ 2 * kinetic (deriv γ)`, absolute continuity of the radial function);
* the homothetic curve, its derivative, its kinetic energy and its potential energy;
* the truncation time `T_k` (the first crossing of the level `2μ(a)`);
* the four-piece competitor `η_k` and the strict inequality `A(η_k) < A(γ_k)`;
* the theorem `withoutCollisions_of_limshape`.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## §1 The radial function of a configuration curve -/

/-- The mass norm is bounded by the ambient norm (with constants that depend only on the masses). -/
lemma weightedNorm_le_mul_norm {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (x : EN E N) :
    ‖x‖_[m] ≤ Real.sqrt (∑ i, m i) * ‖x‖ := by
  rw [weightedNorm, show ‖x‖ = Real.sqrt (∑ i, ‖x.ofLp i‖ ^ 2) from PiLp.norm_eq_of_L2 x]
  rw [← (Real.sqrt_mul (x := ∑ i, m i) (Finset.sum_nonneg fun i _ => hm i)
    (∑ i, ‖x.ofLp i‖ ^ 2))]
  apply Real.sqrt_le_sqrt
  calc ∑ i, m i * ‖x.ofLp i‖ ^ 2
      ≤ ∑ i, (∑ j, m j) * ‖x.ofLp i‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h2 : m i ≤ ∑ j, m j := Finset.single_le_sum (fun j _ => hm j) (Finset.mem_univ i)
        gcongr
    _ = (∑ j, m j) * ∑ i, ‖x.ofLp i‖ ^ 2 := by rw [Finset.mul_sum]

/-- The mass norm is `1`-Lipschitz for the mass distance. -/
lemma abs_weightedNorm_sub_le {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (x y : EN E N) :
    |‖x‖_[m] - ‖y‖_[m]| ≤ ‖x - y‖_[m] := by
  have h1 : ‖x‖_[m] ≤ ‖x - y‖_[m] + ‖y‖_[m] := by
    have h := weightedNorm_sub_le hm x y 0
    rwa [sub_zero, sub_zero] at h
  have h2 : ‖y - x‖_[m] = ‖x - y‖_[m] := by
    rw [← neg_sub x y]
    simpa using weightedNorm_smul hm (-1 : ℝ) (x - y)
  have h3 : ‖y‖_[m] ≤ ‖x - y‖_[m] + ‖x‖_[m] := by
    have h := weightedNorm_sub_le hm y x 0
    rw [sub_zero, sub_zero, h2] at h
    exact h
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The radial function `t ↦ ‖γ t‖_[m]` is Lipschitz with constant `√(∑ mᵢ)`. -/
lemma lipschitzWith_weightedNorm {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) :
    LipschitzWith (⟨Real.sqrt (∑ i, m i), Real.sqrt_nonneg _⟩ : NNReal)
      (fun x : EN E N => ‖x‖_[m]) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [Real.dist_eq]
  calc |‖x‖_[m] - ‖y‖_[m]| ≤ ‖x - y‖_[m] := abs_weightedNorm_sub_le hm x y
    _ ≤ Real.sqrt (∑ i, m i) * ‖x - y‖ := weightedNorm_le_mul_norm hm (x - y)
    _ = ↑(⟨Real.sqrt (∑ i, m i), Real.sqrt_nonneg _⟩ : NNReal) * dist x y := by
        rw [dist_eq_norm]

/-- The mass norm is continuous. -/
lemma continuous_weightedNorm {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) :
    Continuous (fun x : EN E N => ‖x‖_[m]) :=
  (lipschitzWith_weightedNorm hm).continuous

/-- The kinetic energy is half the square of the mass norm. -/
lemma kinetic_eq_half_weightedNorm_sq {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (v : EN E N) :
    kinetic m v = (1 / 2) * (‖v‖_[m]) ^ 2 := by
  rw [kinetic, weightedNorm]
  have h : 0 ≤ ∑ i, m i * ‖v i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _)
  rw [Real.sq_sqrt h]

/-- The radial function of an absolutely continuous curve is absolutely continuous. -/
lemma absolutelyContinuousOnInterval_weightedNorm_comp {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i)
    {γ : ℝ → EN E N} {a b : ℝ} (hac : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (fun t => ‖γ t‖_[m]) a b := by
  have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_lipschitzWith
    (K := (⟨Real.sqrt (∑ i, m i), Real.sqrt_nonneg _⟩ : NNReal))
    hac (lipschitzWith_weightedNorm (E := E) (N := N) hm)
  simpa only [Function.comp_apply] using h

/-! ## §2 The radial derivative bound

The key analytic input of the polar decomposition: along an absolutely continuous curve the
derivative of the radial function is bounded by the norm of the derivative in the mass norm. -/

/-- **The radial derivative is bounded by the mass norm of the derivative.** -/
theorem ae_deriv_weightedNorm_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {γ : ℝ → EN E N} {a b : ℝ}
    (hac : AbsolutelyContinuousOnInterval γ a b) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      |deriv (fun s => ‖γ s‖_[m]) t| ≤ ‖deriv γ t‖_[m] := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  have hγ : ∀ᵐ t : ℝ, t ∈ Set.Ioc a b → DifferentiableAt ℝ γ t :=
    (Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_ae_differentiableAt_vector
      hac).mono fun t ht hmem =>
      ht (Set.uIoc_subset_uIcc (Set.Ioc_subset_uIoc hmem))
  have hρ : ∀ᵐ t : ℝ, t ∈ Set.Ioc a b →
      DifferentiableAt ℝ (fun s => ‖γ s‖_[m]) t :=
    ((absolutelyContinuousOnInterval_weightedNorm_comp hm0 hac).ae_differentiableAt).mono
      fun t ht hmem => ht (Set.uIoc_subset_uIcc (Set.Ioc_subset_uIoc hmem))
  filter_upwards [hγ, hρ] with t hγt hρt hmem
  have hγd : HasDerivAt γ (deriv γ t) t := (hγt hmem).hasDerivAt
  have hρd : HasDerivAt (fun s => ‖γ s‖_[m])
      (deriv (fun s => ‖γ s‖_[m]) t) t := (hρt hmem).hasDerivAt
  have h1 : Tendsto (fun h : ℝ =>
      h⁻¹ * ((fun s => ‖γ s‖_[m]) (t + h) - (fun s => ‖γ s‖_[m]) t))
      (𝓝[≠] (0 : ℝ)) (𝓝 (deriv (fun s => ‖γ s‖_[m]) t)) := by
    have h := (hasDerivAt_iff_tendsto_slope_zero).mp hρd
    simpa only [smul_eq_mul] using h
  have h2 : Tendsto (fun h : ℝ => h⁻¹ • (γ (t + h) - γ t)) (𝓝[≠] (0 : ℝ))
      (𝓝 (deriv γ t)) := (hasDerivAt_iff_tendsto_slope_zero).mp hγd
  have h3 : Tendsto (fun h : ℝ => ‖h⁻¹ • (γ (t + h) - γ t)‖_[m]) (𝓝[≠] (0 : ℝ))
      (𝓝 ‖deriv γ t‖_[m]) :=
    ((continuous_weightedNorm hm0).tendsto (deriv γ t)).comp h2
  have h4 : Tendsto (fun h : ℝ =>
      |h⁻¹ * ((fun s => ‖γ s‖_[m]) (t + h) - (fun s => ‖γ s‖_[m]) t)|)
      (𝓝[≠] (0 : ℝ)) (𝓝 |deriv (fun s => ‖γ s‖_[m]) t|) :=
    (continuous_abs.tendsto _).comp h1
  refine le_of_tendsto_of_tendsto h4 h3 ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [abs_mul, abs_inv, weightedNorm_smul hm0 h⁻¹ (γ (t + h) - γ t), abs_inv]
  exact mul_le_mul_of_nonneg_left (abs_weightedNorm_sub_le hm0 _ _)
    (inv_nonneg.mpr (abs_nonneg h))

/-! ## §3 The homothetic curve -/

/-- The homothetic curve through the configuration `z`, with radial function `ρ`, normalised so
that at a time `c` with `ρ c = ‖z‖_[m]` it passes through `z`: `t ↦ (ρ t / c) • z`. -/
noncomputable def homothetic (ρ : ℝ → ℝ) (c : ℝ) (z : EN E N) : ℝ → EN E N :=
  fun t => (ρ t / c) • z

@[simp] lemma homothetic_apply (ρ : ℝ → ℝ) (c : ℝ) (z : EN E N) (t : ℝ) :
    homothetic ρ c z t = (ρ t / c) • z := rfl

/-- The homothetic curve of an absolutely continuous radial function is absolutely continuous. -/
lemma homothetic_absolutelyContinuous {ρ : ℝ → ℝ} {c : ℝ} {z : EN E N} {a b : ℝ}
    (hρ : AbsolutelyContinuousOnInterval ρ a b) :
    AbsolutelyContinuousOnInterval (homothetic (E := E) (N := N) ρ c z) a b := by
  have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_of_dist_le
    (f := ρ) (g := fun s : ℝ => (s / c) • z) (K := ‖z‖ * |c|⁻¹)
    (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (abs_nonneg c))) ?_ hρ
  · change AbsolutelyContinuousOnInterval (fun t : ℝ => (ρ t / c) • z) a b
    have h2 : (fun t : ℝ => (ρ t / c) • z) = ((fun s : ℝ => (s / c) • z) ∘ ρ) := by
      funext t
      rfl
    rw [h2]
    exact h
  · intro x y
    calc dist ((x / c) • z) ((y / c) • z)
        = |(x - y) / c| * ‖z‖ := by
          rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
          congr 2
          ring
      _ = ‖z‖ * |c|⁻¹ * |x - y| := by
          rw [abs_div]
          ring
      _ ≤ ‖z‖ * |c|⁻¹ * dist x y := le_of_eq (by rw [Real.dist_eq])

/-- The derivative of the homothetic curve. -/
lemma deriv_homothetic {ρ : ℝ → ℝ} {c : ℝ} {z : EN E N} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ t) :
    deriv (homothetic (E := E) (N := N) ρ c z) t = (deriv ρ t / c) • z := by
  have h1 : HasDerivAt (fun s : ℝ => ρ s / c) (deriv ρ t / c) t := hρ.hasDerivAt.div_const c
  have h2 : HasDerivAt (fun s : ℝ => (ρ s / c) • z) ((deriv ρ t / c) • z) t :=
    h1.smul_const z
  have h3 : HasDerivAt (homothetic (E := E) (N := N) ρ c z) ((deriv ρ t / c) • z) t := h2
  exact h3.deriv

/-- The homothetic curve of a collision-free configuration, with a positive scalar, is
collision free. -/
lemma withoutCollisions_homothetic {ρ : ℝ → ℝ} {c : ℝ} {z : EN E N} {t : ℝ}
    (hz : WithoutCollisions z) (hpos : 0 < ρ t / c) :
    WithoutCollisions (homothetic (E := E) (N := N) ρ c z t) := by
  rw [homothetic_apply]
  exact withoutCollisions_smul hz (ne_of_gt hpos)

/-- The potential energy of the homothetic curve. -/
lemma U_homothetic {m : Fin N → ℝ} {ρ : ℝ → ℝ} {c : ℝ} {z : EN E N} {t : ℝ}
    (hc : 0 < c) (hρt : 0 < ρ t) :
    U m (homothetic (E := E) (N := N) ρ c z t) = (c / ρ t) * U m z := by
  rw [homothetic_apply, U_smul, abs_of_pos (div_pos hρt hc)]
  field_simp

/-- The kinetic energy of the derivative of the homothetic curve. -/
lemma kinetic_deriv_homothetic {m : Fin N → ℝ} {ρ : ℝ → ℝ} {c : ℝ} {z : EN E N} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ t) :
    kinetic m (deriv (homothetic (E := E) (N := N) ρ c z) t)
      = (deriv ρ t / c) ^ 2 * kinetic m z := by
  rw [deriv_homothetic hρ, kinetic_smul]

/-! ## §4 The configurational measure near a collision -/

/-- The sum of the masses is positive as soon as there is an index. -/
lemma sum_mass_pos {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) (i : Fin N) : 0 < ∑ i, m i :=
  lt_of_lt_of_le (hm i) (Finset.single_le_sum (fun i _ => (hm i).le) (Finset.mem_univ i))

/-- **The Newtonian potential blows up near a colliding configuration** (on configurations which
are themselves collision free). -/
lemma exists_lt_U_of_collision {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {b : EN E N} {i j : Fin N}
    (hij : i ≠ j) (hbij : b i = b j) (K : ℝ) :
    ∃ ε > 0, ∀ x : EN E N, WithoutCollisions x → dist x b < ε → K < U m x := by
  have hpos : 0 < m i * m j := mul_pos (hm i) (hm j)
  refine ⟨m i * m j / (2 * (|K| + 1)), by positivity, fun x hxnc hx => ?_⟩
  have hxd : 0 < dist (x i) (x j) := by
    have h := hxnc i j hij
    rw [r] at h
    exact lt_of_le_of_ne dist_nonneg (Ne.symm h)
  have hd : dist (x i) (x j) ≤ 2 * (m i * m j / (2 * (|K| + 1))) := by
    have h1 : dist (x i) (b i) ≤ dist x b := PiLp.dist_apply_le x b i
    have h2 : dist (b j) (x j) ≤ dist x b := by
      rw [dist_comm]; exact PiLp.dist_apply_le x b j
    have h3 : dist (b i) (b j) = 0 := by rw [hbij]; exact dist_self _
    have h4 := dist_triangle (b i) (b j) (x j)
    calc dist (x i) (x j) ≤ dist (x i) (b i) + dist (b i) (x j) := dist_triangle _ _ _
      _ ≤ dist (x i) (b i) + (dist (b i) (b j) + dist (b j) (x j)) := by linarith
      _ ≤ 2 * (m i * m j / (2 * (|K| + 1))) := by rw [h3]; linarith
  have hinv : (2 * (m i * m j / (2 * (|K| + 1))))⁻¹ ≤ (dist (x i) (x j))⁻¹ :=
    inv_anti₀ hxd hd
  have hterm : |K| + 1 ≤ m i * m j * (dist (x i) (x j))⁻¹ := by
    have h2 : m i * m j * (2 * (m i * m j / (2 * (|K| + 1))))⁻¹ = |K| + 1 := by
      have h1 : (2 * (m i * m j / (2 * (|K| + 1)))) = m i * m j / (|K| + 1) := by
        rw [mul_div_assoc']
        exact mul_div_mul_left (m i * m j) (|K| + 1) (c := 2) (by norm_num)
      rw [h1, inv_div]
      field_simp
      exact div_self (ne_of_gt hpos)
    calc |K| + 1 = m i * m j * (2 * (m i * m j / (2 * (|K| + 1))))⁻¹ := h2.symm
      _ ≤ m i * m j * (dist (x i) (x j))⁻¹ := mul_le_mul_of_nonneg_left hinv hpos.le
  have hnn : ∀ p ∈ pairFinset N, (0:ℝ) ≤ m p.1 * m p.2 * (r x p.1 p.2)⁻¹ := by
    intro p _
    have : 0 ≤ (r x p.1 p.2)⁻¹ := inv_nonneg.mpr dist_nonneg
    exact mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) this
  have hK : K < |K| + 1 := lt_of_le_of_lt (le_abs_self K) (lt_add_one |K|)
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · have hmem : (i, j) ∈ pairFinset N := by
      rw [pairFinset, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hij'⟩
    have hle := Finset.single_le_sum hnn hmem
    rw [← U_eq_pairFinset] at hle
    have hsame : m i * m j * (r x i j)⁻¹ = m i * m j * (dist (x i) (x j))⁻¹ := rfl
    rw [hsame] at hle
    linarith
  · have hmem : (j, i) ∈ pairFinset N := by
      rw [pairFinset, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hij'⟩
    have hle := Finset.single_le_sum hnn hmem
    rw [← U_eq_pairFinset] at hle
    have hsym : m j * m i * (r x j i)⁻¹ = m i * m j * (dist (x i) (x j))⁻¹ := by
      rw [r_eq_norm_sub, dist_eq_norm, norm_sub_rev]
      ring
    rw [hsym] at hle
    linarith

/-- **The configurational measure blows up near a colliding configuration** (for positive
masses, on collision-free configurations, with `b ≠ 0`). -/
lemma exists_lt_configMeasure_of_collision {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {b : EN E N}
    {i j : Fin N} (hij : i ≠ j) (hbij : b i = b j) (hb0 : b ≠ 0) (K : ℝ) :
    ∃ ε > 0, ∀ x : EN E N, WithoutCollisions x → dist x b < ε → K < configMeasure m x := by
  have hbpos : 0 < ‖b‖_[m] := by
    refine lt_of_le_of_ne (weightedNorm_nonneg m b) (Ne.symm ?_)
    intro h
    exact hb0 ((weightedNorm_eq_zero_iff (fun i => hm i) b).mp h)
  rcases lt_or_ge K 0 with hK | hK
  · refine ⟨1, one_pos, fun x _ _ => ?_⟩
    have : 0 ≤ configMeasure m x := configMeasure_nonneg (fun i => (hm i).le) x
    linarith
  have hSpos : 0 < ∑ i, m i := sum_mass_pos (N := N) hm i
  have hC : 0 < Real.sqrt (∑ i, m i) + 1 := by positivity
  obtain ⟨ε₁, hε₁, h₁⟩ :=
    exists_lt_U_of_collision (N := N) hm hij hbij (2 * K / ‖b‖_[m])
  refine ⟨min ε₁ (‖b‖_[m] / 2 / (Real.sqrt (∑ i, m i) + 1)), lt_min hε₁ (by positivity),
    fun x hxnc hx => ?_⟩
  have hxε₁ : dist x b < ε₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hxε₂ : dist x b < ‖b‖_[m] / 2 / (Real.sqrt (∑ i, m i) + 1) :=
    lt_of_lt_of_le hx (min_le_right _ _)
  have hxn : ‖b‖_[m] / 2 ≤ ‖x‖_[m] := by
    have h2 : ‖x - b‖_[m] ≤ Real.sqrt (∑ i, m i) * dist x b := by
      calc ‖x - b‖_[m] ≤ Real.sqrt (∑ i, m i) * ‖x - b‖ :=
            weightedNorm_le_mul_norm (fun i => (hm i).le) (x - b)
        _ = Real.sqrt (∑ i, m i) * dist x b := by rw [dist_eq_norm]
    have h3 : Real.sqrt (∑ i, m i) * dist x b
        < Real.sqrt (∑ i, m i) * (‖b‖_[m] / 2 / (Real.sqrt (∑ i, m i) + 1)) :=
      mul_lt_mul_of_pos_left hxε₂ (Real.sqrt_pos.mpr hSpos)
    have h4 : Real.sqrt (∑ i, m i) * (‖b‖_[m] / 2 / (Real.sqrt (∑ i, m i) + 1))
        ≤ ‖b‖_[m] / 2 := by
      have h5 : Real.sqrt (∑ i, m i) * (Real.sqrt (∑ i, m i) + 1)⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ hC]
        linarith [Real.sqrt_nonneg (∑ i, m i)]
      calc Real.sqrt (∑ i, m i) * (‖b‖_[m] / 2 / (Real.sqrt (∑ i, m i) + 1))
          = (Real.sqrt (∑ i, m i) * (Real.sqrt (∑ i, m i) + 1)⁻¹) * (‖b‖_[m] / 2) := by
            rw [div_eq_mul_inv]; ring
        _ ≤ 1 * (‖b‖_[m] / 2) := mul_le_mul_of_nonneg_right h5 (by linarith [hbpos])
        _ = ‖b‖_[m] / 2 := one_mul _
    have h5 : |‖x‖_[m] - ‖b‖_[m]| ≤ ‖x - b‖_[m] :=
      abs_weightedNorm_sub_le (fun i => (hm i).le) x b
    have h6 : ‖b‖_[m] - ‖x‖_[m] ≤ ‖x - b‖_[m] := by linarith [(abs_le.mp h5).1]
    linarith
  have hxU : 2 * K / ‖b‖_[m] < U m x := h₁ x hxnc hxε₁
  have h2 : ‖x‖_[m] * (2 * K / ‖b‖_[m]) < ‖x‖_[m] * U m x :=
    mul_lt_mul_of_pos_left hxU (by linarith [hxn, hbpos])
  have h3 : K ≤ ‖x‖_[m] * (2 * K / ‖b‖_[m]) := by
    rw [mul_div_assoc', le_div_iff₀ hbpos]
    have h4 : ‖b‖_[m] ≤ 2 * ‖x‖_[m] := by linarith
    nlinarith [hK, h4]
  rw [configMeasure]
  linarith

/-! ## §5 Glueing curves, continuity of the configurational measure, growth -/

/-- The curve obtained by following `f` up to time `c` and then `g`, shifted. -/
noncomputable def glue (c : ℝ) (f g : ℝ → EN E N) : ℝ → EN E N :=
  fun t => if t ≤ c then f t else g (t - c)

@[simp] lemma glue_of_le {c : ℝ} {f g : ℝ → EN E N} {t : ℝ} (ht : t ≤ c) :
    glue c f g t = f t := if_pos ht

@[simp] lemma glue_of_gt {c : ℝ} {f g : ℝ → EN E N} {t : ℝ} (ht : c < t) :
    glue c f g t = g (t - c) := if_neg (not_le_of_gt ht)

/-- The action of a glued curve is the sum of the actions of its pieces. -/
theorem actionOn_glue {m : Fin N → ℝ} {h : ℝ} {c L : ℝ} (hc : 0 < c) (hL : 0 < L)
    (f g : ℝ → EN E N) :
    actionOn m h (glue (E := E) (N := N) c f g) 0 (c + L)
      = actionOn m h f 0 c + actionOn m h g 0 L := by
  change actionOn m h (fun t => if t ≤ c then f t else g (t - c)) 0 (c + L) = _
  exact actionOn_concat (m := m) (h := h) (γ₁ := f) (γ₂ := g) hc hL

/-- A glued curve is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_glue {f g : ℝ → EN E N} {a c b : ℝ} (hac : a ≤ c)
    (hcb : c ≤ b) (hfc : f c = g 0) (hf : AbsolutelyContinuousOnInterval f a c)
    (hg : AbsolutelyContinuousOnInterval g 0 (b - c)) :
    AbsolutelyContinuousOnInterval (glue (E := E) (N := N) c f g) a b := by
  have hgc : AbsolutelyContinuousOnInterval (fun t => g (t - c)) c b := by
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := g) (a := 0) (b := b - c) (c := 1) (d := -c) one_ne_zero hg
    have h1 : (0 - -c) / 1 = c := by ring
    have h2 : ((b - c) - -c) / 1 = b := by ring
    rw [h1, h2] at h
    simpa only [one_mul, sub_eq_add_neg] using h
  have hjoin : f c = (fun t => g (t - c)) c := by simpa using hfc
  have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_concat
    hac hcb hjoin hf hgc
  change AbsolutelyContinuousOnInterval (fun x : ℝ => if x ≤ c then f x else g (x - c)) a b at h
  exact h

/-- Two indices in `Fin N` as soon as `2 ≤ N`. -/
lemma exists_ne_fin {N : ℕ} (hN : 2 ≤ N) : ∃ i j : Fin N, i ≠ j :=
  ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
    intro h
    have : (0 : ℕ) = 1 := by simpa [Fin.ext_iff] using h
    omega⟩

/-- The configurational measure is continuous along a collision-free continuous curve. -/
lemma continuousOn_configMeasure_comp {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {γ : ℝ → EN E N}
    {a b : ℝ} (hcont : ContinuousOn γ (Set.Icc a b))
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t)) :
    ContinuousOn (fun t => configMeasure m (γ t)) (Set.Icc a b) := by
  have h1 : ContinuousOn (fun t => ‖γ t‖_[m]) (Set.Icc a b) :=
    (continuous_weightedNorm (fun i => (hm i).le)).comp_continuousOn hcont
  have h2 : ContinuousOn (fun t => U m (γ t)) (Set.Icc a b) :=
    continuousOn_U.comp hcont fun t ht => hnc t ht
  exact h1.mul h2

/-- A collision-free configuration of a curve with at least two bodies is non-zero. -/
lemma ne_zero_of_withoutCollisions {x : EN E N} (hN : 2 ≤ N) (hx : WithoutCollisions x) :
    x ≠ 0 := by
  obtain ⟨i, j, hij⟩ := exists_ne_fin hN
  intro h0
  have h := hx i j hij
  rw [r, h0] at h
  simp at h

/-- **Growth of the mass norm from the limit shape.** -/
lemma eventually_weightedNorm_le_mul {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {x : ℝ → EN E N} {b : EN E N} (h : Tendsto (fun t : ℝ => t⁻¹ • x t) atTop (𝓝 b)) :
    ∃ C T : ℝ, 0 < C ∧ ∀ t ≥ T, ‖x t‖_[m] ≤ C * t := by
  have hconv : Tendsto (fun t : ℝ => ‖t⁻¹ • x t - b‖_[m]) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t⁻¹ • x t - b) atTop (𝓝 (0 : EN E N)) := by
      have h2 : Tendsto (fun t : ℝ => t⁻¹ • x t - b) atTop (𝓝 (b - b)) :=
        h.sub tendsto_const_nhds
      simpa using h2
    have h3 := ((continuous_weightedNorm (fun i => (hm i).le)).tendsto (0 : EN E N)).comp h1
    have h0 : ‖(0 : EN E N)‖_[m] = 0 := by
      rw [weightedNorm_eq_norm_massScale (fun i => (hm i).le), massScale_zero, norm_zero]
    rw [h0] at h3
    simpa only [Function.comp_def, id_eq] using h3
  have hev : ∀ᶠ t : ℝ in atTop, ‖t⁻¹ • x t - b‖_[m] < 1 :=
    (tendsto_order.1 hconv).2 1 (by norm_num)
  rw [eventually_atTop] at hev
  obtain ⟨T₁, hT₁⟩ := hev
  refine ⟨‖b‖_[m] + 1, max T₁ 1, by linarith [weightedNorm_nonneg m b], fun t ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have htT : T₁ ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
  have h1 : ‖t⁻¹ • x t - b‖_[m] < 1 := hT₁ t htT
  have h2 : ‖t⁻¹ • x t‖_[m] ≤ ‖t⁻¹ • x t - b‖_[m] + ‖b‖_[m] := by
    have h3 := weightedNorm_sub_le (fun i => (hm i).le) (t⁻¹ • x t) b 0
    rwa [sub_zero, sub_zero] at h3
  have h4 : ‖t⁻¹ • x t‖_[m] = t⁻¹ * ‖x t‖_[m] := by
    rw [weightedNorm_smul (fun i => (hm i).le), abs_of_pos (inv_pos.mpr ht0)]
  rw [h4] at h2
  have h5 : t⁻¹ * ‖x t‖_[m] < ‖b‖_[m] + 1 := by linarith
  calc ‖x t‖_[m] = t * (t⁻¹ * ‖x t‖_[m]) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ht0), one_mul]
    _ ≤ t * (‖b‖_[m] + 1) := (mul_lt_mul_of_pos_left h5 ht0).le
    _ = (‖b‖_[m] + 1) * t := by ring


/-! ## §6 The integral comparison with the homothetic curve -/

/-- The mass norm is positive at a non-zero configuration. -/
lemma weightedNorm_pos {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {x : EN E N} (hx : x ≠ 0) :
    0 < ‖x‖_[m] := by
  refine lt_of_le_of_ne (weightedNorm_nonneg m x) (Ne.symm ?_)
  intro h
  exact hx ((weightedNorm_eq_zero_iff hm x).mp h)

/-- **The action of a minimiser dominates the action of the homothetic curve plus the divergence
term.**  On `[T₀, T_k]` the configurational measure along `γ` stays above `2μ(a)` and above `3μ(a)`
on the sub-interval `[T₀, T]`; the homothetic curve `t ↦ (ρ(t)/ρ(T_k)) • γ(T_k)` has the same radial
function `ρ` as `γ`, hence the same radial kinetic energy, but potential energy `2μ(a)/ρ`; the
difference of the potential energies is at least `μ(a)/ρ ≥ μ(a)/(C t)` on `[T₀, T]`. -/
theorem actionOn_ge_homothetic_add {m : Fin N → ℝ} {h : ℝ} {a : EN E N}
    {γ : ℝ → EN E N} {τ T₀ Tk T C : ℝ}
    (hN : 2 ≤ N) (hm : ∀ i, 0 < m i) (hh : 0 ≤ h) (hT₀ : 0 < T₀) (hC : 0 < C)
    (hμa : 0 ≤ configMeasure m a)
    (hT0Tk : T₀ < Tk) (hT₀T : T₀ ≤ T) (hTTk : T ≤ Tk) (hTkτ : Tk < τ)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hnc : ∀ t ∈ Set.Icc T₀ τ, WithoutCollisions (γ t))
    (hfin : actionOn m h γ T₀ Tk < ⊤)
    (h2 : ∀ t ∈ Set.Icc T₀ Tk, 2 * configMeasure m a ≤ configMeasure m (γ t))
    (hTk : configMeasure m (γ Tk) = 2 * configMeasure m a)
    (h3 : ∀ t ∈ Set.Icc T₀ T, 3 * configMeasure m a ≤ configMeasure m (γ t))
    (hρC : ∀ t ∈ Set.Icc T₀ T, ‖γ t‖_[m] ≤ C * t) :
    actionOn m h (homothetic (E := E) (N := N) (fun t => ‖γ t‖_[m]) (‖γ Tk‖_[m]) (γ Tk)) T₀ Tk
        + ENNReal.ofReal ((configMeasure m a / C) * (Real.log T - Real.log T₀))
      ≤ actionOn m h γ T₀ Tk := by
  classical
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hT0Tk_le : T₀ ≤ Tk := hT0Tk.le
  have hT₀τ : T₀ < τ := lt_of_lt_of_le hT0Tk hTkτ.le
  have hTτ : T < τ := lt_of_le_of_lt hTTk hTkτ
  have hT0T_le : T₀ ≤ T := hT₀T
  -- positivity of the radial function
  have hρpos : ∀ t ∈ Set.Icc T₀ τ, 0 < ‖γ t‖_[m] := fun t ht =>
    weightedNorm_pos hm (ne_zero_of_withoutCollisions hN (hnc t ht))
  have hρTk : 0 < ‖γ Tk‖_[m] := hρpos Tk ⟨hT0Tk.le, hTkτ.le⟩
  have hγTk_nc : WithoutCollisions (γ Tk) := hnc Tk ⟨hT0Tk.le, hTkτ.le⟩
  -- the homothetic curve
  set ĥ : ℝ → EN E N := homothetic (fun t => ‖γ t‖_[m]) (‖γ Tk‖_[m]) (γ Tk) with hĥdef
  have hĥnc : ∀ t ∈ Set.Icc T₀ Tk, WithoutCollisions (ĥ t) := by
    intro t ht
    refine withoutCollisions_homothetic hγTk_nc ?_
    exact div_pos (hρpos t ⟨ht.1, le_trans ht.2 hTkτ.le⟩) hρTk
  -- `ρ = ‖γ ·‖` is absolutely continuous on the relevant intervals
  have hρac : AbsolutelyContinuousOnInterval (fun t => ‖γ t‖_[m]) T₀ τ := by
    refine absolutelyContinuousOnInterval_weightedNorm_comp hm0 (hac.mono ?_)
    rw [uIcc_of_le hT₀τ.le, uIcc_of_le (by linarith : (0:ℝ) ≤ τ)]
    exact Set.Icc_subset_Icc (le_of_lt hT₀) le_rfl
  -- the real integral form of the action of `γ`
  have hacTk : AbsolutelyContinuousOnInterval γ T₀ Tk := by
    refine hac.mono ?_
    rw [uIcc_of_le hT0Tk_le, uIcc_of_le (by linarith : (0:ℝ) ≤ τ)]
    exact Set.Icc_subset_Icc (le_of_lt hT₀) hTkτ.le
  have hncTk : ∀ t ∈ Set.Icc T₀ Tk, WithoutCollisions (γ t) :=
    fun t ht => hnc t ⟨ht.1, le_trans ht.2 hTkτ.le⟩
  have hAγ : actionOn m h γ T₀ Tk
      = ∫⁻ t in Set.Ioc T₀ Tk, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)) := by
    have hint : Integrable (fun t => lagR m h (γ t) (deriv γ t))
        (volume.restrict (Set.Ioc T₀ Tk)) :=
      integrable_lagR_of_actionOn_lt_top hT0Tk_le hm0 hh hacTk hncTk hfin
    have hnn : ∀ t, 0 ≤ lagR m h (γ t) (deriv γ t) := by
      intro t
      have h1 : 0 ≤ kinetic m (deriv γ t) := kinetic_nonneg m hm0 (deriv γ t)
      have h2 : 0 ≤ U m (γ t) := U_nonneg hm0 (γ t)
      rw [lagR, kinetic] at *
      linarith
    rw [actionOn_eq_ofReal_integral_lagR hT0Tk_le hm0 hh hacTk hncTk hfin,
      intervalIntegral.integral_of_le hT0Tk_le]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall hnn)
  have hAĥ : actionOn m h ĥ T₀ Tk
      = ∫⁻ t in Set.Ioc T₀ Tk, ENNReal.ofReal (lagR m h (ĥ t) (deriv ĥ t)) := by
    unfold actionOn
    exact setLIntegral_congr_fun measurableSet_Ioc fun t ht =>
      lagrangian_eq_ofReal_lagR (hĥnc t ⟨ht.1.le, ht.2⟩)
  -- the pointwise estimate
  have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioc T₀ Tk)),
      ENNReal.ofReal (lagR m h (ĥ t) (deriv ĥ t))
        + ENNReal.ofReal (if t ∈ Set.Ioc T₀ T then configMeasure m a / (C * t) else 0)
      ≤ ENNReal.ofReal (lagR m h (γ t) (deriv γ t)) := by
    have h1 : ∀ᵐ t ∂(volume.restrict (Set.Ioc T₀ Tk)),
        |deriv (fun s => ‖γ s‖_[m]) t| ≤ ‖deriv γ t‖_[m] :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (fun x hx => show x ∈ Set.Ioc (0:ℝ) τ from
          ⟨lt_of_lt_of_le hT₀ hx.1.le, le_trans hx.2 hTkτ.le⟩)
        (ae_deriv_weightedNorm_le hm hac)
    have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioc T₀ Tk)),
        DifferentiableAt ℝ (fun s => ‖γ s‖_[m]) t := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine hρac.ae_differentiableAt.mono (fun t ht hmem => ht ?_)
      rw [uIcc_of_le hT₀τ.le]
      exact ⟨hmem.1.le, le_trans hmem.2 hTkτ.le⟩
    filter_upwards [h1, hdiff, MeasureTheory.self_mem_ae_restrict measurableSet_Ioc]
      with t hd1 hd2 hmem
    have htIcc : t ∈ Set.Icc T₀ Tk := ⟨hmem.1.le, hmem.2⟩
    have htτ : t ∈ Set.Icc T₀ τ := ⟨hmem.1.le, le_trans hmem.2 hTkτ.le⟩
    have hρt : 0 < ‖γ t‖_[m] := hρpos t htτ
    have hkin : kinetic m (deriv ĥ t) = (1 / 2) * (deriv (fun s => ‖γ s‖_[m]) t) ^ 2 := by
      rw [hĥdef]
      rw [kinetic_deriv_homothetic hd2, kinetic_eq_half_weightedNorm_sq hm0]
      field_simp
    have hUĥ : U m (ĥ t) = 2 * configMeasure m a / ‖γ t‖_[m] := by
      rw [hĥdef, homothetic_apply, U_smul, abs_of_pos (div_pos hρt hρTk)]
      have h4 : ‖γ Tk‖_[m] * U m (γ Tk) = 2 * configMeasure m a := by
        rw [← hTk]; rfl
      field_simp
      linarith [h4]
    have hUγ : U m (γ t) = configMeasure m (γ t) / ‖γ t‖_[m] := by
      rw [configMeasure]; field_simp
    have hg : (if t ∈ Set.Ioc T₀ T then configMeasure m a / (C * t) else 0)
        ≤ (configMeasure m (γ t) - 2 * configMeasure m a) / ‖γ t‖_[m] := by
      by_cases ht : t ∈ Set.Ioc T₀ T
      · rw [if_pos ht]
        have h3' : 3 * configMeasure m a ≤ configMeasure m (γ t) := h3 t ⟨ht.1.le, ht.2⟩
        have hρCt : ‖γ t‖_[m] ≤ C * t := hρC t ⟨ht.1.le, ht.2⟩
        have hCt : 0 < C * t := mul_pos hC (lt_trans hT₀ ht.1)
        have hA : configMeasure m a / (C * t) ≤ configMeasure m a / ‖γ t‖_[m] := by
          rw [div_le_div_iff₀ hCt hρt]
          nlinarith [hμa, hρCt]
        have hB : configMeasure m a / ‖γ t‖_[m]
            ≤ (configMeasure m (γ t) - 2 * configMeasure m a) / ‖γ t‖_[m] := by
          rw [div_le_div_iff₀ hρt hρt]
          nlinarith [h3']
        linarith
      · rw [if_neg ht]
        have h3' : 2 * configMeasure m a ≤ configMeasure m (γ t) := h2 t htIcc
        exact div_nonneg (by linarith) hρt.le
    have hkinγ : (1 / 2) * (deriv (fun s => ‖γ s‖_[m]) t) ^ 2 ≤ kinetic m (deriv γ t) := by
      have h3' : (deriv (fun s => ‖γ s‖_[m]) t) ^ 2 ≤ (‖deriv γ t‖_[m]) ^ 2 := by
        nlinarith [abs_nonneg (deriv (fun s => ‖γ s‖_[m]) t), hd1,
          sq_abs (deriv (fun s => ‖γ s‖_[m]) t)]
      rw [kinetic_eq_half_weightedNorm_sq hm0]
      linarith
    have hreal : lagR m h (ĥ t) (deriv ĥ t)
        + (if t ∈ Set.Ioc T₀ T then configMeasure m a / (C * t) else 0)
        ≤ lagR m h (γ t) (deriv γ t) := by
      have h1' : lagR m h (ĥ t) (deriv ĥ t) = kinetic m (deriv ĥ t) + U m (ĥ t) + h := by
        rw [lagR, kinetic]
      have h2' : lagR m h (γ t) (deriv γ t) = kinetic m (deriv γ t) + U m (γ t) + h := by
        rw [lagR, kinetic]
      rw [h1', h2', hkin, hUĥ, hUγ]
      have hg' : (if t ∈ Set.Ioc T₀ T then configMeasure m a / (C * t) else 0) * ‖γ t‖_[m]
          ≤ configMeasure m (γ t) - 2 * configMeasure m a := by
        rw [le_div_iff₀ hρt] at hg
        exact hg
      have hmult : ((1 / 2) * (deriv (fun s => ‖γ s‖_[m]) t) ^ 2
            + 2 * configMeasure m a / ‖γ t‖_[m]
            + h + (if t ∈ Set.Ioc T₀ T then configMeasure m a / (C * t) else 0)) * ‖γ t‖_[m]
          ≤ (kinetic m (deriv γ t) + configMeasure m (γ t) / ‖γ t‖_[m] + h) * ‖γ t‖_[m] := by
        have h1 : ((1 / 2) * (deriv (fun s => ‖γ s‖_[m]) t) ^ 2) * ‖γ t‖_[m]
            ≤ kinetic m (deriv γ t) * ‖γ t‖_[m] :=
          mul_le_mul_of_nonneg_right hkinγ hρt.le
        have h2 : (2 * configMeasure m a / ‖γ t‖_[m]) * ‖γ t‖_[m] = 2 * configMeasure m a := by
          field_simp
        have h3 : (configMeasure m (γ t) / ‖γ t‖_[m]) * ‖γ t‖_[m]
            = configMeasure m (γ t) := by field_simp
        nlinarith [h1, hg', h2, h3, hρt]
      exact le_of_mul_le_mul_right hmult hρt
    have hnn1 : 0 ≤ lagR m h (ĥ t) (deriv ĥ t) := by
      have h3 : 0 ≤ kinetic m (deriv ĥ t) := kinetic_nonneg m hm0 _
      have h4 : 0 ≤ U m (ĥ t) := U_nonneg hm0 _
      rw [lagR, kinetic] at *
      linarith
    have hnn2 : 0 ≤ (if t ∈ Set.Ioc T₀ T then configMeasure m a / (C * t) else 0) := by
      by_cases ht : t ∈ Set.Ioc T₀ T
      · rw [if_pos ht]
        exact div_nonneg hμa (mul_pos hC (lt_trans hT₀ ht.1)).le
      · rw [if_neg ht]
    rw [← ENNReal.ofReal_add hnn1 hnn2]
    exact ENNReal.ofReal_le_ofReal hreal
  -- the indicator integral
  set g : ℝ → ℝ := fun t => if t ∈ Set.Ioc T₀ T then configMeasure m a / (C * t) else 0 with hgdef
  have hg_meas : AEMeasurable (fun t => ENNReal.ofReal (g t))
      (volume.restrict (Set.Ioc T₀ Tk)) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    refine Measurable.aemeasurable ?_
    refine Measurable.ite measurableSet_Ioc ?_ measurable_const
    exact measurable_const.div (measurable_const.mul measurable_id)
  -- the integral of the indicator
  have hg_int : ∫⁻ t in Set.Ioc T₀ Tk, ENNReal.ofReal (g t)
      = ENNReal.ofReal ((configMeasure m a / C) * (Real.log T - Real.log T₀)) := by
    have hsplit : Set.Ioc T₀ Tk = Set.Ioc T₀ T ∪ Set.Ioc T Tk :=
      (Set.Ioc_union_Ioc_eq_Ioc hT0T_le hTTk).symm
    rw [hsplit, lintegral_union measurableSet_Ioc
      (Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le_of_gt hx'.1))]
    have hzero : ∫⁻ t in Set.Ioc T Tk, ENNReal.ofReal (g t) = 0 := by
      rw [show (∫⁻ t in Set.Ioc T Tk, ENNReal.ofReal (g t))
          = ∫⁻ _t in Set.Ioc T Tk, (0 : ℝ≥0∞) from
        setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_]
      · simp
      · have ht' : t ∉ Set.Ioc T₀ T := fun hmem => absurd hmem.2 (not_le_of_gt ht.1)
        rw [hgdef]
        simp only
        rw [if_neg ht', ENNReal.ofReal_zero]
    rw [hzero, add_zero]
    have hgT : ∀ t ∈ Set.Ioc T₀ T, g t = configMeasure m a / (C * t) := by
      intro t ht
      rw [hgdef]
      exact if_pos ht
    rw [show (∫⁻ t in Set.Ioc T₀ T, ENNReal.ofReal (g t))
        = ∫⁻ t in Set.Ioc T₀ T, ENNReal.ofReal (configMeasure m a / (C * t)) from
      setLIntegral_congr_fun measurableSet_Ioc fun t ht => by rw [hgT t ht]]
    have hcont : ContinuousOn (fun t : ℝ => configMeasure m a / (C * t)) (Set.Icc T₀ T) := by
      refine ContinuousOn.div (continuousOn_const) (continuousOn_const.mul continuousOn_id)
        fun t ht => ?_
      exact ne_of_gt (mul_pos hC (lt_of_lt_of_le hT₀ ht.1))
    have hint : IntegrableOn (fun t : ℝ => configMeasure m a / (C * t)) (Set.Ioc T₀ T) :=
      (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc T₀ T)]
        (fun t : ℝ => configMeasure m a / (C * t)) := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2
        (Filter.Eventually.of_forall fun t ht => ?_)
      exact div_nonneg hμa (le_of_lt (mul_pos hC (lt_trans hT₀ ht.1)))
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn,
      ← intervalIntegral.integral_of_le hT0T_le,
      Commons.MeasureTheory.Integral.integral_const_div_mul_eq hT₀ hT0T_le]
  calc actionOn m h ĥ T₀ Tk
        + ENNReal.ofReal ((configMeasure m a / C) * (Real.log T - Real.log T₀))
      = ∫⁻ t in Set.Ioc T₀ Tk,
          (ENNReal.ofReal (lagR m h (ĥ t) (deriv ĥ t)) + ENNReal.ofReal (g t)) := by
        rw [hAĥ, lintegral_add_right' _ hg_meas, hg_int]
    _ ≤ ∫⁻ t in Set.Ioc T₀ Tk, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)) :=
        MeasureTheory.lintegral_mono_ae hpt
    _ = actionOn m h γ T₀ Tk := hAγ.symm

/-! ## §7 The competitor curve -/

/-- **The competitor curve has strictly smaller action.**  Assuming the configurational measure
blows up at the limit shape, the minimiser `γ` can be beaten: replacing the piece `[T₀, Tk]` by a
minimiser to the rescaled configuration `z` and the homothetic curve through it saves at least the
divergence term `X = (μ(a)/C)(log T - log T₀)`, which dominates the cost `A(δ)` of the first
replacement. -/
theorem exists_competitor_action_lt {m : Fin N → ℝ} {h : ℝ} {a : EN E N} {α β C R : ℝ}
    {γ : ℝ → EN E N} {τ T₀ Tk T : ℝ}
    (hdim : 2 ≤ Module.finrank ℝ E) (hN : 2 ≤ N)
    (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hμa : 0 < configMeasure m a) (hC : 0 < C) (hT₀ : 0 < T₀)
    (hα : 0 < α) (hβ : 0 < β)
    (hest : ∀ x z : EN E N, actionPot m h x z ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2)))
    (hτ0 : 0 < τ) (hT0Tk : T₀ < Tk) (hT₀T : T₀ ≤ T) (hTTk : T ≤ Tk) (hTkτ : Tk < τ)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hmin : IsHMinimizer m h γ 0 τ)
    (hnc : ∀ t ∈ Set.Icc T₀ τ, WithoutCollisions (γ t))
    (h2 : ∀ t ∈ Set.Icc T₀ Tk, 2 * configMeasure m a ≤ configMeasure m (γ t))
    (hTk : configMeasure m (γ Tk) = 2 * configMeasure m a)
    (h3 : ∀ t ∈ Set.Icc T₀ T, 3 * configMeasure m a ≤ configMeasure m (γ t))
    (hρC : ∀ t ∈ Set.Icc T₀ T, ‖γ t‖_[m] ≤ C * t)
    (hR : ‖γ T₀ - (‖γ T₀‖_[m] / ‖γ Tk‖_[m]) • γ Tk‖ ≤ R)
    (hX : Real.sqrt (α * R + h * β * R ^ 2)
        < (configMeasure m a / C) * (Real.log T - Real.log T₀)) :
    ∃ (S : ℝ) (η : ℝ → EN E N), 0 < S ∧ η 0 = γ 0 ∧ η S = γ τ ∧
      AbsolutelyContinuousOnInterval η 0 S ∧ actionOn m h η 0 S < actionOn m h γ 0 τ := by
  classical
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hTkτ' : Tk ≤ τ := hTkτ.le
  have hT₀τ : T₀ < τ := lt_of_lt_of_le hT0Tk hTkτ'
  have hTτ : T < τ := lt_of_le_of_lt hTTk hTkτ
  -- positivity and collision freeness of the two configurations involved
  have hxnc : WithoutCollisions (γ T₀) := hnc T₀ ⟨le_rfl, hT₀τ.le⟩
  have hγTknc : WithoutCollisions (γ Tk) := hnc Tk ⟨hT0Tk.le, hTkτ'⟩
  have hρT₀ : 0 < ‖γ T₀‖_[m] :=
    weightedNorm_pos hm (ne_zero_of_withoutCollisions hN hxnc)
  have hρTk : 0 < ‖γ Tk‖_[m] :=
    weightedNorm_pos hm (ne_zero_of_withoutCollisions hN hγTknc)
  -- the rescaled configuration `z`
  have hznc : WithoutCollisions ((‖γ T₀‖_[m] / ‖γ Tk‖_[m]) • γ Tk) :=
    withoutCollisions_smul hγTknc (ne_of_gt (div_pos hρT₀ hρTk))
  have hμz : configMeasure m ((‖γ T₀‖_[m] / ‖γ Tk‖_[m]) • γ Tk) = 2 * configMeasure m a := by
    rw [configMeasure_smul hm0 (div_pos hρT₀ hρTk)]
    exact hTk
  -- the two configurations differ
  have hxne : γ T₀ ≠ (‖γ T₀‖_[m] / ‖γ Tk‖_[m]) • γ Tk := by
    intro heq
    have h4 : 2 * configMeasure m a ≤ configMeasure m (γ T₀) := h2 T₀ ⟨le_rfl, hT0Tk.le⟩
    have h5 : 3 * configMeasure m a ≤ configMeasure m (γ T₀) := h3 T₀ ⟨le_rfl, hT₀T⟩
    rw [heq, hμz] at h4 h5
    linarith
  -- Tonelli: a minimiser `δ` from `γ T₀` to `z`
  obtain ⟨s, hs, δ, hδ0, hδs, hδac, hδmin⟩ :=
    exists_minimizer_of_avoiding hm hh hdim hxne hxnc hznc
  -- its action is bounded by the Hölder estimate
  have hδle : actionOn m h δ 0 s ≤ ENNReal.ofReal (Real.sqrt (α * R + h * β * R ^ 2)) := by
    calc actionOn m h δ 0 s = actionPot m h (γ T₀) ((‖γ T₀‖_[m] / ‖γ Tk‖_[m]) • γ Tk) := hδmin
      _ ≤ ENNReal.ofReal (Real.sqrt (α * ‖γ T₀ - (‖γ T₀‖_[m] / ‖γ Tk‖_[m]) • γ Tk‖
            + h * β * ‖γ T₀ - (‖γ T₀‖_[m] / ‖γ Tk‖_[m]) • γ Tk‖ ^ 2)) := hest _ _
      _ ≤ ENNReal.ofReal (Real.sqrt (α * R + h * β * R ^ 2)) := by
          refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
          have h6 : 0 ≤ R := le_trans (norm_nonneg _) hR
          have h7 : ‖γ T₀ - (‖γ T₀‖_[m] / ‖γ Tk‖_[m]) • γ Tk‖ ^ 2 ≤ R ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hR 2
          refine add_le_add (mul_le_mul_of_nonneg_left hR hα.le) ?_
          exact mul_le_mul_of_nonneg_left h7 (mul_nonneg hh.le hβ.le)
  have hXpos : 0 < (configMeasure m a / C) * (Real.log T - Real.log T₀) :=
    lt_of_le_of_lt (Real.sqrt_nonneg _) hX
  have hδlt : actionOn m h δ 0 s
      < ENNReal.ofReal ((configMeasure m a / C) * (Real.log T - Real.log T₀)) :=
    lt_of_le_of_lt hδle ((ENNReal.ofReal_lt_ofReal_iff hXpos).mpr hX)
  -- ── finiteness of the actions involved ──────────────────────────────────────
  have hmin_eq : actionOn m h γ 0 τ = actionPot m h (γ 0) (γ τ) := hmin
  have hτfin : actionOn m h γ 0 τ < ⊤ :=
    lt_of_le_of_lt hmin_eq.le (lt_of_le_of_lt (hest (γ 0) (γ τ)) ENNReal.ofReal_lt_top)
  have hsum : actionOn m h γ 0 τ = actionOn m h γ 0 T₀ + actionOn m h γ T₀ τ :=
    actionOn_add γ hT₀.le hT₀τ.le
  have hfin0 : actionOn m h γ 0 T₀ < ⊤ := by
    have hh := hτfin; rw [hsum] at hh; exact (ENNReal.add_lt_top.mp hh).1
  have hfinT0τ : actionOn m h γ T₀ τ < ⊤ := by
    have hh := hτfin; rw [hsum] at hh; exact (ENNReal.add_lt_top.mp hh).2
  have hT0τsplit : actionOn m h γ T₀ τ = actionOn m h γ T₀ Tk + actionOn m h γ Tk τ :=
    actionOn_add γ hT0Tk.le hTkτ'
  have hfinT0Tk : actionOn m h γ T₀ Tk < ⊤ := by
    have hh := hfinT0τ; rw [hT0τsplit] at hh; exact (ENNReal.add_lt_top.mp hh).1
  have hfinTkTτ : actionOn m h γ Tk τ < ⊤ := by
    have hh := hfinT0τ; rw [hT0τsplit] at hh; exact (ENNReal.add_lt_top.mp hh).2
  -- ── the homothetic curve and its comparison with `γ` ────────────────────────
  set ĥ : ℝ → EN E N := homothetic (fun t => ‖γ t‖_[m]) (‖γ Tk‖_[m]) (γ Tk) with hĥdef
  have hAhom : actionOn m h ĥ T₀ Tk
      + ENNReal.ofReal ((configMeasure m a / C) * (Real.log T - Real.log T₀))
      ≤ actionOn m h γ T₀ Tk := by
    rw [hĥdef]
    exact actionOn_ge_homothetic_add hN hm hh.le hT₀ hC hμa.le hT0Tk hT₀T hTTk hTkτ hac hnc
      hfinT0Tk h2 hTk h3 hρC
  have hAhne : actionOn m h ĥ T₀ Tk ≠ ⊤ :=
    ne_of_lt (ENNReal.add_lt_top.mp (lt_of_le_of_lt hAhom hfinT0Tk)).1
  -- ── the pieces of the competitor curve ──────────────────────────────────────
  have hTk'T₀ : 0 < Tk - T₀ := by linarith
  have hτTk : 0 < τ - Tk := by linarith
  have hτT₀ : 0 < τ - T₀ := by linarith
  have hL : 0 < s + (τ - T₀) := by linarith
  set g₀ : ℝ → EN E N := fun u => ĥ (u + T₀) with hg₀def
  set g₁ : ℝ → EN E N := fun u => γ (u + Tk) with hg₁def
  set rest : ℝ → EN E N := glue (Tk - T₀) g₀ g₁ with hrestdef
  set g₂ : ℝ → EN E N := glue s δ rest with hg₂def
  set η : ℝ → EN E N := glue T₀ γ g₂ with hηdef
  set S : ℝ := T₀ + (s + (τ - T₀)) with hSdef
  -- ── absolute continuity of the pieces ───────────────────────────────────────
  have hacT0 : AbsolutelyContinuousOnInterval γ 0 T₀ := by
    refine hac.mono ?_
    rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ T₀), uIcc_of_le (by linarith : (0 : ℝ) ≤ τ)]
    exact Set.Icc_subset_Icc le_rfl hT₀τ.le
  have hacTkτ : AbsolutelyContinuousOnInterval γ Tk τ := by
    refine hac.mono ?_
    rw [uIcc_of_le hTkτ', uIcc_of_le (by linarith : (0 : ℝ) ≤ τ)]
    exact Set.Icc_subset_Icc (le_of_lt (lt_of_lt_of_le hT₀ hT0Tk.le)) le_rfl
  have hρac : AbsolutelyContinuousOnInterval (fun t => ‖γ t‖_[m]) T₀ Tk := by
    refine absolutelyContinuousOnInterval_weightedNorm_comp hm0 (hac.mono ?_)
    rw [uIcc_of_le hT0Tk.le, uIcc_of_le (by linarith : (0 : ℝ) ≤ τ)]
    exact Set.Icc_subset_Icc (le_of_lt hT₀) hTkτ'
  have hĥac : AbsolutelyContinuousOnInterval ĥ T₀ Tk := by
    rw [hĥdef]
    exact homothetic_absolutelyContinuous hρac
  have hg₀ac : AbsolutelyContinuousOnInterval g₀ 0 (Tk - T₀) := by
    rw [hg₀def]
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := ĥ) (a := T₀) (b := Tk) (c := 1) (d := T₀) one_ne_zero hĥac
    simpa only [one_mul, sub_self, zero_div, div_one] using h
  have hg₁ac : AbsolutelyContinuousOnInterval g₁ 0 (τ - Tk) := by
    rw [hg₁def]
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := γ) (a := Tk) (b := τ) (c := 1) (d := Tk) one_ne_zero hacTkτ
    simpa only [one_mul, sub_self, zero_div, div_one] using h
  have hrestac : AbsolutelyContinuousOnInterval rest 0 (τ - T₀) := by
    rw [hrestdef]
    refine absolutelyContinuousOnInterval_glue (a := 0) (c := Tk - T₀) (b := τ - T₀)
      (sub_nonneg.mpr hT0Tk.le) (by linarith) ?_ hg₀ac ?_
    · rw [hg₀def, hg₁def]
      simp only [zero_add]
      rw [show (Tk - T₀) + T₀ = Tk by ring, hĥdef, homothetic_apply, div_self (ne_of_gt hρTk),
        one_smul]
    · have h1 : (τ - T₀) - (Tk - T₀) = τ - Tk := by ring
      rw [h1]; exact hg₁ac
  have hg₂ac : AbsolutelyContinuousOnInterval g₂ 0 (s + (τ - T₀)) := by
    rw [hg₂def]
    refine absolutelyContinuousOnInterval_glue (a := 0) (c := s) (b := s + (τ - T₀)) hs.le
      (by linarith) ?_ hδac ?_
    · rw [hδs]
      show (‖γ T₀‖_[m] / ‖γ Tk‖_[m]) • γ Tk = rest 0
      rw [hrestdef, glue_of_le (sub_nonneg.mpr hT0Tk.le), hg₀def]
      show (‖γ T₀‖_[m] / ‖γ Tk‖_[m]) • γ Tk = ĥ (0 + T₀)
      rw [zero_add, hĥdef, homothetic_apply]
    · have h1 : s + (τ - T₀) - s = τ - T₀ := by ring
      rw [h1]; exact hrestac
  have hηac : AbsolutelyContinuousOnInterval η 0 S := by
    rw [hηdef, hSdef]
    refine absolutelyContinuousOnInterval_glue (a := 0) (c := T₀) (b := T₀ + (s + (τ - T₀)))
      hT₀.le (by linarith) ?_ hacT0 ?_
    · rw [hg₂def]
      show γ T₀ = glue s δ rest 0
      rw [glue_of_le hs.le, hδ0]
    · have h1 : T₀ + (s + (τ - T₀)) - T₀ = s + (τ - T₀) := by ring
      rw [h1]; exact hg₂ac
  -- ── the endpoint values ─────────────────────────────────────────────────────
  have hη0 : η 0 = γ 0 := by rw [hηdef, glue_of_le hT₀.le]
  have hηS : η S = γ τ := by
    rw [hSdef, hηdef, glue_of_gt (show T₀ < T₀ + (s + (τ - T₀)) by linarith)]
    rw [show T₀ + (s + (τ - T₀)) - T₀ = s + (τ - T₀) by ring]
    change (glue s δ rest) (s + (τ - T₀)) = γ τ
    rw [glue_of_gt (show s < s + (τ - T₀) by linarith)]
    rw [show s + (τ - T₀) - s = τ - T₀ by ring]
    change (glue (Tk - T₀) g₀ g₁) (τ - T₀) = γ τ
    rw [glue_of_gt (show Tk - T₀ < τ - T₀ by linarith)]
    rw [show τ - T₀ - (Tk - T₀) = τ - Tk by ring]
    show γ ((τ - Tk) + Tk) = γ τ
    rw [show (τ - Tk) + Tk = τ by ring]
  -- ── the action of the competitor ────────────────────────────────────────────
  have hA1 : actionOn m h g₀ 0 (Tk - T₀) = actionOn m h ĥ T₀ Tk := by
    rw [hg₀def]
    exact actionOn_comp_add_const'
  have hA2 : actionOn m h g₁ 0 (τ - Tk) = actionOn m h γ Tk τ := by
    rw [hg₁def]
    exact actionOn_comp_add_const'
  have hrestA : actionOn m h rest 0 (τ - T₀)
      = actionOn m h g₀ 0 (Tk - T₀) + actionOn m h g₁ 0 (τ - Tk) := by
    have h := actionOn_glue (m := m) (h := h) (c := Tk - T₀) (L := τ - Tk) hTk'T₀ hτTk g₀ g₁
    rw [show (Tk - T₀) + (τ - Tk) = τ - T₀ by ring] at h
    rw [hrestdef]
    exact h
  have hg₂A : actionOn m h g₂ 0 (s + (τ - T₀))
      = actionOn m h δ 0 s + actionOn m h rest 0 (τ - T₀) := by
    have h := actionOn_glue (m := m) (h := h) (c := s) (L := τ - T₀) hs hτT₀ δ rest
    rw [hg₂def]
    exact h
  have hηA : actionOn m h η 0 S
      = actionOn m h γ 0 T₀ + actionOn m h g₂ 0 (s + (τ - T₀)) := by
    have h := actionOn_glue (m := m) (h := h) (c := T₀) (L := s + (τ - T₀)) hT₀ hL γ g₂
    rw [hηdef, hSdef]
    exact h
  -- ── the strict inequality ───────────────────────────────────────────────────
  have hkey : actionOn m h δ 0 s + actionOn m h ĥ T₀ Tk < actionOn m h γ T₀ Tk :=
    calc actionOn m h δ 0 s + actionOn m h ĥ T₀ Tk
        < ENNReal.ofReal ((configMeasure m a / C) * (Real.log T - Real.log T₀))
            + actionOn m h ĥ T₀ Tk := ENNReal.add_lt_add_right hAhne hδlt
      _ = actionOn m h ĥ T₀ Tk
            + ENNReal.ofReal ((configMeasure m a / C) * (Real.log T - Real.log T₀)) :=
          add_comm _ _
      _ ≤ actionOn m h γ T₀ Tk := hAhom
  have hinner : actionOn m h δ 0 s + (actionOn m h ĥ T₀ Tk + actionOn m h γ Tk τ)
      < actionOn m h γ T₀ Tk + actionOn m h γ Tk τ := by
    rw [← add_assoc]
    exact ENNReal.add_lt_add_right (ne_of_lt hfinTkTτ) hkey
  have houter : actionOn m h γ 0 T₀
        + (actionOn m h δ 0 s + (actionOn m h ĥ T₀ Tk + actionOn m h γ Tk τ))
      < actionOn m h γ 0 T₀ + (actionOn m h γ T₀ Tk + actionOn m h γ Tk τ) :=
    ENNReal.add_lt_add_left (ne_of_lt hfin0) hinner
  have hcomb : actionOn m h η 0 S
      = actionOn m h γ 0 T₀
        + (actionOn m h δ 0 s + (actionOn m h ĥ T₀ Tk + actionOn m h γ Tk τ)) := by
    rw [hηA, hg₂A, hrestA, hA1, hA2]
  have hcombγ : actionOn m h γ 0 τ
      = actionOn m h γ 0 T₀ + (actionOn m h γ T₀ Tk + actionOn m h γ Tk τ) := by
    rw [actionOn_add γ hT₀.le hT₀τ.le, actionOn_add γ hT0Tk.le hTkτ']
  refine ⟨S, η, ?_, hη0, hηS, hηac, ?_⟩
  · rw [hSdef]; linarith
  · rw [hcomb, hcombγ]
    exact houter

set_option maxHeartbeats 2000000

/-! ## §9 The limit shape has no collisions -/

/-- **The limit shape of the calibrating curve is collision free** (Maderna--Venturelli, §4.3
step 2).  If the `h`-minimisers `γ_k` from `γ 1` to `λ_k • a` (with `λ_k > 0`, `τ_k → ∞`) converge
uniformly on compacts to the calibrating curve `γ`, whose limit shape `t⁻¹ • γ t → b` is non-zero,
then the configurational measure `μ = ‖·‖_[m] · U` blows up at `b` (which forces the contradiction
with minimality through the competitor curve of `exists_competitor_action_lt`). -/
theorem withoutCollisions_of_limshape {m : Fin N → ℝ} {h : ℝ} {a b : EN E N}
    {γ : ℝ → EN E N} {lam τ : ℕ → ℝ} {γs : ℕ → ℝ → EN E N}
    {α β ε T₀ T C c R : ℝ}
    (hE : 2 ≤ Module.finrank ℝ E) (hN : 2 ≤ N) (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hM : MarchalProperty (E := E) m h)
    (ha_nc : WithoutCollisions a) (hμa : 0 < configMeasure m a) (hb0 : b ≠ 0)
    (hα : 0 < α) (hβ : 0 < β)
    (hest : ∀ x z : EN E N, actionPot m h x z ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2)))
    (hεpos : 0 < ε)
    (hεprop : ∀ x : EN E N, WithoutCollisions x → dist x b < ε →
      3 * configMeasure m a < configMeasure m x)
    (hT₀pos : 0 < T₀) (h1T₀ : (1 : ℝ) ≤ T₀) (hCaT₀ : 4 * (‖b‖ + 1) / ε ≤ T₀)
    (hshape4 : ∀ t ≥ T₀, dist (t⁻¹ • γ t) b < ε / 4)
    (hshape1 : ∀ t ≥ T₀, dist (t⁻¹ • γ t) b < 1)
    (hCpos : 0 < C) (hC : C = Real.sqrt (∑ i, m i) * (2 * ‖b‖ + 3))
    (hcpos : 0 < c) (hc : ∀ i, c ≤ m i)
    (hR : R = 2 * C * T₀ / Real.sqrt c)
    (hlam : ∀ k, 0 < lam k) (hτ : ∀ k, 0 < τ k)
    (h0 : ∀ k, γs k 0 = γ 1) (h1 : ∀ k, γs k (τ k) = lam k • a)
    (hac : ∀ k, AbsolutelyContinuousOnInterval (γs k) 0 (τ k))
    (hmin : ∀ k, IsHMinimizer m h (γs k) 0 (τ k))
    (hτtop : Tendsto τ atTop atTop)
    (hT₀T : T₀ < T)
    (hX : Real.sqrt (α * R + h * β * R ^ 2)
      < (configMeasure m a / C) * (Real.log T - Real.log T₀))
    (hconv : TendstoUniformlyOn (fun k => γs k) (fun t => γ (t + 1)) atTop (Set.Icc 0 T)) :
    WithoutCollisions b := by
  classical
  by_contra hb
  have hε4 : 0 < ε / 4 := by linarith
  have hTpos : 0 < T := lt_trans hT₀pos hT₀T
  have hT_gt : T₀ < T := hT₀T
  -- growth of the calibrating curve
  have hγbound : ∀ t ≥ T₀, ‖γ (t + 1)‖ ≤ (‖b‖ + 1) * (t + 1) := by
    intro t ht
    have h5 : dist ((t + 1)⁻¹ • γ (t + 1)) b < 1 := hshape1 (t + 1) (by linarith)
    have h6 : ‖(t + 1)⁻¹ • γ (t + 1)‖ ≤ ‖b‖ + 1 := by
      have h7 : |‖(t + 1)⁻¹ • γ (t + 1)‖ - ‖b‖| ≤ dist ((t + 1)⁻¹ • γ (t + 1)) b := by
        rw [dist_eq_norm]
        exact abs_norm_sub_norm_le _ _
      linarith [(abs_le.mp h7).2, h5]
    calc ‖γ (t + 1)‖ = (t + 1) * ‖(t + 1)⁻¹ • γ (t + 1)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith : (0 : ℝ) < t + 1)),
            mul_inv_cancel_left₀ (by linarith : (t + 1) ≠ 0)]
      _ ≤ (t + 1) * (‖b‖ + 1) := mul_le_mul_of_nonneg_left h6 (by linarith)
      _ = (‖b‖ + 1) * (t + 1) := by ring
  -- the shape bound for the shifted curve
  have hshift_ε : ∀ t ≥ T₀, dist (t⁻¹ • γ (t + 1)) b < ε / 2 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hT₀pos ht
    have hdiff : 0 < t⁻¹ - (t + 1)⁻¹ := by
      rw [inv_sub_inv (by linarith) (by linarith)]
      exact div_pos (by linarith) (by positivity)
    have h3 : ‖(t⁻¹ - (t + 1)⁻¹) • γ (t + 1)‖ ≤ ε / 4 := by
      have h4 : (t⁻¹ - (t + 1)⁻¹) * (‖b‖ + 1) * (t + 1) = (‖b‖ + 1) / t := by
        rw [inv_sub_inv (by linarith) (by linarith)]
        field_simp
        ring
      calc ‖(t⁻¹ - (t + 1)⁻¹) • γ (t + 1)‖
          = (t⁻¹ - (t + 1)⁻¹) * ‖γ (t + 1)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hdiff]
        _ ≤ (t⁻¹ - (t + 1)⁻¹) * ((‖b‖ + 1) * (t + 1)) :=
            mul_le_mul_of_nonneg_left (hγbound t ht) hdiff.le
        _ = (‖b‖ + 1) / t := by rw [← h4]; ring
        _ ≤ (‖b‖ + 1) / T₀ := by
            rw [div_le_div_iff₀ ht0 hT₀pos]
            exact mul_le_mul_of_nonneg_left ht (by positivity)
        _ ≤ ε / 4 := by
            rw [div_le_div_iff₀ hT₀pos (by norm_num : (0 : ℝ) < 4)]
            have h8 := (div_le_iff₀ hεpos).mp hCaT₀
            linarith
    have h2 : dist ((t + 1)⁻¹ • γ (t + 1)) b < ε / 4 := hshape4 (t + 1) (by linarith)
    calc dist (t⁻¹ • γ (t + 1)) b
        ≤ dist (t⁻¹ • γ (t + 1)) ((t + 1)⁻¹ • γ (t + 1))
          + dist ((t + 1)⁻¹ • γ (t + 1)) b := dist_triangle _ _ _
      _ = ‖(t⁻¹ - (t + 1)⁻¹) • γ (t + 1)‖ + dist ((t + 1)⁻¹ • γ (t + 1)) b := by
          rw [dist_eq_norm, ← sub_smul]
      _ < ε / 4 + ε / 4 := add_lt_add_of_le_of_lt h3 h2
      _ = ε / 2 := by ring
  -- the constants of the growth and Hölder estimates
  have hSpos : 0 < ∑ i, m i := sum_mass_pos hm ⟨0, by omega⟩
  set Ce : ℝ := 2 * ‖b‖ + 3 with hCedef
  have hnorm_le : ∀ y : EN E N, ‖y‖ ≤ ‖y‖_[m] / Real.sqrt c := by
    intro y
    have hsq : ‖y‖ ^ 2 * c ≤ (‖y‖_[m]) ^ 2 := by
      rw [weightedNorm_sq (fun i => (hm i).le) y, PiLp.norm_eq_of_L2]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      calc ‖y.ofLp i‖ ^ 2 * c ≤ ‖y.ofLp i‖ ^ 2 * m i :=
            mul_le_mul_of_nonneg_left (hc i) (sq_nonneg _)
        _ = m i * ‖y.ofLp i‖ ^ 2 := by ring
    have h2 : ‖y‖ * Real.sqrt c ≤ ‖y‖_[m] := by
      have h3 : (‖y‖ * Real.sqrt c) ^ 2 ≤ (‖y‖_[m]) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hcpos.le]
        linarith
      have h4 := sq_le_sq.mp h3
      rwa [abs_of_nonneg (mul_nonneg (norm_nonneg y) (Real.sqrt_nonneg _)),
        abs_of_nonneg (weightedNorm_nonneg m y)] at h4
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hcpos)]
    linarith
  -- choose `k` large
  have hδpos : 0 < min (ε / 4 * T₀) 1 := lt_min (mul_pos hε4 hT₀pos) one_pos
  have hconv_ev : ∀ᶠ k in atTop,
      ∀ t ∈ Set.Icc 0 T, dist (γs k t) (γ (t + 1)) < min (ε / 4 * T₀) 1 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hconv) (min (ε / 4 * T₀) 1) hδpos
    exact h.mono fun k hk t ht => by
      have h' := hk t ht
      rwa [dist_comm] at h'
  have hτev : ∀ᶠ k in atTop, T + 1 ≤ τ k := tendsto_atTop.1 hτtop (T + 1)
  obtain ⟨k, hk⟩ := eventually_atTop.1 (hτev.and hconv_ev)
  have hkτ : T + 1 ≤ τ k := (hk k le_rfl).1
  have hkconv : ∀ t ∈ Set.Icc 0 T, dist (γs k t) (γ (t + 1)) < min (ε / 4 * T₀) 1 :=
    (hk k le_rfl).2
  have hT_lt_τk : T < τ k := by linarith
  have hT₀_lt_τk : T₀ < τ k := lt_trans hT_gt hT_lt_τk
  -- Marchal: the minimisers are collision free
  have hnc_kin : ∀ t ∈ Set.Ioo 0 (τ k), WithoutCollisions (γs k t) :=
    fun t ht => hM (γs k) 0 (τ k) (hτ k) (hac k) (hmin k) t ht
  -- the configurational measure is large
  have hμbig : ∀ t ∈ Set.Icc T₀ T, 3 * configMeasure m a < configMeasure m (γs k t) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hT₀pos ht.1
    have hd : dist (t⁻¹ • γs k t) b < ε := by
      have h1 : dist (t⁻¹ • γs k t) (t⁻¹ • γ (t + 1)) < ε / 4 := by
        have h2 := hkconv t ⟨ht0.le, ht.2⟩
        calc dist (t⁻¹ • γs k t) (t⁻¹ • γ (t + 1))
            = ‖t⁻¹‖ * dist (γs k t) (γ (t + 1)) := dist_smul₀ _ _ _
          _ < t⁻¹ * (ε / 4 * T₀) := by
              rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
              exact mul_lt_mul_of_pos_left
                (lt_of_lt_of_le h2 (min_le_left _ _)) (inv_pos.mpr ht0)
          _ = ε / 4 * (T₀ / t) := by ring
          _ ≤ ε / 4 * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ hε4.le
              rw [div_le_one ht0]; exact ht.1
          _ = ε / 4 := by ring
      have h4 : dist (t⁻¹ • γ (t + 1)) b < ε / 2 := hshift_ε t ht.1
      linarith [dist_triangle (t⁻¹ • γs k t) (t⁻¹ • γ (t + 1)) b]
    have hnc' : WithoutCollisions (t⁻¹ • γs k t) :=
      withoutCollisions_smul (hnc_kin t ⟨ht0, lt_of_le_of_lt ht.2 hT_lt_τk⟩)
        (ne_of_gt (inv_pos.mpr ht0))
    have h5 : 3 * configMeasure m a < configMeasure m (t⁻¹ • γs k t) := hεprop _ hnc' hd
    rwa [configMeasure_smul (fun i => (hm i).le) (inv_pos.mpr ht0)] at h5
  -- the growth bound of the minimisers
  have hgrowth : ∀ t ∈ Set.Icc T₀ T, ‖γs k t‖ ≤ Ce * t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hT₀pos ht.1
    have ht1 : (1 : ℝ) ≤ t := le_trans h1T₀ ht.1
    have h1 : ‖γs k t - γ (t + 1)‖ ≤ 1 := by
      have h2 := hkconv t ⟨ht0.le, ht.2⟩
      rw [dist_eq_norm] at h2
      linarith [min_le_right (ε / 4 * T₀) 1]
    have h2 : ‖γ (t + 1)‖ ≤ (‖b‖ + 1) * (t + 1) := hγbound t ht.1
    have h3 : ‖γs k t‖ ≤ ‖γs k t - γ (t + 1)‖ + ‖γ (t + 1)‖ := by
      calc ‖γs k t‖ = ‖(γs k t - γ (t + 1)) + γ (t + 1)‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [hCedef]
    have h4 : (‖b‖ + 1) * (t + 1) ≤ 2 * (‖b‖ + 1) * t := by nlinarith [norm_nonneg b]
    linarith
  have hρC : ∀ t ∈ Set.Icc T₀ T, ‖γs k t‖_[m] ≤ C * t := by
    intro t ht
    calc ‖γs k t‖_[m] ≤ Real.sqrt (∑ i, m i) * ‖γs k t‖ :=
          weightedNorm_le_mul_norm (fun i => (hm i).le) _
      _ ≤ Real.sqrt (∑ i, m i) * (Ce * t) :=
          mul_le_mul_of_nonneg_left (hgrowth t ht) (Real.sqrt_nonneg _)
      _ = C * t := by rw [hC, hCedef]; ring
  -- continuity and collision freeness on the closed interval
  have hcontγ : ContinuousOn (γs k) (Set.Icc T₀ (τ k)) := by
    have h := (hac k).continuousOn
    rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ τ k)] at h
    exact h.mono (Set.Icc_subset_Icc hT₀pos.le le_rfl)
  have hncIcc : ∀ t ∈ Set.Icc T₀ (τ k), WithoutCollisions (γs k t) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact hnc_kin t ⟨lt_of_lt_of_le hT₀pos ht.1, hlt⟩
    · rw [heq, h1 k]
      exact withoutCollisions_smul ha_nc (ne_of_gt (hlam k))
  -- the first crossing of the level `2 μ(a)`
  obtain ⟨Tk, hT₀Tk, hTk_le, hμTk_eq, h2⟩ :=
    Commons.Analysis.Real.first_crossing_strict (a := T₀) (b := τ k) (c := 2 * configMeasure m a)
      hT₀_lt_τk.le
      (continuousOn_configMeasure_comp hm hcontγ hncIcc)
      (by have := hμbig T₀ ⟨le_rfl, hT_gt.le⟩; linarith)
      (by rw [h1 k, configMeasure_smul (fun i => (hm i).le) (hlam k)]; linarith)
  have hTk_lt_τk : Tk < τ k := by
    rcases lt_or_eq_of_le hTk_le with h | h
    · exact h
    · exfalso
      rw [h, h1 k, configMeasure_smul (fun i => (hm i).le) (hlam k)] at hμTk_eq
      linarith
  have hT_le_Tk : T ≤ Tk := by
    by_contra hcon
    push_neg at hcon
    have hmem : Tk ∈ Set.Icc T₀ T := ⟨hT₀Tk.le, hcon.le⟩
    have := hμbig Tk hmem
    linarith
  have h2' : ∀ t ∈ Set.Icc T₀ Tk, 2 * configMeasure m a ≤ configMeasure m (γs k t) := h2
  have h3 : ∀ t ∈ Set.Icc T₀ T, 3 * configMeasure m a ≤ configMeasure m (γs k t) :=
    fun t ht => (hμbig t ht).le
  have hTknc : WithoutCollisions (γs k Tk) := hncIcc Tk ⟨hT₀Tk.le, hTk_le⟩
  have hρTkpos : 0 < ‖γs k Tk‖_[m] :=
    weightedNorm_pos hm (ne_zero_of_withoutCollisions hN hTknc)
  -- the bound `R`
  have hR : ‖γs k T₀ - (‖γs k T₀‖_[m] / ‖γs k Tk‖_[m]) • γs k Tk‖ ≤ R := by
    have hscalepos : 0 < ‖γs k T₀‖_[m] / ‖γs k Tk‖_[m] :=
      div_pos (weightedNorm_pos hm (ne_zero_of_withoutCollisions hN
        (hncIcc T₀ ⟨le_rfl, hT₀_lt_τk.le⟩))) hρTkpos
    have h7 : ‖γs k T₀‖_[m] ≤ C * T₀ := hρC T₀ ⟨le_rfl, hT_gt.le⟩
    calc ‖γs k T₀ - (‖γs k T₀‖_[m] / ‖γs k Tk‖_[m]) • γs k Tk‖
        ≤ ‖γs k T₀‖ + ‖(‖γs k T₀‖_[m] / ‖γs k Tk‖_[m]) • γs k Tk‖ := norm_sub_le _ _
      _ = ‖γs k T₀‖ + (‖γs k T₀‖_[m] / ‖γs k Tk‖_[m]) * ‖γs k Tk‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscalepos]
      _ ≤ ‖γs k T₀‖_[m] / Real.sqrt c
            + (‖γs k T₀‖_[m] / ‖γs k Tk‖_[m])
              * (‖γs k Tk‖_[m] / Real.sqrt c) :=
          add_le_add (hnorm_le _) (mul_le_mul_of_nonneg_left (hnorm_le _) hscalepos.le)
      _ = 2 * ‖γs k T₀‖_[m] / Real.sqrt c := by
          field_simp
          ring
      _ ≤ 2 * C * T₀ / Real.sqrt c := by
          rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hcpos) (Real.sqrt_pos.mpr hcpos)]
          nlinarith [h7, Real.sqrt_pos.mpr hcpos]
      _ = R := by rw [hR]
  -- the competitor curve
  obtain ⟨S, η, hSpos, hη0, hηS, hηac, hηlt⟩ :=
    exists_competitor_action_lt (m := m) (h := h) (a := a) (α := α) (β := β) (C := C) (R := R)
      (γ := γs k) (τ := τ k) (T₀ := T₀) (Tk := Tk) (T := T)
      hE hN hm hh hμa hCpos hT₀pos hα hβ hest (hτ k) hT₀Tk hT_gt.le hT_le_Tk hTk_lt_τk
      (hac k) (hmin k) hncIcc h2' hμTk_eq h3 hρC hR hX
  -- minimality is contradicted
  have hle : actionPot m h (γs k 0) (γs k (τ k)) ≤ actionOn m h η 0 S := by
    have h := actionPot_le_of_interval (m := m) (h := h) (a := (0 : ℝ)) (b := S) hSpos
      (γ := η) (x := γs k 0) (y := γs k (τ k)) hη0 hηS hηac
    simpa using h
  have hmin' : actionOn m h (γs k) 0 (τ k) = actionPot m h (γs k 0) (γs k (τ k)) := hmin k
  exact absurd hle (not_le.mpr (by rw [← hmin']; exact hηlt))

end Submission.NBody
