import Submission.NBody.Assembly
import Submission.NBody.CollisionFreeLimit
import Submission.NBody.ConeArgument
import Submission.NBody.LimitShapeNonzero
import Submission.NBody.Identification
import Submission.NBody.Approximation

/-!
# The final assembly: Theorem 1.1 of Maderna--Venturelli, modulo Marchal and Marchal--Saari

This module assembles all the pieces of the variational chapter into the main theorem: given
Marcal's theorem (`MarchalProperty`, an `h`-minimiser has no interior collision) and
Marchal--Saari (`MarchalSaari`, a non-superhyperbolic motion has a limit shape), for every
collision-free direction `a` with `‖a‖_[m] = 1`, every initial configuration `x₀` and every `h > 0`
there is a genuine solution `x` of the `N`-body problem with `x 0 = x₀`, collision free on `(0,∞)`
and asymptotic to `√(2h)·t·a`:

    `x t = (√(2h) * t) • a + o t`,  with `o =o[atTop] fun t => t`.

The proof chain (see `Submission/ROADMAP.md` for the details):
1. `exists_calibrating_curve_of_masses` produces the horofunction `𝔲` and the calibrating curve `γ`
   through `x₀`, with the escaping sequence `((ψ k : ℕ) : ℝ) • a` and its uniform convergence;
2. `exists_limitShape_of_calibrating` (Marchal--Saari) gives the limit shape `b` of `γ`;
3. `limitShape_ne_zero` (Lagrange--Jacobi) gives `b ≠ 0`;
4. `withoutCollisions_of_limshape` gives `WithoutCollisions b` (the competitor argument);
5. `exists_parallel_of_limitShape` (the cone argument, using Chazy's continuity of the limit shape)
   gives `b = c • a` with `0 ≤ c`;
6. `norm_limitShape_sq_eq_two_h_of_calibrating` gives `(‖b‖_[m])² = 2h`, whence `c = √(2h)`;
7. the conclusion follows with `x := extendLeft γ`.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}
variable [Nontrivial E]

namespace Submission.NBody

theorem theorem_1_1_of_marchal_saari (hE : 2 ≤ Module.finrank ℝ E) (hN : 2 ≤ N)
    (m : Fin N → ℝ) (hm : ∀ i, 0 < m i) (x₀ a : EN E N) (a_nc : WithoutCollisions a)
    (a_norm : ‖a‖_[m] = 1) (h : ℝ) (h_pos : 0 < h)
    (hM : MarchalProperty (E := E) m h) (hMS : MarchalSaari (E := E) (N := N) m) :
    ∃ x : ℝ → EN E N, ∃ o : ℝ → EN E N, (o =o[atTop] fun t => t) ∧ x 0 = x₀ ∧
      IsNBodySolution m x ∧ (∀ t > 0, WithoutCollisions (x t)) ∧
        ∀ t ≥ 0, x t = (sqrt (2 * h) * t) • a + o t := by
  have hNpos : 0 < N := by omega
  -- a positive lower bound for the masses
  obtain ⟨c₀, hc₀pos, hc₀⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N)) m
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    exact ⟨m i₀, hm i₀, fun i => hi₀ i (Finset.mem_univ i)⟩
  have ha_ne : a ≠ 0 := by
    intro h0
    have h1 : ‖a‖_[m] = 0 := by rw [h0]; simp [weightedNorm]
    rw [a_norm] at h1
    norm_num at h1
  -- Hölder constants
  obtain ⟨α, β, hα, hβ, hest⟩ := actionPot_le_holder (E := E) (N := N) hNpos hm h_pos.le
  -- the horofunction, the calibrating curve and the escaping sequence
  obtain ⟨𝔲, γ, ψ, hrest⟩ :=
    exists_calibrating_curve_of_masses (E := E) hNpos hm h_pos a ha_ne a_nc x₀
  obtain ⟨hψ, hψpos, hdom, h𝔲0, hγ0, hγcal, huni⟩ := hrest
  have hγcal' : ∀ t : ℝ, 0 < t → AbsolutelyContinuousOnInterval γ 0 t ∧
      IsHMinimizer m h γ 0 t ∧ actionOn m h γ 0 t = ENNReal.ofReal (𝔲 (γ 0) - 𝔲 (γ t)) := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hγcal t ht
    exact ⟨h1, h2, by rw [h3, hγ0]⟩
  have hlip : ∀ x z : EN E N, ENNReal.ofReal |𝔲 x - 𝔲 z| ≤ actionPot m h x z := by
    intro x z
    have hφtop : actionPot m h x z ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (hest x z) ENNReal.ofReal_lt_top)
    have h1 : 𝔲 x - 𝔲 z ≤ (actionPot m h x z).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hφtop).mp (by rw [actionPot_comm]; exact hdom z x)
    have h2 : 𝔲 z - 𝔲 x ≤ (actionPot m h x z).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hφtop).mp (hdom x z)
    exact (ENNReal.ofReal_le_iff_le_toReal hφtop).mpr (abs_le.mpr ⟨by linarith, by linarith⟩)
  -- the escaping configurations
  set p : ℕ → EN E N := fun k => (((ψ k : ℕ) : ℝ)) • a with hpdef
  have hpnc : ∀ k, WithoutCollisions (p k) := fun k => by
    rw [hpdef]
    exact withoutCollisions_smul a_nc (by exact_mod_cast ne_of_gt (hψpos k))
  have hpgrow : Tendsto (fun k => ‖p k‖) atTop atTop := by
    rw [tendsto_atTop_atTop] at ⊢
    intro B
    have h1 : Tendsto (fun k : ℕ => ((ψ k : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop
    rw [tendsto_atTop_atTop] at h1
    obtain ⟨K, hK⟩ := h1 (max B 0 / ‖a‖)
    refine ⟨K, fun k hk => ?_⟩
    have h2 := hK k hk
    rw [hpdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have h3 : 0 < ‖a‖ := norm_pos_iff.mpr ha_ne
    have h4 : max B 0 ≤ ((ψ k : ℕ) : ℝ) * ‖a‖ := by
      rw [div_le_iff₀ h3] at h2
      linarith
    linarith [le_max_left B 0]
  -- the minimisers from `γ 1` to `p k`
  have hd' : Dominated m h (fun x => -𝔲 x) := by
    intro x y
    have h2 : -𝔲 y - -𝔲 x = 𝔲 x - 𝔲 y := by ring
    rw [h2]
    exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans (hlip x y)
  have hcal2 : IsCalibrating m h (fun x => -𝔲 x) γ 0 2 := by
    have h3 := (hγcal' 2 (by norm_num)).2.2
    rw [IsCalibrating]
    show actionOn m h γ 0 2 = ENNReal.ofReal ((-𝔲) (γ 2) - (-𝔲) (γ 0))
    rw [h3]
    congr 1
    simp only [Pi.neg_apply]
    ring
  have hmin2 : IsHMinimizer m h γ 0 2 :=
    IsCalibrating.isHMinimizer hd' hcal2 (by norm_num) (hγcal' 2 (by norm_num)).1
  have hq0nc : WithoutCollisions (γ 1) :=
    hM γ 0 2 (by norm_num) (hγcal' 2 (by norm_num)).1 hmin2 1 ⟨by norm_num, by norm_num⟩
  -- the `h`-minimisers from `γ 1` to `p k`
  have hmain := exists_minimizer_to (m := m) (h := h) hm h_pos hE hq0nc hpnc hpgrow
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hmain
  have hex : ∀ k : ℕ, ∃ (τ : ℝ) (γk : ℝ → EN E N), 0 < τ ∧ γk 0 = γ 1 ∧ γk τ = p (k + M₀) ∧
      AbsolutelyContinuousOnInterval γk 0 τ ∧ IsHMinimizer m h γk 0 τ := fun k =>
    hM₀ (k + M₀) (Nat.le_add_left M₀ k)
  choose τ γs hτ h0 h1 hac hmin using hex
  -- the shifted data
  set p' : ℕ → EN E N := fun k => p (k + M₀) with hp'def
  set lam : ℕ → ℝ := fun k => ((ψ (k + M₀) : ℕ) : ℝ) with hlamdef
  have hp'eq : ∀ k, p' k = lam k • a := fun k => by rw [hp'def, hpdef, hlamdef]
  have hlam_pos : ∀ k, 0 < lam k := fun k => by
    show (0 : ℝ) < ((ψ (k + M₀) : ℕ) : ℝ)
    exact_mod_cast hψpos (k + M₀)
  have hpnc' : ∀ k, WithoutCollisions (p' k) := fun k => hpnc (k + M₀)
  have hpgrow' : Tendsto (fun k => ‖p' k‖) atTop atTop := by
    rw [hp'def]
    exact hpgrow.comp (tendsto_add_atTop_nat M₀)
  -- the travel times tend to infinity
  have hτtop : Tendsto τ atTop atTop :=
    tau_tendsto_atTop (m := m) (h := h) (α := α) (β := β) (c := c₀) (q0 := γ 1)
      (p := p') hτ h0 h1 hac hmin hc₀pos hc₀ h_pos.le hα hβ hest hpgrow'

  -- the calibrating data for the shifted curve
  have hcal2_gen : ∀ T : ℝ, 0 < T → IsCalibrating m h (fun x => -𝔲 x) γ 0 T := by
    intro T hT
    rw [IsCalibrating]
    have h3 := (hγcal' T hT).2.2
    show actionOn m h γ 0 T = ENNReal.ofReal ((-𝔲) (γ T) - (-𝔲) (γ 0))
    rw [h3]
    congr 1
    simp only [Pi.neg_apply]
    ring
  have hγsac : ∀ δ : ℝ, 0 < δ → AbsolutelyContinuousOnInterval (fun t => γ (t + 1)) 0 δ := by
    intro δ hδ
    have hδ1 : (0 : ℝ) < δ + 1 := by linarith
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := γ) (a := 0) (b := δ + 1) (c := 1) (d := 1) one_ne_zero (hγcal' (δ + 1) hδ1).1
    have h4 : (fun t : ℝ => γ (1 * t + 1)) = fun t : ℝ => γ (t + 1) := by
      funext t; rw [one_mul]
    rw [h4] at h
    refine h.mono ?_
    have h2 : ((0:ℝ) - 1) / 1 = -1 := by norm_num
    have h3 : (δ + 1 - 1) / 1 = δ := by ring
    rw [h2, h3, uIcc_of_le (by linarith : (-1 : ℝ) ≤ δ), uIcc_of_le hδ.le]
    exact Set.Icc_subset_Icc (by linarith) le_rfl
  have hγsscal : ∀ δ : ℝ, 0 < δ → IsCalibrating m h (fun x => -𝔲 x) (fun t => γ (t + 1)) 0 δ := by
    intro δ hδ
    have h := IsCalibrating.sub_right (a := 0) (b := δ + 1) (c := 1) hd'
      (hcal2_gen (δ + 1) (by linarith)) (hγcal' (δ + 1) (by linarith)).1 one_pos (by linarith)
    simpa using IsCalibrating.comp_add_const h
  obtain ⟨hsol, hγnc⟩ := isNBodySolution_extendLeft_of_calibrating (γ := γ) hNpos hm h_pos hM hγcal'
  have henergy_shift : ∀ t > 0, energy m (fun s => γ (s + 1)) t = h := by
    refine energy_eq_of_calibrating (𝔲 := 𝔲) (γs := fun s => γ (s + 1)) hm h_pos
      (by simpa using hq0nc) ?_ ?_
    · intro t ht
      exact hM γ 0 (t + 1 + 1) (by linarith) (hγcal' (t + 1 + 1) (by linarith)).1
        (IsCalibrating.isHMinimizer hd' (hcal2_gen (t + 1 + 1) (by linarith)) (by linarith)
          (hγcal' (t + 1 + 1) (by linarith)).1) (t + 1) ⟨by linarith, by linarith⟩
    · intro t ht
      refine ⟨hγsac t ht, ?_, ?_⟩
      · exact IsCalibrating.isHMinimizer hd' (hγsscal t ht) ht (hγsac t ht)
      · have hcal3 := hγsscal t ht
        rw [IsCalibrating] at hcal3
        show actionOn m h (fun s => γ (s + 1)) 0 t = ENNReal.ofReal (𝔲 (γ (0 + 1)) - 𝔲 (γ (t + 1)))
        rw [hcal3]
        congr 1
        ring
  -- the limit shape
  obtain ⟨b, hbshape⟩ :=
    exists_limitShape_of_calibrating (E := E) (N := N) hNpos hm h_pos hMS hM hγcal'
  -- the collision freeness of `extendLeft γ` and its energy
  have hext_nc : ∀ t > 0, WithoutCollisions (extendLeft γ t) := fun t ht => by
    rw [extendLeft_of_pos ht]; exact hγnc t ht
  have hshift_energy : ∀ t : ℝ, energy m (fun s => γ (s + 1)) t = energy m γ (t + 1) := by
    intro t
    simp only [energy]
    rw [deriv_comp_add_const]
  have henergy_ext : ∀ t > 0, energy m (extendLeft γ) t = h := by
    intro t ht
    have h2 : energy m (extendLeft γ) t = energy m (extendLeft γ) 2 :=
      energy_eq_of_pos m (fun i => (hm i).ne') hsol hext_nc ht (by norm_num)
    rw [h2]
    have h3 : energy m (extendLeft γ) 2 = energy m γ 2 := by
      have hev : extendLeft γ =ᶠ[𝓝 (2:ℝ)] γ := by
        filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0:ℝ) < 2)] with s hs
        rw [extendLeft_of_pos hs]
      simp only [energy]
      rw [hev.deriv_eq, hev.eq_of_nhds]
    rw [h3, show (2 : ℝ) = 1 + 1 by norm_num, ← hshift_energy 1]
    exact henergy_shift 1 (by norm_num)
  -- `b ≠ 0` (Lagrange--Jacobi)
  have hb_ne : b ≠ 0 := by
    refine limitShape_ne_zero (γ := extendLeft γ) hNpos hm h_pos hsol hext_nc henergy_ext ?_
    refine hbshape.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [extendLeft_of_pos ht]
  -- `a ≠ 0` gives `0 < configMeasure m a`
  have hμa : 0 < configMeasure m a := by
    obtain ⟨i, j, hij⟩ := exists_ne_fin hN
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hmem : (i, j) ∈ pairFinset N := by
        rw [pairFinset, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt⟩
      have hterm : 0 < m i * m j * (dist (a i) (a j))⁻¹ := by
        refine mul_pos (mul_pos (hm i) (hm j)) ?_
        rw [inv_pos]
        exact dist_pos.mpr (fun heq => a_nc i j hij (by rw [r, dist_eq_zero]; exact heq))
      have hpos : 0 < U m a := by
        rw [U_eq_pairFinset]
        refine Finset.sum_pos' (fun p _ => ?_) ⟨(i, j), hmem, hterm⟩
        refine mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) ?_
        exact inv_nonneg.mpr dist_nonneg
      calc 0 < ‖a‖_[m] * U m a := by rw [a_norm]; simpa using hpos
        _ = configMeasure m a := rfl
    · have hmem : (j, i) ∈ pairFinset N := by
        rw [pairFinset, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hgt⟩
      have hterm : 0 < m j * m i * (dist (a j) (a i))⁻¹ := by
        refine mul_pos (mul_pos (hm j) (hm i)) ?_
        rw [inv_pos]
        exact dist_pos.mpr (fun heq => a_nc i j hij (by rw [r, dist_eq_zero]; exact heq.symm))
      have hpos : 0 < U m a := by
        rw [U_eq_pairFinset]
        refine Finset.sum_pos' (fun p _ => ?_) ⟨(j, i), hmem, hterm⟩
        refine mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) ?_
        exact inv_nonneg.mpr dist_nonneg
      calc 0 < ‖a‖_[m] * U m a := by rw [a_norm]; simpa using hpos
        _ = configMeasure m a := rfl
  -- a subsequence with convergent initial velocities (used for the cone argument)
  have huni' : ∀ K : Set (EN E N), IsCompact K → TendstoUniformlyOn
      (fun k x => normPot m h (p' k) x) 𝔲 atTop K := by
    intro K hK
    have h1s := (huni K hK).seq_tendstoUniformlyOn (fun k => k + M₀) (tendsto_add_atTop_nat M₀)
    simpa only [hp'def, Function.comp_apply] using h1s
  obtain ⟨φ, v, hφ, hconvT₁, hv, hvtop⟩ :=
    exists_uniform_approx_and_velocity (m := m) (h := h) (u := 𝔲) (γ := γ) hNpos hM hm h_pos
      hlip (fun t ht => (hγcal' t ht).1) hcal2_gen hc₀pos hc₀ hτ h0 h1 hac hmin hτtop huni' hα hβ
      hest (by norm_num : (0 : ℝ) < 1)
  -- (C) `b` is collision free
  have hb_nc : WithoutCollisions b := by
    by_contra hbc
    obtain ⟨i, j, hij, hbij⟩ : ∃ i j : Fin N, i ≠ j ∧ b i = b j := by
      by_contra hcon
      apply hbc
      intro i j hij
      exact fun h0 => hcon ⟨i, j, hij, dist_eq_zero.mp h0⟩
    obtain ⟨ε, hεpos, hεprop⟩ :=
      exists_lt_configMeasure_of_collision hm hij hbij hb_ne (3 * configMeasure m a)
    -- thresholds for the shape of `γ`
    have hε4 : 0 < ε / 4 := by linarith
    obtain ⟨T₁, hT₁⟩ := Metric.tendsto_atTop.mp hbshape (ε / 4) hε4
    obtain ⟨T₂, hT₂⟩ := Metric.tendsto_atTop.mp hbshape 1 (by norm_num)
    set T₀ : ℝ := max (max T₁ T₂) (max 1 (4 * (‖b‖ + 1) / ε)) with hT₀def
    have hT₁T₀ : T₁ ≤ T₀ := by
      rw [hT₀def]; exact le_trans (le_max_left T₁ T₂) (le_max_left _ _)
    have hT₂T₀ : T₂ ≤ T₀ := by
      rw [hT₀def]; exact le_trans (le_max_right T₁ T₂) (le_max_left _ _)
    have h1T₀ : (1 : ℝ) ≤ T₀ := by
      rw [hT₀def]; exact le_trans (le_max_left 1 _) (le_max_right _ _)
    have hT₀pos : 0 < T₀ := lt_of_lt_of_le one_pos h1T₀
    have hCaT₀ : 4 * (‖b‖ + 1) / ε ≤ T₀ := by
      rw [hT₀def]; exact le_trans (le_max_right 1 _) (le_max_right _ _)
    have hshape4 : ∀ t ≥ T₀, dist (t⁻¹ • γ t) b < ε / 4 :=
      fun t ht => hT₁ t (le_trans hT₁T₀ ht)
    have hshape1 : ∀ t ≥ T₀, dist (t⁻¹ • γ t) b < 1 :=
      fun t ht => hT₂ t (le_trans hT₂T₀ ht)
    -- the constants
    have hSpos : 0 < ∑ i, m i := sum_mass_pos hm ⟨0, by omega⟩
    set C : ℝ := Real.sqrt (∑ i, m i) * (2 * ‖b‖ + 3) with hCdef
    have hCpos : 0 < C := by
      rw [hCdef]
      exact mul_pos (Real.sqrt_pos.mpr hSpos) (by positivity)
    set R : ℝ := 2 * C * T₀ / Real.sqrt c₀ with hRdef
    -- the auxiliary time `T`
    have hTend_log : Tendsto (fun T : ℝ => Real.log T - Real.log T₀) atTop atTop := by
      have h := tendsto_atTop_add_const_right atTop (-(Real.log T₀)) Real.tendsto_log_atTop
      simpa only [sub_eq_add_neg] using h
    have hTend : Tendsto (fun T : ℝ => (configMeasure m a / C) * (Real.log T - Real.log T₀))
        atTop atTop :=
      Tendsto.const_mul_atTop (div_pos hμa hCpos) hTend_log
    obtain ⟨T₀', hT'⟩ := eventually_atTop.1
      (tendsto_atTop.1 hTend (Real.sqrt (α * R + h * β * R ^ 2) + 1))
    set T : ℝ := max (max T₀' (T₀ + 1)) 1 with hTdef
    have hT₀'T : T₀' ≤ T := by
      rw [hTdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    have hT₀T : T₀ < T := by
      rw [hTdef]
      have h : T₀ + 1 ≤ max (max T₀' (T₀ + 1)) 1 :=
        le_trans (le_max_right T₀' (T₀ + 1)) (le_max_left _ _)
      linarith
    have hTpos : 0 < T := lt_trans hT₀pos hT₀T
    have hX : Real.sqrt (α * R + h * β * R ^ 2)
        < (configMeasure m a / C) * (Real.log T - Real.log T₀) := by
      have h := hT' T hT₀'T
      linarith
    -- the subsequence with uniform convergence on `[0,T]`
    obtain ⟨φ₂, v₂, hφ₂, hconvT₂, hv₂, hvtop₂⟩ :=
      exists_uniform_approx_and_velocity (m := m) (h := h) (u := 𝔲) (γ := γ) hNpos hM hm h_pos
        hlip (fun t ht => (hγcal' t ht).1) hcal2_gen hc₀pos hc₀ hτ h0 h1 hac hmin hτtop huni' hα hβ
        hest hTpos
    exact hbc (withoutCollisions_of_limshape (m := m) (h := h) (a := a) (b := b) (γ := γ)
      (lam := fun k => lam (φ₂ k)) (τ := fun k => τ (φ₂ k)) (γs := fun k => γs (φ₂ k))
      (α := α) (β := β) (ε := ε) (T₀ := T₀) (T := T) (C := C) (c := c₀) (R := R)
      hE hN hm h_pos hM a_nc hμa hb_ne hα hβ hest hεpos hεprop hT₀pos h1T₀ hCaT₀ hshape4 hshape1
      hCpos hCdef hc₀pos hc₀ hRdef (fun k => hlam_pos (φ₂ k)) (fun k => hτ (φ₂ k))
      (fun k => h0 (φ₂ k)) (fun k => h1 (φ₂ k)) (fun k => hac (φ₂ k)) (fun k => hmin (φ₂ k))
      (hτtop.comp hφ₂.tendsto_atTop) hT₀T hX hconvT₂)
  -- the shifted calibrating data and the shape of `extendLeft γ`
  have hcalShift : ∀ t : ℝ, 0 < t → AbsolutelyContinuousOnInterval (fun s => γ (s + 1)) 0 t ∧
      IsHMinimizer m h (fun s => γ (s + 1)) 0 t ∧
      actionOn m h (fun s => γ (s + 1)) 0 t = ENNReal.ofReal (𝔲 (γ (0 + 1)) - 𝔲 (γ (t + 1))) := by
    intro t ht
    refine ⟨hγsac t ht, IsCalibrating.isHMinimizer hd' (hγsscal t ht) ht (hγsac t ht), ?_⟩
    have hcal3 := hγsscal t ht
    rw [IsCalibrating] at hcal3
    rw [hcal3]
    congr 1
    ring
  have hbshape' : Tendsto (fun t : ℝ => t⁻¹ • extendLeft γ t) atTop (𝓝 b) := by
    refine hbshape.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [extendLeft_of_pos ht]
  -- the collision freeness of the minimisers
  have hncγs' : ∀ k, ∀ t ∈ Set.Icc 0 (τ (φ k)), WithoutCollisions (γs (φ k) t) := by
    intro k t ht
    rcases eq_or_lt_of_le ht.1 with h0' | h0'
    · rw [← h0', h0 (φ k)]; exact hq0nc
    · rcases eq_or_lt_of_le ht.2 with hlast | hlast
      · rw [hlast, h1 (φ k)]
        exact hpnc (φ k + M₀)
      · exact hM (γs (φ k)) 0 (τ (φ k)) (hτ (φ k)) (hac (φ k)) (hmin (φ k)) t ⟨h0', hlast⟩
  have hvtop' : Tendsto (fun k => v (φ k)) atTop (𝓝 (deriv (extendLeft γ) 1)) := by
    have h1 : deriv (extendLeft γ) 1 = deriv γ 1 := by
      have hev : extendLeft γ =ᶠ[𝓝 (1:ℝ)] γ := by
        filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0:ℝ) < 1)] with s hs
        rw [extendLeft_of_pos hs]
      exact hev.deriv_eq
    rw [h1]; exact hvtop
  -- (D) the limit shape is parallel to `a`
  obtain ⟨c₁, hc₁nonneg, hc₁⟩ :=
    exists_parallel_of_limitShape (m := m) (h := h) (a := a) (b := b) (γ := extendLeft γ)
      (γs := fun k => γs (φ k)) (τ := fun k => τ (φ k)) (lam := fun k => lam (φ k))
      (v := fun k => v (φ k)) hN hm h_pos hM a_nc a_norm hb_nc hsol hext_nc hbshape'
      (fun k => hτ (φ k)) (hτtop.comp hφ.tendsto_atTop) (fun k => (hlam_pos (φ k)).le)
      (fun k => by rw [extendLeft_of_pos (by norm_num : (0:ℝ) < 1), ← h0 (φ k)])
      (fun k => h1 (φ k)) (fun k => hac (φ k)) (fun k => hmin (φ k))
      hncγs' (fun k => hv (φ k)) hvtop'
  -- (E) the normalisation
  have hshape_shift : Tendsto (fun t : ℝ => t⁻¹ • γ (t + 1)) atTop (𝓝 b) := by
    have h1 : Tendsto (fun t : ℝ => ((t + 1)⁻¹ : ℝ) • γ (t + 1)) atTop (𝓝 b) :=
      hbshape.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
    have hγbound : ∀ᶠ t : ℝ in atTop, ‖γ (t + 1)‖ ≤ (‖b‖ + 1) * (t + 1) := by
      have h2 : ∀ᶠ t : ℝ in atTop, dist ((t + 1)⁻¹ • γ (t + 1)) b < 1 :=
        (Metric.tendsto_nhds.mp h1) 1 one_pos
      filter_upwards [h2, eventually_gt_atTop (0 : ℝ)] with t ht ht0
      have h4 : ‖(t + 1)⁻¹ • γ (t + 1)‖ < ‖b‖ + 1 := by
        have h5 : |‖(t + 1)⁻¹ • γ (t + 1)‖ - ‖b‖| ≤ dist ((t + 1)⁻¹ • γ (t + 1)) b := by
          rw [dist_eq_norm]
          exact abs_norm_sub_norm_le _ _
        linarith [(abs_le.mp h5).2]
      calc ‖γ (t + 1)‖ = (t + 1) * ‖(t + 1)⁻¹ • γ (t + 1)‖ := by
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr (by linarith : (0 : ℝ) < t + 1)),
              mul_inv_cancel_left₀ (by linarith : (t + 1) ≠ 0)]
        _ ≤ (t + 1) * (‖b‖ + 1) := mul_le_mul_of_nonneg_left h4.le (by linarith)
        _ = (‖b‖ + 1) * (t + 1) := by ring
    have h2 : Tendsto (fun t : ℝ => t⁻¹ • γ (t + 1) - ((t + 1)⁻¹ : ℝ) • γ (t + 1))
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h3 : ∀ᶠ t : ℝ in atTop,
          ‖t⁻¹ • γ (t + 1) - ((t + 1)⁻¹ : ℝ) • γ (t + 1)‖ ≤ (‖b‖ + 1) / t := by
        filter_upwards [hγbound, eventually_gt_atTop (0 : ℝ)] with t hb ht
        have h4 : t⁻¹ • γ (t + 1) - ((t + 1)⁻¹ : ℝ) • γ (t + 1)
            = (t⁻¹ - (t + 1)⁻¹) • γ (t + 1) := by rw [sub_smul]
        rw [h4, norm_smul, Real.norm_eq_abs]
        have h5 : t⁻¹ - (t + 1)⁻¹ = 1 / (t * (t + 1)) := by
          rw [inv_sub_inv (by linarith) (by linarith)]; ring
        have h6 : 0 < t⁻¹ - (t + 1)⁻¹ := by rw [h5]; positivity
        rw [abs_of_pos h6, h5]
        calc 1 / (t * (t + 1)) * ‖γ (t + 1)‖ ≤ 1 / (t * (t + 1)) * ((‖b‖ + 1) * (t + 1)) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = (‖b‖ + 1) / t := by field_simp
      exact squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) h3
        (tendsto_const_nhds.div_atTop tendsto_id)
    have h4 := h2.add h1
    simpa using h4
  have hnorm_b : (‖b‖_[m]) ^ 2 = 2 * h :=
    norm_limitShape_sq_eq_two_h_of_calibrating (𝔲 := 𝔲) (γs := fun s => γ (s + 1)) (b := b)
      hNpos hm h_pos hM (by simpa using hq0nc) (fun t ht => hγnc (t + 1) (by linarith)) hcalShift
      hb_nc hshape_shift
  have hc₁_val : c₁ = Real.sqrt (2 * h) := by
    have h1 : ‖b‖_[m] = c₁ := by
      rw [hc₁, weightedNorm_smul (fun i => (hm i).le), abs_of_nonneg hc₁nonneg, a_norm, mul_one]
    have h2 : c₁ ^ 2 = 2 * h := by
      rw [← h1]; exact hnorm_b
    calc c₁ = Real.sqrt (c₁ ^ 2) := (Real.sqrt_sq hc₁nonneg).symm
      _ = Real.sqrt (2 * h) := by rw [h2]
  -- (F) conclusion
  refine ⟨extendLeft γ, fun t => extendLeft γ t - (Real.sqrt (2 * h) * t) • a, ?_, ?_, hsol, hext_nc, ?_⟩
  · rw [Asymptotics.isLittleO_iff]
    intro cc hcc
    have hlim : Tendsto (fun t : ℝ => t⁻¹ • (extendLeft γ t - ((Real.sqrt (2*h) * t)) • a))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => t⁻¹ • extendLeft γ t - (Real.sqrt (2*h)) • a) atTop
          (𝓝 (b - (Real.sqrt (2*h)) • a)) :=
        hbshape'.sub tendsto_const_nhds
      rw [hc₁, hc₁_val, sub_self] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have h2 : t⁻¹ • ((Real.sqrt (2 * h) * t) • a) = (Real.sqrt (2 * h)) • a := by
        have h3 : t⁻¹ * (Real.sqrt (2 * h) * t) = Real.sqrt (2 * h) := by
          rw [mul_comm (Real.sqrt (2 * h)) t, ← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt ht), one_mul]
        rw [smul_smul, h3]
      rw [smul_sub, h2]
    have h3 : ∀ᶠ t : ℝ in atTop, ‖t⁻¹ • (extendLeft γ t - ((Real.sqrt (2*h) * t)) • a)‖ < cc := by
      have h4 := (Metric.tendsto_nhds.mp hlim) cc hcc
      filter_upwards [h4] with t ht
      rwa [dist_zero_right] at ht
    filter_upwards [h3, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    have h5 : ‖extendLeft γ t - (Real.sqrt (2 * h) * t) • a‖
        = t * ‖t⁻¹ • (extendLeft γ t - (Real.sqrt (2 * h) * t) • a)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
      field_simp
    rw [h5]
    calc t * ‖t⁻¹ • (extendLeft γ t - (Real.sqrt (2 * h) * t) • a)‖ ≤ t * cc :=
          mul_le_mul_of_nonneg_left ht.le ht0.le
      _ = cc * t := by ring
      _ = cc * ‖t‖ := by rw [Real.norm_eq_abs, abs_of_pos ht0]
  · rw [extendLeft_of_nonpos le_rfl]
    exact hγ0
  · intro t ht
    change extendLeft γ t = (Real.sqrt (2 * h) * t) • a
      + (extendLeft γ t - (Real.sqrt (2 * h) * t) • a)
    abel
  -- `b ≠ 0` (Lagrange--Jacobi)
end Submission.NBody
