import Mathlib

/-!
# Schwartz functions are dense in `L¹ ∩ Lᵖ` on `ℝ`

The main result of this file is `Work.BourgainPlan.Maximal.schwartz_density_L1Lp`: for
`1 < p` and `g ∈ L¹(ℝ) ∩ Lᵖ(ℝ)` there is a sequence of Schwartz functions `G n` such that
`G n → g` in `L¹`, `G n → g` in `Lᵖ`, and consequently `∫ ‖G n‖^p → ∫ ‖g‖^p`.

The construction is the standard one: fix the smooth bump `φ_m` equal to `1` on `[-m-1, m+1]`
and supported in `[-(m+2), m+2]`; approximate `g` in `Lᵖ` by a smooth compactly supported `h`,
and set `G := h · φ_m`.  The factor `φ_m` keeps the error supported in a fixed compact set,
where the `Lᵖ` estimate controls the `L¹` estimate (Hölder), and the `Lᵖ`-tails of `g(1 - φ_m)`
tend to `0` by dominated convergence.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- The standard smooth bump on `ℝ`, equal to `1` on `[-m-1, m+1]` and supported in
`[-(m+2), m+2]`. -/
def stdBump (m : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨(m : ℝ) + 1, (m : ℝ) + 2, by positivity, by linarith⟩

lemma continuous_stdBump (m : ℕ) : Continuous (fun x : ℝ => ((stdBump m) x : ℂ)) :=
  Complex.continuous_ofReal.comp
    ((ContDiffBump.contDiff (stdBump m) (n := (⊤ : ℕ∞))).continuous)

lemma contDiff_stdBump (m : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => ((stdBump m) x : ℂ)) :=
  (Complex.ofRealCLM.contDiff).comp (ContDiffBump.contDiff (stdBump m) (n := (⊤ : ℕ∞)))

lemma stdBump_one (m : ℕ) {x : ℝ} (hx : x ∈ Metric.closedBall (0 : ℝ) ((stdBump m).rIn)) :
    ((stdBump m) x : ℂ) = 1 := by
  rw [ContDiffBump.one_of_mem_closedBall _ hx]; norm_num

lemma stdBump_one_of_abs_le (m : ℕ) {x : ℝ} (hx : |x| ≤ (m : ℝ)) :
    ((stdBump m) x : ℂ) = 1 := by
  refine stdBump_one m ?_
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  simp only [stdBump]
  linarith

lemma norm_one_sub_stdBump_le_one (m : ℕ) (x : ℝ) : ‖(1 - ((stdBump m) x : ℂ))‖ ≤ 1 := by
  have h2 : (stdBump m) x ≤ 1 := (stdBump m).le_one
  have h1 : 0 ≤ (stdBump m) x := (stdBump m).nonneg
  have hh : (1 - ((stdBump m) x : ℂ)) = ((1 - (stdBump m) x : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  rw [hh, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

lemma enorm_one_sub_stdBump_le_one (m : ℕ) (x : ℝ) : ‖(1 - ((stdBump m) x : ℂ))‖ₑ ≤ 1 := by
  have h := (enorm_le_iff_norm_le (x := (1 - ((stdBump m) x : ℂ))) (y := (1 : ℂ))).mpr
    (by simpa using norm_one_sub_stdBump_le_one m x)
  simpa using h

lemma norm_stdBump_le_one (m : ℕ) (x : ℝ) : ‖((stdBump m) x : ℂ)‖ ≤ 1 := by
  have h2 : (stdBump m) x ≤ 1 := (stdBump m).le_one
  have h1 : 0 ≤ (stdBump m) x := (stdBump m).nonneg
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]
  exact h2

/-- The `L¹`-tails of `g · (1 - φ_m)` tend to `0`. -/
lemma tendsto_tail_enorm (g : ℝ → ℂ) (hg : Integrable g) :
    Tendsto (fun m : ℕ => ∫⁻ x, ‖g x * (1 - ((stdBump m) x : ℂ))‖ₑ
      ∂(volume : Measure ℝ)) atTop (nhds 0) := by
  have hbound : ∫⁻ x, ‖g x‖ₑ ∂(volume : Measure ℝ) ≠ ∞ := hg.hasFiniteIntegral.ne
  have h := tendsto_lintegral_of_dominated_convergence' (f := fun _ => 0)
    (F := fun m x => ‖g x * (1 - ((stdBump m) x : ℂ))‖ₑ) (fun x => ‖g x‖ₑ)
    (fun m => by
      have hφ : AEMeasurable (fun x : ℝ => ‖(1 - ((stdBump m) x : ℂ))‖ₑ) (volume : Measure ℝ) :=
        ((continuous_stdBump m).aemeasurable.const_sub 1).enorm
      have h2 : AEMeasurable
          (fun x : ℝ => ‖g x‖ₑ * ‖(1 - ((stdBump m) x : ℂ))‖ₑ) (volume : Measure ℝ) :=
        (hg.aestronglyMeasurable.enorm).mul hφ
      simpa only [enorm_mul] using h2)
    (fun m => by
      filter_upwards with x
      rw [enorm_mul]
      exact mul_le_of_le_one_right zero_le (enorm_one_sub_stdBump_le_one m x))
    hbound
    (by
      filter_upwards with x
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (|x|) + 1)] with m hm
      have hm' : (⌈|x|⌉₊ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
      have hmR : |x| ≤ (m : ℝ) := by
        have : |x| ≤ (Nat.ceil (|x|) : ℝ) := Nat.le_ceil _
        linarith
      rw [stdBump_one_of_abs_le m hmR]
      simp)
  simpa using h

/-- The `Lᵖ`-tails of `g · (1 - φ_m)` tend to `0`. -/
lemma tendsto_tail_enorm_rpow (p : ℝ) (hp : 0 < p) (g : ℝ → ℂ)
    (hgp : MemLp g (ENNReal.ofReal p) (volume : Measure ℝ)) :
    Tendsto (fun m : ℕ => ∫⁻ x, ‖g x * (1 - ((stdBump m) x : ℂ))‖ₑ ^ p
      ∂(volume : Measure ℝ)) atTop (nhds 0) := by
  have hP0 : ENNReal.ofReal p ≠ 0 := by positivity
  have hPtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hfin : ∫⁻ x, ‖g x‖ₑ ^ p ∂(volume : Measure ℝ) ≠ ∞ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hP0 hPtop hgp.aestronglyMeasurable).mp
      hgp.eLpNorm_lt_top
    rw [ENNReal.toReal_ofReal hp.le] at h
    exact h.ne
  have h := tendsto_lintegral_of_dominated_convergence' (f := fun _ => 0)
    (F := fun m x => ‖g x * (1 - ((stdBump m) x : ℂ))‖ₑ ^ p) (fun x => ‖g x‖ₑ ^ p)
    (fun m => by
      have hφ : AEMeasurable (fun x : ℝ => ‖(1 - ((stdBump m) x : ℂ))‖ₑ) (volume : Measure ℝ) :=
        ((continuous_stdBump m).aemeasurable.const_sub 1).enorm
      have h2 : AEMeasurable
          (fun x : ℝ => ‖g x‖ₑ * ‖(1 - ((stdBump m) x : ℂ))‖ₑ) (volume : Measure ℝ) :=
        (hgp.aestronglyMeasurable.enorm).mul hφ
      have h3 := h2.pow_const p
      simpa only [enorm_mul] using h3)
    (fun m => by
      filter_upwards with x
      gcongr
      rw [enorm_mul]
      exact mul_le_of_le_one_right zero_le (enorm_one_sub_stdBump_le_one m x))
    hfin
    (by
      filter_upwards with x
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (|x|) + 1)] with m hm
      have hm' : (⌈|x|⌉₊ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
      have hmR : |x| ≤ (m : ℝ) := by
        have : |x| ≤ (Nat.ceil (|x|) : ℝ) := Nat.le_ceil _
        linarith
      rw [stdBump_one_of_abs_le m hmR]
      simp [ENNReal.zero_rpow_of_pos hp])
  simpa using h

/-- `(eLpNorm f p) ^ p` is the `p`-th power integral of `enorm f`. -/
lemma eLpNorm_rpow_eq_lintegral (p : ℝ) (hp : 0 < p) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    (eLpNorm f (ENNReal.ofReal p) (volume : Measure ℝ)) ^ p
      = ∫⁻ x, ENNReal.rpow (enorm (f x)) p ∂(volume : Measure ℝ) := by
  have hP0 : ENNReal.ofReal p ≠ 0 := by positivity
  have hPtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop hf, ENNReal.toReal_ofReal hp.le,
    ← ENNReal.rpow_mul, show (1 / p) * p = 1 by rw [one_div, inv_mul_cancel₀ hp.ne'],
    ENNReal.rpow_one]
  rfl

/-- **Simultaneous approximation.**  For `1 < p`, an `L¹ ∩ Lᵖ` function `g` on `ℝ` and `ε > 0`
there is a Schwartz function `G` with `‖G - g‖_{L¹} ≤ ε` and `‖G - g‖_{Lᵖ} ≤ ε`. -/
theorem exists_schwartz_approx (p : ℝ) (hp : 1 < p) (g : ℝ → ℂ) (hg : Integrable g)
    (hgp : MemLp g (ENNReal.ofReal p) (volume : Measure ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : SchwartzMap ℝ ℂ,
      eLpNorm ((G : ℝ → ℂ) - g) 1 (volume : Measure ℝ) ≤ ENNReal.ofReal ε ∧
      eLpNorm ((G : ℝ → ℂ) - g) (ENNReal.ofReal p) (volume : Measure ℝ) ≤
        ENNReal.ofReal ε := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hPtop : P ≠ ∞ := by rw [hP]; exact ENNReal.ofReal_ne_top
  have hP0 : P ≠ 0 := by rw [hP]; positivity
  have hPtoReal : P.toReal = p := by rw [hP]; exact ENNReal.toReal_ofReal hp0.le
  have h1P : (1 : ℝ≥0∞) ≤ P := by
    rw [hP, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hp.le
  -- choose a bump so that both tails are small
  have hev1 : ∀ᶠ m : ℕ in atTop,
      ∫⁻ x, ‖g x * (1 - ((stdBump m) x : ℂ))‖ₑ ∂(volume : Measure ℝ) ≤
        ENNReal.ofReal (ε / 4) :=
    (ENNReal.tendsto_nhds_zero.mp (tendsto_tail_enorm g hg)) _ (by positivity)
  have hevp : ∀ᶠ m : ℕ in atTop,
      ∫⁻ x, ‖g x * (1 - ((stdBump m) x : ℂ))‖ₑ ^ p ∂(volume : Measure ℝ) ≤
        ENNReal.ofReal ((ε / 4) ^ p) :=
    (ENNReal.tendsto_nhds_zero.mp (tendsto_tail_enorm_rpow p hp0 g hgp)) _ (by positivity)
  obtain ⟨m, hm1, hmp⟩ := (hev1.and hevp).exists
  let φ : ContDiffBump (0 : ℝ) := stdBump m
  let K : Set ℝ := tsupport (⇑φ)
  let c : ℝ := (2 * ((m : ℝ) + 2)) ^ (1 - 1 / p)
  let δ : ℝ := ε / (4 * (c + 1))
  have hcnonneg : 0 ≤ c := by simp only [c]; positivity
  have hδpos : 0 < δ := by simp only [δ]; positivity
  have hδnonneg : 0 ≤ δ := hδpos.le
  have hδle : δ ≤ ε / 4 := by
    simp only [δ]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (c + 1))]
    nlinarith [hε.le, hcnonneg]
  have hδc : δ * c ≤ ε / 4 := by
    have h1 : δ * c = ε * c / (4 * (c + 1)) := by
      simp only [δ]; ring
    rw [h1, div_le_iff₀ (by positivity : (0:ℝ) < 4 * (c + 1))]
    nlinarith [hε.le, hcnonneg]
  -- smooth compactly supported `Lᵖ`-approximation of `g`
  obtain ⟨h, hhcomp, hhdiff, hherr⟩ := MemLp.exist_eLpNorm_sub_le hPtop h1P hgp hδpos
  -- multiply by the bump
  have hφdiff : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => ((φ : ℝ → ℝ) x : ℂ)) :=
    (Complex.ofRealCLM.contDiff).comp (ContDiffBump.contDiff φ (n := (⊤ : ℕ∞)))
  have hφcont : Continuous (fun x : ℝ => ((φ : ℝ → ℝ) x : ℂ)) := hφdiff.continuous
  let G0 : ℝ → ℂ := fun x => h x * ((φ : ℝ → ℝ) x : ℂ)
  have hG0comp : HasCompactSupport G0 :=
    hhcomp.mul_right (f' := fun x : ℝ => ((φ : ℝ → ℝ) x : ℂ))
  have hG0diff : ContDiff ℝ (↑(⊤ : ℕ∞)) G0 :=
    hhdiff.mul hφdiff
  let G : SchwartzMap ℝ ℂ := hG0comp.toSchwartzMap hG0diff
  have hGcoe : (G : ℝ → ℂ) = G0 := rfl
  -- the two pieces of the error
  let u : ℝ → ℂ := fun x => g x * (1 - ((φ : ℝ → ℝ) x : ℂ))
  let v : ℝ → ℂ := fun x => (g x - h x) * ((φ : ℝ → ℝ) x : ℂ)
  have hsplit : g - G0 = u + v := by
    funext x
    simp only [u, v, G0, Pi.sub_apply, Pi.add_apply]
    ring
  have haesm_u : AEStronglyMeasurable u (volume : Measure ℝ) := by
    have h1 : AEStronglyMeasurable (fun x : ℝ => 1 - ((φ : ℝ → ℝ) x : ℂ)) (volume : Measure ℝ) :=
      (continuous_const.sub hφcont).aestronglyMeasurable
    exact hg.aestronglyMeasurable.mul h1
  have haesm_v : AEStronglyMeasurable v (volume : Measure ℝ) := by
    have h1 : AEStronglyMeasurable (fun x : ℝ => ((φ : ℝ → ℝ) x : ℂ)) (volume : Measure ℝ) :=
      hφcont.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x : ℝ => g x - h x) (volume : Measure ℝ) :=
      hg.aestronglyMeasurable.sub hhdiff.continuous.aestronglyMeasurable
    exact h2.mul h1
  -- pointwise domination of `v` by the error
  have hv_le : ∀ x : ℝ, ‖v x‖ ≤ ‖(g - h) x‖ := by
    intro x
    simp only [v, Pi.sub_apply]
    calc ‖(g x - h x) * ((φ : ℝ → ℝ) x : ℂ)‖
        ≤ ‖g x - h x‖ * ‖((φ : ℝ → ℝ) x : ℂ)‖ := norm_mul_le _ _
      _ ≤ ‖g x - h x‖ * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            rw [show ((φ : ℝ → ℝ) x : ℂ) = ((stdBump m) x : ℂ) from rfl]
            exact norm_stdBump_le_one m x
      _ = ‖g x - h x‖ := mul_one _
  have hsupp_v : Function.support v ⊆ K := by
    intro x hx
    rw [Function.mem_support] at hx
    have hφx : ((φ : ℝ → ℝ) x : ℂ) ≠ 0 := fun hz => hx (by simp [v, hz])
    have hφx' : (φ : ℝ → ℝ) x ≠ 0 := fun hz => hφx (by rw [hz]; simp)
    exact subset_closure (Function.mem_support.mpr hφx')
  -- volume of the support of the bump
  have hvolK : (volume : Measure ℝ) K = ENNReal.ofReal (2 * ((m : ℝ) + 2)) := by
    simp only [K, φ, stdBump, ContDiffBump.tsupport_eq, Real.volume_closedBall]
  have hcEq : ((volume : Measure ℝ) K) ^ (1 - 1 / p) = ENNReal.ofReal c := by
    rw [hvolK]
    simp only [c]
    refine ENNReal.ofReal_rpow_of_nonneg (by positivity) ?_
    rw [sub_nonneg, div_le_one hp0]
    linarith
  -- Hölder on the (compact) support of the bump
  have hvolKuniv : ((volume : Measure ℝ).restrict K) Set.univ = (volume : Measure ℝ) K := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  have haesm_v_K : AEStronglyMeasurable v ((volume : Measure ℝ).restrict K) :=
    haesm_v.mono_measure Measure.restrict_le_self
  have hHold : eLpNorm v 1 (volume : Measure ℝ)
      ≤ eLpNorm (g - h) P (volume : Measure ℝ) * ((volume : Measure ℝ) K) ^ (1 - 1 / p) := by
    calc eLpNorm v 1 (volume : Measure ℝ)
        = eLpNorm v 1 ((volume : Measure ℝ).restrict K) :=
          (eLpNorm_restrict_eq_of_support_subset haesm_v hsupp_v).symm
      _ ≤ eLpNorm v P ((volume : Measure ℝ).restrict K)
            * (((volume : Measure ℝ).restrict K) Set.univ) ^ (1 / 1 - 1 / P.toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ h1P haesm_v_K
      _ ≤ eLpNorm (g - h) P ((volume : Measure ℝ).restrict K)
            * (((volume : Measure ℝ).restrict K) Set.univ) ^ (1 / 1 - 1 / P.toReal) :=
          mul_le_mul_left (eLpNorm_mono haesm_v_K hv_le) _
      _ ≤ eLpNorm (g - h) P (volume : Measure ℝ) * ((volume : Measure ℝ) K) ^ (1 - 1 / p) := by
          rw [hvolKuniv]
          simp only [one_div_one, hPtoReal]
          exact mul_le_mul_left (eLpNorm_restrict_le _ _ _ _) _
  have hv1 : eLpNorm v 1 (volume : Measure ℝ) ≤ ENNReal.ofReal (ε / 4) := by
    calc eLpNorm v 1 (volume : Measure ℝ)
        ≤ eLpNorm (g - h) P (volume : Measure ℝ) * ((volume : Measure ℝ) K) ^ (1 - 1 / p) :=
          hHold
      _ ≤ ENNReal.ofReal δ * ((volume : Measure ℝ) K) ^ (1 - 1 / p) :=
          mul_le_mul_left hherr _
      _ = ENNReal.ofReal δ * ENNReal.ofReal c := by rw [hcEq]
      _ = ENNReal.ofReal (δ * c) := (ENNReal.ofReal_mul hδnonneg).symm
      _ ≤ ENNReal.ofReal (ε / 4) := ENNReal.ofReal_le_ofReal hδc
  have hvP : eLpNorm v P (volume : Measure ℝ) ≤ ENNReal.ofReal δ :=
    le_trans (eLpNorm_mono haesm_v hv_le) hherr
  -- the two pieces of the error again: `u`
  have hu1 : eLpNorm u 1 (volume : Measure ℝ) ≤ ENNReal.ofReal (ε / 4) := by
    rw [eLpNorm_one_eq_lintegral_enorm haesm_u]
    simpa only [u, φ] using hm1
  have huP : eLpNorm u P (volume : Measure ℝ) ≤ ENNReal.ofReal (ε / 4) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop haesm_u, hPtoReal]
    calc (∫⁻ x, ‖u x‖ₑ ^ p ∂(volume : Measure ℝ)) ^ (1 / p)
        ≤ (ENNReal.ofReal ((ε / 4) ^ p)) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (by simpa only [u, φ] using hmp) (by positivity)
      _ = ENNReal.ofReal (((ε / 4) ^ p) ^ (1 / p)) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
      _ = ENNReal.ofReal (ε / 4) := by
          congr 1
          rw [← Real.rpow_mul (show (0 : ℝ) ≤ ε / 4 by positivity),
            show p * (1 / p) = 1 by rw [mul_one_div_cancel hp0.ne'], Real.rpow_one]
  -- assemble
  have hgG0_1 : eLpNorm (g - G0) 1 (volume : Measure ℝ) ≤ ENNReal.ofReal ε := by
    calc eLpNorm (g - G0) 1 (volume : Measure ℝ)
        = eLpNorm (u + v) 1 (volume : Measure ℝ) := by rw [hsplit]
      _ ≤ eLpNorm u 1 (volume : Measure ℝ) + eLpNorm v 1 (volume : Measure ℝ) :=
          eLpNorm_add_le le_rfl
      _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := add_le_add hu1 hv1
      _ = ENNReal.ofReal (ε / 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)
  have hgG0_P : eLpNorm (g - G0) P (volume : Measure ℝ) ≤ ENNReal.ofReal ε := by
    calc eLpNorm (g - G0) P (volume : Measure ℝ)
        = eLpNorm (u + v) P (volume : Measure ℝ) := by rw [hsplit]
      _ ≤ eLpNorm u P (volume : Measure ℝ) + eLpNorm v P (volume : Measure ℝ) :=
          eLpNorm_add_le h1P
      _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal δ := add_le_add huP hvP
      _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal hδle)
      _ = ENNReal.ofReal (ε / 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨G, ?_, ?_⟩
  · rw [hGcoe]
    have h1 : G0 - g = -(g - G0) := by
      funext x
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    rw [h1, eLpNorm_neg]
    exact hgG0_1
  · rw [hGcoe]
    have h1 : G0 - g = -(g - G0) := by
      funext x
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    rw [h1, eLpNorm_neg]
    exact hgG0_P

theorem schwartz_density_L1Lp (p : ℝ) (hp : 1 < p) (g : ℝ → ℂ)
    (hg : MeasureTheory.Integrable g)
    (hgp : MeasureTheory.MemLp g (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∃ G : ℕ → SchwartzMap ℝ ℂ,
      Filter.Tendsto (fun n : ℕ => ∫ x : ℝ, ‖(G n : ℝ → ℂ) x - g x‖ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n : ℕ => MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
          (fun x : ℝ => ENNReal.rpow (enorm ((G n : ℝ → ℂ) x - g x)) p)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n : ℕ => MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
          (fun x : ℝ => ENNReal.rpow (enorm ((G n : ℝ → ℂ) x)) p)) Filter.atTop
        (nhds (MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
          (fun x : ℝ => ENNReal.rpow (enorm (g x)) p))) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hPtop : P ≠ ∞ := by rw [hP]; exact ENNReal.ofReal_ne_top
  have hP0 : P ≠ 0 := by rw [hP]; positivity
  have h1P : (1 : ℝ≥0∞) ≤ P := by
    rw [hP, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hkey : ∀ n : ℕ, ∃ G : SchwartzMap ℝ ℂ,
      eLpNorm ((G : ℝ → ℂ) - g) 1 (volume : Measure ℝ) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧
      eLpNorm ((G : ℝ → ℂ) - g) (ENNReal.ofReal p) (volume : Measure ℝ) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    fun n => exists_schwartz_approx p hp g hg hgp (by positivity)
  choose G hG1 hG2 using hkey
  have heps : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [show ENNReal.ofReal (0 : ℝ) = 0 from by simp] at h
    exact Tendsto.congr (fun n => rfl) h
  have hdiffconv : Tendsto (fun n : ℕ => eLpNorm ((G n : ℝ → ℂ) - g) P (volume : Measure ℝ))
      atTop (nhds 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro e he
    filter_upwards [(ENNReal.tendsto_nhds_zero.mp heps e he)] with n hn
    have h1 : eLpNorm ((G n : ℝ → ℂ) - g) P (volume : Measure ℝ)
        ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by rw [hP]; exact hG2 n
    exact le_trans h1 hn
  refine ⟨G, ?_, ?_, ?_⟩
  · -- `L¹` convergence
    have hbound : ∀ n : ℕ, ∫ x : ℝ, ‖(G n : ℝ → ℂ) x - g x‖ ∂(volume : Measure ℝ)
        ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have haesm : AEStronglyMeasurable (fun x : ℝ => (G n : ℝ → ℂ) x - g x)
          (volume : Measure ℝ) :=
        ((G n).continuous.aestronglyMeasurable).sub hg.aestronglyMeasurable
      have h1 : ∫ x : ℝ, ‖(G n : ℝ → ℂ) x - g x‖ ∂(volume : Measure ℝ)
          = (eLpNorm ((G n : ℝ → ℂ) - g) 1 (volume : Measure ℝ)).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm (f := (G n : ℝ → ℂ) - g) haesm]
        exact integral_norm_eq_lintegral_enorm haesm
      rw [h1]
      calc (eLpNorm ((G n : ℝ → ℂ) - g) 1 (volume : Measure ℝ)).toReal
          ≤ (ENNReal.ofReal (1 / ((n : ℝ) + 1))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (hG1 n)
        _ = 1 / ((n : ℝ) + 1) := ENNReal.toReal_ofReal (by positivity)
    refine squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) hbound ?_
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · -- `Lᵖ` convergence
    have hbound : ∀ n : ℕ,
        ∫⁻ x, ENNReal.rpow (enorm ((G n : ℝ → ℂ) x - g x)) p ∂(volume : Measure ℝ)
          ≤ ENNReal.ofReal ((1 / ((n : ℝ) + 1)) ^ p) := by
      intro n
      have h1 : ∫⁻ x, ENNReal.rpow (enorm ((G n : ℝ → ℂ) x - g x)) p ∂(volume : Measure ℝ)
          = (eLpNorm ((G n : ℝ → ℂ) - g) (ENNReal.ofReal p) (volume : Measure ℝ)) ^ p :=
        (eLpNorm_rpow_eq_lintegral p hp0 _
          ((G n).continuous.aestronglyMeasurable.sub hg.aestronglyMeasurable)).symm
      rw [h1]
      calc (eLpNorm ((G n : ℝ → ℂ) - g) (ENNReal.ofReal p) (volume : Measure ℝ)) ^ p
          ≤ (ENNReal.ofReal (1 / ((n : ℝ) + 1))) ^ p := ENNReal.rpow_le_rpow (hG2 n) (by positivity)
        _ = ENNReal.ofReal ((1 / ((n : ℝ) + 1)) ^ p) :=
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / ((n : ℝ) + 1)) ^ p)) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ p) atTop (nhds 0) := by
        have h2 := (Real.continuous_rpow_const hp0.le).tendsto 0
        rw [Real.zero_rpow hp0.ne'] at h2
        exact h2.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
      rw [show ENNReal.ofReal (0 : ℝ) = 0 from by simp] at h2
      exact Tendsto.congr (fun n => rfl) h2
    rw [ENNReal.tendsto_nhds_zero]
    intro e he
    filter_upwards [(ENNReal.tendsto_nhds_zero.mp hlim e he)] with n hn
    exact le_trans (hbound n) hn
  · -- convergence of the `p`-th power integrals
    have hEtop : eLpNorm g (ENNReal.ofReal p) (volume : Measure ℝ) ≠ ∞ := hgp.eLpNorm_ne_top
    have hEconv : Tendsto (fun n : ℕ => eLpNorm (G n) (ENNReal.ofReal p) (volume : Measure ℝ))
        atTop (nhds (eLpNorm g (ENNReal.ofReal p) (volume : Measure ℝ))) := by
      rw [ENNReal.tendsto_nhds hEtop]
      intro ee hee
      filter_upwards [(ENNReal.tendsto_nhds_zero.mp hdiffconv ee hee)] with n hn
      have haesm_G : AEStronglyMeasurable (G n : ℝ → ℂ) (volume : Measure ℝ) :=
        (G n).continuous.aestronglyMeasurable
      have hle1 : eLpNorm (G n) P (volume : Measure ℝ)
          ≤ eLpNorm g P (volume : Measure ℝ) + eLpNorm ((G n : ℝ → ℂ) - g) P (volume : Measure ℝ) := by
        have hd2 : AEStronglyMeasurable (fun x : ℝ => (G n : ℝ → ℂ) x - g x)
            (volume : Measure ℝ) := haesm_G.sub hg.aestronglyMeasurable
        have h' := eLpNorm_add_le (f := fun x : ℝ => g x)
          (g := fun x : ℝ => (G n : ℝ → ℂ) x - g x) (μ := volume) h1P
        have heq : ((fun x : ℝ => g x) + fun x : ℝ => (G n : ℝ → ℂ) x - g x) =
            (G n : ℝ → ℂ) := by
          funext x; simp only [Pi.add_apply]; ring
        rw [heq] at h'
        exact h'
      have hle2 : eLpNorm g P (volume : Measure ℝ)
          ≤ eLpNorm (G n) P (volume : Measure ℝ) + eLpNorm ((G n : ℝ → ℂ) - g) P (volume : Measure ℝ) := by
        have hd2 : AEStronglyMeasurable (fun x : ℝ => g x - (G n : ℝ → ℂ) x)
            (volume : Measure ℝ) := hg.aestronglyMeasurable.sub haesm_G
        have h' := eLpNorm_add_le (f := fun x : ℝ => (G n : ℝ → ℂ) x)
          (g := fun x : ℝ => g x - (G n : ℝ → ℂ) x) (μ := volume) h1P
        have heq : ((fun x : ℝ => (G n : ℝ → ℂ) x) + fun x : ℝ => g x - (G n : ℝ → ℂ) x)
            = g := by
          funext x; simp only [Pi.add_apply]; ring
        have hneg : eLpNorm (fun x : ℝ => g x - (G n : ℝ → ℂ) x) P (volume : Measure ℝ)
            = eLpNorm ((G n : ℝ → ℂ) - g) P (volume : Measure ℝ) := by
          have hh : (fun x : ℝ => g x - (G n : ℝ → ℂ) x) = -((G n : ℝ → ℂ) - g) := by
            funext x; simp only [Pi.sub_apply, Pi.neg_apply]; ring
          rw [hh]; exact eLpNorm_neg _ _ _
        rw [heq, hneg] at h'
        exact h'
      refine ⟨?_, ?_⟩
      · rw [tsub_le_iff_right]
        exact le_trans hle2 (add_le_add le_rfl hn)
      · exact le_trans hle1 (add_le_add le_rfl hn)
    have h3 : Tendsto (fun n : ℕ => (eLpNorm (G n) (ENNReal.ofReal p) (volume : Measure ℝ)) ^ p)
        atTop (nhds ((eLpNorm g (ENNReal.ofReal p) (volume : Measure ℝ)) ^ p)) :=
      ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp hEconv
    have h4 := Tendsto.congr
      (fun n => eLpNorm_rpow_eq_lintegral p hp0 (fun x => (G n : ℝ → ℂ) x)
        (G n).continuous.aestronglyMeasurable) h3
    rwa [eLpNorm_rpow_eq_lintegral p hp0 g hg.aestronglyMeasurable] at h4

end

end Work.BourgainPlan.Maximal
