import Mathlib

noncomputable section

namespace Work.Beltrami

open MeasureTheory Filter
open scoped ContDiff FourierTransform ENNReal NNReal Topology

/-! ### Auxiliary limits and inequalities -/

/-- `(e^{2πi t y} - 1)/t → 2πi y` as `t → 0`, `t ≠ 0`. -/
lemma tendsto_fourierChar_sub_div (y : ℝ) :
    Tendsto (fun t : ℝ => (((Real.fourierChar (t * y) : Circle) : ℂ) - 1) / t)
      (𝓝[≠] (0:ℝ)) (𝓝 (2 * ↑Real.pi * Complex.I * (y:ℂ))) := by
  have hfun : (fun t : ℝ => ((Real.fourierChar (t * y) : Circle) : ℂ)) =
      fun t : ℝ => Complex.exp ((2 * ↑Real.pi * Complex.I * (y:ℂ)) * (t:ℂ)) := by
    funext t
    rw [Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) (1:ℂ) 0 := Complex.ofRealCLM.hasDerivAt
  have hlin : HasDerivAt (fun t : ℝ => (2 * ↑Real.pi * Complex.I * (y:ℂ)) * (t:ℂ))
      (2 * ↑Real.pi * Complex.I * (y:ℂ)) 0 := by
    simpa using h1.const_mul (2 * ↑Real.pi * Complex.I * (y:ℂ))
  have hderiv : HasDerivAt (fun t : ℝ => Complex.exp ((2 * ↑Real.pi * Complex.I * (y:ℂ)) * (t:ℂ)))
      (2 * ↑Real.pi * Complex.I * (y:ℂ)) 0 := by
    have h := hlin.cexp
    simpa [mul_zero, Complex.exp_zero] using h
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp (hfun ▸ hderiv)
  have h0 : ((Real.fourierChar ((0:ℝ) * y) : Circle) : ℂ) = 1 := by
    rw [Real.fourierChar_apply]; simp
  convert hslope using 2
  · rw [zero_add, h0, Complex.real_smul, div_eq_mul_inv, Complex.ofReal_inv]
    ring

/-- A sequence bounded above has `liminf` bounded by the same bound. -/
lemma liminf_le_of_forall_le {u : ℕ → ℝ≥0∞} {Cb : ℝ≥0∞} (h : ∀ n, u n ≤ Cb) :
    Filter.liminf u Filter.atTop ≤ Cb := by
  rw [Filter.liminf_eq_iSup_iInf]
  refine iSup_le fun s => iSup_le fun hs => ?_
  obtain ⟨n, hn⟩ := Filter.mem_atTop_sets.mp hs
  exact le_trans (iInf₂_le n (hn n le_rfl)) (h n)

/-- `t_k = 1/(k+1)`. -/
def dseq (k : ℕ) : ℝ := ((k+1 : ℕ) : ℝ)⁻¹

lemma dseq_pos (k : ℕ) : 0 < dseq k := by unfold dseq; positivity

lemma tendsto_dseq_nhdsWithin : Tendsto dseq atTop (𝓝[≠] (0:ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h1 : Tendsto (fun k : ℕ => ((k+1:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact tendsto_inv_atTop_zero.comp h1
  · exact Filter.Eventually.of_forall (fun k => (dseq_pos k).ne')

lemma tendsto_dseq_fourierChar (y : ℝ) :
    Tendsto (fun k : ℕ => (((Real.fourierChar (dseq k * y) : Circle) : ℂ) - 1) / dseq k)
      atTop (𝓝 (2 * ↑Real.pi * Complex.I * (y:ℂ))) :=
  (tendsto_fourierChar_sub_div y).comp tendsto_dseq_nhdsWithin

/-- `(∫ ‖f‖²)^{1/2} ≤ R` gives the corresponding bound on the lintegral. -/
lemma lintegral_rpow_two_le {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) {R : ℝ≥0∞}
    (h : eLpNorm f 2 volume ≤ R) :
    ∫⁻ ξ, ‖f ξ‖ₑ ^ (2:ℝ) ≤ R ^ (2:ℝ) := by
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := f) (p := 2) (by norm_num) hf
  have h2' : eLpNorm f 2 volume ^ (2:ℝ) = ∫⁻ ξ, ‖f ξ‖ₑ ^ (2:ℝ) := by simpa using h2
  rw [← h2']
  exact ENNReal.rpow_le_rpow h (by norm_num)

/-- `‖(e^{2πix})^M z‖² = x^{2M} ‖z‖²` (as `ℝ≥0∞`). -/
lemma ofReal_pow_mul_enorm (x : ℝ) (M : ℕ) (z : ℂ) :
    ENNReal.ofReal (x ^ (2*M)) * ‖z‖ₑ ^ (2:ℝ) = ‖((x:ℂ) ^ M * z)‖ₑ ^ (2:ℝ) := by
  rw [ENNReal.rpow_two, ENNReal.rpow_two, enorm_mul, mul_pow]
  congr 1
  rw [enorm_pow, show ‖(x:ℂ)‖ₑ = ENNReal.ofReal |x| by rw [← ofReal_norm]; simp,
    ← ENNReal.ofReal_pow (abs_nonneg x) M,
    ← ENNReal.ofReal_pow (pow_nonneg (abs_nonneg x) M) 2]
  congr 1
  rw [← pow_mul, Nat.mul_comm M 2, ← abs_pow,
    abs_of_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) M)]

lemma norm_pow_le_two_pi (x : ℝ) (M : ℕ) :
    ‖((x:ℂ)^M)‖ ≤ ‖((2 * ↑Real.pi * Complex.I * (x:ℂ))^M)‖ := by
  have h1 : ‖(x:ℂ)‖ = |x| := by simp
  have h2 : ‖(2 * ↑Real.pi * Complex.I * (x:ℂ))‖ = 2 * Real.pi * |x| := by
    rw [norm_mul, norm_mul, norm_mul]; simp
  rw [norm_pow, norm_pow, h1, h2]
  exact pow_le_pow_left₀ (abs_nonneg x)
    (by have := Real.pi_gt_three; nlinarith [abs_nonneg x]) M

lemma enorm_pow_le_two_pi (x : ℝ) (M : ℕ) (z : ℂ) :
    ‖((x:ℂ)^M * z)‖ₑ ≤ ‖((2 * ↑Real.pi * Complex.I * (x:ℂ))^M * z)‖ₑ := by
  rw [enorm_mul, enorm_mul]
  refine mul_le_mul_of_nonneg_right ?_ zero_le
  rw [← ofReal_norm ((x:ℂ)^M), ← ofReal_norm ((2 * ↑Real.pi * Complex.I * (x:ℂ))^M)]
  exact ENNReal.ofReal_le_ofReal (norm_pow_le_two_pi x M)

lemma max_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) : max a b ^ m ≤ a^m + b^m := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact le_add_of_nonneg_left (pow_nonneg ha m)
  · rw [max_eq_left h]; exact le_add_of_nonneg_right (pow_nonneg hb m)

lemma one_add_sq_add_sq_pow_le (x y : ℝ) (m : ℕ) :
    (1 + x^2 + y^2)^m ≤ 3^m * (1 + (x^2)^m + (y^2)^m) := by
  have hle : 1 + x^2 + y^2 ≤ 3 * max 1 (max (x^2) (y^2)) := by
    have h1 : (1:ℝ) ≤ max 1 (max (x^2) (y^2)) := le_max_left _ _
    have h2 : x^2 ≤ max 1 (max (x^2) (y^2)) := le_trans (le_max_left _ _) (le_max_right _ _)
    have h3 : y^2 ≤ max 1 (max (x^2) (y^2)) := le_trans (le_max_right _ _) (le_max_right _ _)
    nlinarith
  calc (1 + x^2 + y^2)^m ≤ (3 * max 1 (max (x^2) (y^2)))^m := pow_le_pow_left₀ (by positivity) hle m
    _ = 3^m * (max 1 (max (x^2) (y^2)))^m := by rw [mul_pow]
    _ ≤ 3^m * (1 + (x^2)^m + (y^2)^m) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (max 1 (max (x^2) (y^2)))^m ≤ 1^m + (max (x^2) (y^2))^m :=
              max_pow_le _ _ zero_le_one (le_trans (sq_nonneg x) (le_max_left _ _)) m
          _ = 1 + (max (x^2) (y^2))^m := by rw [one_pow]
          _ ≤ 1 + ((x^2)^m + (y^2)^m) := by
              have := max_pow_le (x^2) (y^2) (sq_nonneg x) (sq_nonneg y) m
              linarith
          _ = 1 + (x^2)^m + (y^2)^m := by ring

/-! ### The moment bound -/

theorem moment_lintegral_lt_top {V : Lp ℂ 2 volume} {C : ℕ → ℝ}
    (hC : ∀ (N : ℕ) (h : ℂ), eLpNorm (fun ξ : ℂ =>
        (((Real.fourierChar (inner ℝ h ξ) : Circle) : ℂ) - 1) ^ N * V ξ) 2 volume
        ≤ ENNReal.ofReal (C N * ‖h‖ ^ N))
    {d : ℂ} (hd : ‖d‖ = 1) {c : ℂ → ℝ} (hcont : Continuous c)
    (hc : ∀ ξ, inner ℝ d ξ = c ξ) (M : ℕ) :
    ∫⁻ ξ : ℂ, ENNReal.ofReal ((c ξ) ^ (2 * M)) * ‖V ξ‖ₑ ^ (2 : ℝ) < ⊤ := by
  set G : ℕ → ℂ → ℂ := fun k ξ =>
    ((((Real.fourierChar (dseq k * c ξ) : Circle) : ℂ) - 1) / (dseq k)) ^ M * V ξ with hG
  have hG_le : ∀ k, eLpNorm (G k) 2 volume ≤ ENNReal.ofReal (C M) := by
    intro k
    have hF_le : eLpNorm (fun ξ : ℂ =>
        (((Real.fourierChar (dseq k * c ξ) : Circle) : ℂ) - 1) ^ M * V ξ) 2 volume
        ≤ ENNReal.ofReal (C M * (dseq k) ^ M) := by
      have h := hC M (dseq k • d)
      have hinner : ∀ ξ, inner ℝ (dseq k • d) ξ = dseq k * c ξ := by
        intro ξ; rw [real_inner_smul_left, hc ξ]
      have hnorm : ‖dseq k • d‖ = dseq k := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (dseq_pos k), hd, mul_one]
      simp only [hinner, hnorm] at h
      exact h
    have hFG : G k = ((↑(dseq k) : ℂ) ^ M)⁻¹ •
        (fun ξ : ℂ => (((Real.fourierChar (dseq k * c ξ) : Circle) : ℂ) - 1) ^ M * V ξ) := by
      rw [hG]
      funext ξ
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_pow, div_eq_mul_inv]
      ring
    rw [hFG, eLpNorm_const_smul]
    have hcnorm : ‖((↑(dseq k) : ℂ) ^ M)⁻¹‖ₑ = ENNReal.ofReal ((dseq k) ^ M)⁻¹ := by
      rw [← ofReal_norm]
      congr 1
      rw [norm_inv, norm_pow, show ‖(↑(dseq k) : ℂ)‖ = |dseq k| by simp, abs_of_pos (dseq_pos k)]
    rw [hcnorm]
    have heq : ENNReal.ofReal ((dseq k) ^ M)⁻¹ * ENNReal.ofReal (C M * (dseq k) ^ M) =
        ENNReal.ofReal (C M) := by
      rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr (pow_pos (dseq_pos k) M)))]
      congr 1
      calc ((dseq k) ^ M)⁻¹ * (C M * (dseq k) ^ M)
          = C M * (((dseq k) ^ M)⁻¹ * (dseq k) ^ M) := by ring
        _ = C M := by rw [inv_mul_cancel₀ (pow_pos (dseq_pos k) M).ne', mul_one]
    exact le_trans (mul_le_mul_of_nonneg_left hF_le zero_le) heq.le
  have hG_asm : ∀ k, AEStronglyMeasurable (G k) volume := by
    intro k
    rw [hG]
    have hc' : Continuous fun ξ : ℂ =>
        (((Real.fourierChar (dseq k * c ξ) : Circle) : ℂ) - 1) / (dseq k) := by
      have heq : (fun ξ : ℂ => (((Real.fourierChar (dseq k * c ξ) : Circle) : ℂ) - 1) /
            (dseq k)) =
          fun ξ => (Complex.exp (↑(2 * Real.pi * (dseq k * c ξ)) * Complex.I) - 1) /
            (dseq k) := by
        funext ξ; rw [Real.fourierChar_apply]
      rw [heq]; fun_prop
    exact ((hc'.pow M).aestronglyMeasurable).mul (Lp.aestronglyMeasurable V)
  have hG_aemeas : ∀ k, AEMeasurable (fun ξ : ℂ => ‖G k ξ‖ₑ ^ (2:ℝ)) volume := by
    intro k
    exact (ENNReal.continuous_rpow_const.comp continuous_enorm).measurable.comp_aemeasurable
      (hG_asm k).aemeasurable
  have hle : ∀ k, ∫⁻ ξ, ‖G k ξ‖ₑ ^ (2:ℝ) ≤ (ENNReal.ofReal (C M)) ^ (2:ℝ) :=
    fun k => lintegral_rpow_two_le (hG_asm k) (hG_le k)
  have hfatou : ∫⁻ ξ, Filter.liminf (fun k => ‖G k ξ‖ₑ ^ (2:ℝ)) atTop
      ≤ Filter.liminf (fun k => ∫⁻ ξ, ‖G k ξ‖ₑ ^ (2:ℝ)) atTop :=
    lintegral_liminf_le' hG_aemeas
  have hliminf : Filter.liminf (fun k => ∫⁻ ξ, ‖G k ξ‖ₑ ^ (2:ℝ)) atTop
      ≤ (ENNReal.ofReal (C M)) ^ (2:ℝ) := liminf_le_of_forall_le hle
  have hpt : ∀ ξ : ℂ, Filter.liminf (fun k => ‖G k ξ‖ₑ ^ (2:ℝ)) atTop
      = ‖(2 * ↑Real.pi * Complex.I * (c ξ : ℂ)) ^ M * V ξ‖ₑ ^ (2:ℝ) := by
    intro ξ
    have h4 : Tendsto (fun k : ℕ =>
        ‖((((Real.fourierChar (dseq k * c ξ) : Circle) : ℂ) - 1) / (dseq k)) ^ M * V ξ‖ₑ ^ (2:ℝ))
        atTop (𝓝 (‖(2 * ↑Real.pi * Complex.I * (c ξ : ℂ)) ^ M * V ξ‖ₑ ^ (2:ℝ))) := by
      have h3 := ((tendsto_dseq_fourierChar (c ξ)).pow M).mul_const (V ξ)
      exact ((ENNReal.continuous_rpow_const.comp continuous_enorm).tendsto _).comp h3
    have h5 : Tendsto (fun k : ℕ => ‖G k ξ‖ₑ ^ (2:ℝ)) atTop
        (𝓝 (‖(2 * ↑Real.pi * Complex.I * (c ξ : ℂ)) ^ M * V ξ‖ₑ ^ (2:ℝ))) := by
      simpa only [hG] using h4
    exact h5.liminf_eq
  have key : ∫⁻ ξ : ℂ, ‖(2 * ↑Real.pi * Complex.I * (c ξ : ℂ)) ^ M * V ξ‖ₑ ^ (2:ℝ) < ⊤ := by
    calc ∫⁻ ξ : ℂ, ‖(2 * ↑Real.pi * Complex.I * (c ξ : ℂ)) ^ M * V ξ‖ₑ ^ (2:ℝ)
        = ∫⁻ ξ : ℂ, Filter.liminf (fun k => ‖G k ξ‖ₑ ^ (2:ℝ)) atTop :=
          lintegral_congr (fun ξ => (hpt ξ).symm)
      _ ≤ Filter.liminf (fun k => ∫⁻ ξ, ‖G k ξ‖ₑ ^ (2:ℝ)) atTop := hfatou
      _ ≤ (ENNReal.ofReal (C M)) ^ (2:ℝ) := hliminf
      _ < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  calc ∫⁻ ξ : ℂ, ENNReal.ofReal ((c ξ) ^ (2 * M)) * ‖V ξ‖ₑ ^ (2:ℝ)
      ≤ ∫⁻ ξ : ℂ, ‖(2 * ↑Real.pi * Complex.I * (c ξ : ℂ)) ^ M * V ξ‖ₑ ^ (2:ℝ) := by
        refine lintegral_mono fun ξ => ?_
        rw [ofReal_pow_mul_enorm (c ξ) M (V ξ)]
        exact ENNReal.rpow_le_rpow (enorm_pow_le_two_pi (c ξ) M (V ξ)) (by norm_num)
    _ < ⊤ := key

/-! ### The main statement -/

/-- If `V : L²(ℂ)` satisfies the "sharp" higher-difference bounds
`‖(e^{2πi⟪h,ξ⟫}-1)^N V‖_{L²} ≤ C N ‖h‖^N` for all `N, h`, then every polynomial moment of `V` is
in `L²`; it suffices (and is what is proved) that `(1+‖ξ‖²)^N V ∈ L²` for all `N`. -/
theorem memLp_poly_mul_fourier {V : Lp ℂ 2 volume} (C : ℕ → ℝ)
    (hC : ∀ (N : ℕ) (h : ℂ), eLpNorm (fun ξ : ℂ =>
        (((Real.fourierChar (inner ℝ h ξ) : Circle) : ℂ) - 1) ^ N * V ξ) 2 volume
        ≤ ENNReal.ofReal (C N * ‖h‖ ^ N)) :
    ∀ N : ℕ, MemLp (fun ξ : ℂ => (1 + ‖ξ‖ ^ 2) ^ N * V ξ) 2 volume := by
  intro N
  have hre : ∀ M : ℕ, ∫⁻ ξ : ℂ, ENNReal.ofReal ((ξ.re) ^ (2 * M)) * ‖V ξ‖ₑ ^ (2:ℝ) < ⊤ :=
    fun M => moment_lintegral_lt_top hC (d := 1) (by simp) Complex.continuous_re
      (by intro ξ; simp) M
  have him : ∀ M : ℕ, ∫⁻ ξ : ℂ, ENNReal.ofReal ((ξ.im) ^ (2 * M)) * ‖V ξ‖ₑ ^ (2:ℝ) < ⊤ :=
    fun M => moment_lintegral_lt_top hC (d := Complex.I) (by simp) Complex.continuous_im
      (by intro ξ; simp) M
  have hsq : ∀ x : ℝ, 0 ≤ x ^ (2*(2*N)) := fun x => by
    rw [pow_mul]; exact pow_nonneg (sq_nonneg x) (2*N)
  have h3nn : (0:ℝ) ≤ (3:ℝ) ^ (2*N) := pow_nonneg (by norm_num) _
  have hV_asm : AEStronglyMeasurable (fun ξ : ℂ => V ξ) volume := Lp.aestronglyMeasurable V
  have hV_mem : eLpNorm (fun ξ : ℂ => V ξ) 2 volume < ⊤ := Lp.memLp V
  set γ : ℂ → ℝ≥0∞ := fun ξ => ‖V ξ‖ₑ ^ (2:ℝ) with hγ
  set A : ℂ → ℝ≥0∞ := fun ξ => ENNReal.ofReal ((ξ.re) ^ (2 * (2*N))) * γ ξ with hA
  set B : ℂ → ℝ≥0∞ := fun ξ => ENNReal.ofReal ((ξ.im) ^ (2 * (2*N))) * γ ξ with hB
  have hγ_meas : AEMeasurable γ volume := by
    rw [hγ]
    exact (ENNReal.continuous_rpow_const.comp continuous_enorm).measurable.comp_aemeasurable
      hV_asm.aemeasurable
  have hA_meas : AEMeasurable A volume := by
    rw [hA]
    refine AEMeasurable.mul ?_ hγ_meas
    exact (ENNReal.continuous_ofReal.measurable.comp
      (Complex.continuous_re.pow (2*(2*N))).measurable).aemeasurable
  have hB_meas : AEMeasurable B volume := by
    rw [hB]
    refine AEMeasurable.mul ?_ hγ_meas
    exact (ENNReal.continuous_ofReal.measurable.comp
      (Complex.continuous_im.pow (2*(2*N))).measurable).aemeasurable
  have hmain : ∫⁻ ξ : ℂ, ‖((1 + ‖ξ‖^2)^N : ℂ) * V ξ‖ₑ ^ (2:ℝ) ≤
      ENNReal.ofReal ((3:ℝ)^(2*N)) * ((∫⁻ ξ, γ ξ) + (∫⁻ ξ, A ξ) + (∫⁻ ξ, B ξ)) := by
    calc ∫⁻ ξ : ℂ, ‖((1 + ‖ξ‖^2)^N : ℂ) * V ξ‖ₑ ^ (2:ℝ)
        = ∫⁻ ξ : ℂ, ENNReal.ofReal ((1 + ‖ξ‖^2)^(2*N)) * γ ξ := by
            refine lintegral_congr fun ξ => ?_
            have hcoe : ((1 + (↑‖ξ‖ : ℂ)^2))^N = ((1 + ‖ξ‖^2 : ℝ) : ℂ)^N := by
              push_cast; ring
            rw [hγ, hcoe]
            exact (ofReal_pow_mul_enorm (1 + ‖ξ‖^2) N (V ξ)).symm
      _ ≤ ∫⁻ ξ : ℂ, ENNReal.ofReal ((3:ℝ)^(2*N)) * (γ ξ + A ξ + B ξ) := by
            refine lintegral_mono fun ξ => ?_
            have hbase : (1 + ‖ξ‖^2) = 1 + (ξ.re)^2 + (ξ.im)^2 := by
              rw [Complex.sq_norm, Complex.normSq_apply]; ring
            have hineq : (1 + ‖ξ‖^2)^(2*N) ≤
                (3:ℝ)^(2*N) * (1 + (ξ.re)^(2*(2*N)) + (ξ.im)^(2*(2*N))) := by
              rw [hbase]
              calc (1 + (ξ.re)^2 + (ξ.im)^2)^(2*N)
                  ≤ 3^(2*N) * (1 + ((ξ.re)^2)^(2*N) + ((ξ.im)^2)^(2*N)) :=
                    one_add_sq_add_sq_pow_le _ _ _
                _ = (3:ℝ)^(2*N) * (1 + (ξ.re)^(2*(2*N)) + (ξ.im)^(2*(2*N))) := by
                    rw [← pow_mul, ← pow_mul]
            calc ENNReal.ofReal ((1 + ‖ξ‖^2)^(2*N)) * γ ξ
                ≤ ENNReal.ofReal ((3:ℝ)^(2*N) *
                    (1 + (ξ.re)^(2*(2*N)) + (ξ.im)^(2*(2*N)))) * γ ξ :=
                    mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hineq) zero_le
              _ = ENNReal.ofReal ((3:ℝ)^(2*N)) *
                    ENNReal.ofReal (1 + (ξ.re)^(2*(2*N)) + (ξ.im)^(2*(2*N))) * γ ξ := by
                    rw [ENNReal.ofReal_mul' (by
                      have := hsq ξ.re; have := hsq ξ.im; positivity)]
              _ = ENNReal.ofReal ((3:ℝ)^(2*N)) * (γ ξ + A ξ + B ξ) := by
                    rw [ENNReal.ofReal_add (add_nonneg zero_le_one (hsq ξ.re)) (hsq ξ.im),
                        ENNReal.ofReal_add zero_le_one (hsq ξ.re), ENNReal.ofReal_one, hA, hB]
                    ring
      _ = ENNReal.ofReal ((3:ℝ)^(2*N)) * ∫⁻ ξ : ℂ, (γ ξ + A ξ + B ξ) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((3:ℝ)^(2*N)) * ((∫⁻ ξ, γ ξ) + (∫⁻ ξ, A ξ) + (∫⁻ ξ, B ξ)) := by
            have e1 : (∫⁻ ξ : ℂ, (γ ξ + A ξ) + B ξ) = (∫⁻ ξ : ℂ, γ ξ + A ξ) +
                ∫⁻ ξ : ℂ, B ξ := lintegral_add_left' (hγ_meas.add hA_meas) B
            have e2 : (∫⁻ ξ : ℂ, γ ξ + A ξ) = (∫⁻ ξ : ℂ, γ ξ) + ∫⁻ ξ : ℂ, A ξ :=
              lintegral_add_left' hγ_meas A
            rw [e1, e2]
  have hfin : ENNReal.ofReal ((3:ℝ)^(2*N)) * ((∫⁻ ξ, γ ξ) + (∫⁻ ξ, A ξ) + (∫⁻ ξ, B ξ)) < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hγ]
      exact lt_of_le_of_lt (lintegral_rpow_two_le hV_asm le_rfl)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hV_mem.ne)
    · rw [hA, hγ]; exact hre (2*N)
    · rw [hB, hγ]; exact him (2*N)
  have hlt : ∫⁻ ξ : ℂ, ‖((1 + ‖ξ‖^2)^N : ℂ) * V ξ‖ₑ ^ (2:ℝ) < ⊤ :=
    lt_of_le_of_lt hmain hfin
  have hc' : Continuous fun ξ : ℂ => ((1 + ‖ξ‖^2)^N : ℂ) :=
    (continuous_const.add ((Complex.continuous_ofReal.comp continuous_norm).pow 2)).pow N
  have hasm : AEStronglyMeasurable (fun ξ : ℂ => ((1 + ‖ξ‖^2)^N : ℂ) * V ξ) volume :=
    (hc'.aestronglyMeasurable).mul hV_asm
  rw [memLp_iff]
  have h2 := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := volume) (p := 2)
    (f := fun ξ : ℂ => ((1 + ‖ξ‖^2)^N : ℂ) * V ξ) (by norm_num) (by norm_num) hasm
  rw [h2]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne

end Work.Beltrami
