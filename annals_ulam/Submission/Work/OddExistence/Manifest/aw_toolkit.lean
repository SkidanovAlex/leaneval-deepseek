import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.KvecM_eq_Kvec
import Submission.Work.OddVolterra.KernelExt.JM_eq_J
import Submission.Work.OddVolterra.KernelExt.JM_diag
import Submission.Work.OddVolterra.KernelExt.Rnu_contDiff
import Submission.Work.OddVolterra.Existence.exists_bound_comp_pair_sub_param
import Submission.Work.OddVolterra.Existence.krad_pos_state_region
import Submission.Work.OddVolterra.Kernel.G2Deriv
import Submission.Work.OddVolterra.Existence.continuousOn_deriv_G2_apply

/-!
# Toolkit for the manifest-kernel closeness estimates (copy of the working prefix of
`Work.OddVolterra.Existence.aw_thetaM_tri_close`, in a private namespace).
-/

namespace Work.OddExistence.Manifest.AW

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra Work.OddVolterra.KernelExt

/-- Local copy of `hquot_contDiff`. -/
lemma hquot_contDiff_local {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × ℝ => hquot h p.1 p.2 :=
  Work.OddVolterra.Existence.hquot_contDiff hh

/-- `(√(τ(1-τ)))⁻¹ (1-τ)` is interval integrable on `[0,1]`. -/
lemma intervalIntegrable_abel_weight_one_sub :
    IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 - τ)) volume (0:ℝ) 1 := by
  refine (Commons.Geometry.Ulam.intervalIntegrable_abel_weight).mono_fun' ?_ ?_
  · exact (((Work.OddVolterra.measurable_sqrt_real.comp
      (measurable_id.mul (measurable_const.sub measurable_id))).inv).mul
        (measurable_const.sub measurable_id)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (by linarith [hτ.2]))]
    exact mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) (by linarith [hτ.1])

/-- The Abel weight `(τ(1-τ))^{-1/2}` times `(1-τ)` has integral at most `π` on `[0,1]`. -/
lemma aw_abel_weight_integral :
    (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 - τ)) ≤ Real.pi := by
  have hmono : (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 - τ)) ≤
      ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ :=
    intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_abel_weight_one_sub
      Commons.Geometry.Ulam.intervalIntegrable_abel_weight (fun x hx => by
        refine mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) ?_
        linarith [hx.1])
  rwa [Work.OddVolterra.Existence.abel_weight_integral] at hmono

/-- **Differentiation under the Abel average for an arbitrary measurable vector kernel.** -/
theorem aw_hasDerivAt_abelAvg {K : ℝ → Fin 2 → ℝ} (hK : Measurable K) {s σ : ℝ}
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hbdK : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      ‖K (x + τ * (σ - x))‖ ≤ C)
    (hdiff : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      DifferentiableAt ℝ K (x + τ * (σ - x)))
    (hbound : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖(1 - τ) • deriv K (x + τ * (σ - x))‖ ≤ C) :
    HasDerivAt (fun u : ℝ => ∫ τ in (0:ℝ)..1,
        (Real.sqrt (τ * (1 - τ)))⁻¹ • K (u + τ * (σ - u)))
      (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv K (s + τ * (σ - s)))) s := by
  have hw_int : IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) volume (0 : ℝ) 1 :=
    Commons.Geometry.Ulam.intervalIntegrable_abel_weight
  have hw_norm : ∀ τ : ℝ, ‖(Real.sqrt (τ * (1 - τ)))⁻¹‖ = (Real.sqrt (τ * (1 - τ)))⁻¹ := by
    intro τ
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hw_meas : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
    (Work.OddVolterra.measurable_sqrt_real.comp
      (measurable_id.mul (measurable_const.sub measurable_id))).inv
  set F : ℝ → ℝ → (Fin 2 → ℝ) := fun x τ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
      K (x + τ * (σ - x)) with hFdef
  set F' : ℝ → ℝ → (Fin 2 → ℝ) := fun x τ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
      ((1 - τ) • deriv K (x + τ * (σ - x))) with hF'def
  have hF_meas_all : ∀ x : ℝ, AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    intro x
    have hm : Measurable (fun τ : ℝ => K (x + τ * (σ - x))) :=
      hK.comp (by fun_prop : Measurable fun τ : ℝ => x + τ * (σ - x))
    exact (hw_meas.smul hm).aestronglyMeasurable
  have hF_meas : ∀ᶠ x in 𝓝 s, AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    Filter.Eventually.of_forall hF_meas_all
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    have hm : Measurable (fun τ : ℝ => deriv K (s + τ * (σ - s))) :=
      (measurable_deriv (𝕜 := ℝ) K).comp
        (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
    exact (hw_meas.smul ((measurable_const.sub measurable_id).smul hm)).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F s) volume (0:ℝ) 1 := by
    refine (hw_int.mul_const C).mono_fun' ?_ ?_
    · exact hF_meas.self_of_nhds
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      by_cases h1 : τ = 1
      · subst h1
        have hz : F s 1 = 0 := by
          simp only [hFdef]
          have hx1 : s + 1 * (σ - s) = σ := by ring
          rw [hx1]
          norm_num
        rw [hz]
        simp
      have hτIco : τ ∈ Set.Ico (0:ℝ) 1 := by
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
        exact ⟨le_of_lt hτ.1, lt_of_le_of_ne hτ.2 h1⟩
      have hK' := hbdK s ⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩ τ hτIco
      have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      calc ‖F s τ‖ = (Real.sqrt (τ * (1 - τ)))⁻¹ * ‖K (s + τ * (σ - s))‖ := by
              simp only [hFdef, norm_smul, hw_norm]
        _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := mul_le_mul_of_nonneg_left hK' hw
  have h_bound : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x ∈ Set.Ioo (s - δ) (s + δ), ‖F' x τ‖ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := by
    refine Filter.Eventually.of_forall (fun τ hτ x hx => ?_)
    have hτIcc : τ ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      exact ⟨le_of_lt hτ.1, hτ.2⟩
    have hK' := hbound x hx τ hτIcc
    have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    calc ‖F' x τ‖ = (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ‖(1 - τ) • deriv K (x + τ * (σ - x))‖ := by
            simp only [hF'def, norm_smul, hw_norm]
      _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := mul_le_mul_of_nonneg_left hK' hw
  have hbound_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * C) volume (0:ℝ) 1 :=
    hw_int.mul_const C
  have h_diff : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x ∈ Set.Ioo (s - δ) (s + δ), HasDerivAt (fun x => F x τ) (F' x τ) x := by
    refine Filter.Eventually.of_forall (fun τ hτ x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
    have hτIcc : τ ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hτ.1, hτ.2⟩
    by_cases h1 : τ = 1
    · subst h1
      have hzero : (fun x : ℝ => F x 1) = fun _ : ℝ => (0 : Fin 2 → ℝ) := by
        funext y
        simp only [hFdef, mul_one]
        have h1 : y + 1 * (σ - y) = σ := by ring
        rw [h1]
        norm_num
      have hzero' : F' x 1 = 0 := by
        simp only [hF'def, sub_self, zero_smul, smul_zero]
      rw [hzero, hzero']
      exact hasDerivAt_const x 0
    · have hτlt : τ < 1 := lt_of_le_of_ne hτIcc.2 h1
      have hinner : HasDerivAt (fun x : ℝ => x + τ * (σ - x)) (1 - τ) x := by
        have hfun : (fun x : ℝ => x + τ * (σ - x)) = fun x : ℝ => (1 - τ) * x + τ * σ := by
          funext y; ring
        rw [hfun]
        simpa using ((hasDerivAt_id x).const_mul (1 - τ)).add_const (τ * σ)
      have houter : HasDerivAt K (deriv K (x + τ * (σ - x))) (x + τ * (σ - x)) :=
        (hdiff x hx τ ⟨hτIcc.1, hτlt⟩).hasDerivAt
      have hcomp := houter.scomp (𝕜 := ℝ) (𝕜' := ℝ) (F := Fin 2 → ℝ) (x := x) hinner
      have hfull := hcomp.const_smul ((Real.sqrt (τ * (1 - τ)))⁻¹)
      refine hfull.congr_deriv ?_
      simp only [hFdef, hF'def]
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0:ℝ)) (b := 1) (μ := volume)
    (F := F) (F' := F') (x₀ := s) (s := Set.Ioo (s - δ) (s + δ))
    (bound := fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * C)
    (isOpen_Ioo.mem_nhds ⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩)
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa only [hFdef, hF'def] using hmain.2

/-! ## The recursion for the Bell numerator as a family of functions of the first slot -/

/-- Smoothness of the section `a ↦ Zrad h (a,σ,t)`. -/
lemma contDiff_Zrad_section {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => Zrad h (a, σ, t)) := by
  unfold Zrad line
  fun_prop

/-- Smoothness of the section `a ↦ Rnu ν h init m (a,σ,t)`. -/
lemma contDiff_Rnu_section (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ) (σ t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => Rnu ν h init m (a, σ, t)) :=
  (Rnu_contDiff_aux ν hh hinit m).comp
    (contDiff_id.prodMk (contDiff_const.prodMk contDiff_const))

/-- Casting a natural into `WithTop ℕ∞` stays below `⊤`. -/
lemma natCast_le_top_enat (j : ℕ) :
    ((j : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

/-- The derivative of a smooth function on `ℝ` is smooth. -/
lemma contDiff_deriv_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv f) := by
  simpa only [Function.iterate_one] using hf.iterate_deriv 1

/-- **The recursion for `Rnu` as a family of functions of the first slot.** -/
lemma Rnu_succ_fun (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ) (σ t : ℝ) :
    (fun a : ℝ => Rnu ν h init (m + 1) (a, σ, t)) =
      (fun a : ℝ => Zrad h (a, σ, t) * deriv (fun u : ℝ => Rnu ν h init m (u, σ, t)) a
        + (ν - (m : ℝ)) * deriv (fun u : ℝ => Zrad h (u, σ, t)) a
          * Rnu ν h init m (a, σ, t)) := by
  funext a
  have hR : DifferentiableAt ℝ (Rnu ν h init m) (a, σ, t) :=
    ((Rnu_contDiff_aux ν hh hinit m).contDiffAt).differentiableAt (by simp)
  have hZ : DifferentiableAt ℝ (Zrad h) (a, σ, t) :=
    ((Zrad_contDiff_aux hh).contDiffAt).differentiableAt (by simp)
  have h1 : deriv (fun u : ℝ => Rnu ν h init m (u, σ, t)) a
      = (fderiv ℝ (Rnu ν h init m) (a, σ, t)) (1, 0, 0) :=
    (hasDerivAt_section (F := Rnu ν h init m) (a, σ, t) hR).deriv
  have h2 : deriv (fun u : ℝ => Zrad h (u, σ, t)) a
      = (fderiv ℝ (Zrad h) (a, σ, t)) (1, 0, 0) :=
    (hasDerivAt_section (F := Zrad h) (a, σ, t) hZ).deriv
  simp only [Rnu]
  rw [h1, h2]

/-- **The `j`-th derivative of the recursion.**  Differentiating
`R_{m+1} = Z ∂R_m + (ν-m) ∂Z R_m` `j` times (Leibniz) gives the expression below. -/
lemma iteratedDeriv_Rnu_succ (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m j : ℕ) (σ t a : ℝ) :
    iteratedDeriv j (fun a : ℝ => Rnu ν h init (m + 1) (a, σ, t)) a =
      (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a *
           iteratedDeriv (j - i + 1) (fun a : ℝ => Rnu ν h init m (a, σ, t)) a))
      + (ν - (m : ℝ)) * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (iteratedDeriv (i + 1) (fun a : ℝ => Zrad h (a, σ, t)) a *
           iteratedDeriv (j - i) (fun a : ℝ => Rnu ν h init m (a, σ, t)) a)) := by
  rw [Rnu_succ_fun ν hh hinit m σ t]
  have hZs : ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => Zrad h (a, σ, t)) :=
    contDiff_Zrad_section hh σ t
  have hRs : ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => Rnu ν h init m (a, σ, t)) :=
    contDiff_Rnu_section ν hh hinit m σ t
  have hRd : ContDiff ℝ (⊤ : ℕ∞)
      (deriv (fun u : ℝ => Rnu ν h init m (u, σ, t))) := contDiff_deriv_of_contDiff hRs
  have hZd : ContDiff ℝ (⊤ : ℕ∞)
      (deriv (fun u : ℝ => Zrad h (u, σ, t))) :=
    contDiff_deriv_of_contDiff hZs
  have hsum : ContDiff ℝ (⊤ : ℕ∞)
      (fun a : ℝ => Zrad h (a, σ, t) * deriv (fun u : ℝ => Rnu ν h init m (u, σ, t)) a) :=
    hZs.mul hRd
  have hsum2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun a : ℝ => (ν - (m : ℝ)) * (deriv (fun u : ℝ => Zrad h (u, σ, t)) a *
        Rnu ν h init m (a, σ, t))) := contDiff_const.mul (hZd.mul hRs)
  have hsplit : (fun a : ℝ => Zrad h (a, σ, t) * deriv (fun u : ℝ => Rnu ν h init m (u, σ, t)) a
        + (ν - (m : ℝ)) * deriv (fun u : ℝ => Zrad h (u, σ, t)) a
          * Rnu ν h init m (a, σ, t)) =
      (fun a : ℝ => Zrad h (a, σ, t) * deriv (fun u : ℝ => Rnu ν h init m (u, σ, t)) a)
        + (fun a : ℝ => (ν - (m : ℝ)) * (deriv (fun u : ℝ => Zrad h (u, σ, t)) a
            * Rnu ν h init m (a, σ, t))) := by
    funext a
    simp only [Pi.add_apply]
    ring
  rw [hsplit, iteratedDeriv_add (hsum.contDiffAt.of_le (natCast_le_top_enat j))
        (hsum2.contDiffAt.of_le (natCast_le_top_enat j)),
    iteratedDeriv_const_mul (ν - (m : ℝ)) ((hZd.mul hRs).contDiffAt.of_le (natCast_le_top_enat j))]
  have hA : iteratedDeriv j (fun a : ℝ => Zrad h (a, σ, t) *
      deriv (fun u : ℝ => Rnu ν h init m (u, σ, t)) a) a =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a *
         iteratedDeriv (j - i + 1) (fun a : ℝ => Rnu ν h init m (a, σ, t)) a) := by
    rw [iteratedDeriv_fun_mul (hZs.contDiffAt.of_le (natCast_le_top_enat j)) (hRd.contDiffAt.of_le (natCast_le_top_enat j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← iteratedDeriv_succ' (f := fun a : ℝ => Rnu ν h init m (a, σ, t)) (n := j - i)]
    ring
  have hB : iteratedDeriv j (fun a : ℝ => deriv (fun u : ℝ => Zrad h (u, σ, t)) a *
      Rnu ν h init m (a, σ, t)) a =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (iteratedDeriv (i + 1) (fun a : ℝ => Zrad h (a, σ, t)) a *
         iteratedDeriv (j - i) (fun a : ℝ => Rnu ν h init m (a, σ, t)) a) := by
    rw [iteratedDeriv_fun_mul (hZd.contDiffAt.of_le (natCast_le_top_enat j)) (hRs.contDiffAt.of_le (natCast_le_top_enat j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← iteratedDeriv_succ' (f := fun a : ℝ => Zrad h (a, σ, t)) (n := i)]
    ring
  rw [hA, hB]


/-- The divided difference `H(s,σ) = ∫_0^1 h'(s + τ(σ-s)) dτ` is bounded by any global bound
of `|h'|` (local copy of `Work.OddVolterra.Existence.abs_hquot_le_state`). -/
lemma abs_hquot_le_state {h : ℝ → ℝ} {ε s σ : ℝ} (hε : ∀ t : ℝ, |deriv h t| ≤ ε) :
    |hquot h s σ| ≤ ε := by
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun τ : ℝ => deriv h (s + τ * (σ - s))) (C := ε) (by
      intro τ _
      simpa [Real.norm_eq_abs] using hε (s + τ * (σ - s)))
  have hint' : ‖∫ τ in (0 : ℝ)..1, deriv h (s + τ * (σ - s))‖ ≤ ε := by
    simpa using hint
  simpa [hquot, Real.norm_eq_abs] using hint'

/-! ## Quantitative positivity of the Abel radicand, and bounds on the divided difference -/

/-- **Quantitative positivity of the radicand.**  On the box `a ∈ [49/100, 1]`, `σ ∈ [1/2, 19/20]`
and `|t| ≥ 1/5`, the radicand `krad h σ t a` — as well as the unperturbed one — is at least
`1/10000`. -/
theorem krad_ge_box {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∀ a σ t : ℝ, 49 / 100 ≤ a → a ≤ 1 → 1 / 2 ≤ σ → σ ≤ 19 / 20 → 1 / 5 ≤ |t| →
      1 / 10000 ≤ Work.OddVolterra.krad h σ t a ∧
        1 / 10000 ≤ Work.OddVolterra.krad 0 σ t a := by
  have hh0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => hsmall 0 (by norm_num) x
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := fun x => by
    simpa using hsmall 1 (by norm_num) x
  have htau1 : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by
    rw [Work.OddVolterra.tau]; norm_num
  have htau2 : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := by
    rw [Work.OddVolterra.tau]; norm_num
  have hzero : ∀ x : ℝ, x < 4 / 5 → h x = 0 := by
    intro x hx
    by_contra hne
    have hmem := hsupp (Function.mem_support.mpr hne)
    rw [htau1, htau2] at hmem
    linarith [hmem.1]
  intro a σ t ha ha1 hσ hσ1 ht
  have hS : 0 < σ + a := by linarith
  have hSge : (99 : ℝ) / 100 ≤ σ + a := by linarith
  have hquotbd : |Work.OddVolterra.hquot h a σ| ≤ 1 / 100 :=
    abs_hquot_le_state hh1
  have hbnd := abs_le.mp hquotbd
  have hhl : |h σ + h a| ≤ 1 / 50 := by
    have h1 := abs_le.mp (hh0 σ)
    have h2 := abs_le.mp (hh0 a)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hhline : Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t
      = (σ + a) * t + (h σ + h a) := by
    unfold Work.OddVolterra.line; ring
  have hk : ∀ {t : ℝ}, 1 / 5 ≤ |t| →
      (19 : ℝ) / 100 * (89 / 500) ≤ Work.OddVolterra.krad h σ t a := by
    intro t ht
    have hhline' : Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t
        = (σ + a) * t + (h σ + h a) := by
      unfold Work.OddVolterra.line; ring
    rw [Work.OddVolterra.krad_apply, hhline']
    rcases lt_trichotomy t 0 with htn | htz | htp
    · have htle : t ≤ -(1 / 5) := by
        have h := ht; rw [abs_of_neg htn] at h; linarith
      have h1 : t + Work.OddVolterra.hquot h a σ ≤ -(19 / 100) := by linarith [hbnd.2]
      have h2 : (σ + a) * t + (h σ + h a) ≤ -(89 / 500) := by
        have h4 : h σ + h a ≤ 1 / 50 := (abs_le.mp hhl).2
        have hmul : (σ + a) * t ≤ -((σ + a) * (1 / 5)) := by
          have h := mul_le_mul_of_nonneg_left htle (le_of_lt hS)
          rwa [show (σ + a) * (-(1 / 5)) = -((σ + a) * (1 / 5)) by ring] at h
        have h5 : (99 : ℝ) / 100 * (1 / 5) ≤ (σ + a) * (1 / 5) :=
          mul_le_mul_of_nonneg_right hSge (by norm_num)
        linarith
      have h3 : (19 : ℝ) / 100 * (89 / 500) = (-(19 / 100)) * (-(89 / 500)) := by ring
      rw [h3]
      exact mul_le_mul_of_nonpos_of_nonpos h1 h2 (by linarith [h1]) (by norm_num)
    · rw [htz] at ht; norm_num at ht
    · have htge : 1 / 5 ≤ t := by
        have h := ht; rwa [abs_of_pos htp] at h
      have h1 : (19 : ℝ) / 100 ≤ t + Work.OddVolterra.hquot h a σ := by linarith [hbnd.1]
      have h2 : (89 : ℝ) / 500 ≤ (σ + a) * t + (h σ + h a) := by
        have h4 : -(1 / 50) ≤ h σ + h a := (abs_le.mp hhl).1
        have h5 : (99 : ℝ) / 100 * (1 / 5) ≤ (σ + a) * t :=
          le_trans (mul_le_mul_of_nonneg_right hSge (by norm_num))
            (mul_le_mul_of_nonneg_left htge (le_of_lt hS))
        linarith
      exact mul_le_mul_of_nonneg h1 h2 (by norm_num) (by linarith [h2])
  have hk0 : ∀ {t : ℝ}, 1 / 5 ≤ |t| → (1 : ℝ) / 10000 ≤ Work.OddVolterra.krad 0 σ t a := by
    intro t ht
    rw [Work.OddVolterra.krad_apply]
    have h1 : Work.OddVolterra.hquot (0 : ℝ → ℝ) a σ = 0 := by
      rw [Work.OddVolterra.hquot]; simp
    have h2 : Work.OddVolterra.line (0 : ℝ → ℝ) σ t = σ * t := by simp [Work.OddVolterra.line]
    have h3 : Work.OddVolterra.line (0 : ℝ → ℝ) a t = a * t := by simp [Work.OddVolterra.line]
    rw [h1, h2, h3, add_zero]
    have ht2 : 1 / 25 ≤ t ^ 2 := by
      have h2 : ((1 : ℝ) / 5) ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ (by norm_num) ht 2
      rw [sq_abs] at h2
      linarith
    have hfac : t * (σ * t + a * t) = (σ + a) * t ^ 2 := by ring
    rw [hfac]
    nlinarith [ht2, hSge]
  exact ⟨le_trans (by norm_num : (1 : ℝ) / 10000 ≤ 19 / 100 * (89 / 500)) (hk ht), hk0 ht⟩

/-- Bounds on the divided difference `hquot h · σ` and its first derivative. -/
theorem hquot_deriv_bound {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ} (hδ : 0 ≤ δ)
    (h1 : ∀ t : ℝ, |deriv h t| ≤ δ) (h2 : ∀ t : ℝ, |iteratedDeriv 2 h t| ≤ δ) (a σ : ℝ) :
    |Work.OddVolterra.hquot h a σ| ≤ δ ∧
      |deriv (fun a : ℝ => Work.OddVolterra.hquot h a σ) a| ≤ δ := by
  have hdc : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := contDiff_deriv_of_contDiff hh
  constructor
  · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun τ : ℝ => deriv h (a + τ * (σ - a))) (C := δ) (by
        intro τ _
        simpa [Real.norm_eq_abs] using h1 (a + τ * (σ - a)))
    simpa [Work.OddVolterra.hquot, Real.norm_eq_abs] using this
  · have hMVT : ∀ x y : ℝ, |deriv h x - deriv h y| ≤ δ * |x - y| := by
      intro x y
      have hd : ∀ z ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (deriv h) z := fun z _ =>
        (hdc.differentiable (by simp)).differentiableAt
      have hb : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv (deriv h) z‖ ≤ δ := fun z _ => by
        have he : deriv (deriv h) z = iteratedDeriv 2 h z := by
          rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
        rw [he, Real.norm_eq_abs]; exact h2 z
      have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := (Set.univ : Set ℝ)) hd hb
        convex_univ (Set.mem_univ y) (Set.mem_univ x)
      simpa [Real.norm_eq_abs] using h
    have hint : ∀ b : ℝ, IntervalIntegrable (fun τ : ℝ => deriv h (b + τ * (σ - b)))
        volume (0 : ℝ) 1 := fun b => (by fun_prop : Continuous
          (fun τ : ℝ => deriv h (b + τ * (σ - b)))).intervalIntegrable _ _
    have hLip : ∀ b : ℝ, |Work.OddVolterra.hquot h a σ - Work.OddVolterra.hquot h b σ|
        ≤ δ * |a - b| := by
      intro b
      rw [Work.OddVolterra.hquot, Work.OddVolterra.hquot,
        ← intervalIntegral.integral_sub (hint a) (hint b)]
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (f := fun τ : ℝ => deriv h (a + τ * (σ - a)) - deriv h (b + τ * (σ - b)))
        (C := δ * |a - b|) ?_) (le_of_eq (by ring))
      intro τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
      have hxy : (a + τ * (σ - a)) - (b + τ * (σ - b)) = (a - b) * (1 - τ) := by ring
      have hτle : |(1 : ℝ) - τ| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
      rw [Real.norm_eq_abs]
      calc |deriv h (a + τ * (σ - a)) - deriv h (b + τ * (σ - b))|
          ≤ δ * |(a + τ * (σ - a)) - (b + τ * (σ - b))| := hMVT _ _
        _ = δ * (|a - b| * |(1 : ℝ) - τ|) := by rw [hxy, abs_mul]
        _ ≤ δ * (|a - b| * 1) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτle (abs_nonneg _)) hδ
        _ = δ * |a - b| := by ring
    have hdiffq : DifferentiableAt ℝ (fun a : ℝ => Work.OddVolterra.hquot h a σ) a :=
      (((Work.OddVolterra.Existence.hquot_contDiff hh).comp
        (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableAt
    have hslope : ∀ᶠ b in 𝓝[≠] a,
        |slope (fun a : ℝ => Work.OddVolterra.hquot h a σ) a b| ≤ δ := by
      filter_upwards [self_mem_nhdsWithin] with b hb
      have hb2 : |Work.OddVolterra.hquot h b σ - Work.OddVolterra.hquot h a σ|
          ≤ δ * |b - a| := by
        have hle := hLip b
        rwa [abs_sub_comm (Work.OddVolterra.hquot h a σ) (Work.OddVolterra.hquot h b σ),
          abs_sub_comm a b] at hle
      rw [slope_def_field, abs_div, div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hb))]
      exact hb2
    have := le_of_tendsto (hdiffq.hasDerivAt.tendsto_slope.abs) hslope
    simpa only [Real.norm_eq_abs] using this

/-- The jet-bounds constants `MZ` for the radicand. -/
noncomputable def jetMZ (i : ℕ) : ℝ := 9 * 2 ^ i + 9

/-- The jet-bounds constants `KZ` for the radicand. -/
noncomputable def jetKZ (i : ℕ) : ℝ := 5 * 2 ^ i + 5

lemma jetMZ_nonneg : ∀ i, 0 ≤ jetMZ i := by
  intro i; rw [jetMZ]; positivity

lemma jetKZ_nonneg : ∀ i, 0 ≤ jetKZ i := by
  intro i; rw [jetKZ]; positivity
/-! ## The jet recursion bound for `Rnu` -/

/-- Elementary telescoping estimate: if `x₁` is `≤ Bx`, the pair `(x₁,x₂)` differs by `≤ Kx δ`,
`y₂` is `≤ By` and `(y₁,y₂)` differs by `≤ By δ`, then `|x₁y₁ - x₂y₂| ≤ (Bx By + Kx By) δ`. -/
lemma abs_mul_sub_mul_le {x1 x2 y1 y2 Bx Kx By δ : ℝ} (hδ : 0 ≤ δ) (hBx : 0 ≤ Bx) (hKx : 0 ≤ Kx)
    (hx : |x1| ≤ Bx) (hxd : |x1 - x2| ≤ Kx * δ) (hy : |y2| ≤ By) (hyd : |y1 - y2| ≤ By * δ) :
    |x1 * y1 - x2 * y2| ≤ (Bx * By + Kx * By) * δ := by
  have hkey : x1 * y1 - x2 * y2 = x1 * (y1 - y2) + (x1 - x2) * y2 := by ring
  rw [hkey]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_mul]
  have h1 : |x1| * |y1 - y2| ≤ Bx * (By * δ) := mul_le_mul hx hyd (abs_nonneg _) hBx
  have h2 : |x1 - x2| * |y2| ≤ (Kx * δ) * By :=
    mul_le_mul hxd hy (abs_nonneg _) (mul_nonneg hKx hδ)
  calc |x1| * |y1 - y2| + |x1 - x2| * |y2| ≤ Bx * (By * δ) + (Kx * δ) * By := add_le_add h1 h2
    _ = (Bx * By + Kx * By) * δ := by ring

/-- The recursion constants of `rnu_jet_bound`. -/
noncomputable def jetC (ν : ℝ) (MZ KZ KI MI : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, j => max (KI j) (MI j)
  | (m + 1), j =>
      (∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (MZ i + 3 * KZ i) * jetC ν MZ KZ KI MI m (j - i + 1))
      + |ν - (m : ℝ)| * (∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (MZ (i + 1) + 3 * KZ (i + 1)) * jetC ν MZ KZ KI MI m (j - i))

lemma jetC_nonneg (ν : ℝ) (MZ KZ KI MI : ℕ → ℝ) (hMZ : ∀ i, 0 ≤ MZ i)
    (hKZ : ∀ i, 0 ≤ KZ i) (hKI : ∀ i, 0 ≤ KI i) (hMI : ∀ i, 0 ≤ MI i) :
    ∀ m j, 0 ≤ jetC ν MZ KZ KI MI m j := by
  intro m
  induction m with
  | zero => intro j; rw [jetC]; exact le_max_of_le_left (hKI j)
  | succ m ih =>
    intro j
    rw [jetC]
    refine add_nonneg ?_ (mul_nonneg (abs_nonneg _) ?_)
    · refine Finset.sum_nonneg fun i _ => ?_
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (hMZ i) (mul_nonneg (by norm_num) (hKZ i)))) (ih _)
    · refine Finset.sum_nonneg fun i _ => ?_
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (hMZ (i + 1)) (mul_nonneg (by norm_num) (hKZ (i + 1))))) (ih _)

/-- **The jet recursion bound.**  Abstract form: given uniform bounds on the jets of `Zrad h`
and of the two `init` functions on the box `[c,d]`, the recursion `R_{m+1} = Z ∂R_m + (ν-m) ∂Z R_m`
transfers these to all the derived quantities, with the explicit constants `jetC`. -/
theorem rnu_jet_bound (ν : ℝ) (N : ℕ) (c d : ℝ) (KZ MZ KI MI : ℕ → ℝ)
    (hKZ : ∀ i, 0 ≤ KZ i) (hMZ : ∀ i, 0 ≤ MZ i) (hKI : ∀ j, 0 ≤ KI j) (hMI : ∀ j, 0 ≤ MI j) :
    ∀ (h : ℝ → ℝ) (init_h init_0 : ℝ × ℝ × ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) h →
      ContDiff ℝ (⊤ : ℕ∞) init_h → ContDiff ℝ (⊤ : ℕ∞) init_0 →
      ∀ (σ t : ℝ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 →
      (∀ i, i ≤ N + 1 → ∀ a ∈ Set.Icc c d,
        |iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a| ≤ MZ i + 2 * KZ i) →
      (∀ i, i ≤ N + 1 → ∀ a ∈ Set.Icc c d,
        |iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a -
          iteratedDeriv i (fun a : ℝ => Zrad 0 (a, σ, t)) a| ≤ KZ i * δ) →
      (∀ i, i ≤ N + 1 → ∀ a ∈ Set.Icc c d,
        |iteratedDeriv i (fun a : ℝ => Zrad 0 (a, σ, t)) a| ≤ MZ i) →
      (∀ j, j ≤ N + 1 → ∀ a ∈ Set.Icc c d,
        |iteratedDeriv j (fun a : ℝ => init_h (a, σ, t)) a -
          iteratedDeriv j (fun a : ℝ => init_0 (a, σ, t)) a| ≤ KI j * δ) →
      (∀ j, j ≤ N + 1 → ∀ a ∈ Set.Icc c d,
        |iteratedDeriv j (fun a : ℝ => init_0 (a, σ, t)) a| ≤ MI j) →
      ∀ m j, m + j ≤ N + 1 → ∀ a ∈ Set.Icc c d,
        |iteratedDeriv j (fun a : ℝ => Rnu ν h init_h m (a, σ, t)) a -
          iteratedDeriv j (fun a : ℝ => Rnu ν 0 init_0 m (a, σ, t)) a|
            ≤ jetC ν MZ KZ KI MI m j * δ ∧
        |iteratedDeriv j (fun a : ℝ => Rnu ν 0 init_0 m (a, σ, t)) a|
            ≤ jetC ν MZ KZ KI MI m j := by
  intro h init_h init_0 hh hih hi0 σ t δ hδ hδ1 hZh hZd hZ0 hIhd hI0
  have hzero : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ → ℝ) := contDiff_const
  have key : ∀ m : ℕ, ∀ j : ℕ, m + j ≤ N + 1 → ∀ a ∈ Set.Icc c d,
      |iteratedDeriv j (fun a : ℝ => Rnu ν h init_h m (a, σ, t)) a -
        iteratedDeriv j (fun a : ℝ => Rnu ν 0 init_0 m (a, σ, t)) a|
          ≤ jetC ν MZ KZ KI MI m j * δ ∧
      |iteratedDeriv j (fun a : ℝ => Rnu ν 0 init_0 m (a, σ, t)) a|
          ≤ jetC ν MZ KZ KI MI m j := by
    intro m
    induction m with
    | zero =>
      intro j hj a ha
      have hj' : j ≤ N + 1 := by omega
      have h1 := hIhd j hj' a ha
      have h2 := hI0 j hj' a ha
      have hc : jetC ν MZ KZ KI MI 0 j = max (KI j) (MI j) := by rw [jetC]
      rw [Rnu, hc]
      exact ⟨le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ),
        le_trans h2 (le_max_right _ _)⟩
    | succ m ih =>
      intro j hj a ha
      have hjN : j ≤ N := by omega
      have hj' : (m + 1) + j ≤ N + 1 := hj
      have hmj : m + j ≤ N := by omega
      -- the two Leibniz expansions
      rw [iteratedDeriv_Rnu_succ ν hh hih m j σ t a,
        iteratedDeriv_Rnu_succ ν hzero hi0 m j σ t a]
      -- abbreviations
      set S1h : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a *
           iteratedDeriv (j - i + 1) (fun a : ℝ => Rnu ν h init_h m (a, σ, t)) a) with hS1h
      set S1z : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (iteratedDeriv i (fun a : ℝ => Zrad 0 (a, σ, t)) a *
           iteratedDeriv (j - i + 1) (fun a : ℝ => Rnu ν 0 init_0 m (a, σ, t)) a) with hS1z
      set S2h : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (iteratedDeriv (i + 1) (fun a : ℝ => Zrad h (a, σ, t)) a *
           iteratedDeriv (j - i) (fun a : ℝ => Rnu ν h init_h m (a, σ, t)) a) with hS2h
      set S2z : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (iteratedDeriv (i + 1) (fun a : ℝ => Zrad 0 (a, σ, t)) a *
           iteratedDeriv (j - i) (fun a : ℝ => Rnu ν 0 init_0 m (a, σ, t)) a) with hS2z
      -- index bookkeeping
      have hi_le : ∀ i, i ∈ Finset.range (j + 1) → i ≤ N + 1 := by
        intro i hi; rw [Finset.mem_range] at hi; omega
      have hi1_le : ∀ i, i ∈ Finset.range (j + 1) → i + 1 ≤ N + 1 := by
        intro i hi; rw [Finset.mem_range] at hi; omega
      have hmj1 : ∀ i, i ∈ Finset.range (j + 1) → m + (j - i + 1) ≤ N + 1 := by
        intro i hi; rw [Finset.mem_range] at hi; omega
      have hmj0 : ∀ i, i ∈ Finset.range (j + 1) → m + (j - i) ≤ N + 1 := by
        intro i hi; rw [Finset.mem_range] at hi; omega
      have hP1 : ∀ i, i ∈ Finset.range (j + 1) → 0 ≤ jetC ν MZ KZ KI MI m (j - i + 1) :=
        fun i _ => jetC_nonneg ν MZ KZ KI MI hMZ hKZ hKI hMI m (j - i + 1)
      have hP2 : ∀ i, i ∈ Finset.range (j + 1) → 0 ≤ jetC ν MZ KZ KI MI m (j - i) :=
        fun i _ => jetC_nonneg ν MZ KZ KI MI hMZ hKZ hKI hMI m (j - i)
      -- the difference of the first sums
      have hS1diff : |S1h - S1z| ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * (MZ i + 3 * KZ i) * jetC ν MZ KZ KI MI m (j - i + 1) * δ := by
        rw [hS1h, hS1z, ← Finset.sum_sub_distrib]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum fun i hi => ?_
        have hiN := hi_le i hi
        have hmj := hmj1 i hi
        have hc : (0:ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
        have hkey : (j.choose i : ℝ) *
              (iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a *
               iteratedDeriv (j - i + 1) (fun a : ℝ => Rnu ν h init_h m (a, σ, t)) a) -
            (j.choose i : ℝ) *
              (iteratedDeriv i (fun a : ℝ => Zrad 0 (a, σ, t)) a *
               iteratedDeriv (j - i + 1) (fun a : ℝ => Rnu ν 0 init_0 m (a, σ, t)) a)
            = (j.choose i : ℝ) *
              ((iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a *
                iteratedDeriv (j - i + 1) (fun a : ℝ => Rnu ν h init_h m (a, σ, t)) a) -
               (iteratedDeriv i (fun a : ℝ => Zrad 0 (a, σ, t)) a *
                iteratedDeriv (j - i + 1) (fun a : ℝ => Rnu ν 0 init_0 m (a, σ, t)) a)) := by
          ring
        rw [hkey, abs_mul, abs_of_nonneg hc]
        have hle := abs_mul_sub_mul_le (δ := δ) (Bx := MZ i + 2 * KZ i) (Kx := KZ i)
            (By := jetC ν MZ KZ KI MI m (j - i + 1)) hδ
            (by linarith [hMZ i, hKZ i]) (hKZ i)
            (hZh i hiN a ha) (hZd i hiN a ha)
            ((ih (j - i + 1) hmj a ha).2) ((ih (j - i + 1) hmj a ha).1)
        refine le_trans (mul_le_mul_of_nonneg_left hle hc) (le_of_eq (by ring))
      -- the difference of the second sums
      have hS2diff : |S2h - S2z| ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * (MZ (i + 1) + 3 * KZ (i + 1)) *
            jetC ν MZ KZ KI MI m (j - i) * δ := by
        rw [hS2h, hS2z, ← Finset.sum_sub_distrib]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum fun i hi => ?_
        have hiN := hi1_le i hi
        have hmj := hmj0 i hi
        have hc : (0:ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
        have hkey : (j.choose i : ℝ) *
              (iteratedDeriv (i + 1) (fun a : ℝ => Zrad h (a, σ, t)) a *
               iteratedDeriv (j - i) (fun a : ℝ => Rnu ν h init_h m (a, σ, t)) a) -
            (j.choose i : ℝ) *
              (iteratedDeriv (i + 1) (fun a : ℝ => Zrad 0 (a, σ, t)) a *
               iteratedDeriv (j - i) (fun a : ℝ => Rnu ν 0 init_0 m (a, σ, t)) a)
            = (j.choose i : ℝ) *
              ((iteratedDeriv (i + 1) (fun a : ℝ => Zrad h (a, σ, t)) a *
                iteratedDeriv (j - i) (fun a : ℝ => Rnu ν h init_h m (a, σ, t)) a) -
               (iteratedDeriv (i + 1) (fun a : ℝ => Zrad 0 (a, σ, t)) a *
                iteratedDeriv (j - i) (fun a : ℝ => Rnu ν 0 init_0 m (a, σ, t)) a)) := by
          ring
        rw [hkey, abs_mul, abs_of_nonneg hc]
        have hle := abs_mul_sub_mul_le (δ := δ) (Bx := MZ (i + 1) + 2 * KZ (i + 1))
            (Kx := KZ (i + 1)) (By := jetC ν MZ KZ KI MI m (j - i)) hδ
            (by linarith [hMZ (i + 1), hKZ (i + 1)]) (hKZ (i + 1))
            (hZh (i + 1) hiN a ha) (hZd (i + 1) hiN a ha)
            ((ih (j - i) hmj a ha).2) ((ih (j - i) hmj a ha).1)
        refine le_trans (mul_le_mul_of_nonneg_left hle hc) (le_of_eq (by ring))
      -- the sizes of the unperturbed sums
      have hS1zsize : |S1z| ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * MZ i * jetC ν MZ KZ KI MI m (j - i + 1) := by
        rw [hS1z]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum fun i hi => ?_
        have hiN := hi_le i hi
        have hmj := hmj1 i hi
        have hc : (0:ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
        rw [abs_mul, abs_of_nonneg hc]
        have hxy : |iteratedDeriv i (fun a : ℝ => Zrad 0 (a, σ, t)) a *
              iteratedDeriv (j - i + 1) (fun a : ℝ => Rnu ν 0 init_0 m (a, σ, t)) a|
            ≤ MZ i * jetC ν MZ KZ KI MI m (j - i + 1) := by
          rw [abs_mul]
          exact mul_le_mul (hZ0 i hiN a ha) ((ih (j - i + 1) hmj a ha).2)
            (abs_nonneg _) (hMZ i)
        refine le_trans (mul_le_mul_of_nonneg_left hxy hc) (le_of_eq (by ring))
      have hS2zsize : |S2z| ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * MZ (i + 1) * jetC ν MZ KZ KI MI m (j - i) := by
        rw [hS2z]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum fun i hi => ?_
        have hiN := hi1_le i hi
        have hmj := hmj0 i hi
        have hc : (0:ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
        rw [abs_mul, abs_of_nonneg hc]
        have hxy : |iteratedDeriv (i + 1) (fun a : ℝ => Zrad 0 (a, σ, t)) a *
              iteratedDeriv (j - i) (fun a : ℝ => Rnu ν 0 init_0 m (a, σ, t)) a|
            ≤ MZ (i + 1) * jetC ν MZ KZ KI MI m (j - i) := by
          rw [abs_mul]
          exact mul_le_mul (hZ0 (i + 1) hiN a ha) ((ih (j - i) hmj a ha).2)
            (abs_nonneg _) (hMZ (i + 1))
        refine le_trans (mul_le_mul_of_nonneg_left hxy hc) (le_of_eq (by ring))
      -- the value of the recursion constant
      have hCval : jetC ν MZ KZ KI MI (m + 1) j =
          (∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * (MZ i + 3 * KZ i) * jetC ν MZ KZ KI MI m (j - i + 1))
          + |ν - (m : ℝ)| * (∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * (MZ (i + 1) + 3 * KZ (i + 1)) *
              jetC ν MZ KZ KI MI m (j - i)) := by
        rw [jetC]
      rw [hCval]
      constructor
      · have hsub : S1h + (ν - (m : ℝ)) * S2h - (S1z + (ν - (m : ℝ)) * S2z)
            = (S1h - S1z) + (ν - (m : ℝ)) * (S2h - S2z) := by ring
        rw [hsub]
        refine le_trans (abs_add_le _ _) ?_
        have hb : |(ν - (m : ℝ)) * (S2h - S2z)| ≤ |ν - (m : ℝ)| *
            (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (MZ (i + 1) + 3 * KZ (i + 1)) *
              jetC ν MZ KZ KI MI m (j - i) * δ) := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hS2diff (abs_nonneg _)
        refine le_trans (add_le_add hS1diff hb) ?_
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        exact le_of_eq (by ring)
      · refine le_trans (abs_add_le _ _) ?_
        have hsummand1 : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * MZ i *
            jetC ν MZ KZ KI MI m (j - i + 1))
          ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (MZ i + 3 * KZ i) *
            jetC ν MZ KZ KI MI m (j - i + 1) := by
          refine Finset.sum_le_sum fun i hi => ?_
          refine mul_le_mul_of_nonneg_right ?_ (hP1 i hi)
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          linarith [hMZ i, hKZ i]
        have hsummand2 : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * MZ (i + 1) *
            jetC ν MZ KZ KI MI m (j - i))
          ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (MZ (i + 1) + 3 * KZ (i + 1)) *
            jetC ν MZ KZ KI MI m (j - i) := by
          refine Finset.sum_le_sum fun i hi => ?_
          refine mul_le_mul_of_nonneg_right ?_ (hP2 i hi)
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          linarith [hMZ (i + 1), hKZ (i + 1)]
        have hb : |(ν - (m : ℝ)) * S2z| ≤ |ν - (m : ℝ)| *
            (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (MZ (i + 1) + 3 * KZ (i + 1)) *
              jetC ν MZ KZ KI MI m (j - i)) := by
          rw [abs_mul]
          exact le_trans (mul_le_mul_of_nonneg_left hS2zsize (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hsummand2 (abs_nonneg _))
        exact le_trans (add_le_add hS1zsize hb) (add_le_add hsummand1 le_rfl)
  exact key



/-! ## Jet bounds for the line `a ↦ a t + h a` and for the radicand `Zrad` -/

/-- `line h σ t - line 0 σ t = h σ`. -/
lemma line_sub_line_zero (h : ℝ → ℝ) (σ t : ℝ) :
    line h σ t - line (0 : ℝ → ℝ) σ t = h σ := by
  simp [line]

/-- The `k`-th derivative of `a ↦ line h a t = a t + h a` in closed form. -/
lemma iteratedDeriv_line_eq (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t a : ℝ) (k : ℕ) :
    iteratedDeriv k (fun a : ℝ => line h a t) a
      = (if k = 0 then a else if k = 1 then 1 else 0) * t + iteratedDeriv k h a := by
  have hsplit : (fun a : ℝ => line h a t) = (fun a : ℝ => a * t + h a) := by
    funext x; simp only [line]
  rw [hsplit, iteratedDeriv_fun_add (by fun_prop)
    (hh.contDiffAt.of_le (natCast_le_top_enat k))]
  rw [show (fun a : ℝ => a * t) = (fun a : ℝ => t * a) from by funext x; ring]
  rw [iteratedDeriv_const_mul (n := k) (f := fun a : ℝ => a) (x := a) t (by fun_prop)]
  rw [show (fun a : ℝ => a) = (id : ℝ → ℝ) from rfl, iteratedDeriv_id]
  ring

/-- The difference of the `k`-th derivatives of `a ↦ line h a t` and `a ↦ line 0 a t` is the
`k`-th derivative of `h`. -/
lemma iteratedDeriv_line_sub_eq (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t a : ℝ) (k : ℕ) :
    iteratedDeriv k (fun a : ℝ => line h a t) a -
      iteratedDeriv k (fun a : ℝ => line (0 : ℝ → ℝ) a t) a = iteratedDeriv k h a := by
  rw [iteratedDeriv_line_eq h hh t a k,
    iteratedDeriv_line_eq (0 : ℝ → ℝ) contDiff_const t a k]
  simp

/-- Uniform bound for the jets of the line `a ↦ line h a t` on the box. -/
lemma abs_iteratedDeriv_line_le {N : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ : δ ≤ 1 / 100) (hjet : ∀ k : ℕ, k ≤ N → ∀ a : ℝ, |iteratedDeriv k h a| ≤ δ)
    {t a : ℝ} (ha : a ∈ Set.Icc (49 / 100 : ℝ) 1) (ht : t ∈ Set.Icc (-2 : ℝ) 2)
    {k : ℕ} (hk : k ≤ N) :
    |iteratedDeriv k (fun a : ℝ => line h a t) a| ≤ 3 := by
  rw [iteratedDeriv_line_eq h hh t a k]
  have ha' : |a| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [ha.1], ha.2⟩
  have ht' : |t| ≤ 2 := by rw [abs_le]; exact ht
  have h1 : |(if k = 0 then a else if k = 1 then 1 else 0) * t| ≤ 2 := by
    rw [abs_mul]
    rcases eq_or_ne k 0 with h0 | h0
    · rw [if_pos h0]
      simpa using mul_le_mul ha' ht' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    · rcases eq_or_ne k 1 with h1' | h1'
      · rw [if_neg h0, if_pos h1']; simpa using ht'
      · rw [if_neg h0, if_neg h1']; simp
  calc |(if k = 0 then a else if k = 1 then 1 else 0) * t + iteratedDeriv k h a|
      ≤ |(if k = 0 then a else if k = 1 then 1 else 0) * t| + |iteratedDeriv k h a| :=
        abs_add_le _ _
    _ ≤ 2 + 1 / 100 := add_le_add h1 (le_trans (hjet k hk a) hδ)
    _ ≤ 3 := by norm_num

/-- Uniform bound for the jets of the line `a ↦ line 0 a t = a t`. -/
lemma abs_iteratedDeriv_line_zero_le {t a : ℝ} (ha : a ∈ Set.Icc (49 / 100 : ℝ) 1)
    (ht : t ∈ Set.Icc (-2 : ℝ) 2) (k : ℕ) :
    |iteratedDeriv k (fun a : ℝ => line (0 : ℝ → ℝ) a t) a| ≤ 2 := by
  rw [iteratedDeriv_line_eq (0 : ℝ → ℝ) contDiff_const t a k]
  have hz : iteratedDeriv k (0 : ℝ → ℝ) a = 0 := by
    change iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) a = 0
    rw [iteratedDeriv_const]; split_ifs <;> simp
  rw [hz, add_zero, abs_mul]
  have ha' : |a| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [ha.1], ha.2⟩
  have ht' : |t| ≤ 2 := by rw [abs_le]; exact ht
  rcases eq_or_ne k 0 with h0 | h0
  · rw [if_pos h0]
    simpa using mul_le_mul ha' ht' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  · rcases eq_or_ne k 1 with h1' | h1'
    · rw [if_neg h0, if_pos h1']; simpa using ht'
    · rw [if_neg h0, if_neg h1']; simp

/-- Smoothness of `a ↦ line h a t`. -/
lemma contDiff_line (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => line h a t) := by
  unfold line; fun_prop

/-- Uniform bound for the jets of the square `a ↦ line h a t ^ 2` on the box. -/
lemma abs_iteratedDeriv_line_sq_le {N : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ : δ ≤ 1 / 100) (hjet : ∀ k : ℕ, k ≤ N → ∀ a : ℝ, |iteratedDeriv k h a| ≤ δ)
    {t a : ℝ} (ha : a ∈ Set.Icc (49 / 100 : ℝ) 1) (ht : t ∈ Set.Icc (-2 : ℝ) 2)
    {i : ℕ} (hi : i ≤ N) :
    |iteratedDeriv i (fun a : ℝ => line h a t ^ 2) a| ≤ 9 * 2 ^ i := by
  have hline := contDiff_line h hh t
  have hFF : (fun a : ℝ => line h a t ^ 2) = fun a : ℝ => line h a t * line h a t := by
    funext x; ring
  rw [hFF, iteratedDeriv_fun_mul (hline.contDiffAt.of_le (natCast_le_top_enat i))
    (hline.contDiffAt.of_le (natCast_le_top_enat i))]
  have hterm : ∀ k ∈ Finset.range (i + 1),
      |(i.choose k : ℝ) * iteratedDeriv k (fun a : ℝ => line h a t) a *
          iteratedDeriv (i - k) (fun a : ℝ => line h a t) a| ≤ (i.choose k : ℝ) * 9 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h1 : |iteratedDeriv k (fun a : ℝ => line h a t) a| ≤ 3 :=
      abs_iteratedDeriv_line_le hh hδ hjet ha ht (by omega)
    have h2 : |iteratedDeriv (i - k) (fun a : ℝ => line h a t) a| ≤ 3 :=
      abs_iteratedDeriv_line_le hh hδ hjet ha ht (by omega)
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc (i.choose k : ℝ) * |iteratedDeriv k (fun a : ℝ => line h a t) a| *
          |iteratedDeriv (i - k) (fun a : ℝ => line h a t) a|
        ≤ (i.choose k : ℝ) * 3 * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
            (abs_nonneg _) (by positivity)
      _ = (i.choose k : ℝ) * 9 := by ring
  calc |∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
        iteratedDeriv k (fun a : ℝ => line h a t) a *
        iteratedDeriv (i - k) (fun a : ℝ => line h a t) a|
      ≤ ∑ k ∈ Finset.range (i + 1), |(i.choose k : ℝ) *
          iteratedDeriv k (fun a : ℝ => line h a t) a *
          iteratedDeriv (i - k) (fun a : ℝ => line h a t) a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * 9 := Finset.sum_le_sum hterm
    _ = 9 * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) := by
          rw [← Finset.sum_mul]; ring
    _ = 9 * 2 ^ i := by
          rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring

/-- Bounds for the jets of the sum `a ↦ line h a t + line 0 a t`. -/
lemma abs_iteratedDeriv_line_add_le {N : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ : δ ≤ 1 / 100) (hjet : ∀ k : ℕ, k ≤ N → ∀ a : ℝ, |iteratedDeriv k h a| ≤ δ)
    {t a : ℝ} (ha : a ∈ Set.Icc (49 / 100 : ℝ) 1) (ht : t ∈ Set.Icc (-2 : ℝ) 2)
    {j : ℕ} (hj : j ≤ N) :
    |iteratedDeriv j (fun a : ℝ => line h a t + line (0 : ℝ → ℝ) a t) a| ≤ 5 := by
  have hline := contDiff_line h hh t
  have hline0 := contDiff_line (0 : ℝ → ℝ) contDiff_const t
  rw [iteratedDeriv_fun_add (hline.contDiffAt.of_le (natCast_le_top_enat j))
    (hline0.contDiffAt.of_le (natCast_le_top_enat j))]
  calc |iteratedDeriv j (fun a : ℝ => line h a t) a +
        iteratedDeriv j (fun a : ℝ => line (0 : ℝ → ℝ) a t) a|
      ≤ |iteratedDeriv j (fun a : ℝ => line h a t) a| +
        |iteratedDeriv j (fun a : ℝ => line (0 : ℝ → ℝ) a t) a| := abs_add_le _ _
    _ ≤ 3 + 2 := add_le_add (abs_iteratedDeriv_line_le hh hδ hjet ha ht hj)
        (abs_iteratedDeriv_line_zero_le ha ht j)
    _ ≤ 5 := by norm_num

/-- Telescoping bound for the difference of the jets of the square `a ↦ line h a t ^ 2` for `h`
and for the zero function. -/
lemma abs_iteratedDeriv_line_sq_diff_le {N : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ N → ∀ a : ℝ, |iteratedDeriv k h a| ≤ δ)
    {t a : ℝ} (ha : a ∈ Set.Icc (49 / 100 : ℝ) 1) (ht : t ∈ Set.Icc (-2 : ℝ) 2)
    {i : ℕ} (hi : i ≤ N) :
    |iteratedDeriv i (fun a : ℝ => line h a t ^ 2) a -
      iteratedDeriv i (fun a : ℝ => line (0 : ℝ → ℝ) a t ^ 2) a| ≤ 5 * 2 ^ i * δ := by
  have hline := contDiff_line h hh t
  have hline0 := contDiff_line (0 : ℝ → ℝ) contDiff_const t
  have hs : (fun a : ℝ => line h a t ^ 2) - (fun a : ℝ => line (0 : ℝ → ℝ) a t ^ 2) =
      fun a : ℝ => h a * (line h a t + line (0 : ℝ → ℝ) a t) := by
    funext x; simp only [Pi.sub_apply, Pi.zero_apply, line]; ring
  have hsumc : ContDiff ℝ (⊤ : ℕ∞)
      (fun a : ℝ => line h a t + line (0 : ℝ → ℝ) a t) := hline.add hline0
  rw [← iteratedDeriv_sub ((hline.pow 2).contDiffAt.of_le (natCast_le_top_enat i))
      ((hline0.pow 2).contDiffAt.of_le (natCast_le_top_enat i)), hs]
  rw [iteratedDeriv_fun_mul (hh.contDiffAt.of_le (natCast_le_top_enat i))
    (hsumc.contDiffAt.of_le (natCast_le_top_enat i))]
  have hterm : ∀ k ∈ Finset.range (i + 1),
      |(i.choose k : ℝ) * iteratedDeriv k h a *
          iteratedDeriv (i - k) (fun a : ℝ => line h a t + line (0 : ℝ → ℝ) a t) a|
        ≤ (i.choose k : ℝ) * (5 * δ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hc : (0:ℝ) ≤ (i.choose k : ℝ) := Nat.cast_nonneg _
    have h1 : |iteratedDeriv k h a| ≤ δ := hjet k (by omega) a
    have h2 : |iteratedDeriv (i - k)
        (fun a : ℝ => line h a t + line (0 : ℝ → ℝ) a t) a| ≤ 5 :=
      abs_iteratedDeriv_line_add_le hh hδ1 hjet ha ht (by omega)
    rw [abs_mul, abs_mul, abs_of_nonneg hc]
    calc (i.choose k : ℝ) * |iteratedDeriv k h a| *
          |iteratedDeriv (i - k) (fun a : ℝ => line h a t + line (0 : ℝ → ℝ) a t) a|
        ≤ (i.choose k : ℝ) * δ * 5 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (abs_nonneg _) (mul_nonneg hc hδ)
      _ = (i.choose k : ℝ) * (5 * δ) := by ring
  calc |∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * iteratedDeriv k h a *
        iteratedDeriv (i - k) (fun a : ℝ => line h a t + line (0 : ℝ → ℝ) a t) a|
      ≤ ∑ k ∈ Finset.range (i + 1), |(i.choose k : ℝ) * iteratedDeriv k h a *
          iteratedDeriv (i - k) (fun a : ℝ => line h a t + line (0 : ℝ → ℝ) a t) a| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * (5 * δ) := Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ)) * (5 * δ) := by rw [Finset.sum_mul]
    _ = 2 ^ i * (5 * δ) := by
          rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
    _ = 5 * 2 ^ i * δ := by ring

/-- The elementary bound `|a σ t + h σ| ≤ 3` for `σ ∈ [1/2, 19/20]`, `|t| ≤ 2`. -/
lemma abs_line_le_three {N : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ : δ ≤ 1 / 100) (hjet : ∀ k : ℕ, k ≤ N → ∀ a : ℝ, |iteratedDeriv k h a| ≤ δ)
    {σ t : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (19 / 20)) (ht : t ∈ Set.Icc (-2 : ℝ) 2) :
    |line h σ t| ≤ 3 := by
  have h0 : |line (0 : ℝ → ℝ) σ t| ≤ 2 := by
    have hlin : line (0 : ℝ → ℝ) σ t = σ * t := by simp [line]
    rw [hlin, abs_mul]
    simpa using mul_le_mul
      (show |σ| ≤ (1 : ℝ) by rw [abs_le]; exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)
      (show |t| ≤ (2 : ℝ) by rw [abs_le]; exact ht) (abs_nonneg _)
      (by norm_num : (0:ℝ) ≤ 1)
  have h1 : |line h σ t - line (0 : ℝ → ℝ) σ t| ≤ δ := by
    rw [line_sub_line_zero]
    exact hjet 0 (Nat.zero_le N) σ
  calc |line h σ t| = |(line h σ t - line (0 : ℝ → ℝ) σ t) + line (0 : ℝ → ℝ) σ t| := by
        rw [sub_add_cancel]
    _ ≤ |line h σ t - line (0 : ℝ → ℝ) σ t| + |line (0 : ℝ → ℝ) σ t| := abs_add_le _ _
    _ ≤ 1 / 100 + 2 := add_le_add (le_trans h1 hδ) h0
    _ ≤ 3 := by norm_num

/-- **Size bound for the jets of the radicand.** -/
lemma abs_iteratedDeriv_Zrad_le {N : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ : δ ≤ 1 / 100) (hjet : ∀ k : ℕ, k ≤ N → ∀ a : ℝ, |iteratedDeriv k h a| ≤ δ)
    {σ t a : ℝ} (ha : a ∈ Set.Icc (49 / 100 : ℝ) 1) (ht : t ∈ Set.Icc (-2 : ℝ) 2)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (19 / 20)) {i : ℕ} (hi : i ≤ N) :
    |iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a| ≤ 9 * 2 ^ i + 9 := by
  have hcq : |line h σ t| ≤ 3 := abs_line_le_three hh hδ hjet hσ ht
  have hline := contDiff_line h hh t
  have hsplit : (fun a : ℝ => Zrad h (a, σ, t)) =
      (fun _ : ℝ => line h σ t ^ 2) - (fun a : ℝ => line h a t ^ 2) := by
    funext x; simp only [Zrad, Pi.sub_apply]
  rw [hsplit, iteratedDeriv_sub (contDiff_const.contDiffAt.of_le (natCast_le_top_enat i))
    ((hline.pow 2).contDiffAt.of_le (natCast_le_top_enat i)), iteratedDeriv_const]
  rcases eq_or_ne i 0 with h0 | h0
  · subst h0
    simp only [if_pos rfl]
    have hsq : |line h a t ^ 2| ≤ 9 := by
      rw [abs_pow]
      calc |line h a t| ^ 2 ≤ 3 ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _)
              (abs_iteratedDeriv_line_le hh hδ hjet ha ht (k := 0) (Nat.zero_le N)) 2
        _ = 9 := by norm_num
    have hsqσ : |line h σ t ^ 2| ≤ 9 := by
      rw [abs_pow]
      calc |line h σ t| ^ 2 ≤ 3 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hcq 2
        _ = 9 := by norm_num
    calc |line h σ t ^ 2 - line h a t ^ 2| ≤ |line h σ t ^ 2| + |line h a t ^ 2| := abs_sub _ _
      _ ≤ 9 + 9 := add_le_add hsqσ hsq
      _ = 9 * 2 ^ 0 + 9 := by norm_num
  · rw [if_neg h0, zero_sub, abs_neg]
    calc |iteratedDeriv i (fun a : ℝ => line h a t ^ 2) a| ≤ 9 * 2 ^ i :=
          abs_iteratedDeriv_line_sq_le hh hδ hjet ha ht hi
      _ ≤ 9 * 2 ^ i + 9 := le_add_of_nonneg_right (by norm_num)

/-- **Telescoping bound for the jets of the radicand, `h` versus `0`.** -/
lemma abs_iteratedDeriv_Zrad_diff_le {N : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ N → ∀ a : ℝ, |iteratedDeriv k h a| ≤ δ)
    {σ t a : ℝ} (ha : a ∈ Set.Icc (49 / 100 : ℝ) 1) (ht : t ∈ Set.Icc (-2 : ℝ) 2)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (19 / 20)) {i : ℕ} (hi : i ≤ N) :
    |iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a -
      iteratedDeriv i (fun a : ℝ => Zrad 0 (a, σ, t)) a| ≤ (5 * 2 ^ i + 5) * δ := by
  have hline := contDiff_line h hh t
  have hline0 := contDiff_line (0 : ℝ → ℝ) contDiff_const t
  have hstep : iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a -
      iteratedDeriv i (fun a : ℝ => Zrad 0 (a, σ, t)) a =
      (iteratedDeriv i (fun _ : ℝ => line h σ t ^ 2) a -
        iteratedDeriv i (fun _ : ℝ => line (0 : ℝ → ℝ) σ t ^ 2) a) -
      (iteratedDeriv i (fun a : ℝ => line h a t ^ 2) a -
        iteratedDeriv i (fun a : ℝ => line (0 : ℝ → ℝ) a t ^ 2) a) := by
    have hs : (fun a : ℝ => Zrad h (a, σ, t)) =
        (fun _ : ℝ => line h σ t ^ 2) - (fun a : ℝ => line h a t ^ 2) := by
      funext x; simp only [Zrad, Pi.sub_apply]
    have hs0 : (fun a : ℝ => Zrad 0 (a, σ, t)) =
        (fun _ : ℝ => line (0 : ℝ → ℝ) σ t ^ 2) - (fun a : ℝ => line (0 : ℝ → ℝ) a t ^ 2) := by
      funext x; simp only [Zrad, Pi.sub_apply]
    rw [hs, hs0,
      iteratedDeriv_sub (contDiff_const.contDiffAt.of_le (natCast_le_top_enat i))
        ((hline.pow 2).contDiffAt.of_le (natCast_le_top_enat i)),
      iteratedDeriv_sub (contDiff_const.contDiffAt.of_le (natCast_le_top_enat i))
        ((hline0.pow 2).contDiffAt.of_le (natCast_le_top_enat i))]
    ring
  rw [hstep]
  have hcd : |iteratedDeriv i (fun _ : ℝ => line h σ t ^ 2) a -
      iteratedDeriv i (fun _ : ℝ => line (0 : ℝ → ℝ) σ t ^ 2) a| ≤ 5 * δ := by
    rw [iteratedDeriv_const, iteratedDeriv_const]
    rcases eq_or_ne i 0 with h0 | h0
    · rw [if_pos h0, if_pos h0]
      have hb : |line h σ t - line (0 : ℝ → ℝ) σ t| ≤ δ := by
        rw [line_sub_line_zero]
        exact hjet 0 (Nat.zero_le N) σ
      have hs5 : |line h σ t + line (0 : ℝ → ℝ) σ t| ≤ 5 := by
        calc |line h σ t + line (0 : ℝ → ℝ) σ t|
            ≤ |line h σ t| + |line (0 : ℝ → ℝ) σ t| := abs_add_le _ _
          _ ≤ 3 + 2 := add_le_add (abs_line_le_three hh hδ1 hjet hσ ht) (by
                have hlin : line (0 : ℝ → ℝ) σ t = σ * t := by simp [line]
                rw [hlin, abs_mul]
                simpa using mul_le_mul
                  (show |σ| ≤ (1 : ℝ) by
                    rw [abs_le]; exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)
                  (show |t| ≤ (2 : ℝ) by rw [abs_le]; exact ht)
                  (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1))
          _ ≤ 5 := by norm_num
      have hfac : line h σ t ^ 2 - line (0 : ℝ → ℝ) σ t ^ 2 =
          (line h σ t - line (0 : ℝ → ℝ) σ t) * (line h σ t + line (0 : ℝ → ℝ) σ t) := by
        ring
      rw [hfac, abs_mul]
      calc |line h σ t - line (0 : ℝ → ℝ) σ t| * |line h σ t + line (0 : ℝ → ℝ) σ t|
          ≤ δ * 5 := mul_le_mul hb hs5 (abs_nonneg _) hδ
        _ = 5 * δ := by ring
    · rw [if_neg h0, if_neg h0, sub_self, abs_zero]
      exact mul_nonneg (by norm_num) hδ
  have hsqd : |iteratedDeriv i (fun a : ℝ => line h a t ^ 2) a -
      iteratedDeriv i (fun a : ℝ => line (0 : ℝ → ℝ) a t ^ 2) a| ≤ 5 * 2 ^ i * δ :=
    abs_iteratedDeriv_line_sq_diff_le hh hδ hδ1 hjet ha ht hi
  calc |(iteratedDeriv i (fun _ : ℝ => line h σ t ^ 2) a -
        iteratedDeriv i (fun _ : ℝ => line (0 : ℝ → ℝ) σ t ^ 2) a) -
      (iteratedDeriv i (fun a : ℝ => line h a t ^ 2) a -
        iteratedDeriv i (fun a : ℝ => line (0 : ℝ → ℝ) a t ^ 2) a)|
      ≤ |iteratedDeriv i (fun _ : ℝ => line h σ t ^ 2) a -
          iteratedDeriv i (fun _ : ℝ => line (0 : ℝ → ℝ) σ t ^ 2) a| +
        |iteratedDeriv i (fun a : ℝ => line h a t ^ 2) a -
          iteratedDeriv i (fun a : ℝ => line (0 : ℝ → ℝ) a t ^ 2) a| := abs_sub _ _
    _ ≤ 5 * δ + 5 * 2 ^ i * δ := add_le_add hcd hsqd
    _ = (5 * 2 ^ i + 5) * δ := by ring

/-! ## Jet bounds for the two manifest Abel numerators -/

set_option maxHeartbeats 1000000 in
/-- **Jet bounds for `J1M`.**  On the box, `J1M n h` differs from `J1M n 0` by `O(δ)`, together
with its `a`-derivative, and the unperturbed quantities are uniformly bounded. -/
theorem aw_J1M_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 / 100 →
      ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ a ∈ Set.Icc (49 / 100 : ℝ) 1, ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (19 / 20),
        ∀ t ∈ Set.Icc (-2 : ℝ) 2,
        (|J1M n h a σ t - J1M n 0 a σ t| ≤ C * δ ∧
         |deriv (fun a : ℝ => J1M n h a σ t) a - deriv (fun a : ℝ => J1M n 0 a σ t) a|
            ≤ C * δ) ∧
        (|J1M n 0 a σ t| ≤ C ∧ |deriv (fun a : ℝ => J1M n 0 a σ t) a| ≤ C) := by
  set C : ℝ := max (jetC ((n : ℝ) + 1 / 2) jetMZ jetKZ (fun _ => 0) (fun _ => 1) (n + 1) 0)
      (jetC ((n : ℝ) + 1 / 2) jetMZ jetKZ (fun _ => 0) (fun _ => 1) (n + 1) 1) with hCdef
  refine ⟨C, ?_, ?_⟩
  · rw [hCdef]
    exact le_trans (jetC_nonneg ((n : ℝ) + 1 / 2) jetMZ jetKZ (fun _ => 0) (fun _ => 1)
      jetMZ_nonneg jetKZ_nonneg (fun _ => le_refl 0) (fun _ => zero_le_one) (n + 1) 0)
      (le_max_left _ _)
  · intro h δ hδ hδ1 hh hjet a ha σ hσ t ht
    have hδ0 : 0 ≤ δ := le_of_lt hδ
    have hjet' : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ := hjet
    have hZh : ∀ i, i ≤ (n + 1) + 1 → ∀ a ∈ Set.Icc (49 / 100 : ℝ) 1,
        |iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a| ≤ jetMZ i + 2 * jetKZ i := by
      intro i hi a ha
      refine le_trans (abs_iteratedDeriv_Zrad_le hh hδ1 hjet' ha ht hσ (by omega)) ?_
      rw [jetMZ, jetKZ]
      have h2i : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i]
    have hZd : ∀ i, i ≤ (n + 1) + 1 → ∀ a ∈ Set.Icc (49 / 100 : ℝ) 1,
        |iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a -
          iteratedDeriv i (fun a : ℝ => Zrad 0 (a, σ, t)) a| ≤ jetKZ i * δ := by
      intro i hi a ha
      rw [jetKZ]
      exact abs_iteratedDeriv_Zrad_diff_le hh hδ0 hδ1 hjet' ha ht hσ (by omega)
    have hZ0 : ∀ i, i ≤ (n + 1) + 1 → ∀ a ∈ Set.Icc (49 / 100 : ℝ) 1,
        |iteratedDeriv i (fun a : ℝ => Zrad 0 (a, σ, t)) a| ≤ jetMZ i := by
      intro i hi a ha
      rw [jetMZ]
      exact abs_iteratedDeriv_Zrad_le (h := fun _ : ℝ => (0 : ℝ)) contDiff_const hδ1
        (fun k _ a => by
          rw [iteratedDeriv_const]; split_ifs <;> simp [hδ0]) ha ht hσ (by omega)
    have hIhd : ∀ j, j ≤ (n + 1) + 1 → ∀ a ∈ Set.Icc (49 / 100 : ℝ) 1,
        |iteratedDeriv j (fun a : ℝ => (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (a, σ, t)) a -
          iteratedDeriv j (fun a : ℝ => (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (a, σ, t)) a|
            ≤ (0 : ℝ) * δ := by
      intro j hj a ha
      simp
    have hI0 : ∀ j, j ≤ (n + 1) + 1 → ∀ a ∈ Set.Icc (49 / 100 : ℝ) 1,
        |iteratedDeriv j (fun a : ℝ => (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (a, σ, t)) a|
          ≤ (1 : ℝ) := by
      intro j hj a ha
      rw [show (fun a : ℝ => (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (a, σ, t)) =
          fun _ : ℝ => (1 : ℝ) from rfl, iteratedDeriv_const]
      split_ifs <;> norm_num
    obtain ⟨h1, h2⟩ := rnu_jet_bound ((n : ℝ) + 1 / 2) (n + 1) (49 / 100) 1 jetKZ jetMZ
      (fun _ => 0) (fun _ => 1) jetKZ_nonneg jetMZ_nonneg (fun _ => le_refl 0)
      (fun _ => zero_le_one) h (fun _ => 1) (fun _ => 1) hh contDiff_const contDiff_const
      σ t δ hδ0 (le_trans hδ1 (by norm_num)) hZh hZd hZ0 hIhd hI0 (n + 1) 0 (by omega) a ha
    obtain ⟨h3, h4⟩ := rnu_jet_bound ((n : ℝ) + 1 / 2) (n + 1) (49 / 100) 1 jetKZ jetMZ
      (fun _ => 0) (fun _ => 1) jetKZ_nonneg jetMZ_nonneg (fun _ => le_refl 0)
      (fun _ => zero_le_one) h (fun _ => 1) (fun _ => 1) hh contDiff_const contDiff_const
      σ t δ hδ0 (le_trans hδ1 (by norm_num)) hZh hZd hZ0 hIhd hI0 (n + 1) 1 (by omega) a ha
    have hC0 : jetC ((n : ℝ) + 1 / 2) jetMZ jetKZ (fun _ => 0) (fun _ => 1) (n + 1) 0 ≤ C := by
      rw [hCdef]; exact le_max_left _ _
    have hC1 : jetC ((n : ℝ) + 1 / 2) jetMZ jetKZ (fun _ => 0) (fun _ => 1) (n + 1) 1 ≤ C := by
      rw [hCdef]; exact le_max_right _ _
    have hJ10 : J1M n h a σ t = iteratedDeriv 0
        (fun a : ℝ => Rnu ((n : ℝ) + 1 / 2) h (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (n + 1)
          (a, σ, t)) a := by simp [J1M]
    have hJ20 : J1M n 0 a σ t = iteratedDeriv 0
        (fun a : ℝ => Rnu ((n : ℝ) + 1 / 2) 0 (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (n + 1)
          (a, σ, t)) a := by simp [J1M]
    have hJ11 : deriv (fun a : ℝ => J1M n h a σ t) a = iteratedDeriv 1
        (fun a : ℝ => Rnu ((n : ℝ) + 1 / 2) h (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (n + 1)
          (a, σ, t)) a := by
      rw [iteratedDeriv_one]
      simp only [J1M]
    have hJ21 : deriv (fun a : ℝ => J1M n 0 a σ t) a = iteratedDeriv 1
        (fun a : ℝ => Rnu ((n : ℝ) + 1 / 2) 0 (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (n + 1)
          (a, σ, t)) a := by
      rw [iteratedDeriv_one]
      simp only [J1M]
    exact ⟨⟨by rw [hJ10, hJ20]; exact le_trans h1 (mul_le_mul_of_nonneg_right hC0 hδ0),
      by rw [hJ11, hJ21]; exact le_trans h3 (mul_le_mul_of_nonneg_right hC1 hδ0)⟩,
      by rw [hJ20]; exact le_trans h2 hC0, by rw [hJ21]; exact le_trans h4 hC1⟩

set_option maxHeartbeats 1000000 in
/-- **Jet bounds for `J2M`.**  Same as `aw_J1M_jet_bound`, for the second numerator. -/
theorem aw_J2M_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 / 100 →
      ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ a ∈ Set.Icc (49 / 100 : ℝ) 1, ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (19 / 20),
        ∀ t ∈ Set.Icc (-2 : ℝ) 2,
        (|J2M n h a σ t - J2M n 0 a σ t| ≤ C * δ ∧
         |deriv (fun a : ℝ => J2M n h a σ t) a - deriv (fun a : ℝ => J2M n 0 a σ t) a|
            ≤ C * δ) ∧
        (|J2M n 0 a σ t| ≤ C ∧ |deriv (fun a : ℝ => J2M n 0 a σ t) a| ≤ C) := by
  set C : ℝ := max (jetC ((n : ℝ) - 1 / 2) jetMZ jetKZ (fun _ => 1) (fun _ => 2) n 0)
      (jetC ((n : ℝ) - 1 / 2) jetMZ jetKZ (fun _ => 1) (fun _ => 2) n 1) with hCdef
  refine ⟨C, ?_, ?_⟩
  · rw [hCdef]
    exact le_trans (jetC_nonneg ((n : ℝ) - 1 / 2) jetMZ jetKZ (fun _ => 1) (fun _ => 2)
      jetMZ_nonneg jetKZ_nonneg (fun _ => zero_le_one) (fun _ => by norm_num) n 0)
      (le_max_left _ _)
  · intro h δ hδ hδ1 hh hjet a ha σ hσ t ht
    have hδ0 : 0 ≤ δ := le_of_lt hδ
    have hjet' : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ := hjet
    have hZh : ∀ i, i ≤ n + 1 → ∀ a ∈ Set.Icc (49 / 100 : ℝ) 1,
        |iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a| ≤ jetMZ i + 2 * jetKZ i := by
      intro i hi a ha
      refine le_trans (abs_iteratedDeriv_Zrad_le hh hδ1 hjet' ha ht hσ (by omega)) ?_
      rw [jetMZ, jetKZ]
      have h2i : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i]
    have hZd : ∀ i, i ≤ n + 1 → ∀ a ∈ Set.Icc (49 / 100 : ℝ) 1,
        |iteratedDeriv i (fun a : ℝ => Zrad h (a, σ, t)) a -
          iteratedDeriv i (fun a : ℝ => Zrad 0 (a, σ, t)) a| ≤ jetKZ i * δ := by
      intro i hi a ha
      rw [jetKZ]
      exact abs_iteratedDeriv_Zrad_diff_le hh hδ0 hδ1 hjet' ha ht hσ (by omega)
    have hZ0 : ∀ i, i ≤ n + 1 → ∀ a ∈ Set.Icc (49 / 100 : ℝ) 1,
        |iteratedDeriv i (fun a : ℝ => Zrad 0 (a, σ, t)) a| ≤ jetMZ i := by
      intro i hi a ha
      rw [jetMZ]
      exact abs_iteratedDeriv_Zrad_le (h := fun _ : ℝ => (0 : ℝ)) contDiff_const hδ1
        (fun k _ a => by
          rw [iteratedDeriv_const]; split_ifs <;> simp [hδ0]) ha ht hσ (by omega)
    have hIhd : ∀ j, j ≤ n + 1 → ∀ a ∈ Set.Icc (49 / 100 : ℝ) 1,
        |iteratedDeriv j (fun a : ℝ => lineSlope h a t) a -
          iteratedDeriv j (fun a : ℝ => lineSlope (0 : ℝ → ℝ) a t) a| ≤ (1 : ℝ) * δ := by
      intro j hj a ha
      have hcd1 : ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => lineSlope h a t) := by
        unfold lineSlope; fun_prop
      have hcd0 : ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => lineSlope (0 : ℝ → ℝ) a t) := by
        have hzero : (fun a : ℝ => lineSlope (0 : ℝ → ℝ) a t) = fun _ : ℝ => t := by
          funext x; simp [lineSlope]
        rw [hzero]; fun_prop
      have he : (fun a : ℝ => lineSlope h a t) - (fun a : ℝ => lineSlope (0 : ℝ → ℝ) a t)
          = fun a : ℝ => deriv h a := by
        funext x; simp [lineSlope]
      rw [← iteratedDeriv_sub (hcd1.contDiffAt.of_le (natCast_le_top_enat j))
        (hcd0.contDiffAt.of_le (natCast_le_top_enat j)), he, one_mul]
      have hs : iteratedDeriv j (fun a : ℝ => deriv h a) a = iteratedDeriv (j + 1) h a := by
        rw [iteratedDeriv_succ' (f := h) (n := j)]
      rw [hs]
      exact hjet (j + 1) (by omega) a
    have hI0 : ∀ j, j ≤ n + 1 → ∀ a ∈ Set.Icc (49 / 100 : ℝ) 1,
        |iteratedDeriv j (fun a : ℝ => lineSlope (0 : ℝ → ℝ) a t) a| ≤ (2 : ℝ) := by
      intro j hj a ha
      have heq : (fun a : ℝ => lineSlope (0 : ℝ → ℝ) a t) = fun _ : ℝ => t := by
        funext x; simp [lineSlope]
      rw [heq, iteratedDeriv_const]
      split_ifs with hj0
      · rw [abs_le]; exact ht
      · simp
    obtain ⟨h1, h2⟩ := rnu_jet_bound ((n : ℝ) - 1 / 2) n (49 / 100) 1 jetKZ jetMZ
      (fun _ => 1) (fun _ => 2) jetKZ_nonneg jetMZ_nonneg (fun _ => zero_le_one)
      (fun _ => by norm_num) h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2)
      (fun p : ℝ × ℝ × ℝ => lineSlope (0 : ℝ → ℝ) p.1 p.2.2) hh
      (by unfold lineSlope; fun_prop)
      (by
        have : (fun p : ℝ × ℝ × ℝ => lineSlope (0 : ℝ → ℝ) p.1 p.2.2) =
            fun p : ℝ × ℝ × ℝ => p.2.2 := by
          funext p; simp [lineSlope]
        rw [this]; fun_prop)
      σ t δ hδ0 (le_trans hδ1 (by norm_num)) hZh hZd hZ0 hIhd hI0 n 0 (by omega) a ha
    obtain ⟨h3, h4⟩ := rnu_jet_bound ((n : ℝ) - 1 / 2) n (49 / 100) 1 jetKZ jetMZ
      (fun _ => 1) (fun _ => 2) jetKZ_nonneg jetMZ_nonneg (fun _ => zero_le_one)
      (fun _ => by norm_num) h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2)
      (fun p : ℝ × ℝ × ℝ => lineSlope (0 : ℝ → ℝ) p.1 p.2.2) hh
      (by unfold lineSlope; fun_prop)
      (by
        have : (fun p : ℝ × ℝ × ℝ => lineSlope (0 : ℝ → ℝ) p.1 p.2.2) =
            fun p : ℝ × ℝ × ℝ => p.2.2 := by
          funext p; simp [lineSlope]
        rw [this]; fun_prop)
      σ t δ hδ0 (le_trans hδ1 (by norm_num)) hZh hZd hZ0 hIhd hI0 n 1 (by omega) a ha
    have hC0 : jetC ((n : ℝ) - 1 / 2) jetMZ jetKZ (fun _ => 1) (fun _ => 2) n 0 ≤ C := by
      rw [hCdef]; exact le_max_left _ _
    have hC1 : jetC ((n : ℝ) - 1 / 2) jetMZ jetKZ (fun _ => 1) (fun _ => 2) n 1 ≤ C := by
      rw [hCdef]; exact le_max_right _ _
    have hJ10 : J2M n h a σ t = iteratedDeriv 0
        (fun a : ℝ => Rnu ((n : ℝ) - 1 / 2) h
          (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) n (a, σ, t)) a := by simp [J2M]
    have hJ20 : J2M n 0 a σ t = iteratedDeriv 0
        (fun a : ℝ => Rnu ((n : ℝ) - 1 / 2) 0
          (fun p : ℝ × ℝ × ℝ => lineSlope (0 : ℝ → ℝ) p.1 p.2.2) n (a, σ, t)) a := by
      simp [J2M]
    have hJ11 : deriv (fun a : ℝ => J2M n h a σ t) a = iteratedDeriv 1
        (fun a : ℝ => Rnu ((n : ℝ) - 1 / 2) h
          (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) n (a, σ, t)) a := by
      rw [iteratedDeriv_one]
      simp only [J2M]
    have hJ21 : deriv (fun a : ℝ => J2M n 0 a σ t) a = iteratedDeriv 1
        (fun a : ℝ => Rnu ((n : ℝ) - 1 / 2) 0
          (fun p : ℝ × ℝ × ℝ => lineSlope (0 : ℝ → ℝ) p.1 p.2.2) n (a, σ, t)) a := by
      rw [iteratedDeriv_one]
      simp only [J2M]
    exact ⟨⟨by rw [hJ10, hJ20]; exact le_trans h1 (mul_le_mul_of_nonneg_right hC0 hδ0),
      by rw [hJ11, hJ21]; exact le_trans h3 (mul_le_mul_of_nonneg_right hC1 hδ0)⟩,
      by rw [hJ20]; exact le_trans h2 hC0, by rw [hJ21]; exact le_trans h4 hC1⟩

/-! ## Measurability, quotient estimates and the bounds for `K1M`, `K2M` -/

lemma measurable_K1M (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    Measurable (fun a : ℝ => K1M n h a σ t) := by
  have hJ : Measurable (fun a : ℝ => J1M n h a σ t) := by
    have hcont : Continuous (fun a : ℝ => J1M n h a σ t) :=
      (Rnu_contDiff_aux ((n : ℝ) + 1 / 2) hh contDiff_const (n + 1)).continuous.comp
        (by fun_prop : Continuous fun a : ℝ => (a, σ, t))
    exact hcont.measurable
  have hK : Measurable (fun a : ℝ => Kden h a σ t) := by
    have hcont : Continuous (fun a : ℝ => Kden h a σ t) := by
      unfold Kden
      refine Real.continuous_sqrt.comp (Continuous.mul ?_ ?_)
      · exact continuous_const.add (((Work.OddVolterra.Existence.hquot_contDiff hh).continuous).comp
          (by fun_prop : Continuous fun a : ℝ => (a, σ)))
      · exact continuous_const.add (by unfold line; fun_prop)
    exact hcont.measurable
  exact hJ.div hK

lemma measurable_K2M (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    Measurable (fun a : ℝ => K2M n h a σ t) := by
  have hinit : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) := by
    unfold lineSlope; fun_prop
  have hJ : Measurable (fun a : ℝ => J2M n h a σ t) := by
    have hcont : Continuous (fun a : ℝ => J2M n h a σ t) :=
      (Rnu_contDiff_aux ((n : ℝ) - 1 / 2) hh hinit n).continuous.comp
        (by fun_prop : Continuous fun a : ℝ => (a, σ, t))
    exact hcont.measurable
  have hK : Measurable (fun a : ℝ => Kden h a σ t) := by
    have hcont : Continuous (fun a : ℝ => Kden h a σ t) := by
      unfold Kden
      refine Real.continuous_sqrt.comp (Continuous.mul ?_ ?_)
      · exact continuous_const.add (((Work.OddVolterra.Existence.hquot_contDiff hh).continuous).comp
          (by fun_prop : Continuous fun a : ℝ => (a, σ)))
      · exact continuous_const.add (by unfold line; fun_prop)
    exact hcont.measurable
  exact hJ.div hK

/-- `KvecM` is measurable in its first slot. -/
lemma measurable_KvecM (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) (z : St) :
    Measurable (fun a : ℝ => KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) := by
  have h1 := measurable_K1M (n := n) (h := h) hh σ (-(z 0))
  have h2 := measurable_K1M (n := n) (h := h) hh σ (z 1)
  have h3 := measurable_K2M (n := n) (h := h) hh σ (-(z 0))
  have h4 := measurable_K2M (n := n) (h := h) hh σ (z 1)
  rw [show (fun a : ℝ => KvecM n h a σ (z 0) (z 1) (z 2) (z 3))
      = fun a : ℝ => ![- (K1M n h a σ (-(z 0)) * z 2 + K1M n h a σ (z 1) * z 3),
          - (K2M n h a σ (-(z 0)) * z 2 + K2M n h a σ (z 1) * z 3)] from by
      funext a i
      fin_cases i <;> rfl]
  rw [measurable_pi_iff]
  intro i
  fin_cases i
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    exact ((h1.mul measurable_const).add (h2.mul measurable_const)).neg
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    exact ((h3.mul measurable_const).add (h4.mul measurable_const)).neg

/-- `|a - b| ≤ |a| + |b|`. -/
lemma abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

/-- `|a + b - c - d| ≤ |a| + |b| + |c| + |d|`. -/
lemma abs_sub_le_four (a b c d : ℝ) : |a + b - c - d| ≤ |a| + |b| + |c| + |d| := by
  have hkey : a + b - c - d = (a + b) - (c + d) := by ring
  rw [hkey]
  refine le_trans (abs_sub_le_add _ _) ?_
  refine le_trans (add_le_add (abs_add_le a b) (abs_add_le c d)) ?_
  ring_nf
  exact le_refl _

/-- Value estimate for the quotients. -/
lemma div_close {f1 f0 g1 g0 : ℝ → ℝ} {x Cf c e : ℝ}
    (hc : 0 < c) (he : 0 ≤ e) (hCf : 0 ≤ Cf)
    (hf : |f1 x - f0 x| ≤ e) (hg : |g1 x - g0 x| ≤ e)
    (hf0 : |f0 x| ≤ Cf) (hg1b : c ≤ |g1 x|) (hg0b : c ≤ |g0 x|) :
    |f1 x / g1 x - f0 x / g0 x| ≤ (1 / c + Cf / c ^ 2) * e := by
  have hg1pos : 0 < |g1 x| := lt_of_lt_of_le hc hg1b
  have hg0pos : 0 < |g0 x| := lt_of_lt_of_le hc hg0b
  have h1 : g1 x ≠ 0 := abs_pos.mp hg1pos
  have h0 : g0 x ≠ 0 := abs_pos.mp hg0pos
  have hkey : f1 x / g1 x - f0 x / g0 x =
      (f1 x - f0 x) / g1 x - f0 x * (g1 x - g0 x) / (g1 x * g0 x) := by
    field_simp
    ring
  rw [hkey]
  refine le_trans (abs_sub_le_add _ _) ?_
  have hb1 : |(f1 x - f0 x) / g1 x| ≤ e / c := by
    rw [abs_div]
    exact div_le_div₀ he hf hc hg1b
  have hb2 : |f0 x * (g1 x - g0 x) / (g1 x * g0 x)| ≤ Cf * e / c ^ 2 := by
    rw [abs_div, abs_mul]
    have hnum : |f0 x| * |g1 x - g0 x| ≤ Cf * e :=
      mul_le_mul hf0 hg (abs_nonneg _) (le_trans (abs_nonneg _) hf0)
    have hden : c ^ 2 ≤ |g1 x * g0 x| := by
      rw [abs_mul, pow_two]
      exact mul_le_mul_of_nonneg hg1b hg0b (le_of_lt hc) (abs_nonneg _)
    exact div_le_div₀ (mul_nonneg hCf he) hnum (pow_pos hc 2) hden
  have h3 : (1 / c + Cf / c ^ 2) * e = e / c + Cf * e / c ^ 2 := by ring
  rw [h3]
  exact add_le_add hb1 hb2

/-- Derivative estimate for the quotients (quotient rule + telescoping). -/
lemma deriv_div_close {f1 f0 g1 g0 : ℝ → ℝ} {x Cf Cg Cg' c e : ℝ}
    (hc : 0 < c) (he : 0 ≤ e) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hCg' : 0 ≤ Cg')
    (hfd1 : DifferentiableAt ℝ f1 x) (hfd0 : DifferentiableAt ℝ f0 x)
    (hgd1 : DifferentiableAt ℝ g1 x) (hgd0 : DifferentiableAt ℝ g0 x)
    (hg1ne : g1 x ≠ 0) (hg0ne : g0 x ≠ 0)
    (hf : |f1 x - f0 x| ≤ e) (hfd : |deriv f1 x - deriv f0 x| ≤ e)
    (hg : |g1 x - g0 x| ≤ e) (hgd : |deriv g1 x - deriv g0 x| ≤ e)
    (hf1 : |f1 x| ≤ Cf) (hf0 : |f0 x| ≤ Cf)
    (hf1' : |deriv f1 x| ≤ Cf) (hf0' : |deriv f0 x| ≤ Cf)
    (hg1b : |g1 x| ≤ Cg) (hg0b : |g0 x| ≤ Cg)
    (hg1b' : |deriv g1 x| ≤ Cg') (hg0b' : |deriv g0 x| ≤ Cg')
    (hc1 : c ≤ |g1 x|) (hc0 : c ≤ |g0 x|) :
    |deriv (f1 / g1) x - deriv (f0 / g0) x|
      ≤ (2 * (Cf * Cg + Cf * Cg') * Cg / c ^ 4 + (Cg + 2 * Cf + Cg') / c ^ 2) * e := by
  rw [deriv_div hfd1 hgd1 hg1ne, deriv_div hfd0 hgd0 hg0ne]
  set N1 : ℝ := deriv f1 x * g1 x - f1 x * deriv g1 x with hN1
  set N0 : ℝ := deriv f0 x * g0 x - f0 x * deriv g0 x with hN0
  have hg1sqpos : 0 < g1 x ^ 2 := by
    have h := pow_pos (abs_pos.mpr hg1ne) 2
    rwa [sq_abs] at h
  have hg0sqpos : 0 < g0 x ^ 2 := by
    have h := pow_pos (abs_pos.mpr hg0ne) 2
    rwa [sq_abs] at h
  have hsq1 : c ^ 2 ≤ g1 x ^ 2 := by
    have h := pow_le_pow_left₀ (le_of_lt hc) hc1 2
    rwa [sq_abs] at h
  have hsq0 : c ^ 2 ≤ g0 x ^ 2 := by
    have h := pow_le_pow_left₀ (le_of_lt hc) hc0 2
    rwa [sq_abs] at h
  have hN1b : |N1| ≤ Cf * Cg + Cf * Cg' := by
    rw [hN1]
    refine le_trans (abs_sub_le_add _ _) ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul hf1' hg1b (abs_nonneg _) hCf)
      (mul_le_mul hf1 hg1b' (abs_nonneg _) hCf)
  have hNN : |N1 - N0| ≤ e * (Cg + 2 * Cf + Cg') := by
    have hkey : N1 - N0 = (deriv f1 x - deriv f0 x) * g1 x + deriv f0 x * (g1 x - g0 x)
        - (f1 x - f0 x) * deriv g1 x - f0 x * (deriv g1 x - deriv g0 x) := by
      rw [hN1, hN0]; ring
    rw [hkey]
    have b1 : |(deriv f1 x - deriv f0 x) * g1 x| ≤ e * Cg := by
      rw [abs_mul]; exact mul_le_mul hfd hg1b (abs_nonneg _) he
    have b2 : |deriv f0 x * (g1 x - g0 x)| ≤ Cf * e := by
      rw [abs_mul]; exact mul_le_mul hf0' hg (abs_nonneg _) hCf
    have b3 : |(f1 x - f0 x) * deriv g1 x| ≤ e * Cg' := by
      rw [abs_mul]; exact mul_le_mul hf hg1b' (abs_nonneg _) he
    have b4 : |f0 x * (deriv g1 x - deriv g0 x)| ≤ Cf * e := by
      rw [abs_mul]; exact mul_le_mul hf0 hgd (abs_nonneg _) hCf
    refine le_trans (abs_sub_le_four _ _ _ _) ?_
    refine le_trans (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) ?_
    ring_nf
    nlinarith [he, hCf, hCg, hCg']
  have hDD : |g0 x ^ 2 - g1 x ^ 2| ≤ 2 * Cg * e := by
    have hkey : g0 x ^ 2 - g1 x ^ 2 = (g0 x - g1 x) * (g0 x + g1 x) := by ring
    rw [hkey, abs_mul]
    have h1 : |g0 x + g1 x| ≤ Cg + Cg := le_trans (abs_add_le _ _) (add_le_add hg0b hg1b)
    have h2 : |g0 x - g1 x| ≤ e := by
      rw [abs_sub_comm]; exact hg
    calc |g0 x - g1 x| * |g0 x + g1 x| ≤ e * (Cg + Cg) := mul_le_mul h2 h1 (abs_nonneg _) he
      _ = 2 * Cg * e := by ring
  have hsplit : N1 / g1 x ^ 2 - N0 / g0 x ^ 2 =
      (N1 * (g0 x ^ 2 - g1 x ^ 2) + (N1 - N0) * g1 x ^ 2) / (g1 x ^ 2 * g0 x ^ 2) := by
    field_simp
    ring
  have hA : |N1 * (g0 x ^ 2 - g1 x ^ 2)| / (g1 x ^ 2 * g0 x ^ 2)
      ≤ (Cf * Cg + Cf * Cg') * (2 * Cg * e) / c ^ 4 := by
    refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
    · rw [abs_mul]
      exact mul_le_mul hN1b hDD (abs_nonneg _) (le_trans (abs_nonneg _) hN1b)
    · nlinarith [hsq1, hsq0, hc]
  have hB : |(N1 - N0) * g1 x ^ 2| / (g1 x ^ 2 * g0 x ^ 2)
      ≤ e * (Cg + 2 * Cf + Cg') / c ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (g1 x))]
    have hg1sqne : g1 x ^ 2 ≠ 0 := ne_of_gt hg1sqpos
    calc |N1 - N0| * g1 x ^ 2 / (g1 x ^ 2 * g0 x ^ 2)
        ≤ (e * (Cg + 2 * Cf + Cg')) * g1 x ^ 2 / (g1 x ^ 2 * g0 x ^ 2) :=
          div_le_div₀ (by positivity) (mul_le_mul hNN le_rfl (by positivity) (by positivity))
            (by positivity) le_rfl
      _ = e * (Cg + 2 * Cf + Cg') / g0 x ^ 2 := by
          rw [mul_comm (g1 x ^ 2) (g0 x ^ 2), mul_div_mul_right _ _ hg1sqne]
      _ ≤ e * (Cg + 2 * Cf + Cg') / c ^ 2 := by
          refine div_le_div₀ (by positivity) le_rfl (by positivity) ?_
          nlinarith [hsq0, hc]
  have hAB : |N1 * (g0 x ^ 2 - g1 x ^ 2) + (N1 - N0) * g1 x ^ 2| / (g1 x ^ 2 * g0 x ^ 2)
      ≤ (2 * (Cf * Cg + Cf * Cg') * Cg / c ^ 4 + (Cg + 2 * Cf + Cg') / c ^ 2) * e := by
    calc |N1 * (g0 x ^ 2 - g1 x ^ 2) + (N1 - N0) * g1 x ^ 2| / (g1 x ^ 2 * g0 x ^ 2)
        ≤ (|N1 * (g0 x ^ 2 - g1 x ^ 2)| + |(N1 - N0) * g1 x ^ 2|) / (g1 x ^ 2 * g0 x ^ 2) :=
          div_le_div₀ (by positivity) (abs_add_le _ _) (by positivity) le_rfl
      _ = |N1 * (g0 x ^ 2 - g1 x ^ 2)| / (g1 x ^ 2 * g0 x ^ 2) +
            |(N1 - N0) * g1 x ^ 2| / (g1 x ^ 2 * g0 x ^ 2) := by rw [add_div]
      _ ≤ (Cf * Cg + Cf * Cg') * (2 * Cg * e) / c ^ 4 + e * (Cg + 2 * Cf + Cg') / c ^ 2 :=
          add_le_add hA hB
      _ = (2 * (Cf * Cg + Cf * Cg') * Cg / c ^ 4 + (Cg + 2 * Cf + Cg') / c ^ 2) * e := by
          ring
  rw [hsplit, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ g1 x ^ 2 * g0 x ^ 2)]
  exact hAB

/-! ## Bounds for the common denominator `Kden` -/

/-- The radicand of `Kden`, in the same form as `krad`. -/
def abelRad (h : ℝ → ℝ) (a σ t : ℝ) : ℝ :=
  (t + hquot h a σ) * (line h σ t + line h a t)

lemma abelRad_eq_krad (h : ℝ → ℝ) (a σ t : ℝ) : abelRad h a σ t = krad h σ t a := rfl

lemma Kden_eq_sqrt_abelRad (h : ℝ → ℝ) (a σ t : ℝ) : Kden h a σ t = √(abelRad h a σ t) := rfl

lemma hquot_zero (a σ : ℝ) : hquot (0 : ℝ → ℝ) a σ = 0 := by
  rw [hquot]; simp

lemma line_zero_left (x t : ℝ) : line (0 : ℝ → ℝ) x t = x * t := by simp [line]

/-- `deriv` of `a ↦ t + hquot h a σ`. -/
lemma hasDerivAt_hquot_add (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a σ t : ℝ) :
    HasDerivAt (fun x : ℝ => t + hquot h x σ) (deriv (fun x : ℝ => hquot h x σ) a) a := by
  have h1 : HasDerivAt (fun x : ℝ => hquot h x σ + t)
      (deriv (fun x : ℝ => hquot h x σ) a) a :=
    ((((Work.OddVolterra.Existence.hquot_contDiff hh).comp
        (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableAt).hasDerivAt.add_const t
  simpa [add_comm] using h1

lemma hasDerivAt_line (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a t : ℝ) :
    HasDerivAt (fun x : ℝ => line h x t) (t + deriv h a) a := by
  have h1 : HasDerivAt (fun x : ℝ => line h x t) ((1 : ℝ) * t + deriv h a) a :=
    ((hasDerivAt_id a).mul_const t).add ((hh.differentiable (by simp)).differentiableAt.hasDerivAt)
  simpa using h1

/-- `HasDerivAt` form of the sum `line h σ t + line h x t`. -/
lemma hasDerivAt_line_add (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a σ t : ℝ) :
    HasDerivAt (fun x : ℝ => line h σ t + line h x t) (t + deriv h a) a := by
  have h1 : HasDerivAt (fun x : ℝ => line h x t + line h σ t) (t + deriv h a) a :=
    (hasDerivAt_line h hh a t).add_const (line h σ t)
  simpa [add_comm] using h1


end

end Work.OddExistence.Manifest.AW
