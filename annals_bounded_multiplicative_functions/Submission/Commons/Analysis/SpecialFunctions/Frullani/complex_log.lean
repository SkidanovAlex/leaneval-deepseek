import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Real BigOperators Topology
open MeasureTheory Set Filter
open intervalIntegral

noncomputable section

namespace Commons.Analysis.SpecialFunctions.Frullani



/-- For Re w > 0, ∫_{Ioi 0} exp (-(w * (t : ℂ))) dt = w⁻¹. -/
lemma exp_neg_mul_Ioi (w : ℂ) (hw : 0 < w.re) :
    (∫ t : ℝ in Set.Ioi 0, Complex.exp (-(w * (t : ℂ)))) = w⁻¹ := by
  have hI := integral_exp_mul_complex_Ioi (a := -w) (by simpa [hw] : (-w).re < 0) (0 : ℝ)
  have hfun : (fun t : ℝ => Complex.exp (-(w * (t : ℂ)))) = fun x : ℝ => Complex.exp ((-w) * (x : ℂ)) := by
    funext x
    congr 1
    ring
  rw [hfun, hI]
  simp

/-- derivative in u of exp (-((b + u * c) * t)) -/
lemma hasDerivAt_exp_neg_mul_seg (b c t : ℂ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (-((b + (u : ℂ) * c) * t)))
      (Complex.exp (-((b + (u : ℂ) * c) * t)) * (-(c * t))) u := by
  have hZ : HasDerivAt (fun u : ℝ => b + (u : ℂ) * c) c u := by
    simpa using (((hasDerivAt_id (u : ℂ)).mul_const c).comp_ofReal).const_add b
  have hE : HasDerivAt (fun u : ℝ => -((b + (u : ℂ) * c) * t)) (-(c * t)) u := by
    convert (hZ.mul_const t).neg <;> first | rfl | ring
  convert (Complex.hasDerivAt_exp (-((b + (u : ℂ) * c) * t))).comp u hE <;> first | rfl | ring

/-- exp(-((b+c)*t)) - exp(-(b*t)) = -(c*t) ∫_0^1 exp(-((b+u*c)*t)) du -/
lemma seg_diff_eq_integral (b c t : ℂ) :
    Complex.exp (-((b + c) * t)) - Complex.exp (-(b * t)) =
      -(c * t) * (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (-((b + (u : ℂ) * c) * t))) := by
  let F : ℝ → ℂ := fun u => Complex.exp (-((b + (u : ℂ) * c) * t))
  let F' : ℝ → ℂ := fun u => F u * (-(c * t))
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    unfold F
    fun_prop
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (F' x) x := by
    intro x hx
    unfold F' F
    simpa [mul_comm, mul_left_comm, mul_assoc] using hasDerivAt_exp_neg_mul_seg b c t x
  have hint : IntervalIntegrable F' volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    unfold F' F
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (E := ℂ) (a := (0 : ℝ)) (b := 1) (f := F) (f' := F') (by norm_num) hcont hderiv hint
  have hmain : (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (-((b + (u : ℂ) * c) * t)) * (-(c * t))) =
      Complex.exp (-((b + (1 : ℂ) * c) * t)) - Complex.exp (-((b + (0 : ℂ) * c) * t)) := by
    simpa [F, F'] using hFTC
  have h1 : (b + (1 : ℂ) * c) * t = (b + c) * t := by ring
  have h0 : (b + (0 : ℂ) * c) * t = b * t := by ring
  calc
    Complex.exp (-((b + c) * t)) - Complex.exp (-(b * t))
        = Complex.exp (-((b + (1 : ℂ) * c) * t)) - Complex.exp (-((b + (0 : ℂ) * c) * t)) := by
          rw [h1, h0]
    _ = (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (-((b + (u : ℂ) * c) * t)) * (-(c * t))) := by
          rw [← hmain]
    _ = (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (-((b + (u : ℂ) * c) * t))) * (-(c * t)) := by
          rw [intervalIntegral.integral_mul_const]
    _ = -(c * t) * (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (-((b + (u : ℂ) * c) * t))) := by
          ring

/-- log FTC along the segment u ↦ b + u*c, u ∈ [0,1] -/
lemma integral_inv_seg_log (b c : ℂ) (hseg : ∀ u ∈ Set.Icc (0 : ℝ) 1,
    (b + (u : ℂ) * c) ∈ Complex.slitPlane) :
    c * (∫ u : ℝ in (0 : ℝ)..1, (b + (u : ℂ) * c)⁻¹) =
      Complex.log (b + c) - Complex.log b := by
  let Z : ℝ → ℂ := fun u => b + (u : ℂ) * c
  let f : ℝ → ℂ := fun u => Complex.log (Z u)
  let f' : ℝ → ℂ := fun u => c * (Z u)⁻¹
  have hZ (u : ℝ) : HasDerivAt Z c u := by
    unfold Z
    simpa using (((hasDerivAt_id (u : ℂ)).mul_const c).comp_ofReal).const_add b
  have hlog (u : ℝ) (hu : Z u ∈ Complex.slitPlane) :
      HasDerivAt (fun u : ℝ => Complex.log (Z u)) ((Z u)⁻¹ * c) u := by
    have := (Complex.hasDerivAt_log hu).comp u (hZ u)
    convert this using 1 <;> first | rfl | ring
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    unfold f Z
    have hZc : ContinuousWithinAt (fun u : ℝ => b + (u : ℂ) * c) (Set.Icc (0 : ℝ) 1) x := by
      fun_prop
    have hlogc : ContinuousAt Complex.log (b + (x : ℂ) * c) :=
      (Complex.differentiableAt_log (hseg x hx)).continuousAt
    exact @ContinuousAt.comp_continuousWithinAt ℝ ℂ ℂ _ _ _
      (fun u : ℝ => b + (u : ℂ) * c) (Set.Icc (0 : ℝ) 1) x Complex.log hlogc hZc
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    unfold f f' Z
    have hd := hlog x (hseg x hx')
    convert hd using 1 <;> first | rfl | ring
  have hint : IntervalIntegrable f' volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    unfold f' Z
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      apply Complex.slitPlane_ne_zero
      exact hseg x (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (E := ℂ) (a := (0 : ℝ)) (b := 1) (f := f) (f' := f') (by norm_num) hcont hderiv hint
  have hmain : (∫ u : ℝ in (0 : ℝ)..1, c * (Z u)⁻¹) = Complex.log (Z 1) - Complex.log (Z 0) := by
    simpa [f, f'] using hFTC
  have hZ1 : Z 1 = b + c := by unfold Z; norm_num
  have hZ0 : Z 0 = b := by unfold Z; norm_num
  calc
    c * (∫ u : ℝ in (0 : ℝ)..1, (b + (u : ℂ) * c)⁻¹)
        = ∫ u : ℝ in (0 : ℝ)..1, c * ((b + (u : ℂ) * c)⁻¹) := by
          rw [intervalIntegral.integral_const_mul]
    _ = ∫ u : ℝ in (0 : ℝ)..1, c * (Z u)⁻¹ := by rfl
    _ = Complex.log (Z 1) - Complex.log (Z 0) := hmain
    _ = Complex.log (b + c) - Complex.log b := by rw [hZ1, hZ0]

/-- ∫ t in 0..T, exp (-(w*t)) = (1 - exp (-(w*T))) * w⁻¹ for 0 ≤ T -/
lemma integral_exp_neg_mul_interval (w : ℂ) (hw : w ≠ 0) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t : ℝ in (0 : ℝ)..T, Complex.exp (-(w * (t : ℂ)))) =
      (1 - Complex.exp (-(w * (T : ℂ)))) * w⁻¹ := by
  have h := integral_exp_mul_complex (c := -w) (by simp [hw]) (a := (0 : ℝ)) (b := T)
  -- h : ∫ x in 0..T, exp ((-w) * x) = (exp ((-w) * T) - exp ((-w) * 0)) / (-w)
  have hfun : (fun t : ℝ => Complex.exp ((-w) * (t : ℂ))) =
      fun t : ℝ => Complex.exp (-(w * (t : ℂ))) := by
    funext t
    congr 1
    ring
  calc
    (∫ t : ℝ in (0 : ℝ)..T, Complex.exp (-(w * (t : ℂ))))
        = (Complex.exp ((-w) * (T : ℂ)) - Complex.exp ((-w) * (0 : ℂ))) / (-w) := by
          simpa [hfun] using h
    _ = (1 - Complex.exp (-(w * (T : ℂ)))) * w⁻¹ := by
          have h0c : (-w) * (0 : ℂ) = 0 := by ring
          have hTc : (-w) * (T : ℂ) = -(w * (T : ℂ)) := by ring
          rw [h0c, hTc]
          simp
          field_simp [hw]
          ring

/-- pointwise: dividing by t, t ≠ 0 -/
lemma seg_div_eq_integral (b c t : ℂ) (ht : t ≠ 0) :
    (Complex.exp (-((b + c) * t)) - Complex.exp (-(b * t))) / t =
      -(c) * (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (-((b + (u : ℂ) * c) * t))) := by
  have h := seg_diff_eq_integral b c t
  calc
    (Complex.exp (-((b + c) * t)) - Complex.exp (-(b * t))) / t
        = (-(c * t) * (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (-((b + (u : ℂ) * c) * t)))) / t := by
          rw [h]
    _ = -(c) * (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (-((b + (u : ℂ) * c) * t))) := by
          field_simp [ht]


/-- Fubini swap: ∫_u (∫_t) = ∫_t (∫_u), u ∈ Ioc 0 1, t ∈ Ioc 0 T -/
lemma swap_restricted (T : ℝ) {F : ℝ → ℝ → ℂ}
    (hF : Integrable (fun p : ℝ × ℝ => F p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) T)))) :
    (∫ u : ℝ in Ioc (0 : ℝ) 1, (∫ t : ℝ in Ioc (0 : ℝ) T, F u t)) =
      (∫ t : ℝ in Ioc (0 : ℝ) T, (∫ u : ℝ in Ioc (0 : ℝ) 1, F u t)) := by
  calc
    (∫ u : ℝ in Ioc (0 : ℝ) 1, (∫ t : ℝ in Ioc (0 : ℝ) T, F u t))
        = ∫ p : ℝ × ℝ, F p.1 p.2
            ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) T))) := by
          rw [integral_prod (μ := volume.restrict (Ioc (0 : ℝ) 1))
            (ν := volume.restrict (Ioc (0 : ℝ) T)) (f := fun p : ℝ × ℝ => F p.1 p.2) hF]
    _ = (∫ t : ℝ in Ioc (0 : ℝ) T, (∫ u : ℝ in Ioc (0 : ℝ) 1, F u t)) := by
          rw [integral_prod_symm (μ := volume.restrict (Ioc (0 : ℝ) 1))
            (ν := volume.restrict (Ioc (0 : ℝ) T)) (f := fun p : ℝ × ℝ => F p.1 p.2) hF]

/-- Fubini: ∫_{t ∈ 0..T} (∫_{u ∈ 0..1} exp(-((b+u*c)*t))) =
      ∫_{u ∈ 0..1} (∫_{t ∈ 0..T} exp(-((b+u*c)*t))) for T ≥ 0 -/
lemma fubini_exp_T (b c : ℂ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t : ℝ in (0 : ℝ)..T, (∫ u : ℝ in (0 : ℝ)..1,
        Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ))))) =
      (∫ u : ℝ in (0 : ℝ)..1, (∫ t : ℝ in (0 : ℝ)..T,
        Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ))))) := by
  let F : ℝ → ℝ → ℂ := fun u t => Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ)))
  have hGc : Continuous (fun p : ℝ × ℝ => F p.1 p.2) := by
    unfold F
    fun_prop
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hsub : (Ioc (0 : ℝ) 1) ×ˢ (Ioc (0 : ℝ) T) ⊆ (Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) T) := by
    intro p hp
    exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, ⟨le_of_lt hp.2.1, hp.2.2⟩⟩
  have hcontK : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) T) := hGc.continuousOn
  have hintK : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) T) (volume.prod volume) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hcontK
  have hintOn : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2)
      ((Ioc (0 : ℝ) 1) ×ˢ (Ioc (0 : ℝ) T)) (volume.prod volume) :=
    hintK.mono_set hsub
  have hprod : Integrable (fun p : ℝ × ℝ => F p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) T))) := by
    rw [Measure.prod_restrict (s := Ioc (0 : ℝ) 1) (t := Ioc (0 : ℝ) T)]
    exact hintOn
  have hswap := swap_restricted (T := T) (F := F) hprod
  calc
    (∫ t : ℝ in (0 : ℝ)..T, (∫ u : ℝ in (0 : ℝ)..1, F u t))
        = (∫ t : ℝ in Ioc (0 : ℝ) T, (∫ u : ℝ in Ioc (0 : ℝ) 1, F u t)) := by
          rw [intervalIntegral.integral_of_le hT]
          congr 1
          funext t
          rw [intervalIntegral.integral_of_le h01]
    _ = (∫ u : ℝ in Ioc (0 : ℝ) 1, (∫ t : ℝ in Ioc (0 : ℝ) T, F u t)) := hswap.symm
    _ = (∫ u : ℝ in (0 : ℝ)..1, (∫ t : ℝ in (0 : ℝ)..T, F u t)) := by
          rw [intervalIntegral.integral_of_le h01]
          congr 1
          funext u
          rw [intervalIntegral.integral_of_le hT]

/-- real part along segment bounded below by min of endpoint real parts -/
lemma re_seg_lower (b c : ℂ) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    min b.re (b + c).re ≤ ((b + (u : ℂ) * c)).re := by
  have hx0 : 0 ≤ u := hu.1
  have hx1 : u ≤ 1 := hu.2
  let M := min b.re (b + c).re
  have hMA : M ≤ b.re := min_le_left _ _
  have hMB : M ≤ (b + c).re := min_le_right _ _
  have hcre : c.re = (b + c).re - b.re := by
    rw [Complex.add_re]
    ring
  have hsum : (b + (u : ℂ) * c).re = (1 - u) * b.re + u * (b + c).re := by
    rw [Complex.add_re, Complex.re_ofReal_mul, hcre]
    ring
  rw [hsum]
  have hA : (1 - u) * M ≤ (1 - u) * b.re :=
    mul_le_mul_of_nonneg_left hMA (sub_nonneg.mpr hx1)
  have hB : u * M ≤ u * (b + c).re := mul_le_mul_of_nonneg_left hMB hx0
  have hconv : (1 - u) * b.re + u * (b + c).re =
      (1 - u) * M + u * M + ((1 - u) * (b.re - M) + u * ((b + c).re - M)) := by ring
  nlinarith [hA, hB]

/-- membership in slitPlane from positive real part along the segment -/
lemma slitPlane_seg_of_re (b c : ℂ) (hb : 0 < b.re) (hc : 0 < (b + c).re) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, (b + (u : ℂ) * c) ∈ Complex.slitPlane := by
  intro u hu
  have hmn := re_seg_lower b c u hu
  have hpos : 0 < ((b + (u : ℂ) * c)).re :=
    lt_of_lt_of_le (lt_min hb hc) hmn
  exact Complex.mem_slitPlane_iff.mpr (Or.inl hpos)

/-- slitPlane membership with explicit m -/
lemma slitPlane_of_m_re {b c : ℂ} {m : ℝ} (hm : 0 < m)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, m ≤ ((b + (u : ℂ) * c)).re) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, (b + (u : ℂ) * c) ∈ Complex.slitPlane := by
  intro u hu
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le hm (hre u hu)))

/-- ‖exp (-(w * (t:ℂ)))‖ = exp (-(w.re * t)) -/
lemma norm_exp_neg_ofReal_mul (w : ℂ) (t : ℝ) :
    ‖Complex.exp (-(w * (t : ℂ)))‖ = Real.exp (-(w.re * t)) := by
  rw [Complex.norm_exp]
  congr 1
  rw [Complex.neg_re, Complex.re_mul_ofReal]

/-- ‖∫_0^1 exp (-((b+u*c) * (t:ℂ))) du‖ ≤ exp (-(m * t)) under Re(b+u*c) ≥ m -/
lemma inner_norm_le (b c : ℂ) {m : ℝ} (hm : 0 < m)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, m ≤ ((b + (u : ℂ) * c)).re)
    {t : ℝ} (ht : 0 < t) :
    ‖(∫ u : ℝ in (0 : ℝ)..1, Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ))))‖ ≤
      Real.exp (-(m * t)) := by
  let F : ℝ → ℂ := fun u => Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ)))
  let G : ℝ → ℝ := fun u => Real.exp (-(m * t))
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hFcont : Continuous F := by
    unfold F; fun_prop
  have hFncont : Continuous (fun u => ‖F u‖) := hFcont.norm
  have hGcont : Continuous G := by
    unfold G; fun_prop
  have hFmono : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖F u‖ ≤ G u := by
    intro u hu
    unfold F G
    rw [norm_exp_neg_ofReal_mul]
    apply Real.exp_le_exp.2
    have hreu : m ≤ ((b + (u : ℂ) * c)).re := hre u hu
    have hlt : m * t ≤ ((b + (u : ℂ) * c)).re * t := mul_le_mul_of_nonneg_right hreu ht.le
    simpa [mul_comm, mul_left_comm, mul_assoc] using neg_le_neg hlt
  have hni := intervalIntegral.norm_integral_le_abs_integral_norm (μ := volume) (a := (0 : ℝ)) (b := 1) (f := F)
  have hnonneg : 0 ≤ (∫ u : ℝ in (0 : ℝ)..1, ‖F u‖) := by
    apply intervalIntegral.integral_nonneg h01
    intro u hu
    exact norm_nonneg _
  have habs : |∫ u : ℝ in (0 : ℝ)..1, ‖F u‖| = (∫ u : ℝ in (0 : ℝ)..1, ‖F u‖) := abs_of_nonneg hnonneg
  calc
    ‖(∫ u : ℝ in (0 : ℝ)..1, F u)‖ ≤ |∫ u : ℝ in (0 : ℝ)..1, ‖F u‖| := hni
    _ = (∫ u : ℝ in (0 : ℝ)..1, ‖F u‖) := habs
    _ ≤ (∫ u : ℝ in (0 : ℝ)..1, G u) := by
      apply intervalIntegral.integral_mono_on h01
      · exact hFncont.continuousOn.intervalIntegrable
      · exact hGcont.continuousOn.intervalIntegrable
      · exact hFmono
    _ = Real.exp (-(m * t)) := by
      -- ∫ u in 0..1, c = c * (1 - 0)
      simp [G]

/-- ‖g(t)‖ ≤ ‖c‖ * exp (-(m * t)) for t > 0, where g(t) = (exp(-(b+c)t) - exp(-(bt)))/t -/
lemma g_norm_le (b c : ℂ) {m : ℝ} (hm : 0 < m)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, m ≤ ((b + (u : ℂ) * c)).re)
    {t : ℝ} (ht : 0 < t) :
    ‖(Complex.exp (-((b + c) * (t : ℂ))) - Complex.exp (-(b * (t : ℂ)))) / (t : ℂ)‖ ≤
      ‖c‖ * Real.exp (-(m * t)) := by
  have hne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have hid := seg_div_eq_integral b c (t : ℂ) hne
  calc
    ‖(Complex.exp (-((b + c) * (t : ℂ))) - Complex.exp (-(b * (t : ℂ)))) / (t : ℂ)‖
        = ‖-c * (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ))))‖ := by
          rw [hid]
    _ = ‖c‖ * ‖(∫ u : ℝ in (0 : ℝ)..1, Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ))))‖ := by
          simp [norm_mul]
    _ ≤ ‖c‖ * Real.exp (-(m * t)) := by
          exact mul_le_mul_of_nonneg_left (inner_norm_le b c hm hre ht) (norm_nonneg c)

/-- integrable on (0,∞): g with |g(t)| ≤ ‖c‖ e^{-m t} -/
lemma integrableOn_g (b c : ℂ) {m : ℝ} (hm : 0 < m)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, m ≤ ((b + (u : ℂ) * c)).re) :
    IntegrableOn (fun t : ℝ => (Complex.exp (-((b + c) * (t : ℂ))) -
        Complex.exp (-(b * (t : ℂ)))) / (t : ℂ)) (Ioi (0 : ℝ)) volume := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (Complex.exp (-((b + c) * (t : ℂ))) -
        Complex.exp (-(b * (t : ℂ)))) / (t : ℂ)) (volume.restrict (Ioi (0 : ℝ))) := by
    apply ContinuousOn.aestronglyMeasurable
    · intro t ht
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      have hnum : ContinuousAt (fun t : ℝ =>
          Complex.exp (-((b + c) * (t : ℂ))) - Complex.exp (-(b * (t : ℂ)))) t := by
        fun_prop
      have hden : ContinuousAt (fun t : ℝ => (t : ℂ)) t := by
        fun_prop
      exact (hnum.div₀ hden ht0).continuousWithinAt
    · exact measurableSet_Ioi
  have hdecay : IntegrableOn (fun t : ℝ => Real.exp (-(m * t))) (Ioi (0 : ℝ)) volume := by
    simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul] using
      integrableOn_exp_mul_Ioi (a := -m) (by linarith) (0 : ℝ)
  change Integrable (fun t : ℝ => Real.exp (-(m * t))) (volume.restrict (Ioi (0 : ℝ))) at hdecay
  have hscaled := hdecay.mul_const ‖c‖
  have hscaled' : Integrable (fun t : ℝ => ‖c‖ * Real.exp (-(m * t))) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [mul_comm] using hscaled
  exact Integrable.mono hscaled' hmeas (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hnorm : ‖‖c‖ * Real.exp (-(m * t))‖ = ‖c‖ * Real.exp (-(m * t)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg c),
        abs_of_nonneg (Real.exp_pos _).le]
    rw [hnorm]
    exact g_norm_le b c hm hre ht)

/-- chain step: interval integral of g equals -c * ∫_u (∫_t exp) -/
lemma interval_g_eq (b c : ℂ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t : ℝ in (0 : ℝ)..T, (Complex.exp (-((b + c) * (t : ℂ))) -
        Complex.exp (-(b * (t : ℂ)))) / (t : ℂ)) =
      -c * (∫ u : ℝ in (0 : ℝ)..1, (∫ t : ℝ in (0 : ℝ)..T,
        Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ))))) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  calc
    (∫ t : ℝ in (0 : ℝ)..T, (Complex.exp (-((b + c) * (t : ℂ))) -
        Complex.exp (-(b * (t : ℂ)))) / (t : ℂ))
        = (∫ t : ℝ in (0 : ℝ)..T, (-c) * (∫ u : ℝ in (0 : ℝ)..1,
            Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ))))) := by
          apply intervalIntegral.integral_congr_ae
          exact Filter.Eventually.of_forall (by
            intro t ht
            have hx : t ∈ Set.uIoc (0 : ℝ) T := ht
            have hpair : 0 < t ∧ t ≤ T := by
              simpa [Set.uIoc, hT] using hx
            have hxpos : 0 < t := hpair.1
            have hxne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hxpos
            rw [seg_div_eq_integral b c (t : ℂ) hxne])
    _ = (-c) * (∫ t : ℝ in (0 : ℝ)..T, (∫ u : ℝ in (0 : ℝ)..1,
            Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ))))) := by
          rw [intervalIntegral.integral_const_mul]
    _ = -c * (∫ u : ℝ in (0 : ℝ)..1, (∫ t : ℝ in (0 : ℝ)..T,
            Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ))))) := by
          rw [fubini_exp_T b c T hT]

/-- ∫_0^1 bounded: ‖∫_0^1 f‖ ≤ C when ‖f u‖ ≤ C on [0,1] and C ≥ 0 -/
lemma interval_norm_le_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {C : ℝ} (hC : 0 ≤ C) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (h : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖f u‖ ≤ C) :
    ‖(∫ u : ℝ in (0 : ℝ)..1, f u)‖ ≤ C := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hnonneg : 0 ≤ (∫ u : ℝ in (0 : ℝ)..1, ‖f u‖) := by
    apply intervalIntegral.integral_nonneg h01
    intro u hu
    exact norm_nonneg _
  have hni := intervalIntegral.norm_integral_le_abs_integral_norm (μ := volume) (a := (0 : ℝ)) (b := 1) (f := f)
  have hfn : ContinuousOn (fun u => ‖f u‖) (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc, h01] using hf.norm
  have hgn : ContinuousOn (fun _ : ℝ => C) (Set.uIcc (0 : ℝ) 1) := by
    fun_prop
  have hmono : (∫ u : ℝ in (0 : ℝ)..1, ‖f u‖) ≤ (∫ _ : ℝ in (0 : ℝ)..1, C) := by
    apply intervalIntegral.integral_mono_on h01
    · exact ContinuousOn.intervalIntegrable hfn
    · exact ContinuousOn.intervalIntegrable hgn
    · intro u hu
      exact h u (by simpa [Set.uIcc, h01] using hu)
  calc
    ‖(∫ u : ℝ in (0 : ℝ)..1, f u)‖ ≤ |∫ u : ℝ in (0 : ℝ)..1, ‖f u‖| := hni
    _ = (∫ u : ℝ in (0 : ℝ)..1, ‖f u‖) := abs_of_nonneg hnonneg
    _ ≤ (∫ _ : ℝ in (0 : ℝ)..1, C) := hmono
    _ = C := by simp

/-- inner t-integral on [0,T] evaluated -/
lemma inner_interval_T (b c : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ u ∈ Set.Icc (0 : ℝ) 1, (b + (u : ℂ) * c) ∈ Complex.slitPlane) :
    (∫ u : ℝ in (0 : ℝ)..1, (∫ t : ℝ in (0 : ℝ)..T,
        Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ))))) =
      (∫ u : ℝ in (0 : ℝ)..1, (1 - Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ)))) *
        (b + (u : ℂ) * c)⁻¹) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall (by
    intro u hu
    have hu' : u ∈ Set.Ioc (0 : ℝ) 1 := by simpa [Set.uIoc, h01] using hu
    have huseg : u ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hu'.1, hu'.2⟩
    have hw : (b + (u : ℂ) * c) ≠ 0 := Complex.slitPlane_ne_zero (hseg u huseg)
    rw [integral_exp_neg_mul_interval (w := b + (u : ℂ) * c) hw T hT])

/-- norm of (Z u)⁻¹ bounded by m⁻¹ -/
lemma inv_seg_norm_le (b c : ℂ) {m : ℝ} (hm : 0 < m)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, m ≤ ((b + (u : ℂ) * c)).re)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ‖(b + (u : ℂ) * c)⁻¹‖ ≤ m⁻¹ := by
  have hzu : m ≤ ‖b + (u : ℂ) * c‖ := le_trans (hre u hu) (Complex.re_le_norm _)
  have hzpos : 0 < ‖b + (u : ℂ) * c‖ := lt_of_lt_of_le hm hzu
  calc
    ‖(b + (u : ℂ) * c)⁻¹‖ = ‖b + (u : ℂ) * c‖⁻¹ := by rw [norm_inv]
    _ ≤ m⁻¹ := by
      simpa [one_div] using (one_div_le_one_div_of_le hm hzu)

/-- pointwise bound for the correction integrand -/
lemma corr_integrand_le (b c : ℂ) {m : ℝ} (hm : 0 < m)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, m ≤ ((b + (u : ℂ) * c)).re)
    {T : ℝ} (hT : 0 ≤ T) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ‖Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) * (b + (u : ℂ) * c)⁻¹‖ ≤
      Real.exp (-(m * T)) * m⁻¹ := by
  have hzu := hre u hu
  have hle1 : Real.exp (-(((b + (u : ℂ) * c)).re * T)) ≤ Real.exp (-(m * T)) := by
    apply Real.exp_le_exp.2
    have hlt : m * T ≤ ((b + (u : ℂ) * c)).re * T := mul_le_mul_of_nonneg_right hzu hT
    exact neg_le_neg hlt
  have hinv : ‖(b + (u : ℂ) * c)⁻¹‖ ≤ m⁻¹ := inv_seg_norm_le b c hm hre hu
  calc
    ‖Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) * (b + (u : ℂ) * c)⁻¹‖
        = ‖Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ)))‖ * ‖(b + (u : ℂ) * c)⁻¹‖ := by
          rw [norm_mul]
    _ = Real.exp (-(((b + (u : ℂ) * c)).re * T)) * ‖(b + (u : ℂ) * c)⁻¹‖ := by
          rw [norm_exp_neg_ofReal_mul]
    _ ≤ Real.exp (-(m * T)) * m⁻¹ := by
          exact mul_le_mul hle1 hinv (norm_nonneg _) (Real.exp_pos _).le

/-- (b + u*c)⁻¹ is continuous on [0,1] -/
lemma inv_seg_continuousOn (b c : ℂ)
    (hseg : ∀ u ∈ Set.Icc (0 : ℝ) 1, (b + (u : ℂ) * c) ∈ Complex.slitPlane) :
    ContinuousOn (fun u : ℝ => (b + (u : ℂ) * c)⁻¹) (Set.Icc (0 : ℝ) 1) := by
  intro u hu
  have hZc : ContinuousWithinAt (fun u : ℝ => b + (u : ℂ) * c) (Set.Icc (0 : ℝ) 1) u := by
    fun_prop
  have hZnz : b + (u : ℂ) * c ≠ 0 := Complex.slitPlane_ne_zero (hseg u hu)
  have hcz : ContinuousAt (fun w : ℂ => w⁻¹) (b + (u : ℂ) * c) := by
    exact ContinuousAt.inv₀ continuousAt_id hZnz
  exact ContinuousAt.comp_continuousWithinAt hcz hZc

/-- exp(-(Z u · (T:ℂ)))·(Z u)⁻¹ is continuous on [0,1] -/
lemma exp_mul_inv_seg_continuousOn (b c : ℂ) (T : ℝ)
    (hseg : ∀ u ∈ Set.Icc (0 : ℝ) 1, (b + (u : ℂ) * c) ∈ Complex.slitPlane) :
    ContinuousOn (fun u : ℝ => Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) *
      (b + (u : ℂ) * c)⁻¹) (Set.Icc (0 : ℝ) 1) := by
  intro u hu
  have hnum : ContinuousWithinAt (fun u : ℝ =>
      Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ)))) (Set.Icc (0 : ℝ) 1) u := by
    fun_prop
  exact hnum.mul (inv_seg_continuousOn b c hseg u hu)

/-- correction term tends to 0 -/
lemma corr_tendsto_zero (b c : ℂ) {m : ℝ} (hm : 0 < m)
    (hseg : ∀ u ∈ Set.Icc (0 : ℝ) 1, (b + (u : ℂ) * c) ∈ Complex.slitPlane)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, m ≤ ((b + (u : ℂ) * c)).re) :
    Tendsto (fun T : ℝ => (∫ u : ℝ in (0 : ℝ)..1,
        Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) * (b + (u : ℂ) * c)⁻¹))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let g : ℝ → ℝ := fun T => Real.exp (-(m * T)) * m⁻¹
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hE0 : Tendsto (fun T : ℝ => Real.exp (-(m * T))) atTop (𝓝 0) := by
      have harg : Tendsto (fun T : ℝ => (-m) * T) atTop atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg (by linarith : (-m) < 0) tendsto_id
      have hcomp : Tendsto (fun T : ℝ => Real.exp ((-m) * T)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp harg
      exact Tendsto.congr' (Filter.Eventually.of_forall (by intro T; congr 1; ring)) hcomp
    unfold g
    simpa using hE0.mul tendsto_const_nhds
  have hbnd : ∀ᶠ T : ℝ in atTop, ‖(∫ u : ℝ in (0 : ℝ)..1,
      Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) * (b + (u : ℂ) * c)⁻¹)‖ ≤ g T := by
    refine eventually_atTop.2 ⟨0, ?_⟩
    intro T hT
    have hφc : ContinuousOn (fun u : ℝ =>
        Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) * (b + (u : ℂ) * c)⁻¹)
        (Set.Icc (0 : ℝ) 1) := exp_mul_inv_seg_continuousOn b c T hseg
    have hC : 0 ≤ Real.exp (-(m * T)) * m⁻¹ := mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr hm.le)
    have hb : ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) * (b + (u : ℂ) * c)⁻¹‖ ≤
          Real.exp (-(m * T)) * m⁻¹ := by
      intro u hu
      exact corr_integrand_le b c hm hre hT hu
    have hmain := interval_norm_le_of_le (f := fun u : ℝ =>
      Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) * (b + (u : ℂ) * c)⁻¹) hC hφc hb
    simpa [g] using hmain
  have hpos : ∀ᶠ T : ℝ in atTop, 0 ≤ ‖(∫ u : ℝ in (0 : ℝ)..1,
      Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) * (b + (u : ℂ) * c)⁻¹)‖ := by
    exact Filter.Eventually.of_forall (fun T => norm_nonneg _)
  simpa [g] using (squeeze_zero' hpos hbnd hg0)

/-- ∫ (1 - e^{-Z(u)T})·Z(u)⁻¹ → ∫ Z(u)⁻¹ as T → ∞ -/
lemma D_tendsto_E (b c : ℂ) {m : ℝ} (hm : 0 < m)
    (hseg : ∀ u ∈ Set.Icc (0 : ℝ) 1, (b + (u : ℂ) * c) ∈ Complex.slitPlane)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, m ≤ ((b + (u : ℂ) * c)).re) :
    Tendsto (fun T : ℝ => (∫ u : ℝ in (0 : ℝ)..1,
        (1 - Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ)))) * (b + (u : ℂ) * c)⁻¹))
      atTop (𝓝 (∫ u : ℝ in (0 : ℝ)..1, (b + (u : ℂ) * c)⁻¹)) := by
  let F : ℂ := ∫ u : ℝ in (0 : ℝ)..1, (b + (u : ℂ) * c)⁻¹
  let corr : ℝ → ℂ := fun T => (∫ u : ℝ in (0 : ℝ)..1,
    Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) * (b + (u : ℂ) * c)⁻¹)
  have hcorr0 : Tendsto corr atTop (𝓝 0) := by
    simpa [corr] using corr_tendsto_zero b c hm hseg hre
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hD : (fun T : ℝ => (∫ u : ℝ in (0 : ℝ)..1,
        (1 - Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ)))) * (b + (u : ℂ) * c)⁻¹)) =ᶠ[atTop]
      fun T => F - corr T := by
    exact Filter.Eventually.of_forall (by
      intro T
      change (∫ u : ℝ in (0 : ℝ)..1,
        (1 - Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ)))) * (b + (u : ℂ) * c)⁻¹) = F - corr T
      have h1 : IntervalIntegrable (fun u : ℝ => (b + (u : ℂ) * c)⁻¹) volume (0 : ℝ) 1 := by
        apply ContinuousOn.intervalIntegrable
        simpa [uIcc_of_le h01] using inv_seg_continuousOn b c hseg
      have h2 : IntervalIntegrable (fun u : ℝ =>
          Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) * (b + (u : ℂ) * c)⁻¹) volume (0 : ℝ) 1 := by
        apply ContinuousOn.intervalIntegrable
        simpa [uIcc_of_le h01] using exp_mul_inv_seg_continuousOn b c T hseg
      have hsub := intervalIntegral.integral_sub (μ := volume) (a := (0 : ℝ)) (b := 1)
        (f := fun u : ℝ => (b + (u : ℂ) * c)⁻¹)
        (g := fun u : ℝ => Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) * (b + (u : ℂ) * c)⁻¹) h1 h2
      have hmul : (∫ u : ℝ in (0 : ℝ)..1,
            (1 - Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ)))) * (b + (u : ℂ) * c)⁻¹) =
          (∫ u : ℝ in (0 : ℝ)..1,
            (b + (u : ℂ) * c)⁻¹ - Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ))) *
              (b + (u : ℂ) * c)⁻¹) := by
        apply intervalIntegral.integral_congr
        intro u hu
        ring
      rw [hmul, hsub])
  have hlimit : Tendsto (fun T : ℝ => F - corr T) atTop (𝓝 (F - 0)) :=
    tendsto_const_nhds.sub hcorr0
  exact Tendsto.congr' hD.symm (by simpa using hlimit)

/-- main Frullani identity: ∫ (e^{-(b+c)t} - e^{-bt})/t = log b - log (b+c) for endpoints in the right half plane -/
lemma frullani_exp_main (b c : ℂ) (hb : 0 < b.re) (hbc : 0 < (b + c).re) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), (Complex.exp (-((b + c) * (t : ℂ))) -
        Complex.exp (-(b * (t : ℂ)))) / (t : ℂ)) =
      Complex.log b - Complex.log (b + c) := by
  let m : ℝ := min b.re (b + c).re
  have hm : 0 < m := lt_min hb hbc
  have hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, m ≤ ((b + (u : ℂ) * c)).re :=
    fun u hu => re_seg_lower b c u hu
  have hseg : ∀ u ∈ Set.Icc (0 : ℝ) 1, (b + (u : ℂ) * c) ∈ Complex.slitPlane :=
    slitPlane_of_m_re hm hre
  let g : ℝ → ℂ := fun t => (Complex.exp (-((b + c) * (t : ℂ))) -
      Complex.exp (-(b * (t : ℂ)))) / (t : ℂ)
  let A : ℝ → ℂ := fun T => (∫ t : ℝ in (0 : ℝ)..T, g t)
  let DT : ℝ → ℂ := fun T => (∫ u : ℝ in (0 : ℝ)..1,
    (1 - Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ)))) * (b + (u : ℂ) * c)⁻¹)
  let E : ℂ := (∫ u : ℝ in (0 : ℝ)..1, (b + (u : ℂ) * c)⁻¹)
  have hA_lim : Tendsto A atTop (𝓝 (∫ t : ℝ in Set.Ioi (0 : ℝ), g t)) := by
    unfold A g
    exact intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ)) (integrableOn_g b c hm hre) tendsto_id
  have hA_eq : A =ᶠ[atTop] (fun T : ℝ => (-c) * DT T) := by
    refine eventually_atTop.2 ⟨0, ?_⟩
    intro T hT
    calc
      A T = (-c) * (∫ u : ℝ in (0 : ℝ)..1, (∫ t : ℝ in (0 : ℝ)..T,
            Complex.exp (-((b + (u : ℂ) * c) * (t : ℂ))))) := by
              exact interval_g_eq b c T hT
      _ = (-c) * (∫ u : ℝ in (0 : ℝ)..1,
            (1 - Complex.exp (-((b + (u : ℂ) * c) * (T : ℂ)))) * (b + (u : ℂ) * c)⁻¹) := by
              exact congrArg (fun x : ℂ => (-c) * x) (inner_interval_T b c hT hseg)
      _ = (-c) * DT T := by
              simp [DT]
  have hDlim : Tendsto DT atTop (𝓝 E) := by
    simpa [DT, E] using D_tendsto_E b c hm hseg hre
  have hDlim' : Tendsto (fun T : ℝ => (-c) * DT T) atTop (𝓝 ((-c) * E)) :=
    Filter.Tendsto.const_mul (-c) hDlim
  have hA_lim2 : Tendsto A atTop (𝓝 ((-c) * E)) := by
    exact Tendsto.congr' hA_eq.symm hDlim'
  have hval : (∫ t : ℝ in Set.Ioi (0 : ℝ), g t) = (-c) * E :=
    tendsto_nhds_unique hA_lim hA_lim2
  have hlogE : c * E = Complex.log (b + c) - Complex.log b := by
    simpa [E] using integral_inv_seg_log b c hseg
  calc
    (∫ t : ℝ in Set.Ioi (0 : ℝ), (Complex.exp (-((b + c) * (t : ℂ))) -
        Complex.exp (-(b * (t : ℂ)))) / (t : ℂ)) = (∫ t : ℝ in Set.Ioi (0 : ℝ), g t) := by
          simp [g]
    _ = (-c) * E := hval
    _ = Complex.log b - Complex.log (b + c) := by
          have hneg : (-c) * E = -(c * E) := by ring
          rw [hneg, hlogE]
          ring

/-- **Frullani's integral for the complex logarithm** -/
theorem complex_log (z : ℂ) (hz : 0 < z.re) (a : ℝ) (ha : 0 < a) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), (Complex.exp (-(z * (t : ℂ))) -
        Complex.exp (-((a : ℂ) * (t : ℂ)))) / (t : ℂ)) =
      Complex.log (a : ℂ) - Complex.log z := by
  let b : ℂ := (a : ℂ)
  let c : ℂ := z - b
  have hb : b = (a : ℂ) := rfl
  have hbpc : b + c = z := by simp [b, c]
  have hb0 : 0 < b.re := by
    rw [hb, Complex.ofReal_re]
    exact ha
  have hbc0 : 0 < (b + c).re := by
    rw [hbpc]
    exact hz
  have hmain := frullani_exp_main b c hb0 hbc0
  calc
    (∫ t : ℝ in Set.Ioi (0 : ℝ), (Complex.exp (-(z * (t : ℂ))) -
        Complex.exp (-((a : ℂ) * (t : ℂ)))) / (t : ℂ))
        = (∫ t : ℝ in Set.Ioi (0 : ℝ), (Complex.exp (-((b + c) * (t : ℂ))) -
            Complex.exp (-(b * (t : ℂ)))) / (t : ℂ)) := by
          congr 1
          funext t
          congr 1 <;> rw [← hb, ← hbpc] <;> ring
    _ = Complex.log b - Complex.log (b + c) := hmain
    _ = Complex.log (a : ℂ) - Complex.log z := by rw [hb, hbpc]


end Commons.Analysis.SpecialFunctions.Frullani