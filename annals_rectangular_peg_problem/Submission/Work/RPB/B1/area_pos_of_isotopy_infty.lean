import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B1.AreaDefs
import Submission.Work.RPB.B1.AreaPosDefs
import Submission.Work.RPB.B1.windInt_continuousOn_and_zero_far
import Submission.Work.RPB.B1.windInt_locallyConstant
import Submission.Work.RPB.B1.windInt_exists_ne_zero
import Submission.Work.RPB.B1.jordan_separation_smooth
import Submission.Work.RPB.B1.volume_range_eq_zero
import Submission.Work.RPB.B1.areaFormula

/-!
# B1: the signed area stays positive along a smooth isotopy of embedded curves

`Work.RPB.B1.area_pos_of_isotopy_infty`: for a **smooth** (`ContDiff ℝ ∞`) isotopy `c` of embedded
`2π`-periodic closed plane curves starting at the counterclockwise unit circle, the signed area
`∫_0^{2π} ω_ℂ (c τ t) (∂_t c τ t)` is positive for every `τ ∈ [0,1]`.

The route is the classical flux computation of the winding number (the same one used by the sibling
`Work.RPB.B1.area_pos_of_isotopy`, which assumes analyticity `ContDiff ℝ ω`; the hypotheses here are
smoothness `ContDiff ℝ ∞`, so only the `C¹`-level pieces of that development are reusable):

* the signed area functional `areaInt` and the winding integral
  `windInt u q = (1/2π) ∮ Im (u'/(u - q))` (`Submission.Work.RPB.B1.AreaPosDefs`);
* `windInt u ·` is continuous off the curve and vanishes far away
  (`windInt_continuousOn`, `windInt_eq_zero_of_norm_lt`, both `C¹`-level);
* the area formula `(1/2) ∮ ω_ℂ (u, u') = ∫_ℂ windInt u` (delegated as
  `Submission.Work.RPB.B1.areaFormula`);
* Jordan separation for a smooth embedded curve
  (`Submission.Work.RPB.B1.jordan_separation_smooth`), the local constancy of `windInt` off the curve
  (`Submission.Work.RPB.B1.windInt_locallyConstant`) and the existence of a point of non-zero winding
  number (`Submission.Work.RPB.B1.windInt_exists_ne_zero`) identify `∫_ℂ windInt u` with
  `k₀ · volume (interior)`, `k₀ ≠ 0`;
* the curve is a Lebesgue null set (`Submission.Work.RPB.B1.volume_range_eq_zero`).

The signed area is continuous in `τ` and equals `2π > 0` at `τ = 0`, so it is positive throughout.
-/

open scoped ContDiff Interval Topology
open MeasureTheory

set_option autoImplicit false

namespace Work.RPB.B1

noncomputable section

/-! ## The parameter derivative of a two-variable function -/

lemma deriv_pair_second (F : ℝ × ℝ → ℂ) (hF : Differentiable ℝ F) (τ t : ℝ) :
    deriv (fun s => F (τ, s)) t = fderiv ℝ F (τ, t) (0, 1) := by
  rw [show (fun s => F (τ, s)) = F ∘ (fun s : ℝ => (τ, s)) from rfl]
  rw [HasDerivAt.deriv ((hF (τ, t)).hasFDerivAt.comp_hasDerivAt t
    (by simpa using (hasDerivAt_const (x := t) (c := τ)).prodMk (hasDerivAt_id t)))]

/-- The partial derivative in the curve parameter of a jointly smooth family is continuous. -/
lemma continuous_deriv_slice (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2)) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s => c p.1 s) p.2) := by
  have hd : Differentiable ℝ (fun z : ℝ × ℝ => c z.1 z.2) := hc.differentiable (by simp)
  have hfun : (fun p : ℝ × ℝ => deriv (fun s => c p.1 s) p.2)
      = fun p : ℝ × ℝ => fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) p (0, 1) := by
    funext p
    exact deriv_pair_second _ hd p.1 p.2
  rw [hfun]
  exact (hc.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The signed-area integrand of a jointly smooth family is continuous. -/
lemma continuous_integrand (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2)) :
    Continuous (fun p : ℝ × ℝ => Work.RPV.ωC (c p.1 p.2) (deriv (fun s => c p.1 s) p.2)) := by
  have h1 : Continuous (fun p : ℝ × ℝ => ((starRingEnd ℂ) (c p.1 p.2))) :=
    continuous_star.comp hc.continuous
  have h2 : Continuous (fun p : ℝ × ℝ => deriv (fun s => c p.1 s) p.2) :=
    continuous_deriv_slice c hc
  have h3 : Continuous (fun p : ℝ × ℝ =>
      ((starRingEnd ℂ) (c p.1 p.2) * deriv (fun s => c p.1 s) p.2).im) :=
    Complex.continuous_im.comp (h1.mul h2)
  simpa [Work.RPV.ωC] using h3

/-- **The signed area is continuous in the isotopy parameter.** -/
theorem continuous_areaInt (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2)) :
    Continuous (fun τ => areaInt (c τ)) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_integrand c hc) 0 (2 * Real.pi)

/-! ## The value at `τ = 0` -/

lemma omegaC_unit_circle (t : ℝ) :
    Work.RPV.ωC (Complex.exp ((t : ℂ) * Complex.I))
      (Complex.I * Complex.exp ((t : ℂ) * Complex.I)) = 1 := by
  rw [Work.RPV.ωC, ← Complex.exp_conj]
  have h1 : (starRingEnd ℂ) ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by simp
  have h2 : Complex.exp (-((t : ℂ) * Complex.I)) *
      (Complex.I * Complex.exp ((t : ℂ) * Complex.I)) = Complex.I := by
    have h3 : Complex.exp (-((t : ℂ) * Complex.I)) *
        Complex.exp ((t : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    calc Complex.exp (-((t : ℂ) * Complex.I)) *
          (Complex.I * Complex.exp ((t : ℂ) * Complex.I))
        = Complex.I * (Complex.exp (-((t : ℂ) * Complex.I)) *
            Complex.exp ((t : ℂ) * Complex.I)) := by ring
      _ = Complex.I * 1 := by rw [h3]
      _ = Complex.I := by ring
  rw [h1, h2]
  simp

lemma deriv_unit_circle (t : ℝ) :
    deriv (fun s : ℝ => Complex.exp (s * Complex.I)) t
      = Complex.I * Complex.exp (t * Complex.I) := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) ((1 : ℂ) * Complex.I) t := by
    simpa using (hasDerivAt_id (t : ℝ)).ofReal_comp.mul_const Complex.I
  have h2 := (Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp t h1
  rw [show (fun s : ℝ => Complex.exp (s * Complex.I))
      = Complex.exp ∘ (fun s : ℝ => (s : ℂ) * Complex.I) from rfl]
  rw [HasDerivAt.deriv h2]
  ring

/-- **The signed area of the starting curve is `2π`.** -/
theorem areaInt_zero (c : ℝ → ℝ → ℂ)
    (hstart : ∀ t, c 0 t = Complex.exp (t * Complex.I)) :
    areaInt (c 0) = 2 * Real.pi := by
  have hfun : c 0 = fun s : ℝ => Complex.exp (s * Complex.I) := funext hstart
  have h : ∀ t : ℝ, Work.RPV.ωC (c 0 t) (deriv (c 0) t) = 1 := by
    intro t
    rw [hfun, deriv_unit_circle, omegaC_unit_circle]
  rw [areaInt_def]
  simp [h]

/-! ## Bounds for periodic curves -/

/-- A `2π`-periodic continuous curve is bounded. -/
lemma exists_bound_of_periodic (u : ℝ → ℂ) (hu : Continuous u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t) : ∃ M : ℝ, ∀ t, ‖u t‖ ≤ M := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    ((isCompact_Icc.image_of_continuousOn hu.continuousOn)).isBounded
  refine ⟨M, fun t => ?_⟩
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  set k : ℤ := ⌊t / (2 * Real.pi)⌋ with hk
  set s : ℝ := t - (k : ℝ) * (2 * Real.pi) with hs
  have hs_mem : s ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    constructor
    · have h := Int.floor_le (t / (2 * Real.pi))
      have h' : ((k : ℝ)) * (2 * Real.pi) ≤ t := by
        rw [hk]
        exact (le_div_iff₀ h2pi).mp h
      rw [hs]; linarith
    · have h := Int.lt_floor_add_one (t / (2 * Real.pi))
      have h' : t < ((k : ℝ) + 1) * (2 * Real.pi) := by
        rw [hk]
        rw [div_lt_iff₀ h2pi] at h
        linarith
      rw [hs]; linarith
  have hper' : Function.Periodic u (2 * Real.pi) := hper
  have hshift := hper'.zsmul k s
  have hst : s + (k : ℝ) * (2 * Real.pi) = t := by rw [hs]; ring
  have hut : u t = u s := by
    rw [← hst]
    simpa [zsmul_eq_mul] using hshift
  rw [hut]
  exact hM (u s) ⟨s, hs_mem, rfl⟩

/-! ## Constancy of the winding integral on preconnected sets -/

/-- A function which is locally constant off the curve is constant on a preconnected set avoiding
the curve. -/
lemma windInt_eq_of_preconnected_of_local (u : ℝ → ℂ)
    (hloc : ∀ q ∈ (Set.range u)ᶜ, ∃ δ > 0,
      ∀ q' ∈ (Set.range u)ᶜ, dist q' q < δ → windInt u q' = windInt u q)
    {C : Set ℂ} (hC : C ⊆ (Set.range u)ᶜ) (hconn : IsPreconnected C) {q q' : ℂ}
    (hq : q ∈ C) (hq' : q' ∈ C) : windInt u q = windInt u q' := by
  let F : C → ℝ := fun x => windInt u x.1
  have hloc' : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨r, hr, hbr⟩ := hloc x.1 (hC x.2)
    have hU : {y : C | dist (y : ℂ) x.1 < r} ∈ 𝓝 x :=
      (continuous_subtype_val.continuousAt).preimage_mem_nhds (Metric.ball_mem_nhds _ hr)
    filter_upwards [hU] with y hy
    exact hbr y.1 (hC y.2) hy
  have hpc : PreconnectedSpace C := Subtype.preconnectedSpace hconn
  exact IsLocallyConstant.apply_eq_of_preconnectedSpace hloc' ⟨q, hq⟩ ⟨q', hq'⟩

/-! ## The topological core: the signed area of an embedded curve is non-zero -/

/-- **The signed area of a smooth embedded closed curve does not vanish**, given the five
ingredients of the flux route: Jordan separation, local constancy of the winding integral off the
curve, the existence of a point of non-zero winding number, the fact that the curve is a null set,
and the area formula. -/
lemma areaInt_ne_zero_of_pieces (u : ℝ → ℂ)
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t)
    (hsep : ∃ ins out : Set ℂ,
      IsOpen ins ∧ IsOpen out ∧ IsPreconnected ins ∧ IsPreconnected out ∧
        Bornology.IsBounded ins ∧ ¬ Bornology.IsBounded out ∧ ins.Nonempty ∧
          (Set.range u)ᶜ = ins ∪ out ∧ Disjoint ins out)
    (hloc : ∀ q ∈ (Set.range u)ᶜ, ∃ δ > 0,
      ∀ q' ∈ (Set.range u)ᶜ, dist q' q < δ → windInt u q' = windInt u q)
    (hex : ∃ q ∈ (Set.range u)ᶜ, windInt u q ≠ 0)
    (hnull : volume (Set.range u) = 0)
    (harea : Integrable (windInt u) volume → (1 / 2) * areaInt u = ∫ q, windInt u q) :
    areaInt u ≠ 0 := by
  classical
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by simp)
  obtain ⟨ins, out, hinsopen, _houtopen, hinsconn, houtconn, hinsbdd, houtunbdd, hinsne,
    hcover, hdisj⟩ := hsep
  have hins_sub : ins ⊆ (Set.range u)ᶜ := by rw [hcover]; exact Set.subset_union_left
  have hout_sub : out ⊆ (Set.range u)ᶜ := by rw [hcover]; exact Set.subset_union_right
  obtain ⟨q₀, hq₀, hq₀ne⟩ := hex
  obtain ⟨M, hM⟩ := exists_bound_of_periodic u hu.continuous hper
  -- a point of `out` far outside the disc of radius `M`
  obtain ⟨q₁, hq₁, hq₁far⟩ : ∃ q ∈ out, M < ‖q‖ := by
    by_contra h
    push_neg at h
    exact houtunbdd (isBounded_iff_forall_norm_le.mpr ⟨M, fun x hx => h x hx⟩)
  have hfar := windInt_eq_zero_of_norm_lt u hu1 hper hM hq₁far
  have hout_zero : ∀ q ∈ out, windInt u q = 0 := by
    intro q hq
    rw [windInt_eq_of_preconnected_of_local u hloc hout_sub houtconn hq hq₁, hfar]
  have hq₀_ins : q₀ ∈ ins := by
    have h : q₀ ∈ ins ∪ out := hcover ▸ hq₀
    rcases h with h | h
    · exact h
    · exact absurd (hout_zero q₀ h) hq₀ne
  have hins_const : ∀ q ∈ ins, windInt u q = windInt u q₀ :=
    fun q hq => windInt_eq_of_preconnected_of_local u hloc hins_sub hinsconn hq hq₀_ins
  have hae : windInt u =ᵐ[volume] (fun q => if q ∈ ins then windInt u q₀ else 0) := by
    filter_upwards [(MeasureTheory.compl_mem_ae_iff).mpr hnull] with q hq
    have hq' : q ∈ ins ∪ out := hcover ▸ hq
    rcases hq' with h | h
    · simp only [hins_const q h, h, if_true]
    · have hnotin : q ∉ ins := fun h' => Set.disjoint_left.mp hdisj h' h
      simp only [hout_zero q h, hnotin, if_false]
  have hInt : (∫ q, windInt u q) = windInt u q₀ * (volume ins).toReal := by
    rw [MeasureTheory.integral_congr_ae hae]
    rw [show (fun q => if q ∈ ins then windInt u q₀ else 0)
        = ins.indicator (fun _ => windInt u q₀) from rfl]
    rw [MeasureTheory.integral_indicator_const (windInt u q₀) hinsopen.measurableSet,
      MeasureTheory.Measure.real_def, smul_eq_mul]
    ring
  have hvol_pos : (0 : ℝ) < (volume ins).toReal := by
    have h1 : 0 < volume ins := hinsopen.measure_pos volume hinsne
    have h2 : volume ins ≠ ⊤ := (hinsbdd.measure_lt_top).ne
    exact ENNReal.toReal_pos h1.ne' h2
  have hintegral_ne : (∫ q, windInt u q) ≠ 0 := by
    rw [hInt]
    exact mul_ne_zero hq₀ne hvol_pos.ne'
  -- integrability of the winding integral
  have hint : Integrable (windInt u) volume := by
    have hbase : Integrable (ins.indicator (fun _ => windInt u q₀)) volume :=
      (MeasureTheory.integrable_indicator_iff hinsopen.measurableSet).mpr
        (MeasureTheory.integrableOn_const (s := ins) (μ := volume) (C := windInt u q₀)
          hinsbdd.measure_lt_top.ne)
    exact hbase.congr hae.symm
  intro hzero
  exact hintegral_ne (by rw [← harea hint, hzero, mul_zero])

/-! ## Positivity from continuity and non-vanishing -/

/-- A continuous function on `[0,1]` which is non-zero there and positive at `0` is positive
throughout. -/
lemma pos_of_continuous_ne_zero {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : f 0 = 2 * Real.pi) (hne : ∀ τ ∈ Set.Icc (0 : ℝ) 1, f τ ≠ 0) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, 0 < f τ := by
  intro τ hτ
  by_contra hcon
  push_neg at hcon
  have hneg : f τ < 0 := lt_of_le_of_ne hcon (hne τ hτ)
  rcases eq_or_lt_of_le hτ.1 with hτz | hτpos
  · rw [← hτz, h0] at hneg
    linarith [Real.pi_pos]
  · have hmem : (0 : ℝ) ∈ Set.Icc (f τ) (f 0) := by
      rw [h0]
      exact ⟨le_of_lt hneg, by linarith [Real.pi_pos]⟩
    obtain ⟨s, hs, hsv⟩ := (intermediate_value_Icc' hτpos.le hf.continuousOn) hmem
    exact hne s ⟨hs.1, le_trans hs.2 hτ.2⟩ hsv

/-! ## The target theorem -/

theorem area_pos_of_isotopy_infty (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2))
    (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t)
    (hinj : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t t', c τ t = c τ t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m)
    (himm : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, deriv (c τ) t ≠ 0)
    (hstart : ∀ t, c 0 t = Complex.exp (t * Complex.I)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      0 < ∫ t in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC (c τ t) (deriv (c τ) t) := by
  have hcont : Continuous (fun τ => areaInt (c τ)) := continuous_areaInt c hc
  have h0 : areaInt (c 0) = 2 * Real.pi := areaInt_zero c hstart
  refine pos_of_continuous_ne_zero hcont h0 (fun τ hτ => ?_)
  have hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c τ) :=
    hc.comp (contDiff_const.prodMk contDiff_id)
  have hu1 : ContDiff ℝ 1 (c τ) := hu.of_le (by simp)
  exact areaInt_ne_zero_of_pieces (c τ) hu (hper τ)
    (jordan_separation_smooth (c τ) hu (hper τ) (hinj τ hτ) (himm τ hτ))
    (fun q hq => windInt_locallyConstant (c τ) hu1 (hper τ) hq)
    (windInt_exists_ne_zero (c τ) hu (hper τ) (hinj τ hτ) (himm τ hτ))
    (volume_range_eq_zero (c τ) hu1 (hper τ))
    (areaFormula (c τ) hu1 (hper τ))

end

end Work.RPB.B1
