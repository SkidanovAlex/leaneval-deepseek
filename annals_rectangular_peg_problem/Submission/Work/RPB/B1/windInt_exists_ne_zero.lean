import Mathlib
import Submission.Work.RPB.B1.AreaPosDefs
import Submission.Work.RPB.B1.WindLiftDefs
import Submission.Work.RPB.B1.exp_integral_of_hasDerivAt
import Submission.Work.RPB.Port.Drive.SeparationBase
import Submission.Work.RPB.Port.Drive.exists_winding_ne_zero
import Submission.Work.RPB.B1.windDir_hasDerivAt
import Submission.Work.RPB.B1.exp_I_eq_one_const

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# A smooth embedded closed plane curve has a point of non-zero winding number

`Work.RPB.B1.windInt_exists_ne_zero`: for a `C^∞`, `2π`-periodic curve `u : ℝ → ℂ` which is
injective up to the period and has nowhere vanishing derivative, there is a point `q` off the
image of `u` with `windInt u q ≠ 0`.

The proof transports `u` to the ported Jordan–curve chapter: `t ↦ u (2π t)` descends to a
continuous injective `C¹` map `γ : ℝ/ℤ → ℝ × ℝ`, to which
`Work.RPB.Port.Drive.exists_winding_ne_zero` applies, producing a point `p` with non-zero
(doubled-direction) *degree* `winding γ p`.  A lift `Φ` of `dirZ (u - cpx p)` with non-zero
monodromy is read off from the degree, and the log-derivative form of the argument principle
(`Work.RPB.B1.logDeriv_integral_pi_monodromy`) relates that monodromy to the integral defining
`windInt`.
-/

namespace Work.RPB.B1

open scoped ContDiff Interval
open Work.RPB.Port.Drive

noncomputable section

/-! ## Transporting a periodic complex curve to the quotient `ℝ/ℤ` -/

/-- The rescaling `x ↦ u (2π x)` of a `2π`-periodic curve, which is `1`-periodic. -/
def uScaled (u : ℝ → ℂ) (x : ℝ) : ℂ := u (2 * Real.pi * x)

lemma uScaled_periodic (u : ℝ → ℂ) (hper : ∀ t, u (t + 2 * Real.pi) = u t) :
    Function.Periodic (uScaled u) 1 := by
  intro x
  show u (2 * Real.pi * (x + 1)) = u (2 * Real.pi * x)
  rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring]
  exact hper (2 * Real.pi * x)

/-- The descent of a `2π`-periodic plane curve to a map on `ℝ/ℤ = UnitAddCircle`. -/
def gammaOf (u : ℝ → ℂ) (hper : ∀ t, u (t + 2 * Real.pi) = u t) : UnitAddCircle → ℝ × ℝ :=
  fun s => (((uScaled_periodic u hper).lift s).re, ((uScaled_periodic u hper).lift s).im)

lemma gammaOf_coe (u : ℝ → ℂ) (hper : ∀ t, u (t + 2 * Real.pi) = u t) (x : ℝ) :
    gammaOf u hper (x : UnitAddCircle) =
      ((u (2 * Real.pi * x)).re, (u (2 * Real.pi * x)).im) := by
  simp only [gammaOf, uScaled, Function.Periodic.lift_coe]

lemma continuous_gammaOf (u : ℝ → ℂ) (hper : ∀ t, u (t + 2 * Real.pi) = u t)
    (hu : Continuous u) : Continuous (gammaOf u hper) := by
  rw [Topology.IsQuotientMap.continuous_iff (IsOpenQuotientMap.isQuotientMap
    (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ))))]
  rw [show (gammaOf u hper ∘ QuotientAddGroup.mk)
      = (fun x : ℝ => ((u (2 * Real.pi * x)).re, (u (2 * Real.pi * x)).im)) from
    funext (fun x => gammaOf_coe u hper x)]
  exact (Complex.continuous_re.comp (hu.comp (continuous_const.mul continuous_id))).prodMk
    (Complex.continuous_im.comp (hu.comp (continuous_const.mul continuous_id)))

lemma contDiff_gammaOf (u : ℝ → ℂ) (hper : ∀ t, u (t + 2 * Real.pi) = u t)
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) :
    ContDiff ℝ (1 : ℕ∞) (fun t : ℝ => gammaOf u hper (t : UnitAddCircle)) := by
  rw [show (fun t : ℝ => gammaOf u hper (t : UnitAddCircle))
      = (fun t : ℝ => ((u (2 * Real.pi * t)).re, (u (2 * Real.pi * t)).im)) from
    funext (fun t => gammaOf_coe u hper t)]
  have hF : ContDiff ℝ (1 : ℕ∞) (fun t : ℝ => u (2 * Real.pi * t)) :=
    (hu.of_le (WithTop.coe_le_coe.mpr le_top)).comp (contDiff_const.mul contDiff_id)
  rw [contDiff_prod_iff]
  exact ⟨Complex.reCLM.contDiff.comp hF, Complex.imCLM.contDiff.comp hF⟩

lemma injective_gammaOf (u : ℝ → ℂ) (hper : ∀ t, u (t + 2 * Real.pi) = u t)
    (hinj : ∀ t t', u t = u t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m) :
    Function.Injective (gammaOf u hper) := by
  intro s s' hss
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective s
  obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective s'
  rw [gammaOf_coe, gammaOf_coe] at hss
  have hcc : u (2 * Real.pi * x) = u (2 * Real.pi * x') := by
    have := congrArg cpx hss
    simpa only [cpx_mk] using this
  obtain ⟨m, hm⟩ := hinj _ _ hcc
  have hx : x' = x + (m : ℝ) := by
    refine mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) ?_
    rw [hm]; ring
  rw [hx]
  have hm0 : (((m : ℝ)) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨m, by simp⟩
  rw [AddCircle.coe_add, hm0, add_zero]

/-- A point of the plane lies in the image of the descended curve `γ` exactly when it represents
a complex number in the image of `u`. -/
lemma mem_range_gammaOf_iff (u : ℝ → ℂ) (hper : ∀ t, u (t + 2 * Real.pi) = u t) (p : ℝ × ℝ) :
    p ∈ Set.range (gammaOf u hper) ↔ cpx p ∈ Set.range u := by
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective s
    refine ⟨2 * Real.pi * x, ?_⟩
    rw [gammaOf_coe]
    exact (cpx_mk _).symm
  · rintro ⟨t, ht⟩
    refine ⟨((t / (2 * Real.pi) : ℝ) : UnitAddCircle), ?_⟩
    rw [gammaOf_coe]
    have h2 : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
    rw [h2]
    exact cpx_injective (by rw [cpx_mk, ht])

/-! ## The direction identity for the unwound curve -/

/-- **The direction identity**: for a nowhere-zero `C¹` curve `v`,
`v s / ‖v s‖ = e^{i·windPhase v s} · (v 0 / ‖v 0‖)`.  It is the statement that the unwound curve
`windDir v s = e^{-i·windPhase v s}·v s` has constant direction; it follows from the ODE
`(windDir v)' = Re (v'/v)·windDir v` (`Work.RPB.B1.windDir_hasDerivAt`) together with the first
integral `Work.RPB.B1.exp_integral_of_hasDerivAt`. -/
lemma normalized_dir_identity (v : ℝ → ℂ) (hv : ContDiff ℝ 1 v) (hne : ∀ t, v t ≠ 0) :
    ∀ s, v s / ((‖v s‖ : ℝ) : ℂ) =
      Complex.exp ((windPhase v s : ℂ) * Complex.I) * (v 0 / ((‖v 0‖ : ℝ) : ℂ)) := by
  have hdw := windDir_hasDerivAt v hv hne
  have hderivcont : Continuous (fun x : ℝ => deriv v x / v x) :=
    (hv.continuous_deriv le_rfl).div hv.continuous hne
  have hode : ∀ s, windDir v s =
      Complex.exp (((∫ x in (0 : ℝ)..s, (deriv v x / v x).re : ℝ) : ℂ)) * v 0 := by
    intro s
    simpa [windDir_zero] using exp_integral_of_hasDerivAt (windDir v) (fun x : ℝ => (deriv v x / v x).re)
      (Complex.continuous_re.comp hderivcont) (fun s => by simpa using hdw s) s
  have hueq : ∀ s, v s = Complex.exp ((windPhase v s : ℂ) * Complex.I) *
      (Complex.exp (((∫ x in (0 : ℝ)..s, (deriv v x / v x).re : ℝ) : ℂ)) * v 0) := by
    intro s
    have h := hode s
    rw [windDir] at h
    have hcancel : Complex.exp ((windPhase v s : ℂ) * Complex.I) *
        Complex.exp (-((windPhase v s : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    calc v s = 1 * v s := (one_mul _).symm
      _ = (Complex.exp ((windPhase v s : ℂ) * Complex.I) *
            Complex.exp (-((windPhase v s : ℂ) * Complex.I))) * v s := by rw [hcancel]
      _ = Complex.exp ((windPhase v s : ℂ) * Complex.I) *
            (Complex.exp (-((windPhase v s : ℂ) * Complex.I)) * v s) := by rw [mul_assoc]
      _ = Complex.exp ((windPhase v s : ℂ) * Complex.I) *
            (Complex.exp (((∫ x in (0 : ℝ)..s, (deriv v x / v x).re : ℝ) : ℂ)) * v 0) := by
            rw [h]
  intro s
  have hnorm : ‖v s‖ = Real.exp (∫ x in (0 : ℝ)..s, (deriv v x / v x).re) * ‖v 0‖ := by
    rw [hueq s, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal]
    ring
  have hD : ((Real.exp (∫ x in (0 : ℝ)..s, (deriv v x / v x).re) : ℝ) : ℂ) ≠ 0 :=
    fun h0 => ne_of_gt (Real.exp_pos _) (Complex.ofReal_eq_zero.mp h0)
  rw [hnorm, hueq s, Complex.ofReal_mul, ← Complex.ofReal_exp, mul_div_assoc]
  rw [mul_div_mul_left _ _ hD]

/-! ## The log-derivative integral and the monodromy of an argument lift -/

/-- **The argument principle in log-derivative form.**  If `Ψ` is a continuous lift of the doubled
direction `dirZ (v t) = (arg (v t) / π : ℝ/ℤ)` of a nowhere-zero `C¹` curve `v`, then
`∮_0^{2π} Im (v'/v) = π · (Ψ (2π) - Ψ 0)`.

Indeed both `exp (i (windPhase v s + θ₀))` and `exp (i π Ψ s)` (with `e^{iθ₀} = v 0/‖v 0‖`) are
continuous arguments of `v s`, so they differ by a continuous `{±1}`-valued function; hence
`s ↦ 2 (π Ψ s - windPhase v s - θ₀)` is a continuous function whose exponential `e^{i·}` equals
`1`, and `Work.RPB.B1.exp_I_eq_one_const` makes it constant.  Specialising at `0` and `2π` and
unwinding the definition of `windPhase` gives the claim. -/
lemma logDeriv_integral_pi_monodromy (v : ℝ → ℂ) (hv : ContDiff ℝ 1 v) (hne : ∀ t, v t ≠ 0)
    (Ψ : ℝ → ℝ) (hΨ : Continuous Ψ)
    (hlift : ∀ t, ((Ψ t : ℝ) : UnitAddCircle) = dirZ (v t)) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), (deriv v t / v t).im)
      = Real.pi * (Ψ (2 * Real.pi) - Ψ 0) := by
  have hdir := normalized_dir_identity v hv hne
  have hderivcont : Continuous (fun x : ℝ => deriv v x / v x) :=
    (hv.continuous_deriv le_rfl).div hv.continuous hne
  have hφcont : Continuous (fun s : ℝ => windPhase v s) := by
    have hcont : Continuous (fun x : ℝ => (deriv v x / v x).im) := Complex.continuous_im.comp hderivcont
    simpa [windPhase] using (intervalIntegral.continuous_primitive (μ := MeasureTheory.volume)
        (f := fun x : ℝ => (deriv v x / v x).im) (fun a b => hcont.intervalIntegrable a b) 0)
  -- a real `θ₀` with `e^{iθ₀} = v 0 / ‖v 0‖`
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : ℝ, Complex.exp (((θ₀ : ℝ) : ℂ) * Complex.I) = v 0 / ((‖v 0‖ : ℝ) : ℂ) := by
    refine ⟨(v 0).arg, ?_⟩
    have h := Complex.norm_mul_exp_arg_mul_I (v 0)
    have hne0 : ((‖v 0‖ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr (hne 0)
    rw [eq_div_iff hne0, mul_comm]
    exact h
  have hexp_dir : ∀ s, Complex.exp ((((windPhase v s + θ₀) : ℝ) : ℂ) * Complex.I) =
      v s / ((‖v s‖ : ℝ) : ℂ) := by
    intro s
    rw [hdir s, ← hθ₀, ← Complex.exp_add]
    congr 1; push_cast; ring
  -- the exponent relation coming from the lift `Ψ`
  have harg_rel : ∀ s, ∃ n : ℤ, Real.pi * Ψ s = (v s).arg + Real.pi * n := by
    intro s
    have h := hlift s
    rw [dirZ] at h
    have hz : ((Ψ s : UnitAddCircle) - ((((v s).arg / Real.pi : ℝ)) : UnitAddCircle)) = 0 := by
      rw [h, sub_self]
    rw [← AddCircle.coe_sub] at hz
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    rw [zsmul_one] at hn
    refine ⟨n, ?_⟩
    have h2 : Ψ s = (v s).arg / Real.pi + n := by linarith
    rw [h2]; field_simp
  have hw : ∀ s, v s / ((‖v s‖ : ℝ) : ℂ) ≠ 0 := by
    intro s
    rw [div_ne_zero_iff]
    exact ⟨hne s, by rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr (hne s)⟩
  have hexp_arg : ∀ s, Complex.exp ((((v s).arg : ℝ) : ℂ) * Complex.I) =
      v s / ((‖v s‖ : ℝ) : ℂ) := by
    intro s
    have h := Complex.norm_mul_exp_arg_mul_I (v s)
    have hne0 : ((‖v s‖ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr (hne s)
    rw [eq_div_iff hne0, mul_comm]; exact h
  -- `2 (π Ψ s - windPhase v s - θ₀)` has exponential `e^{i·} = 1`
  have hexp2 : ∀ s, Complex.exp
      (((2 * (Real.pi * Ψ s - (windPhase v s + θ₀)) : ℝ) : ℂ) * Complex.I) = 1 := by
    intro s
    obtain ⟨n, hn⟩ := harg_rel s
    set w : ℂ := v s / ((‖v s‖ : ℝ) : ℂ) with hwdef
    have hwn : w ≠ 0 := hw s
    have hA : Complex.exp (((2 * (Real.pi * Ψ s) : ℝ) : ℂ) * Complex.I) = w^2 := by
      have hn2 : (2 * (Real.pi * Ψ s) : ℝ) = 2 * (v s).arg + 2 * Real.pi * (n : ℝ) := by
        linarith [hn]
      have harg2 : Complex.exp (((2 * (v s).arg : ℝ) : ℂ) * Complex.I) = w^2 := by
        have hsp : (((2 * (v s).arg : ℝ) : ℂ)) * Complex.I
            = (((v s).arg : ℝ) : ℂ) * Complex.I + (((v s).arg : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [hsp, Complex.exp_add, pow_two, hexp_arg s]
      have hfac : (((2 * (Real.pi * Ψ s) : ℝ)) : ℂ) * Complex.I
          = (((2 * (v s).arg : ℝ) : ℂ)) * Complex.I + (n : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hn2]; push_cast; ring
      rw [hfac, Complex.exp_add, Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩, mul_one, harg2]
    have hB : Complex.exp (((2 * (windPhase v s + θ₀) : ℝ) : ℂ) * Complex.I) = w^2 := by
      have hsp : (((2 * (windPhase v s + θ₀) : ℝ)) : ℂ) * Complex.I
          = (((windPhase v s + θ₀ : ℝ)) : ℂ) * Complex.I
            + (((windPhase v s + θ₀ : ℝ)) : ℂ) * Complex.I := by push_cast; ring
      rw [hsp, Complex.exp_add, pow_two, hexp_dir s]
    have hsplit2 : (((2 * (Real.pi * Ψ s - (windPhase v s + θ₀)) : ℝ)) : ℂ) * Complex.I
        = (((2 * (Real.pi * Ψ s) : ℝ)) : ℂ) * Complex.I
          + ((-(((2 * (windPhase v s + θ₀) : ℝ)) : ℂ))) * Complex.I := by push_cast; ring
    rw [hsplit2, Complex.exp_add, hA,
      show (-(((2 * (windPhase v s + θ₀) : ℝ)) : ℂ)) * Complex.I
        = -((((2 * (windPhase v s + θ₀) : ℝ)) : ℂ) * Complex.I) by ring,
      Complex.exp_neg, hB]
    exact mul_inv_cancel₀ (pow_ne_zero 2 hwn)
  have hgcont : Continuous (fun s : ℝ => 2 * (Real.pi * Ψ s - (windPhase v s + θ₀))) :=
    (((continuous_const.mul hΨ).sub (hφcont.add continuous_const)).const_mul 2)
  have hconstg := exp_I_eq_one_const hgcont hexp2
  have hkey : Real.pi * (Ψ (2 * Real.pi) - Ψ 0) = windPhase v (2 * Real.pi) := by
    have h2 := hconstg (2 * Real.pi)
    have h0 := hconstg 0
    have hφ0 : windPhase v 0 = 0 := windPhase_zero v
    linarith [h2, h0]
  rw [hkey, windPhase]

/-! ## The main theorem -/

theorem windInt_exists_ne_zero (u : ℝ → ℂ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t)
    (hinj : ∀ t t', u t = u t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m)
    (himm : ∀ t, deriv u t ≠ 0) :
    ∃ q : ℂ, q ∉ Set.range u ∧ Work.RPB.B1.windInt u q ≠ 0 := by
  -- transport to the ported curve `γ` and find a point of non-zero winding
  have hγc : Continuous (gammaOf u hper) := continuous_gammaOf u hper hu.continuous
  obtain ⟨p, hp, hwind⟩ := exists_winding_ne_zero (gammaOf u hper) hγc
      (injective_gammaOf u hper hinj) (contDiff_gammaOf u hper hu)
  have hqrange : cpx p ∉ Set.range u :=
    fun hmem => hp ((mem_range_gammaOf_iff u hper p).mpr hmem)
  refine ⟨cpx p, hqrange, ?_⟩
  -- the curve `v = u - cpx p`, nowhere zero
  have hvcont : ContDiff ℝ 1 (fun t : ℝ => u t - cpx p) :=
    (hu.of_le (WithTop.coe_le_coe.mpr le_top)).sub contDiff_const
  have hvne : ∀ t, u t - cpx p ≠ 0 := by
    intro t h
    exact hqrange ⟨t, sub_eq_zero.mp h⟩
  -- a lift of the doubled direction with non-zero monodromy, obtained from the degree
  set dl : UnitAddCircle → UnitAddCircle := dirCurve (gammaOf u hper) hγc p hp with hdl
  have hdlc : Continuous dl := continuous_dirCurve (gammaOf u hper) hγc p hp
  set Φ : ℝ → ℝ := liftOf dl hdlc with hΦ
  have hΦcont : Continuous Φ := liftOf_continuous dl hdlc
  have hdir_apply : ∀ τ : ℝ, dl (τ : UnitAddCircle) = dirZ (u (2 * Real.pi * τ) - cpx p) := by
    intro τ
    rw [hdl]
    have hkey : dirCurve (gammaOf u hper) hγc p hp (τ : UnitAddCircle)
        = dirZ (cpx (gammaOf u hper (τ : UnitAddCircle) - p)) := by
      show Work.RPB.Port.Collision.dirC (gammaOf u hper (τ : UnitAddCircle) - p)
          = dirZ (cpx (gammaOf u hper (τ : UnitAddCircle) - p))
      exact (dirZ_eq_dirC (cpx (gammaOf u hper (τ : UnitAddCircle) - p))).symm
    rw [hkey, cpx_sub, gammaOf_coe, cpx_mk]
  have hΦlift : ∀ τ : ℝ, ((Φ τ : ℝ) : UnitAddCircle) = dirZ (u (2 * Real.pi * τ) - cpx p) := by
    intro τ
    rw [hΦ, ← hdir_apply τ]
    exact liftOf_lifts dl hdlc τ
  -- rescale the parameter to the period `2π`
  set Ψ : ℝ → ℝ := fun s => Φ (s / (2 * Real.pi)) with hΨ
  have hΨcont : Continuous Ψ := hΦcont.comp (continuous_id.div_const _)
  have hΨlift : ∀ s : ℝ, ((Ψ s : ℝ) : UnitAddCircle) = dirZ (u s - cpx p) := by
    intro s
    rw [hΨ]
    show ((Φ (s / (2 * Real.pi)) : ℝ) : UnitAddCircle) = dirZ (u s - cpx p)
    rw [hΦlift (s / (2 * Real.pi))]
    rw [show 2 * Real.pi * (s / (2 * Real.pi)) = s by field_simp]
  -- the monodromy of `Ψ` is the (non-zero) winding number
  have hΦmono : Φ (0 + 1) = Φ 0 + (winding (gammaOf u hper) hγc hp : ℝ) := by
    rw [hΦ]
    simpa [winding] using liftOf_add_one dl hdlc 0
  have hΨmono : Ψ (2 * Real.pi) - Ψ 0 = (winding (gammaOf u hper) hγc hp : ℝ) := by
    rw [hΨ]
    simp only
    rw [show 2 * Real.pi / (2 * Real.pi) = 1 by field_simp, zero_div]
    simp only [zero_add] at hΦmono
    linarith [hΦmono]
  -- the argument principle computes `windInt` from the monodromy
  have hbridge := logDeriv_integral_pi_monodromy (fun t : ℝ => u t - cpx p) hvcont hvne
    Ψ hΨcont hΨlift
  have hderiv_eq : ∀ t, deriv (fun t : ℝ => u t - cpx p) t = deriv u t :=
    fun t => deriv_sub_const (cpx p)
  have hInt : (∫ t in (0 : ℝ)..(2 * Real.pi), (deriv u t / (u t - cpx p)).im)
      = Real.pi * (Ψ (2 * Real.pi) - Ψ 0) := by
    rw [← hbridge]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [hderiv_eq t]
  have hwindInt : windInt u (cpx p) = (1 / (2 * Real.pi)) * (Real.pi * (Ψ (2 * Real.pi) - Ψ 0)) := by
    rw [windInt, hInt]
  -- conclude
  intro hzero
  have hz : Ψ (2 * Real.pi) - Ψ 0 = 0 := by
    rw [hwindInt] at hzero
    rcases mul_eq_zero.mp hzero with h1 | h1
    · exact absurd h1 (by positivity)
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 Real.pi_ne_zero
      · exact h2
  rw [hΨmono] at hz
  exact hwind (by exact_mod_cast hz)

end

end Work.RPB.B1
