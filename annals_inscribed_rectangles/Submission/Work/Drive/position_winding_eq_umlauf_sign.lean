import Mathlib
import Submission.Work.Drive.CappingDefs
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.smooth_jordan_separation
import Submission.Work.Drive.cappingPolar_identification
import Submission.Work.Drive.exists_lift_dirC_deriv
import Submission.Work.Drive.signed_jump_at_point
import Submission.Work.Drive.umlauf
import Submission.Work.Drive.chord_loop_winding

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-! # The position winding and the Umlauf sign agree

Assembly file for `Work.Drive.position_winding_eq_umlauf_sign`.  The pieces used:

* `Work.Drive.signed_jump_at_point` (proved): crossing the curve to the left raises the winding
  number by exactly two, in the doubled `dirC`-normalisation of this workspace.
* the sign of the total turning (`umlauf_sign_aux` below, from the argument of
  `Work.Drive.winding_curve`, `Submission/Work/Drive/umlauf.lean`): the total turning is `+2π` iff the
  tangent at the lowest point of the curve points in the direction of increasing first coordinate.
* `Work.Drive.smooth_jordan_separation` (proved): the complement of a smooth embedded circle has two
  components, one bounded, and the winding number is constant on each.
-/

/-! ## The winding number is insensitive to the proof arguments -/

lemma windG_congr {γ : Circle → ℝ × ℝ} (hγ : Continuous γ) {p : ℝ × ℝ}
    (hp1 hp2 : p ∉ Set.range γ) : windG γ hγ hp1 = windG γ hγ hp2 := by
  unfold windG
  exact congrArg (fun h : p ∉ Set.range (gammaU γ) =>
    winding (gammaU γ) (continuous_gammaU hγ) h) (Subsingleton.elim _ _)

lemma windG_congr_cont {γ : Circle → ℝ × ℝ} (h1 h2 : Continuous γ) {p : ℝ × ℝ}
    (hp : p ∉ Set.range γ) : windG γ h1 hp = windG γ h2 hp := by
  unfold windG
  congr 2

/-! ## Polar lifts: the monodromy of the angle -/

/-- **The monodromy of the angle of a polar lift is constant.**  If `(ρ t, Θ t)` is a polar lift of a
`2π`-periodic curve `f`, with `ρ > 0`, then `Θ (t + 2π) - Θ t` is a continuous integer-valued function
of `t`, hence constant. -/
lemma polarLift_monodromy_const {f : ℝ → ℝ × ℝ} {ρ Θ : ℝ → ℝ}
    (hfper : ∀ t, f (t + 2 * Real.pi) = f t) (hΘ : Continuous Θ) (hρ : ∀ t, 0 < ρ t)
    (hlift : ∀ t, polarLift (ρ t, Θ t) = f t) (t : ℝ) :
    Θ (t + 2 * Real.pi) - Θ t = Θ (0 + 2 * Real.pi) - Θ 0 := by
  have hint : ∀ s : ℝ, ∃ m : ℤ, Θ (s + 2 * Real.pi) - Θ s = (m : ℝ) := by
    intro s
    have h1 : polarLift (ρ (s + 2 * Real.pi), Θ (s + 2 * Real.pi)) = polarLift (ρ s, Θ s) := by
      rw [hlift (s + 2 * Real.pi), hlift s, hfper s]
    have h2 : ρ (s + 2 * Real.pi) = ρ s := polarLift_radius_eq (hρ _) (hρ _) h1
    obtain ⟨m, hm⟩ := polarLift_angle_sub (hρ s) h1 h2
    exact ⟨m, by linarith⟩
  have hcont : Continuous fun s : ℝ => Θ (s + 2 * Real.pi) - Θ s :=
    (hΘ.comp (continuous_id.add continuous_const)).sub hΘ
  exact (isLocallyConstant_of_int_valued hcont hint).apply_eq_of_isPreconnected
    isPreconnected_univ (Set.mem_univ t) (Set.mem_univ 0)

/-- The doubled direction of a polar lift is twice the angle: `dirC (polarLift (r, ψ)) = 2ψ`. -/
lemma dirC_polarLift {r ψ : ℝ} (hr : r ≠ 0) :
    Submission.Collision.dirC (polarLift (r, ψ)) = ((2 * ψ : ℝ) : UnitAddCircle) := by
  have h1 : polarLift (r, ψ) = r • (Real.cos (2 * Real.pi * ψ), Real.sin (2 * Real.pi * ψ)) := by
    ext <;> simp [polarLift, smul_eq_mul]
  rw [h1, dirC_smul_ne hr, dirC_cos_sin]
  congr 1
  field_simp

/-! ## The winding number of a polar lift is `2m` -/

/-- **The position winding of a polar lift.**  If `(ρ, Θ)` is a polar lift of `γ - p` with `ρ > 0`
whose angle has monodromy `m` over one period, then the winding number of `γ` about `p` (in the
doubled `dirC`-normalisation) is `2m`. -/
lemma windG_eq_two_mul {γ : Circle → ℝ × ℝ} (hγc : Continuous γ) {p : ℝ × ℝ}
    (hp : p ∉ Set.range γ) {ρ Θ : ℝ → ℝ} {m : ℤ} (hΘ : Continuous Θ) (hρ : ∀ t, 0 < ρ t)
    (hlift : ∀ t, polarLift (ρ t, Θ t) = γ (Circle.exp t) - p)
    (hmono : ∀ t, Θ (t + 2 * Real.pi) - Θ t = (m : ℝ)) :
    windG γ hγc hp = 2 * m := by
  have hf : Continuous
      (dirCurve (gammaU γ) (continuous_gammaU hγc) p (notMem_range_gammaU hp)) :=
    continuous_dirCurve _ _ _ _
  have hGl : Continuous fun t : ℝ => 2 * Θ (2 * Real.pi * t) :=
    continuous_const.mul (hΘ.comp (continuous_const.mul continuous_id))
  have hlift' : ∀ t : ℝ, ((2 * Θ (2 * Real.pi * t) : ℝ) : UnitAddCircle) =
      dirCurve (gammaU γ) (continuous_gammaU hγc) p (notMem_range_gammaU hp) (t : UnitAddCircle) := by
    intro t
    show ((2 * Θ (2 * Real.pi * t) : ℝ) : UnitAddCircle)
      = Submission.Collision.dirC (gammaU γ (t : UnitAddCircle) - p)
    rw [gammaU_apply_coe]
    show ((2 * Θ (2 * Real.pi * t) : ℝ) : UnitAddCircle)
      = Submission.Collision.dirC (curve γ (2 * Real.pi * t) - p)
    rw [show curve γ (2 * Real.pi * t) - p
        = polarLift (ρ (2 * Real.pi * t), Θ (2 * Real.pi * t))
      from (hlift (2 * Real.pi * t)).symm]
    rw [dirC_polarLift (ne_of_gt (hρ (2 * Real.pi * t)))]
  have hmono' : ∀ t : ℝ,
      2 * Θ (2 * Real.pi * (t + 1)) = 2 * Θ (2 * Real.pi * t) + ((2 * m : ℤ) : ℝ) := by
    intro t
    have h : 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi := by ring
    have hm := hmono (2 * Real.pi * t)
    have hm2 : (2 : ℝ) * (Θ (2 * Real.pi * t + 2 * Real.pi) - Θ (2 * Real.pi * t))
        = ((2 * m : ℤ) : ℝ) := by
      rw [hm]; push_cast; ring
    rw [h]
    linarith [hm2]
  have hdeg := degree_eq_of_lift hf hGl hlift' hmono'
  rw [windG_eq_winding hγc hp (notMem_range_gammaU hp)]
  show degree (dirCurve (gammaU γ) (continuous_gammaU hγc) p (notMem_range_gammaU hp))
    (continuous_dirCurve _ _ _ _) = 2 * m
  exact hdeg.symm

/-! ## `dirOf` of a positive real multiple and of a unit exponential -/

lemma dirOf_mul_ofReal_pos {c : ℝ} (hc : 0 < c) (z : ℂ) :
    dirOf ((c : ℂ) * z) = dirOf z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · apply Subtype.ext
    have hcn : ‖(c : ℂ)‖ = c := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (le_of_lt hc)]
    rw [dirOf_coe (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hc)) hz), dirOf_coe hz,
      norm_mul, hcn, Complex.ofReal_mul]
    exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hc))

lemma dirOf_exp_mul_I (θ : ℝ) :
    dirOf (Complex.exp ((θ : ℂ) * Complex.I)) = Circle.exp θ := by
  apply Subtype.ext
  rw [dirOf_coe (Complex.exp_ne_zero _), Circle.coe_exp, Complex.norm_exp_ofReal_mul_I,
    Complex.ofReal_one, div_one]

/-- **The tangent angle provided by the Umlaufsatz is a lift of the tangent direction.** -/
lemma circleExp_eq_tangDir_of_deriv {γ : Circle → ℝ × ℝ} {θ ρ' : ℝ → ℝ} {t : ℝ}
    (hρ'pos : 0 < ρ' t)
    (hderiv : deriv (curve γ) t = ρ' t • (Real.cos (θ t), Real.sin (θ t))) :
    Circle.exp (θ t) = tangDir (curve γ) t := by
  have hz : toC (deriv (curve γ) t) = (ρ' t : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I) := by
    rw [hderiv, toC_smul, toC_cos_sin]
  show Circle.exp (θ t) = dirOf (toC (deriv (curve γ) t))
  rw [hz, dirOf_mul_ofReal_pos hρ'pos, dirOf_exp_mul_I]

/-! ## The sign of the total turning -/

/-- **The sign of the total turning** (the sign-exposing form of the argument of
`Work.Drive.winding_curve`): at the lowest point of a regular closed plane curve, the tangent points
in the direction of increasing first coordinate exactly when the total turning is `+2π`. -/
lemma umlauf_sign_aux {γ : Circle → ℝ × ℝ} (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    {t₀ : ℝ} (hmin : ∀ t, (curve γ t₀).2 ≤ (curve γ t).2)
    {θ : ℝ → ℝ} (hθc : Continuous θ) (hθ : ∀ t, Circle.exp (θ t) = tangDir (curve γ) t)
    {ε : ℤ} (hεper : ∀ t, θ (t + 2 * Real.pi) - θ t = 2 * Real.pi * ε) :
    (tangDir (curve γ) t₀ = 1 → ε = 1) ∧ (tangDir (curve γ) t₀ = -1 → ε = -1) := by
  have hc : RegCurve (curve γ) :=
    { contDiff := contDiff_curve γ hγ
      deriv_ne_zero := curve_deriv_ne_zero γ hγ
      periodic := curve_periodic γ
      eq_iff := curve_eq_iff γ hγ
      deriv_periodic := deriv_curve_periodic γ hγ }
  let c : ℝ → ℝ × ℝ := curve γ
  have hderiv : (deriv c t₀).2 = 0 := deriv_second_eq_zero c hc hmin
  obtain ⟨Θ, hΘc, hΘexp, hΘbase⟩ : ∃ Θ : tri t₀ → ℝ, Continuous Θ ∧
      (∀ p, Circle.exp (Θ p) = sigma c t₀ p) ∧ Θ (triBase t₀) = θ t₀ :=
    exists_angle_tri c hc t₀ θ hθ
  have hIlo : t₀ ∈ Set.Icc t₀ (t₀ + 2 * Real.pi) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hIhi : t₀ + 2 * Real.pi ∈ Set.Icc t₀ (t₀ + 2 * Real.pi) :=
    ⟨by linarith [Real.pi_pos], le_rfl⟩
  -- ### Step 1: the angle function agrees with the diagonal lift
  have hdiag : ∀ s : Set.Icc t₀ (t₀ + 2 * Real.pi),
      θ s.1 = Θ ⟨(s.1, s.1), ⟨s.2.1, le_rfl, s.2.2⟩⟩ := by
    intro s
    haveI : PreconnectedSpace (Set.Icc t₀ (t₀ + 2 * Real.pi)) :=
      Subtype.preconnectedSpace isPreconnected_Icc
    have h1 : Continuous (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) => θ s.1) :=
      hθc.comp continuous_subtype_val
    have h2 : Continuous (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) =>
        Θ ⟨(s.1, s.1), ⟨s.2.1, le_rfl, s.2.2⟩⟩) :=
      hΘc.comp (Continuous.subtype_mk
        (continuous_subtype_val.prodMk continuous_subtype_val)
        (fun s => ⟨s.2.1, le_rfl, s.2.2⟩))
    have he : ⇑Circle.exp ∘ (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) => θ s.1) =
        ⇑Circle.exp ∘ (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) =>
          Θ ⟨(s.1, s.1), ⟨s.2.1, le_rfl, s.2.2⟩⟩) := by
      funext s
      simp only [Function.comp_apply]
      rw [hθ s.1, hΘexp ⟨(s.1, s.1), ⟨s.2.1, le_rfl, s.2.2⟩⟩, sigma]
      exact (umlauf_sigmaPt_diag c t₀ s.1).symm
    have hbase : (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) => θ s.1) ⟨t₀, hIlo⟩ =
        (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) =>
          Θ ⟨(s.1, s.1), ⟨s.2.1, le_rfl, s.2.2⟩⟩) ⟨t₀, hIlo⟩ := by
      show θ t₀ = Θ ⟨(t₀, t₀), ⟨le_rfl, le_rfl, by linarith [Real.pi_pos]⟩⟩
      rw [← hΘbase]
      exact congrArg Θ (Subtype.ext rfl)
    exact congr_fun (IsCoveringMap.eq_of_comp_eq Circle.isCoveringMap_exp h1 h2 he ⟨t₀, hIlo⟩ hbase) s
  -- ### Step 2: the vertical side and the third side of the triangle
  set G : ℝ → ℝ := fun t => if h : t ∈ Set.Icc t₀ (t₀ + 2 * Real.pi) then
      Θ ⟨(t₀, t), ⟨le_rfl, h.1, h.2⟩⟩ else 0 with hG
  set G' : ℝ → ℝ := fun t => if h : t ∈ Set.Icc t₀ (t₀ + 2 * Real.pi) then
      Θ ⟨(t, t₀ + 2 * Real.pi), ⟨h.1, h.2, le_rfl⟩⟩ else 0 with hG'
  have hGcont : ContinuousOn G (Set.Icc t₀ (t₀ + 2 * Real.pi)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hgI : Continuous (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) =>
        Θ ⟨(t₀, s.1), ⟨le_rfl, s.2.1, s.2.2⟩⟩) :=
      hΘc.comp (Continuous.subtype_mk
        (continuous_const.prodMk continuous_subtype_val)
        (fun s => ⟨le_rfl, s.2.1, s.2.2⟩))
    apply Continuous.congr hgI
    intro s
    rw [Set.domRestrict_apply, hG]
    simp only [dif_pos s.2]
  have hG'cont : ContinuousOn G' (Set.Icc t₀ (t₀ + 2 * Real.pi)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hgI : Continuous (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) =>
        Θ ⟨(s.1, t₀ + 2 * Real.pi), ⟨s.2.1, s.2.2, le_rfl⟩⟩) :=
      hΘc.comp (Continuous.subtype_mk
        (continuous_subtype_val.prodMk continuous_const)
        (fun s => ⟨s.2.1, s.2.2, le_rfl⟩))
    apply Continuous.congr hgI
    intro s
    rw [Set.domRestrict_apply, hG']
    simp only [dif_pos s.2]
  have hGsin : ∀ t ∈ Set.Icc t₀ (t₀ + 2 * Real.pi), 0 ≤ Real.sin (G t) := by
    intro t ht
    have h1 : (((Circle.exp (G t)) : Circle) : ℂ).im = Real.sin (G t) := by
      rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    rw [← h1, hG]
    simp only [dif_pos ht]
    rw [hΘexp, sigma]
    exact sigmaPt_im_nonneg c hc hmin hderiv ht
  have hG'a : ∀ t ∈ Set.Icc t₀ (t₀ + 2 * Real.pi),
      Circle.exp (G' t) = -(Circle.exp (G t)) := by
    intro t ht
    rw [hG', hG]
    simp only [dif_pos ht]
    rw [hΘexp, hΘexp, sigma, sigma]
    exact sigmaPt_antisymm c hc ht
  have hrel : G' (t₀ + 2 * Real.pi) - G (t₀ + 2 * Real.pi) = G' t₀ - G t₀ := by
    have hPhi := eq_of_mem_period_multiples (f := fun t => G' t - G t - Real.pi)
      isPreconnected_Icc ((hG'cont.sub hGcont).sub continuousOn_const)
      (fun t ht => by
        have h1 : Circle.exp (G' t) = Circle.exp (G t + Real.pi) := by
          rw [hG'a t ht, umlauf_circle_exp_add_pi]
        obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp h1
        exact ⟨n, by linarith [hn]⟩)
    linarith [hPhi (t₀ + 2 * Real.pi) hIhi t₀ hIlo]
  -- values at the corners (named to keep the arithmetic below syntactic)
  set A : ℝ := Θ ⟨(t₀, t₀), ⟨le_rfl, le_rfl, by linarith [Real.pi_pos]⟩⟩ with hA
  set B : ℝ := Θ ⟨(t₀, t₀ + 2 * Real.pi), ⟨le_rfl, by linarith [Real.pi_pos], le_rfl⟩⟩ with hB
  set D : ℝ := Θ ⟨(t₀ + 2 * Real.pi, t₀ + 2 * Real.pi),
      ⟨by linarith [Real.pi_pos], le_rfl, le_rfl⟩⟩ with hD
  have hG₀ : G t₀ = A := by rw [hA, hG]; simp only [dif_pos hIlo]
  have hGhi : G (t₀ + 2 * Real.pi) = B := by rw [hB, hG]; simp only [dif_pos hIhi]
  have hG'₀ : G' t₀ = B := by rw [hB, hG']; simp only [dif_pos hIlo]
  have hG'hi : G' (t₀ + 2 * Real.pi) = D := by rw [hD, hG']; simp only [dif_pos hIhi]
  have hdiag_lo : θ t₀ = A := by rw [hA]; exact hdiag ⟨t₀, hIlo⟩
  have hdiag_hi : θ (t₀ + 2 * Real.pi) = D := by rw [hD]; exact hdiag ⟨t₀ + 2 * Real.pi, hIhi⟩
  have hbase' : A = θ t₀ := by
    rw [hA]
    rw [← show triBase t₀ = ⟨(t₀, t₀), ⟨le_rfl, le_rfl, by linarith [Real.pi_pos]⟩⟩
        from Subtype.ext rfl]
    exact hΘbase
  have hdiagch : θ (t₀ + 2 * Real.pi) - θ t₀ = D - A := by rw [hdiag_hi, hdiag_lo]
  -- ### The two cases for the sign of the turning
  have hbranch1 : tangDir c t₀ = 1 → θ (t₀ + 2 * Real.pi) - θ t₀ = 2 * Real.pi := by
    intro hpos
    have hGa : Circle.exp (G t₀) = 1 := by
      rw [hG₀, hA, hΘexp]
      show sigmaPt c t₀ (t₀, t₀) = 1
      rw [umlauf_sigmaPt_diag, hpos]
    have hGb : Circle.exp (G (t₀ + 2 * Real.pi)) = -1 := by
      rw [hGhi, hB, hΘexp]
      show sigmaPt c t₀ (t₀, t₀ + 2 * Real.pi) = -1
      rw [umlauf_sigmaPt_corner, hpos]
    have hδ : G (t₀ + 2 * Real.pi) - G t₀ = Real.pi :=
      strip_change_pos (by linarith [Real.pi_pos]) hGcont hGsin hGa hGb
    linarith [hdiagch, hrel, hδ, hG₀, hGhi, hG'₀, hG'hi]
  have hbranch2 : tangDir c t₀ = -1 → θ (t₀ + 2 * Real.pi) - θ t₀ = -2 * Real.pi := by
    intro hneg
    have hGa : Circle.exp (G t₀) = -1 := by
      rw [hG₀, hA, hΘexp]
      show sigmaPt c t₀ (t₀, t₀) = -1
      rw [umlauf_sigmaPt_diag, hneg]
    have hGb : Circle.exp (G (t₀ + 2 * Real.pi)) = 1 := by
      rw [hGhi, hB, hΘexp]
      show sigmaPt c t₀ (t₀, t₀ + 2 * Real.pi) = 1
      rw [umlauf_sigmaPt_corner, hneg]
      simp
    have hδ : G (t₀ + 2 * Real.pi) - G t₀ = -Real.pi :=
      strip_change_neg (by linarith [Real.pi_pos]) hGcont hGsin hGa hGb
    linarith [hdiagch, hrel, hδ, hG₀, hGhi, hG'₀, hG'hi]
  constructor
  · intro h1
    have h2 := hbranch1 h1
    have h3 := hεper t₀
    have h5 : 2 * Real.pi * (ε : ℝ) = 2 * Real.pi := by rw [← h3, h2]
    have h6 : (ε : ℝ) = 1 := by
      refine mul_left_cancel₀ (a := (2 * Real.pi : ℝ)) (by positivity) ?_
      simpa using h5
    exact_mod_cast h6
  · intro h1
    have h2 := hbranch2 h1
    have h3 := hεper t₀
    have h5 : 2 * Real.pi * (ε : ℝ) = -2 * Real.pi := by rw [← h3, h2]
    have h6 : (ε : ℝ) = -1 := by
      refine mul_left_cancel₀ (a := (2 * Real.pi : ℝ)) (by positivity) ?_
      simpa using h5
    exact_mod_cast h6


/-! ## The region below the lowest point of the curve -/

/-- **The winding number vanishes strictly below the lowest point of the curve**: the half-plane
`{x | x.2 < (curve γ t₀).2}` is disjoint from the curve (`hmin`), convex, and unbounded, and the
winding number is `0` at its far points. -/
lemma windG_eq_zero_of_second_lt {γ : Circle → ℝ × ℝ} (hγc : Continuous γ) {t₀ : ℝ}
    (hmin : ∀ t : ℝ, (curve γ t₀).2 ≤ (curve γ t).2) {q : ℝ × ℝ}
    (hq : q.2 < (curve γ t₀).2) (hq' : q ∉ Set.range γ) :
    windG γ hγc hq' = 0 := by
  set y₀ : ℝ := (curve γ t₀).2 with hy₀
  set C : Set (ℝ × ℝ) := {x | x.2 < y₀} with hC
  have hqC : q ∈ C := hq
  have hCsub : C ⊆ (Set.range γ)ᶜ := by
    intro x hx hxr
    obtain ⟨u, hu⟩ := hxr
    obtain ⟨s, hs⟩ := Circle.exp_surjective u
    have hx2 : y₀ ≤ x.2 := by
      rw [hy₀, ← hu, ← hs]
      exact hmin s
    exact absurd hx (not_lt.mpr hx2)
  have hCconv : Convex ℝ C := by
    have h : C = (LinearMap.snd ℝ ℝ ℝ) ⁻¹' Set.Iio y₀ := rfl
    rw [h]
    exact (convex_Iio y₀).linear_preimage (LinearMap.snd ℝ ℝ ℝ)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t : ℝ, ‖curve γ t‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_range hγc).isBounded.exists_norm_le
    exact ⟨M, fun t => hM (curve γ t) ⟨Circle.exp t, rfl⟩⟩
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  set z : ℝ × ℝ := (M + |y₀| + 1, y₀ - 1) with hz
  have hzC : z ∈ C := by
    change z.2 < y₀
    rw [hz]
    show y₀ - 1 < y₀
    linarith
  have hznorm : M < ‖z‖ := by
    have h1 : z.1 = M + |y₀| + 1 := rfl
    have h2 : ‖z.1‖ ≤ ‖z‖ := by
      rw [Prod.norm_def]
      exact le_max_left _ _
    rw [h1, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h2
    linarith [abs_nonneg y₀]
  have hzrange : z ∉ Set.range γ := by
    rw [← range_curve γ]
    rintro ⟨t, ht⟩
    have hMt := hM t
    rw [ht] at hMt
    linarith
  have hzero_z : windG γ hγc (hCsub hzC) = 0 := by
    refine windG_zero_far hγc (p := z) (hCsub hzC) (c := 0) (fun s => ?_)
    rw [dist_eq_norm, dist_eq_norm, sub_zero, sub_zero]
    exact lt_of_le_of_lt (hM s) hznorm
  have hconst := windG_preconnected hγc hCsub hCconv.isPreconnected
    (⟨z, hzC⟩ : C) (⟨q, hqC⟩ : C)
  exact (windG_congr hγc hq' (hCsub hqC)).trans (hconst.trans hzero_z)

/-! ## Transport of the winding number inside the bounded component -/

/-- **Two points of the complement with non-zero winding number have the same winding number.**
Both then lie in the bounded component (`Work.Drive.smooth_jordan_separation`), on which the winding
number is constant, while it vanishes on the unbounded one. -/
lemma windG_eq_of_ne_zero {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {p q : ℝ × ℝ}
    (hp : p ∉ Set.range γ) (hq : q ∉ Set.range γ)
    (hWp : windG γ hγ.isEmbedding.continuous hp ≠ 0)
    (hWq : windG γ hγ.isEmbedding.continuous hq ≠ 0) :
    windG γ hγ.isEmbedding.continuous hq = windG γ hγ.isEmbedding.continuous hp := by
  have hγc : Continuous γ := hγ.isEmbedding.continuous
  obtain ⟨ins, out, -, -, hins_pc, hout_pc, hinsbdd, -, hinsne, -, hcover, -, -, -⟩ :=
    smooth_jordan_separation γ hγ
  have hinsub : ins ⊆ (Set.range γ)ᶜ := by rw [hcover]; exact Set.subset_union_left
  have houtsub : out ⊆ (Set.range γ)ᶜ := by rw [hcover]; exact Set.subset_union_right
  have houtpre : IsPreconnected out := hout_pc.isConnected.isPreconnected
  have hinspre : IsPreconnected ins := hins_pc.isConnected.isPreconnected
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t : ℝ, ‖curve γ t‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_range hγc).isBounded.exists_norm_le
    exact ⟨M, fun t => hM (curve γ t) ⟨Circle.exp t, rfl⟩⟩
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  obtain ⟨K, hK⟩ := Metric.isBounded_iff.mp hinsbdd
  obtain ⟨a₀, ha₀⟩ := hinsne
  have hKnn : 0 ≤ K := le_trans dist_nonneg (hK ha₀ ha₀)
  set z : ℝ × ℝ := (K + ‖a₀‖ + M + 2, 0) with hz
  have hznorm : M < ‖z‖ := by
    have h1 : z.1 = K + ‖a₀‖ + M + 2 := rfl
    have h2 : ‖z.1‖ ≤ ‖z‖ := by
      rw [Prod.norm_def]
      exact le_max_left _ _
    rw [h1, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hKnn, hMnn, norm_nonneg a₀])] at h2
    linarith [norm_nonneg a₀]
  have hzrange : z ∉ Set.range γ := by
    rw [← range_curve γ]
    rintro ⟨t, ht⟩
    have hMt := hM t
    rw [ht] at hMt
    linarith
  have hz_notins : z ∉ ins := by
    intro hzin
    have hdist := hK hzin ha₀
    have h1 : z.1 = K + ‖a₀‖ + M + 2 := rfl
    have h2 : a₀.1 ≤ ‖a₀‖ := by
      rw [Prod.norm_def]
      simp only [Real.norm_eq_abs]
      exact le_trans (le_abs_self _) (le_max_left _ _)
    rw [Prod.dist_eq, Real.dist_eq, h1] at hdist
    have h2' : |K + ‖a₀‖ + M + 2 - a₀.1| ≤ K := le_trans (le_max_left _ _) hdist
    have h3 : K + ‖a₀‖ + M + 2 - a₀.1 ≥ 0 := by linarith
    rw [abs_of_nonneg h3] at h2'
    linarith
  have hzout : z ∈ out := by
    have hzmem : z ∈ (Set.range γ)ᶜ := hzrange
    rw [hcover] at hzmem
    rcases hzmem with h | h
    · exact absurd h hz_notins
    · exact h
  have hout_zero : ∀ (q' : ℝ × ℝ) (hq' : q' ∉ Set.range γ), q' ∈ out →
      windG γ hγc hq' = 0 := by
    intro q' hq' hq'out
    have hz0 : windG γ hγc (houtsub hzout) = 0 := by
      refine windG_zero_far hγc (p := z) (houtsub hzout) (c := 0) (fun s => ?_)
      rw [dist_eq_norm, dist_eq_norm, sub_zero, sub_zero]
      exact lt_of_le_of_lt (hM s) hznorm
    have hconst := windG_preconnected hγc houtsub houtpre
      (⟨z, hzout⟩ : out) (⟨q', hq'out⟩ : out)
    exact (windG_congr hγc hq' (houtsub hq'out)).trans (hconst.trans hz0)
  have hpins : p ∈ ins := by
    have hpmem : p ∈ (Set.range γ)ᶜ := hp
    rw [hcover] at hpmem
    rcases hpmem with h | h
    · exact h
    · exact absurd (hout_zero p hp h) hWp
  have hqins : q ∈ ins := by
    have hqmem : q ∈ (Set.range γ)ᶜ := hq
    rw [hcover] at hqmem
    rcases hqmem with h | h
    · exact h
    · exact absurd (hout_zero q hq h) hWq
  have hconst := windG_preconnected hγc hinsub hinspre (⟨p, hpins⟩ : ins) (⟨q, hqins⟩ : ins)
  exact (windG_congr hγc hq (hinsub hqins)).trans
    ((hconst.trans (windG_congr hγc (hinsub hpins) hp).symm))

/-! ## The main theorem -/

open Manifold in
open scoped Manifold ContDiff in
/-- **The position winding and the Umlauf sign agree.**  Let `γ : Circle → ℝ²` be a smooth embedded
closed plane curve, `p` a point off it, `(ρ, Θ)` a polar lift of the position vector `γ - p` (so
`polarLift (ρ t, Θ t) = γ (Circle.exp t) - p`, `ρ > 0`, `Θ` continuous) whose total change over one
period is the integer `m`, and `(θ, ρ', ε)` the Umlauf data of `γ` (so `deriv (γ ∘ exp) t` has direction
`θ t`, `ρ' > 0`, and `θ` changes by `2π ε` with `ε = ±1`).

If `m ≠ 0` — i.e. the position winds around `p` at all — then `m = ε`: the position winds around `p`
exactly as the tangent turns, in particular exactly once and in the same direction.  (In the
`dirC`-normalisation of this workspace the same statement reads: the winding number of `γ` about `p`,
i.e. the degree of `t ↦ dirC (γ (Circle.exp t) - p)`, is `2m`, and if it is non-zero then it equals
`2ε`.)

This is the sign coherence that the capping of the configuration Möbius strip needs: with
`η = 2ψ + θ₀` the boundary `∂M` of the strip is a `(2,1)`-curve *up to a curve of degree*
`deg η - 2 deg ψ = 2ε - 2m`, and after the gluing `Submission.Work.Drive.glueTorus` (which turns the
`(2,1)`-family of the configuration boundary torus into the meridian family of the cap,
`glueTorus_preimage_t21`) the boundary curve is a *meridian* — hence bounds a disk of the cap — exactly
when this degree vanishes.  The value of `m` alone (`m ∈ {0, ±1}` for a Jordan curve, the content of
`Work.Drive.winding_values`) does not give the agreement of the *signs*, which is why this statement is
needed separately: geometrically both signs are the orientation of the curve (the boundary of a domain
is positively oriented with respect to it; the sign of the position winding about an interior point is
that orientation, as is the sign of the total turning of the tangent).  Note that injectivity of `γ` is
essential: for a mere immersion (a figure eight) the claim is false. -/
theorem position_winding_eq_umlauf_sign (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {p : ℝ × ℝ} (hp : p ∉ Set.range γ)
    {ρ Θ : ℝ → ℝ} {m : ℤ} (hρ : Continuous ρ) (hΘ : Continuous Θ) (hρpos : ∀ t, 0 < ρ t)
    (hΘlift : ∀ t, Work.Drive.polarLift (ρ t, Θ t) = γ (Circle.exp t) - p)
    (hΘper : Θ (2 * Real.pi) - Θ 0 = (m : ℝ))
    {θ ρ' : ℝ → ℝ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hθ : Continuous θ) (hρ'pos : ∀ t, 0 < ρ' t)
    (hθderiv : ∀ t, deriv (fun s => γ (Circle.exp s)) t =
      ρ' t • (Real.cos (θ t), Real.sin (θ t)))
    (hθper : ∀ t, θ (t + 2 * Real.pi) - θ t = 2 * Real.pi * ε)
    (hne : m ≠ 0) : m = ε := by
  have hγc : Continuous γ := hγ.isEmbedding.continuous
  have hreg : RegCurve (curve γ) :=
    { contDiff := contDiff_curve γ hγ
      deriv_ne_zero := curve_deriv_ne_zero γ hγ
      periodic := curve_periodic γ
      eq_iff := curve_eq_iff γ hγ
      deriv_periodic := deriv_curve_periodic γ hγ }
  -- the monodromy of `Θ` is `m` everywhere
  have hmono : ∀ t, Θ (t + 2 * Real.pi) - Θ t = (m : ℝ) := by
    intro t
    have h := polarLift_monodromy_const (f := fun s => γ (Circle.exp s) - p)
      (fun s => by
        show γ (Circle.exp (s + 2 * Real.pi)) - p = γ (Circle.exp s) - p
        rw [Circle.exp_add, Circle.exp_two_pi, mul_one]) hΘ hρpos hΘlift t
    rw [h]
    simpa using hΘper
  have hW : windG γ hγc hp = 2 * m := windG_eq_two_mul hγc hp hΘ hρpos hΘlift hmono
  -- the lowest point of the curve
  obtain ⟨t₀, -, hmin⟩ := exists_global_min (curve γ) hreg
  have hV2 : (deriv (curve γ) t₀).2 = 0 := deriv_second_eq_zero (curve γ) hreg hmin
  have hVne : deriv (curve γ) t₀ ≠ 0 := curve_deriv_ne_zero γ hγ t₀
  have hV1 : (deriv (curve γ) t₀).1 ≠ 0 := by
    intro h0
    exact hVne (Prod.ext h0 hV2)
  -- `θ` is a lift of the tangent direction
  have htang : ∀ t, Circle.exp (θ t) = tangDir (curve γ) t := fun t =>
    circleExp_eq_tangDir_of_deriv (hρ'pos t) (hθderiv t)
  obtain ⟨hsgn1, hsgnm1⟩ := umlauf_sign_aux hγ hmin hθ htang hθper
  -- the direction of the tangent at the lowest point
  have hdir_t₀ : tangDir (curve γ) t₀
      = if 0 < (deriv (curve γ) t₀).1 then (1 : Circle) else -1 := by
    rw [tangDir]
    have htoC : toC (deriv (curve γ) t₀) = (((deriv (curve γ) t₀).1 : ℝ) : ℂ) := by
      have h2 : deriv (curve γ) t₀ = ((deriv (curve γ) t₀).1, 0) := Prod.ext rfl hV2
      rw [h2]
      simp [toC]
    rw [htoC]
    by_cases h : 0 < (deriv (curve γ) t₀).1
    · rw [if_pos h, dirOf_ofReal_pos h]
    · rw [if_neg h, dirOf_ofReal_neg (lt_of_le_of_ne (le_of_not_gt h) hV1)]
  -- the two points on either side of the lowest point
  obtain ⟨δ, hδpos, hjump⟩ := signed_jump_at_point γ hγ t₀
  set e : ℝ := δ / 2 with he
  have hepos : 0 < e := by rw [he]; linarith
  have helt : e < δ := by rw [he]; linarith
  obtain ⟨hjA, hjB, hjeq⟩ := hjump e hepos helt
  have hrot : rot90 (deriv (curve γ) t₀) = (0, (deriv (curve γ) t₀).1) := by
    ext <;> simp [rot90, hV2]
  have hqA : curve γ t₀ + e • rot90 (deriv (curve γ) t₀) ∉ Set.range γ := by
    rw [← range_curve γ]
    rintro ⟨t, ht⟩
    exact hjA t ht
  have hqB : curve γ t₀ - e • rot90 (deriv (curve γ) t₀) ∉ Set.range γ := by
    rw [← range_curve γ]
    rintro ⟨t, ht⟩
    exact hjB t ht
  have hjump' : windG γ hγc hqA - windG γ hγc hqB = 2 := by
    have h : windG γ hγ.isEmbedding.continuous hqA
        - windG γ hγ.isEmbedding.continuous hqB = 2 := hjeq hqA hqB
    have h1 : windG γ hγc hqA = windG γ hγ.isEmbedding.continuous hqA :=
      windG_congr_cont hγc hγ.isEmbedding.continuous hqA
    have h2 : windG γ hγc hqB = windG γ hγ.isEmbedding.continuous hqB :=
      windG_congr_cont hγc hγ.isEmbedding.continuous hqB
    linarith [h, h1, h2]
  -- on one of the two sides the winding number is `2ε`
  have hεne : ε ≠ 0 := by rcases hε with h | h <;> omega
  have hmain : windG γ hγc hqA = 2 * ε ∨ windG γ hγc hqB = 2 * ε := by
    by_cases hv : 0 < (deriv (curve γ) t₀).1
    · left
      have hε1 : ε = 1 := hsgn1 (by rw [hdir_t₀, if_pos hv])
      have hbelow : windG γ hγc hqB = 0 := by
        refine windG_eq_zero_of_second_lt hγc hmin ?_ hqB
        have h2 : (curve γ t₀ - e • rot90 (deriv (curve γ) t₀)).2
            = (curve γ t₀).2 - e * (deriv (curve γ) t₀).1 := by
          rw [hrot]
          simp [Prod.snd_sub, smul_eq_mul]
        rw [h2]
        nlinarith [hepos, hv]
      rw [hε1] at ⊢
      linarith [hjump', hbelow]
    · right
      have hv' : (deriv (curve γ) t₀).1 < 0 := lt_of_le_of_ne (le_of_not_gt hv) hV1
      have hεm1 : ε = -1 := hsgnm1 (by rw [hdir_t₀, if_neg hv])
      have hbelow : windG γ hγc hqA = 0 := by
        refine windG_eq_zero_of_second_lt hγc hmin ?_ hqA
        have h2 : (curve γ t₀ + e • rot90 (deriv (curve γ) t₀)).2
            = (curve γ t₀).2 + e * (deriv (curve γ) t₀).1 := by
          rw [hrot]
          simp [Prod.snd_add, smul_eq_mul]
        rw [h2]
        nlinarith [hepos, hv']
      rw [hεm1] at ⊢
      linarith [hjump', hbelow]
  -- transport to `p`
  have key : ∀ {q : ℝ × ℝ} (hq : q ∉ Set.range γ), windG γ hγc hq = 2 * ε →
      windG γ hγc hp = 2 * ε := by
    intro q hq hwind
    have hq0 : windG γ hγ.isEmbedding.continuous hq ≠ 0 := by
      have hq0' : windG γ hγc hq ≠ 0 := by
        rw [hwind]
        exact mul_ne_zero (by norm_num) hεne
      rwa [windG_congr_cont hγc hγ.isEmbedding.continuous hq] at hq0'
    have hp0 : windG γ hγ.isEmbedding.continuous hp ≠ 0 := by
      have hp0' : windG γ hγc hp ≠ 0 := by
        rw [hW]
        exact mul_ne_zero (by norm_num) hne
      rwa [windG_congr_cont hγc hγ.isEmbedding.continuous hp] at hp0'
    have h1 := windG_eq_of_ne_zero hγ hp hq hp0 hq0
    rw [← windG_congr_cont hγc hγ.isEmbedding.continuous hq,
        ← windG_congr_cont hγc hγ.isEmbedding.continuous hp] at h1
    rw [← h1, hwind]
  have hfinal : windG γ hγc hp = 2 * ε := by
    rcases hmain with h | h
    · exact key hqA h
    · exact key hqB h
  rw [hW] at hfinal
  omega

end Work.Drive
