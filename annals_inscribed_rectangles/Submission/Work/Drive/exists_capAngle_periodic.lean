import Mathlib
import Submission.Work.Drive.Neutral.stripTauData
import Submission.Work.Drive.planeWrapData
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.exists_contDiff_polarLift
import Submission.Work.Drive.doubledPositionPoint

/-!
# The periodic smooth cap angle of the configuration strip's diagonal

For a smooth embedded closed plane curve `γ` avoiding the origin *and enclosing it with the
orientation of its tangent* (`Work.Drive.WrapData γ` says that the doubled position direction about
the origin has a continuous lift of non-zero total; with `hU : Submission.Drive.UmlaufProp` the
doubled tangent direction then has the same total — the winding of an enclosed point is the rotation
index), the diagonal of the configuration strip has a `C^∞`, `2π`-periodic *cap angle* `Θ`:

`circleOf (Θ t) = symmE γ t 0 * (star (symmD γ t 0)) ^ 2`,

i.e. `Θ` is the cap angle "doubled tangent direction minus doubled position direction (about the
origin), divided by `2π`", computed from the *smooth* data of the strip: `symmE γ t 0` (the squared
unit tangent direction) and `symmD γ t 0` (the disk coordinate, which on the diagonal is the unit
position vector).

The proof assembles:

* the smooth lift of the doubled position direction about the origin (`exists_contDiff_polarLift`
  applied to the nowhere-vanishing `t ↦ symmC (curve γ t)`, using `hγne`), with class
  `dirC (curve γ t)`;
* the smooth lift of the doubled *tangent* direction (`exists_contDiff_polarLift` applied to
  `t ↦ symmC ((curve γ)' t)`, nowhere vanishing by `curve_deriv_ne_zero`);
* the **sign match** about the origin (`doubled_position_total_eq_doubled_tangent_total_of_point`,
  using `hU` and `hW`): a continuous lift of the doubled tangent direction with the same *total* as
  the doubled position direction.  Any two lifts of the same class function differ by an
  integer-valued continuous function, hence by an integer *constant*; together with the constancy of
  the monodromy of a lift of a periodic class function this transports the total equality to the
  smooth lifts, for *every* `t`, giving the periodicity of `Φ₀ - Ψ₀`;
* the arithmetic `circleOf (x - y) = circleOf x * (circleOf y)⁻¹`, the "halving" identity
  `circleOf (dirC v) = (v/‖v‖)^2` of `Drive/contDiffOn_chordUnitDir.lean`, and the diagonal values
  `symmR γ σ 0 = ‖symmC (curve γ σ)‖`, `symmD γ σ 0 = symmC (curve γ σ)/‖symmC (curve γ σ)‖`,
  `symmWC γ σ 0 = symmC (deriv (curve γ) σ)` of `Neutral/stripTauData.lean`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff
open Work.Drive.Neutral

open Submission.Collision (dirC)

noncomputable section

/-! ## The diagonal of the symmetric family -/

/-- The complexification `symmC`, as a sum. -/
lemma symmC_eq_add_mul_I (v : ℝ × ℝ) : symmC v = (v.1 : ℂ) + (v.2 : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_ <;> simp [symmC]

lemma symmMid_zero (γ : Circle → ℝ × ℝ) (σ : ℝ) : symmMid γ σ 0 = curve γ σ := by
  rw [symmMid, add_zero, sub_zero, add_self_div_two_prod]

lemma symmChordC_zero (γ : Circle → ℝ × ℝ) (σ : ℝ) : symmChordC γ σ 0 = 0 := by
  simp only [symmChordC, chordC_eq_symmC, add_zero, sub_zero, sub_self, symmC]
  rfl

/-- On the diagonal, the capping radius is the distance of the point to the origin. -/
lemma symmR_zero (γ : Circle → ℝ × ℝ) (σ : ℝ) : symmR γ σ 0 = ‖symmC (curve γ σ)‖ := by
  have hA : symmA γ σ 0 = ‖symmC (curve γ σ)‖ ^ 2 := by
    rw [symmA, symmMid_zero, symmChordC_zero, Complex.normSq_zero, add_zero, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [symmC]
    ring
  rw [symmR, hA, Real.sqrt_sq (norm_nonneg _)]

/-- On the diagonal, the disk coordinate is the *unit position vector* of the curve point. -/
lemma symmD_zero_eq (γ : Circle → ℝ × ℝ) (σ : ℝ) :
    symmD γ σ 0 = symmC (curve γ σ) / (((‖symmC (curve γ σ)‖ : ℝ)) : ℂ) := by
  rw [symmD, symmMid_zero, symmR_zero, symmC_eq_add_mul_I]

/-- The "halving" identity: `circleOf` of the doubled direction of `v` is the square of its unit
vector. -/
lemma circleOf_dirC (v : ℝ × ℝ) (hv : v ≠ 0) :
    circleOf (dirC v) = (symmC v / (((‖symmC v‖ : ℝ)) : ℂ)) ^ 2 := by
  have hz : symmC v ≠ 0 := fun h => hv (symmC_eq_zero_iff.mp h)
  simpa only [symmC, dirC] using circleOf_arg_div_pi (symmC v) hz

/-- The square of the diagonal disk coordinate is `circleOf` of the doubled position direction. -/
lemma symmD_zero_sq (γ : Circle → ℝ × ℝ) (σ : ℝ) (hv : curve γ σ ≠ 0) :
    (symmD γ σ 0) ^ 2 = circleOf (dirC (curve γ σ)) := by
  rw [symmD_zero_eq, ← circleOf_dirC (curve γ σ) hv]

/-- The square of the conjugate of the diagonal disk coordinate is the inverse of `circleOf` of the
doubled position direction. -/
lemma star_symmD_zero_sq (γ : Circle → ℝ × ℝ) (σ : ℝ) (hv : curve γ σ ≠ 0) :
    (star (symmD γ σ 0)) ^ 2 = (circleOf (dirC (curve γ σ)))⁻¹ := by
  rw [← star_pow, symmD_zero_sq γ σ hv]
  exact (Complex.inv_eq_conj (norm_circleOf _)).symm

lemma mul_one_div_norm_eq_div (z : ℂ) :
    z * (((1 : ℝ) / ‖z‖ : ℝ) : ℂ) = z / (((‖z‖ : ℝ)) : ℂ) := by
  rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_one, one_mul,
    div_eq_mul_inv]

/-- The diagonal value of `symmE` is `circleOf` of the doubled tangent direction. -/
lemma symmE_zero_eq (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (σ : ℝ) :
    symmE γ σ 0 = circleOf (dirC (deriv (curve γ) σ)) := by
  have hv : deriv (curve γ) σ ≠ 0 := curve_deriv_ne_zero γ hγ σ
  rw [symmE, symmWC_zero hγ σ, mul_one_div_norm_eq_div]
  exact (circleOf_dirC (deriv (curve γ) σ) hv).symm

/-- `circleOf` of a real difference is the quotient of the two `circleOf`'s. -/
lemma circleOf_sub (x y : ℝ) :
    circleOf ((x - y : ℝ) : UnitAddCircle)
      = circleOf ((x : ℝ) : UnitAddCircle) * (circleOf ((y : ℝ) : UnitAddCircle))⁻¹ := by
  rw [circleOf_coe_eq_exp, circleOf_coe_eq_exp, circleOf_coe_eq_exp, ← Complex.exp_neg,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A smooth polar lift of a nowhere-vanishing complex curve doubles to its `dirC`-class: if
`polarLift (‖v t‖, ϑ t) = ((v t).re, (v t).im)` then `(2 ϑ t) = dirC ((v t).re, (v t).im)` in
`ℝ/ℤ`. -/
lemma dirC_symmC_polarLift {v : ℝ → ℂ} {ϑ : ℝ → ℝ} (hne : ∀ t, v t ≠ 0)
    (hlift : ∀ t, polarLift (‖v t‖, ϑ t) = ((v t).re, (v t).im)) :
    ∀ t, ((2 * ϑ t : ℝ) : UnitAddCircle) = dirC ((v t).re, (v t).im) := by
  intro t
  have h := dirC_polarLift (r := ‖v t‖) (ψ := ϑ t) (norm_ne_zero_iff.mpr (hne t))
  rw [hlift t] at h
  exact h.symm

end

/-! ## The theorem -/

theorem exists_capAngle_periodic (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hU : Submission.Drive.UmlaufProp)
    (hW : Work.Drive.WrapData γ) :
    ∃ Θ : ℝ → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
      (∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t) ∧
      (∀ t : ℝ, circleOf (Θ t)
        = Work.Drive.Neutral.symmE γ t 0 * (star (Work.Drive.Neutral.symmD γ t 0)) ^ 2) := by
  have hcurve : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (curve γ) := contDiff_curve_top hγ
  have hcurve_ne : ∀ t : ℝ, curve γ t ≠ 0 := fun t => hγne (Circle.exp t)
  -- ### the smooth lift of the doubled position direction about the origin
  have hvP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => symmC (curve γ t)) :=
    contDiff_symmC.comp hcurve
  have hvPne : ∀ t : ℝ, symmC (curve γ t) ≠ 0 := fun t h => hcurve_ne t (symmC_eq_zero_iff.mp h)
  obtain ⟨ϑP, hϑPsm, hϑPlift⟩ := exists_contDiff_polarLift _ hvP hvPne
  let Ψ₀ : ℝ → ℝ := fun t => 2 * ϑP t
  have hΨ₀sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ₀ := contDiff_const.mul hϑPsm
  have hΨ₀cls : ∀ t : ℝ, ((Ψ₀ t : ℝ) : UnitAddCircle) = dirC (curve γ t) := by
    intro t
    have h := dirC_symmC_polarLift (v := fun t => symmC (curve γ t)) (ϑ := ϑP) hvPne hϑPlift t
    simpa only [Ψ₀, symmC] using h
  -- ### the smooth lift of the doubled tangent direction
  have hderivsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (curve γ)) :=
    contDiff_deriv_of_contDiff hcurve
  have hvT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => symmC (deriv (curve γ) t)) :=
    contDiff_symmC.comp hderivsm
  have hvTne : ∀ t : ℝ, symmC (deriv (curve γ) t) ≠ 0 :=
    fun t h => curve_deriv_ne_zero γ hγ t (symmC_eq_zero_iff.mp h)
  obtain ⟨ϑT, hϑTsm, hϑTlift⟩ := exists_contDiff_polarLift _ hvT hvTne
  let Φ₀ : ℝ → ℝ := fun t => 2 * ϑT t
  have hΦ₀sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ₀ := contDiff_const.mul hϑTsm
  have hΦ₀cls : ∀ t : ℝ, ((Φ₀ t : ℝ) : UnitAddCircle) = dirC (deriv (curve γ) t) := by
    intro t
    have h := dirC_symmC_polarLift (v := fun t => symmC (deriv (curve γ) t)) (ϑ := ϑT) hvTne
      hϑTlift t
    simpa only [Φ₀, symmC] using h
  -- ### the sign match about the origin
  obtain ⟨Ψ, hΨc, hΨcls, hΨtot⟩ := hW
  have h0 : (0 : ℝ × ℝ) ∉ Set.range γ := fun ⟨x, hx⟩ => hγne x hx
  have hΨcls' : ∀ t : ℝ, ((Ψ t : ℝ) : UnitAddCircle) = dirC (γ (Circle.exp t) - 0) :=
    fun t => by simpa using hΨcls t
  obtain ⟨Φ, hΦc, hΦcls, hΦtot⟩ :=
    doubled_position_total_eq_doubled_tangent_total_of_point hU γ hγ h0 Ψ hΨc hΨcls' hΨtot
  have hΦcls' : ∀ t : ℝ, ((Φ t : ℝ) : UnitAddCircle) = dirC (deriv (curve γ) t) := by
    intro t
    have h := hΦcls t
    rw [show deriv (fun s : ℝ => γ (Circle.exp s)) t = deriv (curve γ) t from rfl] at h
    exact h
  -- ### the smooth lift differs from the continuous one by an integer constant
  have hΦdiff : ∀ t : ℝ, Φ₀ t - Φ t = Φ₀ 0 - Φ 0 := by
    have hcont : Continuous fun t : ℝ => Φ₀ t - Φ t := hΦ₀sm.continuous.sub hΦc
    have hint : ∀ t : ℝ, ∃ k : ℤ, Φ₀ t - Φ t = (k : ℝ) := by
      intro t
      have hcl : ((Φ₀ t : ℝ) : UnitAddCircle) = ((Φ t : ℝ) : UnitAddCircle) := by
        rw [hΦ₀cls t, hΦcls' t]
      obtain ⟨k, hk⟩ := (coe_eq_coe_iff_int (Φ₀ t) (Φ t)).mp hcl
      exact ⟨k, hk.symm⟩
    have hlc := isLocallyConstant_of_int_valued hcont hint
    intro t
    exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ t) (Set.mem_univ 0)
  have hΨdiff : ∀ t : ℝ, Ψ₀ t - Ψ t = Ψ₀ 0 - Ψ 0 := by
    have hcont : Continuous fun t : ℝ => Ψ₀ t - Ψ t := hΨ₀sm.continuous.sub hΨc
    have hint : ∀ t : ℝ, ∃ k : ℤ, Ψ₀ t - Ψ t = (k : ℝ) := by
      intro t
      have hcl : ((Ψ₀ t : ℝ) : UnitAddCircle) = ((Ψ t : ℝ) : UnitAddCircle) := by
        rw [hΨ₀cls t, hΨcls' t]
        simp [curve]
      obtain ⟨k, hk⟩ := (coe_eq_coe_iff_int (Ψ₀ t) (Ψ t)).mp hcl
      exact ⟨k, hk.symm⟩
    have hlc := isLocallyConstant_of_int_valued hcont hint
    intro t
    exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ t) (Set.mem_univ 0)
  -- ### the monodromy of each continuous lift is constant
  have hΦmono : ∀ t : ℝ, Φ (t + 2 * Real.pi) - Φ t = Φ (2 * Real.pi) - Φ 0 := by
    refine monodromy_const_of_int_valued hΦc ?_
    intro t
    have hper : deriv (fun s : ℝ => γ (Circle.exp s)) (t + 2 * Real.pi)
        = deriv (fun s : ℝ => γ (Circle.exp s)) t := deriv_curve_periodic γ hγ t
    have hcl : ((Φ (t + 2 * Real.pi) : ℝ) : UnitAddCircle) = ((Φ t : ℝ) : UnitAddCircle) := by
      rw [hΦcls (t + 2 * Real.pi), hΦcls t, hper]
    obtain ⟨k, hk⟩ := (coe_eq_coe_iff_int (Φ (t + 2 * Real.pi)) (Φ t)).mp hcl
    exact ⟨k, hk.symm⟩
  have hΨmono : ∀ t : ℝ, Ψ (t + 2 * Real.pi) - Ψ t = Ψ (2 * Real.pi) - Ψ 0 := by
    refine monodromy_const_of_int_valued hΨc ?_
    intro t
    have hper : γ (Circle.exp (t + 2 * Real.pi)) = γ (Circle.exp t) := by
      rw [Circle.exp_add_two_pi]
    have hcl : ((Ψ (t + 2 * Real.pi) : ℝ) : UnitAddCircle) = ((Ψ t : ℝ) : UnitAddCircle) := by
      rw [hΨcls (t + 2 * Real.pi), hΨcls t, hper]
    obtain ⟨k, hk⟩ := (coe_eq_coe_iff_int (Ψ (t + 2 * Real.pi)) (Ψ t)).mp hcl
    exact ⟨k, hk.symm⟩
  -- ### the smooth lifts have the same monodromy, hence `Φ₀ - Ψ₀` is periodic
  have hΦ₀per : ∀ t : ℝ, Φ₀ (t + 2 * Real.pi) - Φ₀ t = Φ (2 * Real.pi) - Φ 0 := by
    intro t
    have h1 := hΦdiff (t + 2 * Real.pi)
    have h2 := hΦdiff t
    have h3 := hΦmono t
    linarith
  have hΨ₀per : ∀ t : ℝ, Ψ₀ (t + 2 * Real.pi) - Ψ₀ t = Ψ (2 * Real.pi) - Ψ 0 := by
    intro t
    have h1 := hΨdiff (t + 2 * Real.pi)
    have h2 := hΨdiff t
    have h3 := hΨmono t
    linarith
  refine ⟨fun t => Φ₀ t - Ψ₀ t, hΦ₀sm.sub hΨ₀sm, ?_, ?_⟩
  · intro t
    have h3 : Φ₀ (t + 2 * Real.pi) - Φ₀ t = Ψ₀ (t + 2 * Real.pi) - Ψ₀ t := by
      rw [hΦ₀per t, hΨ₀per t, hΦtot]
    linarith
  · intro t
    have hE : symmE γ t 0 = circleOf ((Φ₀ t : ℝ) : UnitAddCircle) := by
      rw [symmE_zero_eq γ hγ t, ← hΦ₀cls t]
    have hS : (star (symmD γ t 0)) ^ 2 = (circleOf ((Ψ₀ t : ℝ) : UnitAddCircle))⁻¹ := by
      rw [star_symmD_zero_sq γ t (hcurve_ne t), ← hΨ₀cls t]
    show circleOf ((Φ₀ t - Ψ₀ t : ℝ) : UnitAddCircle)
      = symmE γ t 0 * (star (symmD γ t 0)) ^ 2
    rw [hE, hS, circleOf_sub]

end Work.Drive
