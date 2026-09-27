import Mathlib
import Submission.Work.Drive.planeChartCurve
import Submission.Work.Drive.seamEssentiality

/-!
# The essentiality of a plane chart needs no smoothness of the curve

`Work.Drive.exists_neg_parallelism_of_planeChart` (`seamEssentiality.lean`) proves that the class map
of a plane chart `Q` of `γ` is *essential*: for any continuous nonvanishing lift `V` of that class map
on the boundary circle one has `V (-z) = c z • V z` with `c (-1) < 0`.  Its proof, however, is stated
for a **smooth embedding** `γ`.

The computation never uses the regularity of `γ`:

* the *halving* `stripHalf γ w = (γ (exp (w 0)) - γ (exp (w 1))) / ‖·‖` of the doubled chord
  direction is a unit complex number as soon as the two endpoints differ (**injectivity** of `γ`, not
  smoothness), and its square is `circleOf` of the capping direction by the purely complex-algebraic
  identity `Work.Drive.circleOf_arg_div_pi`;
* the comparison factor of two lifts `V` and `seamLift γ` is `θ ↦ inner (W θ) (seamLift γ θ)/‖·‖²`,
  so continuity of `seamLift γ` along the seam parametrisation `seamParam θ = (θ + π/2, θ - π/2)`
  suffices — and that only needs **continuity** of `γ`, which the chart itself supplies
  (`Work.Drive.continuous_curve_of_isPlaneChart`).

This file provides these two forms (`Work.Drive.stripHalf_norm_of_injective`,
`Work.Drive.cls_seamLift_of_injective`, `Work.Drive.continuous_seamLift_of_injective`, …) and the
target `Work.Drive.exists_neg_parallelism_of_planeChart_of_isPlaneChart`, the same conclusion for a
merely injective curve avoiding the origin.  The statement is the one a colleague consumes: only
`Function.Injective γ` and `∀ x, γ x ≠ 0` are assumed.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

noncomputable section

variable {γ : Circle → ℝ × ℝ}

/-! ## 1. The halving of the chord direction, from injectivity alone -/

/-- The chord `γ (exp p.1) - γ (exp p.2)` is nonzero as soon as the two circle points differ — only
injectivity of `γ` enters. -/
lemma chordC_ne_zero_of_injective (hγinj : Function.Injective γ) {p : ℝ × ℝ}
    (hp : Circle.exp p.1 ≠ Circle.exp p.2) : chordC γ p ≠ 0 := by
  intro h
  have h' : toC (γ (Circle.exp p.1) - γ (Circle.exp p.2)) = 0 := by
    rw [← chordC_eq_toC]; exact h
  exact hp (hγinj (sub_eq_zero.mp (toC_eq_zero_iff.mp h')))

/-- The halving of the doubled chord direction has unit norm, from injectivity alone. -/
lemma stripHalf_norm_of_injective (hγinj : Function.Injective γ)
    (w : EuclideanSpace ℝ (Fin 2)) : ‖stripHalf γ w‖ = 1 := by
  unfold stripHalf
  split_ifs with h
  · simp
  · rw [chordUnitDir, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr (chordC_ne_zero_of_injective hγinj h))]

/-- `circOf` of the square of the halving is the doubled direction of the configuration point, from
injectivity alone. -/
lemma circOf_stripHalf_sq_of_injective (hγinj : Function.Injective γ)
    (w : EuclideanSpace ℝ (Fin 2)) :
    circOf (stripHalf γ w ^ 2)
        (by rw [norm_pow, stripHalf_norm_of_injective hγinj w]; norm_num)
      = (stripData γ w).2.2 := by
  refine circleOf_injective ?_
  rw [circleOf_circOf, stripData_thd]
  unfold stripHalf
  split_ifs with h
  · have hdir : Submission.Collision.dirC (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1))) = 0 := by
      rw [sub_eq_zero.mpr (congrArg γ h), dirC_zero]
    rw [hdir, circleOf_zero]
    norm_num
  · rw [chordUnitDir]
    exact (circleOf_arg_div_pi (chordC γ (w 0, w 1))
      (chordC_ne_zero_of_injective hγinj h)).symm

/-- The square of the halving is `circleOf` of the doubled direction, from injectivity alone. -/
lemma stripHalf_sq_circleOf_of_injective (hγinj : Function.Injective γ)
    (w : EuclideanSpace ℝ (Fin 2)) :
    (stripHalf γ w) ^ 2 = circleOf ((stripData γ w).2.2) := by
  rw [← circleOf_circOf (stripHalf γ w ^ 2)
    (by rw [norm_pow, stripHalf_norm_of_injective hγinj w]; norm_num),
    circOf_stripHalf_sq_of_injective hγinj w]

/-- The seam lift never vanishes, from injectivity alone. -/
lemma seamLift_ne_zero_of_injective (hγinj : Function.Injective γ) (θ : ℝ) :
    seamLift γ θ ≠ 0 :=
  confProjVecOf_ne_zero_of_norm_eq_one (stripHalf_norm_of_injective hγinj (seamParam θ)) _

/-! ## 2. Continuity of the seam lift from continuity of the curve -/

/-- Continuity of `θ ↦ γ (exp (θ + c))` from continuity of `γ`. -/
lemma continuous_exp_shift_of_continuous (hγcont : Continuous γ) (c : ℝ) :
    Continuous (fun θ : ℝ => γ (Circle.exp (θ + c))) :=
  hγcont.comp (Circle.exp.continuous.comp (continuous_id.add continuous_const))

/-- The complexified seam chord `θ ↦ chordC γ (seamParam θ)` is continuous. -/
lemma continuous_seamChord (hγcont : Continuous γ) :
    Continuous (fun θ : ℝ => chordC γ (seamParam θ 0, seamParam θ 1)) := by
  have h0 : Continuous (fun θ : ℝ => γ (Circle.exp (θ + Real.pi / 2))) :=
    continuous_exp_shift_of_continuous hγcont (Real.pi / 2)
  have h1 : Continuous (fun θ : ℝ => γ (Circle.exp (θ - Real.pi / 2))) :=
    hγcont.comp (Circle.exp.continuous.comp (continuous_id.sub continuous_const))
  have hsub : Continuous (fun θ : ℝ =>
      γ (Circle.exp (θ + Real.pi / 2)) - γ (Circle.exp (θ - Real.pi / 2))) := h0.sub h1
  have hEq : (fun θ : ℝ => chordC γ (seamParam θ 0, seamParam θ 1))
      = fun θ : ℝ => (((γ (Circle.exp (θ + Real.pi / 2))
            - γ (Circle.exp (θ - Real.pi / 2))).1 : ℂ)
          + ((γ (Circle.exp (θ + Real.pi / 2))
            - γ (Circle.exp (θ - Real.pi / 2))).2 : ℂ) * Complex.I) := by
    funext θ
    simp only [chordC, seamParam_zero, seamParam_one]
    exact complex_mk_eq_add_mul_I _ _
  rw [hEq]
  exact (Complex.continuous_ofReal.comp hsub.fst).add
    ((Complex.continuous_ofReal.comp hsub.snd).mul continuous_const)

/-- The seam midpoint `θ ↦ stripMid γ (seamParam θ)` is continuous. -/
lemma continuous_seamMid (hγcont : Continuous γ) :
    Continuous (fun θ : ℝ => stripMid γ (seamParam θ)) := by
  have h0 : Continuous (fun θ : ℝ => γ (Circle.exp (θ + Real.pi / 2))) :=
    continuous_exp_shift_of_continuous hγcont (Real.pi / 2)
  have h1 : Continuous (fun θ : ℝ => γ (Circle.exp (θ - Real.pi / 2))) :=
    hγcont.comp (Circle.exp.continuous.comp (continuous_id.sub continuous_const))
  have hsum : Continuous (fun θ : ℝ =>
      γ (Circle.exp (θ + Real.pi / 2)) + γ (Circle.exp (θ - Real.pi / 2))) := h0.add h1
  have hEq : (fun θ : ℝ => stripMid γ (seamParam θ))
      = fun θ : ℝ => (γ (Circle.exp (θ + Real.pi / 2))
          + γ (Circle.exp (θ - Real.pi / 2))) / 2 := by
    funext θ
    simp only [stripMid, seamParam_zero, seamParam_one]
  rw [hEq]
  exact hsum.div_const 2

/-- The disk coordinate of the configuration point along the seam is continuous. -/
lemma continuous_seamStripD (hγne : ∀ x : Circle, γ x ≠ 0) (hγcont : Continuous γ) :
    Continuous (fun θ : ℝ => (stripData γ (seamParam θ)).2.1) := by
  have hmid := continuous_seamMid hγcont
  have hchord := continuous_seamChord hγcont
  have hnum : Continuous (fun θ : ℝ => (((stripMid γ (seamParam θ)).1 : ℂ)
      + ((stripMid γ (seamParam θ)).2 : ℂ) * Complex.I)) :=
    (Complex.continuous_ofReal.comp hmid.fst).add
      ((Complex.continuous_ofReal.comp hmid.snd).mul continuous_const)
  have hR : Continuous (fun θ : ℝ => stripR γ (seamParam θ)) := by
    have hA : Continuous (fun θ : ℝ => stripA γ (seamParam θ)) := by
      have hEq : (fun θ : ℝ => stripA γ (seamParam θ))
          = fun θ : ℝ => (stripMid γ (seamParam θ)).1 ^ 2 + (stripMid γ (seamParam θ)).2 ^ 2
              + ‖chordC γ (seamParam θ 0, seamParam θ 1)‖ ^ 2 := by
        funext θ
        simp only [stripA, stripChord, Complex.normSq_eq_norm_sq]
      rw [hEq]
      exact ((hmid.fst.pow 2).add (hmid.snd.pow 2)).add (hchord.norm.pow 2)
    exact Real.continuous_sqrt.comp hA
  have hden : Continuous (fun θ : ℝ => ((stripR γ (seamParam θ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hR
  have hne : ∀ θ : ℝ, ((stripR γ (seamParam θ) : ℝ) : ℂ) ≠ 0 := by
    intro θ
    have h := stripData_pos hγne (seamParam θ)
    rw [stripData_fst] at h
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt h)
  have hfun : (fun θ : ℝ => (stripData γ (seamParam θ)).2.1)
      = fun θ : ℝ => (((stripMid γ (seamParam θ)).1 : ℂ)
          + ((stripMid γ (seamParam θ)).2 : ℂ) * Complex.I)
          / ((stripR γ (seamParam θ) : ℝ) : ℂ) := by
    funext θ
    simp only [stripData_snd, stripD]
  rw [hfun]
  exact hnum.div hden hne

/-- The halving of the chord direction along the seam is continuous (injectivity supplies the
non-vanishing of the chord). -/
lemma continuous_seamStripHalf (hγinj : Function.Injective γ) (hγcont : Continuous γ) :
    Continuous (fun θ : ℝ => stripHalf γ (seamParam θ)) := by
  have hchord := continuous_seamChord hγcont
  have hdiv : Continuous (fun θ : ℝ => chordC γ (seamParam θ 0, seamParam θ 1)
      / ((‖chordC γ (seamParam θ 0, seamParam θ 1)‖ : ℝ) : ℂ)) :=
    hchord.div (Complex.continuous_ofReal.comp hchord.norm) (fun θ => by
      rw [Complex.ofReal_ne_zero]
      exact norm_ne_zero_iff.mpr (chordC_ne_zero_of_injective hγinj (seamParam_exp_ne θ)))
  have h1 : Continuous (fun θ : ℝ => chordUnitDir γ (seamParam θ 0, seamParam θ 1)) :=
    hdiv.congr (fun θ => by rw [chordUnitDir])
  exact h1.congr (fun θ => (stripHalf_of_ne (seamParam_exp_ne θ)).symm)

/-- **The seam lift is continuous** as soon as `γ` is continuous and injective: this is the form of
`Work.Drive.continuous_seamLift` that the plane-chart hypothesis supplies. -/
lemma continuous_seamLift_of_injective (hγinj : Function.Injective γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγcont : Continuous γ) : Continuous (seamLift γ) := by
  have hu := continuous_seamStripHalf hγinj hγcont
  have hd := continuous_seamStripD hγne hγcont
  have hA : Continuous (fun θ : ℝ => stripHalf γ (seamParam θ)
      * (((Real.sqrt (1 - ‖(stripData γ (seamParam θ)).2.1‖ ^ 2 / 2) : ℝ) : ℂ))) :=
    hu.mul (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_const.sub ((hd.norm.pow 2).div_const 2))))
  have hB : Continuous (fun θ : ℝ => star (stripHalf γ (seamParam θ))
      * (stripData γ (seamParam θ)).2.1 / ((Real.sqrt 2 : ℝ) : ℂ)) :=
    (hu.star.mul hd).div_const _
  exact (prpt_continuous_ofComplex hA hB).congr (fun _ => rfl)

/-! ## 3. The class of the seam lift, from injectivity alone -/

/-- **The class of the seam lift is the class of the chart at the same parameter**, with the
smoothness hypothesis of `Work.Drive.cls_seamLift` replaced by injectivity of `γ`. -/
theorem cls_seamLift_of_injective (hγinj : Function.Injective γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) (θ : ℝ) :
    Projectivization.mk ℝ (seamLift γ θ) (seamLift_ne_zero_of_injective hγinj θ)
      = (cappingSpaceHomeoProj (Q ((Circle.exp θ : Circle) : ℂ))).2 := by
  set z : ℂ := ((Circle.exp θ : Circle) : ℂ) with hz
  have hz1 : ‖z‖ = 1 := by rw [hz]; exact Circle.norm_coe _
  have hlt : 1 / 2 < ‖z‖ := by rw [hz1]; norm_num
  have hle : ‖z‖ ≤ 1 := le_of_eq hz1
  have hsqrt : Real.sqrt (Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2) = Real.pi / 2 := by
    have h1 : Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2 = (Real.pi / 2) ^ 2 := by rw [hz1]; ring
    rw [h1, Real.sqrt_sq (by positivity)]
  have harg_eq : Circle.exp (Complex.arg z) = Circle.exp θ := by
    refine Subtype.ext ?_
    rw [circle_exp_arg_coe z hz1, ← hz]
  have hdata : stripData γ (mk2 (Complex.arg z + Real.pi / 2) (Complex.arg z - Real.pi / 2))
      = stripData γ (seamParam θ) := by
    refine stripData_eq_of_exp_eq ?_ ?_
    · change Circle.exp (Complex.arg z + Real.pi / 2) = Circle.exp (θ + Real.pi / 2)
      rw [Circle.exp_add, Circle.exp_add, harg_eq]
    · change Circle.exp (Complex.arg z - Real.pi / 2) = Circle.exp (θ - Real.pi / 2)
      rw [show Complex.arg z - Real.pi / 2 = Complex.arg z + (-(Real.pi / 2)) by ring,
        show θ - Real.pi / 2 = θ + (-(Real.pi / 2)) by ring,
        Circle.exp_add, Circle.exp_add, harg_eq]
  have hu : (stripHalf γ (seamParam θ)) ^ 2
      = circleOf ((stripData γ (mk2 (Complex.arg z + Real.pi / 2)
          (Complex.arg z - Real.pi / 2))).2.2) := by
    rw [hdata]
    exact stripHalf_sq_circleOf_of_injective hγinj (seamParam θ)
  rw [hQ.2.1 z hlt hle, hsqrt,
    cls_stripChart_zero γ hγne (mk2 (Complex.arg z + Real.pi / 2) (Complex.arg z - Real.pi / 2))]
  change Projectivization.mk ℝ (seamLift γ θ) (seamLift_ne_zero_of_injective hγinj θ)
      = classOfConf ((stripData γ (mk2 (Complex.arg z + Real.pi / 2)
            (Complex.arg z - Real.pi / 2))).2.1) (confOf_snd_norm_le_one _)
          ((stripData γ (mk2 (Complex.arg z + Real.pi / 2) (Complex.arg z - Real.pi / 2))).2.2)
  refine Eq.trans ?_ (classOfConf_eq_mk_confProjVecOf (u := stripHalf γ (seamParam θ)) hu).symm
  refine (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨1, ?_⟩
  rw [one_smul, show (stripData γ (mk2 (Complex.arg z + Real.pi / 2)
          (Complex.arg z - Real.pi / 2))).2.1 = (stripData γ (seamParam θ)).2.1
      from congrArg (fun q => q.2.1) hdata]
  rfl

/-! ## 4. The essentiality of a plane chart of an injective curve -/

/-- **The essentiality of a plane chart, with no smoothness of the curve.**  `IsPlaneChart` alone (with
injectivity of `γ` and `γ ≠ 0`) forces the class map of the chart to be the non-trivial loop of
`ℝP³ = P(Eucl 3)`: every continuous nonvanishing lift `V` of it is negated at the antipode, i.e.
`V (-1) = c • V 1` with `c < 0`. -/
theorem exists_neg_parallelism_of_planeChart_of_isPlaneChart {γ : Circle → ℝ × ℝ} (hγinj : Function.Injective γ) (hγne : ∀ x : Circle, γ x ≠ 0) {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) (V : ℂ → Eucl 3) (hVne : ∀ z : ℂ, ‖z‖ = 1 → V z ≠ 0) (hVcont : ContinuousOn V {z : ℂ | ‖z‖ = 1}) (hVcls : ∀ z (hz : ‖z‖ = 1), Projectivization.mk ℝ (V z) (hVne z hz) = (cappingSpaceHomeoProj (Q z)).2) : (∀ z : ℂ, ‖z‖ = 1 → ∃ c : ℝ, V (-z) = c • V z) ∧ ∃ c : ℝ, V (-1) = c • V 1 ∧ c < 0 := by
  have hγcont : Continuous γ := continuous_curve_of_isPlaneChart hQ
  set W : ℝ → Eucl 3 := fun θ => V ((Circle.exp θ : Circle) : ℂ) with hWdef
  have hnorm (θ : ℝ) : ‖((Circle.exp θ : Circle) : ℂ)‖ = 1 := Circle.norm_coe (Circle.exp θ)
  have hcircle : Continuous (fun θ : ℝ => ((Circle.exp θ : Circle) : ℂ)) :=
    continuous_subtype_val.comp Circle.exp.continuous
  have hWcont : Continuous W := hVcont.comp_continuous hcircle hnorm
  have hWne : ∀ θ, W θ ≠ 0 := fun θ => hVne _ (hnorm θ)
  have hWcls : ∀ θ, Projectivization.mk ℝ (W θ) (hWne θ)
      = (cappingSpaceHomeoProj (Q ((Circle.exp θ : Circle) : ℂ))).2 :=
    fun θ => hVcls _ (hnorm θ)
  have hseamcont : Continuous (seamLift γ) := continuous_seamLift_of_injective hγinj hγne hγcont
  have hseamne : ∀ θ, seamLift γ θ ≠ 0 := seamLift_ne_zero_of_injective hγinj
  -- the parallelism: two lifts of the same projective point differ by a real factor
  have hpar : ∀ z : ℂ, ‖z‖ = 1 → ∃ c : ℝ, V (-z) = c • V z := by
    intro z hz
    have hz' : ‖-z‖ = 1 := by simpa using hz
    have hmk : Projectivization.mk ℝ (V (-z)) (hVne (-z) hz')
        = Projectivization.mk ℝ (V z) (hVne z hz) := by
      rw [hVcls (-z) hz', hVcls z hz, hQ.2.2.1 z hz]
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ (V (-z)) (V z)
      (hVne (-z) hz') (hVne z hz)).mp hmk
    exact ⟨a, ha.symm⟩
  -- the comparison with the explicit seam lift
  have hpar' : ∀ θ, ∃ a : ℝ, W θ = a • seamLift γ θ := by
    intro θ
    have hmk : Projectivization.mk ℝ (W θ) (hWne θ)
        = Projectivization.mk ℝ (seamLift γ θ) (hseamne θ) := by
      rw [hWcls θ, cls_seamLift_of_injective hγinj hγne hQ θ]
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ (W θ) (seamLift γ θ)
      (hWne θ) (hseamne θ)).mp hmk
    exact ⟨a, ha.symm⟩
  set α : ℝ → ℝ := fun θ => inner ℝ (W θ) (seamLift γ θ) / ‖seamLift γ θ‖ ^ 2 with hαdef
  have hαprop : ∀ θ, W θ = α θ • seamLift γ θ := by
    intro θ
    obtain ⟨a, ha⟩ := hpar' θ
    have hS : ‖seamLift γ θ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (hseamne θ))
    have hinner : inner ℝ (W θ) (seamLift γ θ) = a * ‖seamLift γ θ‖ ^ 2 := by
      rw [ha, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hαθ : α θ = a := by
      rw [hαdef]
      simp only
      rw [hinner, mul_div_cancel_right₀ _ hS]
    rw [hαθ]
    exact ha
  have hαcont : Continuous α := by
    rw [hαdef]
    exact (Continuous.inner hWcont hseamcont).div (hseamcont.norm.pow 2)
      (fun θ => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hseamne θ)))
  have hαne : ∀ θ, α θ ≠ 0 := by
    intro θ h0
    have h1 : W θ = α θ • seamLift γ θ := hαprop θ
    rw [h0, zero_smul] at h1
    exact hWne θ h1
  -- the explicit lift is odd, so the comparison factor changes sign at the antipode
  have hexp : seamLift γ Real.pi = - seamLift γ 0 := by
    rw [show Real.pi = 0 + Real.pi from by ring]
    exact seamLift_add_pi γ 0
  have hWrel : W Real.pi = (-(α Real.pi / α 0)) • W 0 := by
    have h0 : W 0 = α 0 • seamLift γ 0 := hαprop 0
    rw [hαprop Real.pi, hexp, h0, smul_neg, neg_smul, smul_smul]
    rw [div_mul_cancel₀ (α Real.pi) (hαne 0)]
  have hsign : 0 < α Real.pi / α 0 := by
    have hmem0 : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_refl 0, Real.pi_pos.le⟩
    have hmemπ : Real.pi ∈ Set.Icc 0 Real.pi := ⟨Real.pi_pos.le, le_refl _⟩
    rcases prpt_sign_const (isPreconnected_Icc : IsPreconnected (Set.Icc (0 : ℝ) Real.pi))
      hαcont.continuousOn (fun t _ => hαne t) with hpos | hneg
    · exact div_pos (hpos _ hmemπ) (hpos _ hmem0)
    · exact div_pos_of_neg_of_neg (hneg _ hmemπ) (hneg _ hmem0)
  refine ⟨hpar, -(α Real.pi / α 0), ?_, by linarith⟩
  rw [show (-1 : ℂ) = ((Circle.exp Real.pi : Circle) : ℂ) from circle_exp_pi_coe.symm,
    show (1 : ℂ) = ((Circle.exp (0 : ℝ) : Circle) : ℂ) from circle_exp_zero_coe.symm]
  exact hWrel

end

end Work.Drive
