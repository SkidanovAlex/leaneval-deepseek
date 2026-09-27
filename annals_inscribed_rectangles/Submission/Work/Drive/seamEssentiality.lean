import Mathlib
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.stripChartExt
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.classDatum
import Submission.Work.Drive.cappingProjCoords
import Submission.Work.Drive.cappingSpaceHomeoProj_confPiece
import Submission.Work.Drive.contDiffOn_chordUnitDir
import Submission.Work.Drive.projRot_profile_trans
import Submission.Work.Drive.mk2CLM

/-!
# The seam lift of the plane chart, and the essentiality of its class map

`Work.Drive.IsPlaneChart γ hγne Q` presents the capped plane `P = M ∪ cap` as a disk model
`Q : ℂ → CappingSpace`.  Its **strip clause** forces the value of `Q` on the outer annulus
`1/2 < ‖z‖ ≤ 1`, in particular on the boundary circle `‖z‖ = 1` (the *seam* `ℝP¹ ⊂ P` of the plane),
and the seam clause `Q (-z) = Q z` identifies antipodal boundary points.

The class map of a plane chart therefore restricts to a loop `θ ↦ [Q (e^{iθ})]` in `ℝP³` — the double of
the loop on the half-period — and its *essentiality* (the `ℤ/2` invariant `[P] ≠ 0 ∈ H₂(ℝ × ℝP³)`, the
paper's standing hypothesis) is exactly the statement that a lift of that loop to the unit sphere
`S³ ⊂ ℝ⁴` has **antipodal** endpoints:

> `V (-z) = c z • V z` with `c z < 0`.

This file proves that for an arbitrary continuous nonvanishing lift `V` of the chart's class map on the
circle, with no hypothesis beyond `IsPlaneChart` itself.  The content is a computation with the strip
parametrisation:

* the seam chord at the parameter `θ` has endpoints `exp (θ ± π/2)`;
* the chord at the *antipodal* parameter `θ + π` is the same chord with its two endpoints **exchanged**;
* exchanging the endpoints leaves the capping data `stripData` (radius, disk coordinate, doubled
  direction) untouched but **negates** the undoubled chord direction `chordUnitDir`, so the natural lift
  `confProjVecOf (stripHalf ·) ·` is negated;
* any other continuous nonvanishing lift differs from it by a continuous nonvanishing real factor, of
  constant sign on the connected circle, so it is negated as well.

This is the `hpar`/`hneg` input of `Work.Drive.exists_odd_classLift`
(`Submission/Work/Drive/oddClassLift.lean`), i.e. the essentiality input of the (B) half of the ends
clause of the counting route.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

noncomputable section

variable {γ : Circle → ℝ × ℝ}

/-! ## 1. Swapping the two chord endpoints: `stripData` is even, `stripHalf` is odd -/

/-- The complexified chord is antisymmetric in the ordered pair. -/
private lemma chordC_swap (γ : Circle → ℝ × ℝ) (a b : ℝ) :
    chordC γ (b, a) = - chordC γ (a, b) := by
  unfold chordC
  apply Complex.ext <;> simp

/-- The undoubled chord direction is **antisymmetric** in the ordered pair (it is the direction of an
*oriented* segment, so exchanging the endpoints negates it). -/
lemma chordUnitDir_swap (γ : Circle → ℝ × ℝ) (a b : ℝ) :
    chordUnitDir γ (b, a) = - chordUnitDir γ (a, b) := by
  unfold chordUnitDir
  rw [chordC_swap, norm_neg, neg_div]

/-- `stripData` is invariant under exchanging the two strip parameters. -/
lemma stripData_swap (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    stripData γ (mk2 (w 1) (w 0)) = stripData γ w := by
  simp only [stripData, mk2_apply_zero, mk2_apply_one]
  rw [muOrd_comm]

/-- `stripHalf` is negated by exchanging the two strip parameters, off the diagonal (where it is the
undoubled chord direction, which is oriented). -/
lemma stripHalf_swap (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2))
    (hw : Circle.exp (w 0) ≠ Circle.exp (w 1)) :
    stripHalf γ (mk2 (w 1) (w 0)) = - stripHalf γ w := by
  have h1 : Circle.exp ((mk2 (w 1) (w 0)) 0) ≠ Circle.exp ((mk2 (w 1) (w 0)) 1) := by
    simpa [mk2] using fun hc => hw hc.symm
  rw [stripHalf_of_ne h1, stripHalf_of_ne hw]
  simpa [mk2] using chordUnitDir_swap γ (w 0) (w 1)

/-- `stripData` depends on the parameters only through the two circle points. -/
lemma stripData_eq_of_exp_eq {w w' : EuclideanSpace ℝ (Fin 2)}
    (h0 : Circle.exp (w 0) = Circle.exp (w' 0)) (h1 : Circle.exp (w 1) = Circle.exp (w' 1)) :
    stripData γ w = stripData γ w' := by
  simp only [stripData, h0, h1]

/-- `stripHalf` depends on the parameters only through the two circle points. -/
lemma stripHalf_eq_of_exp_eq {w w' : EuclideanSpace ℝ (Fin 2)}
    (h0 : Circle.exp (w 0) = Circle.exp (w' 0)) (h1 : Circle.exp (w 1) = Circle.exp (w' 1)) :
    stripHalf γ w = stripHalf γ w' := by
  by_cases h : Circle.exp (w 0) = Circle.exp (w 1)
  · have h' : Circle.exp (w' 0) = Circle.exp (w' 1) := by rw [← h0, ← h1]; exact h
    rw [stripHalf_of_eq h, stripHalf_of_eq h']
  · have h' : ¬ (Circle.exp (w' 0) = Circle.exp (w' 1)) := fun hc => h (by rw [h0, h1]; exact hc)
    rw [stripHalf_of_ne h, stripHalf_of_ne h']
    unfold chordUnitDir chordC
    rw [h0, h1]

/-! ## 2. `confProjVecOf` is odd in its first argument -/

lemma c₁_neg_ext (v : Eucl 3) : c₁ (-v) = - c₁ v := by
  simp only [c₁, PiLp.neg_apply]
  push_cast
  ring

lemma c₂_neg_ext (v : Eucl 3) : c₂ (-v) = - c₂ v := by
  simp only [c₂, PiLp.neg_apply]
  push_cast
  ring

/-- `confProjVecOf` is odd in its first argument: the two square roots of a doubled direction give
opposite sphere lifts, hence the same projective point. -/
lemma confProjVecOf_neg_u (u d : ℂ) : confProjVecOf (-u) d = - confProjVecOf u d := by
  have h1 : c₁ (confProjVecOf (-u) d) = c₁ (-(confProjVecOf u d)) := by
    rw [c₁_confProjVecOf, c₁_neg_ext, c₁_confProjVecOf]
    ring
  have h2 : c₂ (confProjVecOf (-u) d) = c₂ (-(confProjVecOf u d)) := by
    rw [c₂_confProjVecOf, c₂_neg_ext, c₂_confProjVecOf, star_neg]
    ring
  rw [← ofComplex_c₁_c₂ (confProjVecOf (-u) d), ← ofComplex_c₁_c₂ (-(confProjVecOf u d)),
    h1, h2]

/-! ## 3. The seam parameters and the seam lift -/

/-- The strip parameters of the seam chord at the angular parameter `θ`: the chord of `γ` between the
parameters `θ ± π/2`.  Its opening is `π`, i.e. half of the period. -/
def seamParam (θ : ℝ) : EuclideanSpace ℝ (Fin 2) := mk2 (θ + Real.pi / 2) (θ - Real.pi / 2)

@[simp] lemma seamParam_zero (θ : ℝ) : seamParam θ 0 = θ + Real.pi / 2 := rfl

@[simp] lemma seamParam_one (θ : ℝ) : seamParam θ 1 = θ - Real.pi / 2 := rfl

/-- The two endpoints of a seam chord are distinct: the two parameters differ by `π`, which is not a
multiple of `2π`. -/
lemma seamParam_exp_ne (θ : ℝ) : Circle.exp (seamParam θ 0) ≠ Circle.exp (seamParam θ 1) := by
  rw [seamParam_zero, seamParam_one]
  intro hc
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hc
  have h2 : (2 * m : ℤ) = 1 := by
    have h3 : ((2 * m : ℤ) : ℝ) = 1 := by
      push_cast
      have h4 : (m : ℝ) * (2 * Real.pi) = Real.pi := by linarith
      nlinarith [Real.pi_pos]
    exact_mod_cast h3
  omega

/-- **The seam lift**: the sphere lift of the class of the seam chord at the parameter `θ`, built from
the undoubled chord direction `stripHalf` and the normalised midpoint `(stripData ·).2.1`. -/
def seamLift (γ : Circle → ℝ × ℝ) (θ : ℝ) : Eucl 3 :=
  confProjVecOf (stripHalf γ (seamParam θ)) ((stripData γ (seamParam θ)).2.1)

/-- The seam lift never vanishes (its first argument is a unit complex number). -/
lemma seamLift_ne_zero (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (θ : ℝ) : seamLift γ θ ≠ 0 :=
  confProjVecOf_ne_zero_of_norm_eq_one (stripHalf_norm hγ (seamParam θ)) _

/-- The capping data of the seam chord is unchanged under the antipodal shift of the parameter. -/
lemma stripData_seamParam_add_pi (γ : Circle → ℝ × ℝ) (θ : ℝ) :
    stripData γ (seamParam (θ + Real.pi)) = stripData γ (seamParam θ) := by
  have h0 : Circle.exp ((seamParam (θ + Real.pi)) 0) = Circle.exp ((seamParam θ) 1) := by
    rw [seamParam_zero, seamParam_one]
    rw [show θ + Real.pi + Real.pi / 2 = (θ - Real.pi / 2) + 2 * Real.pi by ring,
      Circle.exp_add, Circle.exp_two_pi, mul_one]
  have h1 : Circle.exp ((seamParam (θ + Real.pi)) 1) = Circle.exp ((seamParam θ) 0) := by
    rw [seamParam_zero, seamParam_one]
    rw [show θ + Real.pi - Real.pi / 2 = θ + Real.pi / 2 by ring]
  rw [stripData_eq_of_exp_eq (w := seamParam (θ + Real.pi))
      (w' := mk2 ((seamParam θ) 1) ((seamParam θ) 0)) h0 h1,
    stripData_swap]

/-- The halving of the seam chord is negated under the antipodal shift of the parameter. -/
lemma stripHalf_seamParam_add_pi (γ : Circle → ℝ × ℝ) (θ : ℝ) :
    stripHalf γ (seamParam (θ + Real.pi)) = - stripHalf γ (seamParam θ) := by
  have h0 : Circle.exp ((seamParam (θ + Real.pi)) 0) = Circle.exp ((seamParam θ) 1) := by
    rw [seamParam_zero, seamParam_one]
    rw [show θ + Real.pi + Real.pi / 2 = (θ - Real.pi / 2) + 2 * Real.pi by ring,
      Circle.exp_add, Circle.exp_two_pi, mul_one]
  have h1 : Circle.exp ((seamParam (θ + Real.pi)) 1) = Circle.exp ((seamParam θ) 0) := by
    rw [seamParam_zero, seamParam_one]
    rw [show θ + Real.pi - Real.pi / 2 = θ + Real.pi / 2 by ring]
  have hne : Circle.exp ((seamParam θ) 0) ≠ Circle.exp ((seamParam θ) 1) := seamParam_exp_ne θ
  rw [stripHalf_eq_of_exp_eq (w := seamParam (θ + Real.pi))
      (w' := mk2 ((seamParam θ) 1) ((seamParam θ) 0)) h0 h1,
    stripHalf_swap _ _ hne]

/-- **The seam lift is odd under the antipodal shift**: this is the essentiality of the plane chart. -/
theorem seamLift_add_pi (γ : Circle → ℝ × ℝ) (θ : ℝ) :
    seamLift γ (θ + Real.pi) = - seamLift γ θ := by
  unfold seamLift
  rw [stripHalf_seamParam_add_pi, stripData_seamParam_add_pi, confProjVecOf_neg_u]

/-! ## 4. The class of the seam lift -/

/-- `Circle.exp` of the principal argument of a unit complex number is the number itself. -/
lemma circle_exp_arg_coe (z : ℂ) (hz : ‖z‖ = 1) :
    ((Circle.exp (Complex.arg z) : Circle) : ℂ) = z := by
  rw [Circle.coe_exp]
  have h : ‖z‖ * Complex.exp (Complex.arg z * Complex.I) = z := Complex.norm_mul_exp_arg_mul_I z
  rw [hz] at h
  simpa using h

/-- `classOfConf` computed with *any* square root of the doubled direction. -/
lemma classOfConf_eq_mk_confProjVecOf {d : ℂ} {hd : ‖d‖ ≤ 1} {η : UnitAddCircle} {u : ℂ}
    (hu : u ^ 2 = circleOf η) :
    classOfConf d hd η = Projectivization.mk ℝ (confProjVecOf u d)
      (confProjVecOf_ne_zero (norm_eq_one_of_sq_eq_circleOf hu) hd) := by
  rw [classOfConf_eq_mk]
  refine (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ?_
  rcases classDatum_eq_or_eq_neg_of_sq_eq (u := classRoot η) (u' := u)
    (by rw [classRoot_sq, ← hu]) with h | h
  · exact ⟨1, by rw [one_smul, h]⟩
  · exact ⟨-1, by rw [neg_one_smul, h, confProjVecOf_neg_u]⟩

/-- The undoubled seam direction is a square root of the doubled direction: `(stripHalf γ w) ^ 2` is
`circleOf` of the third capping coordinate. -/
lemma stripHalf_sq_circleOf (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (w : EuclideanSpace ℝ (Fin 2)) :
    (stripHalf γ w) ^ 2 = circleOf ((stripData γ w).2.2) := by
  rw [← circleOf_circOf (stripHalf γ w ^ 2)
    (by rw [norm_pow, stripHalf_norm hγ w]; norm_num), circOf_stripHalf_sq hγ w]

/-- **The class of the seam lift is the class of the chart at the same parameter.** -/
theorem cls_seamLift (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) (θ : ℝ) :
    Projectivization.mk ℝ (seamLift γ θ) (seamLift_ne_zero hγ θ)
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
    exact stripHalf_sq_circleOf hγ (seamParam θ)
  rw [hQ.2.1 z hlt hle, hsqrt,
    cls_stripChart_zero γ hγne (mk2 (Complex.arg z + Real.pi / 2) (Complex.arg z - Real.pi / 2))]
  change Projectivization.mk ℝ (seamLift γ θ) (seamLift_ne_zero hγ θ)
      = classOfConf ((stripData γ (mk2 (Complex.arg z + Real.pi / 2)
            (Complex.arg z - Real.pi / 2))).2.1) (confOf_snd_norm_le_one _)
          ((stripData γ (mk2 (Complex.arg z + Real.pi / 2) (Complex.arg z - Real.pi / 2))).2.2)
  refine Eq.trans ?_ (classOfConf_eq_mk_confProjVecOf (u := stripHalf γ (seamParam θ)) hu).symm
  refine (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨1, ?_⟩
  rw [one_smul, show (stripData γ (mk2 (Complex.arg z + Real.pi / 2)
          (Complex.arg z - Real.pi / 2))).2.1 = (stripData γ (seamParam θ)).2.1
      from congrArg (fun q => q.2.1) hdata]
  rfl

/-! ## 5. Continuity of the seam lift -/

/-- **The seam lift is continuous.**  Its two ingredients are the halving `stripHalf`, smooth off the
diagonal (and the seam parameters are never on the diagonal, `seamParam_exp_ne`), and the normalised
midpoint, smooth wherever the configuration point is nonzero (true by `hγne`). -/
lemma continuous_seamLift (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) : Continuous (seamLift γ) := by
  have hW : Continuous (seamParam : ℝ → EuclideanSpace ℝ (Fin 2)) := by
    unfold seamParam mk2
    fun_prop
  have hH : Continuous (fun θ : ℝ => stripHalf γ (seamParam θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    exact ((contDiffAt_stripHalf hγ (seamParam_exp_ne θ)).continuousAt).comp hW.continuousAt
  have hD : Continuous (fun θ : ℝ => (stripData γ (seamParam θ)).2.1) := by
    have hcont : Continuous (fun w : EuclideanSpace ℝ (Fin 2) => (stripData γ w).2.1) := by
      rw [continuous_iff_continuousAt]
      intro w
      exact (contMDiffAt_stripData_snd hγ (stripA_ne_zero hγne w)).continuousAt
    exact hcont.comp hW
  have hnorm : Continuous (fun θ : ℝ => ‖(stripData γ (seamParam θ)).2.1‖ ^ 2) := hD.norm.pow 2
  have hA : Continuous (fun θ : ℝ => stripHalf γ (seamParam θ)
      * (((Real.sqrt (1 - ‖(stripData γ (seamParam θ)).2.1‖ ^ 2 / 2) : ℝ) : ℂ))) :=
    hH.mul ((Complex.continuous_ofReal).comp
      (Real.continuous_sqrt.comp (continuous_const.sub (hnorm.div_const 2))))
  have hB : Continuous (fun θ : ℝ => star (stripHalf γ (seamParam θ))
      * (stripData γ (seamParam θ)).2.1 / ((Real.sqrt 2 : ℝ) : ℂ)) :=
    (hH.star.mul hD).div_const _
  refine (prpt_continuous_ofComplex hA hB).congr fun θ => ?_
  rfl

/-! ## 6. The essentiality of the plane chart -/

lemma circle_exp_pi_coe : ((Circle.exp Real.pi : Circle) : ℂ) = -1 := by
  rw [Circle.coe_exp, Complex.exp_pi_mul_I]

lemma circle_exp_zero_coe : ((Circle.exp (0 : ℝ) : Circle) : ℂ) = 1 := by
  rw [Circle.coe_exp]
  simp

/-- **The essentiality of a plane chart.**  For any continuous nonvanishing lift `V` of the chart's
class map on the boundary circle, the parallelism factor `V (-z) = c z • V z` is **negative** at
`z = 1`: the seam loop of the chart is the nontrivial loop of `π₁(ℝP³) = ℤ/2`.

This is the `hneg` hypothesis of `Work.Drive.exists_odd_classLift` (`oddClassLift.lean`), i.e. the
essentiality input of the (B) half of the ends clause of the counting route. -/
theorem exists_neg_parallelism_of_planeChart
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (V : ℂ → Eucl 3) (hVne : ∀ z : ℂ, ‖z‖ = 1 → V z ≠ 0)
    (hVcont : ContinuousOn V {z : ℂ | ‖z‖ = 1})
    (hVcls : ∀ z (hz : ‖z‖ = 1),
      Projectivization.mk ℝ (V z) (hVne z hz) = (cappingSpaceHomeoProj (Q z)).2) :
    (∀ z : ℂ, ‖z‖ = 1 → ∃ c : ℝ, V (-z) = c • V z) ∧
      ∃ c : ℝ, V (-1) = c • V 1 ∧ c < 0 := by
  set W : ℝ → Eucl 3 := fun θ => V ((Circle.exp θ : Circle) : ℂ) with hWdef
  have hnorm (θ : ℝ) : ‖((Circle.exp θ : Circle) : ℂ)‖ = 1 := Circle.norm_coe (Circle.exp θ)
  have hcircle : Continuous (fun θ : ℝ => ((Circle.exp θ : Circle) : ℂ)) :=
    continuous_subtype_val.comp Circle.exp.continuous
  have hWcont : Continuous W := hVcont.comp_continuous hcircle hnorm
  have hWne : ∀ θ, W θ ≠ 0 := fun θ => hVne _ (hnorm θ)
  have hWcls : ∀ θ, Projectivization.mk ℝ (W θ) (hWne θ)
      = (cappingSpaceHomeoProj (Q ((Circle.exp θ : Circle) : ℂ))).2 :=
    fun θ => hVcls _ (hnorm θ)
  have hseamcont : Continuous (seamLift γ) := continuous_seamLift hγ hγne
  have hseamne : ∀ θ, seamLift γ θ ≠ 0 := seamLift_ne_zero hγ
  -- the parallelism
  have hpar : ∀ z : ℂ, ‖z‖ = 1 → ∃ c : ℝ, V (-z) = c • V z := by
    intro z hz
    have hz' : ‖-z‖ = 1 := by simpa using hz
    have hmk : Projectivization.mk ℝ (V (-z)) (hVne (-z) hz')
        = Projectivization.mk ℝ (V z) (hVne z hz) := by
      rw [hVcls (-z) hz', hVcls z hz, hQ.2.2.1 z hz]
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ (V (-z)) (V z)
      (hVne (-z) hz') (hVne z hz)).mp hmk
    exact ⟨a, ha.symm⟩
  -- the explicit lift and the comparison factor
  have hpar' : ∀ θ, ∃ a : ℝ, W θ = a • seamLift γ θ := by
    intro θ
    have hmk : Projectivization.mk ℝ (W θ) (hWne θ)
        = Projectivization.mk ℝ (seamLift γ θ) (hseamne θ) := by
      rw [hWcls θ, cls_seamLift hγ hγne hQ θ]
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
  -- the parallelism factor of the explicit lift is `-1`
  have hexp : seamLift γ Real.pi = - seamLift γ 0 := by
    rw [show Real.pi = 0 + Real.pi from by ring]
    exact seamLift_add_pi γ 0
  have hWrel : W Real.pi = (-(α Real.pi / α 0)) • W 0 := by
    have h0 : W 0 = α 0 • seamLift γ 0 := hαprop 0
    rw [hαprop Real.pi, hexp, h0, smul_neg, neg_smul, smul_smul]
    rw [div_mul_cancel₀ (α Real.pi) (hαne 0)]
  -- the sign of `α` is constant on `[0, π]`
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
