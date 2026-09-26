import Mathlib
import Submission.Work.SphereJordan.tgtUpPC_isSimple
import Submission.Work.SphereJordan.srcBranches
import Submission.Work.SphereJordan.annulusSourceSpans
import Submission.Work.Smooth.SphereJordan.annulusInterpolation
import Submission.Work.Smooth.SphereJordan.ballHomeo_of_circleHomeo
import Submission.Work.SphereJordan.annulusInnerReparam

/-!
# The two-cuts assembly of the planar annulus theorem

Given two plane Schoenflies discs `T_up`, `T_dn` of the two four-arc curves `tgtUpB`, `tgtDnB`
whose closures tile the annulus `annulus S` and meet in the two crosscuts, we assemble a
continuous injection `G : 𝔻 → 𝔻` fixing `∂𝔻` pointwise with `G` of the inner circle contained in
`γ`, and apply `Work.SphereJordan.annulusInnerReparam`.

The model annulus `{1/2 ≤ ‖z‖ ≤ 1}` is glued to the target annulus `annulus S` by matching the
boundary parameters of the source maps `Ψu, Ψd` (from `Work.SphereJordan.annulusSourceSpans`) with
those of the target boundary curves `tgtUpB`, `tgtDnB`.
-/

open Set

namespace Work.SphereJordan.TwoCutsAsm

/-- `perPt` is the identity on one period `[0, 2π)`.  (Copied here, together with the rest of this
module, from `Submission.Work.SphereJordan.twoCutsAssembly` so that the two-cuts assembly is
available inside the cone of `Submission.Work.Smooth.SphereJordan.coreAuxTwoCuts`.) -/
theorem perPt_eq_self {τ : ℝ} (h0 : 0 ≤ τ) (h2 : τ < 2 * Real.pi) :
    Work.Smooth.SphereJordan.perPt τ = τ := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hf : ⌊τ / (2 * Real.pi)⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨div_nonneg h0 hpos.le, by rw [div_lt_one hpos]; exact h2⟩
  unfold Work.Smooth.SphereJordan.perPt
  rw [hf]
  norm_num

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## Elementary facts about `circlePoint`, and the angle of `cutDir S` -/

theorem circlePoint_cp_add (a b : ℝ) :
    ((Work.Smooth.SphereJordan.circlePoint (a + b) : Work.Smooth.SphereJordan.Disc) : ℂ) =
      ((Work.Smooth.SphereJordan.circlePoint a : Work.Smooth.SphereJordan.Disc) : ℂ) *
      ((Work.Smooth.SphereJordan.circlePoint b : Work.Smooth.SphereJordan.Disc) : ℂ) := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe,
    Work.Smooth.Jordan.circlePoint_coe, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem circlePoint_cp_norm (a : ℝ) :
    ‖((Work.Smooth.SphereJordan.circlePoint a : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

theorem circlePoint_cp_neg (a : ℝ) :
    -((Work.Smooth.SphereJordan.circlePoint a : Work.Smooth.SphereJordan.Disc) : ℂ) =
      ((Work.Smooth.SphereJordan.circlePoint (a + Real.pi) :
        Work.Smooth.SphereJordan.Disc) : ℂ) := by
  rw [circlePoint_cp_add, Work.SphereJordan.cp_pi]
  ring

theorem exp_pi_mul_I : Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) = -1 :=
  Work.SphereJordan.cp_pi

theorem exists_cutAngle (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ α : ℝ, ((Work.Smooth.SphereJordan.circlePoint α : Work.Smooth.SphereJordan.Disc) : ℂ) =
      Work.Smooth.SphereJordan.cutDir S := by
  obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq
    ⟨Work.Smooth.SphereJordan.cutDir S, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq (Work.Smooth.SphereJordan.norm_cutDir S)⟩
    (Work.Smooth.SphereJordan.norm_cutDir S)
  exact ⟨θ, congrArg Subtype.val hθ⟩

/-- A parameter of the point `cutDir S` on the boundary circle. -/
def cutAng (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : ℝ := Classical.choose (exists_cutAngle S)

theorem cutAng_spec (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ((Work.Smooth.SphereJordan.circlePoint (cutAng S) : Work.Smooth.SphereJordan.Disc) : ℂ) =
      Work.Smooth.SphereJordan.cutDir S := Classical.choose_spec (exists_cutAngle S)

/-- The "upper outer" boundary point of the model disc at arc parameter `x ∈ [0,1]`:
`e^{i(cutAng S + π x)}`.  It equals `srcOuterUp S x`. -/
def outerPt (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) : ℂ :=
  Complex.exp (((cutAng S + Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The "lower outer" boundary point: `e^{i(cutAng S + π + π x)}`. -/
def outerPtDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) : ℂ :=
  Complex.exp (((cutAng S + Real.pi + Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The "upper inner" point of the model disc at angle parameter `θ ∈ [0,π]`. -/
def innerPtUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) : ℂ :=
  (1 / 2 : ℂ) * Complex.exp (((cutAng S + θ : ℝ) : ℂ) * Complex.I)

/-- The "lower inner" point of the model disc at angle parameter `θ ∈ [0,π]`: the point
`(1/2) e^{i(cutAng S - π + θ)}`, which runs from `-cutDir S/2` to `cutDir S/2`. -/
def innerPtDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) : ℂ :=
  (1 / 2 : ℂ) * Complex.exp (((cutAng S - Real.pi + θ : ℝ) : ℂ) * Complex.I)

theorem neg_exp_eq (a : ℝ) :
    -Complex.exp ((a : ℂ) * Complex.I) =
      Complex.exp (((a + Real.pi : ℝ) : ℂ) * Complex.I) := by
  have h1 : Complex.exp (((a + Real.pi : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((a : ℂ) * Complex.I) * Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, exp_pi_mul_I]
  ring

theorem outerPt_eq_src (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    outerPt S x = Work.Smooth.SphereJordan.srcOuterUp S x := by
  rw [Work.SphereJordan.srcOuterUp_cp, outerPt, ← cutAng_spec S, Work.Smooth.Jordan.circlePoint_coe,
    Work.Smooth.Jordan.circlePoint_coe, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem outerPtDn_eq_src (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    outerPtDn S x = Work.Smooth.SphereJordan.srcOuterDn S x := by
  unfold outerPtDn Work.Smooth.SphereJordan.srcOuterDn
  rw [← cutAng_spec S, Work.Smooth.Jordan.circlePoint_coe]
  rw [neg_exp_eq (cutAng S), ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The source data of `annulusSourceSpans` -/

/-- The two source-side spanning discs `Ψ_up`, `Ψ_dn` of the model half-annuli. -/
structure SourceData (S : Work.Smooth.Jordan.PlaneSchoenflies γ) where
  Ψu : C(Work.Smooth.SphereJordan.Disc, ℂ)
  Ψd : C(Work.Smooth.SphereJordan.Disc, ℂ)
  inju : Function.Injective Ψu
  injd : Function.Injective Ψd
  bdu : ∀ τ : ℝ, Ψu (Work.Smooth.SphereJordan.circlePoint τ) =
    Work.Smooth.SphereJordan.srcUpB S τ
  bdd : ∀ τ : ℝ, Ψd (Work.Smooth.SphereJordan.circlePoint τ) =
    Work.Smooth.SphereJordan.srcDnB S τ
  union : Set.range ⇑Ψu ∪ Set.range ⇑Ψd =
    Metric.closedBall (0 : ℂ) 1 \ Metric.ball (0 : ℂ) (1 / 2)
  meet : Set.range ⇑Ψu ∩ Set.range ⇑Ψd =
    ({z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
        z = (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S} ∪
     {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
        z = -((σ : ℂ) * Work.Smooth.SphereJordan.cutDir S)})

theorem exists_sourceData (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Nonempty (SourceData S) := by
  obtain ⟨Ψu, Ψd, h1, h2, h3, h4, h5, h6⟩ := Work.SphereJordan.annulusSourceSpans h S
  exact ⟨Ψu, Ψd, h1, h2, h3, h4, h5, h6⟩

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

/-- The upper half-annulus of the model disc, as the range of `Ψu`. -/
def Hup (D : SourceData S) : Set ℂ := Set.range ⇑D.Ψu

/-- The lower half-annulus of the model disc, as the range of `Ψd`. -/
def Hdn (D : SourceData S) : Set ℂ := Set.range ⇑D.Ψd

/-- The model annulus `{1/2 ≤ ‖z‖ ≤ 1}`. -/
def Msub : Set ℂ := {z : ℂ | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1}

/-- The inner disc `{‖z‖ ≤ 1/2}`. -/
def Dsub : Set ℂ := {z : ℂ | ‖z‖ ≤ 1 / 2}

/-- The inner circle `{‖z‖ = 1/2}`. -/
def Csub : Set ℂ := {z : ℂ | ‖z‖ = 1 / 2}

theorem Hup_union_Hdn (D : SourceData S) : Hup D ∪ Hdn D = Msub := by
  rw [Hup, Hdn, D.union, Msub, Metric.closedBall, Metric.ball]
  ext z
  simp only [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
    Set.mem_ofPred_eq, not_lt]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem Hup_inter_Hdn (D : SourceData S) : Hup D ∩ Hdn D =
    ({z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
        z = (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S} ∪
     {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
        z = -((σ : ℂ) * Work.Smooth.SphereJordan.cutDir S)}) := by
  rw [Hup, Hdn]
  exact D.meet

/-- The homeomorphism `𝔻 ≃ₜ Hup` given by `Ψu`. -/
def ΨuEquiv (D : SourceData S) : Work.Smooth.SphereJordan.Disc ≃ ↥(Hup D) :=
  Equiv.ofBijective (fun z => (⟨D.Ψu z, ⟨z, rfl⟩⟩ : ↥(Hup D)))
    ⟨fun a b hab => D.inju (Subtype.ext_iff.mp hab),
     fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩⟩

theorem continuous_ΨuEquiv (D : SourceData S) : Continuous (ΨuEquiv D) := by
  refine Continuous.subtype_mk ?_ _
  exact D.Ψu.continuous

/-- `Ψu` as a homeomorphism onto its range. -/
def ΨuHomeo (D : SourceData S) : Work.Smooth.SphereJordan.Disc ≃ₜ ↥(Hup D) :=
  Continuous.homeoOfEquivCompactToT2 (f := ΨuEquiv D) (continuous_ΨuEquiv D)

theorem ΨuHomeo_apply (D : SourceData S) (z : Work.Smooth.SphereJordan.Disc) :
    (ΨuHomeo D z : ℂ) = D.Ψu z := rfl

theorem ΨuHomeo_symm_apply (D : SourceData S) (z : ↥(Hup D)) :
    D.Ψu ((ΨuHomeo D).symm z) = (z : ℂ) :=
  congrArg (fun w : ↥(Hup D) => (w : ℂ)) (Homeomorph.apply_symm_apply (ΨuHomeo D) z)

theorem ΨuHomeo_symm_eq_of (D : SourceData S) {w : Work.Smooth.SphereJordan.Disc}
    {z : ↥(Hup D)} (h : ΨuHomeo D w = z) : (ΨuHomeo D).symm z = w :=
  (Homeomorph.symm_apply_eq (ΨuHomeo D)).mpr h.symm

/-- The homeomorphism `𝔻 ≃ₜ Hdn` given by `Ψd`. -/
def ΨdEquiv (D : SourceData S) : Work.Smooth.SphereJordan.Disc ≃ ↥(Hdn D) :=
  Equiv.ofBijective (fun z => (⟨D.Ψd z, ⟨z, rfl⟩⟩ : ↥(Hdn D)))
    ⟨fun a b hab => D.injd (Subtype.ext_iff.mp hab),
     fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩⟩

theorem continuous_ΨdEquiv (D : SourceData S) : Continuous (ΨdEquiv D) := by
  refine Continuous.subtype_mk ?_ _
  exact D.Ψd.continuous

/-- `Ψd` as a homeomorphism onto its range. -/
def ΨdHomeo (D : SourceData S) : Work.Smooth.SphereJordan.Disc ≃ₜ ↥(Hdn D) :=
  Continuous.homeoOfEquivCompactToT2 (f := ΨdEquiv D) (continuous_ΨdEquiv D)

theorem ΨdHomeo_apply (D : SourceData S) (z : Work.Smooth.SphereJordan.Disc) :
    (ΨdHomeo D z : ℂ) = D.Ψd z := rfl

theorem ΨdHomeo_symm_apply (D : SourceData S) (z : ↥(Hdn D)) :
    D.Ψd ((ΨdHomeo D).symm z) = (z : ℂ) :=
  congrArg (fun w : ↥(Hdn D) => (w : ℂ)) (Homeomorph.apply_symm_apply (ΨdHomeo D) z)

theorem ΨdHomeo_symm_eq_of (D : SourceData S) {w : Work.Smooth.SphereJordan.Disc}
    {z : ↥(Hdn D)} (h : ΨdHomeo D w = z) : (ΨdHomeo D).symm z = w :=
  (Homeomorph.symm_apply_eq (ΨdHomeo D)).mpr h.symm

/-! ## The values of the source maps on the four arcs of the model half-annuli -/

section SrcVal

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

theorem halfPi_mul_sub_bounds (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    0 ≤ (Real.pi / 2) * (1 - θ / Real.pi) ∧
      (Real.pi / 2) * (1 - θ / Real.pi) ≤ Real.pi / 2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2 : 0 ≤ 1 - θ / Real.pi := by
    rw [sub_nonneg, div_le_one hπ]
    exact h1
  have h3 : 1 - θ / Real.pi ≤ 1 := by
    have := div_nonneg h0 hπ.le
    linarith
  refine ⟨mul_nonneg (by positivity) h2, ?_⟩
  calc (Real.pi / 2) * (1 - θ / Real.pi) ≤ (Real.pi / 2) * 1 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = Real.pi / 2 := by ring

theorem halfPi_mul_2m1_bounds (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    0 ≤ (Real.pi / 2) * (2 * ρ - 1) ∧ (Real.pi / 2) * (2 * ρ - 1) ≤ Real.pi / 2 := by
  have h3 : 0 ≤ 2 * ρ - 1 := by linarith
  have h4 : 2 * ρ - 1 ≤ 1 := by linarith
  refine ⟨mul_nonneg (by positivity) h3, ?_⟩
  calc (Real.pi / 2) * (2 * ρ - 1) ≤ (Real.pi / 2) * 1 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = Real.pi / 2 := by ring

theorem halfPi_mul_2m2rho_bounds (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    0 ≤ (Real.pi / 2) * (2 - 2 * ρ) ∧ (Real.pi / 2) * (2 - 2 * ρ) ≤ Real.pi / 2 := by
  have h3 : 0 ≤ 2 - 2 * ρ := by linarith
  have h4 : 2 - 2 * ρ ≤ 1 := by linarith
  refine ⟨mul_nonneg (by positivity) h3, ?_⟩
  calc (Real.pi / 2) * (2 - 2 * ρ) ≤ (Real.pi / 2) * 1 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = Real.pi / 2 := by ring

theorem srcUpB_outer (D : SourceData S) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    D.Ψu (Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 * x)) = outerPt S x := by
  rw [D.bdu, (Work.SphereJordan.srcBranches S).1 (Real.pi / 2 * x)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show Real.pi / 2 * x / (Real.pi / 2) = x by field_simp]
  exact (outerPt_eq_src S x).symm

theorem srcDnB_outer (D : SourceData S) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    D.Ψd (Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 * x)) = outerPtDn S x := by
  rw [D.bdd, (Work.SphereJordan.srcBranches S).2.2.2.2.1 (Real.pi / 2 * x)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show Real.pi / 2 * x / (Real.pi / 2) = x by field_simp]
  exact (outerPtDn_eq_src S x).symm

theorem srcUpB_inner (D : SourceData S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    D.Ψu (Work.Smooth.SphereJordan.circlePoint
      (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi))) = innerPtUp S θ := by
  obtain ⟨b0, b1⟩ := halfPi_mul_sub_bounds θ h0 h1
  rw [D.bdu, (Work.SphereJordan.srcBranches S).2.2.1
    ((Real.pi / 2) * (1 - θ / Real.pi)) b0 b1]
  rw [show (Real.pi / 2) * (1 - θ / Real.pi) / (Real.pi / 2) = 1 - θ / Real.pi by field_simp]
  rw [Work.Smooth.SphereJordan.srcInnerUp, innerPtUp, ← cutAng_spec S]
  simp only [Work.Smooth.Jordan.circlePoint_coe]
  have hπ : Real.pi * (1 - (1 - θ / Real.pi)) = θ := by field_simp; ring
  rw [hπ, mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem srcDnB_inner (D : SourceData S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    D.Ψd (Work.Smooth.SphereJordan.circlePoint
      (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi))) = innerPtDn S θ := by
  obtain ⟨b0, b1⟩ := halfPi_mul_sub_bounds θ h0 h1
  rw [D.bdd, (Work.SphereJordan.srcBranches S).2.2.2.2.2.2.1
    ((Real.pi / 2) * (1 - θ / Real.pi)) b0 b1]
  rw [show (Real.pi / 2) * (1 - θ / Real.pi) / (Real.pi / 2) = 1 - θ / Real.pi by field_simp]
  rw [Work.Smooth.SphereJordan.srcInnerDn, innerPtDn, ← cutAng_spec S]
  simp only [Work.Smooth.Jordan.circlePoint_coe]
  have hπ : -(Real.pi * (1 - θ / Real.pi)) = -Real.pi + θ := by field_simp; ring
  rw [hπ, mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem srcUpB_radpos (D : SourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    D.Ψu (Work.Smooth.SphereJordan.circlePoint
      (3 * Real.pi / 2 + (Real.pi / 2) * (2 * ρ - 1))) =
        (ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S := by
  obtain ⟨b0, b1⟩ := halfPi_mul_2m1_bounds ρ h1 h2
  rw [D.bdu, (Work.SphereJordan.srcBranches S).2.2.2.1
    ((Real.pi / 2) * (2 * ρ - 1)) b0 b1]
  rw [show (Real.pi / 2) * (2 * ρ - 1) / (Real.pi / 2) / 2 = (ρ - 1 / 2) by field_simp]
  push_cast
  ring

theorem srcDnB_radpos (D : SourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    D.Ψd (Work.Smooth.SphereJordan.circlePoint
      (Real.pi / 2 + (Real.pi / 2) * (2 - 2 * ρ))) =
        (ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S := by
  obtain ⟨b0, b1⟩ := halfPi_mul_2m2rho_bounds ρ h1 h2
  rw [D.bdd, (Work.SphereJordan.srcBranches S).2.2.2.2.2.1
    ((Real.pi / 2) * (2 - 2 * ρ)) b0 b1]
  rw [show (Real.pi / 2) * (2 - 2 * ρ) / (Real.pi / 2) / 2 = (1 - ρ) by field_simp]
  push_cast
  ring

theorem srcUpB_radneg (D : SourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    D.Ψu (Work.Smooth.SphereJordan.circlePoint
      (Real.pi / 2 + (Real.pi / 2) * (2 - 2 * ρ))) =
        -((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S) := by
  obtain ⟨b0, b1⟩ := halfPi_mul_2m2rho_bounds ρ h1 h2
  rw [D.bdu, (Work.SphereJordan.srcBranches S).2.1
    ((Real.pi / 2) * (2 - 2 * ρ)) b0 b1]
  rw [show (Real.pi / 2) * (2 - 2 * ρ) / (Real.pi / 2) / 2 = (1 - ρ) by field_simp]
  push_cast
  ring

theorem srcDnB_radneg (D : SourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    D.Ψd (Work.Smooth.SphereJordan.circlePoint
      (3 * Real.pi / 2 + (Real.pi / 2) * (2 * ρ - 1))) =
        -((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S) := by
  obtain ⟨b0, b1⟩ := halfPi_mul_2m1_bounds ρ h1 h2
  rw [D.bdd, (Work.SphereJordan.srcBranches S).2.2.2.2.2.2.2
    ((Real.pi / 2) * (2 * ρ - 1)) b0 b1]
  rw [show (Real.pi / 2) * (2 * ρ - 1) / (Real.pi / 2) / 2 = (ρ - 1 / 2) by field_simp]
  push_cast
  ring

end SrcVal

/-! ## The two-cuts configuration -/

/-- The hypotheses of the two-cuts assembly, bundled: the configuration data, the two spanning
discs of the four-arc curves and the tiling conditions. -/
structure TwoCuts (S : Work.Smooth.Jordan.PlaneSchoenflies γ) where
  t₁ : ℝ
  s₁ : ℝ
  t₂ : ℝ
  s₂ : ℝ
  b : Bool
  θ₁ : ℝ
  θ₂ : ℝ
  hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) *
    Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S
  hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) *
    Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S
  hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) +
    (t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S
  hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) -
    (t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S
  Tu : Work.Smooth.Jordan.PlaneSchoenflies
    (Work.SphereJordan.tgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂)
  Td : Work.Smooth.Jordan.PlaneSchoenflies
    (Work.SphereJordan.tgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂)
  htil : closure Tu.V ∪ closure Td.V = Work.Smooth.SphereJordan.annulus S
  hmeet : closure Tu.V ∩ closure Td.V =
    Work.Smooth.SphereJordan.cut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.cut₂ S t₂ s₂

namespace TwoCuts

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

theorem Tu_apply (K : TwoCuts S) (τ : ℝ) :
    K.Tu.e (Work.Smooth.SphereJordan.circlePoint τ) =
      Work.Smooth.SphereJordan.tgtUpB S K.t₁ K.s₁ K.t₂ K.s₂ K.b K.θ₁ K.θ₂ τ := by
  rw [K.Tu.boundary]
  exact Work.SphereJordan.tgtUpPC_apply S K.t₁ K.s₁ K.t₂ K.s₂ K.b K.θ₁ K.θ₂ K.hout₁ K.hout₂
    K.hθ₁ K.hθ₂ τ

theorem Td_apply (K : TwoCuts S) (τ : ℝ) :
    K.Td.e (Work.Smooth.SphereJordan.circlePoint τ) =
      Work.Smooth.SphereJordan.tgtDnB S K.t₁ K.s₁ K.t₂ K.s₂ K.b K.θ₁ K.θ₂ τ := by
  rw [K.Td.boundary]
  exact Work.SphereJordan.tgtDnPC_apply S K.t₁ K.s₁ K.t₂ K.s₂ K.b K.θ₁ K.θ₂ K.hout₁ K.hout₂
    K.hθ₁ K.hθ₂ τ


end TwoCuts

theorem perPt_two_pi_aux : Work.Smooth.SphereJordan.perPt (2 * Real.pi) = 0 := by
  rw [Work.Smooth.SphereJordan.perPt]
  rw [div_self (by positivity : (2 * Real.pi) ≠ 0), Int.floor_one]
  norm_num

theorem gamma_sub_two_pi (t : ℝ) :
    γ.γ (t - 2 * Real.pi) = γ.γ t := by
  rw [show t - 2 * Real.pi = t + ((-1 : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
  exact Work.Smooth.Jordan.PlaneCurve.apply_add_int_mul γ t (-1)

section TgtVal

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ} {t₁ s₁ t₂ s₂ : ℝ} {b : Bool} {θ₁ θ₂ : ℝ}
variable (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S)
variable (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S)
variable (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) + (t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
variable (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) - (t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
include hout₁ hout₂ hθ₁ hθ₂

theorem tgtUpB_pi_half :
    Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 2) =
      -Work.Smooth.SphereJordan.cutDir S := by
  rw [Work.Smooth.SphereJordan.tgtUpB,
    Work.SphereJordan.TwoCutsAsm.perPt_eq_self (by positivity) (by nlinarith [Real.pi_pos]),
    if_pos le_rfl]
  rw [show Real.pi / 2 / (Real.pi / 2) = 1 by field_simp]
  rw [Work.SphereJordan.srcOuterUp_cp]
  rw [show Real.pi * 1 = Real.pi by ring, Work.SphereJordan.cp_pi]
  ring

theorem tgtUpB_pi :
    Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ Real.pi = γ.γ θ₂ := by
  rw [Work.Smooth.SphereJordan.tgtUpB,
    Work.SphereJordan.TwoCutsAsm.perPt_eq_self (by positivity) (by nlinarith [Real.pi_pos]),
    if_neg (by linarith [Real.pi_pos]), if_pos le_rfl]
  rw [show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 by field_simp; norm_num]
  rw [Work.Smooth.SphereJordan.tgtCut₂]
  rw [show (s₂ + 1 * (t₂ - s₂)) = t₂ by ring]
  exact hθ₂.symm

theorem tgtUpB_3pi_half :
    Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (3 * Real.pi / 2) = γ.γ θ₁ := by
  rw [Work.Smooth.SphereJordan.tgtUpB,
    Work.SphereJordan.TwoCutsAsm.perPt_eq_self (by positivity) (by nlinarith [Real.pi_pos]),
    if_neg (by linarith [Real.pi_pos]), if_neg (by linarith [Real.pi_pos]), if_pos le_rfl]
  rw [show (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 by field_simp; norm_num]
  cases b with
  | false =>
    rw [if_neg (by simp)]
    rw [show θ₂ + 1 * (θ₁ - θ₂ - 2 * Real.pi) = θ₁ + ((-1 : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast; ring]
    exact Work.Smooth.Jordan.PlaneCurve.apply_add_int_mul γ θ₁ (-1)
  | true => rw [if_pos rfl, show θ₂ + 1 * (θ₁ - θ₂) = θ₁ by ring]

theorem tgtUpB_2pi :
    Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (2 * Real.pi) =
      Work.Smooth.SphereJordan.cutDir S := by
  rw [Work.Smooth.SphereJordan.tgtUpB, perPt_two_pi_aux]
  rw [if_pos (by positivity), zero_div, Work.SphereJordan.srcOuterUp_cp, mul_zero]
  simp

theorem tgtDnB_pi_half :
    Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 2) =
      Work.Smooth.SphereJordan.cutDir S := by
  rw [Work.Smooth.SphereJordan.tgtDnB,
    Work.SphereJordan.TwoCutsAsm.perPt_eq_self (by positivity) (by nlinarith [Real.pi_pos]),
    if_pos le_rfl]
  rw [show Real.pi / 2 / (Real.pi / 2) = 1 by field_simp]
  rw [Work.Smooth.SphereJordan.srcOuterDn]
  rw [show Real.pi * 1 = Real.pi by ring, exp_pi_mul_I]
  ring

theorem tgtDnB_pi :
    Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ Real.pi = γ.γ θ₁ := by
  rw [Work.Smooth.SphereJordan.tgtDnB,
    Work.SphereJordan.TwoCutsAsm.perPt_eq_self (by positivity) (by nlinarith [Real.pi_pos]),
    if_neg (by linarith [Real.pi_pos]), if_pos le_rfl]
  rw [show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 by field_simp; norm_num]
  rw [Work.Smooth.SphereJordan.tgtCut₁]
  rw [show (s₁ + 1 * (t₁ - s₁)) = t₁ by ring]
  exact hθ₁.symm

theorem tgtDnB_3pi_half :
    Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (3 * Real.pi / 2) = γ.γ θ₂ := by
  rw [Work.Smooth.SphereJordan.tgtDnB,
    Work.SphereJordan.TwoCutsAsm.perPt_eq_self (by positivity) (by nlinarith [Real.pi_pos]),
    if_neg (by linarith [Real.pi_pos]), if_neg (by linarith [Real.pi_pos]), if_pos le_rfl]
  rw [show (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 by field_simp; norm_num]
  cases b with
  | false => rw [if_neg (by simp), show θ₁ + 1 * (θ₂ - θ₁) = θ₂ by ring]
  | true => rw [if_pos rfl, show θ₁ - 2 * Real.pi + 1 * (θ₂ - θ₁ + 2 * Real.pi) = θ₂ by ring]

theorem tgtDnB_2pi :
    Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (2 * Real.pi) =
      -Work.Smooth.SphereJordan.cutDir S := by
  rw [Work.Smooth.SphereJordan.tgtDnB, perPt_two_pi_aux]
  rw [if_pos (by positivity), zero_div, Work.Smooth.SphereJordan.srcOuterDn, mul_zero]
  simp

theorem tgtB_up1 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ x =
      Work.Smooth.SphereJordan.srcOuterUp S (x / (Real.pi / 2)) := by
  rw [Work.Smooth.SphereJordan.tgtUpB,
    Work.SphereJordan.TwoCutsAsm.perPt_eq_self h0 (by nlinarith [Real.pi_pos]), if_pos h1]

theorem tgtB_up2 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 2 + x) =
      Work.Smooth.SphereJordan.tgtCut₂ S t₂ s₂ (x / (Real.pi / 2)) := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    rw [add_zero, tgtUpB_pi_half hout₁ hout₂ hθ₁ hθ₂]
    rw [Work.Smooth.SphereJordan.tgtCut₂, zero_div,
      show (s₂ + 0 * (t₂ - s₂)) = s₂ by ring]
    exact hout₂.symm
  · rw [Work.Smooth.SphereJordan.tgtUpB,
      Work.SphereJordan.TwoCutsAsm.perPt_eq_self (by linarith) (by nlinarith [Real.pi_pos]),
      if_neg (by linarith), if_pos (by linarith)]
    rw [show Real.pi / 2 + x - Real.pi / 2 = x by ring]

theorem tgtB_up3 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi + x) =
      (if b then γ.γ (θ₂ + (x / (Real.pi / 2)) * (θ₁ - θ₂))
       else γ.γ (θ₂ + (x / (Real.pi / 2)) * (θ₁ - θ₂ - 2 * Real.pi))) := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    rw [add_zero, tgtUpB_pi hout₁ hout₂ hθ₁ hθ₂]
    cases b <;> simp
  · rw [Work.Smooth.SphereJordan.tgtUpB,
      Work.SphereJordan.TwoCutsAsm.perPt_eq_self (by linarith) (by nlinarith [Real.pi_pos]),
      if_neg (by linarith), if_neg (by linarith), if_pos (by linarith)]
    rw [show Real.pi + x - Real.pi = x by ring]

theorem tgtB_up4 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (3 * Real.pi / 2 + x) =
      Work.Smooth.SphereJordan.tgtCut₁ S t₁ s₁ (1 - x / (Real.pi / 2)) := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    rw [add_zero, tgtUpB_3pi_half hout₁ hout₂ hθ₁ hθ₂]
    rw [Work.Smooth.SphereJordan.tgtCut₁, show (1 : ℝ) - 0 / (Real.pi / 2) = 1 by simp,
      show (s₁ + 1 * (t₁ - s₁)) = t₁ by ring]
    exact hθ₁
  · rcases eq_or_lt_of_le h1 with hx2 | hx2
    · subst hx2
      rw [show 3 * Real.pi / 2 + Real.pi / 2 = 2 * Real.pi by ring,
        tgtUpB_2pi hout₁ hout₂ hθ₁ hθ₂]
      rw [Work.Smooth.SphereJordan.tgtCut₁, show (1 : ℝ) - Real.pi / 2 / (Real.pi / 2) = 0 by
        field_simp; ring, show (s₁ + 0 * (t₁ - s₁)) = s₁ by ring]
      exact hout₁.symm
    · rw [Work.Smooth.SphereJordan.tgtUpB,
        Work.SphereJordan.TwoCutsAsm.perPt_eq_self (by linarith) (by nlinarith [Real.pi_pos]),
        if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
      rw [show 3 * Real.pi / 2 + x - 3 * Real.pi / 2 = x by ring]

theorem tgtB_dn1 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ x =
      Work.Smooth.SphereJordan.srcOuterDn S (x / (Real.pi / 2)) := by
  rw [Work.Smooth.SphereJordan.tgtDnB,
    Work.SphereJordan.TwoCutsAsm.perPt_eq_self h0 (by nlinarith [Real.pi_pos]), if_pos h1]

theorem tgtB_dn2 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 2 + x) =
      Work.Smooth.SphereJordan.tgtCut₁ S t₁ s₁ (x / (Real.pi / 2)) := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    rw [add_zero, tgtDnB_pi_half hout₁ hout₂ hθ₁ hθ₂]
    rw [Work.Smooth.SphereJordan.tgtCut₁, zero_div,
      show (s₁ + 0 * (t₁ - s₁)) = s₁ by ring]
    exact hout₁.symm
  · rw [Work.Smooth.SphereJordan.tgtDnB,
      Work.SphereJordan.TwoCutsAsm.perPt_eq_self (by linarith) (by nlinarith [Real.pi_pos]),
      if_neg (by linarith), if_pos (by linarith)]
    rw [show Real.pi / 2 + x - Real.pi / 2 = x by ring]

theorem tgtB_dn3 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi + x) =
      (if b then γ.γ (θ₁ - 2 * Real.pi + (x / (Real.pi / 2)) * (θ₂ - θ₁ + 2 * Real.pi))
       else γ.γ (θ₁ + (x / (Real.pi / 2)) * (θ₂ - θ₁))) := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    rw [add_zero, tgtDnB_pi hout₁ hout₂ hθ₁ hθ₂]
    cases b with
    | false => rw [if_neg (by simp)]; simp
    | true =>
      rw [if_pos rfl]
      rw [show θ₁ - 2 * Real.pi + 0 / (Real.pi / 2) * (θ₂ - θ₁ + 2 * Real.pi) =
        θ₁ - 2 * Real.pi by ring]
      exact (gamma_sub_two_pi θ₁).symm
  · rw [Work.Smooth.SphereJordan.tgtDnB,
      Work.SphereJordan.TwoCutsAsm.perPt_eq_self (by linarith) (by nlinarith [Real.pi_pos]),
      if_neg (by linarith), if_neg (by linarith), if_pos (by linarith)]
    rw [show Real.pi + x - Real.pi = x by ring]

theorem tgtB_dn4 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (3 * Real.pi / 2 + x) =
      Work.Smooth.SphereJordan.tgtCut₂ S t₂ s₂ (1 - x / (Real.pi / 2)) := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    rw [add_zero, tgtDnB_3pi_half hout₁ hout₂ hθ₁ hθ₂]
    rw [Work.Smooth.SphereJordan.tgtCut₂, show (1 : ℝ) - 0 / (Real.pi / 2) = 1 by simp,
      show (s₂ + 1 * (t₂ - s₂)) = t₂ by ring]
    exact hθ₂
  · rcases eq_or_lt_of_le h1 with hx2 | hx2
    · subst hx2
      rw [show 3 * Real.pi / 2 + Real.pi / 2 = 2 * Real.pi by ring,
        tgtDnB_2pi hout₁ hout₂ hθ₁ hθ₂]
      rw [Work.Smooth.SphereJordan.tgtCut₂, show (1 : ℝ) - Real.pi / 2 / (Real.pi / 2) = 0 by
        field_simp; ring, show (s₂ + 0 * (t₂ - s₂)) = s₂ by ring]
      exact hout₂.symm
    · rw [Work.Smooth.SphereJordan.tgtDnB,
        Work.SphereJordan.TwoCutsAsm.perPt_eq_self (by linarith) (by nlinarith [Real.pi_pos]),
        if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
      rw [show 3 * Real.pi / 2 + x - 3 * Real.pi / 2 = x by ring]

namespace TwoCuts

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ}


theorem Tu_outer (K : TwoCuts S) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    K.Tu.e (Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 * x)) = outerPt S x := by
  rw [Tu_apply, tgtB_up1 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ (Real.pi / 2 * x)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show Real.pi / 2 * x / (Real.pi / 2) = x by field_simp]
  exact (outerPt_eq_src S x).symm

theorem Td_outer (K : TwoCuts S) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    K.Td.e (Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 * x)) = outerPtDn S x := by
  rw [Td_apply, tgtB_dn1 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ (Real.pi / 2 * x)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show Real.pi / 2 * x / (Real.pi / 2) = x by field_simp]
  exact (outerPtDn_eq_src S x).symm

theorem Tu_cut₂ (K : TwoCuts S) (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    K.Tu.e (Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 + (Real.pi / 2) * y)) =
      Work.Smooth.SphereJordan.tgtCut₂ S K.t₂ K.s₂ y := by
  rw [Tu_apply, tgtB_up2 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ ((Real.pi / 2) * y)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show (Real.pi / 2) * y / (Real.pi / 2) = y by field_simp]

theorem Td_cut₁ (K : TwoCuts S) (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    K.Td.e (Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 + (Real.pi / 2) * y)) =
      Work.Smooth.SphereJordan.tgtCut₁ S K.t₁ K.s₁ y := by
  rw [Td_apply, tgtB_dn2 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ ((Real.pi / 2) * y)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show (Real.pi / 2) * y / (Real.pi / 2) = y by field_simp]

theorem Tu_cut₁ (K : TwoCuts S) (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    K.Tu.e (Work.Smooth.SphereJordan.circlePoint (3 * Real.pi / 2 + (Real.pi / 2) * y)) =
      Work.Smooth.SphereJordan.tgtCut₁ S K.t₁ K.s₁ (1 - y) := by
  rw [Tu_apply, tgtB_up4 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ ((Real.pi / 2) * y)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show (Real.pi / 2) * y / (Real.pi / 2) = y by field_simp]

theorem Td_cut₂ (K : TwoCuts S) (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    K.Td.e (Work.Smooth.SphereJordan.circlePoint (3 * Real.pi / 2 + (Real.pi / 2) * y)) =
      Work.Smooth.SphereJordan.tgtCut₂ S K.t₂ K.s₂ (1 - y) := by
  rw [Td_apply, tgtB_dn4 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ ((Real.pi / 2) * y)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show (Real.pi / 2) * y / (Real.pi / 2) = y by field_simp]

theorem Tu_inner (K : TwoCuts S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    K.Tu.e (Work.Smooth.SphereJordan.circlePoint (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi))) =
      (if K.b then γ.γ (K.θ₂ + (1 - θ / Real.pi) * (K.θ₁ - K.θ₂))
       else γ.γ (K.θ₂ + (1 - θ / Real.pi) * (K.θ₁ - K.θ₂ - 2 * Real.pi))) := by
  obtain ⟨b0, b1⟩ := halfPi_mul_sub_bounds θ h0 h1
  rw [Tu_apply, tgtB_up3 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ ((Real.pi / 2) * (1 - θ / Real.pi)) b0 b1]
  rw [show (Real.pi / 2) * (1 - θ / Real.pi) / (Real.pi / 2) = 1 - θ / Real.pi by field_simp]

theorem Td_inner (K : TwoCuts S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    K.Td.e (Work.Smooth.SphereJordan.circlePoint (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi))) =
      (if K.b then γ.γ (K.θ₁ - 2 * Real.pi + (1 - θ / Real.pi) * (K.θ₂ - K.θ₁ + 2 * Real.pi))
       else γ.γ (K.θ₁ + (1 - θ / Real.pi) * (K.θ₂ - K.θ₁))) := by
  obtain ⟨b0, b1⟩ := halfPi_mul_sub_bounds θ h0 h1
  rw [Td_apply, tgtB_dn3 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ ((Real.pi / 2) * (1 - θ / Real.pi)) b0 b1]
  rw [show (Real.pi / 2) * (1 - θ / Real.pi) / (Real.pi / 2) = 1 - θ / Real.pi by field_simp]

end TwoCuts

end TgtVal


/-! ## The gluing map of the annulus -/

section Glue

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ} (D : SourceData S) (K : TwoCuts S)

/-- The upper sheet of the gluing map. -/
def glueU : C(↥(Hup D), ℂ) :=
  ⟨fun z => K.Tu.e ((ΨuHomeo D).symm z),
    K.Tu.e.continuous.comp (ΨuHomeo D).symm.continuous⟩

/-- The lower sheet of the gluing map. -/
def glueD : C(↥(Hdn D), ℂ) :=
  ⟨fun z => K.Td.e ((ΨdHomeo D).symm z),
    K.Td.e.continuous.comp (ΨdHomeo D).symm.continuous⟩

theorem glueU_apply (z : ↥(Hup D)) : glueU D K z = K.Tu.e ((ΨuHomeo D).symm z) := rfl

theorem glueD_apply (z : ↥(Hdn D)) : glueD D K z = K.Td.e ((ΨdHomeo D).symm z) := rfl

/-- **The gluing map on the model annulus**: on the upper sheet it is the target upper disc read
through the inverse of `Ψu`, on the lower sheet the target lower disc read through `Ψd`. -/
def glueFun (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ Hup D then glueU D K ⟨z, h⟩
    else if h2 : z ∈ Hdn D then glueD D K ⟨z, h2⟩
    else 0

theorem glueFun_of_Hup {z : ℂ} (hz : z ∈ Hup D) : glueFun D K z = glueU D K ⟨z, hz⟩ := by
  rw [glueFun]
  exact dif_pos hz

theorem glueFun_of_Hdn {z : ℂ} (hz : z ∈ Hdn D) (hz' : z ∉ Hup D) :
    glueFun D K z = glueD D K ⟨z, hz⟩ := by
  rw [glueFun]
  rw [dif_neg hz', dif_pos hz]

theorem ΨuHomeo_symm_eq {z : ℂ} (hz : z ∈ Hup D) {w : Work.Smooth.SphereJordan.Disc}
    (hw : (D.Ψu w : ℂ) = z) : (ΨuHomeo D).symm ⟨z, hz⟩ = w :=
  ΨuHomeo_symm_eq_of D (Subtype.ext (by rw [ΨuHomeo_apply, hw]))

theorem ΨdHomeo_symm_eq {z : ℂ} (hz : z ∈ Hdn D) {w : Work.Smooth.SphereJordan.Disc}
    (hw : (D.Ψd w : ℂ) = z) : (ΨdHomeo D).symm ⟨z, hz⟩ = w :=
  ΨdHomeo_symm_eq_of D (Subtype.ext (by rw [ΨdHomeo_apply, hw]))

/-- The value of the gluing map at a point known to lie on the upper sheet. -/
theorem glueFun_eq_Tu {z : ℂ} (hz : z ∈ Hup D) {w : Work.Smooth.SphereJordan.Disc}
    (hw : (D.Ψu w : ℂ) = z) : glueFun D K z = K.Tu.e w := by
  rw [glueFun_of_Hup D K hz, glueU_apply, ΨuHomeo_symm_eq D hz hw]

/-- The value of the gluing map at a point known to lie on the lower sheet and not on the upper
one. -/
theorem glueFun_eq_Td {z : ℂ} (hz : z ∈ Hdn D) (hz' : z ∉ Hup D)
    {w : Work.Smooth.SphereJordan.Disc} (hw : (D.Ψd w : ℂ) = z) : glueFun D K z = K.Td.e w := by
  rw [glueFun_of_Hdn D K hz hz', glueD_apply, ΨdHomeo_symm_eq D hz hw]

end Glue




/-! ## Points of the boundary circle, of the inner circle and of the radial segments -/

section GlueVal

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ} (D : SourceData S) (K : TwoCuts S)

theorem exp_I_eq_iff (a b : ℝ)
    (h : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I)) :
    ∃ k : ℤ, a - b = k * (2 * Real.pi) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have him : ((a : ℂ) * Complex.I).im =
      ((b : ℂ) * Complex.I + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im :=
    congrArg Complex.im hn
  have h1 : ((a : ℂ) * Complex.I).im = a := by simp
  have h2 : ((b : ℂ) * Complex.I + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im =
      b + (n : ℝ) * (2 * Real.pi) := by
    have : ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
        (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this]
    simp
  rw [h1, h2] at him
  linarith

theorem norm_cutDir' (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ‖Work.Smooth.SphereJordan.cutDir S‖ = 1 := Work.Smooth.SphereJordan.norm_cutDir S

theorem norm_outerPtDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    ‖outerPtDn S x‖ = 1 := by
  rw [outerPtDn, Complex.norm_exp_ofReal_mul_I]

theorem norm_outerPt (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    ‖outerPt S x‖ = 1 := by
  rw [outerPt, Complex.norm_exp_ofReal_mul_I]

theorem norm_innerPtUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) :
    ‖innerPtUp S θ‖ = 1 / 2 := by
  rw [innerPtUp, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  norm_num

theorem norm_innerPtDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) :
    ‖innerPtDn S θ‖ = 1 / 2 := by
  rw [innerPtDn, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  norm_num

/-- A point of norm one lying in both sheets of the model annulus is one of the two outer feet. -/
theorem norm_one_mem_both (D : SourceData S) {z : ℂ} (h1 : z ∈ Hup D) (h2 : z ∈ Hdn D)
    (hz : ‖z‖ = 1) : z = Work.Smooth.SphereJordan.cutDir S ∨
      z = -Work.Smooth.SphereJordan.cutDir S := by
  have hmem : z ∈ ({z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
        z = (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S} ∪
     {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
        z = -((σ : ℂ) * Work.Smooth.SphereJordan.cutDir S)}) := by
    rw [← Hup_inter_Hdn D]
    exact ⟨h1, h2⟩
  rcases hmem with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
  · left
    have hσ1 : σ = 1 := by
      have : ‖(σ : ℂ) * Work.Smooth.SphereJordan.cutDir S‖ = σ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num) hσ.1),
          Work.Smooth.SphereJordan.norm_cutDir, mul_one]
      rw [this] at hz
      exact hz
    rw [hσ1]
    norm_num
  · right
    have hσ1 : σ = 1 := by
      have : ‖-((σ : ℂ) * Work.Smooth.SphereJordan.cutDir S)‖ = σ := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (le_trans (by norm_num) hσ.1), Work.Smooth.SphereJordan.norm_cutDir, mul_one]
      rw [this] at hz
      exact hz
    rw [hσ1]
    norm_num

/-- Membership of the outer arcs in the two sheets. -/
theorem mem_Hup_outer (D : SourceData S) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    outerPt S x ∈ Hup D := ⟨Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 * x),
      srcUpB_outer (S := S) D x h0 h1⟩

theorem mem_Hdn_outer (D : SourceData S) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    outerPtDn S x ∈ Hdn D := ⟨Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 * x),
      srcDnB_outer (S := S) D x h0 h1⟩

/-- Membership of the inner arcs in the two sheets. -/
theorem mem_Hup_inner (D : SourceData S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    innerPtUp S θ ∈ Hup D := ⟨Work.Smooth.SphereJordan.circlePoint
      (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi)), srcUpB_inner (S := S) D θ h0 h1⟩

theorem mem_Hdn_inner (D : SourceData S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    innerPtDn S θ ∈ Hdn D := ⟨Work.Smooth.SphereJordan.circlePoint
      (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi)), srcDnB_inner (S := S) D θ h0 h1⟩

/-- Membership of the radial segments in the two sheets. -/
theorem mem_Hup_radpos (D : SourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    (ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∈ Hup D :=
  ⟨Work.Smooth.SphereJordan.circlePoint (3 * Real.pi / 2 + (Real.pi / 2) * (2 * ρ - 1)),
    srcUpB_radpos (S := S) D ρ h1 h2⟩

theorem mem_Hdn_radpos (D : SourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    (ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∈ Hdn D :=
  ⟨Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 + (Real.pi / 2) * (2 - 2 * ρ)),
    srcDnB_radpos (S := S) D ρ h1 h2⟩

theorem mem_Hup_radneg (D : SourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    -((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S) ∈ Hup D :=
  ⟨Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 + (Real.pi / 2) * (2 - 2 * ρ)),
    srcUpB_radneg (S := S) D ρ h1 h2⟩

theorem mem_Hdn_radneg (D : SourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    -((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S) ∈ Hdn D :=
  ⟨Work.Smooth.SphereJordan.circlePoint (3 * Real.pi / 2 + (Real.pi / 2) * (2 * ρ - 1)),
    srcDnB_radneg (S := S) D ρ h1 h2⟩

/-- The lower outer arc avoids the upper sheet of the model annulus. -/
theorem outerPtDn_notMem_Hup (D : SourceData S) {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    outerPtDn S x ∉ Hup D := by
  intro hz
  have hboth := norm_one_mem_both D hz (mem_Hdn_outer D x h0.le h1.le) (norm_outerPtDn S x)
  rw [outerPtDn] at hboth
  rcases hboth with h | h
  · rw [← cutAng_spec S] at h
    obtain ⟨k, hk⟩ := exp_I_eq_iff _ _ h
    have hk' : Real.pi + Real.pi * x = (k : ℝ) * (2 * Real.pi) := by linarith
    have h2 : (1 + x : ℝ) = (k : ℝ) * 2 := by
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      refine mul_right_cancel₀ hπ ?_
      nlinarith [hk']
    have hklt : k < 1 := by
      have : (k : ℝ) < 1 := by linarith
      exact_mod_cast this
    have hkle : k ≤ 0 := by omega
    have hkge : (1 : ℝ) < (k : ℝ) * 2 := by linarith
    have : (k : ℝ) ≤ 0 := by exact_mod_cast hkle
    linarith
  · rw [show -Work.Smooth.SphereJordan.cutDir S =
        ((Work.Smooth.SphereJordan.circlePoint (cutAng S + Real.pi) :
          Work.Smooth.SphereJordan.Disc) : ℂ) by
      rw [← cutAng_spec S, Work.SphereJordan.TwoCutsAsm.circlePoint_cp_neg (cutAng S)]] at h
    obtain ⟨k, hk⟩ := exp_I_eq_iff _ _ h
    have hk' : Real.pi * x = (k : ℝ) * (2 * Real.pi) := by linarith
    have h2 : x = (k : ℝ) * 2 := by
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      refine mul_right_cancel₀ hπ ?_
      nlinarith [hk']
    have hklt : (k : ℝ) < 1 := by linarith
    have hklt' : k < 1 := by exact_mod_cast hklt
    have hkgt : 0 < k := by
      by_contra hk
      push_neg at hk
      have : (k : ℝ) ≤ 0 := by exact_mod_cast hk
      linarith
    omega

end GlueVal


/-- The radial point of the model annulus at radius parameter `ρ`. -/
def radPt (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (ρ : ℝ) : ℂ :=
  (ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S

section GlueVal2

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ} (D : SourceData S) (K : TwoCuts S)

/-! ### The two sheets agree on the radial segments -/

theorem glueU_radPt (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1)
    (hmem : (ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∈ Hup D) :
    glueU D K ⟨(ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S, hmem⟩ =
      Work.Smooth.SphereJordan.tgtCut₁ S K.t₁ K.s₁ (2 - 2 * ρ) := by
  rw [glueU_apply, ΨuHomeo_symm_eq D hmem (srcUpB_radpos (S := S) D ρ h1 h2)]
  have := TwoCuts.Tu_cut₁ K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (2 * ρ - 1) (by linarith) (by linarith)
  rwa [show 1 - (2 * ρ - 1) = (2 - 2 * ρ) by ring] at this

theorem glueD_radPt (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1)
    (hmem : (ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∈ Hdn D) :
    glueD D K ⟨(ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S, hmem⟩ =
      Work.Smooth.SphereJordan.tgtCut₁ S K.t₁ K.s₁ (2 - 2 * ρ) := by
  rw [glueD_apply, ΨdHomeo_symm_eq D hmem (srcDnB_radpos (S := S) D ρ h1 h2)]
  exact TwoCuts.Td_cut₁ K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (2 - 2 * ρ) (by linarith) (by linarith)

theorem glueU_radPt_neg (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1)
    (hmem : -((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S) ∈ Hup D) :
    glueU D K ⟨-((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S), hmem⟩ =
      Work.Smooth.SphereJordan.tgtCut₂ S K.t₂ K.s₂ (2 - 2 * ρ) := by
  rw [glueU_apply, ΨuHomeo_symm_eq D hmem (srcUpB_radneg (S := S) D ρ h1 h2)]
  exact TwoCuts.Tu_cut₂ K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (2 - 2 * ρ) (by linarith) (by linarith)

theorem glueD_radPt_neg (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1)
    (hmem : -((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S) ∈ Hdn D) :
    glueD D K ⟨-((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S), hmem⟩ =
      Work.Smooth.SphereJordan.tgtCut₂ S K.t₂ K.s₂ (2 - 2 * ρ) := by
  rw [glueD_apply, ΨdHomeo_symm_eq D hmem (srcDnB_radneg (S := S) D ρ h1 h2)]
  have := TwoCuts.Td_cut₂ K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (2 * ρ - 1) (by linarith) (by linarith)
  rwa [show 1 - (2 * ρ - 1) = (2 - 2 * ρ) by ring] at this

/-- **The two sheets of the gluing map agree on the radial segments**, hence on the whole
intersection `Hup ∩ Hdn`. -/
theorem glueU_eq_glueD (z : ℂ) (hz1 : z ∈ Hup D) (hz2 : z ∈ Hdn D) :
    glueU D K ⟨z, hz1⟩ = glueD D K ⟨z, hz2⟩ := by
  have hmem : z ∈ Hup D ∩ Hdn D := ⟨hz1, hz2⟩
  rw [Hup_inter_Hdn D] at hmem
  rcases hmem with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
  · rw [glueU_radPt D K σ hσ.1 hσ.2 hz1, glueD_radPt D K σ hσ.1 hσ.2 hz2]
  · rw [glueU_radPt_neg D K σ hσ.1 hσ.2 hz1, glueD_radPt_neg D K σ hσ.1 hσ.2 hz2]

/-! ### The values of the gluing map -/

theorem glueFun_eq_Td' {z : ℂ} (hz : z ∈ Hdn D) {w : Work.Smooth.SphereJordan.Disc}
    (hw : (D.Ψd w : ℂ) = z) : glueFun D K z = K.Td.e w := by
  by_cases h : z ∈ Hup D
  · rw [glueFun_of_Hup D K h, glueU_eq_glueD D K z h hz, glueD_apply, ΨdHomeo_symm_eq D hz hw]
  · rw [glueFun_of_Hdn D K hz h, glueD_apply, ΨdHomeo_symm_eq D hz hw]

theorem glueFun_outer (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    glueFun D K (outerPt S x) = outerPt S x := by
  rw [glueFun_eq_Tu D K (mem_Hup_outer D x h0 h1) (srcUpB_outer (S := S) D x h0 h1)]
  exact TwoCuts.Tu_outer K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K x h0 h1

theorem glueFun_outerDn (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    glueFun D K (outerPtDn S x) = outerPtDn S x := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    have hpt : outerPtDn S 0 = outerPt S 1 := by
      rw [outerPtDn, outerPt]
      norm_num
    rw [hpt, glueFun_outer D K 1 zero_le_one le_rfl]
  · rcases eq_or_lt_of_le h1 with hx2 | hx2
    · subst hx2
      have hpt : outerPtDn S 1 = outerPt S 0 := by
        rw [outerPtDn, outerPt]
        rw [show cutAng S + Real.pi + Real.pi * 1 = cutAng S + 2 * Real.pi by ring,
          show cutAng S + Real.pi * 0 = cutAng S by ring]
        rw [show ((cutAng S + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
          (cutAng S : ℂ) * Complex.I + (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
        rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      rw [hpt, glueFun_outer D K 0 le_rfl zero_le_one]
    · rw [glueFun_eq_Td' D K (mem_Hdn_outer D x h0 h1) (srcDnB_outer (S := S) D x h0 h1)]
      exact TwoCuts.Td_outer K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K x h0 h1

theorem glueFun_innerUp (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    glueFun D K (innerPtUp S θ) =
      K.Tu.e (Work.Smooth.SphereJordan.circlePoint
        (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi))) := by
  rw [glueFun_eq_Tu D K (mem_Hup_inner D θ h0 h1) (srcUpB_inner (S := S) D θ h0 h1)]

theorem glueFun_innerDn (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    glueFun D K (innerPtDn S θ) =
      K.Td.e (Work.Smooth.SphereJordan.circlePoint
        (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi))) := by
  rw [glueFun_eq_Td' D K (mem_Hdn_inner D θ h0 h1) (srcDnB_inner (S := S) D θ h0 h1)]

theorem glueFun_radPt (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    glueFun D K ((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S) =
      Work.Smooth.SphereJordan.tgtCut₁ S K.t₁ K.s₁ (2 - 2 * ρ) := by
  rw [glueFun_eq_Tu D K (mem_Hup_radpos D ρ h1 h2) (srcUpB_radpos (S := S) D ρ h1 h2)]
  have := TwoCuts.Tu_cut₁ K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (2 * ρ - 1) (by linarith) (by linarith)
  rwa [show 1 - (2 * ρ - 1) = (2 - 2 * ρ) by ring] at this

theorem glueFun_radPt_neg (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    glueFun D K (-((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S)) =
      Work.Smooth.SphereJordan.tgtCut₂ S K.t₂ K.s₂ (2 - 2 * ρ) := by
  rw [glueFun_eq_Tu D K (mem_Hup_radneg D ρ h1 h2) (srcUpB_radneg (S := S) D ρ h1 h2)]
  exact TwoCuts.Tu_cut₂ K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (2 - 2 * ρ) (by linarith) (by linarith)

/-! ### The image of the gluing map -/

theorem glueU_injective : Function.Injective (glueU D K) := by
  intro a b h
  have h' : (ΨuHomeo D).symm a = (ΨuHomeo D).symm b := K.Tu.inj h
  exact (ΨuHomeo D).symm.injective h'

theorem glueD_injective : Function.Injective (glueD D K) := by
  intro a b h
  have h' : (ΨdHomeo D).symm a = (ΨdHomeo D).symm b := K.Td.inj h
  exact (ΨdHomeo D).symm.injective h'

theorem range_glueU : Set.range (glueU D K) = closure K.Tu.V := by
  rw [← K.Tu.range_e]
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(ΨuHomeo D).symm a, rfl⟩
  · rintro ⟨w, rfl⟩
    refine ⟨ΨuHomeo D w, ?_⟩
    rw [glueU_apply, Homeomorph.symm_apply_apply]

theorem range_glueD : Set.range (glueD D K) = closure K.Td.V := by
  rw [← K.Td.range_e]
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(ΨdHomeo D).symm a, rfl⟩
  · rintro ⟨w, rfl⟩
    refine ⟨ΨdHomeo D w, ?_⟩
    rw [glueD_apply, Homeomorph.symm_apply_apply]

theorem range_glueU_inter : Set.range (glueU D K) ∩ Set.range (glueD D K) =
    Work.Smooth.SphereJordan.cut₁ S K.t₁ K.s₁ ∪
      Work.Smooth.SphereJordan.cut₂ S K.t₂ K.s₂ := by
  rw [range_glueU, range_glueD, K.hmeet]

theorem div_mem_Icc_of_mem_Icc {t s σ : ℝ} (hts : t ≠ s) (hσ : σ ∈ Set.Icc t s) :
    0 ≤ (σ - s) / (t - s) ∧ (σ - s) / (t - s) ≤ 1 ∧
      s + (σ - s) / (t - s) * (t - s) = σ := by
  have hkey : (σ - s) / (t - s) * (t - s) = σ - s := by
    field_simp
  refine ⟨?_, ?_, by rw [hkey]; ring⟩
  · rcases lt_or_gt_of_ne hts with hlt | hlt
    · have h1 : σ - s ≤ 0 := by linarith [hσ.2]
      have h2 : t - s < 0 := by linarith
      rw [div_nonneg_iff]
      exact Or.inr ⟨h1, le_of_lt h2⟩
    · have h1 : 0 ≤ σ - s := by linarith [hσ.1]
      have h2 : 0 < t - s := by linarith
      exact div_nonneg h1 (le_of_lt h2)
  · rcases lt_or_gt_of_ne hts with hlt | hlt
    · have h2 : t - s < 0 := by linarith
      rw [div_le_iff_of_neg h2]
      linarith [hσ.1]
    · have h2 : 0 < t - s := by linarith
      rw [div_le_iff₀ h2]
      linarith [hσ.2]

/-- **The radial segments cover the two crosscuts** under the gluing map. -/
theorem cut_subset_frontier (y : ℂ)
    (hy : y ∈ Work.Smooth.SphereJordan.cut₁ S K.t₁ K.s₁ ∪
      Work.Smooth.SphereJordan.cut₂ S K.t₂ K.s₂) :
    (∃ ρ : ℝ, 1 / 2 ≤ ρ ∧ ρ ≤ 1 ∧
        glueFun D K ((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S) = y) ∨
      (∃ ρ : ℝ, 1 / 2 ≤ ρ ∧ ρ ≤ 1 ∧
        glueFun D K (-((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S)) = y) := by
  rcases hy with hy | hy
  · left
    rcases hy with ⟨σ, hσ, rfl⟩
    rcases eq_or_ne K.t₁ K.s₁ with hts | hts
    · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      rw [glueFun_radPt D K (1 / 2) (by norm_num) (by norm_num)]
      rw [Work.Smooth.SphereJordan.tgtCut₁]
      have hσeq : σ = K.s₁ := by
        refine le_antisymm hσ.2 ?_
        rw [← hts]
        exact hσ.1
      rw [show K.s₁ + (2 - 2 * (1 / 2)) * (K.t₁ - K.s₁) = σ by
        rw [hts]; ring_nf; exact hσeq.symm]
    · obtain ⟨hx0, hx1, hxeq⟩ :=
        (div_mem_Icc_of_mem_Icc hts hσ)
      refine ⟨1 - (σ - K.s₁) / (K.t₁ - K.s₁) / 2, by linarith, by linarith, ?_⟩
      rw [glueFun_radPt D K (1 - (σ - K.s₁) / (K.t₁ - K.s₁) / 2) (by linarith) (by linarith)]
      rw [Work.Smooth.SphereJordan.tgtCut₁]
      rw [show (2 - 2 * (1 - (σ - K.s₁) / (K.t₁ - K.s₁) / 2) : ℝ) =
        (σ - K.s₁) / (K.t₁ - K.s₁) by ring]
      rw [hxeq]
  · right
    rcases hy with ⟨σ, hσ, rfl⟩
    rcases eq_or_ne K.t₂ K.s₂ with hts | hts
    · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      rw [glueFun_radPt_neg D K (1 / 2) (by norm_num) (by norm_num)]
      rw [Work.Smooth.SphereJordan.tgtCut₂]
      have hσeq : σ = K.s₂ := by
        refine le_antisymm hσ.2 ?_
        rw [← hts]
        exact hσ.1
      rw [show K.s₂ + (2 - 2 * (1 / 2)) * (K.t₂ - K.s₂) = σ by
        rw [hts]; ring_nf; exact hσeq.symm]
    · obtain ⟨hx0, hx1, hxeq⟩ :=
        (div_mem_Icc_of_mem_Icc hts hσ)
      refine ⟨1 - (σ - K.s₂) / (K.t₂ - K.s₂) / 2, by linarith, by linarith, ?_⟩
      rw [glueFun_radPt_neg D K (1 - (σ - K.s₂) / (K.t₂ - K.s₂) / 2) (by linarith) (by linarith)]
      rw [Work.Smooth.SphereJordan.tgtCut₂]
      rw [show (2 - 2 * (1 - (σ - K.s₂) / (K.t₂ - K.s₂) / 2) : ℝ) =
        (σ - K.s₂) / (K.t₂ - K.s₂) by ring]
      rw [hxeq]

/-! ### Injectivity of the gluing map on the model annulus -/

theorem mem_Hdn_of_mem_Msub {z : ℂ} (hz : z ∈ Msub) (hz' : z ∉ Hup D) : z ∈ Hdn D := by
  have h := hz
  rw [← Hup_union_Hdn D] at h
  rcases h with h | h
  · exact absurd h hz'
  · exact h

/-- The gluing map is injective on the model annulus restricted to a point of the upper sheet. -/
theorem glueFun_injOn_of_Hup {z z' : ℂ} (hz : z ∈ Msub) (hz' : z' ∈ Msub)
    (h1 : z ∈ Hup D) (h2 : z' ∉ Hup D)
    (h : glueFun D K z = glueFun D K z') : z = z' := by
  have hz2 : z' ∈ Hdn D := mem_Hdn_of_mem_Msub D hz' h2
  have hy : glueFun D K z ∈ Work.Smooth.SphereJordan.cut₁ S K.t₁ K.s₁ ∪
      Work.Smooth.SphereJordan.cut₂ S K.t₂ K.s₂ := by
    have hy1 : glueFun D K z ∈ Set.range (glueU D K) := by
      rw [glueFun_of_Hup D K h1]
      exact ⟨⟨z, h1⟩, rfl⟩
    have hy2 : glueFun D K z' ∈ Set.range (glueD D K) := by
      rw [glueFun_of_Hdn D K hz2 h2]
      exact ⟨⟨z', hz2⟩, rfl⟩
    rw [← range_glueU_inter D K]
    exact ⟨hy1, h ▸ hy2⟩
  rcases cut_subset_frontier D K (glueFun D K z) hy with
    ⟨ρ, hρ1, hρ2, hρ⟩ | ⟨ρ, hρ1, hρ2, hρ⟩
  · have hzu : z = (ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S := by
      have hx : glueU D K ⟨z, h1⟩ =
          glueU D K ⟨(ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S,
            mem_Hup_radpos D ρ hρ1 hρ2⟩ := by
        rw [← glueFun_of_Hup D K h1,
          ← glueFun_of_Hup D K (mem_Hup_radpos D ρ hρ1 hρ2)]
        exact hρ.symm
      exact congrArg Subtype.val (glueU_injective D K hx)
    have hz'u : z' = (ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S := by
      have hz2b : z' ∈ Hdn D := hz2
      obtain ⟨w, hw⟩ := hz2b
      have h1' : glueFun D K z' = K.Td.e w := glueFun_eq_Td' D K hz2 hw
      have h2' : glueFun D K ((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S) =
          K.Td.e (Work.Smooth.SphereJordan.circlePoint
            (Real.pi / 2 + (Real.pi / 2) * (2 - 2 * ρ))) :=
        glueFun_eq_Td' D K (mem_Hdn_radpos D ρ hρ1 hρ2) (srcDnB_radpos (S := S) D ρ hρ1 hρ2)
      have hkey : K.Td.e w = K.Td.e (Work.Smooth.SphereJordan.circlePoint
          (Real.pi / 2 + (Real.pi / 2) * (2 - 2 * ρ))) := by
        rw [← h1', ← h, ← hρ, ← h2']
      have hw' := K.Td.inj hkey
      rw [← hw, hw']
      exact srcDnB_radpos (S := S) D ρ hρ1 hρ2
    rw [hzu, hz'u]
  · have hzu : z = -((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S) := by
      have hx : glueU D K ⟨z, h1⟩ =
          glueU D K ⟨-((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S),
            mem_Hup_radneg D ρ hρ1 hρ2⟩ := by
        rw [← glueFun_of_Hup D K h1,
          ← glueFun_of_Hup D K (mem_Hup_radneg D ρ hρ1 hρ2)]
        exact hρ.symm
      exact congrArg Subtype.val (glueU_injective D K hx)
    have hz'u : z' = -((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S) := by
      have hz2b : z' ∈ Hdn D := hz2
      obtain ⟨w, hw⟩ := hz2b
      have h1' : glueFun D K z' = K.Td.e w := glueFun_eq_Td' D K hz2 hw
      have h2' : glueFun D K (-((ρ : ℂ) * Work.Smooth.SphereJordan.cutDir S)) =
          K.Td.e (Work.Smooth.SphereJordan.circlePoint
            (3 * Real.pi / 2 + (Real.pi / 2) * (2 * ρ - 1))) :=
        glueFun_eq_Td' D K (mem_Hdn_radneg D ρ hρ1 hρ2) (srcDnB_radneg (S := S) D ρ hρ1 hρ2)
      have hkey : K.Td.e w = K.Td.e (Work.Smooth.SphereJordan.circlePoint
          (3 * Real.pi / 2 + (Real.pi / 2) * (2 * ρ - 1))) := by
        rw [← h1', ← h, ← hρ, ← h2']
      have hw' := K.Td.inj hkey
      rw [← hw, hw']
      exact srcDnB_radneg (S := S) D ρ hρ1 hρ2
    rw [hzu, hz'u]

/-- **The gluing map is injective on the model annulus.** -/
theorem glueFun_injOn {z z' : ℂ} (hz : z ∈ Msub) (hz' : z' ∈ Msub)
    (h : glueFun D K z = glueFun D K z') : z = z' := by
  by_cases h2 : z' ∈ Hup D
  · by_cases h1 : z ∈ Hup D
    · have hU : glueU D K ⟨z, h1⟩ = glueU D K ⟨z', h2⟩ := by
        rw [← glueFun_of_Hup D K h1, ← glueFun_of_Hup D K h2]
        exact h
      exact congrArg Subtype.val (glueU_injective D K hU)
    · exact (glueFun_injOn_of_Hup D K hz' hz h2 h1 h.symm).symm
  · by_cases h1 : z ∈ Hup D
    · exact glueFun_injOn_of_Hup D K hz hz' h1 h2 h
    · have hz2 : z ∈ Hdn D := mem_Hdn_of_mem_Msub D hz h1
      have hz2' : z' ∈ Hdn D := mem_Hdn_of_mem_Msub D hz' h2
      have hD : glueD D K ⟨z, hz2⟩ = glueD D K ⟨z', hz2'⟩ := by
        rw [← glueFun_of_Hdn D K hz2 h1, ← glueFun_of_Hdn D K hz2' h2]
        exact h
      exact congrArg Subtype.val (glueD_injective D K hD)

/-! ### Continuity of the gluing map -/

theorem isClosed_Hup : IsClosed (Hup D) :=
  (isCompact_range D.Ψu.continuous).isClosed

theorem isClosed_Hdn : IsClosed (Hdn D) :=
  (isCompact_range D.Ψd.continuous).isClosed

theorem continuousOn_glueFun_Hup : ContinuousOn (glueFun D K) (Hup D) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hEq : (Hup D).domRestrict (glueFun D K) = fun z : ↥(Hup D) => glueU D K z := by
    funext z
    exact glueFun_of_Hup D K z.2
  rw [hEq]
  exact (glueU D K).continuous

theorem continuousOn_glueFun_Hdn : ContinuousOn (glueFun D K) (Hdn D) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hEq : (Hdn D).domRestrict (glueFun D K) = fun z : ↥(Hdn D) => glueD D K z := by
    funext z
    by_cases h : (z : ℂ) ∈ Hup D
    · rw [Set.domRestrict_apply, glueFun_of_Hup D K h]
      have h2 : (⟨(z : ℂ), h⟩ : ↥(Hup D)) = ⟨(z : ℂ), h⟩ := rfl
      rw [glueU_eq_glueD D K (z : ℂ) h z.2]
    · rw [Set.domRestrict_apply, glueFun_of_Hdn D K z.2 h]
  rw [hEq]
  exact (glueD D K).continuous

/-- The gluing map, as a map on the model annulus. -/
def glueM (z : ↥(Msub)) : ℂ := glueFun D K (z : ℂ)

theorem glueM_apply (z : ↥(Msub)) : glueM D K z = glueFun D K (z : ℂ) := rfl

theorem continuous_glueM : Continuous (glueM D K) := by
  have hA : IsClosed {z : ↥(Msub) | (z : ℂ) ∈ Hup D} :=
    (isClosed_Hup D).preimage continuous_subtype_val
  have hB : IsClosed {z : ↥(Msub) | (z : ℂ) ∈ Hdn D} :=
    (isClosed_Hdn D).preimage continuous_subtype_val
  have hcov : ({z : ↥(Msub) | (z : ℂ) ∈ Hup D} ∪ {z : ↥(Msub) | (z : ℂ) ∈ Hdn D}) = univ := by
    ext z
    constructor
    · intro _; trivial
    · intro _
      have h : (z : ℂ) ∈ Hup D ∪ Hdn D := by
        rw [Hup_union_Hdn D]
        exact z.2
      exact h
  have hcontA : ContinuousOn (glueM D K) {z : ↥(Msub) | (z : ℂ) ∈ Hup D} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : ({z : ↥(Msub) | (z : ℂ) ∈ Hup D}).domRestrict (glueM D K) =
        fun z : ↥{z : ↥(Msub) | (z : ℂ) ∈ Hup D} =>
          glueU D K (⟨((z : ↥(Msub)) : ℂ), z.2⟩ : ↥(Hup D)) := by
      funext z
      exact glueFun_of_Hup D K z.2
    rw [hEq]
    exact (glueU D K).continuous.comp
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
  have hcontB : ContinuousOn (glueM D K) {z : ↥(Msub) | (z : ℂ) ∈ Hdn D} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : ({z : ↥(Msub) | (z : ℂ) ∈ Hdn D}).domRestrict (glueM D K) =
        fun z : ↥{z : ↥(Msub) | (z : ℂ) ∈ Hdn D} =>
          glueD D K (⟨((z : ↥(Msub)) : ℂ), z.2⟩ : ↥(Hdn D)) := by
      funext z
      by_cases h : (((z : ↥{z : ↥(Msub) | (z : ℂ) ∈ Hdn D}) : ↥(Msub)) : ℂ) ∈ Hup D
      · rw [Set.domRestrict_apply, glueM_apply, glueFun_of_Hup D K h]
        rw [glueU_eq_glueD D K (((z : ↥(Msub)) : ℂ)) h z.2]
      · rw [Set.domRestrict_apply, glueM_apply, glueFun_of_Hdn D K z.2 h]
    rw [hEq]
    exact (glueD D K).continuous.comp
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
  refine LocallyFinite.continuous (f := fun i : Bool =>
      bif i then {z : ↥(Msub) | (z : ℂ) ∈ Hup D} else {z : ↥(Msub) | (z : ℂ) ∈ Hdn D})
    (locallyFinite_of_finite _) ?_ ?_ ?_
  · have hunion : (⋃ i : Bool, bif i then {z : ↥(Msub) | (z : ℂ) ∈ Hup D}
        else {z : ↥(Msub) | (z : ℂ) ∈ Hdn D}) =
        ({z : ↥(Msub) | (z : ℂ) ∈ Hup D} ∪ {z : ↥(Msub) | (z : ℂ) ∈ Hdn D}) := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_union, Bool.exists_bool, Bool.cond_true,
        Bool.cond_false]
      tauto
    rw [hunion, hcov]
  · intro i
    cases i <;> simp only [Bool.cond_true, Bool.cond_false] <;> assumption
  · intro i
    cases i <;> simp only [Bool.cond_true, Bool.cond_false] <;> assumption

end GlueVal2





section Config

/-! ## The ordering of the two parameters -/

theorem abs_lt_two_pi_of_injOn_arc {γ : Work.Smooth.Jordan.PlaneCurve} {a L : ℝ} (hL : L ≠ 0)
    (hinj : Set.InjOn (fun x : ℝ => γ.γ (a + x * L)) (Set.Icc (0 : ℝ) 1)) :
    |L| < 2 * Real.pi := by
  by_contra h
  rw [not_lt] at h
  have hLpos : 0 < |L| := abs_pos.mpr hL
  set y : ℝ := 2 * Real.pi / |L| with hy
  have hy0 : 0 < y := by
    rw [hy]
    positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_one hLpos]
    exact h
  have hkey : γ.γ (a + y * L) = γ.γ (a + 0 * L) := by
    rcases le_or_gt 0 L with hL0 | hL0
    · have hyL : y * L = 2 * Real.pi := by
        rw [hy, abs_of_nonneg hL0]
        field_simp
      rw [hyL, zero_mul, add_zero]
      exact γ.periodic a
    · have hyL : y * L = -(2 * Real.pi) := by
        rw [hy, abs_of_neg hL0]
        field_simp
      rw [hyL, zero_mul, add_zero]
      exact gamma_sub_two_pi a
  have h0 : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hy' : y ∈ Set.Icc 0 1 := ⟨hy0.le, hy1⟩
  have hres := hinj hy' h0 hkey
  linarith

theorem configOrder {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) {θ₁ θ₂ : ℝ}
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
    (T_up : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.tgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (T_dn : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.tgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂)) :
    0 < θ₁ - θ₂ ∧ θ₁ - θ₂ < 2 * Real.pi := by
  have hUp := T_up.simple
  have hDn := T_dn.simple
  -- the third-branch values and their injectivity
  have hup3 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi + (Real.pi / 2) * x) =
        (if b then γ.γ (θ₂ + x * (θ₁ - θ₂))
         else γ.γ (θ₂ + x * (θ₁ - θ₂ - 2 * Real.pi))) := by
    intro x hx
    rw [tgtB_up3 hout₁ hout₂ hθ₁ hθ₂ ((Real.pi / 2) * x)
      (by nlinarith [Real.pi_pos, hx.1]) (by nlinarith [Real.pi_pos, hx.2]),
      show (Real.pi / 2) * x / (Real.pi / 2) = x by field_simp]
  have hdn3 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi + (Real.pi / 2) * x) =
        (if b then γ.γ (θ₁ - 2 * Real.pi + x * (θ₂ - θ₁ + 2 * Real.pi))
         else γ.γ (θ₁ + x * (θ₂ - θ₁))) := by
    intro x hx
    rw [tgtB_dn3 hout₁ hout₂ hθ₁ hθ₂ ((Real.pi / 2) * x)
      (by nlinarith [Real.pi_pos, hx.1]) (by nlinarith [Real.pi_pos, hx.2]),
      show (Real.pi / 2) * x / (Real.pi / 2) = x by field_simp]
  have hmem3 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Real.pi + (Real.pi / 2) * x ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    intro x hx
    constructor
    · nlinarith [Real.pi_pos, hx.1]
    · nlinarith [Real.pi_pos, hx.1, hx.2]
  -- injectivity of the up-arc of the third branch
  have hinjUp : Set.InjOn (fun x : ℝ =>
      Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi + (Real.pi / 2) * x))
      (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have h := hUp (hmem3 x hx) (hmem3 y hy) hxy
    have h' : (Real.pi / 2) * x = (Real.pi / 2) * y := by linarith
    exact mul_left_cancel₀ (by positivity : (Real.pi / 2) ≠ 0) h'
  have hinjDn : Set.InjOn (fun x : ℝ =>
      Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi + (Real.pi / 2) * x))
      (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have h := hDn (hmem3 x hx) (hmem3 y hy) hxy
    have h' : (Real.pi / 2) * x = (Real.pi / 2) * y := by linarith
    exact mul_left_cancel₀ (by positivity : (Real.pi / 2) ≠ 0) h'
  -- non-degeneracy of the increments
  have ne_of_inj {a L : ℝ} (hinj : Set.InjOn (fun x : ℝ => γ.γ (a + x * L)) (Set.Icc (0:ℝ) 1)) :
      L ≠ 0 := by
    intro hL
    have h1 := hinj (show (1:ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
      (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩) (by rw [hL]; ring)
    norm_num at h1
  cases b with
  | true =>
    have atrue_up : Set.InjOn (fun x : ℝ => γ.γ (θ₂ + x * (θ₁ - θ₂)))
        (Set.Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      refine hinjUp hx hy ?_
      show Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ true θ₁ θ₂
        (Real.pi + (Real.pi / 2) * x) =
        Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ true θ₁ θ₂
          (Real.pi + (Real.pi / 2) * y)
      rw [hup3 x hx, hup3 y hy, if_pos rfl, if_pos rfl]
      exact hxy
    have atrue_dn : Set.InjOn (fun x : ℝ =>
        γ.γ (θ₁ - 2 * Real.pi + x * (θ₂ - θ₁ + 2 * Real.pi))) (Set.Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      refine hinjDn hx hy ?_
      show Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ true θ₁ θ₂
        (Real.pi + (Real.pi / 2) * x) =
        Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ true θ₁ θ₂
          (Real.pi + (Real.pi / 2) * y)
      rw [hdn3 x hx, hdn3 y hy, if_pos rfl, if_pos rfl]
      exact hxy
    have h1 : |θ₁ - θ₂| < 2 * Real.pi :=
      abs_lt_two_pi_of_injOn_arc (ne_of_inj atrue_up) atrue_up
    have h2 : |θ₂ - θ₁ + 2 * Real.pi| < 2 * Real.pi :=
      abs_lt_two_pi_of_injOn_arc (ne_of_inj atrue_dn) atrue_dn
    rw [abs_lt] at h1 h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  | false =>
    have afalse_up : Set.InjOn (fun x : ℝ => γ.γ (θ₂ + x * (θ₁ - θ₂ - 2 * Real.pi)))
        (Set.Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      refine hinjUp hx hy ?_
      show Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ false θ₁ θ₂
        (Real.pi + (Real.pi / 2) * x) =
        Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ false θ₁ θ₂
          (Real.pi + (Real.pi / 2) * y)
      rw [hup3 x hx, hup3 y hy, if_neg (by simp), if_neg (by simp)]
      exact hxy
    have afalse_dn : Set.InjOn (fun x : ℝ => γ.γ (θ₁ + x * (θ₂ - θ₁)))
        (Set.Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      refine hinjDn hx hy ?_
      show Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ false θ₁ θ₂
        (Real.pi + (Real.pi / 2) * x) =
        Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ false θ₁ θ₂
          (Real.pi + (Real.pi / 2) * y)
      rw [hdn3 x hx, hdn3 y hy, if_neg (by simp), if_neg (by simp)]
      exact hxy
    have h1 : |θ₁ - θ₂ - 2 * Real.pi| < 2 * Real.pi :=
      abs_lt_two_pi_of_injOn_arc (ne_of_inj afalse_up) afalse_up
    have h2 : |θ₂ - θ₁| < 2 * Real.pi :=
      abs_lt_two_pi_of_injOn_arc (ne_of_inj afalse_dn) afalse_dn
    rw [abs_lt] at h1 h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end Config


/-! ## The inner-boundary curve and the assembled disc map

This section builds the continuous injection `G : 𝔻 → 𝔻` which fixes the boundary circle
pointwise and carries the inner circle into `γ.trace`.  It is the input of
`Work.SphereJordan.annulusInnerReparam`. -/

namespace Assembly

section

theorem circlePoint_add_int_two_pi (θ : ℝ) (k : ℤ) :
    Work.Smooth.Jordan.circlePoint (θ + (k : ℝ) * (2 * Real.pi)) =
      Work.Smooth.Jordan.circlePoint θ := by
  apply Subtype.ext
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  have h : (((θ + (k : ℝ) * (2 * Real.pi) : ℝ)) : ℂ) * Complex.I
      = (θ : ℂ) * Complex.I + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem halfCirclePoint_add_int_two_pi (θ : ℝ) (k : ℤ) :
    Work.Smooth.SphereJordan.halfCirclePoint (θ + (k : ℝ) * (2 * Real.pi)) =
      Work.Smooth.SphereJordan.halfCirclePoint θ := by
  apply Subtype.ext
  rw [Work.Smooth.SphereJordan.halfCirclePoint_coe,
    Work.Smooth.SphereJordan.halfCirclePoint_coe, circlePoint_add_int_two_pi]

theorem norm_halfCirclePoint (θ : ℝ) :
    ‖((Work.Smooth.SphereJordan.halfCirclePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)‖
      = 1 / 2 := by
  rw [Work.Smooth.SphereJordan.halfCirclePoint_coe, norm_mul,
    Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I, mul_one]
  norm_num

theorem halfCirclePoint_mem_Msub (θ : ℝ) :
    ((Work.Smooth.SphereJordan.halfCirclePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ Msub := by
  refine ⟨?_, ?_⟩
  · rw [norm_halfCirclePoint]
  · rw [norm_halfCirclePoint]; norm_num

theorem halfCirclePoint_innerPtUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) :
    Work.Smooth.SphereJordan.halfCirclePoint (cutAng S + θ) = innerPtUp S θ := by
  rw [Work.Smooth.SphereJordan.halfCirclePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  rfl

theorem halfCirclePoint_innerPtDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) :
    Work.Smooth.SphereJordan.halfCirclePoint (cutAng S - Real.pi + θ) = innerPtDn S θ := by
  rw [Work.Smooth.SphereJordan.halfCirclePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  rfl

theorem halfCirclePoint_reduce (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) :
    Work.Smooth.SphereJordan.halfCirclePoint θ =
      Work.Smooth.SphereJordan.halfCirclePoint
        (cutAng S - Real.pi + Work.Smooth.SphereJordan.perPt (θ - (cutAng S - Real.pi))) := by
  set r := Work.Smooth.SphereJordan.perPt (θ - (cutAng S - Real.pi)) with hr
  set k : ℤ := ⌊(θ - (cutAng S - Real.pi)) / (2 * Real.pi)⌋ with hk
  have hkey : θ - (cutAng S - Real.pi) = r + (k : ℝ) * (2 * Real.pi) := by
    rw [hr, hk, Work.Smooth.SphereJordan.perPt]; ring
  have hθ : θ = (cutAng S - Real.pi + r) + (k : ℝ) * (2 * Real.pi) := by linarith
  rw [hθ]
  exact halfCirclePoint_add_int_two_pi (cutAng S - Real.pi + r) k

/-! ## The curve traced by the gluing map on the inner circle -/

def betaC (D : SourceData S) (K : TwoCuts S) (θ : ℝ) : ℂ :=
  glueFun D K
    (((Work.Smooth.SphereJordan.halfCirclePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ))

theorem glueFun_inner_mem_trace (D : SourceData S) (K : TwoCuts S) (θ : ℝ) :
    ∃ θ' : ℝ, betaC D K θ = γ.γ θ' := by
  rw [betaC, halfCirclePoint_reduce (S := S) θ]
  set r := Work.Smooth.SphereJordan.perPt (θ - (cutAng S - Real.pi)) with hr
  obtain ⟨hr0', hr2'⟩ := Work.SphereJordan.perPt_mem (θ - (cutAng S - Real.pi))
  have hr0 : 0 ≤ r := by rw [hr]; exact hr0'
  have hr2 : r < 2 * Real.pi := by rw [hr]; exact hr2'
  rcases lt_or_ge r Real.pi with hlt | hge
  · rw [halfCirclePoint_innerPtDn, glueFun_innerDn D K r hr0 (le_of_lt hlt),
      TwoCuts.Td_inner K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K r hr0 (le_of_lt hlt)]
    by_cases hb : K.b = true
    · rw [if_pos hb]; exact ⟨_, rfl⟩
    · rw [if_neg hb]; exact ⟨_, rfl⟩
  · have h0 : 0 ≤ r - Real.pi := by linarith
    have h1 : r - Real.pi ≤ Real.pi := by linarith
    rw [show cutAng S - Real.pi + r = cutAng S + (r - Real.pi) by ring,
      halfCirclePoint_innerPtUp, glueFun_innerUp D K (r - Real.pi) h0 h1,
      TwoCuts.Tu_inner K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (r - Real.pi) h0 h1]
    by_cases hb : K.b = true
    · rw [if_pos hb]; exact ⟨_, rfl⟩
    · rw [if_neg hb]; exact ⟨_, rfl⟩

theorem continuous_betaC (D : SourceData S) (K : TwoCuts S) : Continuous (betaC D K) := by
  have hval : Continuous fun θ : ℝ =>
      ((Work.Smooth.SphereJordan.halfCirclePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ) :=
    continuous_subtype_val.comp Work.SphereJordan.continuous_halfCirclePoint
  have hbase : Continuous fun θ : ℝ =>
      (⟨((Work.Smooth.SphereJordan.halfCirclePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ),
        halfCirclePoint_mem_Msub θ⟩ : ↥(Msub)) :=
    Continuous.subtype_mk hval _
  exact (continuous_glueM D K).comp hbase

theorem betaC_periodic (D : SourceData S) (K : TwoCuts S) :
    ∀ θ : ℝ, betaC D K (θ + 2 * Real.pi) = betaC D K θ := by
  intro θ
  rw [betaC, betaC, Work.SphereJordan.halfCirclePoint_add_two_pi]

theorem betaC_injOn (D : SourceData S) (K : TwoCuts S) :
    Set.InjOn (betaC D K) (Set.Ico 0 (2 * Real.pi)) := by
  intro a ha b hb hab
  have h1 : ((Work.Smooth.SphereJordan.halfCirclePoint a : Work.Smooth.SphereJordan.Disc) : ℂ) =
      ((Work.Smooth.SphereJordan.halfCirclePoint b : Work.Smooth.SphereJordan.Disc) : ℂ) :=
    glueFun_injOn D K (halfCirclePoint_mem_Msub a) (halfCirclePoint_mem_Msub b) hab
  exact Work.SphereJordan.halfCirclePoint_injOn_Ico ha hb (Subtype.ext h1)

theorem not_isBounded_U {c : Work.Smooth.Jordan.PlaneCurve}
    (d : Work.Smooth.Jordan.PlaneSeparation c) : ¬ Bornology.IsBounded d.U := by
  have hcomp : IsCompact c.trace := by
    rw [Work.Smooth.Jordan.PlaneCurve.trace_eq_image_Icc]
    exact isCompact_Icc.image c.cont
  obtain ⟨R, hR⟩ := hcomp.isBounded.exists_norm_le
  have hR0 : 0 ≤ R := le_trans (norm_nonneg (c.γ 0)) (hR _ ⟨0, rfl⟩)
  have hnb : ¬ Bornology.IsBounded c.traceᶜ := by
    intro hb
    obtain ⟨C, hC⟩ := hb.exists_norm_le
    have hXpos : 0 < max C R + 1 := by linarith [le_max_right C R, hR0]
    have hnormX : ‖(((max C R + 1 : ℝ)) : ℂ)‖ = max C R + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hXpos]
    have hmem : (((max C R + 1 : ℝ)) : ℂ) ∈ c.traceᶜ := by
      intro hxc
      have h1 := hR _ hxc
      rw [hnormX] at h1
      have h2 : R < max C R + 1 := by linarith [le_max_right C R]
      linarith
    have h2 := hC _ hmem
    rw [hnormX] at h2
    have h3 : C < max C R + 1 := by linarith [le_max_left C R]
    linarith
  intro hU
  have : Bornology.IsBounded c.traceᶜ := by
    rw [← d.union_eq]
    exact hU.union d.bounded_V
  exact hnb this

theorem V_eq_compl {c : Work.Smooth.Jordan.PlaneCurve}
    (d : Work.Smooth.Jordan.PlaneSeparation c) : d.V = c.traceᶜ \ d.U := by
  ext x
  constructor
  · intro hx
    refine ⟨d.union_eq ▸ Or.inr hx, fun hxU => Set.disjoint_left.mp d.disjoint_UV hxU hx⟩
  · rintro ⟨hxt, hxU⟩
    have : x ∈ d.U ∪ d.V := by rw [d.union_eq]; exact hxt
    rcases this with h' | h'
    · exact absurd h' hxU
    · exact h'

theorem V_eq_of_trace_eq {c₁ c₂ : Work.Smooth.Jordan.PlaneCurve}
    (h : c₁.trace = c₂.trace)
    (S₁ : Work.Smooth.Jordan.PlaneSchoenflies c₁)
    (S₂ : Work.Smooth.Jordan.PlaneSchoenflies c₂) : S₁.V = S₂.V := by
  have hV₁ : S₁.V ⊆ c₂.traceᶜ := by
    rw [← h]
    intro x hx
    exact S₁.union_eq ▸ Or.inr hx
  have hV₂ : S₂.V ⊆ c₁.traceᶜ := by
    rw [h]
    intro x hx
    exact S₂.union_eq ▸ Or.inr hx
  have hU₁ : S₁.U ⊆ c₂.traceᶜ := by
    rw [← h]
    intro x hx
    exact S₁.union_eq ▸ Or.inl hx
  have hU₂ : S₂.U ⊆ c₁.traceᶜ := by
    rw [h]
    intro x hx
    exact S₂.union_eq ▸ Or.inl hx
  rcases S₁.preconn_V.subset_or_subset S₂.isOpen_U S₂.isOpen_V S₂.disjoint_UV
      (by rw [S₂.union_eq]; exact hV₁) with h1 | h1
  · rcases S₂.preconn_V.subset_or_subset S₁.isOpen_U S₁.isOpen_V S₁.disjoint_UV
        (by rw [S₁.union_eq]; exact hV₂) with h2 | h2
    · rcases S₁.preconn_U.subset_or_subset S₂.isOpen_U S₂.isOpen_V S₂.disjoint_UV
          (by rw [S₂.union_eq]; exact hU₁) with h3 | h3
      · rcases S₂.preconn_U.subset_or_subset S₁.isOpen_U S₁.isOpen_V S₁.disjoint_UV
            (by rw [S₁.union_eq]; exact hU₂) with h4 | h4
        · have hUeq : S₁.U = S₂.U := Set.Subset.antisymm h3 h4
          rw [V_eq_compl S₁.toPlaneSeparation, V_eq_compl S₂.toPlaneSeparation, h, hUeq]
        · exact absurd (S₁.bounded_V.subset h4) (not_isBounded_U S₂.toPlaneSeparation)
      · exact absurd (S₂.bounded_V.subset h3) (not_isBounded_U S₁.toPlaneSeparation)
    · exfalso
      obtain ⟨y, hy⟩ := S₂.nonempty_V
      exact Set.disjoint_left.mp S₂.disjoint_UV (h1 (h2 hy)) hy
  · rcases S₂.preconn_V.subset_or_subset S₁.isOpen_U S₁.isOpen_V S₁.disjoint_UV
        (by rw [S₁.union_eq]; exact hV₂) with h2 | h2
    · exfalso
      obtain ⟨y, hy⟩ := S₁.nonempty_V
      exact Set.disjoint_left.mp S₁.disjoint_UV (h2 (h1 hy)) hy
    · exact Set.Subset.antisymm h1 h2

/-! ## The inner circle as the boundary of a second Schoenflies disc -/

theorem range_betaC (D : SourceData S) (K : TwoCuts S) (hs : γ.IsSimple) :
    Set.range (betaC D K) = γ.trace := by
  refine Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic (continuous_betaC D K)
    (betaC_periodic D K) (betaC_injOn D K) γ.cont γ.periodic hs ?_
  rintro _ ⟨θ, rfl⟩
  obtain ⟨θ', hθ'⟩ := glueFun_inner_mem_trace D K θ
  exact ⟨θ', hθ'.symm⟩

/-- The inner boundary curve, as a plane curve. -/
def betaCurve (D : SourceData S) (K : TwoCuts S) : Work.Smooth.Jordan.PlaneCurve where
  γ := betaC D K
  cont := continuous_betaC D K
  periodic := betaC_periodic D K

theorem betaCurve_isSimple (D : SourceData S) (K : TwoCuts S) :
    (betaCurve D K).IsSimple := betaC_injOn D K

/-- A Schoenflies datum for the inner boundary curve. -/
def betaSch (D : SourceData S) (K : TwoCuts S) (h : Work.Smooth.SphereJordan.PlaneHypothesis) :
    Work.Smooth.Jordan.PlaneSchoenflies (betaCurve D K) :=
  (h (betaCurve D K) (betaCurve_isSimple D K)).some

theorem betaSch_boundary (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (θ : ℝ) :
    (betaSch D K h).e (Work.Smooth.SphereJordan.circlePoint θ) = betaC D K θ :=
  (betaSch D K h).boundary θ

theorem trace_betaCurve (D : SourceData S) (K : TwoCuts S) (hs : γ.IsSimple) :
    (betaCurve D K).trace = γ.trace := by
  show Set.range (betaC D K) = γ.trace
  exact range_betaC D K hs

theorem V_beta_eq (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple) :
    (betaSch D K h).V = S.V :=
  V_eq_of_trace_eq (c₁ := betaCurve D K) (c₂ := γ) (trace_betaCurve D K hs) _ _

/-! ## The gluing map is the identity on the boundary circle -/

theorem outerPt_eq_circlePoint (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    outerPt S x =
      ((Work.Smooth.SphereJordan.circlePoint (cutAng S + Real.pi * x) :
        Work.Smooth.SphereJordan.Disc) : ℂ) := by
  rw [outerPt, Work.Smooth.Jordan.circlePoint_coe]

theorem outerPtDn_eq_circlePoint (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    outerPtDn S x =
      ((Work.Smooth.SphereJordan.circlePoint (cutAng S + Real.pi + Real.pi * x) :
        Work.Smooth.SphereJordan.Disc) : ℂ) := by
  rw [outerPtDn, Work.Smooth.Jordan.circlePoint_coe]

theorem circlePoint_perPt_reduce (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) :
    Work.Smooth.SphereJordan.circlePoint θ =
      Work.Smooth.SphereJordan.circlePoint
        (cutAng S + Work.Smooth.SphereJordan.perPt (θ - cutAng S)) := by
  set r := Work.Smooth.SphereJordan.perPt (θ - cutAng S) with hr
  set k : ℤ := ⌊(θ - cutAng S) / (2 * Real.pi)⌋ with hk
  have hkey : θ - cutAng S = r + (k : ℝ) * (2 * Real.pi) := by
    rw [hr, hk, Work.Smooth.SphereJordan.perPt]; ring
  have hθ : θ = (cutAng S + r) + (k : ℝ) * (2 * Real.pi) := by linarith
  rw [hθ]
  exact circlePoint_add_int_two_pi (cutAng S + r) k

theorem glueFun_circlePoint (D : SourceData S) (K : TwoCuts S) (θ : ℝ) :
    glueFun D K (((Work.Smooth.SphereJordan.circlePoint θ :
        Work.Smooth.SphereJordan.Disc) : ℂ)) =
      ((Work.Smooth.SphereJordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ) := by
  rw [circlePoint_perPt_reduce (S := S) θ]
  set r := Work.Smooth.SphereJordan.perPt (θ - cutAng S) with hr
  obtain ⟨hr0, hr2⟩ := Work.SphereJordan.perPt_mem (θ - cutAng S)
  have hr0' : 0 ≤ r := by rw [hr]; exact hr0
  have hr2' : r < 2 * Real.pi := by rw [hr]; exact hr2
  rcases lt_or_ge r Real.pi with hlt | hge
  · have hx0 : 0 ≤ r / Real.pi := div_nonneg hr0' Real.pi_pos.le
    have hx1 : r / Real.pi ≤ 1 := by
      rw [div_le_one Real.pi_pos]; exact le_of_lt hlt
    have hpt : outerPt S (r / Real.pi) =
        ((Work.Smooth.SphereJordan.circlePoint (cutAng S + r) :
          Work.Smooth.SphereJordan.Disc) : ℂ) := by
      rw [outerPt_eq_circlePoint,
        show cutAng S + Real.pi * (r / Real.pi) = cutAng S + r by field_simp]
    rw [← hpt]
    exact glueFun_outer D K (r / Real.pi) hx0 hx1
  · have hy0 : 0 ≤ (r - Real.pi) / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
    have hy1 : (r - Real.pi) / Real.pi ≤ 1 := by
      rw [div_le_one Real.pi_pos]; linarith
    have hpt : outerPtDn S ((r - Real.pi) / Real.pi) =
        ((Work.Smooth.SphereJordan.circlePoint (cutAng S + r) :
          Work.Smooth.SphereJordan.Disc) : ℂ) := by
      rw [outerPtDn_eq_circlePoint,
        show cutAng S + Real.pi + Real.pi * ((r - Real.pi) / Real.pi) = cutAng S + r by
          field_simp; ring]
    rw [← hpt]
    exact glueFun_outerDn D K ((r - Real.pi) / Real.pi) hy0 hy1

/-! ## The gluing map on the model annulus -/

theorem glueFun_mem_annulus (D : SourceData S) (K : TwoCuts S) {z : ℂ} (hz : z ∈ Msub) :
    glueFun D K z ∈ Work.Smooth.SphereJordan.annulus S := by
  have hz' : z ∈ Hup D ∪ Hdn D := by rw [Hup_union_Hdn D]; exact hz
  have hmem : glueFun D K z ∈ Set.range (glueU D K) ∪ Set.range (glueD D K) := by
    rcases hz' with h1 | h1
    · exact Or.inl ⟨⟨z, h1⟩, (glueFun_of_Hup D K h1).symm⟩
    · by_cases h2 : z ∈ Hup D
      · exact Or.inl ⟨⟨z, h2⟩, (glueFun_of_Hup D K h2).symm⟩
      · exact Or.inr ⟨⟨z, h1⟩, (glueFun_of_Hdn D K h1 h2).symm⟩
  rw [← K.htil, ← range_glueU D K, ← range_glueD D K]
  exact hmem

/-! ## The assembled map on the model disc -/

theorem coe_mem_Msub_of_le (z : Work.Smooth.SphereJordan.Disc)
    (hz : (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖) :
    ((z : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ Msub := by
  refine ⟨hz, ?_⟩
  have h := z.2
  rw [Metric.mem_closedBall, dist_zero_right] at h
  exact h

theorem dbl_mem_closedBall {z : Work.Smooth.SphereJordan.Disc}
    (hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2) :
    (2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  linarith

theorem exists_halfCirclePoint_eq (z : Work.Smooth.SphereJordan.Disc)
    (hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 / 2) :
    ∃ θ : ℝ, Work.Smooth.SphereJordan.halfCirclePoint θ = z := by
  have h2 : ‖((2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ))‖ = 1 := by
    rw [norm_mul, hz]
    have h3 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h3]
    norm_num
  obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq
    ⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ), by
      rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_eq h2⟩ h2
  refine ⟨θ, Subtype.ext ?_⟩
  rw [Work.Smooth.SphereJordan.halfCirclePoint_coe]
  have hval : ((Work.Smooth.Jordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)
      = (2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ) := Subtype.ext_iff.mp hθ
  rw [hval]
  ring

def Gc (D : SourceData S) (K : TwoCuts S) (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (z : Work.Smooth.SphereJordan.Disc) : ℂ :=
  if hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2 then
    (betaSch D K h).e
      ⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ), dbl_mem_closedBall hz⟩
  else glueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ)

theorem Gc_inner (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) {z : Work.Smooth.SphereJordan.Disc}
    (hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2) :
    Gc D K h z = (betaSch D K h).e
      ⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ), dbl_mem_closedBall hz⟩ := by
  rw [Gc, dif_pos hz]

theorem Gc_outer (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) {z : Work.Smooth.SphereJordan.Disc}
    (hz : ¬ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2) :
    Gc D K h z = glueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ) := by
  rw [Gc, dif_neg hz]

theorem Gc_eq_glueFun_of_half (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) {z : Work.Smooth.SphereJordan.Disc}
    (hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 / 2) :
    Gc D K h z = glueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ) := by
  obtain ⟨θ, hθ⟩ := exists_halfCirclePoint_eq z hz
  rw [Gc_inner D K h hz.le]
  have hpt : (⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ),
      dbl_mem_closedBall hz.le⟩ : Work.Smooth.SphereJordan.Disc) =
      Work.Smooth.SphereJordan.circlePoint θ := by
    refine Subtype.ext ?_
    show (2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ) =
      ((Work.Smooth.SphereJordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)
    rw [← hθ, Work.Smooth.SphereJordan.halfCirclePoint_coe]
    ring
  rw [hpt, betaSch_boundary D K h θ]
  show betaC D K θ = glueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ)
  rw [betaC, hθ]

theorem Gc_mem_Vbeta (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) {z : Work.Smooth.SphereJordan.Disc}
    (hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 / 2) :
    Gc D K h z ∈ (betaSch D K h).V := by
  rw [Gc_inner D K h hz.le]
  rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq (betaSch D K h)]
  refine ⟨⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ),
    dbl_mem_closedBall hz.le⟩, ?_, rfl⟩
  show ‖(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1
  rw [norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  linarith

theorem Gc_notMem_Vbeta (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    {z : Work.Smooth.SphereJordan.Disc}
    (hz : (1 : ℝ) / 2 < ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖) :
    Gc D K h z ∉ (betaSch D K h).V := by
  rw [Gc_outer D K h (not_le.mpr hz), V_beta_eq D K h hs]
  exact (glueFun_mem_annulus D K (coe_mem_Msub_of_le z hz.le)).2

theorem continuousOn_Gc_inner (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) :
    ContinuousOn (Gc D K h)
      {z : Work.Smooth.SphereJordan.Disc |
        ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hh : ({z : Work.Smooth.SphereJordan.Disc |
      ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2}).domRestrict (Gc D K h) =
      fun z : {z : Work.Smooth.SphereJordan.Disc |
        ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2} =>
        (betaSch D K h).e ⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ),
          dbl_mem_closedBall z.2⟩ := by
    funext z
    exact Gc_inner D K h z.2
  rw [hh]
  exact (betaSch D K h).e.continuous.comp
    (Continuous.subtype_mk (by fun_prop) (fun z => dbl_mem_closedBall z.2))

theorem continuousOn_Gc_outer (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) :
    ContinuousOn (Gc D K h)
      {z : Work.Smooth.SphereJordan.Disc |
        (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hh : ({z : Work.Smooth.SphereJordan.Disc |
      (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖}).domRestrict (Gc D K h) =
      fun z : {z : Work.Smooth.SphereJordan.Disc |
        (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖} =>
        glueM D K ⟨((z : Work.Smooth.SphereJordan.Disc) : ℂ),
          coe_mem_Msub_of_le (z : Work.Smooth.SphereJordan.Disc) z.2⟩ := by
    funext z
    by_cases hlt : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2
    · have hzeq : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 / 2 :=
        le_antisymm hlt z.2
      rw [Set.domRestrict_apply, Gc_eq_glueFun_of_half D K h hzeq]
      exact (glueM_apply D K ⟨((z : Work.Smooth.SphereJordan.Disc) : ℂ),
        coe_mem_Msub_of_le (z : Work.Smooth.SphereJordan.Disc) z.2⟩).symm
    · rw [Set.domRestrict_apply, Gc_outer D K h hlt]
      exact (glueM_apply D K ⟨((z : Work.Smooth.SphereJordan.Disc) : ℂ),
        coe_mem_Msub_of_le (z : Work.Smooth.SphereJordan.Disc) z.2⟩).symm
  rw [hh]
  exact (continuous_glueM D K).comp
    (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
      (fun z => coe_mem_Msub_of_le (z : Work.Smooth.SphereJordan.Disc) z.2))

theorem continuous_Gc (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) : Continuous (Gc D K h) := by
  have hA : IsClosed {z : Work.Smooth.SphereJordan.Disc |
      ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2} :=
    isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const
  have hB : IsClosed {z : Work.Smooth.SphereJordan.Disc |
      (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖} :=
    isClosed_le continuous_const (continuous_norm.comp continuous_subtype_val)
  have hcov : ({z : Work.Smooth.SphereJordan.Disc |
        ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2} ∪
      {z : Work.Smooth.SphereJordan.Disc |
        (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖}) = univ := by
    ext z
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact le_total _ _
  refine LocallyFinite.continuous (f := fun i : Bool =>
      bif i then {z : Work.Smooth.SphereJordan.Disc |
          ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2}
        else {z : Work.Smooth.SphereJordan.Disc |
          (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖})
    (locallyFinite_of_finite _) ?_ ?_ ?_
  · have hunion : (⋃ i : Bool, bif i then {z : Work.Smooth.SphereJordan.Disc |
          ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2}
        else {z : Work.Smooth.SphereJordan.Disc |
          (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖}) =
        ({z : Work.Smooth.SphereJordan.Disc |
            ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2} ∪
          {z : Work.Smooth.SphereJordan.Disc |
            (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖}) := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_union, Bool.exists_bool, Bool.cond_true,
        Bool.cond_false]
      tauto
    rw [hunion, hcov]
  · intro i
    cases i
    · simpa only [Bool.cond_false] using hB
    · simpa only [Bool.cond_true] using hA
  · intro i
    cases i
    · simpa only [Bool.cond_false] using continuousOn_Gc_outer D K h
    · simpa only [Bool.cond_true] using continuousOn_Gc_inner D K h

theorem Gc_mem_closedBall (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (z : Work.Smooth.SphereJordan.Disc) :
    Gc D K h z ∈ Metric.closedBall (0 : ℂ) 1 := by
  by_cases hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2
  · rw [Gc_inner D K h hz]
    have h1 : (betaSch D K h).e ⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ),
        dbl_mem_closedBall hz⟩ ∈ closure (betaSch D K h).V := by
      rw [← (betaSch D K h).range_e]
      exact ⟨_, rfl⟩
    rw [V_beta_eq D K h hs] at h1
    have h2 := Work.Smooth.SphereJordan.closure_V_subset_openBall S hball h1
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt h2
  · rw [Gc_outer D K h hz]
    exact (glueFun_mem_annulus D K
      (coe_mem_Msub_of_le z (le_of_lt (not_le.mp hz)))).1

def G (D : SourceData S) (K : TwoCuts S) (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) :
    C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc) :=
  ⟨fun z => ⟨Gc D K h z, Gc_mem_closedBall D K h hs hball z⟩,
    Continuous.subtype_mk (continuous_Gc D K h) _⟩

theorem G_apply (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (z : Work.Smooth.SphereJordan.Disc) :
    ((G D K h hs hball z : Work.Smooth.SphereJordan.Disc) : ℂ) = Gc D K h z := rfl

theorem Gc_injective (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (_hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) : Function.Injective (Gc D K h) := by
  intro z z' h'
  by_cases hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2
  · by_cases hz' : ‖((z' : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2
    · rw [Gc_inner D K h hz, Gc_inner D K h hz'] at h'
      have h2 : (⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ),
          dbl_mem_closedBall hz⟩ : Work.Smooth.SphereJordan.Disc) =
          ⟨(2 : ℂ) * ((z' : Work.Smooth.SphereJordan.Disc) : ℂ),
            dbl_mem_closedBall hz'⟩ := (betaSch D K h).inj h'
      have h3 : (2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ) =
          (2 : ℂ) * ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) := Subtype.ext_iff.mp h2
      have h4 : ((z : Work.Smooth.SphereJordan.Disc) : ℂ) =
          ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) := by
        have h5 := congrArg (fun w : ℂ => (2 : ℂ)⁻¹ * w) h3
        simpa [mul_assoc] using h5
      exact Subtype.ext h4
    · have hz'2 : (1 : ℝ) / 2 < ‖((z' : Work.Smooth.SphereJordan.Disc) : ℂ)‖ :=
        not_le.mp hz'
      by_cases hzlt : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 / 2
      · have h1 : Gc D K h z' ∈ (betaSch D K h).V := h' ▸ Gc_mem_Vbeta D K h hzlt
        exact absurd h1 (Gc_notMem_Vbeta D K h hs hz'2)
      · have hzeq : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 / 2 :=
          le_antisymm hz (not_lt.mp hzlt)
        have hzM : ((z : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ Msub :=
          coe_mem_Msub_of_le z hzeq.ge
        have hz'M : ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ Msub :=
          coe_mem_Msub_of_le z' hz'2.le
        have hglue : glueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ) =
            glueFun D K ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) := by
          have h1 : Gc D K h z = glueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ) :=
            Gc_eq_glueFun_of_half D K h hzeq
          have h2 : Gc D K h z' = glueFun D K ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) :=
            Gc_outer D K h hz'
          rw [← h1, h', h2]
        rw [glueFun_injOn D K hzM hz'M hglue] at hzeq
        linarith
  · have hz2 : (1 : ℝ) / 2 < ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ := not_le.mp hz
    by_cases hz' : ‖((z' : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2
    · by_cases hz'lt : ‖((z' : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 / 2
      · have h1 : Gc D K h z' ∈ (betaSch D K h).V := Gc_mem_Vbeta D K h hz'lt
        rw [← h'] at h1
        exact absurd h1 (Gc_notMem_Vbeta D K h hs hz2)
      · have hz'eq : ‖((z' : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 / 2 :=
          le_antisymm hz' (not_lt.mp hz'lt)
        have hzM : ((z : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ Msub :=
          coe_mem_Msub_of_le z hz2.le
        have hz'M : ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ Msub :=
          coe_mem_Msub_of_le z' hz'eq.ge
        have hglue : glueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ) =
            glueFun D K ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) := by
          have h1 : Gc D K h z = glueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ) :=
            Gc_outer D K h hz
          have h2 : Gc D K h z' = glueFun D K ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) :=
            Gc_eq_glueFun_of_half D K h hz'eq
          rw [← h1, h', h2]
        exact Subtype.ext (glueFun_injOn D K hzM hz'M hglue)
    · have hz'M : ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ Msub :=
        coe_mem_Msub_of_le z' (not_le.mp hz').le
      have hzM : ((z : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ Msub :=
        coe_mem_Msub_of_le z hz2.le
      rw [Gc_outer D K h hz, Gc_outer D K h hz'] at h'
      exact Subtype.ext (glueFun_injOn D K hzM hz'M h')

theorem G_injective (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (_hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) : Function.Injective (G D K h hs _hball) := by
  intro z z' h'
  refine Gc_injective D K h hs _hball ?_
  simpa only [G_apply] using congrArg
    (fun w : Work.Smooth.SphereJordan.Disc => ((w : Work.Smooth.SphereJordan.Disc) : ℂ)) h'

theorem G_circlePoint (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (θ : ℝ) :
    G D K h hs hball (Work.Smooth.SphereJordan.circlePoint θ) =
      Work.Smooth.SphereJordan.circlePoint θ := by
  refine Subtype.ext ?_
  show Gc D K h (Work.Smooth.SphereJordan.circlePoint θ) =
    ((Work.Smooth.SphereJordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)
  have hnorm : ‖((Work.Smooth.SphereJordan.circlePoint θ :
      Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 :=
    Work.SphereJordan.TwoCutsAsm.circlePoint_cp_norm θ
  rw [Gc_outer D K h (by rw [hnorm]; norm_num)]
  exact glueFun_circlePoint D K θ

theorem G_halfCirclePoint (D : SourceData S) (K : TwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (θ : ℝ) :
    ∃ θ' : ℝ, ((G D K h hs hball (Work.Smooth.SphereJordan.halfCirclePoint θ) :
      Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ' := by
  have hnorm : ‖((Work.Smooth.SphereJordan.halfCirclePoint θ :
      Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 / 2 := norm_halfCirclePoint θ
  have hval : Gc D K h (Work.Smooth.SphereJordan.halfCirclePoint θ) =
      (betaSch D K h).e (Work.Smooth.SphereJordan.circlePoint θ) := by
    rw [Gc_inner D K h hnorm.le]
    have hpt : (⟨(2 : ℂ) * ((Work.Smooth.SphereJordan.halfCirclePoint θ :
        Work.Smooth.SphereJordan.Disc) : ℂ), dbl_mem_closedBall hnorm.le⟩ :
        Work.Smooth.SphereJordan.Disc) = Work.Smooth.SphereJordan.circlePoint θ := by
      refine Subtype.ext ?_
      show (2 : ℂ) * ((Work.Smooth.SphereJordan.halfCirclePoint θ :
        Work.Smooth.SphereJordan.Disc) : ℂ) =
        ((Work.Smooth.SphereJordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)
      rw [Work.Smooth.SphereJordan.halfCirclePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
      ring
    rw [hpt]
  obtain ⟨θ', hθ'⟩ := glueFun_inner_mem_trace D K θ
  exact ⟨θ', by rw [G_apply, hval, betaSch_boundary D K h θ, betaC]; exact hθ'⟩

end

end Assembly

theorem twoCutsAssembly (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) + (t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) - (t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
    (T_up : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.tgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (T_dn : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.tgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (htil : closure T_up.V ∪ closure T_dn.V = Work.Smooth.SphereJordan.annulus S)
    (hmeet : closure T_up.V ∩ closure T_dn.V =
      Work.Smooth.SphereJordan.cut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.cut₂ S t₂ s₂) :
    ∃ (F : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc)) (s : ℝ),
      (s = 1 ∨ s = -1) ∧ Function.Injective F ∧
      (∀ θ : ℝ, F (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ θ : ℝ, ((F (Work.Smooth.SphereJordan.halfCirclePoint (s * θ)) :
          Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ) := by
  let K : TwoCuts S :=
    { t₁ := t₁, s₁ := s₁, t₂ := t₂, s₂ := s₂, b := b, θ₁ := θ₁, θ₂ := θ₂,
      hout₁ := hout₁, hout₂ := hout₂, hθ₁ := hθ₁, hθ₂ := hθ₂,
      Tu := T_up, Td := T_dn, htil := htil, hmeet := hmeet }
  obtain ⟨D⟩ := exists_sourceData h S
  exact Work.SphereJordan.annulusInnerReparam hball S
    (Assembly.G D K h hs hball) (Assembly.G_injective D K h hs hball)
    (Assembly.G_circlePoint D K h hs hball) (Assembly.G_halfCirclePoint D K h hs hball)

end

end Work.SphereJordan.TwoCutsAsm
