import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.coreAuxTwoCuts
import Submission.Work.Smooth.SphereJordan.PCopy.tgtUpPC_isSimple
import Submission.Work.Smooth.SphereJordan.PCopy.srcBranches
import Submission.Work.Smooth.SphereJordan.PCopy.annulusSourceSpans
import Submission.Work.Smooth.SphereJordan.annulusInterpolation
import Submission.Work.Smooth.SphereJordan.ballHomeo_of_circleHomeo
import Submission.Work.Smooth.SphereJordan.PCopy.annulusInnerReparam

/-!
# The two-pccuts assembly of the planar pcannulus theorem

Given two plane Schoenflies discs `T_up`, `T_dn` of the two four-arc curves `pctgtUpB`, `pctgtDnB`
whose closures tile the pcannulus `pcannulus S` and meet in the two crosscuts, we assemble a
continuous injection `pcG : 𝔻 → 𝔻` fixing `∂𝔻` pointwise with `pcG` of the inner circle contained in
`γ`, and apply `Work.SphereJordan.pcannulusInnerReparam`.

The model pcannulus `{1/2 ≤ ‖z‖ ≤ 1}` is glued to the target pcannulus `pcannulus S` by matching the
boundary parameters of the source maps `Ψu, Ψd` (from `Work.SphereJordan.pcannulusSourceSpans`) with
those of the target boundary curves `pctgtUpB`, `pctgtDnB`.
-/

open Set

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## Elementary facts about `circlePoint`, and the angle of `pccutDir S` -/

theorem pccirclePoint_cp_add (a b : ℝ) :
    ((Work.Smooth.SphereJordan.circlePoint (a + b) : Work.Smooth.SphereJordan.Disc) : ℂ) =
      ((Work.Smooth.SphereJordan.circlePoint a : Work.Smooth.SphereJordan.Disc) : ℂ) *
      ((Work.Smooth.SphereJordan.circlePoint b : Work.Smooth.SphereJordan.Disc) : ℂ) := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe,
    Work.Smooth.Jordan.circlePoint_coe, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem pccirclePoint_cp_norm (a : ℝ) :
    ‖((Work.Smooth.SphereJordan.circlePoint a : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

theorem pccirclePoint_cp_neg (a : ℝ) :
    -((Work.Smooth.SphereJordan.circlePoint a : Work.Smooth.SphereJordan.Disc) : ℂ) =
      ((Work.Smooth.SphereJordan.circlePoint (a + Real.pi) :
        Work.Smooth.SphereJordan.Disc) : ℂ) := by
  rw [pccirclePoint_cp_add, Work.SphereJordan.pccp_pi]
  ring

theorem pcexp_pi_mul_I : Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) = -1 :=
  Work.SphereJordan.pccp_pi

theorem pcexists_cutAngle (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ α : ℝ, ((Work.Smooth.SphereJordan.circlePoint α : Work.Smooth.SphereJordan.Disc) : ℂ) =
      Work.Smooth.SphereJordan.pccutDir S := by
  obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq
    ⟨Work.Smooth.SphereJordan.pccutDir S, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq (Work.Smooth.SphereJordan.pcnorm_cutDir S)⟩
    (Work.Smooth.SphereJordan.pcnorm_cutDir S)
  exact ⟨θ, congrArg Subtype.val hθ⟩

/-- A parameter of the point `pccutDir S` on the boundary circle. -/
def pccutAng (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : ℝ := Classical.choose (pcexists_cutAngle S)

theorem pccutAng_spec (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ((Work.Smooth.SphereJordan.circlePoint (pccutAng S) : Work.Smooth.SphereJordan.Disc) : ℂ) =
      Work.Smooth.SphereJordan.pccutDir S := Classical.choose_spec (pcexists_cutAngle S)

/-- The "upper outer" boundary point of the model disc at arc parameter `x ∈ [0,1]`:
`e^{i(pccutAng S + π x)}`.  It equals `pcsrcOuterUp S x`. -/
def pcouterPt (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) : ℂ :=
  Complex.exp (((pccutAng S + Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The "lower outer" boundary point: `e^{i(pccutAng S + π + π x)}`. -/
def pcouterPtDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) : ℂ :=
  Complex.exp (((pccutAng S + Real.pi + Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The "upper inner" point of the model disc at angle parameter `θ ∈ [0,π]`. -/
def pcinnerPtUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) : ℂ :=
  (1 / 2 : ℂ) * Complex.exp (((pccutAng S + θ : ℝ) : ℂ) * Complex.I)

/-- The "lower inner" point of the model disc at angle parameter `θ ∈ [0,π]`: the point
`(1/2) e^{i(pccutAng S - π + θ)}`, which runs from `-pccutDir S/2` to `pccutDir S/2`. -/
def pcinnerPtDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) : ℂ :=
  (1 / 2 : ℂ) * Complex.exp (((pccutAng S - Real.pi + θ : ℝ) : ℂ) * Complex.I)

theorem pcneg_exp_eq (a : ℝ) :
    -Complex.exp ((a : ℂ) * Complex.I) =
      Complex.exp (((a + Real.pi : ℝ) : ℂ) * Complex.I) := by
  have h1 : Complex.exp (((a + Real.pi : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((a : ℂ) * Complex.I) * Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, pcexp_pi_mul_I]
  ring

theorem pcouterPt_eq_src (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    pcouterPt S x = Work.Smooth.SphereJordan.pcsrcOuterUp S x := by
  rw [Work.SphereJordan.pcsrcOuterUp_cp, pcouterPt, ← pccutAng_spec S, Work.Smooth.Jordan.circlePoint_coe,
    Work.Smooth.Jordan.circlePoint_coe, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem pcouterPtDn_eq_src (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    pcouterPtDn S x = Work.Smooth.SphereJordan.pcsrcOuterDn S x := by
  unfold pcouterPtDn Work.Smooth.SphereJordan.pcsrcOuterDn
  rw [← pccutAng_spec S, Work.Smooth.Jordan.circlePoint_coe]
  rw [pcneg_exp_eq (pccutAng S), ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The source data of `pcannulusSourceSpans` -/

/-- The two source-side spanning discs `Ψ_up`, `Ψ_dn` of the model half-annuli. -/
structure pcSourceData (S : Work.Smooth.Jordan.PlaneSchoenflies γ) where
  Ψu : C(Work.Smooth.SphereJordan.Disc, ℂ)
  Ψd : C(Work.Smooth.SphereJordan.Disc, ℂ)
  inju : Function.Injective Ψu
  injd : Function.Injective Ψd
  bdu : ∀ τ : ℝ, Ψu (Work.Smooth.SphereJordan.circlePoint τ) =
    Work.Smooth.SphereJordan.pcsrcUpB S τ
  bdd : ∀ τ : ℝ, Ψd (Work.Smooth.SphereJordan.circlePoint τ) =
    Work.Smooth.SphereJordan.pcsrcDnB S τ
  union : Set.range ⇑Ψu ∪ Set.range ⇑Ψd =
    Metric.closedBall (0 : ℂ) 1 \ Metric.ball (0 : ℂ) (1 / 2)
  meet : Set.range ⇑Ψu ∩ Set.range ⇑Ψd =
    ({z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
        z = (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S} ∪
     {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
        z = -((σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)})

theorem pcexists_sourceData (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Nonempty (pcSourceData S) := by
  obtain ⟨Ψu, Ψd, h1, h2, h3, h4, h5, h6⟩ := Work.SphereJordan.pcannulusSourceSpans h S
  exact ⟨Ψu, Ψd, h1, h2, h3, h4, h5, h6⟩

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

/-- The upper half-pcannulus of the model disc, as the range of `Ψu`. -/
def pcHup (D : pcSourceData S) : Set ℂ := Set.range ⇑D.Ψu

/-- The lower half-pcannulus of the model disc, as the range of `Ψd`. -/
def pcHdn (D : pcSourceData S) : Set ℂ := Set.range ⇑D.Ψd

/-- The model pcannulus `{1/2 ≤ ‖z‖ ≤ 1}`. -/
def pcMsub : Set ℂ := {z : ℂ | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1}

/-- The inner disc `{‖z‖ ≤ 1/2}`. -/
def pcDsub : Set ℂ := {z : ℂ | ‖z‖ ≤ 1 / 2}

/-- The inner circle `{‖z‖ = 1/2}`. -/
def pcCsub : Set ℂ := {z : ℂ | ‖z‖ = 1 / 2}

theorem pcHup_union_Hdn (D : pcSourceData S) : pcHup D ∪ pcHdn D = pcMsub := by
  rw [pcHup, pcHdn, D.union, pcMsub, Metric.closedBall, Metric.ball]
  ext z
  simp only [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
    Set.mem_ofPred_eq, not_lt]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem pcHup_inter_Hdn (D : pcSourceData S) : pcHup D ∩ pcHdn D =
    ({z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
        z = (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S} ∪
     {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
        z = -((σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)}) := by
  rw [pcHup, pcHdn]
  exact D.meet

/-- The homeomorphism `𝔻 ≃ₜ pcHup` given by `Ψu`. -/
def pcΨuEquiv (D : pcSourceData S) : Work.Smooth.SphereJordan.Disc ≃ ↥(pcHup D) :=
  Equiv.ofBijective (fun z => (⟨D.Ψu z, ⟨z, rfl⟩⟩ : ↥(pcHup D)))
    ⟨fun a b hab => D.inju (Subtype.ext_iff.mp hab),
     fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩⟩

theorem pccontinuous_ΨuEquiv (D : pcSourceData S) : Continuous (pcΨuEquiv D) := by
  refine Continuous.subtype_mk ?_ _
  exact D.Ψu.continuous

/-- `Ψu` as a homeomorphism onto its range. -/
def pcΨuHomeo (D : pcSourceData S) : Work.Smooth.SphereJordan.Disc ≃ₜ ↥(pcHup D) :=
  Continuous.homeoOfEquivCompactToT2 (f := pcΨuEquiv D) (pccontinuous_ΨuEquiv D)

theorem pcΨuHomeo_apply (D : pcSourceData S) (z : Work.Smooth.SphereJordan.Disc) :
    (pcΨuHomeo D z : ℂ) = D.Ψu z := rfl

theorem pcΨuHomeo_symm_apply (D : pcSourceData S) (z : ↥(pcHup D)) :
    D.Ψu ((pcΨuHomeo D).symm z) = (z : ℂ) :=
  congrArg (fun w : ↥(pcHup D) => (w : ℂ)) (Homeomorph.apply_symm_apply (pcΨuHomeo D) z)

theorem pcΨuHomeo_symm_eq_of (D : pcSourceData S) {w : Work.Smooth.SphereJordan.Disc}
    {z : ↥(pcHup D)} (h : pcΨuHomeo D w = z) : (pcΨuHomeo D).symm z = w :=
  (Homeomorph.symm_apply_eq (pcΨuHomeo D)).mpr h.symm

/-- The homeomorphism `𝔻 ≃ₜ pcHdn` given by `Ψd`. -/
def pcΨdEquiv (D : pcSourceData S) : Work.Smooth.SphereJordan.Disc ≃ ↥(pcHdn D) :=
  Equiv.ofBijective (fun z => (⟨D.Ψd z, ⟨z, rfl⟩⟩ : ↥(pcHdn D)))
    ⟨fun a b hab => D.injd (Subtype.ext_iff.mp hab),
     fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩⟩

theorem pccontinuous_ΨdEquiv (D : pcSourceData S) : Continuous (pcΨdEquiv D) := by
  refine Continuous.subtype_mk ?_ _
  exact D.Ψd.continuous

/-- `Ψd` as a homeomorphism onto its range. -/
def pcΨdHomeo (D : pcSourceData S) : Work.Smooth.SphereJordan.Disc ≃ₜ ↥(pcHdn D) :=
  Continuous.homeoOfEquivCompactToT2 (f := pcΨdEquiv D) (pccontinuous_ΨdEquiv D)

theorem pcΨdHomeo_apply (D : pcSourceData S) (z : Work.Smooth.SphereJordan.Disc) :
    (pcΨdHomeo D z : ℂ) = D.Ψd z := rfl

theorem pcΨdHomeo_symm_apply (D : pcSourceData S) (z : ↥(pcHdn D)) :
    D.Ψd ((pcΨdHomeo D).symm z) = (z : ℂ) :=
  congrArg (fun w : ↥(pcHdn D) => (w : ℂ)) (Homeomorph.apply_symm_apply (pcΨdHomeo D) z)

theorem pcΨdHomeo_symm_eq_of (D : pcSourceData S) {w : Work.Smooth.SphereJordan.Disc}
    {z : ↥(pcHdn D)} (h : pcΨdHomeo D w = z) : (pcΨdHomeo D).symm z = w :=
  (Homeomorph.symm_apply_eq (pcΨdHomeo D)).mpr h.symm

/-! ## The values of the source maps on the four arcs of the model half-annuli -/

section SrcVal

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

theorem pchalfPi_mul_sub_bounds (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
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

theorem pchalfPi_mul_2m1_bounds (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    0 ≤ (Real.pi / 2) * (2 * ρ - 1) ∧ (Real.pi / 2) * (2 * ρ - 1) ≤ Real.pi / 2 := by
  have h3 : 0 ≤ 2 * ρ - 1 := by linarith
  have h4 : 2 * ρ - 1 ≤ 1 := by linarith
  refine ⟨mul_nonneg (by positivity) h3, ?_⟩
  calc (Real.pi / 2) * (2 * ρ - 1) ≤ (Real.pi / 2) * 1 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = Real.pi / 2 := by ring

theorem pchalfPi_mul_2m2rho_bounds (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    0 ≤ (Real.pi / 2) * (2 - 2 * ρ) ∧ (Real.pi / 2) * (2 - 2 * ρ) ≤ Real.pi / 2 := by
  have h3 : 0 ≤ 2 - 2 * ρ := by linarith
  have h4 : 2 - 2 * ρ ≤ 1 := by linarith
  refine ⟨mul_nonneg (by positivity) h3, ?_⟩
  calc (Real.pi / 2) * (2 - 2 * ρ) ≤ (Real.pi / 2) * 1 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = Real.pi / 2 := by ring

theorem pcsrcUpB_outer (D : pcSourceData S) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    D.Ψu (Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 * x)) = pcouterPt S x := by
  rw [D.bdu, (Work.SphereJordan.pcsrcBranches S).1 (Real.pi / 2 * x)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show Real.pi / 2 * x / (Real.pi / 2) = x by field_simp]
  exact (pcouterPt_eq_src S x).symm

theorem pcsrcDnB_outer (D : pcSourceData S) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    D.Ψd (Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 * x)) = pcouterPtDn S x := by
  rw [D.bdd, (Work.SphereJordan.pcsrcBranches S).2.2.2.2.1 (Real.pi / 2 * x)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show Real.pi / 2 * x / (Real.pi / 2) = x by field_simp]
  exact (pcouterPtDn_eq_src S x).symm

theorem pcsrcUpB_inner (D : pcSourceData S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    D.Ψu (Work.Smooth.SphereJordan.circlePoint
      (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi))) = pcinnerPtUp S θ := by
  obtain ⟨b0, b1⟩ := pchalfPi_mul_sub_bounds θ h0 h1
  rw [D.bdu, (Work.SphereJordan.pcsrcBranches S).2.2.1
    ((Real.pi / 2) * (1 - θ / Real.pi)) b0 b1]
  rw [show (Real.pi / 2) * (1 - θ / Real.pi) / (Real.pi / 2) = 1 - θ / Real.pi by field_simp]
  rw [Work.Smooth.SphereJordan.pcsrcInnerUp, pcinnerPtUp, ← pccutAng_spec S]
  simp only [Work.Smooth.Jordan.circlePoint_coe]
  have hπ : Real.pi * (1 - (1 - θ / Real.pi)) = θ := by field_simp; ring
  rw [hπ, mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem pcsrcDnB_inner (D : pcSourceData S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    D.Ψd (Work.Smooth.SphereJordan.circlePoint
      (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi))) = pcinnerPtDn S θ := by
  obtain ⟨b0, b1⟩ := pchalfPi_mul_sub_bounds θ h0 h1
  rw [D.bdd, (Work.SphereJordan.pcsrcBranches S).2.2.2.2.2.2.1
    ((Real.pi / 2) * (1 - θ / Real.pi)) b0 b1]
  rw [show (Real.pi / 2) * (1 - θ / Real.pi) / (Real.pi / 2) = 1 - θ / Real.pi by field_simp]
  rw [Work.Smooth.SphereJordan.pcsrcInnerDn, pcinnerPtDn, ← pccutAng_spec S]
  simp only [Work.Smooth.Jordan.circlePoint_coe]
  have hπ : -(Real.pi * (1 - θ / Real.pi)) = -Real.pi + θ := by field_simp; ring
  rw [hπ, mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem pcsrcUpB_radpos (D : pcSourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    D.Ψu (Work.Smooth.SphereJordan.circlePoint
      (3 * Real.pi / 2 + (Real.pi / 2) * (2 * ρ - 1))) =
        (ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  obtain ⟨b0, b1⟩ := pchalfPi_mul_2m1_bounds ρ h1 h2
  rw [D.bdu, (Work.SphereJordan.pcsrcBranches S).2.2.2.1
    ((Real.pi / 2) * (2 * ρ - 1)) b0 b1]
  rw [show (Real.pi / 2) * (2 * ρ - 1) / (Real.pi / 2) / 2 = (ρ - 1 / 2) by field_simp]
  push_cast
  ring

theorem pcsrcDnB_radpos (D : pcSourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    D.Ψd (Work.Smooth.SphereJordan.circlePoint
      (Real.pi / 2 + (Real.pi / 2) * (2 - 2 * ρ))) =
        (ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  obtain ⟨b0, b1⟩ := pchalfPi_mul_2m2rho_bounds ρ h1 h2
  rw [D.bdd, (Work.SphereJordan.pcsrcBranches S).2.2.2.2.2.1
    ((Real.pi / 2) * (2 - 2 * ρ)) b0 b1]
  rw [show (Real.pi / 2) * (2 - 2 * ρ) / (Real.pi / 2) / 2 = (1 - ρ) by field_simp]
  push_cast
  ring

theorem pcsrcUpB_radneg (D : pcSourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    D.Ψu (Work.Smooth.SphereJordan.circlePoint
      (Real.pi / 2 + (Real.pi / 2) * (2 - 2 * ρ))) =
        -((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) := by
  obtain ⟨b0, b1⟩ := pchalfPi_mul_2m2rho_bounds ρ h1 h2
  rw [D.bdu, (Work.SphereJordan.pcsrcBranches S).2.1
    ((Real.pi / 2) * (2 - 2 * ρ)) b0 b1]
  rw [show (Real.pi / 2) * (2 - 2 * ρ) / (Real.pi / 2) / 2 = (1 - ρ) by field_simp]
  push_cast
  ring

theorem pcsrcDnB_radneg (D : pcSourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    D.Ψd (Work.Smooth.SphereJordan.circlePoint
      (3 * Real.pi / 2 + (Real.pi / 2) * (2 * ρ - 1))) =
        -((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) := by
  obtain ⟨b0, b1⟩ := pchalfPi_mul_2m1_bounds ρ h1 h2
  rw [D.bdd, (Work.SphereJordan.pcsrcBranches S).2.2.2.2.2.2.2
    ((Real.pi / 2) * (2 * ρ - 1)) b0 b1]
  rw [show (Real.pi / 2) * (2 * ρ - 1) / (Real.pi / 2) / 2 = (ρ - 1 / 2) by field_simp]
  push_cast
  ring

end SrcVal

/-! ## The two-pccuts configuration -/

/-- The hypotheses of the two-pccuts assembly, bundled: the configuration data, the two spanning
discs of the four-arc curves and the tiling conditions. -/
structure pcTwoCuts (S : Work.Smooth.Jordan.PlaneSchoenflies γ) where
  t₁ : ℝ
  s₁ : ℝ
  t₂ : ℝ
  s₂ : ℝ
  b : Bool
  θ₁ : ℝ
  θ₂ : ℝ
  hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
    Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S
  hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
    Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S
  hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
    (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S
  hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
    (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S
  Tu : Work.Smooth.Jordan.PlaneSchoenflies
    (Work.SphereJordan.pctgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂)
  Td : Work.Smooth.Jordan.PlaneSchoenflies
    (Work.SphereJordan.pctgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂)
  htil : closure Tu.V ∪ closure Td.V = Work.Smooth.SphereJordan.pcannulus S
  hmeet : closure Tu.V ∩ closure Td.V =
    Work.Smooth.SphereJordan.pccut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.pccut₂ S t₂ s₂

namespace pcTwoCuts

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

theorem pcTu_apply (K : pcTwoCuts S) (τ : ℝ) :
    K.Tu.e (Work.Smooth.SphereJordan.circlePoint τ) =
      Work.Smooth.SphereJordan.pctgtUpB S K.t₁ K.s₁ K.t₂ K.s₂ K.b K.θ₁ K.θ₂ τ := by
  rw [K.Tu.boundary]
  exact Work.SphereJordan.pctgtUpPC_apply S K.t₁ K.s₁ K.t₂ K.s₂ K.b K.θ₁ K.θ₂ K.hout₁ K.hout₂
    K.hθ₁ K.hθ₂ τ

theorem pcTd_apply (K : pcTwoCuts S) (τ : ℝ) :
    K.Td.e (Work.Smooth.SphereJordan.circlePoint τ) =
      Work.Smooth.SphereJordan.pctgtDnB S K.t₁ K.s₁ K.t₂ K.s₂ K.b K.θ₁ K.θ₂ τ := by
  rw [K.Td.boundary]
  exact Work.SphereJordan.pctgtDnPC_apply S K.t₁ K.s₁ K.t₂ K.s₂ K.b K.θ₁ K.θ₂ K.hout₁ K.hout₂
    K.hθ₁ K.hθ₂ τ


end pcTwoCuts

theorem pcperPt_two_pi_aux : Work.Smooth.SphereJordan.pcperPt (2 * Real.pi) = 0 := by
  rw [Work.Smooth.SphereJordan.pcperPt]
  rw [div_self (by positivity : (2 * Real.pi) ≠ 0), Int.floor_one]
  norm_num

theorem pcgamma_sub_two_pi (t : ℝ) :
    γ.γ (t - 2 * Real.pi) = γ.γ t := by
  rw [show t - 2 * Real.pi = t + ((-1 : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
  exact Work.Smooth.Jordan.PlaneCurve.apply_add_int_mul γ t (-1)

section TgtVal

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ} {t₁ s₁ t₂ s₂ : ℝ} {b : Bool} {θ₁ θ₂ : ℝ}
variable (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
variable (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
variable (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) + (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
variable (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) - (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
include hout₁ hout₂ hθ₁ hθ₂

theorem pctgtUpB_pi_half :
    Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 2) =
      -Work.Smooth.SphereJordan.pccutDir S := by
  rw [Work.Smooth.SphereJordan.pctgtUpB,
    Work.Smooth.SphereJordan.pcperPt_eq_self (by positivity) (by nlinarith [Real.pi_pos]),
    if_pos le_rfl]
  rw [show Real.pi / 2 / (Real.pi / 2) = 1 by field_simp]
  rw [Work.SphereJordan.pcsrcOuterUp_cp]
  rw [show Real.pi * 1 = Real.pi by ring, Work.SphereJordan.pccp_pi]
  ring

theorem pctgtUpB_pi :
    Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ Real.pi = γ.γ θ₂ := by
  rw [Work.Smooth.SphereJordan.pctgtUpB,
    Work.Smooth.SphereJordan.pcperPt_eq_self (by positivity) (by nlinarith [Real.pi_pos]),
    if_neg (by linarith [Real.pi_pos]), if_pos le_rfl]
  rw [show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 by field_simp; norm_num]
  rw [Work.Smooth.SphereJordan.pctgtCut₂]
  rw [show (s₂ + 1 * (t₂ - s₂)) = t₂ by ring]
  exact hθ₂.symm

theorem pctgtUpB_3pi_half :
    Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (3 * Real.pi / 2) = γ.γ θ₁ := by
  rw [Work.Smooth.SphereJordan.pctgtUpB,
    Work.Smooth.SphereJordan.pcperPt_eq_self (by positivity) (by nlinarith [Real.pi_pos]),
    if_neg (by linarith [Real.pi_pos]), if_neg (by linarith [Real.pi_pos]), if_pos le_rfl]
  rw [show (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 by field_simp; norm_num]
  cases b with
  | false =>
    rw [if_neg (by simp)]
    rw [show θ₂ + 1 * (θ₁ - θ₂ - 2 * Real.pi) = θ₁ + ((-1 : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast; ring]
    exact Work.Smooth.Jordan.PlaneCurve.apply_add_int_mul γ θ₁ (-1)
  | true => rw [if_pos rfl, show θ₂ + 1 * (θ₁ - θ₂) = θ₁ by ring]

theorem pctgtUpB_2pi :
    Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (2 * Real.pi) =
      Work.Smooth.SphereJordan.pccutDir S := by
  rw [Work.Smooth.SphereJordan.pctgtUpB, pcperPt_two_pi_aux]
  rw [if_pos (by positivity), zero_div, Work.SphereJordan.pcsrcOuterUp_cp, mul_zero]
  simp

theorem pctgtDnB_pi_half :
    Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 2) =
      Work.Smooth.SphereJordan.pccutDir S := by
  rw [Work.Smooth.SphereJordan.pctgtDnB,
    Work.Smooth.SphereJordan.pcperPt_eq_self (by positivity) (by nlinarith [Real.pi_pos]),
    if_pos le_rfl]
  rw [show Real.pi / 2 / (Real.pi / 2) = 1 by field_simp]
  rw [Work.Smooth.SphereJordan.pcsrcOuterDn]
  rw [show Real.pi * 1 = Real.pi by ring, pcexp_pi_mul_I]
  ring

theorem pctgtDnB_pi :
    Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ Real.pi = γ.γ θ₁ := by
  rw [Work.Smooth.SphereJordan.pctgtDnB,
    Work.Smooth.SphereJordan.pcperPt_eq_self (by positivity) (by nlinarith [Real.pi_pos]),
    if_neg (by linarith [Real.pi_pos]), if_pos le_rfl]
  rw [show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 by field_simp; norm_num]
  rw [Work.Smooth.SphereJordan.pctgtCut₁]
  rw [show (s₁ + 1 * (t₁ - s₁)) = t₁ by ring]
  exact hθ₁.symm

theorem pctgtDnB_3pi_half :
    Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (3 * Real.pi / 2) = γ.γ θ₂ := by
  rw [Work.Smooth.SphereJordan.pctgtDnB,
    Work.Smooth.SphereJordan.pcperPt_eq_self (by positivity) (by nlinarith [Real.pi_pos]),
    if_neg (by linarith [Real.pi_pos]), if_neg (by linarith [Real.pi_pos]), if_pos le_rfl]
  rw [show (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 by field_simp; norm_num]
  cases b with
  | false => rw [if_neg (by simp), show θ₁ + 1 * (θ₂ - θ₁) = θ₂ by ring]
  | true => rw [if_pos rfl, show θ₁ - 2 * Real.pi + 1 * (θ₂ - θ₁ + 2 * Real.pi) = θ₂ by ring]

theorem pctgtDnB_2pi :
    Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (2 * Real.pi) =
      -Work.Smooth.SphereJordan.pccutDir S := by
  rw [Work.Smooth.SphereJordan.pctgtDnB, pcperPt_two_pi_aux]
  rw [if_pos (by positivity), zero_div, Work.Smooth.SphereJordan.pcsrcOuterDn, mul_zero]
  simp

theorem pctgtB_up1 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ x =
      Work.Smooth.SphereJordan.pcsrcOuterUp S (x / (Real.pi / 2)) := by
  rw [Work.Smooth.SphereJordan.pctgtUpB,
    Work.Smooth.SphereJordan.pcperPt_eq_self h0 (by nlinarith [Real.pi_pos]), if_pos h1]

theorem pctgtB_up2 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 2 + x) =
      Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂ (x / (Real.pi / 2)) := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    rw [add_zero, pctgtUpB_pi_half hout₁ hout₂ hθ₁ hθ₂]
    rw [Work.Smooth.SphereJordan.pctgtCut₂, zero_div,
      show (s₂ + 0 * (t₂ - s₂)) = s₂ by ring]
    exact hout₂.symm
  · rw [Work.Smooth.SphereJordan.pctgtUpB,
      Work.Smooth.SphereJordan.pcperPt_eq_self (by linarith) (by nlinarith [Real.pi_pos]),
      if_neg (by linarith), if_pos (by linarith)]
    rw [show Real.pi / 2 + x - Real.pi / 2 = x by ring]

theorem pctgtB_up3 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi + x) =
      (if b then γ.γ (θ₂ + (x / (Real.pi / 2)) * (θ₁ - θ₂))
       else γ.γ (θ₂ + (x / (Real.pi / 2)) * (θ₁ - θ₂ - 2 * Real.pi))) := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    rw [add_zero, pctgtUpB_pi hout₁ hout₂ hθ₁ hθ₂]
    cases b <;> simp
  · rw [Work.Smooth.SphereJordan.pctgtUpB,
      Work.Smooth.SphereJordan.pcperPt_eq_self (by linarith) (by nlinarith [Real.pi_pos]),
      if_neg (by linarith), if_neg (by linarith), if_pos (by linarith)]
    rw [show Real.pi + x - Real.pi = x by ring]

theorem pctgtB_up4 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (3 * Real.pi / 2 + x) =
      Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁ (1 - x / (Real.pi / 2)) := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    rw [add_zero, pctgtUpB_3pi_half hout₁ hout₂ hθ₁ hθ₂]
    rw [Work.Smooth.SphereJordan.pctgtCut₁, show (1 : ℝ) - 0 / (Real.pi / 2) = 1 by simp,
      show (s₁ + 1 * (t₁ - s₁)) = t₁ by ring]
    exact hθ₁
  · rcases eq_or_lt_of_le h1 with hx2 | hx2
    · subst hx2
      rw [show 3 * Real.pi / 2 + Real.pi / 2 = 2 * Real.pi by ring,
        pctgtUpB_2pi hout₁ hout₂ hθ₁ hθ₂]
      rw [Work.Smooth.SphereJordan.pctgtCut₁, show (1 : ℝ) - Real.pi / 2 / (Real.pi / 2) = 0 by
        field_simp; ring, show (s₁ + 0 * (t₁ - s₁)) = s₁ by ring]
      exact hout₁.symm
    · rw [Work.Smooth.SphereJordan.pctgtUpB,
        Work.Smooth.SphereJordan.pcperPt_eq_self (by linarith) (by nlinarith [Real.pi_pos]),
        if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
      rw [show 3 * Real.pi / 2 + x - 3 * Real.pi / 2 = x by ring]

theorem pctgtB_dn1 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ x =
      Work.Smooth.SphereJordan.pcsrcOuterDn S (x / (Real.pi / 2)) := by
  rw [Work.Smooth.SphereJordan.pctgtDnB,
    Work.Smooth.SphereJordan.pcperPt_eq_self h0 (by nlinarith [Real.pi_pos]), if_pos h1]

theorem pctgtB_dn2 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 2 + x) =
      Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁ (x / (Real.pi / 2)) := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    rw [add_zero, pctgtDnB_pi_half hout₁ hout₂ hθ₁ hθ₂]
    rw [Work.Smooth.SphereJordan.pctgtCut₁, zero_div,
      show (s₁ + 0 * (t₁ - s₁)) = s₁ by ring]
    exact hout₁.symm
  · rw [Work.Smooth.SphereJordan.pctgtDnB,
      Work.Smooth.SphereJordan.pcperPt_eq_self (by linarith) (by nlinarith [Real.pi_pos]),
      if_neg (by linarith), if_pos (by linarith)]
    rw [show Real.pi / 2 + x - Real.pi / 2 = x by ring]

theorem pctgtB_dn3 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi + x) =
      (if b then γ.γ (θ₁ - 2 * Real.pi + (x / (Real.pi / 2)) * (θ₂ - θ₁ + 2 * Real.pi))
       else γ.γ (θ₁ + (x / (Real.pi / 2)) * (θ₂ - θ₁))) := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    rw [add_zero, pctgtDnB_pi hout₁ hout₂ hθ₁ hθ₂]
    cases b with
    | false => rw [if_neg (by simp)]; simp
    | true =>
      rw [if_pos rfl]
      rw [show θ₁ - 2 * Real.pi + 0 / (Real.pi / 2) * (θ₂ - θ₁ + 2 * Real.pi) =
        θ₁ - 2 * Real.pi by ring]
      exact (pcgamma_sub_two_pi θ₁).symm
  · rw [Work.Smooth.SphereJordan.pctgtDnB,
      Work.Smooth.SphereJordan.pcperPt_eq_self (by linarith) (by nlinarith [Real.pi_pos]),
      if_neg (by linarith), if_neg (by linarith), if_pos (by linarith)]
    rw [show Real.pi + x - Real.pi = x by ring]

theorem pctgtB_dn4 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (3 * Real.pi / 2 + x) =
      Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂ (1 - x / (Real.pi / 2)) := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    rw [add_zero, pctgtDnB_3pi_half hout₁ hout₂ hθ₁ hθ₂]
    rw [Work.Smooth.SphereJordan.pctgtCut₂, show (1 : ℝ) - 0 / (Real.pi / 2) = 1 by simp,
      show (s₂ + 1 * (t₂ - s₂)) = t₂ by ring]
    exact hθ₂
  · rcases eq_or_lt_of_le h1 with hx2 | hx2
    · subst hx2
      rw [show 3 * Real.pi / 2 + Real.pi / 2 = 2 * Real.pi by ring,
        pctgtDnB_2pi hout₁ hout₂ hθ₁ hθ₂]
      rw [Work.Smooth.SphereJordan.pctgtCut₂, show (1 : ℝ) - Real.pi / 2 / (Real.pi / 2) = 0 by
        field_simp; ring, show (s₂ + 0 * (t₂ - s₂)) = s₂ by ring]
      exact hout₂.symm
    · rw [Work.Smooth.SphereJordan.pctgtDnB,
        Work.Smooth.SphereJordan.pcperPt_eq_self (by linarith) (by nlinarith [Real.pi_pos]),
        if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
      rw [show 3 * Real.pi / 2 + x - 3 * Real.pi / 2 = x by ring]

namespace pcTwoCuts

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ}


theorem pcTu_outer (K : pcTwoCuts S) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    K.Tu.e (Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 * x)) = pcouterPt S x := by
  rw [pcTu_apply, pctgtB_up1 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ (Real.pi / 2 * x)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show Real.pi / 2 * x / (Real.pi / 2) = x by field_simp]
  exact (pcouterPt_eq_src S x).symm

theorem pcTd_outer (K : pcTwoCuts S) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    K.Td.e (Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 * x)) = pcouterPtDn S x := by
  rw [pcTd_apply, pctgtB_dn1 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ (Real.pi / 2 * x)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show Real.pi / 2 * x / (Real.pi / 2) = x by field_simp]
  exact (pcouterPtDn_eq_src S x).symm

theorem pcTu_cut₂ (K : pcTwoCuts S) (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    K.Tu.e (Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 + (Real.pi / 2) * y)) =
      Work.Smooth.SphereJordan.pctgtCut₂ S K.t₂ K.s₂ y := by
  rw [pcTu_apply, pctgtB_up2 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ ((Real.pi / 2) * y)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show (Real.pi / 2) * y / (Real.pi / 2) = y by field_simp]

theorem pcTd_cut₁ (K : pcTwoCuts S) (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    K.Td.e (Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 + (Real.pi / 2) * y)) =
      Work.Smooth.SphereJordan.pctgtCut₁ S K.t₁ K.s₁ y := by
  rw [pcTd_apply, pctgtB_dn2 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ ((Real.pi / 2) * y)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show (Real.pi / 2) * y / (Real.pi / 2) = y by field_simp]

theorem pcTu_cut₁ (K : pcTwoCuts S) (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    K.Tu.e (Work.Smooth.SphereJordan.circlePoint (3 * Real.pi / 2 + (Real.pi / 2) * y)) =
      Work.Smooth.SphereJordan.pctgtCut₁ S K.t₁ K.s₁ (1 - y) := by
  rw [pcTu_apply, pctgtB_up4 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ ((Real.pi / 2) * y)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show (Real.pi / 2) * y / (Real.pi / 2) = y by field_simp]

theorem pcTd_cut₂ (K : pcTwoCuts S) (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    K.Td.e (Work.Smooth.SphereJordan.circlePoint (3 * Real.pi / 2 + (Real.pi / 2) * y)) =
      Work.Smooth.SphereJordan.pctgtCut₂ S K.t₂ K.s₂ (1 - y) := by
  rw [pcTd_apply, pctgtB_dn4 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ ((Real.pi / 2) * y)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  rw [show (Real.pi / 2) * y / (Real.pi / 2) = y by field_simp]

theorem pcTu_inner (K : pcTwoCuts S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    K.Tu.e (Work.Smooth.SphereJordan.circlePoint (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi))) =
      (if K.b then γ.γ (K.θ₂ + (1 - θ / Real.pi) * (K.θ₁ - K.θ₂))
       else γ.γ (K.θ₂ + (1 - θ / Real.pi) * (K.θ₁ - K.θ₂ - 2 * Real.pi))) := by
  obtain ⟨b0, b1⟩ := pchalfPi_mul_sub_bounds θ h0 h1
  rw [pcTu_apply, pctgtB_up3 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ ((Real.pi / 2) * (1 - θ / Real.pi)) b0 b1]
  rw [show (Real.pi / 2) * (1 - θ / Real.pi) / (Real.pi / 2) = 1 - θ / Real.pi by field_simp]

theorem pcTd_inner (K : pcTwoCuts S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    K.Td.e (Work.Smooth.SphereJordan.circlePoint (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi))) =
      (if K.b then γ.γ (K.θ₁ - 2 * Real.pi + (1 - θ / Real.pi) * (K.θ₂ - K.θ₁ + 2 * Real.pi))
       else γ.γ (K.θ₁ + (1 - θ / Real.pi) * (K.θ₂ - K.θ₁))) := by
  obtain ⟨b0, b1⟩ := pchalfPi_mul_sub_bounds θ h0 h1
  rw [pcTd_apply, pctgtB_dn3 K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ ((Real.pi / 2) * (1 - θ / Real.pi)) b0 b1]
  rw [show (Real.pi / 2) * (1 - θ / Real.pi) / (Real.pi / 2) = 1 - θ / Real.pi by field_simp]

end pcTwoCuts

end TgtVal


/-! ## The gluing map of the pcannulus -/

section Glue

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ} (D : pcSourceData S) (K : pcTwoCuts S)

/-- The upper sheet of the gluing map. -/
def pcglueU : C(↥(pcHup D), ℂ) :=
  ⟨fun z => K.Tu.e ((pcΨuHomeo D).symm z),
    K.Tu.e.continuous.comp (pcΨuHomeo D).symm.continuous⟩

/-- The lower sheet of the gluing map. -/
def pcglueD : C(↥(pcHdn D), ℂ) :=
  ⟨fun z => K.Td.e ((pcΨdHomeo D).symm z),
    K.Td.e.continuous.comp (pcΨdHomeo D).symm.continuous⟩

theorem pcglueU_apply (z : ↥(pcHup D)) : pcglueU D K z = K.Tu.e ((pcΨuHomeo D).symm z) := rfl

theorem pcglueD_apply (z : ↥(pcHdn D)) : pcglueD D K z = K.Td.e ((pcΨdHomeo D).symm z) := rfl

/-- **The gluing map on the model pcannulus**: on the upper sheet it is the target upper disc read
through the inverse of `Ψu`, on the lower sheet the target lower disc read through `Ψd`. -/
def pcglueFun (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ pcHup D then pcglueU D K ⟨z, h⟩
    else if h2 : z ∈ pcHdn D then pcglueD D K ⟨z, h2⟩
    else 0

theorem pcglueFun_of_Hup {z : ℂ} (hz : z ∈ pcHup D) : pcglueFun D K z = pcglueU D K ⟨z, hz⟩ := by
  rw [pcglueFun]
  exact dif_pos hz

theorem pcglueFun_of_Hdn {z : ℂ} (hz : z ∈ pcHdn D) (hz' : z ∉ pcHup D) :
    pcglueFun D K z = pcglueD D K ⟨z, hz⟩ := by
  rw [pcglueFun]
  rw [dif_neg hz', dif_pos hz]

theorem pcΨuHomeo_symm_eq {z : ℂ} (hz : z ∈ pcHup D) {w : Work.Smooth.SphereJordan.Disc}
    (hw : (D.Ψu w : ℂ) = z) : (pcΨuHomeo D).symm ⟨z, hz⟩ = w :=
  pcΨuHomeo_symm_eq_of D (Subtype.ext (by rw [pcΨuHomeo_apply, hw]))

theorem pcΨdHomeo_symm_eq {z : ℂ} (hz : z ∈ pcHdn D) {w : Work.Smooth.SphereJordan.Disc}
    (hw : (D.Ψd w : ℂ) = z) : (pcΨdHomeo D).symm ⟨z, hz⟩ = w :=
  pcΨdHomeo_symm_eq_of D (Subtype.ext (by rw [pcΨdHomeo_apply, hw]))

/-- The value of the gluing map at a point known to lie on the upper sheet. -/
theorem pcglueFun_eq_Tu {z : ℂ} (hz : z ∈ pcHup D) {w : Work.Smooth.SphereJordan.Disc}
    (hw : (D.Ψu w : ℂ) = z) : pcglueFun D K z = K.Tu.e w := by
  rw [pcglueFun_of_Hup D K hz, pcglueU_apply, pcΨuHomeo_symm_eq D hz hw]

/-- The value of the gluing map at a point known to lie on the lower sheet and not on the upper
one. -/
theorem pcglueFun_eq_Td {z : ℂ} (hz : z ∈ pcHdn D) (hz' : z ∉ pcHup D)
    {w : Work.Smooth.SphereJordan.Disc} (hw : (D.Ψd w : ℂ) = z) : pcglueFun D K z = K.Td.e w := by
  rw [pcglueFun_of_Hdn D K hz hz', pcglueD_apply, pcΨdHomeo_symm_eq D hz hw]

end Glue




/-! ## Points of the boundary circle, of the inner circle and of the radial segments -/

section GlueVal

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ} (D : pcSourceData S) (K : pcTwoCuts S)

theorem pcexp_I_eq_iff (a b : ℝ)
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

theorem pcnorm_cutDir' (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ‖Work.Smooth.SphereJordan.pccutDir S‖ = 1 := Work.Smooth.SphereJordan.pcnorm_cutDir S

theorem pcnorm_outerPtDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    ‖pcouterPtDn S x‖ = 1 := by
  rw [pcouterPtDn, Complex.norm_exp_ofReal_mul_I]

theorem pcnorm_outerPt (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    ‖pcouterPt S x‖ = 1 := by
  rw [pcouterPt, Complex.norm_exp_ofReal_mul_I]

theorem pcnorm_innerPtUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) :
    ‖pcinnerPtUp S θ‖ = 1 / 2 := by
  rw [pcinnerPtUp, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  norm_num

theorem pcnorm_innerPtDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) :
    ‖pcinnerPtDn S θ‖ = 1 / 2 := by
  rw [pcinnerPtDn, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  norm_num

/-- A point of norm one lying in both sheets of the model pcannulus is one of the two outer feet. -/
theorem pcnorm_one_mem_both (D : pcSourceData S) {z : ℂ} (h1 : z ∈ pcHup D) (h2 : z ∈ pcHdn D)
    (hz : ‖z‖ = 1) : z = Work.Smooth.SphereJordan.pccutDir S ∨
      z = -Work.Smooth.SphereJordan.pccutDir S := by
  have hmem : z ∈ ({z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
        z = (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S} ∪
     {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
        z = -((σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)}) := by
    rw [← pcHup_inter_Hdn D]
    exact ⟨h1, h2⟩
  rcases hmem with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
  · left
    have hσ1 : σ = 1 := by
      have : ‖(σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S‖ = σ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num) hσ.1),
          Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one]
      rw [this] at hz
      exact hz
    rw [hσ1]
    norm_num
  · right
    have hσ1 : σ = 1 := by
      have : ‖-((σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)‖ = σ := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (le_trans (by norm_num) hσ.1), Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one]
      rw [this] at hz
      exact hz
    rw [hσ1]
    norm_num

/-- Membership of the outer arcs in the two sheets. -/
theorem pcmem_Hup_outer (D : pcSourceData S) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    pcouterPt S x ∈ pcHup D := ⟨Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 * x),
      pcsrcUpB_outer (S := S) D x h0 h1⟩

theorem pcmem_Hdn_outer (D : pcSourceData S) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    pcouterPtDn S x ∈ pcHdn D := ⟨Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 * x),
      pcsrcDnB_outer (S := S) D x h0 h1⟩

/-- Membership of the inner arcs in the two sheets. -/
theorem pcmem_Hup_inner (D : pcSourceData S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    pcinnerPtUp S θ ∈ pcHup D := ⟨Work.Smooth.SphereJordan.circlePoint
      (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi)), pcsrcUpB_inner (S := S) D θ h0 h1⟩

theorem pcmem_Hdn_inner (D : pcSourceData S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    pcinnerPtDn S θ ∈ pcHdn D := ⟨Work.Smooth.SphereJordan.circlePoint
      (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi)), pcsrcDnB_inner (S := S) D θ h0 h1⟩

/-- Membership of the radial segments in the two sheets. -/
theorem pcmem_Hup_radpos (D : pcSourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    (ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈ pcHup D :=
  ⟨Work.Smooth.SphereJordan.circlePoint (3 * Real.pi / 2 + (Real.pi / 2) * (2 * ρ - 1)),
    pcsrcUpB_radpos (S := S) D ρ h1 h2⟩

theorem pcmem_Hdn_radpos (D : pcSourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    (ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈ pcHdn D :=
  ⟨Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 + (Real.pi / 2) * (2 - 2 * ρ)),
    pcsrcDnB_radpos (S := S) D ρ h1 h2⟩

theorem pcmem_Hup_radneg (D : pcSourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    -((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) ∈ pcHup D :=
  ⟨Work.Smooth.SphereJordan.circlePoint (Real.pi / 2 + (Real.pi / 2) * (2 - 2 * ρ)),
    pcsrcUpB_radneg (S := S) D ρ h1 h2⟩

theorem pcmem_Hdn_radneg (D : pcSourceData S) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    -((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) ∈ pcHdn D :=
  ⟨Work.Smooth.SphereJordan.circlePoint (3 * Real.pi / 2 + (Real.pi / 2) * (2 * ρ - 1)),
    pcsrcDnB_radneg (S := S) D ρ h1 h2⟩

/-- The lower outer arc avoids the upper sheet of the model pcannulus. -/
theorem pcouterPtDn_notMem_Hup (D : pcSourceData S) {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    pcouterPtDn S x ∉ pcHup D := by
  intro hz
  have hboth := pcnorm_one_mem_both D hz (pcmem_Hdn_outer D x h0.le h1.le) (pcnorm_outerPtDn S x)
  rw [pcouterPtDn] at hboth
  rcases hboth with h | h
  · rw [← pccutAng_spec S] at h
    obtain ⟨k, hk⟩ := pcexp_I_eq_iff _ _ h
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
  · rw [show -Work.Smooth.SphereJordan.pccutDir S =
        ((Work.Smooth.SphereJordan.circlePoint (pccutAng S + Real.pi) :
          Work.Smooth.SphereJordan.Disc) : ℂ) by
      rw [← pccutAng_spec S, Work.SphereJordan.pccirclePoint_cp_neg (pccutAng S)]] at h
    obtain ⟨k, hk⟩ := pcexp_I_eq_iff _ _ h
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


/-- The radial point of the model pcannulus at radius parameter `ρ`. -/
def pcradPt (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (ρ : ℝ) : ℂ :=
  (ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S

section GlueVal2

variable {S : Work.Smooth.Jordan.PlaneSchoenflies γ} (D : pcSourceData S) (K : pcTwoCuts S)

/-! ### The two sheets agree on the radial segments -/

theorem pcglueU_radPt (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1)
    (hmem : (ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈ pcHup D) :
    pcglueU D K ⟨(ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S, hmem⟩ =
      Work.Smooth.SphereJordan.pctgtCut₁ S K.t₁ K.s₁ (2 - 2 * ρ) := by
  rw [pcglueU_apply, pcΨuHomeo_symm_eq D hmem (pcsrcUpB_radpos (S := S) D ρ h1 h2)]
  have := pcTwoCuts.pcTu_cut₁ K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (2 * ρ - 1) (by linarith) (by linarith)
  rwa [show 1 - (2 * ρ - 1) = (2 - 2 * ρ) by ring] at this

theorem pcglueD_radPt (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1)
    (hmem : (ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈ pcHdn D) :
    pcglueD D K ⟨(ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S, hmem⟩ =
      Work.Smooth.SphereJordan.pctgtCut₁ S K.t₁ K.s₁ (2 - 2 * ρ) := by
  rw [pcglueD_apply, pcΨdHomeo_symm_eq D hmem (pcsrcDnB_radpos (S := S) D ρ h1 h2)]
  exact pcTwoCuts.pcTd_cut₁ K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (2 - 2 * ρ) (by linarith) (by linarith)

theorem pcglueU_radPt_neg (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1)
    (hmem : -((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) ∈ pcHup D) :
    pcglueU D K ⟨-((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S), hmem⟩ =
      Work.Smooth.SphereJordan.pctgtCut₂ S K.t₂ K.s₂ (2 - 2 * ρ) := by
  rw [pcglueU_apply, pcΨuHomeo_symm_eq D hmem (pcsrcUpB_radneg (S := S) D ρ h1 h2)]
  exact pcTwoCuts.pcTu_cut₂ K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (2 - 2 * ρ) (by linarith) (by linarith)

theorem pcglueD_radPt_neg (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1)
    (hmem : -((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) ∈ pcHdn D) :
    pcglueD D K ⟨-((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S), hmem⟩ =
      Work.Smooth.SphereJordan.pctgtCut₂ S K.t₂ K.s₂ (2 - 2 * ρ) := by
  rw [pcglueD_apply, pcΨdHomeo_symm_eq D hmem (pcsrcDnB_radneg (S := S) D ρ h1 h2)]
  have := pcTwoCuts.pcTd_cut₂ K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (2 * ρ - 1) (by linarith) (by linarith)
  rwa [show 1 - (2 * ρ - 1) = (2 - 2 * ρ) by ring] at this

/-- **The two sheets of the gluing map agree on the radial segments**, hence on the whole
intersection `pcHup ∩ pcHdn`. -/
theorem pcglueU_eq_glueD (z : ℂ) (hz1 : z ∈ pcHup D) (hz2 : z ∈ pcHdn D) :
    pcglueU D K ⟨z, hz1⟩ = pcglueD D K ⟨z, hz2⟩ := by
  have hmem : z ∈ pcHup D ∩ pcHdn D := ⟨hz1, hz2⟩
  rw [pcHup_inter_Hdn D] at hmem
  rcases hmem with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
  · rw [pcglueU_radPt D K σ hσ.1 hσ.2 hz1, pcglueD_radPt D K σ hσ.1 hσ.2 hz2]
  · rw [pcglueU_radPt_neg D K σ hσ.1 hσ.2 hz1, pcglueD_radPt_neg D K σ hσ.1 hσ.2 hz2]

/-! ### The values of the gluing map -/

theorem pcglueFun_eq_Td' {z : ℂ} (hz : z ∈ pcHdn D) {w : Work.Smooth.SphereJordan.Disc}
    (hw : (D.Ψd w : ℂ) = z) : pcglueFun D K z = K.Td.e w := by
  by_cases h : z ∈ pcHup D
  · rw [pcglueFun_of_Hup D K h, pcglueU_eq_glueD D K z h hz, pcglueD_apply, pcΨdHomeo_symm_eq D hz hw]
  · rw [pcglueFun_of_Hdn D K hz h, pcglueD_apply, pcΨdHomeo_symm_eq D hz hw]

theorem pcglueFun_outer (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    pcglueFun D K (pcouterPt S x) = pcouterPt S x := by
  rw [pcglueFun_eq_Tu D K (pcmem_Hup_outer D x h0 h1) (pcsrcUpB_outer (S := S) D x h0 h1)]
  exact pcTwoCuts.pcTu_outer K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K x h0 h1

theorem pcglueFun_outerDn (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    pcglueFun D K (pcouterPtDn S x) = pcouterPtDn S x := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx
    have hpt : pcouterPtDn S 0 = pcouterPt S 1 := by
      rw [pcouterPtDn, pcouterPt]
      norm_num
    rw [hpt, pcglueFun_outer D K 1 zero_le_one le_rfl]
  · rcases eq_or_lt_of_le h1 with hx2 | hx2
    · subst hx2
      have hpt : pcouterPtDn S 1 = pcouterPt S 0 := by
        rw [pcouterPtDn, pcouterPt]
        rw [show pccutAng S + Real.pi + Real.pi * 1 = pccutAng S + 2 * Real.pi by ring,
          show pccutAng S + Real.pi * 0 = pccutAng S by ring]
        rw [show ((pccutAng S + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
          (pccutAng S : ℂ) * Complex.I + (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
        rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      rw [hpt, pcglueFun_outer D K 0 le_rfl zero_le_one]
    · rw [pcglueFun_eq_Td' D K (pcmem_Hdn_outer D x h0 h1) (pcsrcDnB_outer (S := S) D x h0 h1)]
      exact pcTwoCuts.pcTd_outer K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K x h0 h1

theorem pcglueFun_innerUp (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    pcglueFun D K (pcinnerPtUp S θ) =
      K.Tu.e (Work.Smooth.SphereJordan.circlePoint
        (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi))) := by
  rw [pcglueFun_eq_Tu D K (pcmem_Hup_inner D θ h0 h1) (pcsrcUpB_inner (S := S) D θ h0 h1)]

theorem pcglueFun_innerDn (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    pcglueFun D K (pcinnerPtDn S θ) =
      K.Td.e (Work.Smooth.SphereJordan.circlePoint
        (Real.pi + (Real.pi / 2) * (1 - θ / Real.pi))) := by
  rw [pcglueFun_eq_Td' D K (pcmem_Hdn_inner D θ h0 h1) (pcsrcDnB_inner (S := S) D θ h0 h1)]

theorem pcglueFun_radPt (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    pcglueFun D K ((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) =
      Work.Smooth.SphereJordan.pctgtCut₁ S K.t₁ K.s₁ (2 - 2 * ρ) := by
  rw [pcglueFun_eq_Tu D K (pcmem_Hup_radpos D ρ h1 h2) (pcsrcUpB_radpos (S := S) D ρ h1 h2)]
  have := pcTwoCuts.pcTu_cut₁ K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (2 * ρ - 1) (by linarith) (by linarith)
  rwa [show 1 - (2 * ρ - 1) = (2 - 2 * ρ) by ring] at this

theorem pcglueFun_radPt_neg (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    pcglueFun D K (-((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)) =
      Work.Smooth.SphereJordan.pctgtCut₂ S K.t₂ K.s₂ (2 - 2 * ρ) := by
  rw [pcglueFun_eq_Tu D K (pcmem_Hup_radneg D ρ h1 h2) (pcsrcUpB_radneg (S := S) D ρ h1 h2)]
  exact pcTwoCuts.pcTu_cut₂ K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (2 - 2 * ρ) (by linarith) (by linarith)

/-! ### The image of the gluing map -/

theorem pcglueU_injective : Function.Injective (pcglueU D K) := by
  intro a b h
  have h' : (pcΨuHomeo D).symm a = (pcΨuHomeo D).symm b := K.Tu.inj h
  exact (pcΨuHomeo D).symm.injective h'

theorem pcglueD_injective : Function.Injective (pcglueD D K) := by
  intro a b h
  have h' : (pcΨdHomeo D).symm a = (pcΨdHomeo D).symm b := K.Td.inj h
  exact (pcΨdHomeo D).symm.injective h'

theorem pcrange_glueU : Set.range (pcglueU D K) = closure K.Tu.V := by
  rw [← K.Tu.range_e]
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(pcΨuHomeo D).symm a, rfl⟩
  · rintro ⟨w, rfl⟩
    refine ⟨pcΨuHomeo D w, ?_⟩
    rw [pcglueU_apply, Homeomorph.symm_apply_apply]

theorem pcrange_glueD : Set.range (pcglueD D K) = closure K.Td.V := by
  rw [← K.Td.range_e]
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(pcΨdHomeo D).symm a, rfl⟩
  · rintro ⟨w, rfl⟩
    refine ⟨pcΨdHomeo D w, ?_⟩
    rw [pcglueD_apply, Homeomorph.symm_apply_apply]

theorem pcrange_glueU_inter : Set.range (pcglueU D K) ∩ Set.range (pcglueD D K) =
    Work.Smooth.SphereJordan.pccut₁ S K.t₁ K.s₁ ∪
      Work.Smooth.SphereJordan.pccut₂ S K.t₂ K.s₂ := by
  rw [pcrange_glueU, pcrange_glueD, K.hmeet]

theorem pcdiv_mem_Icc_of_mem_Icc {t s σ : ℝ} (hts : t ≠ s) (hσ : σ ∈ Set.Icc t s) :
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
theorem pccut_subset_frontier (y : ℂ)
    (hy : y ∈ Work.Smooth.SphereJordan.pccut₁ S K.t₁ K.s₁ ∪
      Work.Smooth.SphereJordan.pccut₂ S K.t₂ K.s₂) :
    (∃ ρ : ℝ, 1 / 2 ≤ ρ ∧ ρ ≤ 1 ∧
        pcglueFun D K ((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) = y) ∨
      (∃ ρ : ℝ, 1 / 2 ≤ ρ ∧ ρ ≤ 1 ∧
        pcglueFun D K (-((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)) = y) := by
  rcases hy with hy | hy
  · left
    rcases hy with ⟨σ, hσ, rfl⟩
    rcases eq_or_ne K.t₁ K.s₁ with hts | hts
    · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      rw [pcglueFun_radPt D K (1 / 2) (by norm_num) (by norm_num)]
      rw [Work.Smooth.SphereJordan.pctgtCut₁]
      have hσeq : σ = K.s₁ := by
        refine le_antisymm hσ.2 ?_
        rw [← hts]
        exact hσ.1
      rw [show K.s₁ + (2 - 2 * (1 / 2)) * (K.t₁ - K.s₁) = σ by
        rw [hts]; ring_nf; exact hσeq.symm]
    · obtain ⟨hx0, hx1, hxeq⟩ :=
        (pcdiv_mem_Icc_of_mem_Icc hts hσ)
      refine ⟨1 - (σ - K.s₁) / (K.t₁ - K.s₁) / 2, by linarith, by linarith, ?_⟩
      rw [pcglueFun_radPt D K (1 - (σ - K.s₁) / (K.t₁ - K.s₁) / 2) (by linarith) (by linarith)]
      rw [Work.Smooth.SphereJordan.pctgtCut₁]
      rw [show (2 - 2 * (1 - (σ - K.s₁) / (K.t₁ - K.s₁) / 2) : ℝ) =
        (σ - K.s₁) / (K.t₁ - K.s₁) by ring]
      rw [hxeq]
  · right
    rcases hy with ⟨σ, hσ, rfl⟩
    rcases eq_or_ne K.t₂ K.s₂ with hts | hts
    · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      rw [pcglueFun_radPt_neg D K (1 / 2) (by norm_num) (by norm_num)]
      rw [Work.Smooth.SphereJordan.pctgtCut₂]
      have hσeq : σ = K.s₂ := by
        refine le_antisymm hσ.2 ?_
        rw [← hts]
        exact hσ.1
      rw [show K.s₂ + (2 - 2 * (1 / 2)) * (K.t₂ - K.s₂) = σ by
        rw [hts]; ring_nf; exact hσeq.symm]
    · obtain ⟨hx0, hx1, hxeq⟩ :=
        (pcdiv_mem_Icc_of_mem_Icc hts hσ)
      refine ⟨1 - (σ - K.s₂) / (K.t₂ - K.s₂) / 2, by linarith, by linarith, ?_⟩
      rw [pcglueFun_radPt_neg D K (1 - (σ - K.s₂) / (K.t₂ - K.s₂) / 2) (by linarith) (by linarith)]
      rw [Work.Smooth.SphereJordan.pctgtCut₂]
      rw [show (2 - 2 * (1 - (σ - K.s₂) / (K.t₂ - K.s₂) / 2) : ℝ) =
        (σ - K.s₂) / (K.t₂ - K.s₂) by ring]
      rw [hxeq]

/-! ### Injectivity of the gluing map on the model pcannulus -/

theorem pcmem_Hdn_of_mem_Msub {z : ℂ} (hz : z ∈ pcMsub) (hz' : z ∉ pcHup D) : z ∈ pcHdn D := by
  have h := hz
  rw [← pcHup_union_Hdn D] at h
  rcases h with h | h
  · exact absurd h hz'
  · exact h

/-- The gluing map is injective on the model pcannulus restricted to a point of the upper sheet. -/
theorem pcglueFun_injOn_of_Hup {z z' : ℂ} (hz : z ∈ pcMsub) (hz' : z' ∈ pcMsub)
    (h1 : z ∈ pcHup D) (h2 : z' ∉ pcHup D)
    (h : pcglueFun D K z = pcglueFun D K z') : z = z' := by
  have hz2 : z' ∈ pcHdn D := pcmem_Hdn_of_mem_Msub D hz' h2
  have hy : pcglueFun D K z ∈ Work.Smooth.SphereJordan.pccut₁ S K.t₁ K.s₁ ∪
      Work.Smooth.SphereJordan.pccut₂ S K.t₂ K.s₂ := by
    have hy1 : pcglueFun D K z ∈ Set.range (pcglueU D K) := by
      rw [pcglueFun_of_Hup D K h1]
      exact ⟨⟨z, h1⟩, rfl⟩
    have hy2 : pcglueFun D K z' ∈ Set.range (pcglueD D K) := by
      rw [pcglueFun_of_Hdn D K hz2 h2]
      exact ⟨⟨z', hz2⟩, rfl⟩
    rw [← pcrange_glueU_inter D K]
    exact ⟨hy1, h ▸ hy2⟩
  rcases pccut_subset_frontier D K (pcglueFun D K z) hy with
    ⟨ρ, hρ1, hρ2, hρ⟩ | ⟨ρ, hρ1, hρ2, hρ⟩
  · have hzu : z = (ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
      have hx : pcglueU D K ⟨z, h1⟩ =
          pcglueU D K ⟨(ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S,
            pcmem_Hup_radpos D ρ hρ1 hρ2⟩ := by
        rw [← pcglueFun_of_Hup D K h1,
          ← pcglueFun_of_Hup D K (pcmem_Hup_radpos D ρ hρ1 hρ2)]
        exact hρ.symm
      exact congrArg Subtype.val (pcglueU_injective D K hx)
    have hz'u : z' = (ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
      have hz2b : z' ∈ pcHdn D := hz2
      obtain ⟨w, hw⟩ := hz2b
      have h1' : pcglueFun D K z' = K.Td.e w := pcglueFun_eq_Td' D K hz2 hw
      have h2' : pcglueFun D K ((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) =
          K.Td.e (Work.Smooth.SphereJordan.circlePoint
            (Real.pi / 2 + (Real.pi / 2) * (2 - 2 * ρ))) :=
        pcglueFun_eq_Td' D K (pcmem_Hdn_radpos D ρ hρ1 hρ2) (pcsrcDnB_radpos (S := S) D ρ hρ1 hρ2)
      have hkey : K.Td.e w = K.Td.e (Work.Smooth.SphereJordan.circlePoint
          (Real.pi / 2 + (Real.pi / 2) * (2 - 2 * ρ))) := by
        rw [← h1', ← h, ← hρ, ← h2']
      have hw' := K.Td.inj hkey
      rw [← hw, hw']
      exact pcsrcDnB_radpos (S := S) D ρ hρ1 hρ2
    rw [hzu, hz'u]
  · have hzu : z = -((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) := by
      have hx : pcglueU D K ⟨z, h1⟩ =
          pcglueU D K ⟨-((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S),
            pcmem_Hup_radneg D ρ hρ1 hρ2⟩ := by
        rw [← pcglueFun_of_Hup D K h1,
          ← pcglueFun_of_Hup D K (pcmem_Hup_radneg D ρ hρ1 hρ2)]
        exact hρ.symm
      exact congrArg Subtype.val (pcglueU_injective D K hx)
    have hz'u : z' = -((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) := by
      have hz2b : z' ∈ pcHdn D := hz2
      obtain ⟨w, hw⟩ := hz2b
      have h1' : pcglueFun D K z' = K.Td.e w := pcglueFun_eq_Td' D K hz2 hw
      have h2' : pcglueFun D K (-((ρ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)) =
          K.Td.e (Work.Smooth.SphereJordan.circlePoint
            (3 * Real.pi / 2 + (Real.pi / 2) * (2 * ρ - 1))) :=
        pcglueFun_eq_Td' D K (pcmem_Hdn_radneg D ρ hρ1 hρ2) (pcsrcDnB_radneg (S := S) D ρ hρ1 hρ2)
      have hkey : K.Td.e w = K.Td.e (Work.Smooth.SphereJordan.circlePoint
          (3 * Real.pi / 2 + (Real.pi / 2) * (2 * ρ - 1))) := by
        rw [← h1', ← h, ← hρ, ← h2']
      have hw' := K.Td.inj hkey
      rw [← hw, hw']
      exact pcsrcDnB_radneg (S := S) D ρ hρ1 hρ2
    rw [hzu, hz'u]

/-- **The gluing map is injective on the model pcannulus.** -/
theorem pcglueFun_injOn {z z' : ℂ} (hz : z ∈ pcMsub) (hz' : z' ∈ pcMsub)
    (h : pcglueFun D K z = pcglueFun D K z') : z = z' := by
  by_cases h2 : z' ∈ pcHup D
  · by_cases h1 : z ∈ pcHup D
    · have hU : pcglueU D K ⟨z, h1⟩ = pcglueU D K ⟨z', h2⟩ := by
        rw [← pcglueFun_of_Hup D K h1, ← pcglueFun_of_Hup D K h2]
        exact h
      exact congrArg Subtype.val (pcglueU_injective D K hU)
    · exact (pcglueFun_injOn_of_Hup D K hz' hz h2 h1 h.symm).symm
  · by_cases h1 : z ∈ pcHup D
    · exact pcglueFun_injOn_of_Hup D K hz hz' h1 h2 h
    · have hz2 : z ∈ pcHdn D := pcmem_Hdn_of_mem_Msub D hz h1
      have hz2' : z' ∈ pcHdn D := pcmem_Hdn_of_mem_Msub D hz' h2
      have hD : pcglueD D K ⟨z, hz2⟩ = pcglueD D K ⟨z', hz2'⟩ := by
        rw [← pcglueFun_of_Hdn D K hz2 h1, ← pcglueFun_of_Hdn D K hz2' h2]
        exact h
      exact congrArg Subtype.val (pcglueD_injective D K hD)

/-! ### Continuity of the gluing map -/

theorem pcisClosed_Hup : IsClosed (pcHup D) :=
  (isCompact_range D.Ψu.continuous).isClosed

theorem pcisClosed_Hdn : IsClosed (pcHdn D) :=
  (isCompact_range D.Ψd.continuous).isClosed

theorem pccontinuousOn_glueFun_Hup : ContinuousOn (pcglueFun D K) (pcHup D) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hEq : (pcHup D).domRestrict (pcglueFun D K) = fun z : ↥(pcHup D) => pcglueU D K z := by
    funext z
    exact pcglueFun_of_Hup D K z.2
  rw [hEq]
  exact (pcglueU D K).continuous

theorem pccontinuousOn_glueFun_Hdn : ContinuousOn (pcglueFun D K) (pcHdn D) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hEq : (pcHdn D).domRestrict (pcglueFun D K) = fun z : ↥(pcHdn D) => pcglueD D K z := by
    funext z
    by_cases h : (z : ℂ) ∈ pcHup D
    · rw [Set.domRestrict_apply, pcglueFun_of_Hup D K h]
      have h2 : (⟨(z : ℂ), h⟩ : ↥(pcHup D)) = ⟨(z : ℂ), h⟩ := rfl
      rw [pcglueU_eq_glueD D K (z : ℂ) h z.2]
    · rw [Set.domRestrict_apply, pcglueFun_of_Hdn D K z.2 h]
  rw [hEq]
  exact (pcglueD D K).continuous

/-- The gluing map, as a map on the model pcannulus. -/
def pcglueM (z : ↥(pcMsub)) : ℂ := pcglueFun D K (z : ℂ)

theorem pcglueM_apply (z : ↥(pcMsub)) : pcglueM D K z = pcglueFun D K (z : ℂ) := rfl

theorem pccontinuous_glueM : Continuous (pcglueM D K) := by
  have hA : IsClosed {z : ↥(pcMsub) | (z : ℂ) ∈ pcHup D} :=
    (pcisClosed_Hup D).preimage continuous_subtype_val
  have hB : IsClosed {z : ↥(pcMsub) | (z : ℂ) ∈ pcHdn D} :=
    (pcisClosed_Hdn D).preimage continuous_subtype_val
  have hcov : ({z : ↥(pcMsub) | (z : ℂ) ∈ pcHup D} ∪ {z : ↥(pcMsub) | (z : ℂ) ∈ pcHdn D}) = univ := by
    ext z
    constructor
    · intro _; trivial
    · intro _
      have h : (z : ℂ) ∈ pcHup D ∪ pcHdn D := by
        rw [pcHup_union_Hdn D]
        exact z.2
      exact h
  have hcontA : ContinuousOn (pcglueM D K) {z : ↥(pcMsub) | (z : ℂ) ∈ pcHup D} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : ({z : ↥(pcMsub) | (z : ℂ) ∈ pcHup D}).domRestrict (pcglueM D K) =
        fun z : ↥{z : ↥(pcMsub) | (z : ℂ) ∈ pcHup D} =>
          pcglueU D K (⟨((z : ↥(pcMsub)) : ℂ), z.2⟩ : ↥(pcHup D)) := by
      funext z
      exact pcglueFun_of_Hup D K z.2
    rw [hEq]
    exact (pcglueU D K).continuous.comp
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
  have hcontB : ContinuousOn (pcglueM D K) {z : ↥(pcMsub) | (z : ℂ) ∈ pcHdn D} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : ({z : ↥(pcMsub) | (z : ℂ) ∈ pcHdn D}).domRestrict (pcglueM D K) =
        fun z : ↥{z : ↥(pcMsub) | (z : ℂ) ∈ pcHdn D} =>
          pcglueD D K (⟨((z : ↥(pcMsub)) : ℂ), z.2⟩ : ↥(pcHdn D)) := by
      funext z
      by_cases h : (((z : ↥{z : ↥(pcMsub) | (z : ℂ) ∈ pcHdn D}) : ↥(pcMsub)) : ℂ) ∈ pcHup D
      · rw [Set.domRestrict_apply, pcglueM_apply, pcglueFun_of_Hup D K h]
        rw [pcglueU_eq_glueD D K (((z : ↥(pcMsub)) : ℂ)) h z.2]
      · rw [Set.domRestrict_apply, pcglueM_apply, pcglueFun_of_Hdn D K z.2 h]
    rw [hEq]
    exact (pcglueD D K).continuous.comp
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
  refine LocallyFinite.continuous (f := fun i : Bool =>
      bif i then {z : ↥(pcMsub) | (z : ℂ) ∈ pcHup D} else {z : ↥(pcMsub) | (z : ℂ) ∈ pcHdn D})
    (locallyFinite_of_finite _) ?_ ?_ ?_
  · have hunion : (⋃ i : Bool, bif i then {z : ↥(pcMsub) | (z : ℂ) ∈ pcHup D}
        else {z : ↥(pcMsub) | (z : ℂ) ∈ pcHdn D}) =
        ({z : ↥(pcMsub) | (z : ℂ) ∈ pcHup D} ∪ {z : ↥(pcMsub) | (z : ℂ) ∈ pcHdn D}) := by
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

theorem pcabs_lt_two_pi_of_injOn_arc {γ : Work.Smooth.Jordan.PlaneCurve} {a L : ℝ} (hL : L ≠ 0)
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
      exact pcgamma_sub_two_pi a
  have h0 : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hy' : y ∈ Set.Icc 0 1 := ⟨hy0.le, hy1⟩
  have hres := hinj hy' h0 hkey
  linarith

theorem pcconfigOrder {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) {θ₁ θ₂ : ℝ}
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (T_up : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (T_dn : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂)) :
    0 < θ₁ - θ₂ ∧ θ₁ - θ₂ < 2 * Real.pi := by
  have hUp := T_up.simple
  have hDn := T_dn.simple
  -- the third-branch values and their injectivity
  have hup3 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi + (Real.pi / 2) * x) =
        (if b then γ.γ (θ₂ + x * (θ₁ - θ₂))
         else γ.γ (θ₂ + x * (θ₁ - θ₂ - 2 * Real.pi))) := by
    intro x hx
    rw [pctgtB_up3 hout₁ hout₂ hθ₁ hθ₂ ((Real.pi / 2) * x)
      (by nlinarith [Real.pi_pos, hx.1]) (by nlinarith [Real.pi_pos, hx.2]),
      show (Real.pi / 2) * x / (Real.pi / 2) = x by field_simp]
  have hdn3 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi + (Real.pi / 2) * x) =
        (if b then γ.γ (θ₁ - 2 * Real.pi + x * (θ₂ - θ₁ + 2 * Real.pi))
         else γ.γ (θ₁ + x * (θ₂ - θ₁))) := by
    intro x hx
    rw [pctgtB_dn3 hout₁ hout₂ hθ₁ hθ₂ ((Real.pi / 2) * x)
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
      Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi + (Real.pi / 2) * x))
      (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have h := hUp (hmem3 x hx) (hmem3 y hy) hxy
    have h' : (Real.pi / 2) * x = (Real.pi / 2) * y := by linarith
    exact mul_left_cancel₀ (by positivity : (Real.pi / 2) ≠ 0) h'
  have hinjDn : Set.InjOn (fun x : ℝ =>
      Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi + (Real.pi / 2) * x))
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
      show Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ true θ₁ θ₂
        (Real.pi + (Real.pi / 2) * x) =
        Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ true θ₁ θ₂
          (Real.pi + (Real.pi / 2) * y)
      rw [hup3 x hx, hup3 y hy, if_pos rfl, if_pos rfl]
      exact hxy
    have atrue_dn : Set.InjOn (fun x : ℝ =>
        γ.γ (θ₁ - 2 * Real.pi + x * (θ₂ - θ₁ + 2 * Real.pi))) (Set.Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      refine hinjDn hx hy ?_
      show Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ true θ₁ θ₂
        (Real.pi + (Real.pi / 2) * x) =
        Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ true θ₁ θ₂
          (Real.pi + (Real.pi / 2) * y)
      rw [hdn3 x hx, hdn3 y hy, if_pos rfl, if_pos rfl]
      exact hxy
    have h1 : |θ₁ - θ₂| < 2 * Real.pi :=
      pcabs_lt_two_pi_of_injOn_arc (ne_of_inj atrue_up) atrue_up
    have h2 : |θ₂ - θ₁ + 2 * Real.pi| < 2 * Real.pi :=
      pcabs_lt_two_pi_of_injOn_arc (ne_of_inj atrue_dn) atrue_dn
    rw [abs_lt] at h1 h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  | false =>
    have afalse_up : Set.InjOn (fun x : ℝ => γ.γ (θ₂ + x * (θ₁ - θ₂ - 2 * Real.pi)))
        (Set.Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      refine hinjUp hx hy ?_
      show Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ false θ₁ θ₂
        (Real.pi + (Real.pi / 2) * x) =
        Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ false θ₁ θ₂
          (Real.pi + (Real.pi / 2) * y)
      rw [hup3 x hx, hup3 y hy, if_neg (by simp), if_neg (by simp)]
      exact hxy
    have afalse_dn : Set.InjOn (fun x : ℝ => γ.γ (θ₁ + x * (θ₂ - θ₁)))
        (Set.Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      refine hinjDn hx hy ?_
      show Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ false θ₁ θ₂
        (Real.pi + (Real.pi / 2) * x) =
        Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ false θ₁ θ₂
          (Real.pi + (Real.pi / 2) * y)
      rw [hdn3 x hx, hdn3 y hy, if_neg (by simp), if_neg (by simp)]
      exact hxy
    have h1 : |θ₁ - θ₂ - 2 * Real.pi| < 2 * Real.pi :=
      pcabs_lt_two_pi_of_injOn_arc (ne_of_inj afalse_up) afalse_up
    have h2 : |θ₂ - θ₁| < 2 * Real.pi :=
      pcabs_lt_two_pi_of_injOn_arc (ne_of_inj afalse_dn) afalse_dn
    rw [abs_lt] at h1 h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end Config


/-! ## The inner-boundary curve and the assembled disc map

This section builds the continuous injection `pcG : 𝔻 → 𝔻` which fixes the boundary circle
pointwise and carries the inner circle into `γ.trace`.  It is the input of
`Work.SphereJordan.pcannulusInnerReparam`. -/

namespace Assembly

section

theorem pccirclePoint_add_int_two_pi (θ : ℝ) (k : ℤ) :
    Work.Smooth.Jordan.circlePoint (θ + (k : ℝ) * (2 * Real.pi)) =
      Work.Smooth.Jordan.circlePoint θ := by
  apply Subtype.ext
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  have h : (((θ + (k : ℝ) * (2 * Real.pi) : ℝ)) : ℂ) * Complex.I
      = (θ : ℂ) * Complex.I + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem pchalfCirclePoint_add_int_two_pi (θ : ℝ) (k : ℤ) :
    Work.Smooth.SphereJordan.halfCirclePoint (θ + (k : ℝ) * (2 * Real.pi)) =
      Work.Smooth.SphereJordan.halfCirclePoint θ := by
  apply Subtype.ext
  rw [Work.Smooth.SphereJordan.halfCirclePoint_coe,
    Work.Smooth.SphereJordan.halfCirclePoint_coe, pccirclePoint_add_int_two_pi]

theorem pcnorm_halfCirclePoint (θ : ℝ) :
    ‖((Work.Smooth.SphereJordan.halfCirclePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)‖
      = 1 / 2 := by
  rw [Work.Smooth.SphereJordan.halfCirclePoint_coe, norm_mul,
    Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I, mul_one]
  norm_num

theorem pchalfCirclePoint_mem_Msub (θ : ℝ) :
    ((Work.Smooth.SphereJordan.halfCirclePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ pcMsub := by
  refine ⟨?_, ?_⟩
  · rw [pcnorm_halfCirclePoint]
  · rw [pcnorm_halfCirclePoint]; norm_num

theorem pchalfCirclePoint_innerPtUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) :
    Work.Smooth.SphereJordan.halfCirclePoint (pccutAng S + θ) = pcinnerPtUp S θ := by
  rw [Work.Smooth.SphereJordan.halfCirclePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  rfl

theorem pchalfCirclePoint_innerPtDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) :
    Work.Smooth.SphereJordan.halfCirclePoint (pccutAng S - Real.pi + θ) = pcinnerPtDn S θ := by
  rw [Work.Smooth.SphereJordan.halfCirclePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  rfl

theorem pchalfCirclePoint_reduce (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) :
    Work.Smooth.SphereJordan.halfCirclePoint θ =
      Work.Smooth.SphereJordan.halfCirclePoint
        (pccutAng S - Real.pi + Work.Smooth.SphereJordan.pcperPt (θ - (pccutAng S - Real.pi))) := by
  set r := Work.Smooth.SphereJordan.pcperPt (θ - (pccutAng S - Real.pi)) with hr
  set k : ℤ := ⌊(θ - (pccutAng S - Real.pi)) / (2 * Real.pi)⌋ with hk
  have hkey : θ - (pccutAng S - Real.pi) = r + (k : ℝ) * (2 * Real.pi) := by
    rw [hr, hk, Work.Smooth.SphereJordan.pcperPt]; ring
  have hθ : θ = (pccutAng S - Real.pi + r) + (k : ℝ) * (2 * Real.pi) := by linarith
  rw [hθ]
  exact pchalfCirclePoint_add_int_two_pi (pccutAng S - Real.pi + r) k

/-! ## The curve traced by the gluing map on the inner circle -/

def pcbetaC (D : pcSourceData S) (K : pcTwoCuts S) (θ : ℝ) : ℂ :=
  pcglueFun D K
    (((Work.Smooth.SphereJordan.halfCirclePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ))

theorem pcglueFun_inner_mem_trace (D : pcSourceData S) (K : pcTwoCuts S) (θ : ℝ) :
    ∃ θ' : ℝ, pcbetaC D K θ = γ.γ θ' := by
  rw [pcbetaC, pchalfCirclePoint_reduce (S := S) θ]
  set r := Work.Smooth.SphereJordan.pcperPt (θ - (pccutAng S - Real.pi)) with hr
  obtain ⟨hr0', hr2'⟩ := Work.SphereJordan.pcperPt_mem (θ - (pccutAng S - Real.pi))
  have hr0 : 0 ≤ r := by rw [hr]; exact hr0'
  have hr2 : r < 2 * Real.pi := by rw [hr]; exact hr2'
  rcases lt_or_ge r Real.pi with hlt | hge
  · rw [pchalfCirclePoint_innerPtDn, pcglueFun_innerDn D K r hr0 (le_of_lt hlt),
      pcTwoCuts.pcTd_inner K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K r hr0 (le_of_lt hlt)]
    by_cases hb : K.b = true
    · rw [if_pos hb]; exact ⟨_, rfl⟩
    · rw [if_neg hb]; exact ⟨_, rfl⟩
  · have h0 : 0 ≤ r - Real.pi := by linarith
    have h1 : r - Real.pi ≤ Real.pi := by linarith
    rw [show pccutAng S - Real.pi + r = pccutAng S + (r - Real.pi) by ring,
      pchalfCirclePoint_innerPtUp, pcglueFun_innerUp D K (r - Real.pi) h0 h1,
      pcTwoCuts.pcTu_inner K.hout₁ K.hout₂ K.hθ₁ K.hθ₂ K (r - Real.pi) h0 h1]
    by_cases hb : K.b = true
    · rw [if_pos hb]; exact ⟨_, rfl⟩
    · rw [if_neg hb]; exact ⟨_, rfl⟩

theorem pccontinuous_betaC (D : pcSourceData S) (K : pcTwoCuts S) : Continuous (pcbetaC D K) := by
  have hval : Continuous fun θ : ℝ =>
      ((Work.Smooth.SphereJordan.halfCirclePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ) :=
    continuous_subtype_val.comp Work.SphereJordan.pccontinuous_halfCirclePoint
  have hbase : Continuous fun θ : ℝ =>
      (⟨((Work.Smooth.SphereJordan.halfCirclePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ),
        pchalfCirclePoint_mem_Msub θ⟩ : ↥(pcMsub)) :=
    Continuous.subtype_mk hval _
  exact (pccontinuous_glueM D K).comp hbase

theorem pcbetaC_periodic (D : pcSourceData S) (K : pcTwoCuts S) :
    ∀ θ : ℝ, pcbetaC D K (θ + 2 * Real.pi) = pcbetaC D K θ := by
  intro θ
  rw [pcbetaC, pcbetaC, Work.SphereJordan.pchalfCirclePoint_add_two_pi]

theorem pcbetaC_injOn (D : pcSourceData S) (K : pcTwoCuts S) :
    Set.InjOn (pcbetaC D K) (Set.Ico 0 (2 * Real.pi)) := by
  intro a ha b hb hab
  have h1 : ((Work.Smooth.SphereJordan.halfCirclePoint a : Work.Smooth.SphereJordan.Disc) : ℂ) =
      ((Work.Smooth.SphereJordan.halfCirclePoint b : Work.Smooth.SphereJordan.Disc) : ℂ) :=
    pcglueFun_injOn D K (pchalfCirclePoint_mem_Msub a) (pchalfCirclePoint_mem_Msub b) hab
  exact Work.SphereJordan.pchalfCirclePoint_injOn_Ico ha hb (Subtype.ext h1)

theorem pcnot_isBounded_U {c : Work.Smooth.Jordan.PlaneCurve}
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

theorem pcV_eq_compl {c : Work.Smooth.Jordan.PlaneCurve}
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

theorem pcV_eq_of_trace_eq {c₁ c₂ : Work.Smooth.Jordan.PlaneCurve}
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
          rw [pcV_eq_compl S₁.toPlaneSeparation, pcV_eq_compl S₂.toPlaneSeparation, h, hUeq]
        · exact absurd (S₁.bounded_V.subset h4) (pcnot_isBounded_U S₂.toPlaneSeparation)
      · exact absurd (S₂.bounded_V.subset h3) (pcnot_isBounded_U S₁.toPlaneSeparation)
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

theorem pcrange_betaC (D : pcSourceData S) (K : pcTwoCuts S) (hs : γ.IsSimple) :
    Set.range (pcbetaC D K) = γ.trace := by
  refine Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic (pccontinuous_betaC D K)
    (pcbetaC_periodic D K) (pcbetaC_injOn D K) γ.cont γ.periodic hs ?_
  rintro _ ⟨θ, rfl⟩
  obtain ⟨θ', hθ'⟩ := pcglueFun_inner_mem_trace D K θ
  exact ⟨θ', hθ'.symm⟩

/-- The inner boundary curve, as a plane curve. -/
def pcbetaCurve (D : pcSourceData S) (K : pcTwoCuts S) : Work.Smooth.Jordan.PlaneCurve where
  γ := pcbetaC D K
  cont := pccontinuous_betaC D K
  periodic := pcbetaC_periodic D K

theorem pcbetaCurve_isSimple (D : pcSourceData S) (K : pcTwoCuts S) :
    (pcbetaCurve D K).IsSimple := pcbetaC_injOn D K

/-- A Schoenflies datum for the inner boundary curve. -/
def pcbetaSch (D : pcSourceData S) (K : pcTwoCuts S) (h : Work.Smooth.SphereJordan.PlaneHypothesis) :
    Work.Smooth.Jordan.PlaneSchoenflies (pcbetaCurve D K) :=
  (h (pcbetaCurve D K) (pcbetaCurve_isSimple D K)).some

theorem pcbetaSch_boundary (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (θ : ℝ) :
    (pcbetaSch D K h).e (Work.Smooth.SphereJordan.circlePoint θ) = pcbetaC D K θ :=
  (pcbetaSch D K h).boundary θ

theorem pctrace_betaCurve (D : pcSourceData S) (K : pcTwoCuts S) (hs : γ.IsSimple) :
    (pcbetaCurve D K).trace = γ.trace := by
  show Set.range (pcbetaC D K) = γ.trace
  exact pcrange_betaC D K hs

theorem pcV_beta_eq (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple) :
    (pcbetaSch D K h).V = S.V :=
  pcV_eq_of_trace_eq (c₁ := pcbetaCurve D K) (c₂ := γ) (pctrace_betaCurve D K hs) _ _

/-! ## The gluing map is the identity on the boundary circle -/

theorem pcouterPt_eq_circlePoint (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    pcouterPt S x =
      ((Work.Smooth.SphereJordan.circlePoint (pccutAng S + Real.pi * x) :
        Work.Smooth.SphereJordan.Disc) : ℂ) := by
  rw [pcouterPt, Work.Smooth.Jordan.circlePoint_coe]

theorem pcouterPtDn_eq_circlePoint (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    pcouterPtDn S x =
      ((Work.Smooth.SphereJordan.circlePoint (pccutAng S + Real.pi + Real.pi * x) :
        Work.Smooth.SphereJordan.Disc) : ℂ) := by
  rw [pcouterPtDn, Work.Smooth.Jordan.circlePoint_coe]

theorem pccirclePoint_perPt_reduce (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) :
    Work.Smooth.SphereJordan.circlePoint θ =
      Work.Smooth.SphereJordan.circlePoint
        (pccutAng S + Work.Smooth.SphereJordan.pcperPt (θ - pccutAng S)) := by
  set r := Work.Smooth.SphereJordan.pcperPt (θ - pccutAng S) with hr
  set k : ℤ := ⌊(θ - pccutAng S) / (2 * Real.pi)⌋ with hk
  have hkey : θ - pccutAng S = r + (k : ℝ) * (2 * Real.pi) := by
    rw [hr, hk, Work.Smooth.SphereJordan.pcperPt]; ring
  have hθ : θ = (pccutAng S + r) + (k : ℝ) * (2 * Real.pi) := by linarith
  rw [hθ]
  exact pccirclePoint_add_int_two_pi (pccutAng S + r) k

theorem pcglueFun_circlePoint (D : pcSourceData S) (K : pcTwoCuts S) (θ : ℝ) :
    pcglueFun D K (((Work.Smooth.SphereJordan.circlePoint θ :
        Work.Smooth.SphereJordan.Disc) : ℂ)) =
      ((Work.Smooth.SphereJordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ) := by
  rw [pccirclePoint_perPt_reduce (S := S) θ]
  set r := Work.Smooth.SphereJordan.pcperPt (θ - pccutAng S) with hr
  obtain ⟨hr0, hr2⟩ := Work.SphereJordan.pcperPt_mem (θ - pccutAng S)
  have hr0' : 0 ≤ r := by rw [hr]; exact hr0
  have hr2' : r < 2 * Real.pi := by rw [hr]; exact hr2
  rcases lt_or_ge r Real.pi with hlt | hge
  · have hx0 : 0 ≤ r / Real.pi := div_nonneg hr0' Real.pi_pos.le
    have hx1 : r / Real.pi ≤ 1 := by
      rw [div_le_one Real.pi_pos]; exact le_of_lt hlt
    have hpt : pcouterPt S (r / Real.pi) =
        ((Work.Smooth.SphereJordan.circlePoint (pccutAng S + r) :
          Work.Smooth.SphereJordan.Disc) : ℂ) := by
      rw [pcouterPt_eq_circlePoint,
        show pccutAng S + Real.pi * (r / Real.pi) = pccutAng S + r by field_simp]
    rw [← hpt]
    exact pcglueFun_outer D K (r / Real.pi) hx0 hx1
  · have hy0 : 0 ≤ (r - Real.pi) / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
    have hy1 : (r - Real.pi) / Real.pi ≤ 1 := by
      rw [div_le_one Real.pi_pos]; linarith
    have hpt : pcouterPtDn S ((r - Real.pi) / Real.pi) =
        ((Work.Smooth.SphereJordan.circlePoint (pccutAng S + r) :
          Work.Smooth.SphereJordan.Disc) : ℂ) := by
      rw [pcouterPtDn_eq_circlePoint,
        show pccutAng S + Real.pi + Real.pi * ((r - Real.pi) / Real.pi) = pccutAng S + r by
          field_simp; ring]
    rw [← hpt]
    exact pcglueFun_outerDn D K ((r - Real.pi) / Real.pi) hy0 hy1

/-! ## The gluing map on the model pcannulus -/

theorem pcglueFun_mem_annulus (D : pcSourceData S) (K : pcTwoCuts S) {z : ℂ} (hz : z ∈ pcMsub) :
    pcglueFun D K z ∈ Work.Smooth.SphereJordan.pcannulus S := by
  have hz' : z ∈ pcHup D ∪ pcHdn D := by rw [pcHup_union_Hdn D]; exact hz
  have hmem : pcglueFun D K z ∈ Set.range (pcglueU D K) ∪ Set.range (pcglueD D K) := by
    rcases hz' with h1 | h1
    · exact Or.inl ⟨⟨z, h1⟩, (pcglueFun_of_Hup D K h1).symm⟩
    · by_cases h2 : z ∈ pcHup D
      · exact Or.inl ⟨⟨z, h2⟩, (pcglueFun_of_Hup D K h2).symm⟩
      · exact Or.inr ⟨⟨z, h1⟩, (pcglueFun_of_Hdn D K h1 h2).symm⟩
  rw [← K.htil, ← pcrange_glueU D K, ← pcrange_glueD D K]
  exact hmem

/-! ## The assembled map on the model disc -/

theorem pccoe_mem_Msub_of_le (z : Work.Smooth.SphereJordan.Disc)
    (hz : (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖) :
    ((z : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ pcMsub := by
  refine ⟨hz, ?_⟩
  have h := z.2
  rw [Metric.mem_closedBall, dist_zero_right] at h
  exact h

theorem pcdbl_mem_closedBall {z : Work.Smooth.SphereJordan.Disc}
    (hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2) :
    (2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  linarith

theorem pcexists_halfCirclePoint_eq (z : Work.Smooth.SphereJordan.Disc)
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

def pcGc (D : pcSourceData S) (K : pcTwoCuts S) (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (z : Work.Smooth.SphereJordan.Disc) : ℂ :=
  if hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2 then
    (pcbetaSch D K h).e
      ⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ), pcdbl_mem_closedBall hz⟩
  else pcglueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ)

theorem pcGc_inner (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) {z : Work.Smooth.SphereJordan.Disc}
    (hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2) :
    pcGc D K h z = (pcbetaSch D K h).e
      ⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ), pcdbl_mem_closedBall hz⟩ := by
  rw [pcGc, dif_pos hz]

theorem pcGc_outer (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) {z : Work.Smooth.SphereJordan.Disc}
    (hz : ¬ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2) :
    pcGc D K h z = pcglueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ) := by
  rw [pcGc, dif_neg hz]

theorem pcGc_eq_glueFun_of_half (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) {z : Work.Smooth.SphereJordan.Disc}
    (hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 / 2) :
    pcGc D K h z = pcglueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ) := by
  obtain ⟨θ, hθ⟩ := pcexists_halfCirclePoint_eq z hz
  rw [pcGc_inner D K h hz.le]
  have hpt : (⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ),
      pcdbl_mem_closedBall hz.le⟩ : Work.Smooth.SphereJordan.Disc) =
      Work.Smooth.SphereJordan.circlePoint θ := by
    refine Subtype.ext ?_
    show (2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ) =
      ((Work.Smooth.SphereJordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)
    rw [← hθ, Work.Smooth.SphereJordan.halfCirclePoint_coe]
    ring
  rw [hpt, pcbetaSch_boundary D K h θ]
  show pcbetaC D K θ = pcglueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ)
  rw [pcbetaC, hθ]

theorem pcGc_mem_Vbeta (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) {z : Work.Smooth.SphereJordan.Disc}
    (hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 / 2) :
    pcGc D K h z ∈ (pcbetaSch D K h).V := by
  rw [pcGc_inner D K h hz.le]
  rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq (pcbetaSch D K h)]
  refine ⟨⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ),
    pcdbl_mem_closedBall hz.le⟩, ?_, rfl⟩
  show ‖(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1
  rw [norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  linarith

theorem pcGc_notMem_Vbeta (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    {z : Work.Smooth.SphereJordan.Disc}
    (hz : (1 : ℝ) / 2 < ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖) :
    pcGc D K h z ∉ (pcbetaSch D K h).V := by
  rw [pcGc_outer D K h (not_le.mpr hz), pcV_beta_eq D K h hs]
  exact (pcglueFun_mem_annulus D K (pccoe_mem_Msub_of_le z hz.le)).2

theorem pccontinuousOn_Gc_inner (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) :
    ContinuousOn (pcGc D K h)
      {z : Work.Smooth.SphereJordan.Disc |
        ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hh : ({z : Work.Smooth.SphereJordan.Disc |
      ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2}).domRestrict (pcGc D K h) =
      fun z : {z : Work.Smooth.SphereJordan.Disc |
        ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2} =>
        (pcbetaSch D K h).e ⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ),
          pcdbl_mem_closedBall z.2⟩ := by
    funext z
    exact pcGc_inner D K h z.2
  rw [hh]
  exact (pcbetaSch D K h).e.continuous.comp
    (Continuous.subtype_mk (by fun_prop) (fun z => pcdbl_mem_closedBall z.2))

theorem pccontinuousOn_Gc_outer (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) :
    ContinuousOn (pcGc D K h)
      {z : Work.Smooth.SphereJordan.Disc |
        (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hh : ({z : Work.Smooth.SphereJordan.Disc |
      (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖}).domRestrict (pcGc D K h) =
      fun z : {z : Work.Smooth.SphereJordan.Disc |
        (1 : ℝ) / 2 ≤ ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖} =>
        pcglueM D K ⟨((z : Work.Smooth.SphereJordan.Disc) : ℂ),
          pccoe_mem_Msub_of_le (z : Work.Smooth.SphereJordan.Disc) z.2⟩ := by
    funext z
    by_cases hlt : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2
    · have hzeq : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 / 2 :=
        le_antisymm hlt z.2
      rw [Set.domRestrict_apply, pcGc_eq_glueFun_of_half D K h hzeq]
      exact (pcglueM_apply D K ⟨((z : Work.Smooth.SphereJordan.Disc) : ℂ),
        pccoe_mem_Msub_of_le (z : Work.Smooth.SphereJordan.Disc) z.2⟩).symm
    · rw [Set.domRestrict_apply, pcGc_outer D K h hlt]
      exact (pcglueM_apply D K ⟨((z : Work.Smooth.SphereJordan.Disc) : ℂ),
        pccoe_mem_Msub_of_le (z : Work.Smooth.SphereJordan.Disc) z.2⟩).symm
  rw [hh]
  exact (pccontinuous_glueM D K).comp
    (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
      (fun z => pccoe_mem_Msub_of_le (z : Work.Smooth.SphereJordan.Disc) z.2))

theorem pccontinuous_Gc (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) : Continuous (pcGc D K h) := by
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
    · simpa only [Bool.cond_false] using pccontinuousOn_Gc_outer D K h
    · simpa only [Bool.cond_true] using pccontinuousOn_Gc_inner D K h

theorem pcGc_mem_closedBall (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (z : Work.Smooth.SphereJordan.Disc) :
    pcGc D K h z ∈ Metric.closedBall (0 : ℂ) 1 := by
  by_cases hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2
  · rw [pcGc_inner D K h hz]
    have h1 : (pcbetaSch D K h).e ⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ),
        pcdbl_mem_closedBall hz⟩ ∈ closure (pcbetaSch D K h).V := by
      rw [← (pcbetaSch D K h).range_e]
      exact ⟨_, rfl⟩
    rw [pcV_beta_eq D K h hs] at h1
    have h2 := Work.Smooth.SphereJordan.pcclosure_V_subset_openBall S hball h1
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt h2
  · rw [pcGc_outer D K h hz]
    exact (pcglueFun_mem_annulus D K
      (pccoe_mem_Msub_of_le z (le_of_lt (not_le.mp hz)))).1

def pcG (D : pcSourceData S) (K : pcTwoCuts S) (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) :
    C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc) :=
  ⟨fun z => ⟨pcGc D K h z, pcGc_mem_closedBall D K h hs hball z⟩,
    Continuous.subtype_mk (pccontinuous_Gc D K h) _⟩

theorem pcG_apply (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (z : Work.Smooth.SphereJordan.Disc) :
    ((pcG D K h hs hball z : Work.Smooth.SphereJordan.Disc) : ℂ) = pcGc D K h z := rfl

theorem pcGc_injective (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (_hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) : Function.Injective (pcGc D K h) := by
  intro z z' h'
  by_cases hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2
  · by_cases hz' : ‖((z' : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2
    · rw [pcGc_inner D K h hz, pcGc_inner D K h hz'] at h'
      have h2 : (⟨(2 : ℂ) * ((z : Work.Smooth.SphereJordan.Disc) : ℂ),
          pcdbl_mem_closedBall hz⟩ : Work.Smooth.SphereJordan.Disc) =
          ⟨(2 : ℂ) * ((z' : Work.Smooth.SphereJordan.Disc) : ℂ),
            pcdbl_mem_closedBall hz'⟩ := (pcbetaSch D K h).inj h'
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
      · have h1 : pcGc D K h z' ∈ (pcbetaSch D K h).V := h' ▸ pcGc_mem_Vbeta D K h hzlt
        exact absurd h1 (pcGc_notMem_Vbeta D K h hs hz'2)
      · have hzeq : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 / 2 :=
          le_antisymm hz (not_lt.mp hzlt)
        have hzM : ((z : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ pcMsub :=
          pccoe_mem_Msub_of_le z hzeq.ge
        have hz'M : ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ pcMsub :=
          pccoe_mem_Msub_of_le z' hz'2.le
        have hglue : pcglueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ) =
            pcglueFun D K ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) := by
          have h1 : pcGc D K h z = pcglueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ) :=
            pcGc_eq_glueFun_of_half D K h hzeq
          have h2 : pcGc D K h z' = pcglueFun D K ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) :=
            pcGc_outer D K h hz'
          rw [← h1, h', h2]
        rw [pcglueFun_injOn D K hzM hz'M hglue] at hzeq
        linarith
  · have hz2 : (1 : ℝ) / 2 < ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ := not_le.mp hz
    by_cases hz' : ‖((z' : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2
    · by_cases hz'lt : ‖((z' : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 / 2
      · have h1 : pcGc D K h z' ∈ (pcbetaSch D K h).V := pcGc_mem_Vbeta D K h hz'lt
        rw [← h'] at h1
        exact absurd h1 (pcGc_notMem_Vbeta D K h hs hz2)
      · have hz'eq : ‖((z' : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 / 2 :=
          le_antisymm hz' (not_lt.mp hz'lt)
        have hzM : ((z : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ pcMsub :=
          pccoe_mem_Msub_of_le z hz2.le
        have hz'M : ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ pcMsub :=
          pccoe_mem_Msub_of_le z' hz'eq.ge
        have hglue : pcglueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ) =
            pcglueFun D K ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) := by
          have h1 : pcGc D K h z = pcglueFun D K ((z : Work.Smooth.SphereJordan.Disc) : ℂ) :=
            pcGc_outer D K h hz
          have h2 : pcGc D K h z' = pcglueFun D K ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) :=
            pcGc_eq_glueFun_of_half D K h hz'eq
          rw [← h1, h', h2]
        exact Subtype.ext (pcglueFun_injOn D K hzM hz'M hglue)
    · have hz'M : ((z' : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ pcMsub :=
        pccoe_mem_Msub_of_le z' (not_le.mp hz').le
      have hzM : ((z : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ pcMsub :=
        pccoe_mem_Msub_of_le z hz2.le
      rw [pcGc_outer D K h hz, pcGc_outer D K h hz'] at h'
      exact Subtype.ext (pcglueFun_injOn D K hzM hz'M h')

theorem pcG_injective (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (_hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) : Function.Injective (pcG D K h hs _hball) := by
  intro z z' h'
  refine pcGc_injective D K h hs _hball ?_
  simpa only [pcG_apply] using congrArg
    (fun w : Work.Smooth.SphereJordan.Disc => ((w : Work.Smooth.SphereJordan.Disc) : ℂ)) h'

theorem pcG_circlePoint (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (θ : ℝ) :
    pcG D K h hs hball (Work.Smooth.SphereJordan.circlePoint θ) =
      Work.Smooth.SphereJordan.circlePoint θ := by
  refine Subtype.ext ?_
  show pcGc D K h (Work.Smooth.SphereJordan.circlePoint θ) =
    ((Work.Smooth.SphereJordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)
  have hnorm : ‖((Work.Smooth.SphereJordan.circlePoint θ :
      Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 :=
    Work.SphereJordan.pccirclePoint_cp_norm θ
  rw [pcGc_outer D K h (by rw [hnorm]; norm_num)]
  exact pcglueFun_circlePoint D K θ

theorem pcG_halfCirclePoint (D : pcSourceData S) (K : pcTwoCuts S)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (θ : ℝ) :
    ∃ θ' : ℝ, ((pcG D K h hs hball (Work.Smooth.SphereJordan.halfCirclePoint θ) :
      Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ' := by
  have hnorm : ‖((Work.Smooth.SphereJordan.halfCirclePoint θ :
      Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 / 2 := pcnorm_halfCirclePoint θ
  have hval : pcGc D K h (Work.Smooth.SphereJordan.halfCirclePoint θ) =
      (pcbetaSch D K h).e (Work.Smooth.SphereJordan.circlePoint θ) := by
    rw [pcGc_inner D K h hnorm.le]
    have hpt : (⟨(2 : ℂ) * ((Work.Smooth.SphereJordan.halfCirclePoint θ :
        Work.Smooth.SphereJordan.Disc) : ℂ), pcdbl_mem_closedBall hnorm.le⟩ :
        Work.Smooth.SphereJordan.Disc) = Work.Smooth.SphereJordan.circlePoint θ := by
      refine Subtype.ext ?_
      show (2 : ℂ) * ((Work.Smooth.SphereJordan.halfCirclePoint θ :
        Work.Smooth.SphereJordan.Disc) : ℂ) =
        ((Work.Smooth.SphereJordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)
      rw [Work.Smooth.SphereJordan.halfCirclePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
      ring
    rw [hpt]
  obtain ⟨θ', hθ'⟩ := pcglueFun_inner_mem_trace D K θ
  exact ⟨θ', by rw [pcG_apply, hval, pcbetaSch_boundary D K h θ, pcbetaC]; exact hθ'⟩

end

end Assembly

theorem pctwoCutsAssembly (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) + (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) - (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (T_up : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (T_dn : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (htil : closure T_up.V ∪ closure T_dn.V = Work.Smooth.SphereJordan.pcannulus S)
    (hmeet : closure T_up.V ∩ closure T_dn.V =
      Work.Smooth.SphereJordan.pccut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.pccut₂ S t₂ s₂) :
    ∃ (F : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc)) (s : ℝ),
      (s = 1 ∨ s = -1) ∧ Function.Injective F ∧
      (∀ θ : ℝ, F (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ θ : ℝ, ((F (Work.Smooth.SphereJordan.halfCirclePoint (s * θ)) :
          Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ) := by
  let K : pcTwoCuts S :=
    { t₁ := t₁, s₁ := s₁, t₂ := t₂, s₂ := s₂, b := b, θ₁ := θ₁, θ₂ := θ₂,
      hout₁ := hout₁, hout₂ := hout₂, hθ₁ := hθ₁, hθ₂ := hθ₂,
      Tu := T_up, Td := T_dn, htil := htil, hmeet := hmeet }
  obtain ⟨D⟩ := pcexists_sourceData h S
  exact Work.SphereJordan.pcannulusInnerReparam hball S
    (Assembly.pcG D K h hs hball) (Assembly.pcG_injective D K h hs hball)
    (Assembly.pcG_circlePoint D K h hs hball) (Assembly.pcG_halfCirclePoint D K h hs hball)

end

end Work.SphereJordan
