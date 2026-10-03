import Mathlib
import Submission.Work.Fatou.Surface.Core
import Submission.Work.Fatou.Surface.Manifold
import Submission.Work.Fatou.DevH.basic
import Submission.Work.Fatou.Smooth
import Submission.Work.Fatou.DevH.devH_deriv
import Submission.Lib.Unif2.Commons.Analysis.Complex.UpperHalfPlane.halfPlane_disc_diffeomorph
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
import Submission.Work.Fatou.Surface.Wirtinger.dz_dzbar_comp
import Submission.Work.Fatou.Surface.Wirtinger.dz_dzbar_sub_const
import Submission.Work.Fatou.Surface.devH_wirtinger

/-!
# The half-plane case of uniformization is impossible for `XF`

The complex structure on `XF D = ℂ` is defined by the charts `ζ ↦ devH (ζ - n)`, where `devH` is the
interpolating map of `Submission/Work/Fatou/Setup.lean`: it is `C¹`, globally injective, and its
Wirtinger derivatives satisfy `|∂ devH - 1| ≤ 1/16`, `|∂̄ devH| ≤ 1/32`, so its dilatation is at most
`1/30 < 1`.

Suppose `Ψ : XF D ≃ₘ ℍ` were a biholomorphism.  Composing with the (bounded) Cayley transform
`ℍ ≃ₘ ` (open unit disc) and reading the result in the charts `chart D n` gives that, near any point
`z`, the composed map `g = cayley ∘ Ψ ∘ ofℂ` agrees with a *holomorphic* function of `devH (· - n)`:
on the chart source, `g z = F_n (devH (z - n))` with `F_n` holomorphic (as the coordinate expression
of a `C^∞` map of complex manifolds) and injective (hence `F_n' ≠ 0`).  Therefore

  `∂g = F_n' · ∂ devH`,  `∂̄g = F_n' · ∂̄ devH`,

whence `|∂̄g| ≤ (1/15)|∂g|` and `∂g ≠ 0` pointwise; moreover `g` is injective and `‖g‖ ≤ 1`.  This
contradicts `QCLiouville` (the length–area theorem: a bounded injective `C¹` map of the plane whose
dilatation is bounded away from `1` cannot exist).  ∎
-/

namespace Work.Fatou.Surface

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- The open unit disc, as an open subset of `ℂ`. -/
def unitDisc : TopologicalSpace.Opens ℂ := ⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩

/-- The source of the chart of index `n` is open. -/
theorem isOpen_chartSource (D : FatouData) (n : ℤ) : IsOpen (D.chartSource n) := by
  rw [← D.chart_source n]
  exact (D.chart n).open_source

/-- Every point lies in the source of the chart of index `⌊Re z⌋`. -/
theorem ofℂ_mem_chartSource_floor (D : FatouData) (z : ℂ) :
    D.ofℂ z ∈ D.chartSource ⌊z.re⌋ := by
  rw [D.mem_chartSource]
  simp only [D.toℂ_ofℂ]
  have h1 : ((⌊z.re⌋ : ℤ) : ℝ) ≤ z.re := Int.floor_le z.re
  have h2 : z.re < ((⌊z.re⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one z.re
  constructor <;> linarith

/-- In the chart `chart D n`, the map `cayley ∘ Ψ` is complex differentiable: it is the coordinate
expression of a `C^∞` map of complex manifolds, read in the source chart `chart D n` and in the
preferred chart `refl ℂ` of the model space `ℂ` at the target point. -/
theorem contDiffOn_chart_symm (D : FatouData)
    (Φ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ unitDisc) (n : ℤ) :
    ContDiffOn ℂ 1 (fun w : ℂ => (Φ ((D.chart n).symm w) : ℂ)) (D.chart n).target := by
  intro u hu
  have hx : (D.chart n).symm u ∈ (D.chart n).source := (D.chart n).map_target hu
  have hy : (fun x : D.XF => (Φ x : ℂ)) ((D.chart n).symm u) ∈
      (OpenPartialHomeomorph.refl ℂ).source := trivial
  have he : D.chart n ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 D.XF :=
    IsManifold.subset_maximalAtlas (Set.mem_range_self n)
  have he' : OpenPartialHomeomorph.refl ℂ ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 ℂ := by
    apply IsManifold.subset_maximalAtlas
    rw [chartedSpaceSelf_atlas]
  have hc1 : ContMDiffWithinAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) 1
      (fun x : D.XF => (Φ x : ℂ)) Set.univ ((D.chart n).symm u) :=
    ((contMDiff_subtype_val.comp Φ.contMDiff).of_le (by norm_num)).contMDiffAt.contMDiffWithinAt
  obtain ⟨-, hcd'⟩ := (contMDiffWithinAt_iff_of_mem_maximalAtlas (e := D.chart n)
      (e' := OpenPartialHomeomorph.refl ℂ) (f := fun x : D.XF => (Φ x : ℂ))
      (s := Set.univ) (x := (D.chart n).symm u) (n := 1) he he' hx hy).mp hc1
  have hset : ((D.chart n).extend (modelWithCornersSelf ℂ ℂ)).symm ⁻¹' (Set.univ : Set D.XF) ∩
      Set.range (modelWithCornersSelf ℂ ℂ) = Set.univ := by
    simp only [preimage_univ, modelWithCornersSelf_coe, range_id, inter_self]
  have hpt : ((D.chart n).extend (modelWithCornersSelf ℂ ℂ)) ((D.chart n).symm u) = u := by
    simp only [OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialHomeomorph.toFun_eq_coe,
      OpenPartialHomeomorph.coe_toPartialHomeomorph]
    exact (D.chart n).right_inv hu
  have hfun : ∀ w : ℂ, ((OpenPartialHomeomorph.refl ℂ).extend (modelWithCornersSelf ℂ ℂ))
      ((fun x : D.XF => (Φ x : ℂ)) (((D.chart n).extend (modelWithCornersSelf ℂ ℂ)).symm w)) =
      (Φ ((D.chart n).symm w) : ℂ) := by
    intro w
    simp only [OpenPartialHomeomorph.extend, OpenPartialHomeomorph.refl_partialEquiv,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl,
      PartialHomeomorph.coe_toPartialEquiv_symm, OpenPartialHomeomorph.coe_toPartialHomeomorph_symm,
      PartialEquiv.refl_coe, id_eq]
  rw [hset, hpt] at hcd'
  exact (ContDiffWithinAt.congr hcd' (fun w _ => (hfun w).symm) (hfun u).symm).mono
    (subset_univ _)

/-- The coordinate expression of `cayley ∘ Ψ` in the chart `chart D n` is holomorphic on the
(open) chart target. -/
theorem analyticAt_chart_symm (D : FatouData)
    (Φ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ unitDisc) (n : ℤ) {u : ℂ}
    (hu : u ∈ (D.chart n).target) :
    AnalyticAt ℂ (fun w : ℂ => (Φ ((D.chart n).symm w) : ℂ)) u := by
  have hOn := contDiffOn_chart_symm D Φ n
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => (Φ ((D.chart n).symm w) : ℂ))
      (D.chart n).target :=
    fun w hw => (hOn w hw).differentiableWithinAt (by norm_num)
  exact (hdiff.analyticOnNhd (D.chart n).open_target) u hu

/-- The coordinate expression of `cayley ∘ Ψ` in the chart `chart D n` is injective on the chart
target. -/
theorem chart_symm_injOn (D : FatouData)
    (Φ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ unitDisc) (n : ℤ) :
    Set.InjOn (fun w : ℂ => (Φ ((D.chart n).symm w) : ℂ)) (D.chart n).target := by
  intro w₁ h₁ w₂ h₂ hw
  have h1 : Φ ((D.chart n).symm w₁) = Φ ((D.chart n).symm w₂) := Subtype.ext hw
  have h2 : (D.chart n).symm w₁ = (D.chart n).symm w₂ := Φ.injective h1
  calc w₁ = (D.chart n) ((D.chart n).symm w₁) := ((D.chart n).right_inv h₁).symm
    _ = (D.chart n) ((D.chart n).symm w₂) := by rw [h2]
    _ = w₂ := (D.chart n).right_inv h₂

/-- Hence its derivative does not vanish (an injective holomorphic function has nonzero
derivative). -/
theorem deriv_chart_symm_ne_zero (D : FatouData)
    (Φ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ unitDisc) (n : ℤ) {u : ℂ}
    (hu : u ∈ (D.chart n).target) :
    deriv (fun w : ℂ => (Φ ((D.chart n).symm w) : ℂ)) u ≠ 0 := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp ((D.chart n).open_target.mem_nhds hu)
  exact Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hr
    (analyticAt_chart_symm D Φ n hu) ((chart_symm_injOn D Φ n).mono hrU)

/-- Near a point of the source of `chart D n`, the map `g = cayley ∘ Ψ ∘ ofℂ` agrees with the
composition of the (holomorphic) chart expression with `devH (· - n)`. -/
theorem eventuallyEq_chart (D : FatouData)
    (Φ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ unitDisc) (n : ℤ) {z : ℂ}
    (hz : D.ofℂ z ∈ D.chartSource n) :
    (fun z : ℂ => (Φ (D.ofℂ z) : ℂ)) =ᶠ[𝓝 z]
      fun w => (Φ ((D.chart n).symm (D.devH (w - (n : ℂ)))) : ℂ) := by
  filter_upwards [(isOpen_chartSource D n).mem_nhds hz] with w hw
  have hws : D.ofℂ w ∈ (D.chart n).source := by rwa [D.chart_source]
  show (Φ (D.ofℂ w) : ℂ) = (Φ ((D.chart n).symm (D.devH (w - (n : ℂ)))) : ℂ)
  rw [← D.chart_apply_ofℂ n w, (D.chart n).left_inv hws]

/-- `g = cayley ∘ Ψ ∘ ofℂ` is `C¹` on the plane: locally it is a holomorphic function of
`devH (· - n)`, and these local expressions cover the plane. -/
theorem contDiff_g (D : FatouData)
    (Φ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ unitDisc) :
    ContDiff ℝ 1 (fun z : ℂ => (Φ (D.ofℂ z) : ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hz : D.ofℂ z ∈ D.chartSource ⌊z.re⌋ := ofℂ_mem_chartSource_floor D z
  have hu : D.devH (z - ((⌊z.re⌋ : ℤ) : ℂ)) ∈ (D.chart ⌊z.re⌋).target := by
    rw [← D.chart_apply_ofℂ ⌊z.re⌋ z]
    exact (D.chart ⌊z.re⌋).map_source (by rw [D.chart_source]; exact hz)
  have hF : ContDiffAt ℝ 1 (fun w : ℂ => (Φ ((D.chart ⌊z.re⌋).symm w) : ℂ))
      (D.devH (z - ((⌊z.re⌋ : ℤ) : ℂ))) :=
    ((contDiffOn_chart_symm D Φ ⌊z.re⌋).contDiffAt
      ((D.chart ⌊z.re⌋).open_target.mem_nhds hu)).restrict_scalars ℝ
  have hshift : ContDiffAt ℝ 1 (fun w : ℂ => D.devH (w - ((⌊z.re⌋ : ℤ) : ℂ))) z :=
    (D.devB.contDiff.contDiffAt).comp z
      (contDiffAt_id.sub ((contDiff_const (c := ((⌊z.re⌋ : ℤ) : ℂ))).contDiffAt (x := z)))
  have hgoal : ContDiffAt ℝ 1 (fun w : ℂ => (Φ ((D.chart ⌊z.re⌋).symm
      (D.devH (w - ((⌊z.re⌋ : ℤ) : ℂ)))) : ℂ)) z :=
    ContDiffAt.comp (g := fun v : ℂ => (Φ ((D.chart ⌊z.re⌋).symm v) : ℂ))
      (f := fun w : ℂ => D.devH (w - ((⌊z.re⌋ : ℤ) : ℂ))) z hF hshift
  exact hgoal.congr_of_eventuallyEq (eventuallyEq_chart D Φ ⌊z.re⌋ hz)

/-- `g = cayley ∘ Ψ ∘ ofℂ` is injective. -/
theorem injective_g (D : FatouData)
    (Φ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ unitDisc) :
    Function.Injective (fun z : ℂ => (Φ (D.ofℂ z) : ℂ)) := by
  intro z₁ z₂ h
  have h1 : Φ (D.ofℂ z₁) = Φ (D.ofℂ z₂) := Subtype.ext h
  exact D.ofℂ_toℂ z₁ ▸ D.ofℂ_toℂ z₂ ▸ congrArg D.toℂ (Φ.injective h1)

/-- `g = cayley ∘ Ψ ∘ ofℂ` is bounded by `1`. -/
theorem norm_g_le (D : FatouData)
    (Φ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ unitDisc) (z : ℂ) :
    ‖(Φ (D.ofℂ z) : ℂ)‖ ≤ 1 := by
  have h : (Φ (D.ofℂ z) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := (Φ (D.ofℂ z)).2
  rw [Metric.mem_ball, dist_zero_right] at h
  exact le_of_lt h

/-- The Wirtinger bounds for `g = cayley ∘ Ψ ∘ ofℂ`: `∂g ≠ 0` and `|∂̄g| ≤ (1/15)|∂g|` pointwise.
The chain rule `∂(F ∘ h) = F'(h)·∂h` with `F` holomorphic and `h = devH (· - n)` (whose dilatation
is at most `1/30 < 1/15`) gives this, since `F' ≠ 0`. -/
theorem dz_dzbar_g (D : FatouData)
    (Φ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ unitDisc) (z : ℂ) :
    MandelDim.dz (fun z : ℂ => (Φ (D.ofℂ z) : ℂ)) z ≠ 0 ∧
      ‖MandelDim.dzbar (fun z : ℂ => (Φ (D.ofℂ z) : ℂ)) z‖ ≤
        (1 / 15) * ‖MandelDim.dz (fun z : ℂ => (Φ (D.ofℂ z) : ℂ)) z‖ := by
  have hz : D.ofℂ z ∈ D.chartSource ⌊z.re⌋ := ofℂ_mem_chartSource_floor D z
  have hu : D.devH (z - ((⌊z.re⌋ : ℤ) : ℂ)) ∈ (D.chart ⌊z.re⌋).target := by
    rw [← D.chart_apply_ofℂ ⌊z.re⌋ z]
    exact (D.chart ⌊z.re⌋).map_source (by rw [D.chart_source]; exact hz)
  have hF : DifferentiableAt ℂ (fun w : ℂ => (Φ ((D.chart ⌊z.re⌋).symm w) : ℂ))
      (D.devH (z - ((⌊z.re⌋ : ℤ) : ℂ))) :=
    (analyticAt_chart_symm D Φ ⌊z.re⌋ hu).differentiableAt
  have hF' : deriv (fun w : ℂ => (Φ ((D.chart ⌊z.re⌋).symm w) : ℂ))
      (D.devH (z - ((⌊z.re⌋ : ℤ) : ℂ))) ≠ 0 := deriv_chart_symm_ne_zero D Φ ⌊z.re⌋ hu
  have hh : DifferentiableAt ℝ (fun w : ℂ => D.devH (w - ((⌊z.re⌋ : ℤ) : ℂ))) z :=
    (D.devB.contDiff.differentiable_one.differentiableAt).comp z
      (differentiableAt_id.sub_const ((⌊z.re⌋ : ℤ) : ℂ))
  have hcomp := Wirtinger.dz_dzbar_comp (f := fun w : ℂ => (Φ ((D.chart ⌊z.re⌋).symm w) : ℂ))
    (h := fun w : ℂ => D.devH (w - ((⌊z.re⌋ : ℤ) : ℂ))) hF hh
  have hsub := Wirtinger.dz_dzbar_sub_const D.devH ((⌊z.re⌋ : ℤ) : ℂ) z
  have hE := eventuallyEq_chart D Φ ⌊z.re⌋ hz
  have hdz : MandelDim.dz (fun z : ℂ => (Φ (D.ofℂ z) : ℂ)) z
      = deriv (fun w : ℂ => (Φ ((D.chart ⌊z.re⌋).symm w) : ℂ))
          (D.devH (z - ((⌊z.re⌋ : ℤ) : ℂ))) *
        MandelDim.dz D.devH (z - ((⌊z.re⌋ : ℤ) : ℂ)) := by
    rw [show MandelDim.dz (fun z : ℂ => (Φ (D.ofℂ z) : ℂ)) z
        = MandelDim.dz ((fun w : ℂ => (Φ ((D.chart ⌊z.re⌋).symm w) : ℂ)) ∘
            fun w : ℂ => D.devH (w - ((⌊z.re⌋ : ℤ) : ℂ))) z from by
      simp only [MandelDim.dz, hE.fderiv_eq, Function.comp_def]]
    rw [hcomp.1, hsub.1]
  have hdzbar : MandelDim.dzbar (fun z : ℂ => (Φ (D.ofℂ z) : ℂ)) z
      = deriv (fun w : ℂ => (Φ ((D.chart ⌊z.re⌋).symm w) : ℂ))
          (D.devH (z - ((⌊z.re⌋ : ℤ) : ℂ))) *
        MandelDim.dzbar D.devH (z - ((⌊z.re⌋ : ℤ) : ℂ)) := by
    rw [show MandelDim.dzbar (fun z : ℂ => (Φ (D.ofℂ z) : ℂ)) z
        = MandelDim.dzbar ((fun w : ℂ => (Φ ((D.chart ⌊z.re⌋).symm w) : ℂ)) ∘
            fun w : ℂ => D.devH (w - ((⌊z.re⌋ : ℤ) : ℂ))) z from by
      simp only [MandelDim.dzbar, hE.fderiv_eq, Function.comp_def]]
    rw [hcomp.2, hsub.2]
  have hdev := devH_wirtinger D
  constructor
  · rw [hdz]; exact mul_ne_zero hF' (hdev.2.1 _)
  · rw [hdzbar, hdz, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hdev.2.2 _) (norm_nonneg _) |>.trans_eq (by ring)

/-- **The upper half-plane case of uniformization is impossible for `XF`.**
If `MandelDim.QCLiouville` holds (a bounded injective `C¹` map of the plane with bounded dilatation
`< 1` cannot exist), then there is no biholomorphism from the surface `XF D` (defined in
`Submission/Work/Fatou/Surface/Core.lean`) onto the upper half-plane.  The proof composes such a
biholomorphism with the (bounded) Cayley map `𝓗 → ℂ`, reads the result in the charts
`chart D n` of `XF D = ℂ` (where it becomes `G ∘ devH (· - n)` with `G` holomorphic and injective),
and uses the Wirtinger bounds `|∂ devH - 1| ≤ 1/16`, `|∂̄ devH| ≤ 1/32` (from
`Work.Fatou.devH_deriv`, note `1/32 ≤ (1/15)·(15/16)`) to get `|∂̄| ≤ (1/15) |∂|` and `∂ ≠ 0`. -/
theorem noHalfPlane (hQC : MandelDim.QCLiouville) (D : Work.Fatou.FatouData) :
    ¬ Nonempty (D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) := by
  rintro ⟨Ψ⟩
  obtain ⟨e⟩ := Commons.Analysis.Complex.UpperHalfPlane.halfPlane_disc_diffeomorph
  let Φ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ unitDisc := Ψ.trans e
  exact hQC (fun z : ℂ => (Φ (D.ofℂ z) : ℂ)) (1 / 15) 1 (by norm_num)
    (contDiff_g D Φ) (injective_g D Φ) (fun z => (dz_dzbar_g D Φ z).1)
    (fun z => (dz_dzbar_g D Φ z).2) (fun z => norm_g_le D Φ z)

end

end Work.Fatou.Surface
