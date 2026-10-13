/-
# The mixed iterates of the model defect `E₂` split over `E2smooth` and `E2gamma`

The model of the `D_z`-commutator defect is by definition the sum

  `E2model α f = E2smooth f + E2gamma α f`,

and the operator `D_z^j D_θ^i` is a composition of derivatives, hence additive on
`(z,θ)`-functions that are smooth on an open neighbourhood of the point.  The two summands
are smooth on the open quadrant `(0,∞) × (0,π/2)`:

* `E2smooth f` is smooth (analytic) on the box `E2box = (-1,∞) × (-1,π/2+1)`
  (`contDiffOn_uncurry_E2smooth`), hence on the quadrant;
* `E2gamma α f = (Gfun f / c α)·Γ(θ)` separates into a radial analytic factor
  `Gfun f / c α` on `(0,∞)` and an angular analytic factor `Γ(θ)` on `(0,π/2)`.

The radial factor needs the analyticity of the tail integral `L₁₂(f)` on `(0,∞)`.
This is *not* the hypothesis of `L12f_contDiffOn`, which asks for integrability of the
`L₁₂`-density on all of `(0,∞)` (false in general: the density behaves like `1/s` near
`s = 0`); it is instead the observation of `L12f_contDiffOn_infty` that either the density
is integrable on one tail `(z₁,∞)`, `z₁ > 0` — and then `L₁₂(f)` is a genuine tail integral
of an analytic density, hence analytic — or the density is integrable on no tail, and then
`L₁₂(f)` vanishes identically.  The lemma `L12f_contDiffOn_nohint` records this.

The main statement is then a three-line assembly: apply additivity of `mixed` on the open
quadrant to the two summands.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Coercivity.E2Slice.E2SliceDefs
import Submission.Work.Coercivity.CommutZQuadQDerivLike
import Submission.Work.Coercivity.F1F2_smooth
import Submission.Work.Coercivity.L12f_contDiffOn_infty
import Submission.Work.Coercivity.CommutZ_Frad_smooth
import Submission.Work.Coercivity.HkIntegrand_EcommT_le_Bound
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.DzIterSmoothOn
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.DerivLikeBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity.E2Mixed

set_option autoImplicit false

/-! ## The open quadrant -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def E2mixQuad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_E2mixQuad : IsOpen E2mixQuad := isOpen_Ioi.prod isOpen_Ioo

theorem E2mixQuad_subset_E2box : E2mixQuad ⊆ E2box := by
  rintro ⟨z, θ⟩ hp
  have hz : 0 < z := hp.1
  have hθ1 : 0 < θ := hp.2.1
  have hθ2 : θ < π / 2 := hp.2.2
  refine ⟨?_, ?_, ?_⟩
  · show -1 < z
    linarith
  · show -1 < θ
    linarith
  · show θ < π / 2 + 1
    linarith [Real.pi_pos]

/-! ## Analyticity of the tail integral `L₁₂(f)` without an integrability hypothesis -/

/-- **The tail integral `L₁₂(f)` is analytic on `(0,∞)`** for `f` smooth on a neighbourhood
of the closed quadrant, with *no* integrability hypothesis on the `L₁₂`-density.

If the density is integrable on one tail `(z₁,∞)` with `z₁ > 0`, then, being continuous on
`(0,∞)`, it is integrable on every tail `(z,∞)` with `z > 0`; at a point `z₀ > 0` the tail
integral is then, near `z₀`, the constant `∫_{(z₀,∞)}` minus the analytic primitive
`z ↦ ∫_{z₀}^{z}`, hence analytic.  Otherwise the density is integrable on no tail and the
Bochner integral is the junk value `0`, so `L₁₂(f)` vanishes identically on `(0,∞)`. -/
theorem L12f_contDiffOn_nohint (g : ℝ → ℝ → ℝ) (hg : Spaces.SmoothNbhd g) :
    ContDiffOn ℝ ⊤ (L12f g) (Set.Ioi 0) := by
  have hd : ContDiffOn ℝ ⊤ (fun s => FM.L12dens Spaces.K g s) (Set.Ioi 0) :=
    L12dens_contDiffOn g hg
  have hd_an : AnalyticOn ℝ (fun s => FM.L12dens Spaces.K g s) (Set.Ioi 0) :=
    (contDiffOn_omega_iff_analyticOn isOpen_Ioi.uniqueDiffOn).mp hd
  have hd_cont : ContinuousOn (fun s => FM.L12dens Spaces.K g s) (Set.Ioi 0) := hd.continuousOn
  have heq : L12f g = fun z => ∫ s in Set.Ioi z, FM.L12dens Spaces.K g s := rfl
  rw [heq]
  refine (contDiffOn_omega_iff_analyticOn isOpen_Ioi.uniqueDiffOn).mpr ?_
  rw [isOpen_Ioi.analyticOn_iff_analyticOnNhd]
  intro z₀ hz₀
  by_cases hcase : ∃ z ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun s => FM.L12dens Spaces.K g s) (Set.Ioi z)
  · obtain ⟨z₁, hz₁, hint₁⟩ := hcase
    have hall : ∀ z ∈ Set.Ioi (0 : ℝ),
        IntegrableOn (fun s => FM.L12dens Spaces.K g s) (Set.Ioi z) :=
      integrableOn_Ioi_of_integrableOn_Ioi hd_cont hint₁
    have hAw : AnalyticAt ℝ (fun s => FM.L12dens Spaces.K g s) z₀ :=
      hd_an.analyticAt (isOpen_Ioi.mem_nhds hz₀)
    have hprim : AnalyticAt ℝ (fun z => ∫ s in z₀..z, FM.L12dens Spaces.K g s) z₀ :=
      primitive_analyticAt _ z₀ hAw
    have hconst : AnalyticAt ℝ
        (fun _ : ℝ => ∫ s in Set.Ioi z₀, FM.L12dens Spaces.K g s) z₀ :=
      analyticAt_const
    refine (analyticAt_congr ?_).mpr (hconst.sub hprim)
    filter_upwards [isOpen_Ioi.mem_nhds hz₀] with z hz
    have hin0 : IntegrableOn (fun s => FM.L12dens Spaces.K g s) (Set.Ioi z₀) := hall z₀ hz₀
    have hinz : IntegrableOn (fun s => FM.L12dens Spaces.K g s) (Set.Ioi z) := hall z hz
    have hid := intervalIntegral.integral_Ioi_sub_Ioi' (a := z₀) (b := z) hin0 hinz
    show (∫ s in Set.Ioi z, FM.L12dens Spaces.K g s)
        = (∫ s in Set.Ioi z₀, FM.L12dens Spaces.K g s)
          - ∫ s in z₀..z, FM.L12dens Spaces.K g s
    linarith [hid]
  · push_neg at hcase
    have hzero : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) z₀ := analyticAt_const
    refine (analyticAt_congr ?_).mpr hzero
    filter_upwards [isOpen_Ioi.mem_nhds hz₀] with z hz
    show (∫ s in Set.Ioi z, FM.L12dens Spaces.K g s) = 0
    exact integral_undef (hcase z hz)

/-! ## Analyticity of the radial factor `Gfun f / c α` -/

/-- The radial factor `Gfun f / c α` of the `Γ`-piece is analytic on `(0,∞)`: it is a
combination of the analytic rational profiles `cfac`, `zdq`, `qfun` with `L₁₂(f)`, and
division by the non-zero constant `c α` preserves analyticity (for `c α = 0` the function
is identically zero, and Lean's totalised division makes this automatic). -/
theorem Gfun_div_const_contDiffOn (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : Spaces.SmoothNbhd f) :
    ContDiffOn ℝ ⊤ (fun z => CommutZ.Gfun f z / Spaces.c α) (Set.Ioi 0) := by
  have hL : ContDiffOn ℝ ⊤ (fun z => L12f f z) (Set.Ioi 0) := L12f_contDiffOn_nohint f hf
  have hG : ContDiffOn ℝ ⊤ (CommutZ.Gfun f) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ ⊤ (fun z => CommutZ.cfac z * L12f f z) (Set.Ioi 0) :=
      CommutZ.cfac_contDiffOn.mul hL
    have h2 : ContDiffOn ℝ ⊤ (fun z => CommutZ.zdq z * CommutZ.Lam1 f) (Set.Ioi 0) :=
      CommutZ.zdq_contDiffOn.mul contDiffOn_const
    have h3 : ContDiffOn ℝ ⊤ (fun z => CommutZ.qfun z * CommutZ.Lam2 f) (Set.Ioi 0) :=
      CommutZ.qfun_contDiffOn.mul contDiffOn_const
    show ContDiffOn ℝ ⊤ (fun z => CommutZ.cfac z * L12f f z + CommutZ.zdq z * CommutZ.Lam1 f
      - CommutZ.qfun z * CommutZ.Lam2 f) (Set.Ioi 0)
    exact (h1.add h2).sub h3
  exact ContDiffOn.div_const hG _

/-- **The `Γ`-piece is analytic on the open quadrant**: it is the product of the radial
factor `Gfun f / c α` and the angular factor `Γ`. -/
theorem E2gamma_contDiffOn (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : Spaces.SmoothNbhd f) :
    ContDiffOn ℝ ⊤ (Function.uncurry (E2gamma α f)) E2mixQuad := by
  have hG : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => CommutZ.Gfun f p.1 / Spaces.c α) E2mixQuad :=
    (Gfun_div_const_contDiffOn α f hf).comp contDiffOn_fst (fun p hp => hp.1)
  have hGam : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Spaces.Gam α p.2) E2mixQuad :=
    (contDiffOn_Gam α).comp contDiffOn_snd (fun p hp => hp.2)
  refine (hG.mul hGam).congr (fun p hp => ?_)
  rfl

/-- The smooth part is analytic on the quadrant. -/
theorem E2smooth_contDiffOn (f : ℝ → ℝ → ℝ) (hf : Spaces.SmoothNbhd f) :
    ContDiffOn ℝ ⊤ (Function.uncurry (E2smooth f)) E2mixQuad :=
  (contDiffOn_uncurry_E2smooth f hf).mono E2mixQuad_subset_E2box

/-! ## The iterated operators on an open set

`D_z` and `D_θ` are local, deriv-based, hence linear operators on functions smooth on an
open set.  Everything below is stated for an arbitrary open `V`; the case at hand is the
quadrant `E2mixQuad`. -/

/-- The `z`-slices of a function smooth on an open set are differentiable. -/
theorem slice_diffAt_fst_of_contDiffOn {F : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) V) {z θ : ℝ} (h : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun z' => F z' θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry F) (z, θ) :=
    (hF.differentiableOn (by simp)).differentiableAt (hV.mem_nhds h)
  change DifferentiableAt ℝ (Function.uncurry F ∘ fun z' : ℝ => (z', θ)) z
  exact hd.comp z (hasFDerivAt_prodMk_left z θ).differentiableAt

/-- The `θ`-slices of a function smooth on an open set are differentiable. -/
theorem slice_diffAt_snd_of_contDiffOn {F : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) V) {z θ : ℝ} (h : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun θ' => F z θ') θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry F) (z, θ) :=
    (hF.differentiableOn (by simp)).differentiableAt (hV.mem_nhds h)
  change DifferentiableAt ℝ (Function.uncurry F ∘ fun θ' : ℝ => (z, θ')) θ
  exact hd.comp θ (hasFDerivAt_prodMk_right z θ).differentiableAt

/-- `D_θ` preserves smoothness on an open set. -/
theorem contDiffOn_uncurry_Dth_of_isOpen {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.Dth G)) V := by
  have hpth : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.pth G)) V :=
    Spaces.contDiffOn_uncurry_pth hV h
  have hsin : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  refine (hsin.mul hpth).congr (fun p hp => ?_)
  rfl

/-- Every iterate of `D_θ` preserves smoothness on an open set. -/
theorem DthIter_smoothOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (i : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.DthIter i G)) V := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      rw [Spaces.DthIter_succ]
      exact contDiffOn_uncurry_Dth_of_isOpen hV ih

/-- Two functions agreeing on an open set have the same `D_z`-iterates there. -/
theorem DzIter_congr_of_isOpen {F G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Spaces.DzIter j F))
      (Function.uncurry (Spaces.DzIter j G)) V := by
  induction j with
  | zero => exact h
  | succ n ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      show z * deriv (fun z' => Spaces.DzIter n F z' θ) z
        = z * deriv (fun z' => Spaces.DzIter n G z' θ) z
      congr 1
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [(Continuous.prodMk_left θ).continuousAt.eventually
        (hV.mem_nhds hy)] with z' hz'
      exact ih hz'

/-- Two functions agreeing on an open set have the same `D_θ`-iterates there. -/
theorem DthIter_congr_of_isOpen {F G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Spaces.DthIter i F))
      (Function.uncurry (Spaces.DthIter i G)) V := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      show Real.sin (2 * θ) * deriv (fun θ' => Spaces.DthIter n F z θ') θ
        = Real.sin (2 * θ) * deriv (fun θ' => Spaces.DthIter n G z θ') θ
      congr 1
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [(Continuous.prodMk_right z).continuousAt.eventually
        (hV.mem_nhds hy)] with θ' hθ'
      exact ih hθ'

/-- `D_z`-iterates are additive on functions smooth on an open set. -/
theorem DzIter_add_of_isOpen {F G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) V)
    (hG : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Spaces.DzIter j (F + G)))
      (Function.uncurry (Spaces.DzIter j F + Spaces.DzIter j G)) V := by
  induction j with
  | zero => intro y hy; rfl
  | succ n ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      have heq : (fun z' => Spaces.DzIter n (F + G) z' θ) =ᶠ[𝓝 z]
          (fun z' => Spaces.DzIter n F z' θ + Spaces.DzIter n G z' θ) := by
        filter_upwards [(Continuous.prodMk_left θ).continuousAt.eventually
          (hV.mem_nhds hy)] with z' hz'
        exact ih hz'
      have h1 : DifferentiableAt ℝ (fun z' => Spaces.DzIter n F z' θ) z :=
        slice_diffAt_fst_of_contDiffOn hV (Spaces.DzIterSmoothOn hV hF n) hy
      have h2 : DifferentiableAt ℝ (fun z' => Spaces.DzIter n G z' θ) z :=
        slice_diffAt_fst_of_contDiffOn hV (Spaces.DzIterSmoothOn hV hG n) hy
      have hderiv : deriv (fun z' => Spaces.DzIter n (F + G) z' θ) z
          = deriv (fun z' => Spaces.DzIter n F z' θ) z
            + deriv (fun z' => Spaces.DzIter n G z' θ) z := by
        rw [heq.deriv_eq]
        exact deriv_add h1 h2
      show z * deriv (fun z' => Spaces.DzIter n (F + G) z' θ) z
          = z * deriv (fun z' => Spaces.DzIter n F z' θ) z
            + z * deriv (fun z' => Spaces.DzIter n G z' θ) z
      rw [hderiv]; ring

/-- `D_θ`-iterates are additive on functions smooth on an open set. -/
theorem DthIter_add_of_isOpen {F G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) V)
    (hG : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Spaces.DthIter i (F + G)))
      (Function.uncurry (Spaces.DthIter i F + Spaces.DthIter i G)) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ n ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      have heq : (fun θ' => Spaces.DthIter n (F + G) z θ') =ᶠ[𝓝 θ]
          (fun θ' => Spaces.DthIter n F z θ' + Spaces.DthIter n G z θ') := by
        filter_upwards [(Continuous.prodMk_right z).continuousAt.eventually
          (hV.mem_nhds hy)] with θ' hθ'
        exact ih hθ'
      have h1 : DifferentiableAt ℝ (fun θ' => Spaces.DthIter n F z θ') θ :=
        slice_diffAt_snd_of_contDiffOn hV (DthIter_smoothOn hV hF n) hy
      have h2 : DifferentiableAt ℝ (fun θ' => Spaces.DthIter n G z θ') θ :=
        slice_diffAt_snd_of_contDiffOn hV (DthIter_smoothOn hV hG n) hy
      have hderiv : deriv (fun θ' => Spaces.DthIter n (F + G) z θ') θ
          = deriv (fun θ' => Spaces.DthIter n F z θ') θ
            + deriv (fun θ' => Spaces.DthIter n G z θ') θ := by
        rw [heq.deriv_eq]
        exact deriv_add h1 h2
      show Real.sin (2 * θ) * deriv (fun θ' => Spaces.DthIter n (F + G) z θ') θ
          = Real.sin (2 * θ) * deriv (fun θ' => Spaces.DthIter n F z θ') θ
            + Real.sin (2 * θ) * deriv (fun θ' => Spaces.DthIter n G z θ') θ
      rw [hderiv]; ring

/-- **The mixed iterates are additive on functions smooth on an open set.** -/
theorem mixed_add_of_isOpen {F G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) V)
    (hG : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (j i : ℕ) :
    Set.EqOn (Function.uncurry (Spaces.mixed j i (F + G)))
      (Function.uncurry (Spaces.mixed j i F + Spaces.mixed j i G)) V := by
  have hDth := DthIter_add_of_isOpen hV hF hG i
  have hDthF : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.DthIter i F)) V :=
    DthIter_smoothOn hV hF i
  have hDthG : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.DthIter i G)) V :=
    DthIter_smoothOn hV hG i
  have hDz := DzIter_add_of_isOpen hV hDthF hDthG j
  intro y hy
  obtain ⟨z, θ⟩ := y
  show Spaces.mixed j i (F + G) z θ = Spaces.mixed j i F z θ + Spaces.mixed j i G z θ
  exact (DzIter_congr_of_isOpen hV hDth j hy).trans (hDz hy)

/-! ## The split of the model -/

theorem E2model_mixed_split (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : Work.Spaces.SmoothNbhd f) (j i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (Work.Coercivity.E2model α f) z θ
        = Work.Spaces.mixed j i (Work.Coercivity.E2smooth f) z θ
          + Work.Spaces.mixed j i (Work.Coercivity.E2gamma α f) z θ := by
  intro z θ hz hθ hθ2
  have hadd := mixed_add_of_isOpen isOpen_E2mixQuad (E2smooth_contDiffOn f hf)
    (E2gamma_contDiffOn α f hf) j i (show (z, θ) ∈ E2mixQuad from ⟨hz, hθ, hθ2⟩)
  rw [show E2model α f = E2smooth f + E2gamma α f from rfl]
  simpa only [Function.uncurry, Pi.add_apply] using hadd

end Work.Coercivity.E2Mixed
