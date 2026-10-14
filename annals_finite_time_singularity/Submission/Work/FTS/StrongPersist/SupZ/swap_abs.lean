import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.DzRIter_L12f =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `D_z`-iterates of `L₁₂^K(g)` and their `θ`-coercivity

This module proves `Work.Coercivity.DzRIter_L12f`.  With `D_z = z ∂_z` acting on functions of
`z` alone (`Work.Coercivity.CT.DzRIter`), the *index-raising* identity
`D_z^k L₁₂^K(g) = - ∫_θ K(θ) (D_z^{k-1} g)(·,θ) dθ` holds for every `k ≥ 1`; squaring it and
applying Cauchy–Schwarz in `θ` against the weight `K` gives
`(D_z^k L₁₂^K(g))² ≤ 3 ∫_θ (D_z^{k-1} g)²`.

The identity is the general-`k` form of `Work.Elliptic.L12Iterate` (which states it for
`k ≤ 4`, the range needed by the elliptic estimate `L12H`): the angular moments
`Q_j(z) = ∫_θ K(θ)(D_z^j g)(z,θ)dθ` satisfy `Q_{j+1} = z ∂_z Q_j`
(`Work.Elliptic.Qang_deriv_mul`, proved by differentiating under the `θ`-integral), so the
recursion is formalised here once and for all and then transported to the `Work.Coercivity`
vocabulary through the relabelling bridges `L12f g = Elliptic.L12 g` and
`CT.DzRIter = Elliptic.DzdIter` (both `rfl`).
-/

namespace Work.Coercivity

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Bridges to the `Work.Elliptic` vocabulary -/



/-- The angular moment `Elliptic.Qang g j z` is the `θ`-integral against `Spaces.K`. -/
theorem DzRIter_L12f_bridge_Qang (g : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Work.Elliptic.Qang g j z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter j g z θ := by
  rw [Work.Elliptic.Qang]
  exact setIntegral_congr_fun measurableSet_Icc
    (fun θ _ => by rw [Work.Elliptic.Ktheta_eq_K])

/-! ## The general index-raising recursion -/



/-! ## The theorem -/


end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.E2Mixed.E2model_mixed_split =====
section

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




/-! ## Analyticity of the tail integral `L₁₂(f)` without an integrability hypothesis -/


/-! ## Analyticity of the radial factor `Gfun f / c α` -/




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


end Work.Coercivity.E2Mixed
end
end
-- ===== merged: Submission.Work.Coercivity.Gam_jet_upper_pi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular jet of `Γ` is `O((π/2 - θ)^{2α/3})` near `θ = π/2`

`Γ(θ) = (sin θ · cos²θ)^{α/3}` vanishes at `θ = π/2` like `(π/2 - θ)^{2α/3}`, and so do all
its `D_θ`-iterates, because on `(0, π/2)`

`D_θ^{j+1} Γ = α · Tfun j α · Γ`   (`Work.Coercivity.DthU_iter_Gam_all`)

and `sin θ cos²θ` is comparable with `(π/2 - θ)²` on `(π/2 - 1, π/2)`.  The factor
`Tfun j α` is smooth (hence bounded on the closed interval), which gives the claim for
arbitrary real `α` and every `j`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The comparison of `sin θ · cos²θ` with `(π/2 - θ)²` near `π/2` -/


/-! ## The `i = 0` case: `Γ` itself is `O((π/2 - θ)^{2α/3})` -/


/-! ## Assembly -/




end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.Gam_jet_upper_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- `D_θ`-iterates of a function of `θ` alone, viewed as a function of `(z,θ)`,
agree with the univariate iterates `Spaces.dthU^[i]`. -/
lemma DthIter_rad_eq (i : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Spaces.DthIter i (fun _ θ => g θ) z θ = Spaces.dthU^[i] g θ := by
  have h : (fun (_ : ℝ) (θ : ℝ) => g θ) = (fun (z : ℝ) (θ : ℝ) => g θ * (1 : ℝ)) := by
    funext z θ; ring
  rw [h, Spaces.DthIter_decomp]
  ring




end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.HardyWeight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false




end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.HkSq_succ_le_of_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false
-- the `HkMem` hypothesis on the left-hand side of `HkSq_le_sum_of_integrand_le` is part
-- of the natural statement (the left-hand side is an honest iterated integral) even
-- though the proof of that lemma uses only the hypotheses on the right-hand side
set_option linter.unusedVariables false

/-! ## Additivity of the iterated set integral -/

/-- The iterated set integral of a sum of three functions whose `θ`-slices and
`z`-integrals are all integrable is the sum of the three iterated integrals. -/
theorem setIntegral_iterated_add {s t : Set ℝ} (hs : MeasurableSet s) (u v w : ℝ → ℝ → ℝ)
    (hu : (∀ z ∈ s, IntegrableOn (fun θ => u z θ) t) ∧ IntegrableOn (fun z => ∫ θ in t, u z θ) s)
    (hv : (∀ z ∈ s, IntegrableOn (fun θ => v z θ) t) ∧ IntegrableOn (fun z => ∫ θ in t, v z θ) s)
    (hw : (∀ z ∈ s, IntegrableOn (fun θ => w z θ) t) ∧ IntegrableOn (fun z => ∫ θ in t, w z θ) s) :
    (∫ z in s, ∫ θ in t, (u z θ + v z θ + w z θ))
      = (∫ z in s, ∫ θ in t, u z θ) + (∫ z in s, ∫ θ in t, v z θ)
        + (∫ z in s, ∫ θ in t, w z θ) := by
  have hθ : ∀ z ∈ s, (∫ θ in t, (u z θ + v z θ + w z θ))
      = (∫ θ in t, u z θ) + (∫ θ in t, v z θ) + (∫ θ in t, w z θ) := by
    intro z hz
    rw [integral_add (f := fun θ => u z θ + v z θ) (g := fun θ => w z θ)
      ((hu.1 z hz).add (hv.1 z hz)) (hw.1 z hz)]
    rw [integral_add (hu.1 z hz) (hv.1 z hz)]
  rw [integral_congr_ae (ae_restrict_of_forall_mem hs (fun z hz => hθ z hz))]
  rw [integral_add (f := fun z => (∫ θ in t, u z θ) + (∫ θ in t, v z θ))
    (g := fun z => ∫ θ in t, w z θ) (hu.2.add hv.2) hw.2]
  rw [integral_add hu.2 hv.2]

/-! ## From a pointwise bound of the integrands to a bound of the squared norms -/

/-- **Integration step.**  If the `H^m`-integrand of `f` is pointwise dominated on the
closed quadrant by the sum of the `H^k`-integrands of `g₁, g₂, g₃`, and these four
functions have honest iterated integrals at the levels `m`, resp. `k`, then the
corresponding inequality holds for the squared norms. -/
theorem HkSq_le_sum_of_integrand_le (α : ℝ) (m k : ℕ) {f g₁ g₂ g₃ : ℝ → ℝ → ℝ}
    (h₁ : Spaces.HkMem α m f) (h₂ : Spaces.HkMem α k g₁) (h₃ : Spaces.HkMem α k g₂)
    (h₄ : Spaces.HkMem α k g₃)
    (hle : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ,
      Spaces.HkIntegrand α m f z θ
        ≤ Spaces.HkIntegrand α k g₁ z θ + Spaces.HkIntegrand α k g₂ z θ
          + Spaces.HkIntegrand α k g₃ z θ) :
    Spaces.HkSq α m f ≤ Spaces.HkSq α k g₁ + Spaces.HkSq α k g₂ + Spaces.HkSq α k g₃ := by
  have hIz : MeasurableSet Spaces.Iz := measurableSet_Ici
  have hIθ : MeasurableSet Spaces.Iθ := measurableSet_Icc
  -- the `z`-integral of the summed integrand is integrable: it agrees a.e. with the sum
  -- of the three `z`-integrals, which is integrable by the `HkMem` hypotheses
  have hae : (fun z => ∫ θ in Spaces.Iθ, (Spaces.HkIntegrand α k g₁ z θ
        + Spaces.HkIntegrand α k g₂ z θ + Spaces.HkIntegrand α k g₃ z θ))
      =ᵐ[volume.restrict Spaces.Iz]
      (fun z => (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g₁ z θ)
        + (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g₂ z θ)
        + (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g₃ z θ)) := by
    refine ae_restrict_of_forall_mem hIz fun z hz => ?_
    show (∫ θ in Spaces.Iθ, (Spaces.HkIntegrand α k g₁ z θ + Spaces.HkIntegrand α k g₂ z θ
          + Spaces.HkIntegrand α k g₃ z θ))
      = (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g₁ z θ)
        + (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g₂ z θ)
        + (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g₃ z θ)
    rw [integral_add (f := fun θ => Spaces.HkIntegrand α k g₁ z θ
          + Spaces.HkIntegrand α k g₂ z θ) (g := fun θ => Spaces.HkIntegrand α k g₃ z θ)
        ((h₂.1 z hz).add (h₃.1 z hz)) (h₄.1 z hz)]
    rw [integral_add (h₂.1 z hz) (h₃.1 z hz)]
  have hintsum : Integrable (fun z => ∫ θ in Spaces.Iθ, (Spaces.HkIntegrand α k g₁ z θ
        + Spaces.HkIntegrand α k g₂ z θ + Spaces.HkIntegrand α k g₃ z θ))
      (volume.restrict Spaces.Iz) :=
    ((h₂.2.add h₃.2).add h₄.2).congr hae.symm
  -- the pointwise bound of the integrands integrates to a bound of the iterated integrals
  have hbound : (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α m f z θ)
      ≤ ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (Spaces.HkIntegrand α k g₁ z θ
          + Spaces.HkIntegrand α k g₂ z θ + Spaces.HkIntegrand α k g₃ z θ) := by
    refine integral_mono_of_nonneg ?_ hintsum ?_
    · exact ae_restrict_of_forall_mem hIz (fun z _ =>
        integral_nonneg (fun θ => Spaces.HkIntegrand_nonneg α m f z θ))
    · exact ae_restrict_of_forall_mem hIz (fun z hz =>
        integral_mono_of_nonneg
          (ae_restrict_of_forall_mem hIθ (fun θ _ => Spaces.HkIntegrand_nonneg α m f z θ))
          (((h₂.1 z hz).add (h₃.1 z hz)).add (h₄.1 z hz))
          (ae_restrict_of_forall_mem hIθ (fun θ hθ => hle z hz θ hθ)))
  calc Spaces.HkSq α m f
      = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α m f z θ := rfl
    _ ≤ ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (Spaces.HkIntegrand α k g₁ z θ
          + Spaces.HkIntegrand α k g₂ z θ + Spaces.HkIntegrand α k g₃ z θ) := hbound
    _ = Spaces.HkSq α k g₁ + Spaces.HkSq α k g₂ + Spaces.HkSq α k g₃ := by
        rw [setIntegral_iterated_add hIz (fun z θ => Spaces.HkIntegrand α k g₁ z θ)
          (fun z θ => Spaces.HkIntegrand α k g₂ z θ)
          (fun z θ => Spaces.HkIntegrand α k g₃ z θ) ⟨h₂.1, h₂.2⟩ ⟨h₃.1, h₃.2⟩ ⟨h₄.1, h₄.2⟩]
        rfl

/-! ## The target lemma -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.KC_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false



/-- The angular factor dual to `DthWt` in the `KC0` estimate:
`v₀ = 3 K(θ) · z/(1+z)³ · sin(2θ)^{γ/2}`. -/
abbrev Kv (α : ℝ) : ℝ × ℝ → ℝ :=
  fun p => 3 * Spaces.K p.2 * p.1 / (1 + p.1) ^ 3 * (Real.sin (2 * p.2)) ^ (Spaces.gam α / 2)


/-! ## Elementary angular and radial facts -/

private lemma continuous_K : Continuous Spaces.K := by
  unfold Spaces.K; fun_prop


/-- For `x ≥ 0`, the square of `x ^ (γ/2)` is `x ^ γ`. -/
private lemma rpow_half_sq_prv (x γ : ℝ) (hx : 0 ≤ x) : (x ^ (γ / 2)) ^ 2 = x ^ γ := by
  rw [← Real.rpow_natCast (x ^ (γ / 2)) 2]
  calc (x ^ (γ / 2)) ^ (2 : ℝ) = x ^ ((γ / 2) * 2) := (Real.rpow_mul hx (γ / 2) 2).symm
    _ = x ^ γ := by rw [show γ / 2 * 2 = γ by ring]







/-! ## The two pointwise identities -/



/-- For two reals, `|a·b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (1 / 2) * (a ^ 2 + b ^ 2) := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-! ## The radial factor `z/(1+z)³` -/




/-! ## The angular factors -/



/-- `volume Iθ` is finite. -/
private lemma volume_Iθ_ne_top : volume Spaces.Iθ ≠ ⊤ := by
  rw [Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top











/-! ## The `KC0`/`KC1` angular factors on the quadrant -/









/-! ## The energy is nonnegative -/


/-! ## The two halves of the estimate -/




end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.slice_Z16 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- **The `Z₁+Z₆` slice identity of the `D_z`-coercivity estimate (Elgindi, Annals 194 (3) 2021,
§"`L²` coercivity for `𝓛_Γ^T` with one `z`-derivative").**

Writing `g = D_z f` and `Weta = w²·sin(2θ)^{-η}`, the pointwise identity
`𝓛(g)·w = g·w + z∂_z(g·w)` (`L_mul_w_deriv`) gives, for every fixed `z > 0` and every `θ`,

  `L g · g · Weta = ½ g² · Weta + ½ ∂_z(z (g w)²) · sin(2θ)^{-η}`,

and the `θ`-integration by parts of `D_θ g · g · Weta` (`slice_ibp_eta`, whose boundary term
`sin(2θ)^{1-η} g²` vanishes because `η = 99/100 < 1`) gives

  `∫_θ D_θ g · g · Weta = (η-1) ∫_θ cos(2θ) g² · Weta`.

Since `Z16 = Z1 + Z6 = 𝓛(D_z f) - (3/(1+z)) D_θ(D_z f)`, adding `-(3/(1+z))` times the second
identity to the `θ`-integral of the first yields exactly the identity below. -/
theorem slice_Z16 (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    ∀ z, 0 < z → (∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ)
      = (1 / 2) * (∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ)
        + (1 / 2) * (∫ θ in Spaces.Iθ,
            deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
              * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        + (3 * (1 - Spaces.eta) / (1 + z))
            * (∫ θ in Spaces.Iθ, Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ) := by
  intro z hz
  have hg : Spaces.SmoothNbhd (Spaces.Dz f) := Work.Spaces.SmoothNbhd.Dz hsm
  have hIBP := slice_ibp_eta (Spaces.Dz f) hg hz
  have hBC := slice_Z16_integrable f hsm hz
  have hLmul : ∀ θ ∈ Spaces.Iθ, L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
      = (1 / 2) * (Spaces.Dz f z θ) ^ 2 * Weta z θ
        + (1 / 2) * deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
            * (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
    fun θ hθ => L_mul_self_Weta (Spaces.Dz f) hg hz hθ
  have hIA := hBC.1
  have hIB := hBC.2.1
  have hIX := hBC.2.2.1
  have hIY := hBC.2.2.2
  -- (1) the pointwise identity for the `𝓛(D_z f)` term, integrated over `θ`
  have hA_pt : ∀ θ ∈ Spaces.Iθ, L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
      = (1 / 2) * ((Spaces.Dz f z θ) ^ 2 * Weta z θ)
        + (1 / 2) * (deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
            * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
    intro θ hθ
    rw [hLmul θ hθ]; ring
  have hA_eq : ∫ θ in Spaces.Iθ, L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
      = (1 / 2) * (∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ)
        + (1 / 2) * (∫ θ in Spaces.Iθ,
            deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
              * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
    calc ∫ θ in Spaces.Iθ, L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
        = ∫ θ in Spaces.Iθ, ((1 / 2) * ((Spaces.Dz f z θ) ^ 2 * Weta z θ)
            + (1 / 2) * (deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
                * (Real.sin (2 * θ)) ^ (-Spaces.eta))) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Icc hA_pt
      _ = (1 / 2) * (∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ)
            + (1 / 2) * (∫ θ in Spaces.Iθ,
                deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
                  * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
          rw [MeasureTheory.integral_add (hIX.const_mul (1 / 2)) (hIY.const_mul (1 / 2)),
              MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- (2) the `θ`-integration by parts for the `Z₆` term
  have hB_eq : ∫ θ in Spaces.Iθ, Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
      = (Spaces.eta - 1)
          * ∫ θ in Spaces.Iθ, Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ := by
    have e1 : ∫ θ in Spaces.Iθ, Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
        = Spaces.w z ^ 2 * ∫ θ in Spaces.Iθ,
            Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ
              * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
      have h2 : ∫ θ in Spaces.Iθ, Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
          = ∫ θ in Spaces.Iθ, Spaces.w z ^ 2
              * (Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ
                  * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro θ hθ; simp only [Weta]; ring
      rw [h2, MeasureTheory.integral_const_mul]
    have e2 : ∫ θ in Spaces.Iθ, Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ
        = Spaces.w z ^ 2 * ∫ θ in Spaces.Iθ,
            Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
      have h2 : ∫ θ in Spaces.Iθ, Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ
          = ∫ θ in Spaces.Iθ, Spaces.w z ^ 2
              * (Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro θ hθ; simp only [Weta]; ring
      rw [h2, MeasureTheory.integral_const_mul]
    rw [e1, e2, hIBP]; ring
  -- (3) split the integrand of the left-hand side
  have hG_pt : ∀ θ ∈ Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ
      = L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
        + (-(3 / (1 + z)))
            * (Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ) := by
    intro θ hθ
    unfold Z16 Z1 Z6
    ring
  have hG_eq : ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ
      = (∫ θ in Spaces.Iθ, L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ)
        + (-(3 / (1 + z)))
            * (∫ θ in Spaces.Iθ, Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ) := by
    have h1 : ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ
        = ∫ θ in Spaces.Iθ, (L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
            + (-(3 / (1 + z)))
              * (Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ)) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc hG_pt
    rw [h1, MeasureTheory.integral_add (μ := MeasureTheory.volume.restrict Spaces.Iθ)
        hIA (hIB.const_mul (-(3 / (1 + z)))), MeasureTheory.integral_const_mul]
  rw [hG_eq, hA_eq, hB_eq]
  ring

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.theta_coercive =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The two integrands of the `D_θ`-coercivity estimate -/





/-! ## The `Aop` pairing is integrable on the quadrant -/


/-! ## Measurability of the energy integrand -/










/-! ## Bounds on the box for the two integrands of the one-dimensional by-parts lemmas -/

/-- `(w z)² · z⁴ = (1+z)⁴`. -/
theorem w_sq_mul_z4 (z : ℝ) (hz : z ≠ 0) : Spaces.w z ^ 2 * z ^ 4 = (1 + z) ^ 4 := by
  rw [Spaces.w, div_pow]
  field_simp



/-! ## The two limit ingredients of the coercivity estimate -/




/-! ## The final assembly (given the finite-box coercivity) -/



/-! ## Integrability of the joint energy integrand on a box -/











end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Construction.H6N_GammaTerm_rho_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.Construction

set_option autoImplicit false

/-! ## The fifth and sixth `D_z`-iterates of `ρ`

One step of `Zop` on the shape `w ↦ u w / (1+w)^m` is `Zop_div_pow` of
`H4N_rhoR_shape3`; all that is needed is `HasDerivAt` of the numerator. -/

private lemma Zop_rhoR_step5 (z : ℝ) (hz : z ≠ -1) :
    Work.Spaces.Zop (fun w : ℝ =>
        w^2 * (16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4) / (1+w)^8) z
      = z^2 * (32 - 684*z + 2644*z^2 - 2644*z^3 + 684*z^4 - 32*z^5) / (1+z)^9 := by
  have h1z : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  have h2 : HasDerivAt (fun w : ℝ => 16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4)
      (-196 + 832*z - 588*z^2 + 64*z^3) z := by
    have hp0 : HasDerivAt (fun w : ℝ => 16 - 196*w) (-(196*1)) z :=
      ((hasDerivAt_id' z).const_mul (196:ℝ)).const_sub (16:ℝ)
    have hp1 : HasDerivAt (fun w : ℝ => 416*w^2) (416*(↑2*z^(2-1))) z :=
      (hasDerivAt_pow 2 z).const_mul (416:ℝ)
    have hp2 : HasDerivAt (fun w : ℝ => 196*w^3) (196*(↑3*z^(3-1))) z :=
      (hasDerivAt_pow 3 z).const_mul (196:ℝ)
    have hp3 : HasDerivAt (fun w : ℝ => 16*w^4) (16*(↑4*z^(4-1))) z :=
      (hasDerivAt_pow 4 z).const_mul (16:ℝ)
    have hA : HasDerivAt (fun w : ℝ => 16 - 196*w + 416*w^2)
        (-(196*1) + 416*(↑2*z^(2-1))) z := hp0.add hp1
    have hB : HasDerivAt (fun w : ℝ => 16 - 196*w + 416*w^2 - 196*w^3)
        (-(196*1) + 416*(↑2*z^(2-1)) - 196*(↑3*z^(3-1))) z := hA.sub hp2
    have hC : HasDerivAt (fun w : ℝ => 16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4)
        (-(196*1) + 416*(↑2*z^(2-1)) - 196*(↑3*z^(3-1)) + 16*(↑4*z^(4-1))) z :=
      hB.add hp3
    have he : (-(196*1) + 416*(↑2*z^(2-1)) - 196*(↑3*z^(3-1)) + 16*(↑4*z^(4-1)) : ℝ)
        = -196 + 832*z - 588*z^2 + 64*z^3 := by ring
    rwa [he] at hC
  have hderiv : HasDerivAt (fun w : ℝ =>
        w^2 * (16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4))
      (32*z - 588*z^2 + 1664*z^3 - 980*z^4 + 96*z^5) z := by
    have h' : HasDerivAt (fun w : ℝ =>
          w^2 * (16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4))
        ((↑2*z^(2-1)) * (16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4)
          + z^2 * (-196 + 832*z - 588*z^2 + 64*z^3)) z :=
      (hasDerivAt_pow 2 z).mul h2
    have he : ((↑2*z^(2-1)) * (16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4)
        + z^2 * (-196 + 832*z - 588*z^2 + 64*z^3) : ℝ)
        = 32*z - 588*z^2 + 1664*z^3 - 980*z^4 + 96*z^5 := by ring
    rwa [he] at h'
  have h := Zop_div_pow 8 (by norm_num)
    (fun w : ℝ => w^2 * (16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4))
    (32*z - 588*z^2 + 1664*z^3 - 980*z^4 + 96*z^5) z hderiv hz
  refine h.trans ?_
  field_simp
  ring

private lemma Zop_rhoR_step6 (z : ℝ) (hz : z ≠ -1) :
    Work.Spaces.Zop (fun w : ℝ =>
        w^2 * (32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5) / (1+w)^9) z
      = z^2 * (64 - 2276*z + 14680*z^2 - 26440*z^3 + 14680*z^4 - 2276*z^5 + 64*z^6)
          / (1+z)^10 := by
  have h1z : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  have h2 : HasDerivAt (fun w : ℝ => 32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5)
      (-684 + 5288*z - 7932*z^2 + 2736*z^3 - 160*z^4) z := by
    have hp0 : HasDerivAt (fun w : ℝ => 32 - 684*w) (-(684*1)) z :=
      ((hasDerivAt_id' z).const_mul (684:ℝ)).const_sub (32:ℝ)
    have hp1 : HasDerivAt (fun w : ℝ => 2644*w^2) (2644*(↑2*z^(2-1))) z :=
      (hasDerivAt_pow 2 z).const_mul (2644:ℝ)
    have hp2 : HasDerivAt (fun w : ℝ => 2644*w^3) (2644*(↑3*z^(3-1))) z :=
      (hasDerivAt_pow 3 z).const_mul (2644:ℝ)
    have hp3 : HasDerivAt (fun w : ℝ => 684*w^4) (684*(↑4*z^(4-1))) z :=
      (hasDerivAt_pow 4 z).const_mul (684:ℝ)
    have hp4 : HasDerivAt (fun w : ℝ => 32*w^5) (32*(↑5*z^(5-1))) z :=
      (hasDerivAt_pow 5 z).const_mul (32:ℝ)
    have hA : HasDerivAt (fun w : ℝ => 32 - 684*w + 2644*w^2)
        (-(684*1) + 2644*(↑2*z^(2-1))) z := hp0.add hp1
    have hB : HasDerivAt (fun w : ℝ => 32 - 684*w + 2644*w^2 - 2644*w^3)
        (-(684*1) + 2644*(↑2*z^(2-1)) - 2644*(↑3*z^(3-1))) z := hA.sub hp2
    have hC : HasDerivAt (fun w : ℝ => 32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4)
        (-(684*1) + 2644*(↑2*z^(2-1)) - 2644*(↑3*z^(3-1)) + 684*(↑4*z^(4-1))) z :=
      hB.add hp3
    have hD : HasDerivAt (fun w : ℝ =>
          32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5)
        (-(684*1) + 2644*(↑2*z^(2-1)) - 2644*(↑3*z^(3-1)) + 684*(↑4*z^(4-1))
          - 32*(↑5*z^(5-1))) z := hC.sub hp4
    have he : (-(684*1) + 2644*(↑2*z^(2-1)) - 2644*(↑3*z^(3-1)) + 684*(↑4*z^(4-1))
        - 32*(↑5*z^(5-1)) : ℝ) = -684 + 5288*z - 7932*z^2 + 2736*z^3 - 160*z^4 := by ring
    rwa [he] at hD
  have hderiv : HasDerivAt (fun w : ℝ =>
        w^2 * (32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5))
      (64*z - 2052*z^2 + 10576*z^3 - 13220*z^4 + 4104*z^5 - 224*z^6) z := by
    have h' : HasDerivAt (fun w : ℝ =>
          w^2 * (32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5))
        ((↑2*z^(2-1)) * (32 - 684*z + 2644*z^2 - 2644*z^3 + 684*z^4 - 32*z^5)
          + z^2 * (-684 + 5288*z - 7932*z^2 + 2736*z^3 - 160*z^4)) z :=
      (hasDerivAt_pow 2 z).mul h2
    have he : ((↑2*z^(2-1)) * (32 - 684*z + 2644*z^2 - 2644*z^3 + 684*z^4 - 32*z^5)
        + z^2 * (-684 + 5288*z - 7932*z^2 + 2736*z^3 - 160*z^4) : ℝ)
        = 64*z - 2052*z^2 + 10576*z^3 - 13220*z^4 + 4104*z^5 - 224*z^6 := by ring
    rwa [he] at h'
  have h := Zop_div_pow 9 (by norm_num)
    (fun w : ℝ => w^2 * (32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5))
    (64*z - 2052*z^2 + 10576*z^3 - 13220*z^4 + 4104*z^5 - 224*z^6) z hderiv hz
  refine h.trans ?_
  field_simp
  ring

/-- The closed form of the fifth `D_z`-iterate of `ρ`. -/
private lemma Zop_rhoR_shape5 (z : ℝ) (hz : z ≠ -1) :
    (Work.Spaces.Zop^[5] rhoR) z
      = z^2 * (32 - 684*z + 2644*z^2 - 2644*z^3 + 684*z^4 - 32*z^5) / (1 + z)^9 := by
  have h4 : (Work.Spaces.Zop^[4] rhoR) =ᶠ[𝓝 z]
      (fun w : ℝ => w^2 * (16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4) / (1+w)^8) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact H4N_rhoR_shape4 w hw
  have h1 : Work.Spaces.Zop (Work.Spaces.Zop^[4] rhoR) z
      = Work.Spaces.Zop (fun w : ℝ =>
          w^2 * (16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4) / (1+w)^8) z := by
    rw [Zop_apply, Zop_apply, h4.deriv_eq]
  rw [show (5 : ℕ) = 4 + 1 by norm_num, Function.iterate_succ_apply', h1]
  exact Zop_rhoR_step5 z hz

/-- The closed form of the sixth `D_z`-iterate of `ρ`. -/
private lemma Zop_rhoR_shape6 (z : ℝ) (hz : z ≠ -1) :
    (Work.Spaces.Zop^[6] rhoR) z
      = z^2 * (64 - 2276*z + 14680*z^2 - 26440*z^3 + 14680*z^4 - 2276*z^5 + 64*z^6)
          / (1 + z)^10 := by
  have h5 : (Work.Spaces.Zop^[5] rhoR) =ᶠ[𝓝 z]
      (fun w : ℝ => w^2 * (32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5)
        / (1+w)^9) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact Zop_rhoR_shape5 w hw
  have h1 : Work.Spaces.Zop (Work.Spaces.Zop^[5] rhoR) z
      = Work.Spaces.Zop (fun w : ℝ =>
          w^2 * (32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5) / (1+w)^9) z := by
    rw [Zop_apply, Zop_apply, h5.deriv_eq]
  rw [show (6 : ℕ) = 5 + 1 by norm_num, Function.iterate_succ_apply', h1]
  exact Zop_rhoR_step6 z hz

/-! ## The polynomial bounds -/

/-- `z^k ≤ (1+z)^n` on `z ≥ 0` for `k ≤ n`. -/
private lemma pow_le_one_add_pow (z : ℝ) (hz : 0 ≤ z) {k n : ℕ} (hkn : k ≤ n) :
    z^k ≤ (1+z)^n := by
  calc z^k ≤ (1+z)^k := pow_le_pow_left₀ hz (by linarith) k
    _ ≤ (1+z)^n := pow_le_pow_right₀ (by linarith) hkn

/-- The `ℓ¹`-bound for `N_5`: `|N_5(z)| ≤ 6720(1+z)^5`. -/
private lemma rhoN5_bound (z : ℝ) (hz : 0 ≤ z) :
    |(32:ℝ) - 684*z + 2644*z^2 - 2644*z^3 + 684*z^4 - 32*z^5| ≤ 6720*(1+z)^5 := by
  have h0 : z^0 ≤ (1+z)^5 := pow_le_one_add_pow z hz (by norm_num)
  have h1 : z^1 ≤ (1+z)^5 := pow_le_one_add_pow z hz (by norm_num)
  have h2 : z^2 ≤ (1+z)^5 := pow_le_one_add_pow z hz (by norm_num)
  have h3 : z^3 ≤ (1+z)^5 := pow_le_one_add_pow z hz (by norm_num)
  have h4 : z^4 ≤ (1+z)^5 := pow_le_one_add_pow z hz (by norm_num)
  have h5 : z^5 ≤ (1+z)^5 := pow_le_one_add_pow z hz (by norm_num)
  rw [abs_le]
  constructor <;> nlinarith [h0, h1, h2, h3, h4, h5]

/-- The `ℓ¹`-bound for `N_6`: `|N_6(z)| ≤ 60480(1+z)^6`. -/
private lemma rhoN6_bound (z : ℝ) (hz : 0 ≤ z) :
    |(64:ℝ) - 2276*z + 14680*z^2 - 26440*z^3 + 14680*z^4 - 2276*z^5 + 64*z^6|
      ≤ 60480*(1+z)^6 := by
  have h0 : z^0 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  have h1 : z^1 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  have h2 : z^2 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  have h3 : z^3 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  have h4 : z^4 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  have h5 : z^5 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  have h6 : z^6 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  rw [abs_le]
  constructor <;> nlinarith [h0, h1, h2, h3, h4, h5, h6]

/-! ## The single step, and the theorem -/

/-- If `Zop^[j] ρ = z²·N/(1+z)^{4+j}` at `z` and `|N(z)| ≤ C(1+z)^j`, then
`|Zop^[j] ρ (z) · w(z)| ≤ C/(1+z)²`. -/
private lemma rho_w_bound_of (j : ℕ) (N : ℝ → ℝ) (C z : ℝ) (hC : 0 < C) (hz : 0 ≤ z)
    (hshape : (Work.Spaces.Zop^[j] rhoR) z = z^2 * N z / (1 + z)^(4+j))
    (hnumb : |N z| ≤ C * (1 + z)^j) :
    |(Work.Spaces.Zop^[j] rhoR) z * Work.Spaces.w z| ≤ C / (1 + z)^2 := by
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    rw [Work.Spaces.w]
    norm_num
    positivity
  · have hz0 : z ≠ 0 := ne_of_gt hpos
    have h1z : (0:ℝ) < 1 + z := by linarith
    rw [hshape, Work.Spaces.w]
    have hp : (1 + z)^(4+j) = (1 + z)^(2+j) * (1+z)^2 := by
      rw [show (4:ℕ) + j = (2+j)+2 by omega, pow_add]
    rw [hp]
    have key : z^2 * N z / ((1+z)^(2+j)*(1+z)^2) * ((1+z)^2/z^2)
        = N z / (1+z)^(2+j) := by
      field_simp
    rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1+z)^(2+j))]
    have hp2 : (1+z)^(2+j) = (1+z)^2 * (1+z)^j := by
      rw [pow_add]
    rw [div_le_div_iff₀ (by positivity) (by positivity), hp2]
    have hfin : |N z| * (1+z)^2 ≤ C * (1+z)^j * (1+z)^2 :=
      mul_le_mul_of_nonneg_right hnumb (by positivity)
    nlinarith [hfin]

theorem H6N_GammaTerm_rho_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z| ≤ M / (1 + z) ^ 2 := by
  refine ⟨60480, by norm_num, ?_⟩
  intro j hj z hz
  interval_cases j
  · have h := rho_w_bound_of 0 (fun _ : ℝ => 1) 1 z (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[0] rhoR) z * Work.Spaces.w z| ≤ 1 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            norm_num
    · rw [Function.iterate_zero_apply]
      show rhoR z = z^2 * 1 / (1 + z)^(4+0)
      rw [rhoR]
      norm_num
    · simp
  · have h := rho_w_bound_of 1 (fun z : ℝ => 2 - 2*z) 840 z (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[1] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            norm_num
    · rw [H4N_rhoR_shape12.1 z (by linarith)]
    · exact H4N_rhoR_numbound.2.1 z hz
  · have h := rho_w_bound_of 2 (fun z : ℝ => 4 - 12*z + 4*z^2) 840 z (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[2] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            norm_num
    · rw [H4N_rhoR_shape12.2 z (by linarith)]
    · exact H4N_rhoR_numbound.2.2.1 z hz
  · have h := rho_w_bound_of 3 (fun z : ℝ => 8 - 52*z + 52*z^2 - 8*z^3) 840 z
      (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[3] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            norm_num
    · rw [H4N_rhoR_shape3 z (by linarith)]
    · exact H4N_rhoR_numbound.2.2.2.1 z hz
  · have h := rho_w_bound_of 4 (fun z : ℝ => 16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4) 840 z
      (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[4] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            norm_num
    · rw [H4N_rhoR_shape4 z (by linarith)]
    · exact H4N_rhoR_numbound.2.2.2.2 z hz
  · have h := rho_w_bound_of 5
      (fun z : ℝ => 32 - 684*z + 2644*z^2 - 2644*z^3 + 684*z^4 - 32*z^5) 6720 z
      (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[5] rhoR) z * Work.Spaces.w z| ≤ 6720 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            norm_num
    · rw [Zop_rhoR_shape5 z (by linarith)]
    · exact rhoN5_bound z hz
  · have h := rho_w_bound_of 6
      (fun z : ℝ => 64 - 2276*z + 14680*z^2 - 26440*z^3 + 14680*z^4 - 2276*z^5 + 64*z^6)
      60480 z (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[6] rhoR) z * Work.Spaces.w z| ≤ 60480 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := le_refl _
    · rw [Zop_rhoR_shape6 z (by linarith)]
    · exact rhoN6_bound z hz

end Work.Construction
end
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Base.H1IP_cs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Base

set_option autoImplicit false

/-! ## Slice measurability from continuity on the open interval -/


/-! ## The four weighted blocks are `L²` -/




/-! ## The three `L²`-norm identifications with the paper's energies -/




/-! ## Each block `L²`-norm is dominated by the `ℋ¹`-norm square -/




/-- Off the two null endpoints of `Iθ`, the plain block `Xw f = f·w` is dominated by the
`H¹`-integrand, because the `D_z⁰`-summand of the latter is `(f·w/√(sin 2θ^η))²`. -/
private theorem sq_Xw_le_HkIntegrand_ae (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      (Coercivity.Xw f z θ) ^ 2 ≤ Spaces.HkIntegrand α 1 f z θ := by
  rw [← Coercivity.restrict_Ioo_eq_restrict_Iθ]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have ht0 : 0 < (Real.sin (2 * θ)) ^ (Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have ht1 : (Real.sin (2 * θ)) ^ (Spaces.eta / 2) ≤ 1 := by
    calc (Real.sin (2 * θ)) ^ (Spaces.eta / 2)
        ≤ (1 : ℝ) ^ (Spaces.eta / 2) :=
          Real.rpow_le_rpow (le_of_lt hs0) hs1
            (div_nonneg (le_of_lt Spaces.eta_pos) (by norm_num))
      _ = 1 := by simp
  have hkey : (f z θ * Spaces.w z) ^ 2
      ≤ ((f z θ * Spaces.w z) / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (pow_pos ht0 2)]
    have ht2 : (Real.sin (2 * θ) ^ (Spaces.eta / 2)) ^ 2 ≤ 1 := by
      nlinarith [ht0, ht1]
    simpa using mul_le_mul_of_nonneg_left ht2 (sq_nonneg (f z θ * Spaces.w z))
  have hterm : (Coercivity.Xw f z θ) ^ 2
      ≤ (Spaces.DzIter 0 f z θ
          * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2 := by
    simp only [Coercivity.Xw, Spaces.DzIter_zero]
    rw [← mul_div_assoc]
    exact hkey
  exact le_trans hterm (Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num))


/-! ## The triangle inequality for four terms -/

private theorem abs_add_four (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-! ## The two-dimensional Cauchy–Schwarz lemma

For `L²`-functions `X`, `Y` (a.e. strongly measurable on the quadrant and on every
angular slice) the iterated integral of the product is bounded by the product of the
square roots of the two iterated `L²`-norms.  The proof is Cauchy–Schwarz twice: on
each angular slice (`holder_two_mul` with the functions `X z`, `Y z`), and then in the
radial variable applied to the two square-root functions
`z ↦ √(∫_θ X(z,θ)²)` and `z ↦ √(∫_θ Y(z,θ)²)`, which are integrable by
`integrable_sqrt_mul_sqrt`. -/

/-! ## The main theorem -/


end Work.FTS.CoercivityStep.Base
end
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

/-! ## The measure-theoretic transfer -/

/-- **Iterated integrals of a pointwise-dominated nonnegative integrand.**

If `0 ≤ A ≤ B` pointwise on `Iz × Iθ`, if every angular slice of `B` is integrable and
`z ↦ ∫_θ B z θ` is integrable on `Iz`, then `∫_z ∫_θ A ≤ ∫_z ∫_θ B`.

No measurability of `A` is assumed: where the slice `θ ↦ A z θ` is not integrable the
inner integral is `0 ≤ ∫_θ B z θ` (the latter being nonnegative by `0 ≤ B` on the slice),
and `MeasureTheory.integral_mono_of_nonneg` applies in each case. -/
private lemma iterated_integral_le {A B : ℝ → ℝ → ℝ}
    (hA0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ A z θ)
    (hAB : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, A z θ ≤ B z θ)
    (hB : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => B z θ) Work.Spaces.Iθ)
    (hBz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, B z θ) Work.Spaces.Iz) :
    ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, A z θ) ≤
      ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, B z θ) := by
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  refine integral_mono_of_nonneg ?_ hBz ?_
  · -- nonnegativity of the inner integral of `A` on `Iz`
    refine ae_restrict_of_forall_mem hmesz (fun z hz => ?_)
    exact integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hA0 z hz θ hθ))
  · -- `z ↦ ∫_θ A z θ ≤ z ↦ ∫_θ B z θ` on `Iz`
    refine ae_restrict_of_forall_mem hmesz (fun z hz => ?_)
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hA0 z hz θ hθ))
      (hB z hz)
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hAB z hz θ hθ))

/-! ## The target -/

/-- The squared `ℋ^n`-norm of `D_θ f` is dominated by the squared `ℋ^{n+1}`-norm of `f`,
for every `f` with honest `ℋ^{n+1}`-integrand. -/
theorem HkSq_Dth_le (α : ℝ) (hα : 0 < α) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f :=
  iterated_integral_le
    (fun z _ θ _ => Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dth f) z θ)
    (fun z hz θ hθ => Work.Coercivity.HkIntegrand_Dth_le α hα n f z θ hz hθ)
    (fun z hz => h.1 z hz) h.2

end Work.FTS.CoercivityStep.Norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dz_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `|D_z f|_{H^n}² ≤ |f|_{H^{n+1}}²`

The `H^k`-integrand of the paper is a sum of squares of weighted `D`-derivatives.  For
`g = D_z f`, every summand of `HkIntegrand α n (D_z f)` is a summand of
`HkIntegrand α (n+1) f`:

* the pure family: `D_z^i (D_z f) = D_z^{i+1} f` is a pure derivative of `f` of order
  `i + 1 ≤ n + 1`;
* the mixed family: `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`, which uses the
  commutation of `D_z` and `D_θ` on the closed quadrant (available because `f` is
  smooth on a neighbourhood of it), is a mixed derivative of `f` of total order
  `i + j + 1 ≤ n + 1`.

This pointwise domination of the integrands is `Work.Coercivity.HkIntegrand_Dz_le`; the
present lemma is its integrated form.  Unlike the corresponding `D_θ` statement it needs
no hypothesis `0 < α`, because the pure family keeps the lighter weight `w/√sin(2θ)^η`
on both sides (only the `D_θ`-case has to compare that weight with `W`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

theorem HkSq_Dz_le (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f)
    (h : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f := by
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz f) z θ)
    h.2 ?_
  show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (Work.Spaces.Dz f) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (n + 1) f z θ
  exact MeasureTheory.ae_restrict_of_forall_mem hmesz fun z hz =>
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz f) z θ)
      (h.1 z hz)
      (MeasureTheory.ae_restrict_of_forall_mem hmesθ fun θ hθ =>
        Work.Coercivity.HkIntegrand_Dz_le α n hsm z θ hz hθ)

end Work.FTS.CoercivityStep.Norm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Rfun_bound_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! The `C²` version of the chain of `lzeroGrowthSlice.lean`. -/
namespace LzeroGrowthC2

open LzeroGrowth

/-! ## Differentiability and continuity of the data on the open interval, at regularity `C²` -/

theorem hasDerivAt_u {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : HasDerivAt u (deriv u θ) θ :=
  ((hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt

theorem contDiffAt_deriv_of_contDiffOn {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : ContDiffAt ℝ 1 (deriv u) θ :=
  (hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)).derivWithin (m := 1) (by norm_num)


theorem continuousOn_deriv1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
  fun θ hθ => (contDiffAt_deriv_of_contDiffOn hu hθ).continuousAt.continuousWithinAt

theorem continuousOn_deriv2 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun θ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) :=
  fun θ hθ =>
    ((contDiffAt_deriv_of_contDiffOn hu hθ).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt

/-- `Lzero1 u` is continuous on the open interval. -/
theorem continuousOn_Lzero1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) := by
  have hc0 : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn
  have hc1 : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) := continuousOn_deriv1 hu
  have hc2 : ContinuousOn (fun θ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_deriv2 hu
  have hm : ContinuousOn (fun θ => deriv (fun t => Real.tan t * u t) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hg : ContinuousOn
        (fun θ : ℝ => (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContinuousOn (fun θ : ℝ => 1 / Real.cos θ ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
        refine ContinuousOn.div continuousOn_const (Real.continuous_cos.continuousOn.pow 2) ?_
        intro θ hθ
        exact pow_ne_zero 2 (cos_ne_zero hθ)
      have h2 : ContinuousOn (fun θ : ℝ => Real.tan θ * deriv u θ)
          (Set.Ioo 0 (Real.pi / 2)) := by
        have ht : ContinuousOn Real.tan (Set.Ioo 0 (Real.pi / 2)) :=
          Real.continuousOn_tan.mono (fun x hx => cos_ne_zero hx)
        rw [show (fun θ : ℝ => Real.tan θ * deriv u θ) = Real.tan * deriv u from rfl]
        exact ht.mul hc1
      exact (h1.mul hc0).add h2
    refine ContinuousOn.congr hg ?_
    intro θ hθ
    show deriv (fun t => Real.tan t * u t) θ
      = (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ
    have hm' : HasDerivAt (fun t => Real.tan t * u t)
        ((1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ) θ :=
      (Real.hasDerivAt_tan (cos_ne_zero hθ)).mul (hasDerivAt_u hu hθ)
    rw [hm'.deriv]
  refine ContinuousOn.congr (f := fun θ =>
    -(deriv (deriv u) θ) + deriv (fun t => Real.tan t * u t) θ - 6 * u θ) ?_ ?_
  · exact ((hc2.neg).add hm).sub (hc0.const_mul 6)
  · intro θ hθ
    simp only [Work.FTS.EllipticEst.Lzero1]


/-! ## Interval integrability of the source term `2 g sinθcos²θ` -/


/-! ## The two exact derivative identities -/




/-! ## The bound on `Dfun` and the two growth bounds for `Rfun` -/





end LzeroGrowthC2


end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The angular weight and elementary comparisons -/







/-! ## The two Cramer coefficients of a slice, and their derivatives -/







/-! ## The Newton–Leibniz bound and interval integrability -/








/-! ## Bounds for the two Cramer coefficients -/





/-! ## The arithmetic of the two cases -/



/-! ## The main theorem -/


end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4SliceBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The single-slice `I₄` upper bound** (the analytic heart of `I4UpperHonest`).

`Φ` is the angular slice of a stream function, `σ = sin(2θ)^{-η}`, `η = 99/100`, `ψ = Φ/cos θ`.
Given the two `HkMem`-type integrability hypotheses, the *pointwise algebra* `hAlg` (four calculus
identities: `∂_θ(tan θ·Φ) = cos θ·ψ + sin θ·ψ'`; `Φ'' = cos θ·ψ'' − 2 sin θ·ψ' − cos θ·ψ`;
`P' = cos θ·(Φ''+Φ)` with `P = cos²θ·ψ'`; and
`(½·sin θ/cos³θ·σ·P²)' = (sin θ/cos³θ)σPP' + ½Σσ(ψ')²` with `Σ = (1−η)cos²θ + (3+η)sin²θ`),
and the *boundary vanishing* `hBound`: `(sin θ/cos³θ)·σ·P² → 0` as `θ → π/2⁻`, the slice estimate

`∫_θ ∂_θ(tan θ·Φ)·Φ''·σ ≤ 50∫_θ ψ²σ + √(∫_θψ²σ)·√(∫_θ(Φ'')²σ)`

holds (`50 = ½/(1−η)`).  Proof route: on `(δ,θ₁) ⊂ (0,π/2)` the two identities give
`∫_δ^{θ₁} u b σ = ∫_δ^{θ₁} cψbσ + ½[(sσ/c³)P²]_δ^{θ₁} − ½∫_δ^{θ₁}Σσψ'² − ∫_δ^{θ₁}sσψ'Φ`;
the AM–GM inequality `|sσψ'Φ| ≤ ½Σσψ'² + ½(s²σΦ²/Σ)` cancels the negative term;
`s²σΦ²/Σ ≤ σψ²/(1−η)`; drop `−½(sσ/c³)P²(δ) ≤ 0` and let `δ → 0` (ℒ¹ convergence of interval
integrals), then `θ₁ → π/2` using `hBound`; finally Cauchy–Schwarz in `θ`
(`Work.FTS.EllipticEst.AngSecond.slice_sq_integral_mul_le` with `F = cos θ·ψ`, `G = Φ''`,
`κ = σ`) turns `∫_θ cψ·Φ''·σ` into `√(∫_θψ²σ)·√(∫_θ(Φ'')²σ)`.  The case where the left-hand
side is not integrable is trivial (the set integral is the junk value `0`, and the right-hand
side is `≥ 0`). -/
theorem I4SliceBound (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn
      (fun θ => (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2)))
    (hB : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2)))
    (hAlg : (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => Real.tan θ' * Φ θ') θ
          = Real.cos θ * (Φ θ / Real.cos θ)
            + Real.sin θ * deriv (fun θ' => Φ θ' / Real.cos θ') θ)
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (deriv Φ) θ
          = Real.cos θ * deriv (deriv (fun θ' => Φ θ' / Real.cos θ')) θ
            - 2 * Real.sin θ * deriv (fun θ' => Φ θ' / Real.cos θ') θ
            - Real.cos θ * (Φ θ / Real.cos θ))
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => (Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ') θ
          = Real.cos θ * (deriv (deriv Φ) θ + Φ θ))
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => (1/2) * (Real.sin θ' / (Real.cos θ')^3)
            * (Real.sin (2*θ'))^(-(99/100:ℝ))
            * ((Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ')^2) θ
          = (Real.sin θ / (Real.cos θ)^3) * (Real.sin (2*θ))^(-(99/100:ℝ))
              * ((Real.cos θ)^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ)
              * deriv (fun θ' => (Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ') θ
            + (1/2) * ((1 - 99/100) * (Real.cos θ)^2 + (3 + 99/100) * (Real.sin θ)^2)
              * (Real.sin (2*θ))^(-(99/100:ℝ))
              * (deriv (fun θ' => Φ θ' / Real.cos θ') θ)^2))
    (hBound : Filter.Tendsto
      (fun θ => Real.sin θ / (Real.cos θ) ^ 3
        * ((Real.cos θ) ^ 2 * deriv (fun θ' => Φ θ' / Real.cos θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∫ θ in Set.Icc 0 (Real.pi / 2),
        deriv (fun θ' => Real.tan θ' * Φ θ') θ * deriv (deriv Φ) θ
          * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
      ≤ 50 * (∫ θ in Set.Icc 0 (Real.pi / 2),
            (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        + Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
            (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
          * Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
            (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) := by
  -- normalise the hypotheses and the goal to the `I4*` vocabulary
  have hA' : MeasureTheory.IntegrableOn (fun θ => I4psi Φ θ ^ 2 * I4sig θ) Work.Spaces.Iθ := hA
  have hB' : MeasureTheory.IntegrableOn (fun θ => I4b Φ θ ^ 2 * I4sig θ) Work.Spaces.Iθ := hB
  have hBound' : Filter.Tendsto (I4H Φ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := hBound
  change (∫ θ in Work.Spaces.Iθ, I4u Φ θ * I4b Φ θ * I4sig θ)
      ≤ 50 * (∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ)
        + Real.sqrt (∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, I4b Φ θ ^ 2 * I4sig θ)
  -- the three integrals of the statement and the Cauchy–Schwarz bound
  set X : ℝ := ∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ with hX
  set Y : ℝ := ∫ θ in Work.Spaces.Iθ, I4b Φ θ ^ 2 * I4sig θ with hY
  set Z : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ with hZ
  set Bc : ℝ := Real.sqrt Z * Real.sqrt Y with hBc
  have hXnn : 0 ≤ X := by
    rw [hX]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (I4sig_nonneg hθ))
  have hYnn : 0 ≤ Y := by
    rw [hY]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (I4sig_nonneg hθ))
  have hZX : Z ≤ X := by
    have h := I4CosSqIntegralLe Φ hA'
    rwa [← hZ, ← hX] at h
  have hBcle : Bc ≤ Real.sqrt X * Real.sqrt Y := by
    rw [hBc]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hZX) (Real.sqrt_nonneg Y)
  by_cases hint : MeasureTheory.IntegrableOn (fun θ => I4u Φ θ * I4b Φ θ * I4sig θ)
      Work.Spaces.Iθ
  · -- ## main case: truncate at `δ > 0` and `θ₁ < π/2`, then pass to the limits
    have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ q Ψv : ℝ,
        |Real.sin θ * I4sig θ * q * Ψv|
          ≤ (1 / 2) * I4Sig θ * I4sig θ * q ^ 2
            + 50 * I4sig θ * (Ψv / Real.cos θ) ^ 2 :=
      fun θ hθ q Ψv => I4AMGM θ hθ q Ψv
    have hGder : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        HasDerivAt (I4G Φ) (deriv (I4G Φ) θ) θ := I4GHasDerivAt Φ hsm
    -- the truncated inequality
    have htrunc : ∀ δ θ₁ : ℝ, 0 < δ → δ ≤ θ₁ → θ₁ < Real.pi / 2 →
        (∫ θ in δ..θ₁, I4u Φ θ * I4b Φ θ * I4sig θ) ≤ Bc + I4G Φ θ₁ + 50 * X := by
      intro δ θ₁ hδ hδθ hθ₁
      have hid := I4IntervalIdentity Φ hsm hAlg hGder hδ hδθ hθ₁
      have hcross := I4CrossTermBound Φ hsm hA' hpt hδ hδθ hθ₁
      have hcs := I4CSBound Φ hA' hB' hδ hδθ hθ₁
      have hGδ : 0 ≤ I4G Φ δ := I4G_nonneg Φ ⟨hδ, lt_of_le_of_lt hδθ hθ₁⟩
      have hcs' : (∫ θ in δ..θ₁, Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ) ≤ Bc := by
        rw [hBc, hZ, hY]
        exact hcs
      have hcross' : -(∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
          ≤ (1 / 2) * (∫ θ in δ..θ₁, I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
            + 50 * X := by
        have h := hcross
        rw [hX]
        have hab : -(∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
            ≤ |∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ| := by
          have h2 := neg_abs_le (∫ θ in δ..θ₁,
            Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
          linarith
        linarith [hab, h]
      linarith [hid, hcs', hcross', hGδ]
    -- the limits
    have hGlim : Filter.Tendsto (I4G Φ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h1 := hBound'.const_mul (1 / 2 : ℝ)
      have h2 : (fun θ => (1 / 2 : ℝ) * I4H Φ θ) = fun θ => I4G Φ θ := by
        funext θ
        rw [I4H_eq_two_mul_I4G]
        ring
      rw [h2] at h1
      simpa using h1
    have hlimg : Filter.Tendsto
        (fun p : ℝ × ℝ => ∫ x in p.1..p.2, I4u Φ x * I4b Φ x * I4sig x)
        ((nhdsWithin (0 : ℝ) (Set.Ioi 0)) ×ˢ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))))
        (nhds (∫ x in Set.Icc 0 (Real.pi / 2), I4u Φ x * I4b Φ x * I4sig x)) := by
      rw [Filter.prod_eq_inf]
      exact IntervalIntegralTendstoSetIntegral
        (g := fun x => I4u Φ x * I4b Φ x * I4sig x) hint
    have hRHS : Filter.Tendsto (fun p : ℝ × ℝ => Bc + I4G Φ p.2 + 50 * X)
        ((nhdsWithin (0 : ℝ) (Set.Ioi 0)) ×ˢ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))))
        (nhds (Bc + 0 + 50 * X)) := by
      have h1 : Filter.Tendsto (fun p : ℝ × ℝ => I4G Φ p.2)
          ((nhdsWithin (0 : ℝ) (Set.Ioi 0)) ×ˢ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))))
          (nhds 0) := hGlim.comp tendsto_snd
      exact (h1.const_add Bc).add_const (50 * X)
    have hev : ∀ᶠ p : ℝ × ℝ in
        ((nhdsWithin (0 : ℝ) (Set.Ioi 0)) ×ˢ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))),
        (∫ x in p.1..p.2, I4u Φ x * I4b Φ x * I4sig x) ≤ Bc + I4G Φ p.2 + 50 * X := by
      rw [eventually_prod_iff]
      refine ⟨fun x => 0 < x ∧ x < 1, ?_, fun y => 1 < y ∧ y < Real.pi / 2, ?_, ?_⟩
      · refine Filter.Eventually.and ?_ ?_
        · exact self_mem_nhdsWithin
        · have h : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) :=
            isOpen_Iio.mem_nhds (by simp only [Set.mem_Iio]; norm_num)
          exact nhdsWithin_le_nhds h
      · refine Filter.Eventually.and ?_ ?_
        · have h : Set.Ioi (1 : ℝ) ∈ nhds (Real.pi / 2) :=
            isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith [Real.pi_gt_three])
          exact nhdsWithin_le_nhds h
        · exact self_mem_nhdsWithin
      · intro δ hδ θ₁ hθ₁
        exact htrunc δ θ₁ hδ.1 (by linarith [hδ.2, hθ₁.1]) hθ₁.2
    have hmain' : (∫ x in Set.Icc 0 (Real.pi / 2), I4u Φ x * I4b Φ x * I4sig x)
        ≤ Bc + 0 + 50 * X :=
      le_of_tendsto_of_tendsto hlimg hRHS hev
    have hmain : (∫ x in Work.Spaces.Iθ, I4u Φ x * I4b Φ x * I4sig x) ≤ Bc + 0 + 50 * X :=
      hmain'
    calc (∫ x in Work.Spaces.Iθ, I4u Φ x * I4b Φ x * I4sig x)
        ≤ Bc + 0 + 50 * X := hmain
      _ = Bc + 50 * X := by ring
      _ ≤ Real.sqrt X * Real.sqrt Y + 50 * X := by linarith [hBcle]
      _ = 50 * X + Real.sqrt X * Real.sqrt Y := by ring
  · -- ## junk case: the left-hand integral is `0`
    rw [MeasureTheory.integral_undef hint]
    have h1 : 0 ≤ 50 * X := mul_nonneg (by norm_num) hXnn
    have h2 : 0 ≤ Real.sqrt X * Real.sqrt Y :=
      mul_nonneg (Real.sqrt_nonneg X) (Real.sqrt_nonneg Y)
    linarith



end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.H2.L12k0Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

/-- The `k = 0` term of the `ℋ⁴`-norm of `L₁₂(g)`: the weighted Hardy inequality on `(0,1)` and
`(1,∞)` (`HardyLeftW`, `HardyRightW`) applied to `u = L₁₂(g)` with `u(0) = 0` and `u → 0` at
`∞`.  This is *verbatim* `Work.Elliptic.L12k0` with the (in fact unused: the proof body never
mentions it) hypothesis `Work.Spaces.SmoothNbhd g` deleted, so that it applies in the interior
class.  Either copy that proof and drop `hsm` (recommended; the file
`Submission/Work/Elliptic/L12k0.lean` contains the whole proof, and the two Hardy lemmas are
imported unchanged), or call `Work.Elliptic.HardyLeftW`/`HardyRightW` directly. -/
theorem L12k0Q (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α 4 g)
    (hint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0))
    (hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.L12 g z) (-(Work.Elliptic.L12dens g z)) z)
    (hcontd : ContinuousOn (Work.Elliptic.L12dens g) (Set.Ioi 0))
    (hcont : ContinuousOn (fun z => Work.Elliptic.L12 g z) (Set.Icc 0 1))
    (htend : Filter.Tendsto (fun z => Work.Elliptic.L12 g z) Filter.atTop (nhds 0))
    (h0 : Work.Elliptic.L12 g 0 = 0)
    (hQint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  let f : ℝ → ℝ := fun z => Work.Elliptic.Qang g 0 z
  let U : ℝ → ℝ := fun z => Work.Elliptic.L12 g z
  have hdens : ∀ z : ℝ, Work.Elliptic.L12dens g z = f z / z :=
    fun z => Work.Elliptic.L12dens_eq_Qang_div g z
  have hderivU : ∀ z : ℝ, 0 < z → HasDerivAt U (-(f z / z)) z := by
    intro z hz
    have h := hderiv z hz
    rw [← hdens z]
    exact h
  have hderiv01 : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z :=
    fun z hz => hderivU z hz.1
  have hderiv1 : ∀ z ∈ Set.Ioi (1 : ℝ), HasDerivAt U (-(f z / z)) z :=
    fun z hz => hderivU z (lt_trans one_pos hz)
  have hQIoo : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioo 0 1) :=
    hQint.mono_set (show Set.Ioo (0:ℝ) 1 ⊆ Work.Spaces.Iz from
      fun z hz => show (0:ℝ) ≤ z from le_of_lt hz.1)
  have hQIoi : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1) :=
    hQint.mono_set (show Set.Ioi (1:ℝ) ⊆ Work.Spaces.Iz from
      fun z hz => show (0:ℝ) ≤ z from le_of_lt (lt_trans one_pos hz))
  obtain ⟨hIntL, hBoundL⟩ := Work.Elliptic.HardyLeftW f U hderiv01 hcont h0 hQIoo
  obtain ⟨hIntR, hBoundR⟩ := Work.Elliptic.HardyRightW f U hderiv1 htend hQIoi
  have hae : (Set.Ioo (0:ℝ) 1 ∪ Set.Ioi 1) =ᵐ[volume] Work.Spaces.Iz :=
    Work.Elliptic.Ioo_union_Ioi_ae_eq_Iz
  have hvalU : (∫ z in Work.Spaces.Iz, (U z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (∫ z in Set.Ioo (0:ℝ) 1, (U z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + ∫ z in Set.Ioi (1:ℝ), (U z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    rw [← MeasureTheory.setIntegral_congr_set hae]
    exact MeasureTheory.setIntegral_union
      (Set.disjoint_left.mpr (fun a ha hb => absurd (lt_trans ha.2 hb) (lt_irrefl a)))
      measurableSet_Ioi hIntL hIntR
  have hvalf : (∫ z in Work.Spaces.Iz, (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (∫ z in Set.Ioo (0:ℝ) 1, (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + ∫ z in Set.Ioi (1:ℝ), (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    rw [← MeasureTheory.setIntegral_congr_set hae]
    exact MeasureTheory.setIntegral_union
      (Set.disjoint_left.mpr (fun a ha hb => absurd (lt_trans ha.2 hb) (lt_irrefl a)))
      measurableSet_Ioi hQIoo hQIoi
  have hIntAll : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    show MeasureTheory.IntegrableOn (fun z => (U z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz
    exact (MeasureTheory.integrableOn_congr_set_ae hae).mp (hIntL.union hIntR)
  have hbound : (∫ z in Work.Spaces.Iz, (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    show (∫ z in Work.Spaces.Iz, (U z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (∫ z in Work.Spaces.Iz, (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
    rw [hvalU, hvalf]
    linarith [hBoundL, hBoundR]
  exact ⟨hIntAll, hbound⟩

end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.T1HardIntZblk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.radialHkIntegrand_majorant_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem radialHkIntegrand_majorant_cd6 :
    ∃ C : ℝ, 0 < C ∧ ∀ {α K : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ},
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j : ℕ, j ≤ 6 →
        Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ)) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, 1 ≤ i → i + j ≤ 6 →
        Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ)) →
      ∀ {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b r z| ≤ K) →
      Work.Spaces.HkIntegrand α 6 (fun z θ => r z * g z θ) z θ
        ≤ C * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α K r g hDz hMx z θ hz hθ0 hθ1 hKb
  -- unfold the left-hand `ℋ⁶`-integrand into its two slot sums
  conv_lhs => simp only [Work.Spaces.HkIntegrand]
  -- ## the seven pure `D_z`-slots
  have hA : (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 7 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
    calc (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range 7, (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) :=
          Finset.sum_le_sum fun i hi =>
            radial_zslot_le_cd6 (fun j hj => hDz z θ hz hθ0 hθ1 j hj) hKb i (by
              have := Finset.mem_range.mp hi; omega)
      _ = 7 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  -- ## the (`≤ 49`) mixed slots
  have hB : (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 49 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
    calc (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
          (if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ _i ∈ Finset.range 7, ∑ _j ∈ Finset.range 7,
            (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 6
          · rw [ite_eq_left hc]
            exact radial_mslot_le_cd6 (fun j i hi hij => hMx z θ hz hθ0 hθ1 j i hi hij) hKb
              i j hc.1 hc.2
          · rw [ite_eq_right hc]
            exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K))
              (Work.Spaces.HkIntegrand_nonneg α 6 g z θ)
      _ = 49 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- ## the assembly
  have hKH : 0 ≤ K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ :=
    mul_nonneg (sq_nonneg K) (Work.Spaces.HkIntegrand_nonneg α 6 g z θ)
  have h1 : (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      + (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (7 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ))
        + (49 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)) := add_le_add hA hB
  have h2 : (7 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ))
        + (49 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ))
      ≤ 10 ^ 8 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by linarith [hKH]
  exact le_trans h1 h2

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SupZ.swap_abs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SupZ

set_option autoImplicit false

/-! ## A.e. strong measurability on the box `(a,b] × Iθ` -/

/-- A function continuous on the open quadrant `(0,∞) × (0,π/2)` is almost everywhere
strongly measurable for the product of the restrictions of Lebesgue measure to `(a,b]`
(with `0 < a`) and to `[0,π/2]`.  Indeed `(a,b] ⊆ (0,∞)` by `0 < a`, and `(a,b] × [0,π/2]`
differs from the open box `(a,b) × (0,π/2)` by the null set
`{b} × [0,π/2] ∪ (a,b] × {0,π/2}`; the open box is a subset of the open quadrant, where the
function is continuous. -/
theorem aesm_uncurry_prod_Ioc_aux {g : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) := by
  have hz : (Set.Ioc a b : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioo a b :=
    (MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume)).symm
  have hθ : (Set.Icc (0 : ℝ) (π / 2) : Set ℝ) =ᵐ[MeasureTheory.volume]
      Set.Ioo 0 (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
  have hprod : (Set.Ioc a b ×ˢ Set.Icc (0 : ℝ) (π / 2) : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
        (Set.Ioo a b ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
  exact (hg.mono fun p hp => ⟨lt_trans ha hp.1.1, hp.2⟩).aestronglyMeasurable
    (isOpen_Ioo.prod isOpen_Ioo).measurableSet

/-! ## Integrability of the partially integrated angular squares -/

/-- **Finiteness of `s ↦ ∫ θ in Iθ, Φ s θ ^ 2` on `(a,b]`, from the `1/z`-weighted
integrability of the same quantity.**

If every angular slice `θ ↦ Φ s θ ^ 2` is integrable on `Iθ` for `s > 0` (`hFin`), the
partially integrated function `s ↦ (∫ θ in Iθ, Φ s θ ^ 2) / s` is integrable on `(0,∞)`
(`hFint`), and the joint function is a.e. strongly measurable on the box (`hAE`), then
`s ↦ ∫ θ in Iθ, Φ s θ ^ 2` is integrable on `(a,b]` for `0 < a`.  On `(a,b]` one has
`s ≤ b` and `s > 0`, whence (as real numbers)
`‖∫ θ, Φ s θ ^ 2‖ = s · ‖(∫ θ, Φ s θ ^ 2)/s‖ ≤ b · ‖(∫ θ, Φ s θ ^ 2)/s‖`. -/
theorem integrable_partial_sq_div_aux {Φ : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hFin : ∀ z ∈ Set.Ioi 0,
      MeasureTheory.IntegrableOn (fun θ : ℝ => Φ z θ ^ 2) (Set.Icc 0 (π / 2)))
    (hFint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (∫ θ in Set.Icc 0 (π / 2), Φ z θ ^ 2) / z) (Set.Ioi 0))
    (hAE : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Φ p.1 p.2 ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2))))) :
    MeasureTheory.Integrable (fun s : ℝ => ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
  -- `hFin` is not needed below (the pointwise nonnegativity of the slices suffices); it is
  -- kept because it is part of the intended hypothesis set of the caller.
  have _ := hFin
  refine MeasureTheory.Integrable.mono'
    (f := fun s : ℝ => ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2)
    (g := fun s : ℝ => b * ‖(∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) / s‖)
    ?_ hAE.integral_prod_right' ?_
  · exact ((hFint.mono_set fun s hs => lt_trans ha hs.1).norm).const_mul b
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    have hspos : 0 < s := lt_trans ha hs.1
    have hu0 : 0 ≤ ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2 :=
      MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    have hus : 0 ≤ (∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) / s :=
      div_nonneg hu0 (le_of_lt hspos)
    have hbs : 1 ≤ b / s := (one_le_div hspos).mpr hs.2
    rw [Real.norm_of_nonneg hu0, Real.norm_of_nonneg hus]
    calc ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2
        = 1 * (∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) := by ring
      _ ≤ (b / s) * (∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) :=
            mul_le_mul_of_nonneg_right hbs hu0
      _ = b * ((∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) / s) := by ring

/-- **Finiteness of `s ↦ ∫ θ in Iθ, Φ s θ ^ 2` on `(a,b]`, from the `z`-weighted
integrability of the same quantity.**

Same as `integrable_partial_sq_div_aux` but starting from the hypothesis that
`z ↦ (∫ θ in Iθ, Φ z θ ^ 2) · z` is integrable on `(0,∞)`.  On `(a,b]` one has `s ≥ a > 0`,
whence `‖∫ θ, Φ s θ ^ 2‖ = (1/s)·‖(∫ θ, Φ s θ ^ 2)·s‖ ≤ (1/a)·‖(∫ θ, Φ s θ ^ 2)·s‖`. -/
theorem integrable_partial_sq_mul_aux {Φ : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hFin : ∀ z ∈ Set.Ioi 0,
      MeasureTheory.IntegrableOn (fun θ : ℝ => Φ z θ ^ 2) (Set.Icc 0 (π / 2)))
    (hGint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (∫ θ in Set.Icc 0 (π / 2), Φ z θ ^ 2) * z) (Set.Ioi 0))
    (hAE : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Φ p.1 p.2 ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2))))) :
    MeasureTheory.Integrable (fun s : ℝ => ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
  -- `hFin` is not needed below (the pointwise nonnegativity of the slices suffices); it is
  -- kept because it is part of the intended hypothesis set of the caller.
  have _ := hFin
  refine MeasureTheory.Integrable.mono'
    (f := fun s : ℝ => ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2)
    (g := fun s : ℝ => (1 / a) * ‖(∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) * s‖)
    ?_ hAE.integral_prod_right' ?_
  · exact ((hGint.mono_set fun s hs => lt_trans ha hs.1).norm).const_mul (1 / a)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    have hspos : 0 < s := lt_trans ha hs.1
    have hsa : a ≤ s := le_of_lt hs.1
    have hu0 : 0 ≤ ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2 :=
      MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    have hus : 0 ≤ (∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) * s :=
      mul_nonneg hu0 (le_of_lt hspos)
    have hza : 1 ≤ s / a := (one_le_div ha).mpr hsa
    rw [Real.norm_of_nonneg hu0, Real.norm_of_nonneg hus]
    calc ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2
        = 1 * (∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) := by ring
      _ ≤ (s / a) * (∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) :=
            mul_le_mul_of_nonneg_right hza hu0
      _ = (1 / a) * ((∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) * s) := by ring

/-! ## The target -/

theorem swap_abs {Φ Φ' : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hcont' : ContinuousOn (Function.uncurry Φ') (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hFin : ∀ z ∈ Set.Ioi 0, MeasureTheory.IntegrableOn (fun θ : ℝ => Φ z θ ^ 2) Work.Spaces.Iθ)
    (hGin : ∀ z ∈ Set.Ioi 0, MeasureTheory.IntegrableOn (fun θ : ℝ => Φ' z θ ^ 2) Work.Spaces.Iθ)
    (hFint : MeasureTheory.IntegrableOn (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z) (Set.Ioi 0))
    (hGint : MeasureTheory.IntegrableOn (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z) (Set.Ioi 0)) :
    (∫ θ in Work.Spaces.Iθ, ∫ s in a..b, |Φ s θ * Φ' s θ|)
      = ∫ s in a..b, ∫ θ in Work.Spaces.Iθ, |Φ s θ * Φ' s θ| := by
  -- A.e. strong measurability of the uncurried squares.
  have hAEΦ : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Φ p.1 p.2 ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) :=
    aesm_uncurry_prod_Ioc_aux ha (g := fun s θ : ℝ => Φ s θ ^ 2) (hcont.pow 2)
  have hAEΨ : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Φ' p.1 p.2 ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) :=
    aesm_uncurry_prod_Ioc_aux ha (g := fun s θ : ℝ => Φ' s θ ^ 2) (hcont'.pow 2)
  -- The angular slices are integrable for every `s ∈ (a,b]`, hence a.e.
  have hsliceΦ : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
      MeasureTheory.Integrable (fun θ : ℝ => Φ s θ ^ 2)
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2))) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun s hs => hFin s (lt_trans ha hs.1))
  have hsliceΨ : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
      MeasureTheory.Integrable (fun θ : ℝ => Φ' s θ ^ 2)
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2))) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun s hs => hGin s (lt_trans ha hs.1))
  -- The partially integrated squares are integrable.
  have houterΦ := integrable_partial_sq_div_aux (Φ := Φ) ha hFin hFint hAEΦ
  have houterΨ := integrable_partial_sq_mul_aux (Φ := Φ') ha hGin hGint hAEΨ
  -- Tonelli: the uncurried squares are integrable on the product.
  have hIntΦ : MeasureTheory.Integrable (Function.uncurry fun s θ : ℝ => Φ s θ ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) :=
    (Work.Spaces.integrable_prod_of_iterated
      (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
      (ν := MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))
      (G := fun s θ : ℝ => Φ s θ ^ 2) (fun _ _ => sq_nonneg _) hAEΦ hsliceΦ houterΦ).1
  have hIntΨ : MeasureTheory.Integrable (Function.uncurry fun s θ : ℝ => Φ' s θ ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) :=
    (Work.Spaces.integrable_prod_of_iterated
      (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
      (ν := MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))
      (G := fun s θ : ℝ => Φ' s θ ^ 2) (fun _ _ => sq_nonneg _) hAEΨ hsliceΨ houterΨ).1
  -- A.e. strong measurability of the integrand `|Φ · Φ'|`.
  have hquad : ContinuousOn (Function.uncurry fun s θ : ℝ => |Φ s θ * Φ' s θ|)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (hcont.mul hcont').abs
  have hAEabs : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => |Φ p.1 p.2 * Φ' p.1 p.2|)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) :=
    aesm_uncurry_prod_Ioc_aux ha (g := fun s θ : ℝ => |Φ s θ * Φ' s θ|) hquad
  -- Domination `|Φ s θ · Φ' s θ| ≤ Φ s θ ^ 2 + Φ' s θ ^ 2` and integrability on the product.
  have hIntAbs : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => |Φ p.1 p.2 * Φ' p.1 p.2|)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) := by
    refine MeasureTheory.Integrable.mono' (hIntΦ.add hIntΨ) hAEabs ?_
    filter_upwards with p
    have h := sq_nonneg (|Φ p.1 p.2| - |Φ' p.1 p.2|)
    have h2 : |Φ p.1 p.2 * Φ' p.1 p.2| ≤ Φ p.1 p.2 ^ 2 + Φ' p.1 p.2 ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_abs (Φ p.1 p.2), sq_abs (Φ' p.1 p.2), h]
    rwa [Real.norm_eq_abs, abs_abs]
  -- Fubini for interval integrals.
  have hIntU : MeasureTheory.Integrable
      (Function.uncurry fun s θ : ℝ => |Φ s θ * Φ' s θ|)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Set.uIoc_of_le hab]
    exact hIntAbs
  exact (MeasureTheory.intervalIntegral_integral_swap
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun s θ : ℝ => |Φ s θ * Φ' s θ|) hIntU).symm

end Work.FTS.StrongPersist.SupZ
end
end
