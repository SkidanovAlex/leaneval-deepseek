import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.TT.Shim.DzPsiAux
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.ZcutSmoothCompact
-- ===== merged: Submission.Work.AngSecond.I1_honesty =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.AngSecond

open Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Elementary pieces -/




/-- **AM–GM domination.**  If `F²κ` and `G²κ` are integrable on `s` and `κ ≥ 0` on `s`, then
`F G κ` is integrable on `s`:  pointwise `|F G κ| ≤ (F²κ + G²κ)/2`. -/
theorem integrableOn_mul_of_sq_aux {s : Set ℝ} (hs : MeasurableSet s) {F G κ : ℝ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict s))
    (hG : AEStronglyMeasurable G (volume.restrict s))
    (hκm : Measurable κ) (hκnn : ∀ θ ∈ s, 0 ≤ κ θ)
    (hF2 : IntegrableOn (fun θ => F θ * F θ * κ θ) s)
    (hG2 : IntegrableOn (fun θ => G θ * G θ * κ θ) s) :
    IntegrableOn (fun θ => F θ * G θ * κ θ) s := by
  refine ((hF2.add hG2).mul_const (1 / 2)).mono'
    ((hF.mul hG).mul hκm.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_of_forall_mem hs hκnn] with θ hθ
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hθ]
  have hAM : 2 * (|F θ| * |G θ|) ≤ F θ * F θ + G θ * G θ := by
    nlinarith [sq_nonneg (|F θ| - |G θ|), sq_abs (F θ), sq_abs (G θ)]
  calc (|F θ| * |G θ|) * κ θ
      ≤ ((F θ * F θ + G θ * G θ) / 2) * κ θ :=
        mul_le_mul_of_nonneg_right (by linarith) hθ
    _ = (F θ * F θ * κ θ + G θ * G θ * κ θ) * (1 / 2) := by ring

/-- `cw z = 2(z-1)/(1+z)` is bounded by `2` on `[0,∞)`. -/
theorem abs_cw_le_two {z : ℝ} (hz : z ∈ Work.Spaces.Iz) : |cw z| ≤ 2 := by
  rw [Work.Spaces.Iz, Set.mem_Ici] at hz
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : |z - 1| ≤ z + 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [cw, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (le_of_lt h1), div_le_iff₀ h1]
  linarith

/-- `cw` is measurable. -/
private theorem measurable_cw : Measurable cw := by
  change Measurable (fun z : ℝ => 2 * (z - 1) / (1 + z))
  fun_prop

/-! ## Mixed honesty from the diagonal honesties -/


/-! ## The bounded weight `cw` -/

/-- **`IPMem (cw · g) (cw · g)` from `IPMem g g`.**  Since `|cw| ≤ 2` on `[0,∞)`, the extra
factor is bounded: pointwise `(cw z · g)² ≤ 4 g²`, and the `z`-integrand of the pair is
`cw z²` times an integrable function. -/
theorem IPMem_cw_mul_diag {g : ℝ → ℝ → ℝ} (hg : IPMem g g) :
    IPMem (fun z θ => cw z * g z θ) (fun z θ => cw z * g z θ) := by
  have hA : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * w2 z * sig θ)
      Work.Spaces.Iz := hg.2
  constructor
  · intro z hz
    refine ((hg.1 z hz).const_mul (cw z ^ 2)).congr (Eventually.of_forall (fun θ => ?_))
    ring
  · have hcm : Measurable (fun z : ℝ => cw z ^ 2) := by
      change Measurable (fun z : ℝ => (2 * (z - 1) / (1 + z)) ^ 2)
      fun_prop
    have hbd : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), ‖cw z ^ 2‖ ≤ (4 : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := abs_cw_le_two hz
      nlinarith [abs_nonneg (cw z), sq_abs (cw z)]
    have hbdd : IntegrableOn (fun z => cw z ^ 2 * (∫ θ in Work.Spaces.Iθ,
        g z θ * g z θ * w2 z * sig θ)) Work.Spaces.Iz :=
      hA.bdd_mul hcm.aestronglyMeasurable hbd
    refine hbdd.congr (Eventually.of_forall (fun z => ?_))
    show cw z ^ 2 * (∫ θ in Work.Spaces.Iθ, g z θ * g z θ * w2 z * sig θ)
      = ∫ θ in Work.Spaces.Iθ, (cw z * g z θ) * (cw z * g z θ) * w2 z * sig θ
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-! ## The four pairings of `I₁` -/


end Work.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.C0_sq_le_EDthW_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Measurability of `D_θ f · w` for `SmoothQuad` data

`D_θ` preserves genuine `C^∞`-smoothness on the open quadrant
(`Work.FTS.LocData.contDiffOn_Dth`), and on the open quadrant the weight `w` is continuous with
no singularity, so `D_θ f · w` is continuous there; the quadrant is a.e. all of `Iz ×ˢ Iθ`. -/



/-! ## The bound -/


end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.mixed_zmul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.E2Bound

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-! ### Auxiliary lemmas

The two private lemmas below are the route (i)–(iii) of the docstring of `mixed_zmul`:
the unconditional scalar linearity of `deriv`, and the commutation of `D_θ^i` with
multiplication by a factor depending only on `z`. -/

/-- `deriv` is scalar homogeneous **unconditionally**, unlike Mathlib's `deriv_const_mul`,
which needs differentiability: if `f` is not differentiable at `x` then neither is `c * f`
for `c ≠ 0`, so both sides are `0`. -/
private theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

/-- `D_θ^i` commutes with multiplication by a factor depending only on `z`.  No smoothness
is needed: the only ingredient is the unconditional scalar linearity of `deriv`. -/
private theorem DthIter_zmul (i : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => a z * f z θ)
      = fun z θ => a z * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [Work.Spaces.DthIter_succ] at ih ⊢
      rw [ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_uncond]
      ring

/-- Leibniz expansion of `D_z^j D_θ^i (a · f)` when `a` depends only on `z`.

`D_θ` commutes with multiplication by a `z`-only factor, so after applying `D_θ^i` the
problem is `D_z^j (a · (D_θ^i f))`, which is the binomial expansion for the one-variable
operator `Zop = z ∂_z` acting on `a`:
`D_z^j(a·g) = ∑_{b≤j} (j.choose b) · (Zop^b a) · D_z^{j-b} g`.

ROUTE.
* (i) prove locally (private) `DthIter_zmul : DthIter i (fun z θ => a z * f z θ)
  = fun z θ => a z * DthIter i f z θ` by induction on `i`; the step is the *unconditional*
  scalar linearity of `deriv`, `deriv (fun y => c * g y) x = c * deriv g x` (if `c ≠ 0` and
  `g` is not differentiable at `x` then neither is `c * g`, and both sides are `0`) — see
  `deriv_const_mul_uncond` in `Submission/Work/FTS/LocData/HkIntegrand_const_mul.lean` for the
  exact 12-line argument.  No smoothness is needed for this identity.
* (ii) Apply the general one-operator Leibniz rule
  `Work.Spaces.DerivLike.iterate_mul Work.FTS.LocData.Zop_DerivLike_smoothZd
   Work.FTS.LocData.SmoothZsm_FunClass j haSlice hgSlice hz` with base set `Set.Ioi (-1)`
  (note `hz : z ∈ Set.Ioi (-1)`; do NOT try to use `DzIter_mul_smoothQuad`, whose hypothesis is
  the weaker-set `z ∈ Iz = Ici 0`), where `haSlice := ha.curry_z hθ` is the `C^∞`-smoothness of
  `fun z => a z` and `hgSlice := (hf.DthIter i).curry_z hθ` that of
  `fun z => DthIter i f z θ`.  Combine it with step (i) to express
  `mixed j i (fun z θ => a z * f z θ) z θ = DzIter j (fun z θ => a z * DthIter i f z θ) z θ`.
* (iii) rewrite `DzIter b (fun z θ => a z) z θ = Zop^[b] a z` by
  `congrFun (Work.FTS.LocData.Zop_iterate_slice b (fun z θ => a z) θ) z` and
  `DzIter (j - b) (DthIter i f) = mixed (j - b) i f` by `rfl`.

The imports are listed in `depends_on`.  Nothing of the requester's own machinery is needed and
the file must be self-contained (do not import the requester's files). -/
theorem mixed_zmul (j i : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (ha : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => a z))
    (hf : Work.FTS.LocData.SmoothQuad f) :
    Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (Work.Spaces.Zop^[b] a z * Work.Spaces.mixed (j - b) i f z θ) := by
  -- the two `z`-slices at `θ`, which are `C^∞` on `(-1,∞)`
  have haS := ha.curry_z hθ
  have hfS := (hf.DthIter i).curry_z hθ
  -- the one-operator Leibniz rule for `Zop = z ∂_z` at `z`
  have key := (Work.Spaces.DerivLike.iterate_mul Work.FTS.LocData.Zop_DerivLike_smoothZd
    Work.FTS.LocData.SmoothZsm_FunClass j haS hfS) hz
  -- step (i): `D_θ^i` commutes with the `z`-only factor `a`
  have hL : Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
      = Work.Spaces.Zop^[j] ((fun z : ℝ => a z)
          * (fun z : ℝ => Work.Spaces.DthIter i f z θ)) z := by
    rw [Work.Spaces.mixed, DthIter_zmul i a f]
    exact congrFun (Work.FTS.LocData.Zop_iterate_slice j
      (fun z θ => a z * Work.Spaces.DthIter i f z θ) θ) z
  rw [hL, key]
  -- step (iii): identify the two factors of each summand
  apply Finset.sum_congr rfl
  intro b hb
  have h1 : Work.Spaces.Zop^[b] (fun z : ℝ => a z) z = Work.Spaces.Zop^[b] a z := rfl
  have h2 : Work.Spaces.Zop^[j - b] (fun z : ℝ => Work.Spaces.DthIter i f z θ) z
      = Work.Spaces.mixed (j - b) i f z θ := by
    rw [Work.Spaces.mixed]
    exact (congrFun (Work.FTS.LocData.Zop_iterate_slice (j - b)
      (Work.Spaces.DthIter i f) θ) z).symm
  rw [h1, h2]

end Work.FTS.CoercivityFix.E2Bound
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.B_sq_prod_eq_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm


end Work.FTS.CoercivityFix.Transfer.E2norm
end
-- ===== merged: Submission.Work.FTS.EllSol.L12densIntegrableNoAlpha =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

set_option linter.unusedVariables false

/-- The open quadrant `(0,∞) × (0,π/2)` (re-exported from `Work.FTS.H2.Qd`, the single owner
of this notation, so that the proof below reads exactly as in the sibling file). -/
abbrev Qd : Set (ℝ × ℝ) := Work.FTS.H2.Qd

/-- `SmoothQuad` gives continuity of the uncurried datum on the open quadrant `Qd`. -/
private lemma continuousOn_uncurry_Qd {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (Function.uncurry g) Qd := by
  have h := hsm
  rw [Work.FTS.LocData.SmoothQuad] at h
  exact h.continuousOn.mono (fun p hp => by
    simp only [Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩)

/-! ## Pointwise domination of `g²` by the `ℋ⁴`-integrand

The `D_z⁰`-term of `HkIntegrand α 4 g` carries the weight `w/sin(2θ)^{η/2}`; since
`sin(2θ)^{η/2} ≤ 1` and `w ≥ 1` on the quadrant, this term dominates `g² w²`, hence
`g²` is dominated by `HkIntegrand/(w s)²`.  The radial weight `w s = (1+s)²/s²` is exactly
what absorbs the `1/s` of the density in the Cauchy–Schwarz step. -/

/-- On the open quadrant, `(g s θ)² ≤ HkIntegrand α 4 g s θ / (w s)²`. -/
private lemma g_sq_le_HkIntegrand_div_w_sq (α : ℝ) (g : ℝ → ℝ → ℝ) {s θ : ℝ} (hs : 0 < s)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ / (Work.Spaces.w s) ^ 2 := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
  have hSpos : 0 < S := by rw [hSdef]; exact Real.rpow_pos_of_pos hsin _
  have hSsq : S ^ 2 ≤ 1 := by
    have h2 : S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
      rw [hSdef, ← Real.rpow_natCast, ← Real.rpow_mul hsin.le]; norm_num
    calc S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := h2
      _ ≤ 1 := Real.rpow_le_one hsin.le (Real.sin_le_one _) (le_of_lt Work.Spaces.eta_pos)
  have hkey : (g s θ * (Work.Spaces.w s / S)) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
    simpa only [Work.Spaces.DzIter_zero] using
      Work.Spaces.sq_le_HkIntegrand_z α 4 g s θ 0 (by norm_num)
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hstep : (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
    calc (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        ≤ (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 / S ^ 2 := by
          rw [le_div_iff₀ (pow_pos hSpos 2)]
          nlinarith [mul_nonneg (sq_nonneg (g s θ)) (sq_nonneg (Work.Spaces.w s)), hSsq]
      _ = (g s θ * (Work.Spaces.w s / S)) ^ 2 := by
          rw [mul_pow, div_pow, mul_div_assoc]
      _ ≤ _ := hkey
  exact (le_div_iff₀ (pow_pos hwpos 2)).mpr hstep

/-! ## The pointwise bound on the density -/

/-- **The pointwise bound on the `L₁₂`-density.**  For `g` smooth on the open quadrant and
`g ∈ ℋ⁴`, and for `s > 0`,

`|L12dens g s| ≤ (√(∫_θ K(θ)² dθ) + 1)·(s/(1+s)²)·√(∫_θ HkIntegrand α 4 g s θ)`.

The angular integral is bounded by Cauchy–Schwarz in `θ` (`Work.Spaces.cs_integral`)
against `Ktheta ∈ L²` and the slice `L²`-norm `√(∫_θ (g s θ)²)`, which in turn is dominated
by `√(∫_θ HkIntegrand α 4 g s θ)/w s` through the pointwise domination above; the factor
`(1/(s·w s)) = s/(1+s)²` is the sublinear weight at the origin that makes the density
integrable there. -/
private lemma L12dens_abs_le_quad (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ}
    (hs : 0 < s) :
    |Work.Elliptic.L12dens g s|
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
        * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
  have hcontg : ContinuousOn (Function.uncurry g) Qd := continuousOn_uncurry_Qd hsm
  have haesm : AEStronglyMeasurable (fun θ => g s θ) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hcontg hs
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hw1 : 1 ≤ Work.Spaces.w s := Work.Elliptic.one_le_w hs
  have hpk : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ / (Work.Spaces.w s) ^ 2 :=
    Work.Elliptic.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => g_sq_le_HkIntegrand_div_w_sq α g hs h0 h1)
  -- the θ-slice of `g²` is integrable on `Iθ`, dominated by the `ℋ⁴`-integrand
  have hSqInt : IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ := by
    refine Integrable.mono' (hmem.1 s hs.le) (haesm.pow 2) ?_
    filter_upwards [hpk] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    refine le_trans hθ ?_
    rw [div_le_iff₀ (pow_pos hwpos 2)]
    calc Work.Spaces.HkIntegrand α 4 g s θ
        = Work.Spaces.HkIntegrand α 4 g s θ * 1 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 4 g s θ * (Work.Spaces.w s) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [hw1]) (Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
  have hKmem : MemLp (fun θ => Work.Elliptic.Ktheta θ) 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      Work.Elliptic.continuous_ktheta.aestronglyMeasurable).mpr
      ((Work.Elliptic.continuous_ktheta.continuousOn.pow 2).integrableOn_compact isCompact_Icc)
  have hGmem : MemLp (fun θ => g s θ) 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesm).mpr hSqInt
  have hcs := Work.Spaces.cs_integral hKmem hGmem
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    integral_nonneg (fun θ => sq_nonneg _)
  have hH : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ :=
    integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
  have hintle : ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) / (Work.Spaces.w s) ^ 2 := by
    have h := MeasureTheory.integral_mono_ae hSqInt ((hmem.1 s hs.le).div_const _) hpk
    rwa [MeasureTheory.integral_div] at h
  -- Cauchy–Schwarz in the angle, then the slice `L²`-bound
  have hab : |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s) := by
    have h1 : |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by
      calc |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ|
          = Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)) := Real.sqrt_le_sqrt hcs
        _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := Real.sqrt_mul hA _
    have h2 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s := by
      calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)
          ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
              / (Work.Spaces.w s) ^ 2) := Real.sqrt_le_sqrt hintle
        _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
              / Real.sqrt ((Work.Spaces.w s) ^ 2) := Real.sqrt_div hH _
        _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
              / Work.Spaces.w s := by
            rw [Real.sqrt_sq_eq_abs, abs_of_pos hwpos]
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
  have key : (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s)) / s
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
    rw [Work.Spaces.w]; field_simp; try ring
  rw [Work.Elliptic.L12dens_eq_angMoment_div, Work.Elliptic.angMoment, abs_div, abs_of_pos hs]
  calc |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ| / s
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s)) / s := by
        rw [div_le_div_iff_of_pos_right hs]; exact hab
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := key
    _ ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1) * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)

/-! ## A.e. strong measurability of the density

The joint integrand `(s,θ) ↦ K(θ)·g(s,θ)/s` is continuous on the open quadrant, hence a.e.
strongly measurable for `(volume.restrict Iz).prod (volume.restrict Iθ)`
(`Work.Spaces.aesm_of_continuousOn_Qd`); Fubini measurability of the partial integral
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) then gives the a.e. strong
measurability of `s ↦ ∫_θ K(θ)·g(s,θ)/s = L12dens g s` for `volume.restrict Iz`. -/

/-- `L12dens g` is a.e. strongly measurable on `Iz = [0,∞)` for `SmoothQuad` data. -/
private lemma L12dens_aesm (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g) :
    AEStronglyMeasurable (Work.Elliptic.L12dens g) (volume.restrict Work.Spaces.Iz) := by
  have hcontg : ContinuousOn (Function.uncurry g) Qd := continuousOn_uncurry_Qd hsm
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2) Qd :=
    Work.Elliptic.continuous_ktheta.comp_continuousOn continuous_snd.continuousOn
  have hF : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * g p.1 p.2 / p.1) Qd :=
    (h1.mul hcontg).div continuousOn_fst (fun p hp => ne_of_gt hp.1)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * g p.1 p.2 / p.1) hF
  have h := hjoint.integral_prod_right' (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
  convert h using 1
  funext z
  rfl

/-! ## The main theorem -/


end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeColl.pairFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeColl

/-! ## The `ψ_δ''`-term of the truncated chain -/

/-- The angular second-derivative term of the truncated chain for the bump `psiD δ`:
`W_χδ = ∫_z χ w² ∫_θ σ θ · ψ_δ''(θ) · (z ∂_z u)²`.  This is the term whose bound by the
endpoint collar energies is the only place where the Hardy-type rate of the slices of `z∂_z u`
is used. -/
def Wtr (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2),
        sigθ θ * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2

/-! ## The angular bump `psiD δ` -/

theorem psiD_apply (δ θ : ℝ) :
    psiD δ θ = Real.smoothTransition ((θ - δ / 4) / (δ / 4))
      * Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4)) := rfl

/-- `psiD δ` is `C²` on the line (for every `δ`, including the degenerate `δ = 0`). -/
theorem psiD_contDiff (δ : ℝ) : ContDiff ℝ 2 (psiD δ) := by
  have h1 : ContDiff ℝ 2 (fun θ : ℝ => (θ - δ / 4) / (δ / 4)) :=
    (contDiff_id.sub contDiff_const).div_const _
  have h2 : ContDiff ℝ 2 (fun θ : ℝ => ((Real.pi / 2 - δ / 4) - θ) / (δ / 4)) :=
    (contDiff_const.sub contDiff_id).div_const _
  have h3 := (Real.smoothTransition.contDiff (n := 2)).comp h1
  have h4 := (Real.smoothTransition.contDiff (n := 2)).comp h2
  exact h3.mul h4

theorem psiD_nonneg (δ θ : ℝ) : 0 ≤ psiD δ θ :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem psiD_le_one (δ θ : ℝ) : psiD δ θ ≤ 1 := by
  have h1 := Real.smoothTransition.le_one ((θ - δ / 4) / (δ / 4))
  have h2 := Real.smoothTransition.nonneg (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))
  have h3 := Real.smoothTransition.le_one (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))
  have h4 := Real.smoothTransition.nonneg ((θ - δ / 4) / (δ / 4))
  rw [psiD_apply]
  nlinarith [h1, h2, h3, h4]


theorem psiD_eq_one_of_mem {δ θ : ℝ} (hδ : 0 < δ) (h1 : δ / 2 ≤ θ)
    (h2 : θ ≤ Real.pi / 2 - δ / 2) : psiD δ θ = 1 := by
  have hδ4 : 0 < δ / 4 := by linarith
  have hA : 1 ≤ (θ - δ / 4) / (δ / 4) := by
    rw [le_div_iff₀ hδ4]; linarith
  have hB : 1 ≤ ((Real.pi / 2 - δ / 4) - θ) / (δ / 4) := by
    rw [le_div_iff₀ hδ4]; linarith
  rw [psiD_apply, Real.smoothTransition.one_of_one_le hA,
    Real.smoothTransition.one_of_one_le hB, mul_one]



/-- `psiD δ` vanishes off the closed interval `[δ/4, π/2 - δ/4]`. -/
theorem psiD_eq_zero_of_notMem (δ θ : ℝ)
    (h : θ ∉ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4)) : psiD δ θ = 0 := by
  have key : ∀ {a b : ℝ}, a ≤ 0 → Real.smoothTransition a * b = 0 :=
    fun ha => by rw [Real.smoothTransition.zero_of_nonpos ha, zero_mul]
  have key' : ∀ {a b : ℝ}, b ≤ 0 → a * Real.smoothTransition b = 0 :=
    fun hb => by rw [Real.smoothTransition.zero_of_nonpos hb, mul_zero]
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rcases lt_trichotomy (δ / 4) 0 with h' | h' | h'
    · rw [psiD_apply]
      exact key' (le_of_lt (div_neg_of_pos_of_neg (show (0:ℝ) < (Real.pi / 2 - δ / 4) - θ by
        linarith [Real.pi_pos]) h'))
    · rw [psiD_apply, h', div_zero]
      exact key (le_refl (0 : ℝ))
    · rw [psiD_apply]
      exact key (le_of_lt (div_neg_of_neg_of_pos (show θ - δ / 4 < 0 by linarith) h'))
  · rcases lt_trichotomy (δ / 4) 0 with h' | h' | h'
    · rw [psiD_apply]
      exact key (le_of_lt (div_neg_of_pos_of_neg (show (0:ℝ) < θ - δ / 4 by
        linarith [Real.pi_pos]) h'))
    · rw [psiD_apply, h', div_zero]
      exact key (le_refl (0 : ℝ))
    · rw [psiD_apply]
      exact key' (le_of_lt (div_neg_of_neg_of_pos (show (Real.pi / 2 - δ / 4) - θ < 0 by
        linarith) h'))

theorem psiD_support_subset (δ : ℝ) :
    Function.support (psiD δ) ⊆ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4) :=
  Function.support_subset_iff.mpr fun θ hθ =>
    not_not.mp fun h => hθ (psiD_eq_zero_of_notMem δ θ h)

theorem psiD_tsupport_subset (δ : ℝ) :
    tsupport (psiD δ) ⊆ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4) := by
  rw [tsupport]
  exact closure_minimal (psiD_support_subset δ) isClosed_Icc

/-- For `0 < δ ≤ π/8` the support of `psiD δ` is contained in the smaller interval
`(δ/8, π/2 - δ/8)`, whose closure is a compact subset of `(0, π/2)`. -/
theorem psiD_tsupport_subset' {δ : ℝ} (hδ : 0 < δ) (_hδ2 : 4 * δ ≤ Real.pi) :
    tsupport (psiD δ) ⊆ Set.Ioo (δ / 8) (Real.pi / 2 - δ / 8) := by
  intro θ hθ
  have h := psiD_tsupport_subset δ hθ
  constructor
  · linarith [h.1]
  · linarith [h.2]

theorem psiD_tsupport_subset_Ioo {δ : ℝ} (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi) :
    tsupport (psiD δ) ⊆ Set.Ioo 0 (Real.pi / 2) := by
  intro θ hθ
  have h := psiD_tsupport_subset' hδ hδ2 hθ
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem psiD_hasCompactSupport (δ : ℝ) : HasCompactSupport (psiD δ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (psiD_support_subset δ)

/-- The bump tends to `1` pointwise as `δ → 0⁺`. -/
theorem psiD_tendsto_one (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Tendsto (fun δ : ℝ => psiD δ θ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hθ1 : 0 < θ := hθ.1
  have hθ2 : θ < Real.pi / 2 := hθ.2
  have h1 : (fun δ : ℝ => Real.smoothTransition ((θ - δ / 4) / (δ / 4)))
      =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * θ by linarith)] with δ hδ
    have hδ4 : 0 < δ / 4 := by linarith [hδ.1]
    have hA : 1 ≤ (θ - δ / 4) / (δ / 4) := by
      rw [le_div_iff₀ hδ4]; linarith [hδ.2]
    rw [Real.smoothTransition.one_of_one_le hA]
  have h2 : (fun δ : ℝ => Real.smoothTransition
        (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * (Real.pi / 2 - θ) by linarith)]
      with δ hδ
    have hδ4 : 0 < δ / 4 := by linarith [hδ.1]
    have hB : 1 ≤ ((Real.pi / 2 - δ / 4) - θ) / (δ / 4) := by
      rw [le_div_iff₀ hδ4]; linarith [hδ.2]
    rw [Real.smoothTransition.one_of_one_le hB]
  have t1 : Tendsto (fun δ : ℝ => Real.smoothTransition ((θ - δ / 4) / (δ / 4)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : ℝ))).congr' h1.symm
  have t2 : Tendsto (fun δ : ℝ => Real.smoothTransition
      (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : ℝ))).congr' h2.symm
  have := t1.mul t2
  simpa only [psiD_apply, mul_one] using this

/-! ## The radial cut-off `cut n` -/

theorem cut_contDiff_one (n : ℕ) : ContDiff ℝ 1 (Work.FTS.EllipticEst.cut n) :=
  (Work.FTS.EllipticEst.cut_contDiff n).of_le (by norm_num)

theorem cut_support_subset_Icc (n : ℕ) :
    Function.support (Work.FTS.EllipticEst.cut n) ⊆
      Set.Icc (1 / ((n : ℝ) + 1)) (3 * ((n : ℝ) + 1)) := by
  refine Function.support_subset_iff.mpr fun z hz => ?_
  by_contra h
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact hz (Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_of_lt h))
  · exact hz (Work.FTS.EllipticEst.cut_apply_zero_of_ge n (le_of_lt h))

theorem cut_support_subset_Ioi (n : ℕ) :
    Function.support (Work.FTS.EllipticEst.cut n) ⊆ Set.Ioi (0 : ℝ) := by
  intro z hz
  have h := cut_support_subset_Icc n hz
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact lt_of_lt_of_le (by positivity) h.1

theorem cut_tsupport_subset_Ioi (n : ℕ) :
    tsupport (Work.FTS.EllipticEst.cut n) ⊆ Set.Ioi (0 : ℝ) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn
  intro z hz
  rw [tsupport] at hz
  have hle : z ∈ Set.Icc (1 / ((n : ℝ) + 1)) (3 * ((n : ℝ) + 1)) :=
    closure_minimal (cut_support_subset_Icc n) isClosed_Icc hz
  exact lt_of_lt_of_le h1 hle.1

theorem cut_hasCompactSupport (n : ℕ) : HasCompactSupport (Work.FTS.EllipticEst.cut n) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (cut_support_subset_Icc n)

/-! ## The angular weight `sigθ` -/

theorem sigθ_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ sigθ θ := by
  refine Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_) _
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

theorem sigθ_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < sigθ θ := by
  refine Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi ?_ ?_) _
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

theorem sigθ_eq_sig (θ : ℝ) : sigθ θ = Work.FTS.EllipticEst.AngSecond.sig θ := rfl

theorem wt_nonneg (z : ℝ) : 0 ≤ wt z := sq_nonneg _

end Work.FTS.EllipticEst.AeColl
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/Defs` — the vocabulary of the `I₁` bound in the weak class `AeData`

Notation of `Submission/Work/FTS/EllipticEst/AeI1Fts/I1Paper_mixed.lean`: with `u` a datum
smooth on the open quadrant `(0,∞) × (0,π/2)`,

* `U u = z ∂_z u` (definitionally `H2W.Ae.grad u`),
* `V u = z ∂_z ∂_θ u` (the mixed first-order slot whose `ℋ⁰`-honesty is the extra hypothesis
  of `I1Paper_mixed`),
* `Hh u = z ∂_z ∂_θθ u = ∂_θθ (U u)`,
* `AA u = z² ∂_zz u` (definitionally `H2W.Ae.rad2 u`), `BB u = ∂_θθ u`
  (definitionally `H2W.Ae.ang2 u`);
* the angular weights `σ = sigE = sin(2θ)^{-η}`, `σ₁ = sig1 = sin(2θ)^{-1-η}`,
  `σ₂ = sig2 = sin(2θ)^{-2-η}` with `η = Work.Spaces.eta = 99/100`;
* `thCut δ` is the pointwise angular cut-off `χ(2θ/δ)·χ(2(π/2-θ)/δ)`;
* `Fp u` is the `z`-integrand of the pointwise identity `(†)`
  `w²(A·B + cw·U·B + U·H) = ∂_z(z·U·B·w²)`, and `Fd u z θ = z·U·B·w²` is its primitive in `z`.

No proof is carried out here: this module only fixes the vocabulary shared by the target
`I1Paper_mixed` and the auxiliary lemmas it is assembled from.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false

/-- `U = z ∂_z u`. -/
def U (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz u z θ

/-- `V = z ∂_z ∂_θ u` (the mixed first-order slot). -/
def V (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z * Work.Spaces.pz (Work.Spaces.pth u) z θ

/-- `H = z ∂_z ∂_θθ u = ∂_θθ U`. -/
def Hh (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ

/-- `A = z² ∂_zz u`. -/
def AA (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ

/-- `B = ∂_θθ u`. -/
def BB (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 u

/-- `σ θ = sin(2θ)^{-η}`. -/
def sigE (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `σ₁ θ = sin(2θ)^{-1-η}`. -/
def sig1 (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))

/-- `σ₂ θ = sin(2θ)^{-2-η}`. -/
def sig2 (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))

/-- The open angular interval. -/
def Iθo : Set ℝ := Set.Ioo 0 (Real.pi / 2)

/-- The open quadrant. -/
def qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The pointwise angular cut-off `ψ_δ(θ) = χ(2θ/δ)·χ(2(π/2-θ)/δ)`, equal to `1` on
`[δ/2, π/2-δ/2]` and supported in `(0,π/2)`. -/
def thCut (δ θ : ℝ) : ℝ :=
  Real.smoothTransition (2 * θ / δ) * Real.smoothTransition (2 * (Real.pi / 2 - θ) / δ)

/-- The pointwise `z`-integrand of the `(†)`-identity. -/
def Fp (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (z ^ 2 * Work.Spaces.pzIter 2 u z θ) * Work.Spaces.pthIter 2 u z θ
    + Work.FTS.EllipticEst.AngSecond.cw z * (z * Work.Spaces.pz u z θ)
        * Work.Spaces.pthIter 2 u z θ
    + (z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)

/-- The pointwise `z`-integrand whose derivative is `w²·Fp`. -/
def Fd (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  z * (z * Work.Spaces.pz u z θ) * Work.Spaces.pthIter 2 u z θ * (Work.Spaces.w z) ^ 2

end Work.FTS.EllipticEst.AeI1Fts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.cut_deriv_tendsto_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

open MeasureTheory Set Filter
open scoped Topology


end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngClean.I1_cut_alt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# The radial cut-off identity for `I₁`, from scratch

This module proves `I1_cutoff_identity_alt`, the cut-off identity

  `IP (z² ∂_z²Ψ · χ_n) (∂_θθΨ) = - ∫_z ∫_θ σ θ · nice n Ψ z θ`,

directly from the vocabulary of `I1_defs`:

* `slice_nice_ibp_alt` is the one-dimensional integration by parts at a fixed angle
  (`slice_ibp_halfline` + `pz_mul_Dv_eq_nice`),
* `swap_IP_cut_alt`, `swap_nice_alt` exchange the two iterated integrals (Fubini), the
  integrands being supported in the compact band `[1/(2(n+1)), 4(n+1)]` of `χ_n`, where they
  are dominated by `C · |σ θ|` — a product of two integrable functions.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Real ContDiff

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The open quadrant `(0,∞) × (0,π/2)`: every integrand below is continuous there (the two
weights `w²` and `σ` are singular only on its boundary). -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The lower end of the compact band on which the cut-off `χ_n` lives. -/
abbrev zlo (n : ℕ) : ℝ := 1 / (2 * (n + 1 : ℝ))

/-- The upper end of the compact band on which the cut-off `χ_n` lives. -/
abbrev zhi (n : ℕ) : ℝ := 4 * (n + 1 : ℝ)




/-! ## Continuity on the open quadrant -/

theorem continuousOn_uncurry_Qd {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g) :
    ContinuousOn (Function.uncurry g) Qd := by
  refine hg.continuousOn.mono ?_
  intro p hp
  have h1 : (0 : ℝ) < p.1 := hp.1
  have h2 : (0 : ℝ) < p.2 := hp.2.1
  have h3 : p.2 < Real.pi / 2 := hp.2.2
  refine ⟨?_, ?_, ?_⟩
  · show (-1 : ℝ) < p.1
    linarith
  · show (-1 : ℝ) < p.2
    linarith
  · show p.2 < Real.pi / 2 + 1
    linarith [Real.pi_pos]

theorem continuousOn_w2_Qd : ContinuousOn (fun p : ℝ × ℝ => w2 p.1) Qd := by
  have h : ContinuousOn (fun z : ℝ => w2 z) (Set.Ioi 0) := by
    unfold w2 Work.Spaces.w
    refine ContinuousOn.pow ?_ 2
    exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
      (continuous_id.pow 2).continuousOn
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  exact h.comp continuous_fst.continuousOn (fun p hp => hp.1)

theorem continuousOn_sig_Qd : ContinuousOn (fun p : ℝ × ℝ => sig p.2) Qd := by
  have h : ContinuousOn sig (Set.Ioo 0 (Real.pi / 2)) := by
    unfold sig
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ hθ
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])))
  exact h.comp continuous_snd.continuousOn (fun p hp => hp.2)






/-! ## Integrability on the product, from compact support and a bound -/






/-! ## The one-dimensional integration by parts at a fixed angle -/


/-! ## Fubini for the two integrands -/



/-! ## The cut-off identity -/


end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.chiDerivLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A cutoff family whose weighted derivative mass tends to `0`

For `g ∈ L¹(0,∞)` we build a sequence of `C¹` cutoffs `χ_n`, of compact support inside `(0,∞)`,
with `0 ≤ χ_n ≤ 1`, monotone in `n`, tending to `1` pointwise on `(0,∞)`, and such that

`∫_{z>0} |χ_n'(z)| · (z |g z|) dz → 0`.

The family used is the in-tree `Work.FTS.EllipticEst.cut n`: its derivative satisfies the uniform
bound `|z · (cut n)' z| ≤ K` (`AngSecond.cut_deriv_uniform`), and it vanishes identically where
the cutoff is flat-`1`.  Hence the integrand `|(cut n)' z| · z |g z| = |z (cut n)' z| · |g z|`
is dominated by `K |g| ∈ L¹` and converges pointwise to `0` (for each fixed `z > 0` the cutoff
is eventually `1` on a neighbourhood of `z`), so dominated convergence gives the limit.  The key
point is that `|z (cut n)' z| ≤ K` is *uniform* in `n`.
-/

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

open MeasureTheory Set Filter



end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.pthSlotInt_of_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces

open MeasureTheory Set
open scoped Real Topology

/-- The angular weight `sin(2θ)^c` is continuous on the open quadrant `(0,∞) × (0,π/2)`
(the base `sin(2θ)` is strictly positive there). -/
private theorem continuousOn_sin_two_rpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  refine hsin.rpow_const (fun p hp => Or.inl ?_)
  rw [Set.mem_prod] at hp
  obtain ⟨-, h0, h1⟩ := hp
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

/-- The iterated `θ`-derivative of a datum which is `C^∞` on the open quadrant is continuous
on the open quadrant: `∂_θ` preserves `C^∞` there (`LocData.contDiffOn_pth`). -/
private theorem continuousOn_uncurry_pthIter {g : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (m : ℕ) :
    ContinuousOn (Function.uncurry (Work.Spaces.pthIter m g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hV : IsOpen (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pthIter m g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    induction m with
    | zero => exact hF
    | succ k ih =>
        rw [Work.Spaces.pthIter_succ]
        exact Work.FTS.LocData.contDiffOn_pth hV ih
  exact hcd.continuousOn

/-- The slot `θ ↦ (∂_θ^m g z θ)^2 · sin(2θ)^q` is almost everywhere strongly measurable on
`Iθ` for `z > 0`: it is continuous on the open interval `(0,π/2)`, which exhausts `Iθ` up to
the two null endpoints. -/
private theorem aesm_pthIter_sq_mul_sin_rpow {g : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (m : ℕ) (q : ℝ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => (Work.Spaces.pthIter m g z θ) ^ 2 *
      (Real.sin (2 * θ)) ^ q) (volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pthIter m g p.1 p.2) ^ 2 *
      (Real.sin (2 * p.2)) ^ q) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((continuousOn_uncurry_pthIter hF m).pow 2).mul (continuousOn_sin_two_rpow_Qd q)
  exact Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (Work.Spaces.pthIter m g p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ q)
    hcont hz

theorem pthSlotInt_of_HkMem {α : ℝ} (hα : 0 < α) {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hm : Work.Spaces.HkMem α k g) {z : ℝ} (hz : 0 < z) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter m g z θ) ^ 2 *
      (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  -- the a.e. pointwise chain, with a constant depending on `m` only
  obtain ⟨C, hCpos, hC⟩ :=
    Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand m hm1
  -- `g` is `C^∞` on the open quadrant in the honest (all finite orders) sense
  have hF : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_iff_forall_nat_le.mpr (fun n _ => hg n)
  have hzmem : z ∈ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz, Set.mem_Ici]
    exact le_of_lt hz
  -- the radial constant `w(z)^2` is strictly positive
  have hw : 0 < (Work.Spaces.w z) ^ 2 := by
    have hz2 : (0 : ℝ) < z ^ 2 := by positivity
    have h1 : 0 < (1 + z) ^ 2 := by positivity
    have h2 : 0 < Work.Spaces.w z := by
      rw [Work.Spaces.w]
      exact div_pos h1 hz2
    exact pow_pos h2 2
  -- the majorant: `HkIntegrand` is integrable in `θ` for every `z ∈ Iz` by `HkMem`
  have hint : Integrable (fun θ => (C / (Work.Spaces.w z) ^ 2) *
      Work.Spaces.HkIntegrand α k g z θ) (volume.restrict Work.Spaces.Iθ) :=
    (hm.1 z hzmem).const_mul (C / (Work.Spaces.w z) ^ 2)
  have haesm : AEStronglyMeasurable (fun θ => (Work.Spaces.pthIter m g z θ) ^ 2 *
      (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α))
      (volume.restrict Work.Spaces.Iθ) :=
    aesm_pthIter_sq_mul_sin_rpow hF m _ hz
  have hmem : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc
  have hpt := hC α g k hmk hα hg z hzmem
  refine hint.mono' haesm ?_
  filter_upwards [hpt, hmem] with θ hθ hθmem
  -- the slot is nonnegative on `Iθ`, so its norm is itself
  have hsin : 0 ≤ Real.sin (2 * θ) := by
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθmem
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθmem.1])
      (by linarith [hθmem.2, Real.pi_pos])
  have hslot : 0 ≤ (Work.Spaces.pthIter m g z θ) ^ 2 *
      (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)
  rw [Real.norm_eq_abs, abs_of_nonneg hslot, div_mul_eq_mul_div, le_div_iff₀ hw]
  calc (Work.Spaces.pthIter m g z θ) ^ 2 *
        (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α) * (Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m g z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) := by ring
    _ ≤ C * Work.Spaces.HkIntegrand α k g z θ := hθ

end Work.FTS.EllipticEst.Cores.Pieces
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.AeI1Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false

/-! ## The objects of the chain -/

/-- `U = z ∂_z Φ`. -/
def i1U (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Φ z θ

/-- `B = ∂_θ² Φ`. -/
def i1B (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Φ








/-! ## Identification of `HkSq α 0` with the weighted pairing -/

/-- `HkSq α 0 g` is the `w² σ`-weighted `L²`-mass of `g`, i.e. `⟨g, g⟩`. -/
theorem HkSq_zero_eq_IP (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g = Work.FTS.EllipticEst.AngSecond.IP g g := by
  have hI : Work.Spaces.HkIntegrand α 0 g
      = fun z θ => (g z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    funext z θ
    simp only [Work.Spaces.HkIntegrand]
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Work.Spaces.DzIter_zero]
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
  rw [Work.Spaces.HkSq, hI, ← Work.Spaces.L2Sq,
    Work.FTS.EllipticEst.AngSecond.L2Sq_mul_W]

/-! ## Elementary nonnegativity -/




end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.AeCutErr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeProof

open scoped Topology
open Filter MeasureTheory

/-!
## The truncation error of the radial cut-off family `cut n`, with the weight `w`

This file proves `AeCutErr`: for a nonnegative measurable `E` with `E ∈ L¹(Iz)` and
`w²E ∈ L¹(Iz)` (where `w z = (1+z)²/z²`), the truncation error

`Err n = ∫_z (2|(cut n)'| |(z²w²)'| + |(cut n)''| z²w²) E + ∫_z |(cut n)'| (z w²) E`

tends to `0`.

The proof does not need the (fine) structure of the two transition bands of `cut n`.
It uses only

* the two *uniform* bounds `|z (cut n)'(z)| ≤ K` and `|z² (cut n)''(z)| ≤ K₂`
  (`AngSecond.cut_deriv_uniform`, `AngularW.cutZ2Deriv2`), which together with
  `|(z²w²)'| ≤ 2 z w²` bound the integrand *globally* by `(5K + K₂) w² E`
  (the only place where `z > 0` is needed, the point `z = 0` being harmless);
* the pointwise convergence `(cut n)'(z) → 0`, `(cut n)''(z) → 0` for every fixed `z ≠ 0`,
  which follows from the *local constancy* of `cut n` at `z` for large `n`
  (`cut n ≡ 1` near `z > 0`, `cut n ≡ 0` near `z < 0`).

Dominated convergence with the integrable dominating function `(5K + K₂) w² E` then gives
the result.
-/

/-- `cut n` is identically `0` on a neighbourhood of every point `z < 1/(n+1)`. -/
private theorem cut_eventuallyEq_zero_of_lt (n : ℕ) {z : ℝ} (hz : z < 1 / ((n : ℝ) + 1)) :
    Work.FTS.EllipticEst.cut n =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
  have hpos : 0 < 1 / ((n : ℝ) + 1) - z := by linarith
  filter_upwards [Metric.ball_mem_nhds z hpos] with y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  exact Work.FTS.EllipticEst.cut_apply_zero_of_le n (by
    have := (abs_lt.mp hy).2
    linarith)

/-- `cut n` is identically `1` on a neighbourhood of every point of the interval
`(2/(n+1), 2(n+1))`. -/
private theorem cut_eventuallyEq_one_of_mid (n : ℕ) {z : ℝ} (h1 : 2 / ((n : ℝ) + 1) < z)
    (h2 : z < 2 * ((n : ℝ) + 1)) :
    Work.FTS.EllipticEst.cut n =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
  have hpos : 0 < min (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z) / 2 := by
    have h : 0 < min (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z) :=
      lt_min (by linarith) (by linarith)
    linarith
  filter_upwards [Metric.ball_mem_nhds z hpos] with y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hya := (abs_lt.mp hy).1
  have hyb := (abs_lt.mp hy).2
  have hm1 := min_le_left (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z)
  have hm2 := min_le_right (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z)
  exact Work.FTS.EllipticEst.cut_eq_one_of_mem n (by linarith) (by linarith)

/-- If `cut n` is locally constant near `z`, then both its first and its second derivative
vanish at `z`. -/
private theorem cut_derivs_eq_zero_of_eventuallyEq {n : ℕ} {z c : ℝ}
    (h : Work.FTS.EllipticEst.cut n =ᶠ[𝓝 z] (fun _ => c)) :
    deriv (Work.FTS.EllipticEst.cut n) z = 0 ∧
      deriv (deriv (Work.FTS.EllipticEst.cut n)) z = 0 := by
  constructor
  · rw [h.deriv_eq, deriv_const]
  · rw [h.deriv.deriv_eq]
    simp [deriv_const]

/-- For a fixed `z > 0` the derivatives of `cut n` vanish at `z` for all large `n` (there
`cut n ≡ 1` on a neighbourhood of `z`). -/
private theorem eventually_cut_derivs_eq_zero {z : ℝ} (hz : 0 < z) :
    ∀ᶠ n : ℕ in atTop,
      deriv (Work.FTS.EllipticEst.cut n) z = 0 ∧
        deriv (deriv (Work.FTS.EllipticEst.cut n)) z = 0 := by
  have hsmall : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
    simpa only [mul_zero, mul_one_div] using h
  have h1 : ∀ᶠ n : ℕ in atTop, 2 / ((n : ℝ) + 1) < z := (tendsto_order.1 hsmall).2 z hz
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add
      tendsto_const_nhds
  have hbig : ∀ᶠ n : ℕ in atTop, 2 * ((n : ℝ) + 1) > z := by
    have h3 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)) atTop atTop :=
      hbase.const_mul_atTop (by norm_num)
    have := (tendsto_atTop.1 h3) (z + 1)
    filter_upwards [this] with n hn
    linarith
  filter_upwards [h1, hbig] with n hn1 hn2
  exact cut_derivs_eq_zero_of_eventuallyEq (cut_eventuallyEq_one_of_mid n hn1 hn2)

/-- `|(z²w²)'| ≤ 2 z w²` for `z > 0`. -/
private theorem abs_deriv_zsq_w_sq_le (z : ℝ) (hz : 0 < z) :
    |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
      ≤ 2 * (Work.Spaces.w z) ^ 2 * z := by
  have hz3 : (0 : ℝ) < z ^ 3 := by positivity
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have h1z3 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  rw [Work.FTS.EllipticEst.weight_algebra_fts.2.2.1 z (ne_of_gt hz), abs_div, abs_of_pos hz3,
    div_le_iff₀ hz3, Work.Spaces.w]
  rw [show (2 : ℝ) * ((1 + z) ^ 2 / z ^ 2) ^ 2 * z * z ^ 3 = 2 * (1 + z) ^ 4 by
    field_simp]
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (le_of_lt h1z3)]
  have habs : |z - 1| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
  calc (2 * |z - 1|) * (1 + z) ^ 3 ≤ (2 * (1 + z)) * (1 + z) ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (le_of_lt h1z3)
    _ = 2 * (1 + z) ^ 4 := by ring

/-! ### Measurability of the two integrands -/

private theorem measurable_zsq_w_sq : Measurable (fun z : ℝ => z ^ 2 * (Work.Spaces.w z) ^ 2) := by
  refine (measurable_id.pow_const 2).mul ?_
  have h : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
  rw [h]
  exact (((measurable_const.add measurable_id).pow_const 2).div (measurable_id.pow_const 2)).pow_const 2

private theorem measurable_z_mul_w_sq : Measurable (fun z : ℝ => z * (Work.Spaces.w z) ^ 2) := by
  refine measurable_id.mul ?_
  have h : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
  rw [h]
  exact (((measurable_const.add measurable_id).pow_const 2).div (measurable_id.pow_const 2)).pow_const 2

private theorem aestronglyMeasurable_aeCutErr1 (n : ℕ) {E : ℝ → ℝ}
    (hEm : MeasureTheory.AEStronglyMeasurable E (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ =>
        (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hg : Measurable (fun z : ℝ =>
        (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))) := by
    refine Measurable.add ?_ ?_
    · exact (measurable_const.mul (measurable_deriv (Work.FTS.EllipticEst.cut n)).abs).mul
        (measurable_deriv (fun z : ℝ => z ^ 2 * (Work.Spaces.w z) ^ 2)).abs
    · exact ((measurable_deriv (deriv (Work.FTS.EllipticEst.cut n))).abs).mul measurable_zsq_w_sq
  exact MeasureTheory.AEStronglyMeasurable.mul hg.aestronglyMeasurable hEm

private theorem aestronglyMeasurable_aeCutErr2 (n : ℕ) {E : ℝ → ℝ}
    (hEm : MeasureTheory.AEStronglyMeasurable E (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ => |deriv (Work.FTS.EllipticEst.cut n) z|
              * (z * (Work.Spaces.w z) ^ 2) * E z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hg : Measurable (fun z : ℝ => |deriv (Work.FTS.EllipticEst.cut n) z|
              * (z * (Work.Spaces.w z) ^ 2)) :=
    ((measurable_deriv (Work.FTS.EllipticEst.cut n)).abs).mul measurable_z_mul_w_sq
  exact MeasureTheory.AEStronglyMeasurable.mul hg.aestronglyMeasurable hEm

/-! ### The pointwise domination -/

/-- The first integrand of `AeCutErr` is dominated by `C · w² · E`. -/
private theorem aeCutErr_bound1 (E : ℝ → ℝ) (hE0 : ∀ z, 0 ≤ E z) {K K2 C : ℝ}
    (hCpos : 0 < C) (hC : 4 * K + K2 ≤ C)
    (hK : ∀ (n : ℕ) (z : ℝ), |z * deriv (Work.FTS.EllipticEst.cut n) z| ≤ K)
    (hK2 : ∀ (n : ℕ) (z : ℝ), |z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.cut n)) z| ≤ K2) :
    ∀ (n : ℕ) (z : ℝ),
      |(2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z| ≤ C * ((Work.Spaces.w z) ^ 2 * E z) := by
  intro n z
  by_cases hz : 0 < z
  · have hd1 : |deriv (Work.FTS.EllipticEst.cut n) z| * z ≤ K := by
      have h := hK n z
      rw [abs_mul, abs_of_pos hz] at h
      linarith [h]
    have hd2 : |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * z ^ 2 ≤ K2 := by
      have h := hK2 n z
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < z ^ 2 by positivity)] at h
      linarith [h]
    have hW := abs_deriv_zsq_w_sq_le z hz
    have e1 : 2 * |deriv (Work.FTS.EllipticEst.cut n) z|
        * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
        ≤ 4 * K * (Work.Spaces.w z) ^ 2 := by
      calc 2 * |deriv (Work.FTS.EllipticEst.cut n) z|
            * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
          ≤ 2 * |deriv (Work.FTS.EllipticEst.cut n) z|
            * (2 * (Work.Spaces.w z) ^ 2 * z) :=
            mul_le_mul_of_nonneg_left hW (by positivity)
        _ = (4 * (|deriv (Work.FTS.EllipticEst.cut n) z| * z)) * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ (4 * K) * (Work.Spaces.w z) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd1 (by norm_num)) (sq_nonneg _)
    have e2 : |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ K2 * (Work.Spaces.w z) ^ 2 := by
      calc |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
          = (|deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * z ^ 2) * (Work.Spaces.w z) ^ 2 := by
            ring
        _ ≤ K2 * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hd2 (sq_nonneg _)
    have hnn : 0 ≤ 2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    rw [abs_of_nonneg (mul_nonneg hnn (hE0 z))]
    calc (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z
        ≤ ((4 * K + K2) * (Work.Spaces.w z) ^ 2) * E z :=
          mul_le_mul_of_nonneg_right (by linarith [e1, e2]) (hE0 z)
      _ = (4 * K + K2) * ((Work.Spaces.w z) ^ 2 * E z) := by ring
      _ ≤ C * ((Work.Spaces.w z) ^ 2 * E z) :=
          mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg _) (hE0 z))
  · have hz0 : z < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨hd1, hd2⟩ :=
      cut_derivs_eq_zero_of_eventuallyEq (cut_eventuallyEq_zero_of_lt n hz0)
    rw [hd1, hd2]
    simp only [abs_zero, zero_mul, mul_zero, add_zero]
    exact mul_nonneg (le_of_lt hCpos) (mul_nonneg (sq_nonneg _) (hE0 z))

/-- The second integrand of `AeCutErr` is dominated by `C · w² · E`. -/
private theorem aeCutErr_bound2 (E : ℝ → ℝ) (hE0 : ∀ z, 0 ≤ E z) {K C : ℝ}
    (hCpos : 0 < C) (hC : K ≤ C)
    (hK : ∀ (n : ℕ) (z : ℝ), |z * deriv (Work.FTS.EllipticEst.cut n) z| ≤ K) :
    ∀ (n : ℕ) (z : ℝ),
      |(|deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)) * E z|
        ≤ C * ((Work.Spaces.w z) ^ 2 * E z) := by
  intro n z
  by_cases hz : 0 < z
  · have hd1 : |deriv (Work.FTS.EllipticEst.cut n) z| * z ≤ K := by
      have h := hK n z
      rw [abs_mul, abs_of_pos hz] at h
      linarith [h]
    have hnn : 0 ≤ |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) :=
      mul_nonneg (abs_nonneg _) (mul_nonneg (le_of_lt hz) (sq_nonneg _))
    rw [abs_of_nonneg (mul_nonneg hnn (hE0 z))]
    calc (|deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)) * E z
        ≤ (K * (Work.Spaces.w z) ^ 2) * E z :=
          mul_le_mul_of_nonneg_right (by
            calc |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)
                = (|deriv (Work.FTS.EllipticEst.cut n) z| * z) * (Work.Spaces.w z) ^ 2 := by ring
              _ ≤ K * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hd1 (sq_nonneg _))
            (hE0 z)
      _ = K * ((Work.Spaces.w z) ^ 2 * E z) := by ring
      _ ≤ C * ((Work.Spaces.w z) ^ 2 * E z) :=
          mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg _) (hE0 z))
  · have hz0 : z < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨hd1, _⟩ :=
      cut_derivs_eq_zero_of_eventuallyEq (cut_eventuallyEq_zero_of_lt n hz0)
    rw [hd1]
    simp only [abs_zero, zero_mul]
    exact mul_nonneg (le_of_lt hCpos) (mul_nonneg (sq_nonneg _) (hE0 z))

/-! ### The pointwise convergence -/

private theorem aeCutErr_lim1 (E : ℝ → ℝ) :
    ∀ z : ℝ, Tendsto (fun n : ℕ =>
        (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z) atTop (nhds 0) := by
  intro z
  by_cases hz : 0 < z
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_cut_derivs_eq_zero hz] with n hn
    rw [hn.1, hn.2]
    ring
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    have hz0 : z < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨hd1, hd2⟩ :=
      cut_derivs_eq_zero_of_eventuallyEq (cut_eventuallyEq_zero_of_lt n hz0)
    rw [hd1, hd2]
    ring

private theorem aeCutErr_lim2 (E : ℝ → ℝ) :
    ∀ z : ℝ, Tendsto (fun n : ℕ =>
        (|deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)) * E z)
      atTop (nhds 0) := by
  intro z
  by_cases hz : 0 < z
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_cut_derivs_eq_zero hz] with n hn
    rw [hn.1]
    ring
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    have hz0 : z < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨hd1, _⟩ :=
      cut_derivs_eq_zero_of_eventuallyEq (cut_eventuallyEq_zero_of_lt n hz0)
    rw [hd1]
    ring

/-- **The truncation error of the radial cut-off family tends to zero.**

For a nonnegative `E` on `Iz = [0,∞)` which is `AEStronglyMeasurable` and satisfies
`E, w²E ∈ L¹(Iz)` (`w z = (1+z)²/z²`), the truncation error made by the `n`-th cut-off `cut n`
in the radial integration by parts,

`Err n = ∫_z (2|(cut n)'| |(z²w²)'| + |(cut n)''| z²w²) E + ∫_z |(cut n)'| (z w²) E`,

tends to `0` as `n → ∞`.

Proof: the two uniform bounds `|z (cut n)'(z)| ≤ K` (`AngSecond.cut_deriv_uniform`) and
`|z²(cut n)''(z)| ≤ K₂` (`AngularW.cutZ2Deriv2`), together with `|(z²w²)'| ≤ 2 z w²`, dominate
the integrand by `(5K + K₂) w² E` — an integrable function.  For fixed `z > 0` the cut-off is
eventually equal to `1` near `z` (`cut_eq_one_of_mem`), so both derivatives vanish at `z` for
large `n`, while for `z ≤ 0` the cut-off is eventually (indeed always) `0` near `z`.  Hence the
integrand converges pointwise to `0` and dominated convergence applies. -/
theorem AeCutErr (E : ℝ → ℝ) (hE0 : ∀ z, 0 ≤ E z)
    (hEm : MeasureTheory.AEStronglyMeasurable E (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hE1 : MeasureTheory.IntegrableOn E Work.Spaces.Iz)
    (hE2 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * E z) Work.Spaces.Iz) :
    Filter.Tendsto (fun n : ℕ =>
        (∫ z in Work.Spaces.Iz, (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z)
        + (∫ z in Work.Spaces.Iz, |deriv (Work.FTS.EllipticEst.cut n) z|
              * (z * (Work.Spaces.w z) ^ 2) * E z))
      Filter.atTop (nhds 0) := by
  -- `hE1` is not needed: the domination only uses `w²E ∈ L¹`.
  have hE1int : MeasureTheory.IntegrableOn E Work.Spaces.Iz := hE1
  obtain ⟨K, hKpos, hKbd, -, -⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  obtain ⟨K2, hK2pos, hK2bd⟩ := Work.FTS.EllipticEst.AngularW.cutZ2Deriv2
  have hCpos : (0 : ℝ) < 20 * (K + K2 + 1) := by positivity
  have hC1 : 4 * K + K2 ≤ 20 * (K + K2 + 1) := by linarith
  have hC2 : K ≤ 20 * (K + K2 + 1) := by linarith
  have hX : Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
        (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z) atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (F := fun n z =>
        (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z)
      (f := fun _ => (0 : ℝ))
      (fun z => 20 * (K + K2 + 1) * ((Work.Spaces.w z) ^ 2 * E z))
      (fun n => aestronglyMeasurable_aeCutErr1 n hEm)
      (hE2.const_mul (20 * (K + K2 + 1)))
      (fun n => Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        exact aeCutErr_bound1 E hE0 hCpos hC1 hKbd hK2bd n z))
      (Filter.Eventually.of_forall (aeCutErr_lim1 E))
    simpa using h
  have hY : Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
        |deriv (Work.FTS.EllipticEst.cut n) z|
              * (z * (Work.Spaces.w z) ^ 2) * E z) atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (F := fun n z => (|deriv (Work.FTS.EllipticEst.cut n) z|
              * (z * (Work.Spaces.w z) ^ 2)) * E z)
      (f := fun _ => (0 : ℝ))
      (fun z => 20 * (K + K2 + 1) * ((Work.Spaces.w z) ^ 2 * E z))
      (fun n => aestronglyMeasurable_aeCutErr2 n hEm)
      (hE2.const_mul (20 * (K + K2 + 1)))
      (fun n => Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        exact aeCutErr_bound2 E hE0 hCpos hC2 hKbd n z))
      (Filter.Eventually.of_forall (aeCutErr_lim2 E))
    simpa using h
  simpa using hX.add hY

end Work.FTS.EllipticEst.H2W.AeProof
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SlotA.cwPairBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
-- (the former import of `AngSecond/I1_ibp.lean` is dropped: this file only used
-- `AngSecond.abs_cw_le_two` from it, which is now reproduced locally below.  Importing `I1_ibp`
-- pulled in `AngSecond/I1_cut_alt.lean`, whose declarations clash with the `AngClean/I1_cut_alt`
-- copy for every consumer that needs both — see the note at `abs_cw_le_two_Iz`.)

/-!
# The Cauchy–Schwarz bound on the transfer term of `I₁`

In the chain for the `I₁` lower bound (Elgindi, Annals **194** (2021), tex 873–890) the term
produced by the `(w²)'`-part of the radial integration by parts is

```
X = - ⟨U, cw·B⟩ ,      U = z∂_zu ,  B = ∂_θ²u ,  cw z = 2 - 4/(1+z) = 2(z-1)/(1+z) ,
```

with `⟨g,h⟩ = AngSecond.IP g h = ∫_z∫_θ g h w²σ` and `σ θ = sin(2θ)^{-η}`.  Since `|cw z| ≤ 2` on
`z ≥ 0` (`AngSecond.abs_cw_le_two`) and the pairing is Cauchy–Schwarz
(`AngSecond.IP_cauchy_schwarz`),

```
⟨cw·U, B⟩ ≤ 2 √⟨U,U⟩ √⟨B,B⟩ ,
```

which is the `hX` input of the algebraic core `H2W.Ae.i1Lower_algebra_eta` (whose `hX` is stated
as `X ≥ -2 √(A·B)` with `A = ⟨U,U⟩`, `B = ⟨B,B⟩`).

## Design

The only structural fact used is that `cw` depends on `z` alone, so that in the `θ`-integral it
can be pulled out (`Integrable.const_mul` / `integral_const_mul`); the `z`-marginal is then
integrable by `Integrable.mono'` against `K * ‖marginal‖` because `|cw| ≤ 2` on `Iz`.  This is the
content of `IPMem_const_mul_left` below, applied to `cw` and to `cw · U` (the latter via the
symmetric form `IPMem U (cw·U)`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SlotA

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- `cw z = 2(z-1)/(1+z) = 2 - 4/(1+z)` is continuous on `Iz = [0,∞)`. -/
theorem continuousOn_cw :
    ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.cw z) Work.Spaces.Iz := by
  have h1 : ContinuousOn (fun z : ℝ => 2 - 4 / (1 + z)) Work.Spaces.Iz := by
    refine continuousOn_const.sub ?_
    have h2 : ContinuousOn (fun z : ℝ => (1 + z : ℝ)) Work.Spaces.Iz := by fun_prop
    exact continuousOn_const.div h2 (fun z hz => by
      simp only [Work.Spaces.Iz, Set.mem_Ici] at hz
      positivity)
  refine h1.congr (fun z hz => ?_)
  have hz' : (1 : ℝ) + z ≠ 0 := by
    simp only [Work.Spaces.Iz, Set.mem_Ici] at hz
    positivity
  unfold Work.FTS.EllipticEst.AngSecond.cw
  field_simp
  ring

/-- `cw` is bounded by `2` on `Iz`.

(The statement and proof of `AngSecond.abs_cw_le_two` are reproduced here so that this file does
not import `AngSecond/I1_ibp.lean`: that module pulls in `AngSecond/I1_cut_alt.lean`, which
redeclares most of `AngClean/I1_cut_alt.lean` under the same namespace, and the two modules
together are a duplicate-declaration error for every consumer whose cone needs the
`AngClean`-side copy as well (e.g. `AeI1Fts/I1Paper_mixed.lean`).) -/
theorem abs_cw_le_two_Iz {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    |Work.FTS.EllipticEst.AngSecond.cw z| ≤ 2 := by
  have hz0 : (0 : ℝ) ≤ z := by
    simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : |z - 1| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Work.FTS.EllipticEst.AngSecond.cw, abs_div, abs_mul, abs_of_pos h1]
  rw [div_le_iff₀ h1]
  have h3 : |(2 : ℝ)| = 2 := by norm_num
  rw [h3]
  linarith

/-- **Honesty is preserved by multiplying the first slot by a `z`-only bounded factor.** -/
theorem IPMem_const_mul_left (c : ℝ → ℝ) (K : ℝ)
    (hc : ∀ z ∈ Work.Spaces.Iz, |c z| ≤ K)
    (hcaesm : AEStronglyMeasurable c (volume.restrict Work.Spaces.Iz))
    (U B : ℝ → ℝ → ℝ) (hUB : Work.FTS.EllipticEst.AngSecond.IPMem U B) :
    Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => c z * U z θ) B := by
  constructor
  · intro z hz
    refine ((hUB.1 z hz).const_mul (c z)).congr (Filter.Eventually.of_forall (fun θ => ?_))
    ring
  · set M : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, U z θ * B z θ
      * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ with hM
    have hMint : MeasureTheory.Integrable M (volume.restrict Work.Spaces.Iz) := hUB.2
    have haesm : AEStronglyMeasurable (fun z => c z * M z) (volume.restrict Work.Spaces.Iz) :=
      hcaesm.mul hMint.aestronglyMeasurable
    have hbound : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), ‖c z * M z‖ ≤ K * ‖M z‖ := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hc z hz) (abs_nonneg _)
    have hint : MeasureTheory.Integrable (fun z => c z * M z) (volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.mono' (hMint.norm.const_mul K) haesm hbound
    refine hint.congr (Filter.Eventually.of_forall (fun z => ?_))
    show c z * M z = ∫ θ in Work.Spaces.Iθ, (c z * U z θ) * B z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ
    have h1 : (∫ θ in Work.Spaces.Iθ, (c z * U z θ) * B z θ
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
        = ∫ θ in Work.Spaces.Iθ, c z * (U z θ * B z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      ring
    rw [h1, hM, MeasureTheory.integral_const_mul]

/-- **`IPMem` is symmetric in its two slots.** -/
theorem IPMem_symm {g h : ℝ → ℝ → ℝ} (hgh : Work.FTS.EllipticEst.AngSecond.IPMem g h) :
    Work.FTS.EllipticEst.AngSecond.IPMem h g := by
  constructor
  · intro z hz
    refine (hgh.1 z hz).congr (Filter.Eventually.of_forall (fun θ => ?_))
    ring
  · refine hgh.2.congr (Filter.Eventually.of_forall (fun z => ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    ring

/-- **The transfer pairing is at most `2√⟨U,U⟩√⟨B,B⟩`** — the `hX` input of
`H2W.Ae.i1Lower_algebra_eta`. -/
theorem IP_cw_le (U B : ℝ → ℝ → ℝ)
    (hUU : Work.FTS.EllipticEst.AngSecond.IPMem U U)
    (hBB : Work.FTS.EllipticEst.AngSecond.IPMem B B)
    (hUB : Work.FTS.EllipticEst.AngSecond.IPMem U B) :
    Work.FTS.EllipticEst.AngSecond.IP (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ) B
      ≤ 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U)
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) := by
  have hcw_aesm : AEStronglyMeasurable (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.cw z)
      (volume.restrict Work.Spaces.Iz) :=
    continuousOn_cw.aestronglyMeasurable measurableSet_Ici
  have hc : ∀ z ∈ Work.Spaces.Iz, |Work.FTS.EllipticEst.AngSecond.cw z| ≤ 2 :=
    fun z hz => abs_cw_le_two_Iz hz
  have hcwUB : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ) B :=
    IPMem_const_mul_left _ 2 hc hcw_aesm U B hUB
  have hcwUU : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ) :=
    IPMem_const_mul_left _ 2 hc hcw_aesm U (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
      (IPMem_symm (IPMem_const_mul_left _ 2 hc hcw_aesm U U hUU))
  -- ## `⟨cw·U, cw·U⟩ ≤ 4⟨U,U⟩`
  have hquad : Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
      ≤ 4 * Work.FTS.EllipticEst.AngSecond.IP U U := by
    have hinner : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
            * (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
        ≤ 4 * (∫ θ in Work.Spaces.Iθ, U z θ * U z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
      intro z hz
      have hR : MeasureTheory.IntegrableOn (fun θ => 4 * (U z θ * U z θ
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ))
          Work.Spaces.Iθ :=
        (hUU.1 z hz).const_mul 4
      have hL : MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
          * (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
          Work.Spaces.Iθ :=
        ((hUU.1 z hz).const_mul (Work.FTS.EllipticEst.AngSecond.cw z ^ 2)).congr
          (Filter.Eventually.of_forall (fun θ => by ring))
      have hpt : ∀ θ ∈ Work.Spaces.Iθ, (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
          * (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ
          ≤ 4 * (U z θ * U z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
        intro θ hθ
        have hw := Work.FTS.EllipticEst.AngSecond.w2_nonneg z
        have hs := Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
        have h2 := abs_cw_le_two_Iz hz
        have hcw2 : Work.FTS.EllipticEst.AngSecond.cw z ^ 2 ≤ 4 := by
          have h4 := pow_le_pow_left₀
            (abs_nonneg (Work.FTS.EllipticEst.AngSecond.cw z)) h2 2
          norm_num at h4
          exact h4
        have hnn : 0 ≤ U z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ :=
          mul_nonneg (mul_nonneg (sq_nonneg _) hw) hs
        calc (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
              * (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
              * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ
            = Work.FTS.EllipticEst.AngSecond.cw z ^ 2
              * (U z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
          _ ≤ 4 * (U z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ) :=
              mul_le_mul_of_nonneg_right hcw2 hnn
          _ = 4 * (U z θ * U z θ * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_mono_ae hL hR
        ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
          (Filter.Eventually.of_forall hpt))
    have hR : MeasureTheory.IntegrableOn (fun z => 4 * (∫ θ in Work.Spaces.Iθ, U z θ * U z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ))
        Work.Spaces.Iz :=
      hUU.2.const_mul 4
    have hout : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
            * (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
        ≤ ∫ z in Work.Spaces.Iz, 4 * (∫ θ in Work.Spaces.Iθ, U z θ * U z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
      refine MeasureTheory.integral_mono_ae hcwUU.2 hR ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact hinner z hz
    calc Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
              * (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
              * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, 4 * (∫ θ in Work.Spaces.Iθ, U z θ * U z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := hout
      _ = 4 * Work.FTS.EllipticEst.AngSecond.IP U U := by
          rw [MeasureTheory.integral_const_mul]
          rfl
  -- ## Cauchy–Schwarz and the square root
  have hcs := Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz hcwUU hBB hcwUB
  have hsqrt : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ))
      ≤ 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U) := by
    have h1 := Real.sqrt_le_sqrt hquad
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith [Real.sqrt_nonneg (4 : ℝ), h]
    rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4] at h1
  calc Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ) B
      ≤ |Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ) B| := le_abs_self _
    _ ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) := hcs
    _ ≤ (2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)


end Work.FTS.EllipticEst.H2W.SlotA
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RegQ.pth_EllResid_pointwise_smoothQuad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RegQ

open scoped Real Topology
open Filter

set_option autoImplicit false

/-!
# The two `θ`-derivatives of the residual `EllResid α F Ψ` in the class `SmoothQuad`

`EllResid α F Ψ = fun z θ => Ψ z θ - (1/(4α)) · sin(2θ) · L₁₂(F)(z)` is a `Ψ`-part, which is
`C^∞` on the open quadrant, minus a *radial* function `L₁₂(F)` times the *angular* profile
`sin 2θ`.  Differentiating in `θ` therefore only sees the angular factor:

  `∂_θ (EllResid α F Ψ)   = ∂_θΨ   - (1/(4α))·2cos 2θ·L₁₂(F)`,
  `∂_θ² (EllResid α F Ψ)  = ∂_θ²Ψ  + (1/α)·(sin 2θ·L₁₂(F))`.

This file proves both, *pointwise on the open quadrant* `z > -1`, `0 < θ < π/2`, from the only
smoothness hypothesis that is available in the localised-data chapter: `SmoothQuad Ψ` (genuine
`C^∞` on `Ioi (-1) ×ˢ Ioo 0 (π/2)`, i.e. `ContDiffOn ℝ smoothOrder`).  Nothing is assumed about
`F`: only `L₁₂(F)(z)` as a number occurs, and it is treated as a constant in `θ`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

/-! ## Auxiliary calculus: `SmoothQuad` and the `θ`-slices of the `∂_θ`-iterates -/




/-! ## Auxiliary calculus: the two elementary angular profiles -/

/-- `deriv (fun θ' => sin (2 θ')) θ = 2 cos (2 θ)`. -/
private theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_sin (2 * θ)).comp θ
      ((hasDerivAt_const (x := θ) (c := (2 : ℝ))).mul (hasDerivAt_id θ))

/-- `deriv (fun θ' => 2 cos (2 θ')) θ = -4 sin (2 θ)`. -/
private theorem hasDerivAt_two_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => 2 * Real.cos (2 * θ')) (-(4 * Real.sin (2 * θ))) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(2 * Real.sin (2 * θ))) θ := by
    simpa [Function.comp_def, mul_comm, mul_assoc] using
      (Real.hasDerivAt_cos (2 * θ)).comp θ
        ((hasDerivAt_const (x := θ) (c := (2 : ℝ))).mul (hasDerivAt_id θ))
  have h2 := h1.const_mul (2 : ℝ)
  have he : (2 : ℝ) * (-(2 * Real.sin (2 * θ))) = -(4 * Real.sin (2 * θ)) := by ring
  rwa [he] at h2

/-! ## The first `θ`-derivative of the residual -/


/-! ## The second `θ`-derivative of the residual -/


/-! ## The requested statement -/


end

end Work.FTS.EllipticEst.RegQ
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Shim.ExcessM_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The angular slice to which the one-dimensional Agmon inequality is applied -/

/-- The `θ`-slice `h_θ(z) = sin(2θ)^{-γ/2}·D_z^{k-1}D_θΨ(z,θ)` of the radial Agmon estimate. -/
private def hslice (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ → ℝ :=
  fun z => Work.Spaces.wTheta α θ * Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ) z θ



/-! ## Nonnegativity of the three integrands -/




/-! ## The three pointwise identities -/




/-! ## The pointwise-in-`θ` Agmon inequality for `EXM`, `PM`, `ZM` -/


/-! ## Two measure-theoretic steps -/



/-! ## The certificate -/


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Shim.ExcessR_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.Cert.DzAux

set_option autoImplicit false
set_option maxHeartbeats 1000000
-- `hPRz`, `hZRz` are part of the requested statement but are only used by its consumers.
set_option linter.unusedVariables false

/-! ## The one-dimensional identity `z²h'' = rDzIter 2 h - rDzIter 1 h` -/

/-- `rDzIter 2 h z = z h'(z) + z² h''(z)` for `z > 0`. -/
private lemma rDzIter_two_eq {h : ℝ → ℝ} (hh : ContDiffOn ℝ 2 h (Set.Ioi 0)) {z : ℝ}
    (hz : 0 < z) :
    Work.FTS.EllipticEst.rDzIter 2 h z = z * deriv h z + z ^ 2 * deriv (deriv h) z := by
  have hd1 : ContDiffOn ℝ 1 (deriv h) (Set.Ioi 0) :=
    hh.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdiff : DifferentiableAt ℝ (deriv h) z :=
    (hd1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hprod : HasDerivAt (fun y : ℝ => y * deriv h y)
      (deriv h z + z * deriv (deriv h) z) z := by
    have h := (hasDerivAt_id z).mul hdiff.hasDerivAt
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  change z * deriv (fun y : ℝ => y * deriv h y) z = _
  rw [hprod.deriv]
  ring

/-! ## The per-angle Agmon bound for the excess term -/


/-! ## The excess radial term of `D_z Ψ` -/


end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TanTheta.slice_poincare_eta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

set_option autoImplicit false

/-- **Cauchy–Schwarz on an interval.**  For a continuous real function `f` on `[a,b]` with
`a ≤ b`, the square of the integral of `f` is at most the length of the interval times the
integral of `f²`:

  `(∫_a^b f)² ≤ (b - a) · ∫_a^b f²`.

This is Cauchy–Schwarz applied to `f` and the constant function `1`.  The proof below is the
elementary one: with `c = (∫_a^b f)/(b-a)` one has
`0 ≤ ∫_a^b (f - c)² = ∫_a^b f² - 2c ∫_a^b f + c²(b-a)`, and substituting `c` yields
`c²(b-a) ≤ ∫_a^b f²`, i.e. `(∫_a^b f)² ≤ (b-a) ∫_a^b f²`. -/
theorem sq_integral_le (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    simp
  · have hba : 0 < b - a := sub_pos.mpr h
    have hfI : IntervalIntegrable f volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hab]
      exact hf
    set c : ℝ := (∫ t in a..b, f t) / (b - a) with hc
    have hcba : c * (b - a) = ∫ t in a..b, f t := by
      rw [hc]
      exact div_mul_cancel₀ _ (ne_of_gt hba)
    have h1 : IntervalIntegrable (fun t => (f t) ^ 2) volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hab]
      exact hf.pow 2
    have h2 : IntervalIntegrable (fun t => 2 * c * f t) volume a b := hfI.const_mul (2 * c)
    have h3 : IntervalIntegrable (fun t : ℝ => c ^ 2) volume a b := intervalIntegrable_const
    have hnn : 0 ≤ ∫ t in a..b, (f t - c) ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun t => sq_nonneg _)
    have hexp : (∫ t in a..b, (f t - c) ^ 2)
        = (∫ t in a..b, (f t) ^ 2) - 2 * c * (∫ t in a..b, f t) + c ^ 2 * (b - a) := by
      have e : (∫ t in a..b, (f t - c) ^ 2)
          = ∫ t in a..b, ((f t) ^ 2 - 2 * c * f t + c ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      rw [e, intervalIntegral.integral_add (h1.sub h2) h3, intervalIntegral.integral_sub h1 h2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hexp] at hnn
    have hkey : c ^ 2 * (b - a) ≤ ∫ t in a..b, (f t) ^ 2 := by
      have hh := hnn
      rw [← hcba] at hh
      nlinarith [hh]
    calc (∫ t in a..b, f t) ^ 2 = (c * (b - a)) ^ 2 := by rw [← hcba]
      _ = (c ^ 2 * (b - a)) * (b - a) := by ring
      _ ≤ (∫ t in a..b, (f t) ^ 2) * (b - a) := mul_le_mul_of_nonneg_right hkey hba.le
      _ = (b - a) * ∫ t in a..b, (f t) ^ 2 := by ring


end Work.FTS.EllipticEst.TanTheta
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.SlotVDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

/-! ## The open box and the smooth class -/

/-- The open box `(0,∞) × (-1, π/2+1)` on which the smoothness hypothesis of the mixed-slot
estimate lives. -/
abbrev V : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)

theorem isOpen_V : IsOpen V := isOpen_Ioi.prod isOpen_Ioo

theorem mem_V {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    (z, θ) ∈ V := ⟨hz, hθ⟩


/-- `f` is of class `C^∞` (the *genuine* smooth order `smoothOrder`, not analyticity) on the
open box `V`.  This is the class in which the whole proof is run. -/
abbrev SmV (f : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V




theorem SmV.contDiffAt {f : ℝ → ℝ → ℝ} (h : SmV f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry f) (z, θ) :=
  ContDiffOn.contDiffAt h (isOpen_V.mem_nhds (mem_V hz hθ))

/-! ## Closure of `SmV` -/

theorem SmV.pz {f : ℝ → ℝ → ℝ} (h : SmV f) : SmV (Work.Spaces.pz f) :=
  Work.FTS.LocData.contDiffOn_pz isOpen_V h

theorem SmV.pth {f : ℝ → ℝ → ℝ} (h : SmV f) : SmV (Work.Spaces.pth f) :=
  Work.FTS.LocData.contDiffOn_pth isOpen_V h

theorem SmV.Dz {f : ℝ → ℝ → ℝ} (h : SmV f) : SmV (Work.Spaces.Dz f) :=
  Work.FTS.LocData.contDiffOn_Dz isOpen_V h

theorem SmV.Dth {f : ℝ → ℝ → ℝ} (h : SmV f) : SmV (Work.Spaces.Dth f) :=
  Work.FTS.LocData.contDiffOn_Dth isOpen_V h

theorem SmV.DzIter {f : ℝ → ℝ → ℝ} (h : SmV f) (j : ℕ) :
    SmV (Work.Spaces.DzIter j f) :=
  Work.FTS.LocData.contDiffOn_DzIter isOpen_V h j

theorem SmV.DthIter {f : ℝ → ℝ → ℝ} (h : SmV f) (i : ℕ) :
    SmV (Work.Spaces.DthIter i f) :=
  Work.FTS.LocData.contDiffOn_DthIter isOpen_V h i

theorem SmV.mixed {f : ℝ → ℝ → ℝ} (h : SmV f) (j i : ℕ) :
    SmV (Work.Spaces.mixed j i f) :=
  Work.FTS.LocData.contDiffOn_mixed isOpen_V h j i

theorem SmV.pzIter {f : ℝ → ℝ → ℝ} (h : SmV f) (j : ℕ) : SmV (Work.Spaces.pzIter j f) := by
  induction j with
  | zero => simpa using h
  | succ j ih => simpa [Work.Spaces.pzIter] using ih.pz

theorem SmV.pthIter {f : ℝ → ℝ → ℝ} (h : SmV f) (i : ℕ) : SmV (Work.Spaces.pthIter i f) := by
  induction i with
  | zero => simpa using h
  | succ i ih => simpa [Work.Spaces.pthIter] using ih.pth

/-! ## Angular slices at a fixed level `z > 0` -/

/-- The angular slice of an `SmV` function is `C^∞` on the whole open angular interval. -/
theorem SmV.slice {f : ℝ → ℝ → ℝ} (h : SmV f) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => f z θ) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
  Work.FTS.LocData.contDiffOn_slice_θ h hz




/-! ## Locality on `V` -/

theorem Dz_congr_V {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz g)) (Function.uncurry (Work.Spaces.Dz g')) V := by
  intro y hy
  have hp := Work.Spaces.pz_congr_of_isOpen isOpen_V h hy
  show y.1 * Work.Spaces.pz g y.1 y.2 = y.1 * Work.Spaces.pz g' y.1 y.2
  rw [hp]


theorem DzIter_congr_V {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j g))
      (Function.uncurry (Work.Spaces.DzIter j g')) V := by
  induction j with
  | zero => exact h
  | succ j ih => exact Dz_congr_V ih


/-! ## The angular profile `sinTwo` and the identification with `sinIter` -/







end Work.FTS.EllipticEst.ThetaU
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.CutZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false





end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.PsiCutAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The iterated operator `E_ρ = ρ ∂` -/

/-- The operator `E_ρ f = ρ · f'` on functions `ℝ → ℝ`. -/
def Eop (ρ f : ℝ → ℝ) : ℝ → ℝ := ρ * deriv f

/-- The `k`-th iterate of `E_ρ`. -/
def Eiter : ℕ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, _, f => f
  | n + 1, ρ, f => Eop ρ (Eiter n ρ f)

@[simp] theorem Eiter_zero (ρ f : ℝ → ℝ) : Eiter 0 ρ f = f := rfl

@[simp] theorem Eiter_succ (n : ℕ) (ρ f : ℝ → ℝ) : Eiter (n + 1) ρ f = Eop ρ (Eiter n ρ f) := rfl

/-- `Eiter k ρ f` is smooth as soon as `ρ` and `f` are. -/
theorem contDiff_Eiter {ρ f : ℝ → ℝ} (hρ : ∀ n : ℕ, ContDiff ℝ n ρ)
    (hf : ∀ n : ℕ, ContDiff ℝ n f) : ∀ k n : ℕ, ContDiff ℝ n (Eiter k ρ f) := by
  intro k
  induction k with
  | zero => intro n; simpa using hf n
  | succ k ih =>
      intro n
      rw [Eiter_succ]
      have h1 : ContDiff ℝ n (deriv (Eiter k ρ f)) := (ih (n + 1)).deriv'
      exact (hρ n).mul h1

theorem contDiff_smoothTransition (n : ℕ) : ContDiff ℝ n Real.smoothTransition :=
  Real.smoothTransition.contDiff


theorem contDiff_affine (lam c : ℝ) : ∀ n : ℕ, ContDiff ℝ n (fun θ : ℝ => lam * θ + c) :=
  fun n => (contDiff_const.mul contDiff_id).add contDiff_const

theorem contDiff_rhoU (lam c : ℝ) :
    ∀ n : ℕ, ContDiff ℝ n (fun u : ℝ => lam * Real.sin (2 * ((u - c) / lam))) :=
  fun n => contDiff_const.mul
    (Real.contDiff_sin.comp (contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const lam)))

/-! ## Vanishing of the iterates at points where `f` is locally constant -/

/-- If `f` is constant on the open set `U` then all positive iterates of `E_ρ` applied to `f`
vanish on `U`. -/
theorem Eiter_eq_zero_of_open_const {ρ f : ℝ → ℝ} {U : Set ℝ} {u : ℝ} (hU : IsOpen U)
    (hu : u ∈ U) (hconst : ∀ w ∈ U, f w = f u) :
    ∀ k, 1 ≤ k → ∀ v ∈ U, Eiter k ρ f v = 0 := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro _ v hv
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp only [Eiter_succ, Eiter_zero, Eop, Pi.mul_apply]
        have hev : f =ᶠ[𝓝 v] fun _ => f u := by
          filter_upwards [hU.mem_nhds hv] with w hw; exact hconst w hw
        rw [hev.deriv_eq, deriv_const, mul_zero]
      · have hev : (fun w => Eiter k ρ f w) =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
          filter_upwards [hU.mem_nhds hv] with w hw
          exact ih hkpos w hw
        simp only [Eiter_succ, Eop, Pi.mul_apply]
        rw [hev.deriv_eq, deriv_const, mul_zero]

/-! ## The abstract derivative bound -/

/-- The recursive constants of the bound: `Cbnd M B k j` bounds `|iteratedDeriv j (E_ρ^k f)|`
on `[0,1]` whenever `M` bounds the derivatives of `ρ` and `B` those of `f` there. -/
def Cbnd (M B : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, j => B j
  | (k + 1), j => ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * M i * Cbnd M B k (j - i + 1)



/-! ## The rescaled angular coefficient -/

/-- The coefficient `ρ_λ(u) = λ sin(2 (u+1)/λ)` of the angular substitution: in the rescaled
angular variable `u = λ θ - 1` the operator `D_θ = sin(2θ)∂_θ` becomes `E_{ρ_λ}`. -/
def rhoM (lam : ℝ) : ℝ → ℝ := fun u => lam * Real.sin (2 * (u + 1) / lam)

theorem contDiff_rhoM (lam : ℝ) : ∀ n : ℕ, ContDiff ℝ n (rhoM lam) := by
  intro n
  unfold rhoM
  fun_prop

/-! ## Substitution: the rescaled variables -/


/-- **Angular substitution.**  In the rescaled variable `u = λ θ + c` (`λ ≠ 0`) the operator
`D_θ` becomes `E_{u ↦ λ sin(2 (u - c)/λ)}`. -/
theorem DthIter_affine (f : ℝ → ℝ) (lam c : ℝ) (hlam : lam ≠ 0) (i : ℕ)
    (hf : ∀ n : ℕ, ContDiff ℝ n f) :
    ∀ z θ : ℝ, Work.Spaces.DthIter i (fun _ θ' => f (lam * θ' + c)) z θ
      = Eiter i (fun u => lam * Real.sin (2 * ((u - c) / lam))) f (lam * θ + c) := by
  induction i with
  | zero => intro z θ; simp
  | succ i ih =>
      intro z θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      have hfun : (fun θ' => Work.Spaces.DthIter i (fun _ θ' => f (lam * θ' + c)) z θ')
          = fun θ' => Eiter i (fun u => lam * Real.sin (2 * ((u - c) / lam))) f (lam * θ' + c) := by
        funext θ'; exact ih z θ'
      rw [hfun]
      have hd : DifferentiableAt ℝ (Eiter i (fun u => lam * Real.sin (2 * ((u - c) / lam))) f)
          (lam * θ + c) :=
        ((contDiff_Eiter (contDiff_rhoU lam c) hf i 1).differentiable (by norm_num)).differentiableAt
      have hlin : HasDerivAt (fun θ' : ℝ => lam * θ' + c) lam θ := by
        have h := ((hasDerivAt_id θ).const_mul lam).add_const c
        rw [mul_one] at h
        exact h
      have hcomp : HasDerivAt
          (fun θ' => Eiter i (fun u => lam * Real.sin (2 * ((u - c) / lam))) f (lam * θ' + c))
          (deriv (Eiter i (fun u => lam * Real.sin (2 * ((u - c) / lam))) f)
            (lam * θ + c) * lam) θ :=
        hd.hasDerivAt.comp θ hlin
      rw [hcomp.deriv, Eiter_succ, Eop]
      have hq : (lam * θ + c - c) / lam = θ := by
        field_simp
        ring
      simp only [Pi.mul_apply, hq]
      ring

end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false

/-- The `z`-part of the localisation set `U_N`: the complement of the open plateau
`(plo N, phiN N) = (2/(N+1), N+1)` in the radial variable. -/
def Uz (N : ℕ) : Set ℝ := {z | z ∉ Set.Ioo (plo N) (phiN N)}

/-- The `θ`-part of the localisation set `U_N`: the complement of the open plateau
`(qlo N, qhi N) = (2/(N+1), π/2 - 2/(N+1))` in the angular variable. -/
def Ut (N : ℕ) : Set ℝ := {θ | θ ∉ Set.Ioo (qlo N) (qhi N)}

/-- **The localisation set** `U_N ⊂ ℝ × ℝ`: the mixed derivatives `D_z^bD_θ^a χ_N` (`a+b ≤ 4`)
can be non-zero only here. -/
def UN (N : ℕ) : Set (ℝ × ℝ) := {p | p.1 ∈ Uz N ∨ p.2 ∈ Ut N}

/-- **The two angular layers of the cutoff**: the `θ`-derivatives of `χ_N` vanish off `LN N`. -/
def LN (N : ℕ) : Set ℝ :=
  Set.Icc (tlo N) (2 / ((N : ℝ) + 1)) ∪ Set.Icc (Real.pi / 2 - 2 / ((N : ℝ) + 1)) (thi N)

/-! ## Measurability -/





end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.psiCut_basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.GalBasis.cc


/-! ## Smoothness -/

private lemma contDiff_cutA (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (cutA N) := by
  unfold cutA
  fun_prop

private lemma contDiff_cutB (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (cutB N) := by
  unfold cutB
  fun_prop

/-! ## The range `[0,1]` -/



/-! ## The value `1` on the plateau -/



/-! ## The value `0` off the outer box -/





/-! ## The four clauses -/


end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.psiCut_mixed_factor =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The mixed derivatives of the cutoff `psiCut` factorise

`psiCut N z θ = cutA N z * cutB N θ` is a product of a function of `z` alone with a function
of `θ` alone.  The operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` respect that splitting —
`D_z` differentiates only in `z`, so a factor depending on `θ` alone comes out, and dually for
`D_θ` — hence for every `j`, `i`

  `mixed j i (psiCut N) = DzIter j (cutA N) * DthIter i (cutB N)`.

The proof of `psiCut_mixed_factor` below goes through the "one-variable" versions `DzIter1`,
`DthIter1` of the two iterated operators (the `θ`-argument of a function of `z` alone is
irrelevant, and conversely), so that all the bookkeeping is about `ℝ → ℝ` functions.
-/

noncomputable section

open scoped Real Topology

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false

/-! ## The one-variable operators `z ∂_z` and `sin(2θ) ∂_θ` -/

/-- The operator `f ↦ (z ↦ z * f'(z))` on functions `ℝ → ℝ`. -/
def Dz1 (f : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv f z

/-- The operator `f ↦ (θ ↦ sin(2θ) * f'(θ))` on functions `ℝ → ℝ`. -/
def Dth1 (f : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv f θ

/-- The `j`-th iterate of `Dz1`. -/
def DzIter1 : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => Dz1 (DzIter1 n f)

/-- The `i`-th iterate of `Dth1`. -/
def DthIter1 : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => Dth1 (DthIter1 n f)

@[simp] theorem DzIter1_zero (f : ℝ → ℝ) : DzIter1 0 f = f := rfl

@[simp] theorem DzIter1_succ (n : ℕ) (f : ℝ → ℝ) : DzIter1 (n + 1) f = Dz1 (DzIter1 n f) := rfl

@[simp] theorem DthIter1_zero (f : ℝ → ℝ) : DthIter1 0 f = f := rfl

@[simp] theorem DthIter1_succ (n : ℕ) (f : ℝ → ℝ) : DthIter1 (n + 1) f = Dth1 (DthIter1 n f) := rfl

/-! ## `DzIter` and `DthIter` of a function of a single variable -/

/-- `D_z^j` applied to a function of `z` alone is the one-variable iterate `DzIter1`. -/
theorem DzIter_const (j : ℕ) (a : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z' (_ : ℝ) => a z') = fun z _ => DzIter1 j a z := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dz, Work.Spaces.pz, DzIter1_succ, Dz1]

/-- `D_θ^i` applied to a function of `θ` alone is the one-variable iterate `DthIter1`. -/
theorem DthIter_const (i : ℕ) (b : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun (_ : ℝ) θ' => b θ') = fun _ θ => DthIter1 i b θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth, DthIter1_succ, Dth1]



/-! ## `DzIter` and `DthIter` of a separated product -/



/-! ## The theorem -/


end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.L12f_eq_sub_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.RHS

theorem L12f_eq_sub_add {a b : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    Work.Coercivity.L12f a z
      = Work.Coercivity.L12f (fun z θ => a z θ - b z θ) z + Work.Coercivity.L12f b z := by
  -- `L₁₂` is an integral of the density, so it is enough to compute the density of `a - b`.
  -- At the level of the angular density the integrands subtract pointwise, and the two
  -- `θ`-slices of `a`, `b` are integrable (`h1`, `h2`), so `integral_sub` applies.
  have hdens : ∀ s ∈ Set.Ioi z,
      Work.Construction.L12dens (fun z θ => a z θ - b z θ) s
        = Work.Construction.L12dens a s - Work.Construction.L12dens b s := by
    intro s hs
    have hpt : (fun θ => Work.Spaces.K θ * (a s θ - b s θ) / s)
        = fun θ => Work.Spaces.K θ * a s θ / s - Work.Spaces.K θ * b s θ / s := by
      funext θ; ring
    simp only [Work.Construction.L12dens, Work.FM.L12dens]
    rw [hpt]
    exact MeasureTheory.integral_sub (h1 s hs) (h2 s hs)
  -- The `θ`-slice of `a - b` is integrable (difference of the two integrable slices).
  have hslice : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (a s θ - b s θ) / s) Work.Spaces.Iθ := by
    intro s hs
    refine ((h1 s hs).sub (h2 s hs)).congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [Pi.sub_apply]
    ring
  -- The density of `a - b` is integrable on `(z,∞)` (`hdens`, `h3`, `h4`).
  have hdensInt : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (fun z θ => a z θ - b z θ)) (Set.Ioi z) := by
    refine (h3.sub h4).congr_fun (fun s hs => ?_) measurableSet_Ioi
    exact (hdens s hs).symm
  -- Additivity of `L₁₂` on the pair `(a - b, b)`, with `a - b + b = a`.
  obtain ⟨hadd, -⟩ := Work.FTS.LocData.L12_add_mul (c := (0 : ℝ)) hslice h2 hdensInt h4
  have hfun : (fun z θ => (a z θ - b z θ) + b z θ) = a := by
    funext z θ; ring
  rw [hfun] at hadd
  -- `Work.Coercivity.L12f` and `Work.Construction.L12` are the same function (`rfl`).
  change Work.Construction.L12 a z
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) z + Work.Construction.L12 b z
  exact hadd

end Work.FTS.GalFields.RHS
end
-- ===== merged: Submission.Work.FTS.Galerkin.Extraction =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false

/-! ## Diagonal extraction with per-column bounds -/


/-! ## Extension of the limit by equicontinuity -/


/-! ## The extraction on the slab -/


end Work.FTS.Galerkin
end
end
-- ===== merged: Submission.Work.FTS.H2.STQ.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.STQ

set_option autoImplicit false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## Elementary closure properties of `SmoothQuad` -/

theorem SmoothQuad.pth {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) : SmoothQuad (Spaces.pth f) :=
  Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hf



/-! ## The Leibniz rules in the interior class -/

/-- Leibniz rule for `D_z^j` on the open quadrant, at a point with `z ∈ Iz`, `0 < θ < π/2`. -/
theorem DzIter_mul_quad {j : ℕ} {f g : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (hg : SmoothQuad g)
    {z θ : ℝ} (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Spaces.DzIter j (fun z θ => f z θ * g z θ) z θ =
      ∑ b ∈ Finset.range (j + 1),
        (j.choose b : ℝ) * (Spaces.DzIter b f z θ * Spaces.DzIter (j - b) g z θ) :=
  Work.FTS.LocData.DzIter_mul_smoothQuad j f g hz (hf.curry_z hθ) (hg.curry_z hθ)


/-- The same identity as an `EqOn` on the open quadrant (needed to commute it with `D_z^j`). -/
theorem DthIter_mul_eqOn_quad {i : ℕ} {f g : ℝ → ℝ → ℝ} (hf : SmoothQuad f)
    (hg : SmoothQuad g) :
    Set.EqOn (Function.uncurry (Spaces.DthIter i (fun z θ => f z θ * g z θ)))
      (Function.uncurry (fun z θ => ∑ a ∈ Finset.range (i + 1),
        (i.choose a : ℝ) * (Spaces.DthIter a f z θ * Spaces.DthIter (i - a) g z θ)))
      Spaces.quadU := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  exact Work.FTS.LocData.DthIter_mul_smoothQuad i f g hp.2
    (Work.FTS.LocData.SmoothQuad.curry_θ hf hp.1)
    (Work.FTS.LocData.SmoothQuad.curry_θ hg hp.1)

/-! ## Linearity of `D_z^j` over a finite sum with constant coefficients -/

/-- `D_z^j` acts termwise on a finite sum with constant coefficients, on an open set on which
every summand is `C^∞`. -/
theorem DzIter_sum_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → ℝ → ℝ → ℝ)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (F i)) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i * Spaces.DzIter j (F i) z θ)) V := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
    have hFs : ∀ i ∈ s, ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Spaces.DzIter j (F i))) V := fun i hi =>
      Work.FTS.LocData.contDiffOn_DzIter hV (hF i hi) j
    intro p hp
    obtain ⟨z, θ⟩ := p
    have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => Spaces.DzIter j (F i) z' θ) z :=
      fun i hi => by
        have h1 : DifferentiableAt ℝ (Function.uncurry (Spaces.DzIter j (F i))) (z, θ) :=
          ((hFs i hi).contDiffAt (hV.mem_nhds hp)).differentiableAt
            (by simp [Work.FTS.LocData.smoothOrder_ne_zero])
        have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
          (hasFDerivAt_prodMk_left z θ).differentiableAt
        have h3 := h1.comp z h2
        simpa [Function.comp_def, Function.uncurry] using h3
    have hcongr : Spaces.pz (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i * F i z θ)) z θ
        = Spaces.pz (fun z θ => ∑ i ∈ s, c i * Spaces.DzIter j (F i) z θ) z θ :=
      Spaces.pz_congr_of_isOpen hV ih hp
    have h1 : Spaces.pz (fun z θ => ∑ i ∈ s, c i * Spaces.DzIter j (F i) z θ) z θ
        = ∑ i ∈ s, c i * Spaces.pz (Spaces.DzIter j (F i)) z θ := by
      show deriv (fun z' => ∑ i ∈ s, c i * Spaces.DzIter j (F i) z' θ) z = _
      have hfun : (fun z' => ∑ i ∈ s, c i * Spaces.DzIter j (F i) z' θ)
          = ∑ i ∈ s, (fun z' => c i * Spaces.DzIter j (F i) z' θ) := by
        funext z'; rw [Finset.sum_apply]
      rw [hfun, deriv_sum (fun i hi => (hdiff i hi).const_mul (c i))]
      exact Finset.sum_congr rfl fun i hi => deriv_const_mul_field (c i)
    show Spaces.Dz (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i * F i z θ)) z θ
        = ∑ i ∈ s, c i * Spaces.Dz (Spaces.DzIter j (F i)) z θ
    show z * Spaces.pz (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i * F i z θ)) z θ
        = ∑ i ∈ s, c i * (z * Spaces.pz (Spaces.DzIter j (F i)) z θ)
    rw [hcongr, h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by ring

/-! ## The two-operator Leibniz rule for `D_z^j D_θ^i` -/

/-- **The mixed Leibniz rule in the interior class**:
`D_z^j D_θ^i (f·g) = Σ_a Σ_b C(i,a) C(j,b) D_z^b D_θ^a f · D_z^{j-b} D_θ^{i-a} g` at a point
of the open quadrant.  It is the composition of the two one-operator rules (the `D_θ`-rule
applied to the product, then the `D_z`-rule on each summand); no two-operator commutator is
involved. -/
theorem mixed_mul_quad {j i : ℕ} {f g : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (hg : SmoothQuad g)
    {z θ : ℝ} (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ =
      ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Spaces.mixed b a f z θ * Spaces.mixed (j - b) (i - a) g z θ) := by
  have hz1 : (-1 : ℝ) < z := by
    rw [Spaces.Iz, Set.mem_Ici] at hz; linarith
  have hp : (z, θ) ∈ Spaces.quadU := ⟨hz1, hθ⟩
  -- step 1: `D_θ^i(fg)` expands on the open quadrant
  have hfun := DthIter_mul_eqOn_quad (i := i) hf hg
  -- step 2: apply `D_z^j` to both sides
  have h2 := Work.FTS.H2.DzIter_congr_of_isOpen Work.Spaces.isOpen_quadU hfun j hp
  -- step 3: linearity of `D_z^j` over the finite sum
  have h3 := DzIter_sum_eqOn (Finset.range (i + 1)) (fun a => (i.choose a : ℝ))
    (fun a => fun z θ => Spaces.DthIter a f z θ * Spaces.DthIter (i - a) g z θ)
    Work.Spaces.isOpen_quadU ?_ j hp
  · -- step 4: expand each `D_z^j` of a product
    simp only [Function.uncurry] at h2 h3
    rw [show Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
          = Spaces.DzIter j (Spaces.DthIter i (fun z θ => f z θ * g z θ)) z θ from rfl, h2, h3]
    have hterm : ∀ a ∈ Finset.range (i + 1),
        Spaces.DzIter j (fun z θ => Spaces.DthIter a f z θ * Spaces.DthIter (i - a) g z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Spaces.mixed b a f z θ * Spaces.mixed (j - b) (i - a) g z θ) := by
      intro a ha
      exact DzIter_mul_quad (hf.DthIter a) (hg.DthIter (i - a)) hz hθ
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hterm a ha, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b hb => by ring
  · intro a ha
    exact Work.FTS.LocData.smoothQuad_mul (hf.DthIter a) (hg.DthIter (i - a))

/-! ## Linearity of `D_z^j` over a finite sum with `θ`-dependent coefficients -/


/-- The `pz`-form of `Dz_sum_theta_coeff_eqOn`. -/
theorem pz_sum_theta_coeff_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ)
    (F : ι → ℝ → ℝ → ℝ) {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (F i)) V) :
    Set.EqOn (Function.uncurry (Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Spaces.pz (F i) z θ)) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => F i z' θ) z := fun i hi => by
    have h1 : DifferentiableAt ℝ (Function.uncurry (F i)) (z, θ) :=
      ((hF i hi).contDiffAt (hV.mem_nhds hp)).differentiableAt
        (by simp [Work.FTS.LocData.smoothOrder_ne_zero])
    have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
      (hasFDerivAt_prodMk_left z θ).differentiableAt
    have h3 := h1.comp z h2
    simpa [Function.comp_def, Function.uncurry] using h3
  show deriv (fun z' => ∑ i ∈ s, c i θ * F i z' θ) z
      = ∑ i ∈ s, c i θ * Spaces.pz (F i) z θ
  have hfun : (fun z' => ∑ i ∈ s, c i θ * F i z' θ)
      = ∑ i ∈ s, (fun z' => c i θ * F i z' θ) := by
    funext z'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun i hi => (hdiff i hi).const_mul (c i θ))]
  exact Finset.sum_congr rfl fun i hi => deriv_const_mul_field (c i θ)

/-- The iterated form of `Dz_sum_theta_coeff_eqOn`. -/
theorem DzIter_sum_theta_coeff_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ)
    (F : ι → ℝ → ℝ → ℝ) {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (F i)) V)
    (j : ℕ) :
    Set.EqOn (Function.uncurry (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Spaces.DzIter j (F i) z θ)) V := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
    have hFs : ∀ i ∈ s, ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Spaces.DzIter j (F i))) V := fun i hi =>
      Work.FTS.LocData.contDiffOn_DzIter hV (hF i hi) j
    have hstep' := pz_sum_theta_coeff_eqOn s c (fun i => Spaces.DzIter j (F i)) hV hFs
    intro p hp
    obtain ⟨z, θ⟩ := p
    have hcongr : Spaces.pz (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)) z θ
        = Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * Spaces.DzIter j (F i) z θ) z θ :=
      Spaces.pz_congr_of_isOpen hV ih hp
    have h2 := hstep' hp
    simp only [Function.uncurry] at h2
    show Spaces.Dz (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)) z θ
        = ∑ i ∈ s, c i θ * Spaces.Dz (Spaces.DzIter j (F i)) z θ
    show z * Spaces.pz (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)) z θ
        = ∑ i ∈ s, c i θ * (z * Spaces.pz (Spaces.DzIter j (F i)) z θ)
    rw [hcongr, h2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by ring

end Work.FTS.H2.STQ
end
end
-- ===== merged: Submission.Work.FTS.H2.StarPkg.divZWlInf_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.H2.StarPkg

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The genuine smooth order `∞` versus the analytic order `⊤` -/

theorem smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]

theorem smoothOrder_add_one :
    Work.Stability.smoothOrder + 1 = Work.Stability.smoothOrder := rfl

theorem natCast_le_smoothOrder (k : ℕ) :
    ((k : ℕ∞) : ℕ∞ω) ≤ Work.Stability.smoothOrder := by
  rw [Work.Stability.smoothOrder]
  exact WithTop.coe_le_coe.mpr le_top

/-! ## The Taylor quotient of a function of one variable, at the genuine smooth order -/










/-! ## The `z`-slices of `DthIter j f`, `j ≥ 1` -/




/-! ## The main theorem -/


end Work.FTS.H2.StarPkg
end
end
-- ===== merged: Submission.Work.FTS.H2.WPQ.AesmPkg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.WPQ

set_option autoImplicit false


end Work.FTS.H2.WPQ
end
end
-- ===== merged: Submission.Work.FTS.H2.WPQ.Leibniz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS.H2.WPQ

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Uncurried functions which are `C^∞` on the open strip `(-1,∞) × (0,π/2)` in the genuine
smooth order (the class of `Work.FTS.LocData.SmoothQuad`). -/
def SmoothUsm (F : ℝ × ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder F Work.Spaces.quadU

theorem SmoothQuad.toSmoothUsm {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    SmoothUsm (Function.uncurry f) := hf

lemma SmoothUsm.differentiableAt {F : ℝ × ℝ → ℝ} (h : SmoothUsm F) {p : ℝ × ℝ}
    (hp : p ∈ Work.Spaces.quadU) : DifferentiableAt ℝ F p :=
  (h.contDiffAt (Work.Spaces.isOpen_quadU.mem_nhds hp)).differentiableAt (by simp)

theorem SmoothUsm_FunClass : Work.Spaces.FunClass (X := ℝ × ℝ) SmoothUsm where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun p => c * A p) Work.Spaces.quadU
    exact ContDiffOn.const_smul c hA

/-- `Zb = z ∂_z` is a derivation-like operator on the `C^∞` (genuine order) functions of the
open strip.  (`Work.Spaces.Zb_DerivLike` is the analytic-order version.) -/
theorem Zb_DerivLike_sm : Work.Spaces.DerivLike Work.Spaces.quadU SmoothUsm Work.Spaces.Zb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hB.differentiableAt hp)
    show Work.Spaces.Zb (A + B) (z, θ) = Work.Spaces.Zb A (z, θ) + Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [show (fun z' => (A + B) (z', θ)) =
          (fun z' => A (z', θ)) + (fun z' => B (z', θ)) from rfl,
        deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hB.differentiableAt hp)
    show Work.Spaces.Zb (A * B) (z, θ)
        = Work.Spaces.Zb A (z, θ) * B (z, θ) + A (z, θ) * Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [show (fun z' => (A * B) (z', θ)) =
          (fun z' => A (z', θ)) * (fun z' => B (z', θ)) from rfl,
        deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    rintro ⟨z, θ⟩ hp
    have hs : Set.EqOn (fun z' => A (z', θ)) (fun z' => B (z', θ)) (Set.Ioi (-1)) :=
      fun z' hz' => h ⟨hz', hp.2⟩
    show Work.Spaces.Zb A (z, θ) = Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [hs.deriv isOpen_Ioi hp.1]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (fderiv ℝ A) Work.Spaces.quadU :=
      hA.fderiv_of_isOpen Work.Spaces.isOpen_quadU
        (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    have hev : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (fderiv ℝ A p) (1, 0)) Work.Spaces.quadU :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 * (fderiv ℝ A p) (1, 0)) Work.Spaces.quadU :=
      (contDiff_fst.contDiffOn).mul hev
    refine hfun.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    dsimp only
    show Work.Spaces.Zb A (z, θ) = z * (fderiv ℝ A (z, θ)) (1, 0)
    simp only [Work.Spaces.Zb]
    rw [Work.Spaces.deriv_slice_fst A z θ (hA.differentiableAt hp)]
  smul := fun c A hA => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hA.differentiableAt hp)
    show Work.Spaces.Zb (fun p => c * A p) (z, θ) = c * Work.Spaces.Zb A (z, θ)
    simp only [Work.Spaces.Zb]
    rw [deriv_const_mul c hA']
    ring

/-- `Tb = sin(2θ) ∂_θ` is a derivation-like operator on the `C^∞` (genuine order) functions of
the open strip.  (`Work.Spaces.Tb_DerivLike` is the analytic-order version.) -/
theorem Tb_DerivLike_sm : Work.Spaces.DerivLike Work.Spaces.quadU SmoothUsm Work.Spaces.Tb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hB.differentiableAt hp)
    show Work.Spaces.Tb (A + B) (z, θ) = Work.Spaces.Tb A (z, θ) + Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [show (fun θ' => (A + B) (z, θ')) =
          (fun θ' => A (z, θ')) + (fun θ' => B (z, θ')) from rfl,
        deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hB.differentiableAt hp)
    show Work.Spaces.Tb (A * B) (z, θ)
        = Work.Spaces.Tb A (z, θ) * B (z, θ) + A (z, θ) * Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [show (fun θ' => (A * B) (z, θ')) =
          (fun θ' => A (z, θ')) * (fun θ' => B (z, θ')) from rfl,
        deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    rintro ⟨z, θ⟩ hp
    have hs : Set.EqOn (fun θ' => A (z, θ')) (fun θ' => B (z, θ')) (Set.Ioo 0 (π/2)) :=
      fun θ' hθ' => h ⟨hp.1, hθ'⟩
    show Work.Spaces.Tb A (z, θ) = Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [hs.deriv isOpen_Ioo hp.2]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (fderiv ℝ A) Work.Spaces.quadU :=
      hA.fderiv_of_isOpen Work.Spaces.isOpen_quadU
        (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    have hev : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (fderiv ℝ A p) (0, 1)) Work.Spaces.quadU :=
      hfd.clm_apply contDiffOn_const
    have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Spaces.quadU :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hfun : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2) * (fderiv ℝ A p) (0, 1)) Work.Spaces.quadU :=
      hsin.mul hev
    refine hfun.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    dsimp only
    show Work.Spaces.Tb A (z, θ) = Real.sin (2 * θ) * (fderiv ℝ A (z, θ)) (0, 1)
    simp only [Work.Spaces.Tb]
    rw [Work.Spaces.deriv_slice_snd A z θ (hA.differentiableAt hp)]
  smul := fun c A hA => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hA.differentiableAt hp)
    show Work.Spaces.Tb (fun p => c * A p) (z, θ) = c * Work.Spaces.Tb A (z, θ)
    simp only [Work.Spaces.Tb]
    rw [deriv_const_mul c hA']
    ring

/-- **The two-operator Leibniz rule in the interior class `SmoothQuad`.**

`D_z^j D_θ^i (f·g) = ∑_{a≤i} ∑_{b≤j} C(i,a) C(j,b) (D_z^b D_θ^a f)(D_z^{j-b} D_θ^{i-a} g)`
for `z ≥ 0` and `0 < θ < π/2`. -/
theorem mixed_mul_eq_smoothQuad (j i : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ) := by
  intro z hz θ hθ
  have hz1 : z ∈ Set.Ioi (-1) := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    exact Set.mem_Ioi.mpr (by linarith)
  have hp : (z, θ) ∈ Work.Spaces.quadU := ⟨hz1, hθ⟩
  have h2 := (Work.Spaces.DerivLike.twoOp_iterate_mul (X := ℝ × ℝ)
      (s := Work.Spaces.quadU) (P := SmoothUsm) (Z := Work.Spaces.Zb)
      (Θb := Work.Spaces.Tb) SmoothUsm_FunClass Zb_DerivLike_sm
      Tb_DerivLike_sm j i (SmoothQuad.toSmoothUsm hf) (SmoothQuad.toSmoothUsm hg)) hp
  have h2' : Work.Spaces.Zb^[j] (Work.Spaces.Tb^[i]
        (Function.uncurry f * Function.uncurry g)) (z, θ)
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * ((Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry f))) (z, θ)
               * (Work.Spaces.Zb^[j - b] (Work.Spaces.Tb^[i - a] (Function.uncurry g))) (z, θ)) := by
    simpa using h2
  have hL : Work.Spaces.Zb^[j] (Work.Spaces.Tb^[i]
        (Function.uncurry f * Function.uncurry g)) (z, θ)
      = Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ := by
    rw [Work.Spaces.uncurry_mul f g,
      Work.Spaces.Tb_iterate_uncurry i (fun z θ => f z θ * g z θ),
      Work.Spaces.Zb_iterate_uncurry j (Work.Spaces.DthIter i (fun z θ => f z θ * g z θ))]
    rfl
  have e_f : ∀ a b, Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry f)) (z, θ)
      = Work.Spaces.mixed b a f z θ := fun a b => by
    rw [Work.Spaces.Tb_iterate_uncurry a f,
      Work.Spaces.Zb_iterate_uncurry b (Work.Spaces.DthIter a f)]
    rfl
  have e_g : ∀ a b, Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry g)) (z, θ)
      = Work.Spaces.mixed b a g z θ := fun a b => by
    rw [Work.Spaces.Tb_iterate_uncurry a g,
      Work.Spaces.Zb_iterate_uncurry b (Work.Spaces.DthIter a g)]
    rfl
  rw [← hL, h2']
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  rw [e_f a b, e_g (i - a) (j - b)]

end Work.FTS.H2.WPQ
end
end
-- ===== merged: Submission.Work.FTS.H2.integrableOn_w_sq_mul_int_sqQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Auxiliary facts

Three `SmoothQuad`-in-place-of-`SmoothNbhd` versions of the pieces of
`Work.Elliptic.integrableOn_w_sq_mul_int_sq` (equivalently
`Work.FTS.EllipticEst.Blocks.L12Gen.integrableOn_w_sq_mul_int_sq_k`): the a.e. domination of
the pure `D_z^j` slot by the `ℋ⁴`-integrand, the product-integrability of the `ℋ⁴`-integrand,
and the product-integrability of `(D_z^j g)² w²`.  Only the second differs substantively from
the `SmoothNbhd` version: continuity of the integrand on the *open* quadrant
(`Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`) replaces continuity on a neighbourhood
of the closed quadrant. -/

private abbrev quadO : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

private lemma quadO_subset_quadU : quadO ⊆ Work.Spaces.quadU := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  exact ⟨Set.mem_Ioi.mpr (by have h := Set.mem_Ioi.mp hz; linarith), hθ⟩

/-- A.e. pointwise domination of the pure `D_z^j` slot by the `ℋ⁴`-integrand.  No smoothness
hypothesis is needed: on the open quadrant `w² ≤ (w / sin(2θ)^{η/2})²` because
`0 < sin(2θ) ≤ 1` there. -/
private theorem ae_DzIter_sq_mul_w_sq_le_HkIntegrand_Q (α : ℝ) (g : ℝ → ℝ → ℝ)
    {j : ℕ} (hj : j ≤ 4) :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.DzIter j g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g p.1 p.2 := by
  filter_upwards [Work.Elliptic.ae_mem_Qd_prod] with p hp
  obtain ⟨hz, hθ0, hθ1⟩ := hp
  have hsinp := Work.Elliptic.one_le_sin_two_rpow_neg_eta hθ0 hθ1
  have hsin : 0 < Real.sin (2 * p.2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsq : 0 ≤ (Work.Spaces.DzIter j g p.1 p.2) ^ 2 := sq_nonneg _
  have hw2 : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
  calc (Work.Spaces.DzIter j g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
      ≤ (Work.Spaces.DzIter j g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
        nlinarith [mul_nonneg hsq hw2, hsinp]
    _ = (Work.Spaces.DzIter j g p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        have hs : 0 ≤ Real.sin (2 * p.2) := hsin.le
        have hsq' : (Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2)) ^ 2
            = Real.sin (2 * p.2) ^ (Work.Spaces.eta) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
          norm_num
        rw [mul_pow, div_pow, hsq', div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
        ring
    _ ≤ Work.Spaces.HkIntegrand α 4 g p.1 p.2 :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 g p.1 p.2 j hj

/-- Product-integrability of the `ℋ⁴`-integrand for `SmoothQuad` data. -/
private theorem HkIntegrand_integrable_prod_Q (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 g hsm)
  refine ⟨haesm, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hcongr1 : ∫⁻ (p : ℝ × ℝ), ‖Work.Spaces.HkIntegrand α 4 g p.1 p.2‖ₑ
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      = ∫⁻ (p : ℝ × ℝ), ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 g p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    lintegral_congr fun p => Real.enorm_eq_ofReal (Work.Spaces.HkIntegrand_nonneg α 4 g p.1 p.2)
  rw [hcongr1]
  rw [MeasureTheory.lintegral_prod _
    (AEMeasurable.ennreal_ofReal (AEStronglyMeasurable.aemeasurable haesm))]
  have hcongr2 : ∫⁻ (z : ℝ), ∫⁻ (θ : ℝ), ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 g z θ)
        ∂(volume.restrict Work.Spaces.Iθ) ∂(volume.restrict Work.Spaces.Iz)
      = ∫⁻ (z : ℝ), ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 g z θ)
        ∂(volume.restrict Work.Spaces.Iz) := by
    refine lintegral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)).symm
  rw [hcongr2]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
    (Eventually.of_forall fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 4 g z θ)]
  exact ENNReal.ofReal_lt_top

/-- Product-integrability of `(D_z^j g)² w²` for `SmoothQuad` data. -/
private theorem integrable_prod_DzIter_sq_mul_w_sq_Q (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {j : ℕ} (hj : j ≤ 4) :
    Integrable (fun p : ℝ × ℝ => (Work.Spaces.DzIter j g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hsm' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
      Work.Spaces.quadU := hsm
  have hcont1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter j g p.1 p.2) ^ 2) quadO :=
    (((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hsm' j).continuousOn).mono
      quadO_subset_quadU).pow 2
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) quadO := by
    simp only [Work.Spaces.w]
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) ?_
    intro p hp
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  refine MeasureTheory.Integrable.mono' (HkIntegrand_integrable_prod_Q α g hsm hmem)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hcont1.mul hcont2)) ?_
  filter_upwards [ae_DzIter_sq_mul_w_sq_le_HkIntegrand_Q α g hj] with p hp
  rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]

/-- The pure `D_z^j` slot comparison in the interior class: the `z`-integral of the weighted
angular energy `∫_θ (D_z^j g)²` is dominated by `HkSq α 4 g`.  This is
`Work.Elliptic.integrableOn_w_sq_mul_int_sq` with `Work.FTS.LocData.SmoothQuad` (genuine
`C^∞` on the open quadrant) and `HkMem` in place of the analyticity hypothesis
`Work.Spaces.SmoothNbhd`.  A sibling to copy from is
`Work.FTS.EllipticEst.Blocks.L12Gen.integrableOn_w_sq_mul_int_sq_k` (also `SmoothNbhd`, same
proof), or `Work.Elliptic.integrableOn_w_sq_mul_int_sq`.

Route (identical to the sibling, replacing the analyticity input by `SmoothQuad`):
for `z > 0` and a.e. `θ ∈ Iθ` one has `(D_z^j g z θ)²·(w z)² ≤ HkIntegrand α 4 g z θ`
(`Work.Elliptic.sq_DzIter_le_HkIntegrand_Qd`, or `Work.Spaces.sq_le_HkIntegrand_z` plus
`sin(2θ)^{η/2} ≤ 1`), so the weighted angular energy is dominated by `∫_θ HkIntegrand`, which is
integrable in `θ` for every `z ∈ Iz` and integrable in `z` over `Iz` by `hmem`.  Measurability of
the two-variable integrand `(z,θ) ↦ (D_z^j g z θ)²(w z)²` comes from its *continuity* on the open
quadrant (`Work.FTS.LocData.contDiffOn_DzIter` + `Work.Spaces.aesm_of_continuousOn_Qd`), and the
outer function `z ↦ ∫_θ (D_z^j g z θ)²(w z)²` is a.e. strongly measurable by
`AEStronglyMeasurable.integral_prod_right'`; `Integrable.mono'` against `hmem.2` gives the
integrability, `integral_mono_ae` plus `∫_z ∫_θ HkIntegrand = HkSq` (definitional) gives the
bound.  A worked example of exactly this bookkeeping with `SmoothQuad` in place of `SmoothNbhd`
is `Work.FTS.H2.slotM_quad` in `Submission/Work/FTS/H2/LinfQ.lean`. -/
theorem integrableOn_w_sq_mul_int_sqQ (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {j : ℕ} (hj : j ≤ 4) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)) Work.Spaces.Iz
      ∧ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2))
        ≤ Work.Spaces.HkSq α 4 g := by
  have hprod := integrable_prod_DzIter_sq_mul_w_sq_Q α g hsm hmem hj
  have hInt2 := HkIntegrand_integrable_prod_Q α g hsm hmem
  have hkey : (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2))
      = fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    funext z
    rw [MeasureTheory.integral_mul_const]
    ring
  have hHk : (∫ p : ℝ × ℝ, Work.Spaces.HkIntegrand α 4 g p.1 p.2
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = Work.Spaces.HkSq α 4 g := (MeasureTheory.integral_prod _ hInt2).trans rfl
  constructor
  · rw [hkey]
    exact MeasureTheory.Integrable.integral_prod_left hprod
  · rw [hkey, ← MeasureTheory.integral_prod _ hprod]
    have h := MeasureTheory.integral_mono_ae hprod hInt2
      (ae_DzIter_sq_mul_w_sq_le_HkIntegrand_Q α g hj)
    rw [hHk] at h
    exact h

end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.AuxSep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces

/-- `(b / s^e)² = b²·s^{-2e}`, valid for `s ≥ 0` (both sides vanish at `s = 0`). -/
theorem div_rpow_sq_loc (b s e : ℝ) (hs : 0 ≤ s) : (b / s ^ e) ^ 2 = b ^ 2 * s ^ (-(2 * e)) := by
  rw [div_pow, div_eq_mul_inv]
  have h : (s ^ e) ^ 2 = s ^ (2 * e) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    ring_nf
  rw [h, ← Real.rpow_neg hs]

/-- The square of a `D_z`-summand factorises into its radial and angular blocks. -/
theorem sep_sq1_loc (B G w s e : ℝ) (hs : 0 ≤ s) :
    (B * G * (w / s ^ (e / 2))) ^ 2 = (B * w) ^ 2 * (G ^ 2 * s ^ (-e)) := by
  rw [show B * G * (w / s ^ (e / 2)) = B * G * w / s ^ (e / 2) by ring, div_rpow_sq_loc _ _ _ hs]
  rw [show -(2 * (e / 2)) = -e by ring]
  ring

/-- The square of a mixed-summand factorises into its radial and angular blocks. -/
theorem sep_sq2_loc (B G w s g : ℝ) (hs : 0 ≤ s) :
    (B * G * (w * s ^ (-(g / 2)))) ^ 2 = (B * w) ^ 2 * (G ^ 2 * s ^ (-g)) := by
  rw [show B * G * (w * s ^ (-(g / 2))) = (B * G * w) * s ^ (-(g / 2)) by ring, mul_pow]
  rw [show (s ^ (-(g / 2))) ^ 2 = s ^ (-g) from by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]; congr 1; ring]
  ring

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_loc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  apply Real.sin_nonneg_of_mem_Icc
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The `γ`-summand of `angMaj`. -/
theorem Gam_sq_rpow_le_angMaj_gam_loc (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.FTS.LocData.angMaj α θ := by
  have hs0 := sin_two_nonneg_loc hθ
  rw [Work.FTS.LocData.angMaj_apply]
  have h1 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  linarith

end Work.FTS.Nonlinear.Pieces
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.theta_majorant_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false

/-! ## Elementary angular facts -/

/-- On `Iθ = [0,π/2]` the quantity `sin(2θ)` is nonnegative. -/
lemma sin_two_nonneg_of_mem_Iθ_R {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Real.sin_two_mul]
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
    (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)

/-- **Integrability of the angular powers for all exponents `> -1`.**

For `-1 < p` the function `θ ↦ sin(2θ)^p` is integrable on `Iθ`.  (The case `p ≤ 0` is
`Work.Spaces.sin_two_rpow`; for `p > 0` the function is continuous on the compact
interval `Iθ`.) -/
lemma integrableOn_sin_two_rpow_gt {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ := by
  rcases lt_or_ge p 0 with h | h
  · exact (Work.Spaces.sin_two_rpow p hp (le_of_lt h)).1
  · have hcont : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ p :=
      (Real.continuous_rpow_const h).comp (by fun_prop)
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc

/-- `X^a · X^{-b} ≤ X^{a-b}` for `X ≥ 0`, `a > 0`, `b > 0`.  (For `X > 0` this is
`Real.rpow_add`, and at `X = 0` both sides degenerate to `0` up to the harmless case
`a = b`.) -/
lemma rpow_mul_rpow_neg_le {X a b : ℝ} (hX : 0 ≤ X) (ha : 0 < a) (hb : 0 < b) :
    X ^ a * X ^ (-b) ≤ X ^ (a - b) := by
  rcases eq_or_lt_of_le hX with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt ha), Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt hb)),
      mul_zero]
    exact Real.rpow_nonneg le_rfl _
  · rw [← Real.rpow_add h, show a + -b = a - b by ring]

/-! ## The pointwise bound for the second majorant -/

/-- **The bracket vanishes fast enough to beat the weight `sin(2θ)^{-γ(α)}`:**

`(Γ + (α + sin 2θ) sin(2θ)^{α/5})² · sin(2θ)^{-γ(α)} ≤ (α+2)² · sin(2θ)^{3α/10-1}`
on `Iθ`, for every `α > 0`. -/
lemma theta_bracket_le_self {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10 - 1) := by
  have hX0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ_R hθ
  have hX1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hGX : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
    Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ
  have hXp0 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hX0 _
  -- the bracket is at most `(α+2)·sin(2θ)^{α/5}`
  have hbracket : Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
      ≤ (α + 2) * (Real.sin (2 * θ)) ^ (α / 5) := by
    have h2 : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
        ≤ (α + 1) * (Real.sin (2 * θ)) ^ (α / 5) :=
      mul_le_mul_of_nonneg_right (by linarith) hXp0
    calc Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
        ≤ (Real.sin (2 * θ)) ^ (α / 5) + (α + 1) * (Real.sin (2 * θ)) ^ (α / 5) :=
          add_le_add hGX h2
      _ = (α + 2) * (Real.sin (2 * θ)) ^ (α / 5) := by ring
  -- squaring
  have hbr0 : 0 ≤ Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    add_nonneg hG0 (mul_nonneg (by linarith) hXp0)
  have hsq := pow_le_pow_left₀ hbr0 hbracket 2
  have hsqX : (Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (α / 5)
      = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [← Real.rpow_add' hX0 (by linarith : α / 5 + α / 5 ≠ 0)]
    congr 1
    ring
  have hrhs : ((α + 2) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      = (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    have h : ((α + 2) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        = (α + 2) ^ 2
          * ((Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
    rw [h, hsqX]
  have hXg0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hX0 _
  have hstep : (Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← hrhs]
    exact mul_le_mul_of_nonneg_right hsq hXg0
  -- the exponent bookkeeping `2α/5 - γ(α) = 3α/10 - 1`
  have hcore : (Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (3 * α / 10 - 1) := by
    have h := rpow_mul_rpow_neg_le hX0 (show 0 < 2 * α / 5 by linarith)
      (show 0 < Work.Spaces.gam α by rw [Work.Spaces.gam]; linarith)
    refine le_trans h (le_of_eq ?_)
    congr 1
    rw [Work.Spaces.gam]
    ring
  refine le_trans hstep ?_
  calc (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (α + 2) ^ 2
        * ((Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        ring
    _ ≤ (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10 - 1) :=
        mul_le_mul_of_nonneg_left hcore (sq_nonneg _)

/-! ## The main lemma -/

theorem theta_majorant_integrable {α : ℝ} (hα : 0 < α) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Gam α θ
            + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- First conjunct: `Γ² sin(2θ)^{-η} ≤ sin(2θ)^{-η}`.
  have hInt1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
    refine integrableOn_sin_two_rpow_gt ?_
    rw [Work.Spaces.eta]
    norm_num
  have hpt1 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    filter_upwards [ae_restrict_mem hIθ] with θ hθ
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    have hX0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ_R hθ
    have hG2 : (Work.Spaces.Gam α θ) ^ 2 ≤ 1 := by nlinarith
    exact mul_le_of_le_one_left (Real.rpow_nonneg hX0 _) hG2
  have hmeas1 : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  have hf1 : IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    hInt1.mono' hmeas1 (by
      filter_upwards [hpt1, ae_restrict_mem hIθ] with θ h1 h2
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ_R h2) _))]
      exact h1)
  refine ⟨hf1, ?_⟩
  -- Second conjunct: dominated by `(α+2)² sin(2θ)^{3α/10-1}`.
  have hInt2 : IntegrableOn
      (fun θ : ℝ => (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10 - 1))
      Work.Spaces.Iθ :=
    (integrableOn_sin_two_rpow_gt (by linarith : (-1 : ℝ) < 3 * α / 10 - 1)).const_mul _
  have hpt2 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10 - 1) := by
    filter_upwards [ae_restrict_mem hIθ] with θ hθ
    exact theta_bracket_le_self hα hθ
  have hmeas2 : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.Gam α θ
          + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam, Work.Spaces.gam]
    fun_prop
  exact hInt2.mono' hmeas2 (by
    filter_upwards [hpt2, ae_restrict_mem hIθ] with θ h1 h2
    have hX0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ_R h2
    rw [Real.norm_of_nonneg
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hX0 _))]
    exact h1)

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.WlamSqrtMarginal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Radial Cauchy–Schwarz against the sublinear weight `Wlam s = s/(1+s)²`

`Wlam` is nonnegative and square-integrable on `(0,∞)`, with `∫_{(0,∞)} Wlam² = W2` by
definition.  Hence for every nonnegative `H : ℝ → ℝ` with `H` integrable on `(0,∞)` the
pairing `∫_{(0,∞)} Wlam s · √(H s)` is controlled by the `L²`-norms of the two factors:

`∫_{(0,∞)} Wlam s · √(H s) ds ≤ √W2 · √(∫_{(0,∞)} H)`.

This is exactly `L²`-Cauchy–Schwarz for the pair (`Wlam`, `√H`): `(√H)² = H` since `H ≥ 0`,
so `√H ∈ L²((0,∞))` with `∫ (√H)² = ∫ H`, and `Wlam ∈ L²((0,∞))` with `∫ Wlam² = W2`.

The only imported ingredient is the square-integrability of the weight,
`Work.Elliptic.psi_sq_integrable_aux` (`(s/(1+s)²)² ∈ L¹((0,∞))`).
-/

namespace Work.FTS.StrongEps.E5Aux3

open MeasureTheory Set Filter
open scoped Real Topology

/-- `Wlam` is a.e. strongly measurable on `(0,∞)` (it is continuous there). -/
lemma aestronglyMeasurable_wlam :
    AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam (volume.restrict (Set.Ioi (0 : ℝ))) := by
  change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
    (volume.restrict (Set.Ioi (0 : ℝ)))
  refine ContinuousOn.aestronglyMeasurable (μ := volume)
    (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_) measurableSet_Ioi
  intro s hs
  have hne : (1 : ℝ) + s ≠ 0 := by
    simp only [Set.mem_Ioi] at hs
    linarith
  exact pow_ne_zero 2 hne

/-- `Wlam²` is integrable on `(0,∞)` (its integral is `W2` by definition). -/
lemma integrableOn_wlam_sq :
    IntegrableOn (fun s : ℝ => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi (0 : ℝ)) := by
  simpa only [Work.FTS.GalBasis.cc.Wlam] using Work.Elliptic.psi_sq_integrable_aux

/-- `Wlam ∈ L²((0,∞))`. -/
lemma memLp_wlam : MemLp Work.FTS.GalBasis.cc.Wlam 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
  (memLp_two_iff_integrable_sq aestronglyMeasurable_wlam).mpr integrableOn_wlam_sq

/-- `√H ∈ L²((0,∞))` whenever `H ≥ 0` is integrable there. -/
lemma memLp_sqrt {H : ℝ → ℝ} (hHnn : ∀ s, 0 ≤ H s)
    (hH : IntegrableOn H (Set.Ioi (0 : ℝ))) :
    MemLp (fun s : ℝ => Real.sqrt (H s)) 2 (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hA_aesm : AEStronglyMeasurable (fun s : ℝ => Real.sqrt (H s))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hH.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s : ℝ => Real.sqrt (H s) ^ 2) (Set.Ioi (0 : ℝ)) :=
    hH.congr (Filter.Eventually.of_forall fun s => (Real.sq_sqrt (hHnn s)).symm)
  exact (memLp_two_iff_integrable_sq hA_aesm).mpr hA2_int

/-- The integrand `Wlam · √H` is nonnegative on `(0,∞)`, hence so is its integral
(`√` is nonnegative and `Wlam` is nonnegative on `(0,∞)`). -/
lemma integral_wlam_sqrt_nonneg (H : ℝ → ℝ) :
    0 ≤ ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s) := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  show ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
    (0 : ℝ) ≤ Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  exact Eventually.of_forall fun s hs =>
    mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt hs)) (Real.sqrt_nonneg _)

/-- **Radial Cauchy–Schwarz against `Wlam`.**  For `H ≥ 0` integrable on `(0,∞)`,
`∫_{(0,∞)} Wlam s · √(H s) ds ≤ √W2 · √(∫_{(0,∞)} H)`. -/
theorem WlamSqrtMarginal {H : ℝ → ℝ}
    (hHnn : ∀ s, 0 ≤ H s) (hH : MeasureTheory.IntegrableOn H (Set.Ioi 0)) :
    ∫ s in Set.Ioi 0, Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)
      ≤ Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (∫ s in Set.Ioi 0, H s) := by
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
    (u := Work.FTS.GalBasis.cc.Wlam) (v := fun s : ℝ => Real.sqrt (H s))
    (s := Set.Ioi (0 : ℝ)) memLp_wlam (memLp_sqrt hHnn hH)
  -- `∫ (√H)² = ∫ H` on `(0,∞)`
  have hsq : ∫ s in Set.Ioi (0 : ℝ), Real.sqrt (H s) ^ 2 = ∫ s in Set.Ioi (0 : ℝ), H s :=
    setIntegral_congr_fun measurableSet_Ioi fun s _ => Real.sq_sqrt (hHnn s)
  rw [hsq] at hcs
  -- `W2` *is* `∫_{(0,∞)} Wlam²`, so the second factor can be named
  have hW2 : Real.sqrt (∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s ^ 2)
      = Real.sqrt Work.FTS.GalBasis.cc.W2 := by
    simp only [Work.FTS.GalBasis.cc.W2]
  calc ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)
      = |∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)| :=
        (abs_of_nonneg (integral_wlam_sqrt_nonneg H)).symm
    _ ≤ Real.sqrt (∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s ^ 2)
          * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), H s) := hcs
    _ = Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), H s) := by
        rw [hW2]

end Work.FTS.StrongEps.E5Aux3
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.ae_slice_lintegral_lt_top =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A.e. finiteness of the `σ`-slices of a diagonal-energy family

`ae_slice_lintegral_lt_top` is the `L¹`-to-`L^∞`-in-`σ` bridge of the diagonal-energy argument:
from a *uniform-in-`σ`* bound `∫_p (V σ p)² ρ p ≤ K` (for `σ ∈ [0,T]`) it concludes that for a.e.
`p` (with respect to the diagonal measure `diaM = dz dθ` on the quadrant) either `ρ p = 0` or the
`σ`-slice `σ ↦ (V σ p)²` is `lintegral`-finite over the bounded set `Ioc a b`.

The proof is Fubini/Tonelli in *both* orders for the jointly measurable function

`q ↦ ofReal ((V q.1 q.2.1 q.2.2)²) * ofReal (ρ q.2.1 q.2.2)`

on the product `(volume.restrict (Ioc a b)).prod diaM`.  Writing `G p = ∫⁻σ in Ioc a b,
ofReal ((V σ p)²)` and `c p = ofReal (ρ p)`, the two orders of Tonelli give

`∫⁻ p, G p * c p = ∫⁻ σ in Ioc a b, ∫⁻ p, ofReal ((V σ p)²) * c p ≤ ofReal K * vol (Ioc a b) < ⊤`,

where the middle inequality uses the per-`σ` hypothesis `hK` (via
`ofReal_integral_eq_lintegral_ofReal`, which needs the nonnegativity `hρnn`).  Finiteness of that
`lintegral` then forces `G p * c p < ⊤` for a.e. `p` (`ae_lt_top'`), and `G p * c p < ⊤` together
with `0 ≤ ρ p` splits into `ρ p = 0` or `G p < ⊤`.

The point of stating the conclusion a.e. (and with the `ρ p = 0` escape) is that **no**
measurability of the `σ`-slice `σ ↦ V σ p` is assumed — this is exactly the shape in which the
diagonal-energy estimates of the `ε`-scheme supply their data.
-/

namespace Work.FTS.StrongEps.EpsE4Thr


end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.aemeasurable_udot_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `aemeasurable_udot_slice`

If a family `(σ, p) ↦ u σ p.1 p.2` has a.e.-measurable slices in `σ` and is, for a.e. `p`,
differentiable in `σ` on `(0,T)` with derivative `udot σ p.1 p.2`, then the time-derivative slice
`p ↦ udot τ p.1 p.2` is a.e.-measurable (for every `τ ∈ (0,T)`).

The proof is the classical "derivative = limit of difference quotients" argument: on the conull set
of `p` where the derivative exists at `τ`, the sequence of difference quotients
`(c k)⁻¹ * (u (τ + c k) p.1 p.2 - u τ p.1 p.2)` with `c k = ((T-τ)/2)/(k+1)` converges to
`udot τ p.1 p.2`; each term is a.e.-measurable (a fixed real multiple of a difference of two
a.e.-measurable slices), and an a.e. limit of a.e.-measurable functions is a.e.-measurable
(`aemeasurable_of_tendsto_metrizable_ae'`).  The sequence `c k` is scaled by `(T-τ)/2` so that
`τ + c k ∈ (0,T)` for *every* `k`, which is what lets us invoke the hypothesis `hu`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Work.FTS.StrongEps.EpsE4Thr



end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.integrable_uncurry_of_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongEps.EpsE4Thr


end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSq_const_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-- `H^k`-squared is homogeneous of degree two in the amplitude.

`HkSq` is the iterated integral (over `[0,∞) × [0,π/2]`, measure `dz dθ`) of the integrand
`HkIntegrand`, which is a sum of squares of expressions that are *linear* in `f`.  The pointwise
homogeneity of the integrand,
`HkIntegrand α k (fun z θ => c * f z θ) z θ = c ^ 2 * HkIntegrand α k f z θ`
(proved unconditionally in `Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul`: `deriv` is scalar
homogeneous with no differentiability hypothesis), reduces the claim to the unconditional
linearity of the Lebesgue integral in a constant factor,
`∫ θ in Iθ, c ^ 2 * g θ = c ^ 2 * ∫ θ in Iθ, g θ`, applied once to the inner and once to the
outer integral.  No regularity or integrability hypothesis on `f` is needed. -/
theorem HkSq_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => c * f z θ) = c ^ 2 * Work.Spaces.HkSq α k f := by
  have hpoint : ∀ z θ : ℝ,
      Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ
        = c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α k c f z θ
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z
    rw [funext (fun θ => hpoint z θ)]
    exact MeasureTheory.integral_const_mul (c ^ 2)
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  simp only [hinner]
  exact MeasureTheory.integral_const_mul (c ^ 2)
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.EndsBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Two elementary helpers

The estimate is the crudest possible one: on the whole angular interval `Iθ` the integrand
`(K θ · Sw θ)²` is bounded by `9` (`K ≤ 3` and `Sw ≤ 1` there), while the two end-pieces
`Iθ ∖ Icc ε (π/2-ε)` sit inside `Icc 0 ε ∪ Icc (π/2-ε) (π/2)`, a set of total length `2ε`.
Hence `K2 = 18` works. -/





end Work.FTS.StrongEps.L12
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.WSwBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Two elementary monotonicity facts

* `Work.Spaces.w z = (1+z)²/z² = (1 + 1/z)²` is antitone on `(0,∞)`;
* on `[ε, π/2-ε]` (with `ε ≤ π/4`) the function `θ ↦ sin(2θ)` stays above `sin(2ε)`,
  by symmetry about `θ = π/4` and monotonicity of `sin` on `[0,π/2]`.
-/






end Work.FTS.StrongEps.L12
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.WlamCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.StrongEps.L12
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.WlamSqIoo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.StrongEps.L12
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.GamJetBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false

/-! ## Elementary consequences of `Γ ≤ 1` and `1/10 ≤ c ≤ 10` -/

/-- On `Iθ`, `(Γ/c)² ≤ 100` for `0 < α ≤ 1`. -/
private lemma gamCoef_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 100 := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hdiv : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hcpos]
    nlinarith
  have hdiv0 : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α := div_nonneg hG0 hcpos.le
  nlinarith [hdiv, hdiv0]

/-- On `Iθ`, `(Γ/c)² ≤ 100 Γ²` for `0 < α ≤ 1` (used to exploit the vanishing of `Γ`). -/
private lemma gamCoef_sq_le_gamSq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 100 * Work.Spaces.Gam α θ ^ 2 := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hinv : (Work.Spaces.c α)⁻¹ ≤ 10 := by
    rw [inv_le_iff_one_le_mul₀ hcpos]
    linarith
  have h2 : ((Work.Spaces.c α)⁻¹) ^ 2 ≤ 100 := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr hcpos.le) hinv 2
    nlinarith [h]
  rw [div_eq_mul_inv, mul_pow]
  have hG2 : 0 ≤ Work.Spaces.Gam α θ ^ 2 := sq_nonneg _
  calc Work.Spaces.Gam α θ ^ 2 * (Work.Spaces.c α)⁻¹ ^ 2
      ≤ Work.Spaces.Gam α θ ^ 2 * 100 := mul_le_mul_of_nonneg_left h2 hG2
    _ = 100 * Work.Spaces.Gam α θ ^ 2 := by ring

/-! ## The quantitative jet bound for `Γ/c` -/

/-- **Jet bound with the factor `α`.**  For `1 ≤ i ≤ 4` and `θ ∈ Iθ`,
`|D_θ^i (Γ/c)| ≤ α · 10⁵ · (Γ/c)`.

The factor `α` is what makes the subsequent `∫ (D_θ^i(Γ/c))² sin(2θ)^{-γ}` estimate
uniform in `α`: near `θ = 0` the jet vanishes like `Γ ∼ θ^{α/3}`, and the extra `α` exactly
compensates the `1/α` in `∫ sin(2θ)^{17α/30-1} = 3000/(17α)`. -/
private lemma gamCoef_jet_le (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ 4) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ|
      ≤ α * 100000 * (Work.Spaces.Gam α θ / Work.Spaces.c α) := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  rw [Work.FTS.LocData.DthIter_rad_eq]
  rw [show (fun t : ℝ => Work.Spaces.Gam α t / Work.Spaces.c α)
      = (fun t : ℝ => (Work.Spaces.c α)⁻¹ * Work.Spaces.Gam α t) from by
    funext t; rw [div_eq_inv_mul]]
  rw [Work.Spaces.dthU_iter_const_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hcpos.le)]
  have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i hi1 α hα 100000
    (fun θ' _ => Work.FTS.LocData.Tfun_abs_le (i - 1) (by omega) α hα hα1 θ')
  have hb := hkey θ hθ
  have h1 : (Work.Spaces.c α)⁻¹ * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ (Work.Spaces.c α)⁻¹ * (α * 100000 * Work.Spaces.Gam α θ) :=
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hcpos.le)
  have h2 : (Work.Spaces.c α)⁻¹ * (α * 100000 * Work.Spaces.Gam α θ)
      = α * 100000 * (Work.Spaces.Gam α θ / Work.Spaces.c α) := by
    rw [div_eq_mul_inv]; ring
  exact h1.trans (le_of_eq h2)

/-! ## Measurability of the jet (needed for `IntegrableOn`) -/

/-- `dthU^[m] g` is Borel measurable for every `m ≥ 1`, with no hypothesis on `g`
(and for `m = 0` when `g` is measurable): `dthU` multiplies `deriv` by `sin(2·)`, and
`measurable_deriv` is unconditional. -/
private lemma measurable_dthU_iter (g : ℝ → ℝ) (hg : Measurable g) (m : ℕ) :
    Measurable (Work.Spaces.dthU^[m] g) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      show Measurable (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[m] g) θ)
      exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id))).mul
        (measurable_deriv _)

/-- The angular jet of `Γ/c`, as a function of `θ`, is Borel measurable. -/
private lemma measurable_gamCoef_jet (i : ℕ) (α : ℝ) :
    Measurable (fun θ => Work.Spaces.DthIter i
      (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) := by
  have hfun : (fun θ => Work.Spaces.DthIter i
        (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ)
      = fun θ => (Work.Spaces.c α)⁻¹ * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ := by
    funext θ
    rw [Work.FTS.LocData.DthIter_rad_eq]
    rw [show (fun t : ℝ => Work.Spaces.Gam α t / Work.Spaces.c α)
        = (fun t : ℝ => (Work.Spaces.c α)⁻¹ * Work.Spaces.Gam α t) from by
      funext t; rw [div_eq_inv_mul]]
    rw [Work.Spaces.dthU_iter_const_mul]
  rw [hfun]
  exact measurable_const.mul (measurable_dthU_iter _ (by simp only [Work.Spaces.Gam]; fun_prop) i)

/-! ## The pointwise domination of the `γ`-weighted jet -/

/-- **Pointwise domination.**  On `Iθ`, for `1 ≤ i ≤ 4`,

`(D_θ^i (Γ/c))² sin(2θ)^{-γ(α)} ≤ α² · 10¹² · sin(2θ)^{17α/30-1}`,

and the exponent `17α/30 - 1 = 2α/3 - γ(α)` satisfies `-1 < 17α/30 - 1 ≤ 0`. -/
private lemma gamCoef_gam_pt_le (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ 4) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hX0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
      (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  have hXg : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hX0 _
  have hXp : 0 ≤ (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := Real.rpow_nonneg hX0 _
  have hjet := gamCoef_jet_le i hi1 hi α hα hα1 hθ
  have hD2 : (Work.Spaces.DthIter i
        (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
      ≤ (α * 100000) ^ 2 * (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 := by
    rw [← sq_abs]
    have h := pow_le_pow_left₀ (abs_nonneg _) hjet 2
    rwa [mul_pow] at h
  have hcx := gamCoef_sq_le_gamSq α hα hα1 hθ
  have hgs := Work.FTS.LocData.GamSq_sin_neg_gam_le α hα hα1 hθ
  have hstep1 : (Work.Spaces.DthIter i
        (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ((α * 100000) ^ 2 * (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_right hD2 hXg
  have hstep2 : ((α * 100000) ^ 2 * (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ((α * 100000) ^ 2 * (100 * Work.Spaces.Gam α θ ^ 2))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    apply mul_le_mul_of_nonneg_right _ hXg
    exact mul_le_mul_of_nonneg_left hcx (by positivity)
  have hstep4 : (α * 100000) ^ 2 * 100 * (Work.Spaces.Gam α θ ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (α * 100000) ^ 2 * 100 * (2 ^ (-(2 * α / 3))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) :=
    mul_le_mul_of_nonneg_left hgs (by positivity)
  have hbc : (α * 100000) ^ 2 * 100 * 2 ^ (-(2 * α / 3)) ≤ α ^ 2 * 10 ^ 12 := by
    have h2 : (2 : ℝ) ^ (-(2 * α / 3)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith : -(2 * α / 3) ≤ 0)
    calc (α * 100000) ^ 2 * 100 * 2 ^ (-(2 * α / 3))
        ≤ (α * 100000) ^ 2 * 100 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = α ^ 2 * 10 ^ 12 := by ring
  calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ((α * 100000) ^ 2 * (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := hstep1
    _ ≤ ((α * 100000) ^ 2 * (100 * Work.Spaces.Gam α θ ^ 2))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := hstep2
    _ = (α * 100000) ^ 2 * 100 * (Work.Spaces.Gam α θ ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ ≤ (α * 100000) ^ 2 * 100 * (2 ^ (-(2 * α / 3))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) := hstep4
    _ = ((α * 100000) ^ 2 * 100 * 2 ^ (-(2 * α / 3)))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by ring
    _ ≤ α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) :=
        mul_le_mul_of_nonneg_right hbc hXp

/-! ## The two angular mass estimates -/

/-- **The `η`-weighted mass of `Γ/c`.**  `∫_{Iθ} (Γ/c)² sin(2θ)^{-η} ≤ 10⁶` for `0 < α ≤ 1`. -/
private lemma gamCoef_eta_integral_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 1000000 := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsin2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
      (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  have hη1 : -1 < -(Work.Spaces.eta) := by simp only [Work.Spaces.eta]; norm_num
  have hη0 : -(Work.Spaces.eta) ≤ 0 := by simp only [Work.Spaces.eta]; norm_num
  obtain ⟨hInt, hBd⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hη1 hη0
  have hBd' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 10000 := by
    have heq : 100 / (-(Work.Spaces.eta) + 1) = 10000 := by
      simp only [Work.Spaces.eta]; norm_num
    rwa [heq] at hBd
  have h100 : MeasureTheory.IntegrableOn
      (fun θ => 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    hInt.const_mul 100
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    have hX : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_nonneg (hsin2 θ hθ) _
    have h2 := gamCoef_sq_le α hα hα1 hθ
    nlinarith [h2, hX]
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  have hIntf : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    h100.mono' hmeas (by
      filter_upwards [hpt, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2 θ h2) _))]
      exact h1)
  refine ⟨hIntf, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hIntf h100 hpt
  calc ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ ∫ θ in Work.Spaces.Iθ, 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := hmono
    _ = 100 * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ 100 * 10000 := by linarith [hBd']
    _ = 1000000 := by norm_num

/-- **The `γ`-weighted mass of the jet of `Γ/c`.**  For `1 ≤ i ≤ 4` and `0 < α ≤ 1`,

`∫_{Iθ} (D_θ^i (Γ/c))² sin(2θ)^{-γ(α)} ≤ 10¹⁵`. -/
private lemma gamCoef_gam_integral_le (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ 4) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DthIter i
          (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DthIter i
          (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 10 ^ 15 := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsin2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
      (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  have hp1 : -1 < 17 * α / 30 - 1 := by linarith
  have hp2 : 17 * α / 30 - 1 ≤ 0 := by linarith
  obtain ⟨hIntS, hBdS⟩ := Work.Spaces.sin_two_rpow (17 * α / 30 - 1) hp1 hp2
  have hBdS' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)
      ≤ 3000 / (17 * α) := by
    have heq : 100 / ((17 * α / 30 - 1) + 1) = 3000 / (17 * α) := by field_simp; ring
    rwa [heq] at hBdS
  have hdom : MeasureTheory.IntegrableOn
      (fun θ => α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
      Work.Spaces.Iθ := hIntS.const_mul _
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    exact gamCoef_gam_pt_le i hi1 hi α hα hα1 hθ
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.DthIter i
          (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) := by
    have hD := measurable_gamCoef_jet i α
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.gam]
    fun_prop
  have hIntf : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DthIter i
          (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
    hdom.mono' hmeas (by
      filter_upwards [hpt, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2 θ h2) _))]
      exact h1)
  refine ⟨hIntf, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hIntf hdom hpt
  calc ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DthIter i
        (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ∫ θ in Work.Spaces.Iθ,
          α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := hmono
    _ = α ^ 2 * 10 ^ 12
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ α ^ 2 * 10 ^ 12 * (3000 / (17 * α)) :=
        mul_le_mul_of_nonneg_left hBdS' (by positivity)
    _ = 10 ^ 12 * 3000 * α / 17 := by field_simp
    _ ≤ 10 ^ 15 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 17)]
        nlinarith [hα1]

/-! ## The target -/

theorem GamJetBounds : ∃ K : ℝ, 0 < K ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ i ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ => Work.Spaces.Gam α θ) 0 θ| ≤ K) ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ K) ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.DthIter i
            (fun _ θ => Work.Spaces.Gam α θ / Work.Spaces.c α) 0 θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DthIter i
            (fun _ θ => Work.Spaces.Gam α θ / Work.Spaces.c α) 0 θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ K) := by
  refine ⟨10 ^ 15, by norm_num, ?_, ?_, ?_⟩
  · intro α hα hα1 i hi θ hθ
    have hkey := Work.FTS.LocData.DthIter_Gam_abs_le i hi α hα hα1 hθ
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    nlinarith [hkey, hG1, hG0]
  · intro α hα hα1
    obtain ⟨h1, h2⟩ := gamCoef_eta_integral_le α hα hα1
    exact ⟨h1, h2.trans (by norm_num)⟩
  · intro α hα hα1 i hi1 hi
    exact gamCoef_gam_integral_le i hi1 hi α hα hα1

end Work.FTS.StrongPersist.L3Aux
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.HkMem_zero_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- At level `k = 0` the `ℋ⁰`-integrand collapses to a single square: the `D_z`-sum has the one
term `i = 0` and the mixed double sum is empty. -/
theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- The radial slot weight `z ↦ w z` is continuous on `(0,∞)`. -/
theorem continuousOn_w : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
  show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
  refine ContinuousOn.div ?_ ?_ ?_
  · exact ((continuous_const.add continuous_id).pow 2).continuousOn
  · exact (continuous_id.pow 2).continuousOn
  · intro z hz
    exact pow_ne_zero 2 (ne_of_gt hz)

/-- The angular slot weight `θ ↦ sin(2θ)^{η/2}` is continuous on `(0,π/2)`. -/
theorem continuousOn_sin_two_rpow :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo (0 : ℝ) (π / 2)) := by
  refine ContinuousOn.rpow_const ?_ ?_
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  · intro θ _
    exact Or.inr (by rw [Work.Spaces.eta]; norm_num)

/-- The full slot weight `(z,θ) ↦ w z / sin(2θ)^{η/2}` is continuous on the open quadrant. -/
theorem continuousOn_slotWeight :
    ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  refine ContinuousOn.div ?_ ?_ ?_
  · exact continuousOn_w.comp continuousOn_fst (fun p hp => hp.1)
  · exact continuousOn_sin_two_rpow.comp continuousOn_snd (fun p hp => hp.2)
  · intro p hp
    have h2 : 0 < Real.sin (2 * p.2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])
    exact ne_of_gt (Real.rpow_pos_of_pos h2 _)

/-- The `ℋ⁰`-integrand of a function continuous on the open quadrant is continuous there. -/
theorem continuousOn_HkIntegrand_zero (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
  ContinuousOn.congr ((hf.mul continuousOn_slotWeight).pow 2)
    (fun p _ => HkIntegrand_zero_eq α f p.1 p.2)

/-- `(x - y)² ≤ 2x² + 2y²` (the elementary majorant used below). -/
private theorem sq_sub_le_two (x y : ℝ) : (x - y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x + y)]

theorem HkMem_zero_diff {α : ℝ} {Ψ Ψ' : ℝ → ℝ → ℝ}
    (hΨ : Work.Spaces.HkMem α 0 Ψ) (hΨ' : Work.Spaces.HkMem α 0 Ψ')
    (hbΨ : Work.FTS_EllLimOK.BoxReg Ψ) (hbΨ' : Work.FTS_EllLimOK.BoxReg Ψ') :
    Work.Spaces.HkMem α 0 (Work.FTS_EllLimOK.diff Ψ Ψ') := by
  -- The difference of two `BoxReg` profiles is continuous on the open quadrant.
  have hcont : ContinuousOn (Function.uncurry (diff Ψ Ψ'))
      (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    ((BoxReg.diff hbΨ hbΨ').contDiffOn_Qd).continuousOn
  refine Work.FTS.LocData.HkMem_of_majorant α 0
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 Ψ z θ
      + 2 * Work.Spaces.HkIntegrand α 0 Ψ' z θ)
    (continuousOn_HkIntegrand_zero α hcont) ?_ ?_ ?_
  · -- the angular slices of the majorant are integrable
    intro z hz
    exact ((hΨ.1 z hz).const_mul 2).add ((hΨ'.1 z hz).const_mul 2)
  · -- the `θ`-integral of the majorant is integrable
    refine MeasureTheory.IntegrableOn.congr_fun
      ((hΨ.2.const_mul 2).add (hΨ'.2.const_mul 2)) ?_ measurableSet_Ici
    intro z hz
    show 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ)
      = ∫ θ in Work.Spaces.Iθ, (2 * Work.Spaces.HkIntegrand α 0 Ψ z θ
          + 2 * Work.Spaces.HkIntegrand α 0 Ψ' z θ)
    rw [integral_add ((hΨ.1 z hz).const_mul 2) ((hΨ'.1 z hz).const_mul 2),
      integral_const_mul, integral_const_mul]
  · -- the pointwise domination by the majorant
    intro z _ θ _
    rw [HkIntegrand_zero_eq α (diff Ψ Ψ') z θ, HkIntegrand_zero_eq α Ψ z θ,
      HkIntegrand_zero_eq α Ψ' z θ, diff_apply]
    nlinarith [sq_sub_le_two
      (Ψ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (Ψ' z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]

end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ThetaJets.wlam_sqrt_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ThetaJets

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The radial Cauchy–Schwarz inequality against the weight `Wlam s = s/(1+s)²`

`Wlam` is square-integrable on `(0,∞)` (with `∫ Wlam² = W2`) and is nonnegative there, so
for any nonnegative integrable `F` the pairing `∫_{(0,∞)} Wlam·√F` is dominated by the
`L²`-norms of the two factors:

  `∫_{(0,∞)} Wlam s · √(F s) ds ≤ √W2 · √(∫_{(0,∞)} F)`.

Both the finiteness of the left-hand side (through `2ab ≤ a² + b²`) and the sharp constant
(pure Cauchy–Schwarz) are recorded below.  The consumer only ever instantiates `F` with the
angular marginal `s ↦ ∫_θ HkIntegrand α k g s θ` (see `wlam_sqrt_le`), but the statement is
kept general so that it can be reused for other radial profiles. -/


end Work.FTS_EllLimOK.ThetaJets
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN0.L12_sub_of_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLipC.RowN0

/-- (namespace `Work.FTS_MuLipC.RowN0`) **Additivity of `L₁₂` at `z = 0` in subtraction form.**
If the two `L₁₂`-densities are integrable on `(0,∞)` and the two angular slices
`θ ↦ K(θ)·a r θ/r`, `θ ↦ K(θ)·b r θ/r` are integrable on `Iθ` for every `r > 0`, then
`L₁₂ a 0 − L₁₂ b 0 = L₁₂ (a − b) 0`.  Proof: both sides unfold to integrals of densities; the
density of the difference is the difference of the densities on `(0,∞)`
(`Work.FTS.LocData.L12dens_add_of_integrableOn` applied to `a` and `−b`, together with
`Work.FTS.LocData.L12dens_const_mul`), and the two outer Bochner integrals split by
`MeasureTheory.integral_sub` (the density of `−b` is integrable because `L12dens_const_mul`
gives `L12dens (fun z θ => -b z θ) = - L12dens b` unconditionally, and `hBb` is integrable). -/
theorem L12_sub_of_integrable {a b : ℝ → ℝ → ℝ}
    (hBa : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi (0 : ℝ)))
    (hBb : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi (0 : ℝ)))
    (hSa : ∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * a r θ / r) Work.Spaces.Iθ)
    (hSb : ∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * b r θ / r) Work.Spaces.Iθ) :
    Work.Construction.L12 a 0 - Work.Construction.L12 b 0
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) 0 := by
  -- `a - b` is `a + (-b)`, and `-b` is the constant `(-1)` multiple of `b`
  have hfun_sub : (fun z θ => a z θ - b z θ) = (fun z θ => a z θ + (-b z θ)) := by
    funext z θ; ring
  have hfun_neg : (fun z θ => -b z θ) = (fun z θ => (-1 : ℝ) * b z θ) := by
    funext z θ; rw [neg_one_mul]
  -- the angular slices of `-b = (-1)·b` are integrable
  have hSneg : ∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * (-b r θ) / r) Work.Spaces.Iθ := by
    intro r hr
    have hfun : (fun θ : ℝ => Work.Spaces.K θ * (-b r θ) / r)
        = fun θ : ℝ => - (Work.Spaces.K θ * b r θ / r) := by
      funext θ; ring
    rw [hfun]
    exact (hSb r hr).neg
  -- the density of `-b` is minus the density of `b`, hence integrable
  have hdens_neg : Work.Construction.L12dens (fun z θ => -b z θ)
      = fun s => - Work.Construction.L12dens b s := by
    funext s
    rw [hfun_neg]
    show Work.FM.L12dens Work.Spaces.K (fun z θ => (-1 : ℝ) * b z θ) s
      = - Work.FM.L12dens Work.Spaces.K b s
    rw [Work.FTS.LocData.L12dens_const_mul Work.Spaces.K (-1) b s, neg_one_mul]
  have hBneg : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (fun z θ => -b z θ)) (Set.Ioi (0 : ℝ)) := by
    rw [hdens_neg]; exact hBb.neg
  -- additivity of the outer integral
  have hadd : Work.Construction.L12 (fun z θ => a z θ + (-b z θ)) 0
      = Work.Construction.L12 a 0 + Work.Construction.L12 (fun z θ => -b z θ) 0 := by
    simp only [Work.Construction.L12, Work.FM.L12]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun s hs => Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
        (hSa s hs) (hSneg s hs))]
    exact MeasureTheory.integral_add hBa hBneg
  -- homogeneity in the constant `-1`
  have hneg : Work.Construction.L12 (fun z θ => -b z θ) 0
      = - Work.Construction.L12 b 0 := by
    rw [hfun_neg, (Work.FTS.LocData.L12_add_mul (-1) hSb hSa hBb hBa).2, neg_one_mul]
  rw [eq_comm, hfun_sub, hadd, hneg]
  ring

end Work.FTS_MuLipC.RowN0
end
-- ===== merged: Submission.Work.H2.WPQ.DzIter_Wt_sq_le_Aang_Rho =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.WPQ


end Work.H2.WPQ
end
-- ===== merged: Submission.Work.H2.WPQ.HkIntegrand_le_GmajQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.WPQ


end Work.H2.WPQ
end
-- ===== merged: Submission.Work.H2.WPQ.aesm_slice_mixed_Wt_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.WPQ

set_option autoImplicit false

/-! ## Continuity of the weighted mixed slot on the open quadrant

The integrand `(z,θ) ↦ (D_z^jD_θ^i f z θ · W z θ)²` is continuous on the open quadrant
`(0,∞) × (0,π/2)`: the mixed derivative is `C^∞` there because `f` is `C^∞` on the larger
strip `(-1,∞) × (0,π/2)` in which the open quadrant sits, and `W = w · sin(2θ)^{-γ/2}` is
continuous there since `z > 0` and `0 < θ < π/2`.  The open quadrant differs from
`Iz ×ˢ Iθ` by the three null segments `{0} × Iθ`, `Iz × {0}`, `Iz × {π/2}`, which is what
`Work.Spaces.aesm_slice_of_continuousOn_Qd` turns into a.e. strong measurability. -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
private abbrev QdW : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

private lemma QdW_subset_quadU : QdW ⊆ Work.Spaces.quadU :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) subset_rfl

/-- `sin (2θ) > 0` for `θ ∈ (0, π/2)`. -/
private lemma sin_two_pos_QdW {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The product weight `W = w · w_θ` is continuous on the open quadrant. -/
private lemma continuousOn_Wt_QdW (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) QdW := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) QdW := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsp : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      QdW :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (sin_two_pos_QdW hp.2)))
  have hmul := hw.mul hsp
  have heq : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        * (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) := rfl
  rw [heq]
  exact hmul

/-- The mixed derivative `D_z^jD_θ^i f` is continuous on the open quadrant. -/
private lemma continuousOn_mixed_QdW (f : ℝ → ℝ → ℝ) (hf : Work.FTS.LocData.SmoothQuad f)
    (j i : ℕ) : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2) QdW :=
  ((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf j i).continuousOn).mono
    QdW_subset_quadU

/-- **A.e. strong measurability of a weighted mixed derivative in the interior class.**  For `g`
smooth on the open quadrant and `z > 0`, the `θ`-slice of `(D_z^j D_θ^i g · W)²` is a.e. strongly
measurable for the restricted Lebesgue measure on `Iθ`.  (The function is continuous on the open
quadrant, which differs from `Iθ` only in the two endpoints: `(z,θ) ↦ mixed j i f z θ` is
continuous there by `Work.FTS.LocData.contDiffOn_mixed`, and `Wt α z θ = w z · sin(2θ)^{-γ/2}`
is continuous there because `z > 0` and `0 < θ < π/2`; then
`Work.Spaces.aesm_slice_of_continuousOn_Qd` upgrades continuity on the open square to a.e. strong
measurability on `Iθ`.) -/
theorem aesm_slice_mixed_Wt_sq (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2) ?_ hz
  exact ((continuousOn_mixed_QdW f hf j i).mul (continuousOn_Wt_QdW α)).pow 2

end Work.H2.WPQ
end
end
-- ===== merged: Submission.Work.H2.WPQ.hardy_term_le_GmajQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.WPQ

open scoped Real


end Work.H2.WPQ
end
-- ===== merged: Submission.Work.Spaces.SmoothStripDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The corrected smoothness class** (rescope note option (ii), with the joint condition on the
full neighbourhood of the closed quadrant): `f` is `C^∞` (honest order, not analyticity) on
`(-1,∞) × (-1, π/2+1)`, jointly in `(z,θ)`; its `θ`-slices are `C^∞` on `Ioo (-1) (π/2+1)`
(one-sided at the boundary angles) and its `z`-slices are `C^∞` on `Ioi (-1)`.

The joint component already implies the two slice components (see the projections below); they
are recorded in the definition because they are what the consumers of the class use and because
they are the part that the truncation route supplies directly. -/
def SmoothStrip (f : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) ∧
    (∀ z ∈ Set.Ioi (-1),
      ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => f z θ) (Set.Ioo (-1) (Real.pi / 2 + 1))) ∧
    (∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ Work.Stability.smoothOrder (fun z => f z θ) (Set.Ioi (-1)))





/-- `n ≤ smoothOrder` for every `n : ℕ`, in the `C^n`-order `ℕ∞ω`. -/
theorem natCast_le_smoothOrder (n : ℕ) :
    ((n : ℕ∞) : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
  rw [Work.Stability.smoothOrder]
  exact WithTop.coe_le_coe.mpr le_top









/-! ## Compatibility names (kept from the first version of this file) -/



end Work.Spaces
end
