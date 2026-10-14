import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.N6.Exc6
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.excMeanSide6
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.VocabO
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The two bundles -/

/-- **The honest `g`-side bundle** of the level-4 transport clauses: `C^∞` on the open
quadrant, honesty in `ℋ⁴` and `ℋ⁵`, and the mixed radial decay of order `4`. -/
structure HonG (α : ℝ) (g : Fn) : Prop where
  sm : Work.FTS.EllipticEst.SmoothOpen g
  hk4 : Work.Spaces.HkMem α 4 g
  hk5 : Work.Spaces.HkMem α 5 g
  dec : Work.Spaces.DecayAll 4 g

/-- **The `f`-side bundle** of the level-4 transport clauses (verbatim `T2SF`). -/
def HonF (α : ℝ) (f : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen f ∧ Work.Spaces.HkMem α 4 f ∧
    Work.FTS.VocabO.CoefThMem 1 f

theorem HonF.sm {α : ℝ} {f : Fn} (h : HonF α f) : Work.FTS.EllipticEst.SmoothOpen f := h.1
theorem HonF.hk {α : ℝ} {f : Fn} (h : HonF α f) : Work.Spaces.HkMem α 4 f := h.2.1
theorem HonF.coef {α : ℝ} {f : Fn} (h : HonF α f) : Work.FTS.VocabO.CoefThMem 1 f := h.2.2


/-- The honest `g`-bundle supplies the open-quadrant smoothness of every mixed slot. -/
theorem HonG.mixed {α : ℝ} {g : Fn} (h : HonG α g) (j i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.mixed j i g) := h.sm.mixed j i

/-! ## The honest order-`≤ 2` sup bound -/

/-- **The honest sup bound.**  For `g` in the open-quadrant class `HQo α 4 = SmoothOpen ∧
HkMem α 4`, every mixed slot of order `≤ 2` is pointwise bounded by
`√C / √(γ-1) · |g|_{ℋ⁴}` with a universal `C` — the open-quadrant form of Elgindi's
`SecondDerivativesBounded` (`OpenPkg.ProdOpen.PwAny`).  This replaces the frozen
`T2Qaux.supQ_T2Q` in the honest route. -/
theorem pwAny_sup : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ|
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 g := by
  obtain ⟨C, hC, h⟩ := Work.FTS.OpenPkg.ProdOpen.PwAny
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro α g b a hα hα1 hsm hm hab z θ hz hθ hθ2
  have hg1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hsq := h α g b a hα hα1 hsm hm hab z hz θ ⟨hθ, hθ2⟩
  have hXn : Work.Spaces.HkSq α 4 g = (Work.Spaces.HkNorm α 4 g) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 g)]
  rw [hXn, div_mul_eq_mul_div] at hsq
  have hsq' : (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ (Real.sqrt C / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 g) ^ 2 := by
    have hmul : C * (Work.Spaces.HkNorm α 4 g) ^ 2 / (Work.Spaces.gam α - 1)
        = (Real.sqrt C / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 g) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hC.le, Real.sq_sqrt hg1.le]
      ring
    linarith [hsq, hmul.le, hmul.ge]
  calc |Work.Spaces.mixed b a g z θ|
      = Real.sqrt ((Work.Spaces.mixed b a g z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Real.sqrt C / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 g) ^ 2) := Real.sqrt_le_sqrt hsq'
    _ = Real.sqrt C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 g :=
        Real.sqrt_sq (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (Work.Spaces.HkNorm_nonneg α 4 g))

/-! ## The abstract vanishing of a dominated primitive -/


/-! ## The two `Prop`s -/

/-- **The honest top-slot radial integration by parts** (`a + b = 4`).  For `0 < α ≤ 1`,
`f` with open-quadrant smoothness and the two pointwise bounds `|f|, |D_z f| ≤ Mf`, and `g`
in the honest bundle, the top pairing with the canonical weight `canonW q` (`q ≤ γ`, and
`q ≤ η` when `a = 0`) is bounded by `C·Mf·|g|²_{ℋ⁴}`.

This is the replacement of `TransportS.T2Sup.Main.topSlotBound`, whose boundary hypothesis is
the per-angle vanishing `z (D_z^bD_θ^a g · w)² → 0` (`BdryTraces`); the honest proof uses
`HkMem α 4 g`/`HkMem α 5 g` (integrability of the slots of order `4` and `5`) instead. -/
def TopSlotHonProp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (q Mf : ℝ),
    0 < α → α ≤ 1 → 0 ≤ Mf → a + b = 4 → (a = 0 → q ≤ Work.Spaces.eta) →
    q ≤ Work.Spaces.gam α →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.DecayAll 4 g → Work.Spaces.HkMem α 4 g → Work.Spaces.HkMem α 5 g →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf) →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dz f z θ| ≤ Mf) →
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
      ≤ C * Mf * Work.Spaces.HkSq α 4 g

/-- **The honest delicate bound** (the paper's delicate term of the transport estimate): the
same estimate as `TransportS.T2Sup.DelicateProp` with the honest `g`-bundle in place of
`T2SG α g`. -/
def DelicateHonProp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α q : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → 0 ≤ q → q ≤ Work.Spaces.gam α →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.VocabO.CoefThMem 1 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
      ≤ C * α ^ (-(1 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.Spaces.HkSq α 4 g

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5Dth2Six =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0)
open Work.FTS.OpenPkg.ProdOpen (sob_theta_mean sin_two_pos ae_mem_Ioo_Iθ deriv_mixed_weight
  aesm_integral_right sin_neg_gam_nonneg continuousOn_sin_neg_gam continuousOn_w_Q0
  continuousOn_w_sq continuousOn_Wt L2Mem_congr_pt L2Sq_congr_pt)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## The `f`-side: the angular mean-term bound for the top slot `D_z⁵` -/

/-- **The mean-term bound for the top radial slot.**  For `f` with `SmoothOpen f` and
`HkMem α 6 f`, the slice `θ ↦ D_z⁵f(z,θ)` obeys the angular Agmon-type inequality

  `(D_z⁵f(z,θ))² ≤ C (∫_θ (D_z⁵f(z,·))² + (γ-1)⁻¹ ∫_θ (D_z⁵D_θf(z,·))² sin(2·)^{-γ})`

at every interior angle, with `C` universal.

This is the shared library lemma `Work.FTS.StrongPersist.N6Trans.T1SixAux.excMeanSide6`
(proved in `T1SixAux/excMeanSide6.lean` as `Work.FTS.OpenPkg.ProdOpen.sob_theta_mean` —
universal constant `204` — applied to the slice `h := D_z⁵f(z,·)`: the derivative term
`∫ (∂_θh)² sin(2·)^{2-γ}` is the mixed slot `∫ (mixed 5 1 f)² sin(2·)^{-γ}` by
`deriv_mixed_weight`, and the two integrability hypotheses are `integrableOn_dzIter5_sq` and
`integrableOn_slice_neg_gam6`).  It is recorded here under its local name for the consumers of
this module. -/
theorem excMeanSide6Aux : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    SmoothOpen f → HkMem α 6 f → ∀ z : ℝ, 0 < z →
    ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (DzIter 5 f z θ) ^ 2
        ≤ C * ((∫ σ in Iθ, (DzIter 5 f z σ) ^ 2)
          + (gam α - 1)⁻¹ * ∫ σ in Iθ, (mixed 5 1 f z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (-(gam α))) :=
  excMeanSide6

/-! ## Integrability of the exceptional integrand at every `z > 0` -/

/-- **The exceptional integrand is a.e. integrable in `θ` at every `z > 0`.**  For `f`, `g` of
class `SmoothOpen` with honest `ℋ⁶`-membership, a mixed slot `D_z^bD_θ^a g` (`1 ≤ a`,
`a + b ≤ 6`) and the mean-term bound on the slice `D_z⁵f(z,·)`, the square of
`D_z⁵f · D_z^bD_θ^a g · W` is integrable over `Iθ` at every `z > 0`.

The mean-term bound turns the radial factor into the constant `K`; the angular factor is the
integrable slot `(mixed b a g z ·)² sin(2·)^{-γ}` (`integrableOn_slice_neg_gam6`). -/
theorem integrableOn_excA6_mixed {α : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ} (hF : SmoothOpen f)
    (hmemF : HkMem α 6 f) (hG : SmoothOpen g) (hmemG : HkMem α 6 g)
    {b a : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 6)
    {C1 : ℝ} (hC1pos : 0 < C1)
    (hC1 : ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (DzIter 5 f z θ) ^ 2 ≤ C1 * ((∫ σ in Iθ, (DzIter 5 f z σ) ^ 2)
        + (gam α - 1)⁻¹ * ∫ σ in Iθ, (mixed 5 1 f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(gam α))))
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (DzIter 5 f z θ * mixed b a g z θ
      * Wt α z θ) ^ 2) Iθ := by
  set K : ℝ := C1 * ((∫ σ in Iθ, (DzIter 5 f z σ) ^ 2)
    + (gam α - 1)⁻¹ * ∫ σ in Iθ, (mixed 5 1 f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(gam α))) with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    refine mul_nonneg hC1pos.le ?_
    refine add_nonneg (integral_nonneg fun σ => sq_nonneg _) ?_
    have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
    exact mul_nonneg (inv_nonneg.mpr hγ.le)
      (setIntegral_nonneg measurableSet_Icc fun σ hσ =>
        mul_nonneg (sq_nonneg _) (sin_neg_gam_nonneg hσ))
  have hGint : IntegrableOn (fun θ => (mixed b a g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α))) Iθ :=
    Work.FTS.StrongPersist.N6.integrableOn_slice_neg_gam6 hα hG hmemG b a ha (by omega) hz
  refine Integrable.mono' (hGint.const_mul (K * (w z) ^ 2)) ?_ ?_
  · have hcont : ContinuousOn (fun θ : ℝ => (DzIter 5 f z θ
        * mixed b a g z θ * Wt α z θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h1 : ContinuousOn (fun θ : ℝ => DzIter 5 f z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hF.DzIter 5).curry_θ hz).continuousOn
      have h2 : ContinuousOn (fun θ : ℝ => mixed b a g z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hG.mixed b a).curry_θ hz).continuousOn
      have hb : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(gam α / 2)))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        (show Continuous fun θ : ℝ => Real.sin (2 * θ) from by fun_prop).continuousOn.rpow_const
          (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))
      have h3 : ContinuousOn (fun θ : ℝ => Wt α z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
        have hfun : (fun θ : ℝ => Wt α z θ)
            = fun θ : ℝ => w z
              * (Real.sin (2 * θ)) ^ (-(gam α / 2)) := by
          funext θ; rw [Wt, wTheta]
        rw [hfun]
        exact continuousOn_const.mul hb
      exact ((h1.mul h2).mul h3).pow 2
    exact Work.H2.T1Q.aesm_Iθ_of_continuousOn hcont
  · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hsin : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have h1 := hC1 z hz θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [show (DzIter 5 f z θ * mixed b a g z θ * Wt α z θ) ^ 2
        = ((DzIter 5 f z θ) ^ 2 * (w z) ^ 2)
          * ((mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) from by
      rw [mul_pow, mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hsin]
      ring]
    rw [← hKdef] at h1
    have hstep : (DzIter 5 f z θ) ^ 2 * (w z) ^ 2 ≤ K * (w z) ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right hstep
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _))

/-! ## The exceptional term, for a general mixed slot on the `g`-side -/

/-- **The exceptional `D_z⁵`-term with a general mixed `g`-slot**: the function
`D_z⁵p · D_z^bD_θ^a q · W` (`1 ≤ a`, `a + b ≤ 5`) is square integrable and its `L²`-square is
bounded by `C (γ-1)⁻¹ |p|²_{ℋ⁶} |q|²_{ℋ⁶}`, with `C` universal. -/
theorem excDz5_mixed_pair_bound (b a : ℕ) (ha : 1 ≤ a) (hab : a + b ≤ 5) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (p q : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    SmoothOpen p → HkMem α 6 p → SmoothOpen q → HkMem α 6 q →
    L2Mem (fun z θ => DzIter 5 p z θ * mixed b a q z θ * Wt α z θ) ∧
    L2Sq (fun z θ => DzIter 5 p z θ * mixed b a q z θ * Wt α z θ)
      ≤ C / (gam α - 1) * HkSq α 6 p * HkSq α 6 q := by
  obtain ⟨C1, hC1pos, hC1⟩ := excMeanSide6Aux
  obtain ⟨Cq, hCqpos, hCq⟩ := Work.FTS.StrongPersist.N6.sliceAng_le6
  have hMq : (0 : ℝ) < max Cq 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨2 * C1 * max Cq 1, by positivity, ?_⟩
  intro α p q hα hα1 hP hmemP hQ hmemQ
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγle : gam α - 1 ≤ 1 := by rw [gam_sub_one]; linarith
  have hHkP : 0 ≤ HkSq α 6 p := HkSq_nonneg α 6 p
  have hHkQ : 0 ≤ HkSq α 6 q := HkSq_nonneg α 6 q
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγ.le
  set M1 : ℝ → ℝ := fun z => ∫ θ in Iθ, (DzIter 5 p z θ) ^ 2 with hM1def
  set M2 : ℝ → ℝ := fun z => ∫ θ in Iθ, (mixed 5 1 p z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) with hM2def
  set J : ℝ → ℝ := fun z => ∫ θ in Iθ, (mixed b a q z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) with hJdef
  have hM1val : ∀ z : ℝ, M1 z = ∫ θ in Iθ, (DzIter 5 p z θ) ^ 2 := fun z => by
    simp only [hM1def]
  have hM2val : ∀ z : ℝ, M2 z = ∫ θ in Iθ, (mixed 5 1 p z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) := fun z => by simp only [hM2def]
  have hJval : ∀ z : ℝ, J z = ∫ θ in Iθ, (mixed b a q z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) := fun z => by simp only [hJdef]
  have hM1nn : ∀ z, 0 ≤ M1 z := fun z => by
    rw [hM1val z]; exact integral_nonneg fun θ => sq_nonneg _
  have hM2nn : ∀ z, 0 ≤ M2 z := fun z => by
    rw [hM2val z]; exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sin_neg_gam_nonneg hθ)
  have hJnn : ∀ z, 0 ≤ J z := fun z => by
    rw [hJval z]; exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sin_neg_gam_nonneg hθ)
  -- (1) the `q`-side is uniformly bounded by the `ℋ⁶`-norm of `q`
  have hJbd : ∀ z : ℝ, 0 < z → J z ≤ max Cq 1 * HkSq α 6 q := by
    intro z hz
    have h := hCq α q b a hα hα1 hQ hmemQ ha hab z hz
    rw [hJval z]
    exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left Cq 1) hHkQ)
  -- (2) the angular mean-term estimate on the `p`-slice, at every `z > 0`
  have hsob : ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (DzIter 5 p z θ) ^ 2 ≤ C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) := by
    intro z hz θ hθ
    have h := hC1 α p hα hα1 hP hmemP z hz θ hθ
    simpa only [hM1val z, hM2val z] using h
  -- (3) pointwise domination of the two slice integrals by the `ℋ⁶`-integrand of `p`
  have hM1dom : ∀ z : ℝ, 0 < z →
      M1 z * (w z) ^ 2 ≤ ∫ θ in Iθ, HkIntegrand α 6 p z θ := by
    intro z hz
    have hfeq : M1 z * (w z) ^ 2
        = ∫ θ in Iθ, (DzIter 5 p z θ) ^ 2 * (w z) ^ 2 := by
      rw [hM1val z]
      exact (integral_mul_const ((w z) ^ 2)
        (fun θ : ℝ => (DzIter 5 p z θ) ^ 2)).symm
    rw [hfeq]
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ _ =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hmemP.1 z hz.le) ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    exact Work.FTS.StrongPersist.N6.dzIter_sq_w_sq_le6 α hα p 5 hz hθ (by norm_num)
  have hM2dom : ∀ z : ℝ, 0 < z →
      M2 z * (w z) ^ 2 ≤ ∫ θ in Iθ, HkIntegrand α 6 p z θ := by
    intro z hz
    have hfeq : M2 z * (w z) ^ 2 = ∫ θ in Iθ, (mixed 5 1 p z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2 := by
      rw [hM2val z]
      have hfun : (fun θ : ℝ => (mixed 5 1 p z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2)
          = fun θ : ℝ => ((mixed 5 1 p z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(gam α))) * (w z) ^ 2 := rfl
      rw [hfun]
      exact (integral_mul_const ((w z) ^ 2)
        (fun θ : ℝ => (mixed 5 1 p z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(gam α)))).symm
    rw [hfeq]
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (sin_neg_gam_nonneg hθ)) (sq_nonneg _))
      (hmemP.1 z hz.le) ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hsin : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hkey : (mixed 5 1 p z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
          * (w z) ^ 2
        = (mixed 5 1 p z θ * Wt α z θ) ^ 2 := by
      rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hsin]; ring
    rw [hkey]
    exact sq_le_HkIntegrand_mixed α 6 p z θ 1 5 (by norm_num) (by norm_num)
  -- (4) a.e. strong measurability and `z`-integrability of the two slice integrals
  have hAESM1 : AEStronglyMeasurable (fun z : ℝ => M1 z * (w z) ^ 2) (volume.restrict Iz) := by
    have hcont : ContinuousOn (Function.uncurry
        (fun z θ : ℝ => (DzIter 5 p z θ) ^ 2 * (w z) ^ 2)) Q0 := by
      show ContinuousOn (fun u : ℝ × ℝ => (DzIter 5 p u.1 u.2) ^ 2
        * (w u.1) ^ 2) Q0
      exact ((hP.DzIter 5).continuousOn.pow 2).mul continuousOn_w_sq
    have h := aesm_integral_right (F := fun z θ =>
      (DzIter 5 p z θ) ^ 2 * (w z) ^ 2) hcont
    have h2 : (fun z : ℝ => ∫ θ in Iθ, (DzIter 5 p z θ) ^ 2 * (w z) ^ 2)
        = fun z : ℝ => M1 z * (w z) ^ 2 := by
      funext z
      rw [hM1val z]
      exact integral_mul_const ((w z) ^ 2)
        (fun θ : ℝ => (DzIter 5 p z θ) ^ 2)
    rwa [h2] at h
  have hAESM2 : AEStronglyMeasurable (fun z : ℝ => M2 z * (w z) ^ 2) (volume.restrict Iz) := by
    have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
        (mixed 5 1 p z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2)) Q0 := by
      show ContinuousOn (fun u : ℝ × ℝ => (mixed 5 1 p u.1 u.2) ^ 2
        * (Real.sin (2 * u.2)) ^ (-(gam α)) * (w u.1) ^ 2) Q0
      exact (((hP.mixed 5 1).continuousOn.pow 2).mul (continuousOn_sin_neg_gam α)).mul
        continuousOn_w_sq
    have h := aesm_integral_right (F := fun z θ => (mixed 5 1 p z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2) hcont
    have h2 : (fun z : ℝ => ∫ θ in Iθ, (mixed 5 1 p z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2)
        = fun z : ℝ => M2 z * (w z) ^ 2 := by
      funext z
      rw [hM2val z]
      exact integral_mul_const ((w z) ^ 2)
        (fun θ : ℝ => (mixed 5 1 p z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(gam α)))
    rwa [h2] at h
  have hAESMJ : AEStronglyMeasurable J (volume.restrict Iz) := by
    have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
        (mixed b a q z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)))) Q0 := by
      show ContinuousOn (fun u : ℝ × ℝ => (mixed b a q u.1 u.2) ^ 2
        * (Real.sin (2 * u.2)) ^ (-(gam α))) Q0
      exact ((hQ.mixed b a).continuousOn.pow 2).mul (continuousOn_sin_neg_gam α)
    exact aesm_integral_right (F := fun z θ => (mixed b a q z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α))) hcont
  have hInt1 : Integrable (fun z : ℝ => M1 z * (w z) ^ 2) (volume.restrict Iz) := by
    refine Integrable.mono' hmemP.2 hAESM1 ?_
    filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (hM1nn z) (sq_nonneg _))]
    exact hM1dom z hz
  have hInt2 : Integrable (fun z : ℝ => M2 z * (w z) ^ 2) (volume.restrict Iz) := by
    refine Integrable.mono' hmemP.2 hAESM2 ?_
    filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (hM2nn z) (sq_nonneg _))]
    exact hM2dom z hz
  have hz1 : (∫ z in Iz, M1 z * (w z) ^ 2) ≤ HkSq α 6 p := by
    have h := integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (hM1nn z) (sq_nonneg _)) hmemP.2
      (by filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz; exact hM1dom z hz)
    exact h
  have hz2 : (∫ z in Iz, M2 z * (w z) ^ 2) ≤ HkSq α 6 p := by
    have h := integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (hM2nn z) (sq_nonneg _)) hmemP.2
      (by filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz; exact hM2dom z hz)
    exact h
  -- (5) the per-`z` bound on the angular integral of the exceptional integrand
  have hzpt : ∀ z : ℝ, 0 < z → (∫ θ in Iθ, (DzIter 5 p z θ
        * mixed b a q z θ * Wt α z θ) ^ 2)
      ≤ C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2 * J z := by
    intro z hz
    have hGint := (Work.FTS.StrongPersist.N6.integrableOn_slice_neg_gam6 hα hQ hmemQ b a
      ha (by omega) hz).const_mul
      (C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2)
    have hpt : ∀ᵐ θ ∂(volume.restrict Iθ),
        (DzIter 5 p z θ * mixed b a q z θ * Wt α z θ) ^ 2
        ≤ (C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2)
          * ((mixed b a q z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      have hsin : 0 < Real.sin (2 * θ) := sin_two_pos hθ
      have h1 := hsob z hz θ hθ
      rw [show (DzIter 5 p z θ * mixed b a q z θ * Wt α z θ) ^ 2
          = ((DzIter 5 p z θ) ^ 2 * (w z) ^ 2)
            * ((mixed b a q z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) from by
          rw [mul_pow, mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hsin]; ring]
      have hstep : (DzIter 5 p z θ) ^ 2 * (w z) ^ 2
          ≤ C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hstep
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _))
    refine le_trans (integral_mono_of_nonneg ?_ hGint hpt) ?_
    · exact ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => sq_nonneg _
    · rw [integral_const_mul, hJval z]
  -- (6) integrability of the `max`-majorant
  have hmajInt : Integrable (fun z : ℝ => C1 * (M1 z + (gam α - 1)⁻¹ * M2 z)
      * (w z) ^ 2 * (max Cq 1 * HkSq α 6 q)) (volume.restrict Iz) := by
    have hbase : Integrable (fun z : ℝ => C1 * (max Cq 1 * HkSq α 6 q) * (M1 z * (w z) ^ 2)
        + C1 * (max Cq 1 * HkSq α 6 q) * ((gam α - 1)⁻¹ * (M2 z * (w z) ^ 2)))
        (volume.restrict Iz) :=
      (hInt1.const_mul (C1 * (max Cq 1 * HkSq α 6 q))).add
        ((hInt2.const_mul (gam α - 1)⁻¹).const_mul (C1 * (max Cq 1 * HkSq α 6 q)))
    refine Integrable.mono' hbase ?_ ?_
    · have h1 : AEStronglyMeasurable (fun z : ℝ => C1 * (max Cq 1 * HkSq α 6 q)
          * (M1 z * (w z) ^ 2)
          + C1 * (max Cq 1 * HkSq α 6 q) * ((gam α - 1)⁻¹ * (M2 z * (w z) ^ 2)))
          (volume.restrict Iz) :=
        (hAESM1.const_mul _).add ((hAESM2.const_mul _).const_mul _)
      refine h1.congr ?_
      filter_upwards with z
      ring
    · filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC1pos.le
        (add_nonneg (hM1nn z) (mul_nonneg hγinv (hM2nn z)))) (sq_nonneg _))
        (mul_nonneg hMq.le hHkQ))]
      ring_nf
      nlinarith [hM1nn z, hM2nn z, sq_nonneg (w z), hγinv, hHkP, hHkQ, hMq]
  -- (7) the `L²`-square bound
  have hL2Sq : L2Sq (fun z θ => DzIter 5 p z θ * mixed b a q z θ
        * Wt α z θ)
      ≤ 2 * C1 * max Cq 1 / (gam α - 1) * HkSq α 6 p * HkSq α 6 q := by
    rw [L2Sq]
    have hB : (∫ z in Iz, ∫ θ in Iθ, (DzIter 5 p z θ * mixed b a q z θ
          * Wt α z θ) ^ 2)
        ≤ ∫ z in Iz, C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2
            * (max Cq 1 * HkSq α 6 q) := by
      refine integral_mono_of_nonneg ?_ hmajInt ?_
      · exact ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
          integral_nonneg fun θ => sq_nonneg _
      · filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
        exact le_trans (hzpt z hz) (mul_le_mul_of_nonneg_left (hJbd z hz) (mul_nonneg
          (mul_nonneg hC1pos.le (add_nonneg (hM1nn z) (mul_nonneg hγinv (hM2nn z))))
          (sq_nonneg _)))
    refine le_trans hB ?_
    have hC : (∫ z in Iz, C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2
          * (max Cq 1 * HkSq α 6 q))
        = C1 * (max Cq 1 * HkSq α 6 q) * ((∫ z in Iz, M1 z * (w z) ^ 2)
            + (gam α - 1)⁻¹ * (∫ z in Iz, M2 z * (w z) ^ 2)) := by
      have hfun1 : (fun z : ℝ => C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2
            * (max Cq 1 * HkSq α 6 q))
          = fun z : ℝ => (C1 * (max Cq 1 * HkSq α 6 q))
            * ((M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2) := by
        funext z; ring
      rw [hfun1, integral_const_mul]
      have hfun2 : (fun z : ℝ => (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2)
          = fun z : ℝ => M1 z * (w z) ^ 2
            + ((gam α - 1)⁻¹ * (M2 z * (w z) ^ 2)) := by
        funext z; ring
      rw [hfun2, integral_add hInt1 (hInt2.const_mul (gam α - 1)⁻¹)]
      rw [integral_const_mul]
    rw [hC]
    have hX : (∫ z in Iz, M1 z * (w z) ^ 2) + (gam α - 1)⁻¹
          * (∫ z in Iz, M2 z * (w z) ^ 2)
        ≤ 2 * (gam α - 1)⁻¹ * HkSq α 6 p := by
      have h1 : (1 : ℝ) ≤ (gam α - 1)⁻¹ := by
        rw [one_le_inv₀ hγ]; simpa using hγle
      have hA1 : (∫ z in Iz, M1 z * (w z) ^ 2) ≤ (gam α - 1)⁻¹ * HkSq α 6 p :=
        le_trans hz1 (le_mul_of_one_le_left hHkP h1)
      have hA2 : (gam α - 1)⁻¹ * (∫ z in Iz, M2 z * (w z) ^ 2)
          ≤ (gam α - 1)⁻¹ * HkSq α 6 p := mul_le_mul_of_nonneg_left hz2 hγinv
      linarith
    have hfac : 0 ≤ C1 * (max Cq 1 * HkSq α 6 q) :=
      mul_nonneg hC1pos.le (mul_nonneg hMq.le hHkQ)
    have hstep := mul_le_mul_of_nonneg_left hX hfac
    refine le_trans hstep (le_of_eq ?_)
    rw [div_eq_mul_inv]; ring
  refine ⟨⟨?_, ?_⟩, hL2Sq⟩
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · subst h0
      have hzero : (fun θ : ℝ => (DzIter 5 p 0 θ * mixed b a q 0 θ
          * Wt α 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        have hw0 : w (0 : ℝ) = 0 := by simp [w]
        simp [Wt, hw0]
      rw [hzero]
      exact integrableOn_zero
    · exact integrableOn_excA6_mixed hα hP hmemP hQ hmemQ ha (by omega) hC1pos
        (fun z hz θ hθ => hsob z hz θ hθ) hpos
  · have haesm : AEStronglyMeasurable (fun z : ℝ => ∫ θ in Iθ,
        (DzIter 5 p z θ * mixed b a q z θ * Wt α z θ) ^ 2)
        (volume.restrict Iz) := by
      refine aesm_integral_right (F := fun z θ => (DzIter 5 p z θ
        * mixed b a q z θ * Wt α z θ) ^ 2) ?_
      have hW := continuousOn_Wt (α := α)
      exact (((hP.DzIter 5).continuousOn.mul (hQ.mixed b a).continuousOn).mul hW).pow 2
    refine Integrable.mono' hmajInt haesm ?_
    filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact le_trans (hzpt z hz) (mul_le_mul_of_nonneg_left (hJbd z hz) (mul_nonneg
      (mul_nonneg hC1pos.le (add_nonneg (hM1nn z) (mul_nonneg hγinv (hM2nn z))))
      (sq_nonneg _)))

/-! ## The requested exceptional term -/


end Work.FTS.StrongPersist.N6Trans.T1SixAux
end
end
-- ===== merged: Submission.Work.FTS.TransportS.SlotT2.slotCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.SlotT2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The two-level Cauchy–Schwarz bound for a pair of canonical slots

The slot bound `Work.FTS.TransportS.SlotT2.slotCS` is *not* proved by the two-step
(`θ`-then-`z`) route described in its docstring, but by a strictly shorter one that uses
the pointwise slot domination of `Basic.lean` first and then a *single* level of
Cauchy–Schwarz (in `L²` of the product `z`-measure):

* `canonW q z θ · (X z θ)² ≤ HkIntegrand α 4 f z θ` for every slot `X` of `ℋ⁴` (this is
  `canonW_mul_z_le` for a pure `D_z`-slot and `canonW_mul_mixed_le` for a mixed slot);
* hence, pointwise on `Iθ`, `canonW q z θ |X| |Y| = √(canonW q z θ X²) · √(canonW q z θ Y²)
  ≤ √(HkIntegrand α 4 f z θ) · √(HkIntegrand α 4 g z θ)`;
* two applications of `cs_sqrt_le` (the square-root form of the `L²` Cauchy–Schwarz
  inequality on a set) then give

  `∫_z∫_θ canonW q |X| |Y| ≤ √(∫_z (∫_θ HkIntegrand α 4 f)) · √(∫_z (∫_θ HkIntegrand α 4 g))`,

  and the two factors are `HkSq α 4 f`, `HkSq α 4 g` by definition.  So the constant is
  `C = 1`, and none of the measurability bookkeeping of `Basic.lean` (beyond the
  integrability of the `θ`-slices and of the marginals, which is `HkMem`) is needed. -/

/-- **The square-root form of the Cauchy–Schwarz inequality on a set.**  For nonnegative
functions `A`, `B` integrable on `s`,

  `∫_s √A · √B ≤ √(∫_s A) · √(∫_s B)`.

This is `Work.Spaces.cs_integral` applied to `u = √A`, `v = √B` (which are in `L²` precisely
because `√A ^ 2 = A` pointwise), followed by `√(∫A · ∫B) = √(∫A)·√(∫B)`. -/
theorem cs_sqrt_le {s : Set ℝ} {A B : ℝ → ℝ}
    (hA : IntegrableOn A s) (hB : IntegrableOn B s)
    (hAnn : ∀ x, 0 ≤ A x) (hBnn : ∀ x, 0 ≤ B x) :
    (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) := by
  have hu_meas : AEStronglyMeasurable (fun x => Real.sqrt (A x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hv_meas : AEStronglyMeasurable (fun x => Real.sqrt (B x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hu_sq : Integrable (fun x => Real.sqrt (A x) ^ 2) (volume.restrict s) :=
    hA.congr (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (hAnn x)).symm))
  have hv_sq : Integrable (fun x => Real.sqrt (B x) ^ 2) (volume.restrict s) :=
    hB.congr (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (hBnn x)).symm))
  have hu_lp : MemLp (fun x => Real.sqrt (A x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hv_lp : MemLp (fun x => Real.sqrt (B x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have hcs := Work.Spaces.cs_integral hu_lp hv_lp
  have e1 : (∫ x in s, Real.sqrt (A x) ^ 2) = ∫ x in s, A x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hAnn x))
  have e2 : (∫ x in s, Real.sqrt (B x) ^ 2) = ∫ x in s, B x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hBnn x))
  rw [e1, e2] at hcs
  calc (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt ((∫ x in s, A x) * (∫ x in s, B x)) := Real.le_sqrt_of_sq_le hcs
    _ = Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) :=
        Real.sqrt_mul (integral_nonneg hAnn) _

/-! ## Slots of `ℋ⁴` -/

/-- A function `X` is a canonical slot of `ℋ⁴` for the datum `f` with exponent `q` if its
`canonW q`-weighted square is dominated, pointwise on `Iz × Iθ`, by the `ℋ⁴`-integrand of `f`.
This is the only property of a slot that the Cauchy–Schwarz bound uses. -/
structure SlotW (α q : ℝ) (X : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  le : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
    canonW q z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ

/-- A pure `D_z`-slot `D_z^j f`, `j ≤ 4`, priced with `q ≤ η`. -/
theorem slotW_z (α : ℝ) {q : ℝ} (hq0 : 0 < q) (hq : q ≤ Work.Spaces.eta)
    (f : ℝ → ℝ → ℝ) (j : ℕ) (hj : j ≤ 4) :
    SlotW α q (Work.Spaces.DzIter j f) f := by
  refine ⟨fun z hz θ hθ => ?_⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [canonW_zero_z, zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 4 f 0 θ
  · exact canonW_mul_z_le α f hq0 hq hz0 hθ j hj

/-- A mixed slot `D_z^j D_θ^i f`, `1 ≤ i`, `i + j ≤ 4`, priced with `q ≤ γ`. -/
theorem slotW_mixed (α : ℝ) {q : ℝ} (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α)
    (f : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    SlotW α q (Work.Spaces.mixed j i f) f := by
  refine ⟨fun z hz θ hθ => ?_⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [canonW_zero_z, zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 4 f 0 θ
  · exact canonW_mul_mixed_le α f hq0 hqγ hz0 hθ j i hi hij



end Work.FTS.TransportS.SlotT2
end
end
-- ===== merged: Submission.Work.FTS.TransportS.ip4SlotDomFixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Equality on the open quadrant gives equality of the integrals -/

/-- A.e. statement for the restricted measure on `Iz = [0,∞)`: it suffices to prove the
statement on the open half line, where the radial weight `w` does not vanish. -/
theorem ae_restrict_Iz_of_pos {p : ℝ → Prop} (h : ∀ z, 0 < z → p z) :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), p z := by
  rw [Work.Spaces.Iz, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => h z hz)

/-- **Two double integrals agree as soon as their integrands agree on the open quadrant**: the
complement of `Q0` in `Iz × Iθ` is `({0} × Iθ) ∪ (Ioi 0 × ({0} ∪ {π/2}))`, a null set. -/
theorem setIntegral2_congr_Q0 {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, G z θ := by
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_Iz_of_pos (p := fun z => 0 < z) (fun z hz => hz)] with z hz
  refine integral_congr_ae ?_
  refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => ?_)
  exact h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0, h1⟩)

/-! ## The operators respect equality on an open set -/

theorem pz_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) {p : ℝ × ℝ} (hp : p ∈ V) :
    Work.Spaces.pz g p.1 p.2 = Work.Spaces.pz g' p.1 p.2 :=
  Work.Spaces.pz_congr_of_isOpen hV h hp

theorem Dz_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz g)) (Function.uncurry (Work.Spaces.Dz g')) V := by
  intro p hp
  show p.1 * Work.Spaces.pz g p.1 p.2 = p.1 * Work.Spaces.pz g' p.1 p.2
  rw [pz_congrOn hV h hp]

theorem Dth_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth g)) (Function.uncurry (Work.Spaces.Dth g')) V := by
  intro p hp
  have hnb : ∀ᶠ θ' in 𝓝 p.2, (p.1, θ') ∈ V :=
    (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun θ' => Function.uncurry g (p.1, θ')) =ᶠ[𝓝 p.2]
      (fun θ' => Function.uncurry g' (p.1, θ')) := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  exact congrArg (fun t => Real.sin (2 * p.2) * t) hslice.deriv_eq

theorem DzIter_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b g))
      (Function.uncurry (Work.Spaces.DzIter b g')) V := by
  induction b with
  | zero => exact h
  | succ b ih => simpa only [Work.Spaces.DzIter_succ] using Dz_congrOn hV ih

theorem DthIter_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i g))
      (Function.uncurry (Work.Spaces.DthIter i g')) V := by
  induction i with
  | zero => exact h
  | succ i ih => simpa only [Work.Spaces.DthIter_succ] using Dth_congrOn hV ih

/-! ## Associativity of the iterates -/

/-- `D_z^b(D_z f) = D_z^{b+1} f` (pure bookkeeping, no smoothness). -/
theorem DzIter_comp (b : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter b (Work.Spaces.Dz f) = Work.Spaces.DzIter (b + 1) f := by
  induction b with
  | zero => rfl
  | succ b ih =>
      show Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dz f))
          = Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter b f))
      rw [ih]
      rfl

/-- `D_θ^a(D_θ f) = D_θ^{a+1} f` (pure bookkeeping, no smoothness). -/
theorem DthIter_comp (a : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter a (Work.Spaces.Dth f) = Work.Spaces.DthIter (a + 1) f := by
  induction a with
  | zero => rfl
  | succ a ih =>
      show Work.Spaces.Dth (Work.Spaces.DthIter a (Work.Spaces.Dth f))
          = Work.Spaces.Dth (Work.Spaces.Dth (Work.Spaces.DthIter a f))
      rw [ih]
      rfl

/-! ## `D_θ` commutes with the iterates of `D_z` on the open quadrant -/

/-- `D_θ(D_z X) = D_z(D_θ X)` at a point of the open quadrant where `X` is `C²` (Clairaut,
using `D_θ = sin(2θ)∂_θ` and `D_z = z∂_z`). -/
theorem Dth_Dz_apply_of {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Dth (Work.Spaces.Dz X) z θ = Work.Spaces.Dz (Work.Spaces.Dth X) z θ := by
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry X) (z, θ) :=
    (hX.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  have h1 : Work.Spaces.pth (Work.Spaces.Dz X) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz X) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz X z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz X z θ') θ
    rw [deriv_const_mul_field]
  have h2 : Work.Spaces.pz (Work.Spaces.Dth X) z θ
      = Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth X) z θ := by
    show deriv (fun z' => Real.sin (2 * θ) * Work.Spaces.pth X z' θ) z
      = Real.sin (2 * θ) * deriv (fun z' => Work.Spaces.pth X z' θ) z
    rw [deriv_const_mul_field]
  have h3 : Work.Spaces.pth (Work.Spaces.pz X) z θ = Work.Spaces.pz (Work.Spaces.pth X) z θ :=
    (Work.Spaces.pz_pth_comm hcd).symm
  show Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.Dz X) z θ
      = z * Work.Spaces.pz (Work.Spaces.Dth X) z θ
  rw [h1, h2, h3]
  ring

/-- `D_θ` can be moved across any iterate of `D_z` on the open quadrant. -/
theorem Dth_DzIter_eqOn {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b X)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth X))) Work.FTS.EllipticEst.Q0 := by
  induction b with
  | zero => intro p hp; rfl
  | succ b ih =>
      intro p hp
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hb : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter b X) := hX.DzIter b
      have h1 : Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b X)) p.1 p.2
          = Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b X)) p.1 p.2 :=
        Dth_Dz_apply_of hb hz ⟨hθ0, hθ1⟩
      have h2 : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b X)) p.1 p.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth X)) p.1 p.2 :=
        Dz_congrOn Work.FTS.EllipticEst.isOpen_Q0 ih hp
      show Work.Spaces.Dth (Work.Spaces.DzIter (b + 1) X) p.1 p.2
          = Work.Spaces.DzIter (b + 1) (Work.Spaces.Dth X) p.1 p.2
      rw [show Work.Spaces.DzIter (b + 1) X = Work.Spaces.Dz (Work.Spaces.DzIter b X) from rfl,
        show Work.Spaces.DzIter (b + 1) (Work.Spaces.Dth X)
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth X)) from rfl]
      exact h1.trans h2

/-- The iterates of `D_θ` can be moved across any iterate of `D_z` on the open quadrant. -/
theorem DthIter_DzIter_eqOn {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) (b i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter b X)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter i X)))
      Work.FTS.EllipticEst.Q0 := by
  induction i with
  | zero => intro p hp; rfl
  | succ i ih =>
      intro p hp
      have h1 : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b X)) p.1 p.2
          = Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i X)) p.1 p.2 :=
        Dth_congrOn Work.FTS.EllipticEst.isOpen_Q0 ih hp
      have h2 : Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i X)) p.1 p.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i X)) p.1 p.2 :=
        Dth_DzIter_eqOn (hX.DthIter i) b hp
      show Work.Spaces.DthIter (i + 1) (Work.Spaces.DzIter b X) p.1 p.2
          = Work.Spaces.DzIter b (Work.Spaces.DthIter (i + 1) X) p.1 p.2
      rw [show Work.Spaces.DthIter (i + 1) (Work.Spaces.DzIter b X)
            = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b X)) from rfl,
        show Work.Spaces.DthIter (i + 1) X = Work.Spaces.Dth (Work.Spaces.DthIter i X) from rfl]
      exact h1.trans h2

/-! ## The slot pairings shift along the operators -/

/-- `D_θ` shifts the slot index by one in the `θ`-direction:
`D_z^bD_θ^a(D_θ f) = D_z^bD_θ^{a+1} f` (no smoothness needed — pure associativity of the
iterates). -/
theorem mixed_dth (b a : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed b a (Work.Spaces.Dth f) = Work.Spaces.mixed b (a + 1) f := by
  show Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.Dth f))
      = Work.Spaces.DzIter b (Work.Spaces.DthIter (a + 1) f)
  rw [DthIter_comp]

/-- `D_z` shifts the slot index by one in the `z`-direction, on the open quadrant:
`D_z^bD_θ^a(D_z f) = D_z^{b+1}D_θ^a f` (this is where the commutation of `D_θ` with `D_z^b` is
used). -/
theorem mixed_dz_eqOn {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz u)))
      (Function.uncurry (Work.Spaces.mixed (b + 1) a u)) Work.FTS.EllipticEst.Q0 := by
  intro p hp
  have h2 := DzIter_congrOn Work.FTS.EllipticEst.isOpen_Q0
    (DthIter_DzIter_eqOn hu 1 a) b hp
  have h2' : Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.DzIter 1 u)) p.1 p.2
      = Work.Spaces.DzIter b (Work.Spaces.DzIter 1 (Work.Spaces.DthIter a u)) p.1 p.2 := h2
  show Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.DzIter 1 u)) p.1 p.2
      = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a u) p.1 p.2
  rw [h2']
  rw [show Work.Spaces.DzIter 1 (Work.Spaces.DthIter a u)
        = Work.Spaces.Dz (Work.Spaces.DthIter a u) from rfl, DzIter_comp]

/-- **The slot pairing shifts along `D_θ`.** -/
theorem slotPairing_dth (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (u v : Fn) :
    slotPairing ρ a b (Work.Spaces.Dth u) (Work.Spaces.Dth v)
      = slotPairing ρ (a + 1) b u v := by
  unfold slotPairing
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  rw [mixed_dth b a u, mixed_dth b a v]

/-- **The slot pairing shifts along `D_z`** (on the open quadrant). -/
theorem slotPairing_dz (ρ : ℝ → ℝ → ℝ) (a b : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    slotPairing ρ a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)
      = slotPairing ρ a (b + 1) u v := by
  unfold slotPairing
  refine setIntegral2_congr_Q0 (fun p hp => ?_)
  simp only [Function.uncurry]
  have h1 : Work.Spaces.mixed b a (Work.Spaces.Dz u) p.1 p.2
      = Work.Spaces.mixed (b + 1) a u p.1 p.2 := mixed_dz_eqOn hu b a hp
  have h2 : Work.Spaces.mixed b a (Work.Spaces.Dz v) p.1 p.2
      = Work.Spaces.mixed (b + 1) a v p.1 p.2 := mixed_dz_eqOn hv b a hp
  rw [h1, h2]

/-! ## The finite-sum API of the slot sums -/

/-- The slot sum is monotone in the level. -/
theorem SlotSum_mono {α : ℝ} {u v : Fn} {n m : ℕ} (h : n ≤ m) :
    SlotSum α n u v ≤ SlotSum α m u v := by
  rw [SlotSum_eq_sum_SlotTerm, SlotSum_eq_sum_SlotTerm]
  have hinner : ∀ a : ℕ, (∑ b ∈ Finset.range (n + 1 - a), SlotTerm α a b u v)
      ≤ ∑ b ∈ Finset.range (m + 1 - a), SlotTerm α a b u v := by
    intro a
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => ?_)
      (fun b _ _ => SlotTerm_nonneg α a b u v)
    simp only [Finset.mem_range] at hb ⊢
    omega
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a), SlotTerm α a b u v)
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1 - a), SlotTerm α a b u v :=
        Finset.sum_le_sum (fun a _ => hinner a)
    _ ≤ ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1 - a), SlotTerm α a b u v := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => ?_)
          (fun a _ _ => Finset.sum_nonneg (fun b _ => SlotTerm_nonneg α a b u v))
        simp only [Finset.mem_range] at ha ⊢
        omega

/-- Every single slot pairing with a leaf weight of the slot `(a,b)` is dominated by the slot
sum of any level `n ≥ a + b`. -/
theorem slotPairing_le_SlotSum {α : ℝ} {a b n : ℕ} {ρ : ℝ → ℝ → ℝ} (u v : Fn)
    (hρ : IsLeafW α a ρ) (hab : a + b ≤ n) :
    |slotPairing ρ a b u v| ≤ SlotSum α n u v := by
  have hT : |slotPairing ρ a b u v| ≤ SlotTerm α a b u v := by
    have h3 : (0 : ℝ) ≤ (if 1 ≤ a then |slotPairing (leafGam α) a b u v| else 0) := by
      by_cases h : 1 ≤ a
      · rw [if_pos h]; exact abs_nonneg _
      · rw [if_neg h]
    rcases hρ with rfl | rfl | ⟨ha, rfl⟩
    · unfold SlotTerm
      linarith [abs_nonneg (slotPairing leafOne a b u v)]
    · unfold SlotTerm
      linarith [abs_nonneg (slotPairing leafEta a b u v)]
    · unfold SlotTerm
      rw [if_pos ha]
      linarith [abs_nonneg (slotPairing leafEta a b u v),
        abs_nonneg (slotPairing leafOne a b u v)]
  rw [SlotSum_eq_sum_SlotTerm]
  calc |slotPairing ρ a b u v| ≤ SlotTerm α a b u v := hT
    _ ≤ ∑ b' ∈ Finset.range (n + 1 - a), SlotTerm α a b' u v :=
        Finset.single_le_sum (fun b' _ => SlotTerm_nonneg α a b' u v)
          (show b ∈ Finset.range (n + 1 - a) from Finset.mem_range.mpr (by omega))
    _ ≤ ∑ a' ∈ Finset.range (n + 1), ∑ b' ∈ Finset.range (n + 1 - a'),
          SlotTerm α a' b' u v :=
        Finset.single_le_sum
          (f := fun a' : ℕ => ∑ b' ∈ Finset.range (n + 1 - a'), SlotTerm α a' b' u v)
          (fun a' _ => Finset.sum_nonneg (fun b' _ => SlotTerm_nonneg α a' b' u v))
          (show a ∈ Finset.range (n + 1) from Finset.mem_range.mpr (by omega))

/-- `∑_{b < n+1} (if a + b ≤ n then f b else 0) = ∑_{b < n+1-a} f b`. -/
theorem sum_range_ite_eq (n a : ℕ) (f : ℕ → ℝ) (ha : a ≤ n) :
    (∑ b ∈ Finset.range (n + 1), (if a + b ≤ n then f b else 0))
      = ∑ b ∈ Finset.range (n + 1 - a), f b := by
  have hsub : Finset.range (n + 1 - a) ⊆ Finset.range (n + 1) := by
    intro b hb
    simp only [Finset.mem_range] at hb ⊢
    omega
  have hzero : ∀ b ∈ Finset.range (n + 1), b ∉ Finset.range (n + 1 - a) →
      (if a + b ≤ n then f b else 0) = 0 := by
    intro b hb hnb
    rw [if_neg]
    intro hle
    exact hnb (Finset.mem_range.mpr (by omega))
  have h1 : (∑ b ∈ Finset.range (n + 1 - a), f b)
      = ∑ b ∈ Finset.range (n + 1 - a), (if a + b ≤ n then f b else 0) := by
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [if_pos]
    simp only [Finset.mem_range] at hb
    omega
  have h2 : (∑ b ∈ Finset.range (n + 1 - a), (if a + b ≤ n then f b else 0))
      = ∑ b ∈ Finset.range (n + 1), (if a + b ≤ n then f b else 0) :=
    Finset.sum_subset hsub hzero
  exact h2.symm.trans h1.symm

/-- The repaired leaf sum is the slot sum of level `4`. -/
theorem leafSum_eq_SlotSum_four (α : ℝ) (u v : Fn) : leafSum α u v = SlotSum α 4 u v := by
  rw [SlotSum_eq_sum_SlotTerm]
  unfold leafSum
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have ha4 : a ≤ 4 := by
    have := Finset.mem_range.mp ha
    omega
  exact sum_range_ite_eq 4 a (fun b => SlotTerm α a b u v) ha4

/-- The `wip` pairing with the mixed derivative of a slot is the slot pairing. -/
theorem wip_eq_slotPairing (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (X Y : Fn) :
    Work.Coercivity.wip ρ (Work.Spaces.mixed b a X) (Work.Spaces.mixed b a Y)
      = slotPairing ρ a b X Y := by
  unfold Work.Coercivity.wip slotPairing
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  ring

/-- `H1IP` is the sum of its four slot pairings. -/
theorem H1IP_eq_slot_sum (α : ℝ) (u v : Fn) :
    Work.Coercivity.H1IP α u v
      = 10 * slotPairing leafEta 0 1 u v + (10 : ℝ) ^ 10 * slotPairing leafEta 0 0 u v
        + (10 : ℝ) ^ 17 * slotPairing leafOne 0 0 u v
        + (10 : ℝ) ^ 21 * slotPairing (leafGam α) 1 0 u v := by
  have h1 : Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Work.Spaces.Dz u) (Work.Spaces.Dz v) = slotPairing leafEta 0 1 u v :=
    wip_eq_slotPairing leafEta 0 1 u v
  have h2 : Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        u v = slotPairing leafEta 0 0 u v :=
    wip_eq_slotPairing leafEta 0 0 u v
  have h3 : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) u v
      = slotPairing leafOne 0 0 u v :=
    wip_eq_slotPairing leafOne 0 0 u v
  have h4 : Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Work.Spaces.Dth u) (Work.Spaces.Dth v) = slotPairing (leafGam α) 1 0 u v :=
    wip_eq_slotPairing (leafGam α) 1 0 u v
  unfold Work.Coercivity.H1IP
  rw [h1, h2, h3, h4]

/-- Absolute value of a four-term sum. -/
theorem abs_add_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  rw [show a + b + c + d = (a + b) + (c + d) from by ring]
  have h1 := abs_add_le (a + b) (c + d)
  have h2 := abs_add_le a b
  have h3 := abs_add_le c d
  linarith

/-- `|H1IP α u v|` is bounded by `10^22` times the slot sum of level `1`. -/
theorem H1IP_le_SlotSum_one (α : ℝ) (u v : Fn) :
    |Work.Coercivity.H1IP α u v| ≤ (10 : ℝ) ^ 22 * SlotSum α 1 u v := by
  rw [H1IP_eq_slot_sum]
  have hS := SlotSum_nonneg α 1 u v
  have hA : |slotPairing leafEta 0 1 u v| ≤ SlotSum α 1 u v :=
    slotPairing_le_SlotSum u v (Or.inl rfl) (show 0 + 1 ≤ 1 by norm_num)
  have hB : |slotPairing leafEta 0 0 u v| ≤ SlotSum α 1 u v :=
    slotPairing_le_SlotSum u v (Or.inl rfl) (show 0 + 0 ≤ 1 by norm_num)
  have hC : |slotPairing leafOne 0 0 u v| ≤ SlotSum α 1 u v :=
    slotPairing_le_SlotSum u v (Or.inr (Or.inl rfl)) (show 0 + 0 ≤ 1 by norm_num)
  have hD : |slotPairing (leafGam α) 1 0 u v| ≤ SlotSum α 1 u v :=
    slotPairing_le_SlotSum u v (Or.inr (Or.inr ⟨le_refl 1, rfl⟩))
      (show 1 + 0 ≤ 1 by norm_num)
  have h1 : |10 * slotPairing leafEta 0 1 u v| ≤ 10 * SlotSum α 1 u v := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10)]
    exact mul_le_mul_of_nonneg_left hA (by norm_num)
  have h2 : |(10 : ℝ) ^ 10 * slotPairing leafEta 0 0 u v|
      ≤ (10 : ℝ) ^ 10 * SlotSum α 1 u v := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < (10 : ℝ) ^ 10)]
    exact mul_le_mul_of_nonneg_left hB (by norm_num)
  have h3 : |(10 : ℝ) ^ 17 * slotPairing leafOne 0 0 u v|
      ≤ (10 : ℝ) ^ 17 * SlotSum α 1 u v := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < (10 : ℝ) ^ 17)]
    exact mul_le_mul_of_nonneg_left hC (by norm_num)
  have h4 : |(10 : ℝ) ^ 21 * slotPairing (leafGam α) 1 0 u v|
      ≤ (10 : ℝ) ^ 21 * SlotSum α 1 u v := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < (10 : ℝ) ^ 21)]
    exact mul_le_mul_of_nonneg_left hD (by norm_num)
  have hsplit := abs_add_four_le (10 * slotPairing leafEta 0 1 u v)
    ((10 : ℝ) ^ 10 * slotPairing leafEta 0 0 u v)
    ((10 : ℝ) ^ 17 * slotPairing leafOne 0 0 u v)
    ((10 : ℝ) ^ 21 * slotPairing (leafGam α) 1 0 u v)
  have hcoef : (10 : ℝ) + (10 : ℝ) ^ 10 + (10 : ℝ) ^ 17 + (10 : ℝ) ^ 21 ≤ (10 : ℝ) ^ 22 := by
    norm_num
  nlinarith [hsplit, h1, h2, h3, h4, hS, hcoef]

/-! ## The shift inequalities for the slot sums -/

/-- Termwise, `D_θ` moves a slot term to the next slot. -/
theorem SlotTerm_dth_le (α : ℝ) (a b : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    SlotTerm α a b (Work.Spaces.Dth u) (Work.Spaces.Dth v) ≤ SlotTerm α (a + 1) b u v := by
  have heta := slotPairing_dth leafEta a b u v
  have hone := slotPairing_dth leafOne a b u v
  have hgam := slotPairing_dth (leafGam α) a b u v
  have hthird : (if 1 ≤ a then |slotPairing (leafGam α) (a + 1) b u v| else 0)
      ≤ (if 1 ≤ a + 1 then |slotPairing (leafGam α) (a + 1) b u v| else 0) := by
    rw [if_pos (by omega : 1 ≤ a + 1)]
    by_cases ha : 1 ≤ a
    · rw [if_pos ha]
    · rw [if_neg ha]
      exact abs_nonneg _
  unfold SlotTerm
  rw [heta, hone, hgam]
  linarith [hthird]

/-- Termwise, `D_z` moves a slot term to the next slot. -/
theorem SlotTerm_dz_le (α : ℝ) (a b : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    SlotTerm α a b (Work.Spaces.Dz u) (Work.Spaces.Dz v) ≤ SlotTerm α a (b + 1) u v := by
  unfold SlotTerm
  rw [slotPairing_dz leafEta a b hu hv, slotPairing_dz leafOne a b hu hv,
    slotPairing_dz (leafGam α) a b hu hv]

/-- Shifting the slot sum along `D_θ` raises the level by one. -/
theorem SlotSum_dth_le (α : ℝ) (n : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    SlotSum α n (Work.Spaces.Dth u) (Work.Spaces.Dth v) ≤ SlotSum α (n + 1) u v := by
  rw [SlotSum_eq_sum_SlotTerm, SlotSum_eq_sum_SlotTerm]
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a b (Work.Spaces.Dth u) (Work.Spaces.Dth v))
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α (a + 1) b u v :=
        Finset.sum_le_sum (fun a _ =>
          Finset.sum_le_sum (fun b _ => SlotTerm_dth_le α a b hu hv))
    _ = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2 - (a + 1)),
          SlotTerm α (a + 1) b u v := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [show n + 2 - (a + 1) = n + 1 - a from Nat.succ_sub_succ (n := n + 1) (m := a)]
    _ ≤ ∑ a' ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2 - a'),
          SlotTerm α a' b u v := by
        conv_rhs => rw [Finset.sum_range_succ']
        exact le_add_of_nonneg_right
          (show (0 : ℝ) ≤ ∑ b ∈ Finset.range (n + 2 - 0), SlotTerm α 0 b u v from
            Finset.sum_nonneg (fun b _ => SlotTerm_nonneg α 0 b u v))

/-- Shifting the slot sum along `D_z` raises the level by one. -/
theorem SlotSum_dz_le (α : ℝ) (n : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    SlotSum α n (Work.Spaces.Dz u) (Work.Spaces.Dz v) ≤ SlotSum α (n + 1) u v := by
  rw [SlotSum_eq_sum_SlotTerm, SlotSum_eq_sum_SlotTerm]
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a b (Work.Spaces.Dz u) (Work.Spaces.Dz v))
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a (b + 1) u v :=
        Finset.sum_le_sum (fun a _ =>
          Finset.sum_le_sum (fun b _ => SlotTerm_dz_le α a b hu hv))
    _ ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2 - a),
          SlotTerm α a b u v := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        by_cases ha : a ≤ n + 1
        · rw [show n + 2 - a = (n + 1 - a) + 1 from by omega]
          conv_rhs => rw [Finset.sum_range_succ']
          exact le_add_of_nonneg_right
            (show (0 : ℝ) ≤ SlotTerm α a 0 u v from SlotTerm_nonneg α a 0 u v)
        · rw [show n + 1 - a = 0 from by omega]
          simp only [Finset.range_zero, Finset.sum_empty]
          exact Finset.sum_nonneg (fun b _ => SlotTerm_nonneg α a b u v)
    _ ≤ ∑ a' ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2 - a'),
          SlotTerm α a' b u v := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => ?_)
          (fun a _ _ => Finset.sum_nonneg (fun b _ => SlotTerm_nonneg α a b u v))
        simp only [Finset.mem_range] at ha ⊢
        omega

/-! ## The unfolding of the recursion -/

/-- **The induction of the unfolding.**  For every `n`, the `n`-fold iterate of the coercive
recursion is dominated by `3^n · 10^22` times the slot sum of level `n + 1`. -/
theorem ip4_unfold_bound :
    ∀ (n : ℕ) (α : ℝ) (u v : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
      |IPn α n u v| ≤ (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) u v := by
  intro n
  induction n with
  | zero =>
      intro α u v hu hv
      rw [show IPn α 0 = Work.Coercivity.H1IP α from rfl]
      simpa using H1IP_le_SlotSum_one α u v
  | succ n ih =>
      intro α u v hu hv
      have hIHu := ih α u v hu hv
      have hIHd := ih α (Work.Spaces.Dth u) (Work.Spaces.Dth v) hu.Dth hv.Dth
      have hIHz := ih α (Work.Spaces.Dz u) (Work.Spaces.Dz v) hu.Dz hv.Dz
      have hd := SlotSum_dth_le α (n + 1) hu hv
      have hz := SlotSum_dz_le α (n + 1) hu hv
      have hmono := SlotSum_mono (α := α) (u := u) (v := v) (n := n + 1) (m := n + 2) (by omega)
      have hsum : SlotSum α (n + 1) u v + SlotSum α (n + 1) (Work.Spaces.Dth u)
            (Work.Spaces.Dth v) + SlotSum α (n + 1) (Work.Spaces.Dz u)
            (Work.Spaces.Dz v) ≤ 3 * SlotSum α (n + 2) u v := by
        linarith
      have hstep : IPn α (n + 1) u v
          = IPn α n u v + IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v) := by
        rw [show IPn α (n + 1) = Work.Coercivity.HkIPStep 1 1 (IPn α n) from rfl]
        simp only [Work.Coercivity.HkIPStep, one_mul]
      rw [hstep]
      have htri : |IPn α n u v + IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
          ≤ |IPn α n u v| + |IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
            + |IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)| := by
        have h1 := abs_add_le (IPn α n u v + IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v))
          (IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v))
        have h2 := abs_add_le (IPn α n u v) (IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v))
        linarith
      have hscale : |IPn α n u v| + |IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
            + |IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
          ≤ (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) u v
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) (Work.Spaces.Dth u)
              (Work.Spaces.Dth v)
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) (Work.Spaces.Dz u)
              (Work.Spaces.Dz v) := by
        linarith
      have hfac : (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) u v
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) (Work.Spaces.Dth u)
              (Work.Spaces.Dth v)
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) (Work.Spaces.Dz u)
              (Work.Spaces.Dz v)
          = (3 : ℝ) ^ n * (10 : ℝ) ^ 22
            * (SlotSum α (n + 1) u v
              + SlotSum α (n + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
              + SlotSum α (n + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v)) := by
        ring
      have hnonneg : (0 : ℝ) ≤ (3 : ℝ) ^ n * (10 : ℝ) ^ 22 := by positivity
      have hfinal : (3 : ℝ) ^ n * (10 : ℝ) ^ 22
            * (SlotSum α (n + 1) u v
              + SlotSum α (n + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
              + SlotSum α (n + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v))
          ≤ (3 : ℝ) ^ (n + 1) * (10 : ℝ) ^ 22 * SlotSum α (n + 2) u v := by
        have h3 : (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * (3 * SlotSum α (n + 2) u v)
            = (3 : ℝ) ^ (n + 1) * (10 : ℝ) ^ 22 * SlotSum α (n + 2) u v := by
          rw [pow_succ]; ring
        rw [← h3]
        exact mul_le_mul_of_nonneg_left hsum hnonneg
      linarith [htri, hscale, hfac, hfinal]


end Work.FTS.TransportS
end
end
