import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Flat
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Transfer
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferAux` — elementary helpers for the derivative-priced slot transfer

Three reusable facts:

* `sqrt_add_le_aux` — `√(a+b) ≤ √a + √b` for `a, b ≥ 0` (not in Mathlib);
* `quad_lint_ne_top` — the iterated `∫⁻` over `Iz × Iθ` of `ofReal F` is finite as soon as `F` is
  integrable on the whole plane;
* `integrable_cross_of_diag` — AM–GM: `w·A·B` is integrable as soon as `w·A²` and `w·B²` are and
  `w ≥ 0` a.e.;
* `wip_self_nonneg` — the diagonal `wip` of a leaf weight is nonnegative;
* `contDiff_one_logPull_of_forall` — `logPull g` is `C¹` when `g` is smooth on the open quadrant.
-/

noncomputable section
open scoped Real Topology ENNReal ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `√(a+b) ≤ √a + √b`. -/
theorem sqrt_add_le_aux {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : (Real.sqrt (a + b)) ^ 2 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [Real.sq_sqrt (by linarith : (0:ℝ) ≤ a + b), add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  nlinarith [h1, Real.sqrt_nonneg (a + b), Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- The iterated `∫⁻` over `Iz × Iθ` of `ofReal F` is finite as soon as `F` is integrable on the
whole plane. -/
theorem quad_lint_ne_top {F : ℝ → ℝ → ℝ}
    (hF : MeasureTheory.Integrable (Function.uncurry F) MeasureTheory.volume) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ)) ≠ ⊤ := by
  refine ne_of_lt ?_
  have h_inner : ∀ z : ℝ,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ)) ≤ ∫⁻ θ, ENNReal.ofReal |F z θ| :=
    fun z => ((MeasureTheory.lintegral_mono
        (fun θ => ENNReal.ofReal_le_ofReal (le_abs_self _))).trans
      (MeasureTheory.lintegral_mono_set (Set.subset_univ Work.Spaces.Iθ))).trans
      (le_of_eq (MeasureTheory.setLIntegral_univ (fun θ => ENNReal.ofReal |F z θ|)))
  have hAEM : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal |F q.1 q.2|)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hF.aestronglyMeasurable.aemeasurable.norm
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ))
      ≤ ∫⁻ z, ∫⁻ θ, ENNReal.ofReal |F z θ| :=
        ((MeasureTheory.lintegral_mono h_inner).trans
          (MeasureTheory.lintegral_mono_set (Set.subset_univ Work.Spaces.Iz))).trans
          (le_of_eq (MeasureTheory.setLIntegral_univ
            (fun z => ∫⁻ θ, ENNReal.ofReal |F z θ|)))
    _ = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal |F q.1 q.2| :=
        (MeasureTheory.lintegral_prod (fun q : ℝ × ℝ => ENNReal.ofReal |F q.1 q.2|) hAEM).symm
    _ = ENNReal.ofReal (∫ q : ℝ × ℝ, |F q.1 q.2|) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF.abs
          (Eventually.of_forall (fun q => abs_nonneg _))).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- AM–GM for the diagonal data: `w·A·B` is integrable once `w ≥ 0` a.e., `w·A²` and `w·B²` are,
and the product is a.e. strongly measurable. -/
theorem integrable_cross_of_diag {w A B : ℝ → ℝ → ℝ} {μ : MeasureTheory.Measure (ℝ × ℝ)}
    (hw : ∀ᵐ q ∂μ, 0 ≤ w q.1 q.2)
    (hf : AEStronglyMeasurable (fun q : ℝ × ℝ => w q.1 q.2 * A q.1 q.2 * B q.1 q.2) μ)
    (hA : MeasureTheory.Integrable (fun q : ℝ × ℝ => w q.1 q.2 * (A q.1 q.2) ^ 2) μ)
    (hB : MeasureTheory.Integrable (fun q : ℝ × ℝ => w q.1 q.2 * (B q.1 q.2) ^ 2) μ) :
    MeasureTheory.Integrable (fun q : ℝ × ℝ => w q.1 q.2 * A q.1 q.2 * B q.1 q.2) μ := by
  have hmaj : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => (w q.1 q.2 * (A q.1 q.2) ^ 2 + w q.1 q.2 * (B q.1 q.2) ^ 2) / 2) μ :=
    ((hA.add hB).const_mul (1 / 2)).congr (Eventually.of_forall (fun q => by
      show (1 / 2) * (w q.1 q.2 * A q.1 q.2 ^ 2 + w q.1 q.2 * B q.1 q.2 ^ 2)
          = (w q.1 q.2 * A q.1 q.2 ^ 2 + w q.1 q.2 * B q.1 q.2 ^ 2) / 2
      ring))
  refine MeasureTheory.Integrable.mono' hmaj hf ?_
  filter_upwards [hw] with q hq
  show |w q.1 q.2 * A q.1 q.2 * B q.1 q.2|
      ≤ (w q.1 q.2 * A q.1 q.2 ^ 2 + w q.1 q.2 * B q.1 q.2 ^ 2) / 2
  rw [abs_mul, abs_mul, abs_of_nonneg hq]
  have h5 : |A q.1 q.2| * |B q.1 q.2| ≤ ((A q.1 q.2) ^ 2 + (B q.1 q.2) ^ 2) / 2 := by
    nlinarith [sq_nonneg (A q.1 q.2 - B q.1 q.2), sq_nonneg (A q.1 q.2 + B q.1 q.2),
      abs_nonneg (A q.1 q.2), abs_nonneg (B q.1 q.2), sq_abs (A q.1 q.2), sq_abs (B q.1 q.2)]
  calc w q.1 q.2 * |A q.1 q.2| * |B q.1 q.2|
      = w q.1 q.2 * (|A q.1 q.2| * |B q.1 q.2|) := by ring
    _ ≤ w q.1 q.2 * (((A q.1 q.2) ^ 2 + (B q.1 q.2) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left h5 hq
    _ = (w q.1 q.2 * (A q.1 q.2) ^ 2 + w q.1 q.2 * (B q.1 q.2) ^ 2) / 2 := by ring

/-- The diagonal `wip` of a leaf weight is nonnegative. -/
theorem wip_self_nonneg {α : ℝ} {a : ℕ} {w : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a w) (A : ℝ → ℝ → ℝ) :
    0 ≤ Work.Coercivity.wip w A A := by
  have hleafnn : ∀ z : ℝ, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ w z θ := fun z θ hθ =>
    Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z hθ
  rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.wip_eq_flat]
  refine MeasureTheory.setIntegral_nonneg isClosed_Ici.measurableSet (fun z _ => ?_)
  refine MeasureTheory.setIntegral_nonneg isClosed_Icc.measurableSet (fun θ hθ => ?_)
  have hwθ : (0 : ℝ) ≤ w z θ := hleafnn z θ hθ
  nlinarith [sq_nonneg (A z θ)]

/-- `logPull g` is `C¹` when `g` is `C^∞` on the open quadrant. -/
theorem contDiff_one_logPull_of_forall {g : Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ContDiff ℝ 1 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) := by
  have hφ : ContDiff ℝ 1 (fun s : ℝ × ℝ => (Real.exp s.1, Real.arctan (Real.exp s.2))) :=
    (Real.contDiff_exp.comp contDiff_fst).prodMk
      (Real.contDiff_arctan.comp (Real.contDiff_exp.comp contDiff_snd))
  have hmem : ∀ s : ℝ × ℝ, (Real.exp s.1, Real.arctan (Real.exp s.2))
      ∈ Work.FTS.EllipticEst.Q0 := fun s =>
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos _, Real.arctan_pos.mpr (Real.exp_pos s.2),
      Real.arctan_lt_pi_div_two _⟩
  have h := (hg 1).comp_contDiff hφ hmem
  have hfun : ((Function.uncurry g)
      ∘ (fun s : ℝ × ℝ => (Real.exp s.1, Real.arctan (Real.exp s.2))))
      = Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g := rfl
  rwa [hfun] at h

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
