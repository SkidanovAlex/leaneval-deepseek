/-
# The two elementary `ℋ^k` API facts of the Galerkin chapter

`Work.Spaces.HkSq α k` is the square of the weighted `ℋ^k`-norm of the paper,
`HkSq α k f = ∫_{z∈[0,∞)} ∫_{θ∈[0,π/2]} HkIntegrand α k f z θ`, and `HkMem α k f` is the
honest integrability certificate for that iterated integral.  This file provides the two
elementary facts about them that the Galerkin basis construction (`Submission/Work/FTS/GalBasis`)
consumes:

* **scalar homogeneity**: `HkSq α k (c·f) = c² · HkSq α k f`.  `HkIntegrand` is a sum of squares
  of expressions which are *unconditionally* linear in `f` (`deriv` is scalar homogeneous with no
  differentiability hypothesis), so the identity is pointwise, hence an integral identity; only
  `integral_const_mul` is needed to pull `c²` out of the two integrals;

* **the triangle inequality**: `HkSq α k (f-h) ≤ 2 HkSq α k (f-g) + 2 HkSq α k (g-h)`.  This is
  the `(a-b)² ≤ 2(a-c)² + 2(c-b)²` inequality summand by summand of `HkIntegrand`, integrated.
  The additivity of the iterated operators `D_z^i`, `D_z^j D_θ^i` is available on the *open*
  quadrant from `SmoothOpen` (`HkIntegrand_add_le_of_contDiffOn`), and on the two boundary lines
  of the quadrant every `HkIntegrand` vanishes, so the pointwise inequality holds on all of
  `Iz ×ˢ Iθ`.  The integrability certificates of the two *differences* `f-g`, `g-h` (needed to
  know that the dominating function is integrable) are obtained from `HkMem_add_open` together
  with the unconditional identity `HkIntegrand (-g) = HkIntegrand g`; no positivity of `α` is
  needed anywhere.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalBasis.Defs
import Submission.Work.FTS.Galerkin.Hilbert.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.EllHyp_certificates

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn galFun)

set_option linter.unusedVariables false
set_option maxHeartbeats 400000

/-! ## Pointwise helpers -/

/-- Scalar homogeneity of the `ℋ^k`-integrand, pointwise and with no regularity hypothesis. -/
theorem hkIntegrand_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : Fn) :
    ∀ z θ, Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
  fun z θ => Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α k c f z θ

/-- The `ℋ^k`-integrand of the *(Pi-)negation* of `g` is that of `g`: the operators
`D_z^i`, `D_z^j D_θ^i` commute with `-` (totally, `deriv (-f) = -deriv f` for every `f`),
so this holds for the negated function as well. -/
theorem hkIntegrand_neg_fun (α : ℝ) (k : ℕ) (g : Fn) :
    Work.Spaces.HkIntegrand α k (fun z θ => -g z θ) = Work.Spaces.HkIntegrand α k g :=
  Work.FTS.EllipticEst.HkIntegrand_neg α k g

/-- `HkMem` is closed under negation, with no regularity and no positivity hypothesis
(the integrand of `-g` is *equal* to that of `g`). -/
theorem hkMem_neg_open (α : ℝ) (k : ℕ) {g : Fn} (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => -g z θ) := by
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α k (fun z θ => -g z θ) z θ
      = Work.Spaces.HkIntegrand α k g z θ :=
    fun z θ => congrFun (congrFun (hkIntegrand_neg_fun α k g) z) θ
  constructor
  · intro z hz
    exact (hmg.1 z hz).congr_fun (fun θ _ => (hpt z θ).symm) measurableSet_Icc
  · refine hmg.2.congr_fun (fun z _ => ?_) measurableSet_Ici
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => (hpt z θ).symm)

/-- `SmoothOpen` is closed under negation. -/
theorem smoothOpen_neg {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -g z θ) := by
  have hfun : Function.uncurry (fun z θ => -g z θ) = -(Function.uncurry g) := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact hg.neg

/-- **`HkMem` is closed under subtraction** for `C^∞`-on-the-open-quadrant data, with no
positivity hypothesis on `α`: write `f - g = f + (-g)` and use `HkMem_add_open` together with
the negation case above. -/
theorem hkMem_sub_open (α : ℝ) (k : ℕ) {f g : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) := by
  have hfun : (fun z θ => f z θ - g z θ) = (fun z θ => f z θ + -g z θ) := by
    funext z θ; ring
  rw [hfun]
  exact Work.FTS.EllipticEst.HkMem_add_open hf (smoothOpen_neg hg) hmf
    (hkMem_neg_open α k hmg)

/-! ## The API lemma -/

theorem hk_sq_api :
    (∀ (α : ℝ) (k : ℕ) (f : Work.FTS.Galerkin.Fn), Work.FTS.EllipticEst.SmoothOpen f → ∀ c : ℝ,
      Work.Spaces.HkSq α k (fun z θ => c * f z θ) = c ^ 2 * Work.Spaces.HkSq α k f) ∧
    (∀ (α : ℝ) (k : ℕ) (f g h : Work.FTS.Galerkin.Fn),
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      Work.FTS.EllipticEst.SmoothOpen h →
      Work.Spaces.HkMem α k f → Work.Spaces.HkMem α k g → Work.Spaces.HkMem α k h →
      Work.Spaces.HkSq α k (fun z θ => f z θ - h z θ) ≤
        2 * Work.Spaces.HkSq α k (fun z θ => f z θ - g z θ) +
        2 * Work.Spaces.HkSq α k (fun z θ => g z θ - h z θ)) := by
  constructor
  · -- scalar homogeneity: the identity is pointwise, then `c²` comes out of both integrals
    intro α k f _hf c
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
    have hinner : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      have h1 : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
          = ∫ θ in Work.Spaces.Iθ, c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc
          (fun θ _ => hkIntegrand_const_mul α k c f z θ)
      rw [h1, MeasureTheory.integral_const_mul]
    rw [hinner, MeasureTheory.integral_const_mul]
  · -- the triangle inequality
    intro α k f g h hf hg hh hmf hmg hmh
    have hFsmooth : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) :=
      Work.FTS.EllipticEst.smoothOpen_sub hf hg
    have hGsmooth : Work.FTS.EllipticEst.SmoothOpen (fun z θ => g z θ - h z θ) :=
      Work.FTS.EllipticEst.smoothOpen_sub hg hh
    have hmF : Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) :=
      hkMem_sub_open α k hf hg hmf hmg
    have hmG : Work.Spaces.HkMem α k (fun z θ => g z θ - h z θ) :=
      hkMem_sub_open α k hg hh hmg hmh
    -- the pointwise `(a-b)² ≤ 2(a-c)² + 2(c-b)²` inequality for the integrand
    have hpt := Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn α k hFsmooth hGsmooth
    have hres := Work.FTS.EllipticEst.HkSq_add_le_of_pointwise α k hmF hmG hpt
    have hfun : (fun z θ => (f z θ - g z θ) + (g z θ - h z θ))
        = (fun z θ => f z θ - h z θ) := by
      funext z θ; ring
    simpa only [hfun] using hres

end Work.FTS.GalBasis
