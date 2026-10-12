import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseB6Est.Zero.integrableBetaDiv
import Submission.Work.BoseB6Est.Zero.integrableCleanBracket
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.integrable_fsI1Integrand`

FS's `I₁` integrand (`Work.BoseB6Est.fsI1Integrand`) is

  `fsI1Integrand K εT c₁ c₂ t = cleanBracket K εT c₁ c₂ t − β(‖t‖)²/(2‖t‖²)`,

the difference of the zero-point bracket `cleanBracket = (τ̃+β) − √((τ̃+β)²−β²)`
and the mass integrand `β(‖t‖)²/(2‖t‖²)`.  Both summands are Lebesgue
integrable on `ℝ³` *as soon as* `0 ≤ ε_T ≤ 1`:

* `cleanBracket` is nonnegative (`phifun_nonneg`), bounded by
  `β ≤ K.B` (`phifun_le_beta` + `FsKernel.bound`) and vanishes for
  `‖t‖ > K.T` (`phifun_eq_zero_of_T_lt`, the kernel's momentum cut-off);
  the ball `{‖t‖ ≤ K.T}` has finite volume.  This is the content of
  `integrableCleanBracket` at the *weak* hypotheses `0 ≤ εT ≤ 1` (the sibling
  module proves the same statement inside the `FsI1Regime` bundle, which is
  more than integrability needs, so the bound is re-derived here);
* `β(‖t‖)²/(2‖t‖²)` is the mass integrand, integrable by
  `Work.BoseB6Est.Zero.integrableBetaDiv` (in three dimensions the Jacobian
  `4πr²` cancels the `r⁻²` singularity at the origin, so no small-ball estimate
  is needed).

The statement is made over `EuclideanSpace ℝ (Fin 3) = WithLp 2 (Fin 3 → ℝ)`;
the transfer from `Fin 3 → ℝ` is the measure-preserving (and injective)
projection `WithLp.ofLp` (`PiLp.volume_preserving_ofLp`,
`MeasurableEquiv.toLp 2 (Fin 3 → ℝ)`) through
`MeasureTheory.MeasurePreserving.integrable_comp_emb`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBogFS

local notation "ℝ³" => Fin 3 → ℝ
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The zero-point bracket is integrable from `0 ≤ ε_T ≤ 1` alone.**
Same argument as `Work.BoseB6Est.Zero.integrableCleanBracket`, but with the
`FsI1Regime` bundle replaced by the two hypotheses actually used
(`fsTau ≥ 0` and the kernel cut-off): the bracket is nonnegative, bounded by
`K.B`, and supported in the finite-measure set `{‖t‖ ≤ K.T}`. -/
lemma integrable_cleanBracket_weak (K : Work.BoseB6Est.FsKernel) {eT c1 c2 : ℝ}
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) :
    MeasureTheory.Integrable (fun t : ℝ³ => Work.BoseB6Est.cleanBracket K eT c1 c2 t) := by
  -- `τ̃ ≥ 0` at every radius (its `ht` hypothesis is not used).
  have hτ : ∀ r : ℝ, 0 ≤ Work.BoseB6.fsTau eT c1 c2 r := by
    intro r
    simp only [Work.BoseB6.fsTau]
    have h0 : 0 ≤ 1 - eT := by linarith
    have h1 : 0 ≤ (1 - eT) * (max (|r| - c1) 0) ^ 2 := mul_nonneg h0 (sq_nonneg _)
    have h2 : 0 ≤ eT * (max (|r| - c2) 0) ^ 2 := mul_nonneg heT0 (sq_nonneg _)
    linarith
  have hSmeas : MeasurableSet {t : ℝ³ | Work.BoseB6Est.nrm t ≤ K.T} :=
    measurableSet_le Work.BoseB6Est.Zero.measurable_eucNorm3 measurable_const
  -- the support is contained in the cut-off ball
  have hsupp : Function.support (fun t : ℝ³ => Work.BoseB6Est.cleanBracket K eT c1 c2 t)
      ⊆ {t | Work.BoseB6Est.nrm t ≤ K.T} := by
    intro t ht
    rw [Set.mem_ofPred_eq]
    by_contra hlt
    refine ht ?_
    show Work.BoseB6Est.cleanBracket K eT c1 c2 t = 0
    rw [Work.BoseB6Est.cleanBracket_eq_phifun]
    exact Work.BoseB6Est.phifun_eq_zero_of_T_lt K heT0 heT1 (not_le.mp hlt)
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  refine IntegrableOn.of_bound (Work.BoseB6Est.Zero.volume_eucNorm3_le_lt_top K.Tnn)
    (Work.BoseB6Est.Zero.cleanBracket_measurable K eT c1 c2).aestronglyMeasurable.restrict K.B ?_
  rw [MeasureTheory.ae_restrict_iff' hSmeas]
  refine Filter.Eventually.of_forall (fun t _ => ?_)
  rw [Work.BoseB6Est.cleanBracket_eq_phifun, Real.norm_eq_abs,
    abs_of_nonneg (Work.BoseB6Est.phifun_nonneg K (hτ (Work.BoseB6Est.nrm t)))]
  exact le_trans (Work.BoseB6Est.phifun_le_beta K (hτ (Work.BoseB6Est.nrm t))) (K.bound _)

theorem integrable_fsI1Integrand (K : Work.BoseB6Est.FsKernel) (eT c1 c2 : ℝ)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) :
    MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseB6Est.fsI1Integrand K eT c1 c2 t) := by
  -- both summands are integrable on `Fin 3 → ℝ`
  have hcb : MeasureTheory.Integrable
      (fun t : ℝ³ => Work.BoseB6Est.cleanBracket K eT c1 c2 t) :=
    integrable_cleanBracket_weak K heT0 heT1
  have hbd : MeasureTheory.Integrable (fun t : ℝ³ =>
      (K.β (Work.BoseB6Est.nrm t)) ^ 2 / (2 * (Work.BoseB6Est.nrm t) ^ 2)) :=
    Work.BoseB6Est.Zero.integrableBetaDiv K
  have hbase : MeasureTheory.Integrable
      (fun t : ℝ³ => Work.BoseB6Est.fsI1Integrand K eT c1 c2 t) :=
    hcb.sub hbd
  -- transfer along the measure-preserving injection `WithLp.ofLp`
  have hmp : MeasurePreserving (WithLp.ofLp : E3 → ℝ³) volume volume :=
    PiLp.volume_preserving_ofLp (Fin 3)
  have hemb : MeasurableEmbedding (WithLp.ofLp : E3 → ℝ³) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
  exact (hmp.integrable_comp_emb hemb
    (g := fun s : ℝ³ => Work.BoseB6Est.fsI1Integrand K eT c1 c2 s)).mpr hbase

end Work.BoseBogFS
