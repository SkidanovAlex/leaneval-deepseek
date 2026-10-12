import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Minimiser

open MeasureTheory Filter
open Work.BoseSym

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The potential energy `potSq W p = ∫ W · u²` of an almost-everywhere
nonnegative potential is nonnegative (no integrability is needed: an
integrand that is not integrable has Bochner integral `0`). -/
lemma potSq_nonneg {N : ℕ} {W : Conf N → ℝ} (hW : AENonneg N W) (p : Amb N) :
    0 ≤ potSq W p := by
  simp only [potSq]
  exact integral_nonneg_of_ae (hW.mono fun x hx => mul_nonneg hx (sq_nonneg _))

/-- The Dirichlet form of an almost-everywhere nonnegative potential is
nonnegative. This is the lower bound that makes the infimum over the unit
sphere exist (in the `sInf` sense). -/
lemma dirForm_nonneg {N : ℕ} {W : Conf N → ℝ} (hW : AENonneg N W) (p : Amb N) :
    0 ≤ dirForm W p := by
  have hg : 0 ≤ gSq p := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hp : 0 ≤ potSq W p := potSq_nonneg hW p
  simp only [dirForm]
  linarith

theorem iInf_le_dirForm_unit {N : ℕ} (L : ℝ) {W : Conf N → ℝ} (hWnn : AENonneg N W)
    {z : Hsub N L} (hz : l2Sq (z : Amb N) = 1) :
    (⨅ q : {q : Hsub N L // l2Sq (q : Amb N) = 1}, dirForm W (q : Amb N))
      ≤ dirForm W (z : Amb N) := by
  -- `ciInf_le` with `f` supplied explicitly: leaving `f` implicit makes the
  -- higher-order unification against the statement's `⨅` blow up.
  exact ciInf_le (f := fun q : {q : Hsub N L // l2Sq (q : Amb N) = 1} => dirForm W (q : Amb N))
    ⟨0, by rintro _ ⟨q, rfl⟩; exact dirForm_nonneg hWnn _⟩ ⟨z, hz⟩

end

end Work.BoseSym.Minimiser
