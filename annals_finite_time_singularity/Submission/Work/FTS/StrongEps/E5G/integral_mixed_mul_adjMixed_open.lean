import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Apriori.Limit.integral_mixed_mul_adjMixed
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.HkNorm_le_of_tendstoLocUnif_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

/-! ## The bridge between the set integral over `Q0` and the measure `Qμ`

The adjointness of `mixed j i = D_z^j D_θ^i` is available in the open-quadrant class in
`Work.FTS.OpenPkg.integral_mixed_mul_adjMixed_of_contDiffOn`, but phrased with the product
measure `Qμ = (volume ↾ Iz).prod (volume ↾ Iθ)`.  The statement below instead integrates over
the *open* quadrant `Q0` with the ambient volume.  The two agree on functions supported in
`Q0`, because `Q0 ⊆ Iz ×ˢ Iθ` and `Qμ = volume ↾ (Iz ×ˢ Iθ)`. -/

/-- For a function supported on the open quadrant, the set integral over `Work.FTS.EllipticEst.Q0`
(with the ambient volume) coincides with the integral against `Qμ`. -/
theorem setIntegral_Q0_eq_integral_Qμ {F : ℝ × ℝ → ℝ}
    (hF : ∀ p : ℝ × ℝ, p ∉ Work.FTS.EllipticEst.Q0 → F p = 0) :
    (∫ p in Work.FTS.EllipticEst.Q0, F p) = ∫ p, F p ∂Work.FTS.Apriori.Limit.Qμ := by
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    intro p hp
    rw [Work.FTS.EllipticEst.mem_Q0] at hp
    refine Set.mem_prod.mpr ⟨?_, ?_⟩
    · rw [Work.Spaces.Iz]; exact Set.mem_Ici.mpr (le_of_lt hp.1)
    · rw [Work.Spaces.Iθ]; exact Set.mem_Icc.mpr ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
  have hQμ : Work.FTS.Apriori.Limit.Qμ
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [Work.FTS.Apriori.Limit.Qμ, MeasureTheory.Measure.prod_restrict,
      ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hr : Work.FTS.Apriori.Limit.Qμ.restrict Work.FTS.EllipticEst.Q0
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          Work.FTS.EllipticEst.Q0 := by
    rw [hQμ, MeasureTheory.Measure.restrict_restrict_of_subset hsub]
  rw [← hr]
  exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hF

/-! ## The adjoints do not increase the support

Both sides of the identity are supported in the closed support of `ψ`, which lies in `Q0`;
this is what lets the two integrals be read against `Qμ`. -/

/-- The support of the iterated `z`-adjoint is contained in the closed support of the
function. -/
theorem support_adjDzIter_subset_tsupport (j : ℕ) (ψ : ℝ → ℝ → ℝ) :
    Function.support (Function.uncurry (Work.FTS.Apriori.Limit.adjDzIter j ψ))
      ⊆ tsupport (Function.uncurry ψ) := by
  induction j generalizing ψ with
  | zero => exact subset_tsupport _
  | succ j ih =>
      refine (ih (Work.FTS.Apriori.Limit.adjZ ψ)).trans ?_
      exact (closure_mono (Work.FTS.Apriori.Limit.support_adjZ_subset ψ)).trans_eq
        (IsClosed.closure_eq (isClosed_tsupport _))

/-- The support of the iterated `θ`-adjoint is contained in the closed support of the
function. -/
theorem support_adjDthIter_subset_tsupport (i : ℕ) (ψ : ℝ → ℝ → ℝ) :
    Function.support (Function.uncurry (Work.FTS.Apriori.Limit.adjDthIter i ψ))
      ⊆ tsupport (Function.uncurry ψ) := by
  induction i generalizing ψ with
  | zero => exact subset_tsupport _
  | succ i ih =>
      refine (ih (Work.FTS.Apriori.Limit.adjTh ψ)).trans ?_
      exact (closure_mono (Work.FTS.Apriori.Limit.support_adjTh_subset ψ)).trans_eq
        (IsClosed.closure_eq (isClosed_tsupport _))

/-- The closed support of the iterated `z`-adjoint is contained in the closed support of the
function. -/
theorem tsupport_adjDzIter_subset (j : ℕ) (ψ : ℝ → ℝ → ℝ) :
    tsupport (Function.uncurry (Work.FTS.Apriori.Limit.adjDzIter j ψ))
      ⊆ tsupport (Function.uncurry ψ) :=
  (closure_mono (support_adjDzIter_subset_tsupport j ψ)).trans_eq
    (IsClosed.closure_eq (isClosed_tsupport _))

/-- The closed support of `adjMixed (j,i) ψ` is contained in the closed support of `ψ`. -/
theorem support_adjMixed_subset_tsupport (j i : ℕ) (ψ : ℝ → ℝ → ℝ) :
    Function.support (Function.uncurry (Work.FTS.Apriori.Limit.adjMixed (j, i) ψ))
      ⊆ tsupport (Function.uncurry ψ) :=
  (support_adjDthIter_subset_tsupport i (Work.FTS.Apriori.Limit.adjDzIter j ψ)).trans
    (tsupport_adjDzIter_subset j ψ)

/-- The adjointness of `mixed j i = D_z^j D_θ^i` over the open quadrant, for a source that is
`C^∞` on the open quadrant and a test function of compact support inside it. -/
theorem integral_mixed_mul_adjMixed_open {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (hcs : HasCompactSupport (Function.uncurry ψ))
    (hts : tsupport (Function.uncurry ψ) ⊆ Work.FTS.EllipticEst.Q0)
    (j i : ℕ) :
    ∫ p in Work.FTS.EllipticEst.Q0, Work.Spaces.mixed j i g p.1 p.2 * ψ p.1 p.2
      = ∫ p in Work.FTS.EllipticEst.Q0, g p.1 p.2
          * Work.FTS.Apriori.Limit.adjMixed (j, i) ψ p.1 p.2 := by
  -- `ψ` is a test function of the limit chapter (`Q0` and `Qd` are the same set)
  have hg' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
      Work.FTS.Apriori.Limit.Qd := hg
  have hψ' : Work.FTS.Apriori.Limit.TestQ ψ := by
    refine ⟨?_, hcs, hts⟩
    exact contDiffOn_iff_forall_nat_le.mpr (fun n _ => (hψ n).contDiffOn)
  have key := Work.FTS.OpenPkg.integral_mixed_mul_adjMixed_of_contDiffOn hg' hψ' j i
  -- both integrands vanish off the (open) quadrant `Q0`
  have hF1 : ∀ p : ℝ × ℝ, p ∉ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i g p.1 p.2 * ψ p.1 p.2 = 0 := by
    intro p hp
    have hψ0 : ψ p.1 p.2 = 0 := by
      by_contra h
      exact hp (hts (subset_tsupport (Function.uncurry ψ) (by
        show Function.uncurry ψ p ≠ 0
        exact h)))
    rw [hψ0, mul_zero]
  have hF2 : ∀ p : ℝ × ℝ, p ∉ Work.FTS.EllipticEst.Q0 →
      g p.1 p.2 * Work.FTS.Apriori.Limit.adjMixed (j, i) ψ p.1 p.2 = 0 := by
    intro p hp
    have hadj : Work.FTS.Apriori.Limit.adjMixed (j, i) ψ p.1 p.2 = 0 := by
      by_contra h
      exact hp (hts (support_adjMixed_subset_tsupport j i ψ (by
        show Function.uncurry (Work.FTS.Apriori.Limit.adjMixed (j, i) ψ) p ≠ 0
        exact h)))
    rw [hadj, mul_zero]
  rw [setIntegral_Q0_eq_integral_Qμ hF1, setIntegral_Q0_eq_integral_Qμ hF2, key]

end Work.FTS.StrongEps.E5G
