/-
# `ℋ^k`-honesty and the `ℋ^k`-square bound for `f + g - h`

`Work.FTS.StrongPersist.L3Aux.HkMem_HkSq_add3_le`: for `f, g, h` that are `C^k` on the *open*
quadrant `Q0 = (0,∞) × (0,π/2)` and honest in `ℋ^k` (`Work.Spaces.HkMem α k ·`),

  `f + g - h ∈ ℋ^k`   and   `|f + g - h|²_{ℋ^k} ≤ 4 (|f|²_{ℋ^k} + |g|²_{ℋ^k} + |h|²_{ℋ^k})`.

## Route

The proof is the two-term subadditivity of the `ℋ^k`-square, applied twice to the split
`f + g - h = A + B` with `A = f + g` and `B = -h` (`sub_eq_add_neg` is definitional for `ℝ`, so
the splitting is a definitional identity and no rewriting of the datum is needed):

* `HkIntegrand α k (A + B) ≤ 2 HkIntegrand α k A + 2 HkIntegrand α k B` on the whole quadrant,
  from the finite-order pointwise subadditivity
  `Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain` for `C^k` data;
* `HkIntegrand α k B = HkIntegrand α k h` (`Work.FTS.EllipticEst.HkIntegrand_neg`), because the
  iterated operators `D_z^j`, `D_z^j D_θ^i` are odd;
* `HkMem α k A` from `Cores.AlphaRateEstEllT.HkMem_add_of_contDiffOn_le` (closure of `ℋ^k` under
  addition for `C^k` data), and `HkMem α k (A + B)` from
  `Cores.DiagEstEllT.HkMem_of_add_dominated_cont` — the continuity of the integrand that this
  lemma asks for is `Cores.DiagEstEllT.continuousOn_HkIntegrand_of_contDiffOn` applied to
  `A + B`, a `C^k` datum on `Q0`;
* two integrations of the pointwise bound (`MeasureTheory.integral_mono_of_nonneg` against the
  honesty certificates `HkMem.1`/`HkMem.2` of `A` and `h`) give
  `HkSq (A + B) ≤ 2 HkSq A + 2 HkSq h`, while
  `Work.FTS.EllipticEst.HkSq_add_le_of_pointwise` gives `HkSq A ≤ 2 HkSq f + 2 HkSq g`;
* the arithmetic `2(2a + 2b) + 2c ≤ 4(a + b + c)` uses only the nonnegativity of the three
  squares (`Work.Spaces.HkSq_nonneg`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkSq_add_le_of_contDiffOn_le
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.HkIntegrand_add_le_of_contDiffOn
import Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.PthIter2VftsAux
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.OpenQDefs

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
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The datum `f + g - h` of `HkMem_HkSq_add3_le`. -/
private abbrev add3E (f g h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => f z θ + g z θ - h z θ

/-- The partial sum `f + g` of `HkMem_HkSq_add3_le`. -/
private abbrev add3A (f g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => f z θ + g z θ

/-- The negated third summand `-h` of `HkMem_HkSq_add3_le`. -/
private abbrev add3B (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => - h z θ

theorem HkMem_HkSq_add3_le (α : ℝ) (k : ℕ) (hk : 1 ≤ k) {f g h : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ k (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ k (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hh : ContDiffOn ℝ k (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g)
    (hmh : Work.Spaces.HkMem α k h) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ - h z θ) ∧
    Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ - h z θ)
      ≤ 4 * (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g + Work.Spaces.HkSq α k h) := by
  -- The two summands of the split `f + g - h = A + B`, with `A = f + g` and `B = -h`.
  have hA : ContDiffOn ℝ k (Function.uncurry (add3A f g)) Work.FTS.EllipticEst.Q0 :=
    (hf.add hg).congr (fun p hp => by rfl)
  have hB : ContDiffOn ℝ k (Function.uncurry (add3B h)) Work.FTS.EllipticEst.Q0 :=
    (hh.neg).congr (fun p hp => by rfl)
  have hE : ContDiffOn ℝ k (Function.uncurry (add3E f g h)) Work.FTS.EllipticEst.Q0 :=
    (hA.add hB).congr (fun p hp => by rfl)
  -- Honesty of the first summand, and the pointwise subadditivity for both splits.
  have hmA : Work.Spaces.HkMem α k (add3A f g) :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkMem_add_of_contDiffOn_le α k hf hg hmf hmg
  have hptA : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (add3A f g) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α k hf hg
  -- The integrand is invariant under the sign flip `h ↦ -h`.
  have hneg : ∀ z θ, Work.Spaces.HkIntegrand α k (add3B h) z θ
      = Work.Spaces.HkIntegrand α k h z θ :=
    fun z θ => congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k h) z) θ
  have hptE : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (add3E f g h) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k (add3A f g) z θ
          + 2 * Work.Spaces.HkIntegrand α k h z θ := by
    intro z hz θ hθ
    have h1 := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain
      α k hA hB z hz θ hθ
    rw [hneg z θ] at h1
    exact h1
  -- The first conjunct: honesty of `f + g - h` by domination.
  have hmE : Work.Spaces.HkMem α k (add3E f g h) := by
    refine Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_cont α k
      (Work.FTS.EllipticEst.Cores.DiagEstEllT.continuousOn_HkIntegrand_of_contDiffOn hE α)
      hmA hmh ?_
    intro z hz
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hptE z hz θ hθ
  -- The second conjunct: the square, integrated twice.
  have hsqA : Work.Spaces.HkSq α k (add3A f g)
      ≤ 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g :=
    Work.FTS.EllipticEst.HkSq_add_le_of_pointwise α k hmf hmg hptA
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (add3E f g h) z θ)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (add3A f g) z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ) := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k (add3E f g h) z θ)
      (g := fun θ => 2 * Work.Spaces.HkIntegrand α k (add3A f g) z θ
        + 2 * Work.Spaces.HkIntegrand α k h z θ)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (add3E f g h) z θ)
      (((hmA.1 z hz).const_mul 2).add ((hmh.1 z hz).const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hptE z hz θ hθ)
    exact hmono.trans_eq (by
      rw [MeasureTheory.integral_add ((hmA.1 z hz).const_mul 2) ((hmh.1 z hz).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul])
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (add3E f g h) z θ)
    (g := fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (add3A f g) z θ)
      + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ))
    (Eventually.of_forall fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k (add3E f g h) z θ)
    ((hmA.2.const_mul 2).add (hmh.2.const_mul 2))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  have hsqE : Work.Spaces.HkSq α k (add3E f g h)
      ≤ 2 * Work.Spaces.HkSq α k (add3A f g) + 2 * Work.Spaces.HkSq α k h := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
    refine houter.trans_eq ?_
    rw [MeasureTheory.integral_add (hmA.2.const_mul 2) (hmh.2.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  exact ⟨hmE, le_trans hsqE (by
    nlinarith [hsqA, Work.Spaces.HkSq_nonneg α k f, Work.Spaces.HkSq_nonneg α k g,
      Work.Spaces.HkSq_nonneg α k h])⟩

end Work.FTS.StrongPersist.L3Aux
