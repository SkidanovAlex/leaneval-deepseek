/-
# Coercivity of the `ℋ^k`-norm in the *interior* (cut-off compatible) smoothness class

The delivered coercivity of the `H^k`-norm,
`Work.Coercivity.HkSq_succ_le_of_smooth` (and its `α`-free variant
`Work.Coercivity.HkSq_succ_le`),

  `HkSq α (k+1) f ≤ HkSq α k f + HkSq α k (D_θ f) + HkSq α k (D_z f)`  (`k ≥ 1`),

is stated for `Work.Spaces.SmoothNbhd f = ContDiffOn ℝ ⊤ …` on a neighbourhood of the closed
quadrant, which in this Mathlib is the **analytic** order `⊤ : ℕ∞ω`; a cut-off is never
analytic, so this hypothesis is useless for the localised data of the route
(`Work.FTS.LocData.locG`).  This module proves the statement in the honest class
`Work.FTS.LocData.SmoothQuad f` — genuine `C^∞` (`Work.Stability.smoothOrder`) on the open
quadrant `(-1,∞) × (0,π/2)` — which is exactly the class of the localisation chapter.

Nothing new is mathematically required: the only place where `SmoothNbhd` entered the proof of
the pointwise integrand comparison `Work.Coercivity.HkIntegrand_succ_le_sum` was the
commutation of `D_z` with `D_θ` (`Work.Spaces.mixed_comm`), used for the two index shifts

  `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`,   `D_z^j D_θ^i (D_θ f) = D_z^j D_θ^{i+1} f`.

Both are available in `SmoothQuad` as well:

* the second is definitional (`D_θ^{i+1} = D_θ^i ∘ D_θ`), `QuadPorts.mixed_Dth_shift`;
* the first is `QuadPorts.mixed_Dz_shift`: at the interior points it is Clairaut for the two
  curvilinear derivatives (`QuadPorts.DzIter_DthIter_comm_quad`), and on the boundary of the
  quadrant both sides vanish (`z = 0` kills every `D_z`, `sin 2θ = 0` kills every `D_θ`).

So the pointwise comparison `HkIntegrand_succ_le_sum_Q` below is a verbatim copy of
`Work.Coercivity.HkIntegrand_succ_le_sum` with those two inputs replaced, and the integration
step is `Work.Coercivity.HkSq_le_sum_of_integrand_le` together with the honest memberships

* `HkMem α k f` (`Work.GalerkinFix.RegQ.HkMem_mono_Q`),
* `HkMem α k (D_θ f)` (`HkIntegrand_Dth_le` + `Work.FTS.LocData.HkMem_of_majorant`),
* `HkMem α k (D_z f)` (`QuadPorts.HkMem_Dz_quad`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Coercivity.HkSq_succ_le_of_smooth
import Submission.Work.Coercivity.HkIntegrand_succ_le_sum
import Submission.Work.Coercivity.HkMem_dth
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dth
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)

/-! ## Elementary sum lemmas (local copies of the private helpers of `Work.Coercivity`) -/

/-- A sum over `i ≤ k` of `F (i+1)` is dominated by the sum over `a ≤ k+1` of `F a` when
`F ≥ 0` (the extra term being `F 0`). -/
private lemma SumSuccRange_le_Q (k : ℕ) (F : ℕ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ i ∈ Finset.range (k + 1), F (i + 1)) ≤ ∑ a ∈ Finset.range (k + 2), F a := by
  have h2 : (∑ a ∈ Finset.range (k + 2), F a)
      = (∑ i ∈ Finset.range (k + 1), F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F (k + 1)
  linarith [hF 0]

/-- The pure `D_z` family grows by one summand: the sum over `range (k+2)` is dominated by
the sum over `range (k+1)` of the same terms plus the sum over `range (k+1)` of the shifted
terms `te (i+1)`. -/
private lemma sum_range_succ_le_self_add_shift_Q (te : ℕ → ℝ) (h : ∀ i, 0 ≤ te i) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 2), te i)
      ≤ (∑ i ∈ Finset.range (k + 1), te i) + ∑ i ∈ Finset.range (k + 1), te (i + 1) := by
  rw [Finset.sum_range_succ (f := te) (n := k + 1)]
  have h1 : te (k + 1) ≤ ∑ i ∈ Finset.range (k + 1), te (i + 1) :=
    Finset.single_le_sum (f := fun i => te (i + 1)) (fun i _ => h (i + 1))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  linarith

/-! ## The pointwise integrand comparison in the interior class -/

/-- **Coercivity of the `ℋ^k`-integrand**, in the interior smoothness class `SmoothQuad`.
For `k ≥ 1` the `(k+1)`-st `H`-integrand is pointwise dominated on the closed quadrant by the
sum of the `k`-th integrands of `f`, `D_θ f` and `D_z f`.

This is `Work.Coercivity.HkIntegrand_succ_le_sum` with the two commutation inputs replaced by
their `SmoothQuad` counterparts `QuadPorts.mixed_Dz_shift` / `QuadPorts.mixed_Dth_shift`. -/
theorem HkIntegrand_succ_le_sum_Q (α : ℝ) (k : ℕ) (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hsm : SmoothQuad f) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α (k + 1) f z θ
      ≤ Work.Spaces.HkIntegrand α k f z θ
        + Work.Spaces.HkIntegrand α k (Work.Spaces.Dth f) z θ
        + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ := by
  simp only [Work.Spaces.HkIntegrand]
  -- the two fixed weights, isolated so that the sums of squares are honest
  set A : ℝ := Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) with hA
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  -- the curvilinear derivatives pick up exactly one more factor
  have hDzIter : ∀ i, Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ
      = Work.Spaces.DzIter (i + 1) f z θ :=
    fun i => by
      show Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DzIter i f) z θ
      rw [show Work.Spaces.DzIter i (Work.Spaces.Dz f)
            = Work.Spaces.Dz (Work.Spaces.DzIter i f) from by
          simpa using (Work.Spaces.DzIter_add_right i 1 f).symm]
  have hmixDz : ∀ j i, Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
      = Work.Spaces.mixed (j + 1) i f z θ :=
    fun j i => Work.FTS.CoercivityFix.QuadPorts.mixed_Dz_shift hsm j i hz hθ
  have hmixDth : ∀ j i, Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ
      = Work.Spaces.mixed j (i + 1) f z θ :=
    fun j i => by rw [Work.FTS.CoercivityFix.QuadPorts.mixed_Dth_shift j i f]
  -- rewrite the three summands of the right-hand side into the common index form
  have hBpure : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * A) ^ 2)
      = ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (i + 1) f z θ * A) ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; rw [hDzIter i]
  have hBmixed : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ * W) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hmixDz j i]
  have hCmixed : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * W) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j (i + 1) f z θ * W) ^ 2 else 0) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hmixDth j i]
  rw [hBpure, hBmixed, hCmixed]
  -- pure part: two consecutive levels of `D_z` cover `P_{k+1}`
  have hI := sum_range_succ_le_self_add_shift_Q
    (fun i => (Work.Spaces.DzIter i f z θ * A) ^ 2) (fun i => sq_nonneg _) k
  -- mixed part: the combinatorial triangle inequality
  have hII := Work.Coercivity.mixed_index_sum_le k hk
    (fun a b => (Work.Spaces.mixed b a f z θ * W) ^ 2) (fun a b => sq_nonneg _)
  -- the pure family of `D_θ f` only helps
  have hDthnonneg : 0 ≤ ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ * A) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

/-! ## The honest memberships -/

/-- **The `ℋ^k`-membership of `D_θ f`** in the interior class, by domination of its integrand
by the `(k+1)`-integrand of `f` (`Work.Coercivity.HkIntegrand_Dth_le`, which needs no
smoothness at all) and the measurability input `continuousOn_HkIntegrand_smoothQuad`.

This is the membership half of `QuadPorts.RegQ_dth`, stated without the `BdryTraces` bookkeeping
of the `RegQ` class. -/
theorem HkMem_dth_quad (α : ℝ) (hα : 0 < α) (k : ℕ) {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f)
    (h : Work.Spaces.HkMem α (k + 1) f) : Work.Spaces.HkMem α k (Work.Spaces.Dth f) :=
  Work.FTS.LocData.HkMem_of_majorant α k
    (f := Work.Spaces.Dth f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (k + 1) f z θ)
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k (Work.Spaces.Dth f)
      (Work.FTS.CoercivityFix.QuadPorts.smoothQuad_Dth hf))
    h.1 h.2
    (fun z hz θ hθ => Work.Coercivity.HkIntegrand_Dth_le α hα k f z θ hz hθ)

/-- `HkMem` descends one order inside the interior class `SmoothQuad`: this is
`Work.GalerkinFix.RegQ.HkMem_mono_Q`, renamed for use below. -/
theorem HkMem_mono_quad {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f)
    (h : Work.Spaces.HkMem α (k + 1) f) : Work.Spaces.HkMem α k f :=
  Work.GalerkinFix.RegQ.HkMem_mono_Q hf h

/-! ## The target lemma -/

theorem HkSq_succ_le_Q (α : ℝ) (hα : 0 < α) (k : ℕ) (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (h : Work.Spaces.HkMem α (k + 1) f) :
    Work.Spaces.HkSq α (k + 1) f ≤ Work.Spaces.HkSq α k f
      + Work.Spaces.HkSq α k (Work.Spaces.Dth f) + Work.Spaces.HkSq α k (Work.Spaces.Dz f) := by
  have hf : Work.Spaces.HkMem α k f := HkMem_mono_quad hsm h
  have hdth : Work.Spaces.HkMem α k (Work.Spaces.Dth f) := HkMem_dth_quad α hα k hsm h
  have hdz : Work.Spaces.HkMem α k (Work.Spaces.Dz f) :=
    Work.FTS.CoercivityFix.QuadPorts.HkMem_Dz_quad α k hsm h
  refine Work.Coercivity.HkSq_le_sum_of_integrand_le (α := α) (m := k + 1) (k := k)
    (f := f) (g₁ := f) (g₂ := Work.Spaces.Dth f) (g₃ := Work.Spaces.Dz f)
    h hf hdth hdz ?_
  intro z hz θ hθ
  exact HkIntegrand_succ_le_sum_Q α k hk hsm hz hθ

end Work.FTS.CoercivityFix.Assembly
