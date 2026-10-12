import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Minimiser.Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSym.Minimiser.cauchySeq_of_excess_family`

A family `r : ℕ → Hsub N L` whose graph-norm differences are controlled by an
excess `δ j + κ j * ‖·‖²_{L²}` with `δ j → 0`, and whose `L²` parts converge,
is Cauchy for the ambient (sup-product) norm.

The argument is a single `ε`-estimate: by `hconv` the `L²` parts of `r` converge,
hence are Cauchy, so the `L²` excess term `l2Sq (r k - r l)` is arbitrarily small
for `k, l` large; choosing the index `j` of the excess large makes `δ j` small as
well, and `norm_sq_le_hSq` converts the resulting bound on the graph norm
`hSq (r k - r l)` back into a bound on `dist (r k) (r l)`.
-/

namespace Work.BoseSym.Minimiser

open Filter MeasureTheory

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
-- the hypothesis `hl2` is redundant for this statement: convergence of the `L²`
-- parts (`hconv`) already provides the Cauchy property of the `L²` excess.
set_option linter.unusedVariables false

variable {N : ℕ}

/-- The graph norm is nonnegative. -/
lemma cs_hSq_nonneg (p : Work.BoseSym.Amb N) : 0 ≤ Work.BoseSym.hSq p :=
  le_trans (by positivity : (0 : ℝ) ≤ ‖p‖ ^ 2) (norm_sq_le_hSq p)

/-- The ambient norm of a difference is controlled by the graph norm of that
difference. -/
lemma cs_dist_le_sqrt_hSq (p q : Work.BoseSym.Amb N) :
    dist p q ≤ Real.sqrt (Work.BoseSym.hSq (p - q)) := by
  rw [dist_eq_norm, Real.le_sqrt (norm_nonneg _) (cs_hSq_nonneg _)]
  exact norm_sq_le_hSq _

theorem cauchySeq_of_excess_family {N : ℕ} {L : ℝ} {r : ℕ → Work.BoseSym.Hsub N L} {δ κ : ℕ → ℝ}
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hl2 : ∀ n, Work.BoseSym.l2Sq (r n : Work.BoseSym.Amb N) = 1)
    (hbd : ∀ j k l, j ≤ k → j ≤ l →
      Work.BoseSym.hSq ((r k : Work.BoseSym.Amb N) - (r l : Work.BoseSym.Amb N)) ≤
        δ j + κ j * Work.BoseSym.l2Sq ((r k : Work.BoseSym.Amb N) - (r l : Work.BoseSym.Amb N)))
    (hconv : ∃ w : Work.BoseSym.L2 N,
      Work.BoseSym.TendstoL2 N (fun n => Work.BoseSym.jEmbed N L (r n)) w) :
    CauchySeq (fun n => (r n : Work.BoseSym.Amb N)) := by
  obtain ⟨w, hw⟩ := hconv
  -- `hconv` says precisely that the `L²` parts of `r` converge.
  have hw' : Filter.Tendsto (fun n => ((r n : Work.BoseSym.Amb N)).1) Filter.atTop (nhds w) := hw
  have hcau1 : CauchySeq (fun n => ((r n : Work.BoseSym.Amb N)).1) := hw'.cauchySeq
  rw [Metric.cauchySeq_iff]
  intro ε hε
  -- Step 1: choose the index `j0` of the excess so that `δ j0 < ε²/2`.
  have hε2 : 0 < ε ^ 2 / 2 := by positivity
  have hδev : ∀ᶠ j in Filter.atTop, δ j < ε ^ 2 / 2 :=
    hδ.eventually (Iio_mem_nhds hε2)
  obtain ⟨j0, hj0⟩ := Filter.eventually_atTop.1 hδev
  -- Step 2: the `L²` excess is controlled by `β * t²` with `β := |κ j0| + 1 ≥ 1`
  -- and a tolerance `t` chosen so that `β * t² ≤ ε²/4`.
  set β : ℝ := |κ j0| + 1 with hβdef
  have hβ1 : 1 ≤ β := by
    rw [hβdef]; have := abs_nonneg (κ j0); linarith
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ1
  set t : ℝ := ε / (2 * β) with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht : t * (2 * β) = ε := by rw [htdef]; field_simp
  obtain ⟨K0, hK0⟩ := (Metric.cauchySeq_iff.mp hcau1) t htpos
  refine ⟨max j0 K0, ?_⟩
  intro m hm n hn
  have hmj : j0 ≤ m := le_trans (le_max_left _ _) hm
  have hnj : j0 ≤ n := le_trans (le_max_left _ _) hn
  have hmK : K0 ≤ m := le_trans (le_max_right _ _) hm
  have hnK : K0 ≤ n := le_trans (le_max_right _ _) hn
  -- Abbreviate the difference; this keeps all subsequent statements small.
  set X : Work.BoseSym.Amb N := (r m : Work.BoseSym.Amb N) - (r n : Work.BoseSym.Amb N) with hX
  have hX1 : X.1 = ((r m : Work.BoseSym.Amb N)).1 - ((r n : Work.BoseSym.Amb N)).1 := rfl
  have hbd' : Work.BoseSym.hSq X ≤ δ j0 + κ j0 * Work.BoseSym.l2Sq X := hbd j0 m n hmj hnj
  have hdiff : ‖X.1‖ < t := by
    simpa only [dist_eq_norm, hX1] using hK0 m hmK n hnK
  have hl2lt : Work.BoseSym.l2Sq X < t ^ 2 := by
    rw [show Work.BoseSym.l2Sq X = ‖X.1‖ ^ 2 from rfl]
    nlinarith [norm_nonneg X.1, hdiff, htpos]
  have hκle : κ j0 ≤ β := by rw [hβdef]; linarith [le_abs_self (κ j0)]
  have hl2nn : 0 ≤ Work.BoseSym.l2Sq X := by
    simp only [Work.BoseSym.l2Sq]; positivity
  have hκbound : κ j0 * Work.BoseSym.l2Sq X ≤ β * t ^ 2 := by
    calc κ j0 * Work.BoseSym.l2Sq X ≤ β * Work.BoseSym.l2Sq X :=
          mul_le_mul_of_nonneg_right hκle hl2nn
      _ ≤ β * t ^ 2 := mul_le_mul_of_nonneg_left hl2lt.le hβpos.le
  have hβt : β * t ^ 2 ≤ ε ^ 2 / 4 := by
    have hsq : ε ^ 2 / 4 = β ^ 2 * t ^ 2 := by rw [← ht]; ring
    rw [hsq]
    calc β * t ^ 2 = β * t ^ 2 * 1 := by ring
      _ ≤ β * t ^ 2 * β := mul_le_mul_of_nonneg_left hβ1 (by positivity)
      _ = β ^ 2 * t ^ 2 := by ring
  have hκb' : κ j0 * Work.BoseSym.l2Sq X ≤ ε ^ 2 / 4 := le_trans hκbound hβt
  have hSqnn : 0 ≤ Work.BoseSym.hSq X := cs_hSq_nonneg X
  have hhSq : Work.BoseSym.hSq X < ε ^ 2 := by
    have h3 : δ j0 + κ j0 * Work.BoseSym.l2Sq X < ε ^ 2 / 2 + ε ^ 2 / 4 :=
      add_lt_add_of_lt_of_le (hj0 j0 le_rfl) hκb'
    calc Work.BoseSym.hSq X ≤ δ j0 + κ j0 * Work.BoseSym.l2Sq X := hbd'
      _ < ε ^ 2 / 2 + ε ^ 2 / 4 := h3
      _ < ε ^ 2 := by nlinarith [hε, sq_nonneg ε]
  calc dist ((r m : Work.BoseSym.Amb N)) ((r n : Work.BoseSym.Amb N))
      = ‖X‖ := by rw [dist_eq_norm, ← hX]
    _ ≤ Real.sqrt (Work.BoseSym.hSq X) := by
        rw [Real.le_sqrt (norm_nonneg _) hSqnn]
        exact norm_sq_le_hSq X
    _ < Real.sqrt (ε ^ 2) := Real.sqrt_lt_sqrt hSqnn hhSq
    _ = ε := Real.sqrt_sq hε.le

end

end Work.BoseSym.Minimiser
