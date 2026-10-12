import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseSym.Form.gSq_eq_integral
import Submission.Work.BoseSym.Form.l2Sq_eq_integral
import Submission.Work.BoseSym.Form.tendsto_potSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Minimiser — the bilinear forms for the minimiser argument

This file sets up the vocabulary for the existence of a minimiser of the
Dirichlet form `dirForm W` on the unit sphere of the energy space
`Hsub N L ⊆ Amb N`.

The plan of the minimiser argument (Session: `exists_minimiser`) is:

* shift the (a priori only bounded below) Dirichlet form by a positive
  multiple of the `L²`-norm-squared, so as to obtain a positive definite
  quadratic form `G` on `Hsub`;

* write `G` as the diagonal of an explicit bilinear form `formP F + K * (L²
  pairing)`, whose pieces are built out of the `L²` pairings

  `⟪F • p.1, q.1⟫`  (multiplication by an `L∞` class `F`),

  which is where the positivity of `W + C + 1` enters;

* run the classical Cauchy-sequence argument for the generalized Rayleigh
  quotient `l2Sq / G`, using `rellich` for the compactness of the embedding
  of the energy space into `L²`.

The main definitions here are `L2top`, `constLp`, `formP` and `shiftP`.
-/

namespace Work.BoseSym.Minimiser

open MeasureTheory Filter
open Work.BoseSym
open scoped Topology ENNReal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The essentially bounded classes on configuration space. -/
abbrev L2top (N : ℕ) : Type := Lp ℝ (⊤ : ℝ≥0∞) (volC N)

/-- The `L∞` class of the constant function `c` on configuration space.
(Note that `memLp_const` needs a finite measure space; the constant function is
nevertheless essentially bounded with respect to Lebesgue measure.) -/
def constLp (N : ℕ) (c : ℝ) : L2top N :=
  MemLp.toLp (fun _ : Conf N => c)
    (memLp_top_of_bound aestronglyMeasurable_const |c| (Filter.Eventually.of_forall (fun _ => by
      rw [Real.norm_eq_abs])))

/-- The bilinear form whose diagonal is the Dirichlet form: the sum of the
gradient pairing and the pairing `⟪F • p.1, q.1⟫` with the `L∞` class `F`. -/
def formP {N : ℕ} (F : L2top N) (p q : Amb N) : ℝ :=
  (∑ j : GIdx N, inner ℝ (p.2 j) (q.2 j)) + inner ℝ (F • p.1) q.1

/-- The shifted bilinear form `formP F + K * (L² pairing)`, whose diagonal is
`dirForm (F) + K * l2Sq` when `F` represents `W`. -/
def shiftP {N : ℕ} (F : L2top N) (K : ℝ) (p q : Amb N) : ℝ :=
  formP F p q + K * inner ℝ p.1 q.1

@[simp] lemma formP_self {N : ℕ} (F : L2top N) (p : Amb N) :
    formP F p p = gSq p + inner ℝ (F • p.1) p.1 := by
  simp [formP, gSq]

@[simp] lemma shiftP_self {N : ℕ} (F : L2top N) (K : ℝ) (p : Amb N) :
    shiftP F K p p = formP F p p + K * l2Sq p := by
  simp [shiftP, l2Sq]

lemma constLp_coeFn {N : ℕ} (c : ℝ) :
    (constLp N c : Conf N → ℝ) =ᵐ[volC N] fun _ => c :=
  MemLp.coeFn_toLp _

end

end Work.BoseSym.Minimiser
