import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Minimiser — the minimiser set of the Dirichlet form is closed under `+` and `-`

The Dirichlet form `dirForm W p = gSq p + potSq W p` and the `L²`-norm-squared
`l2Sq p = ‖p.1‖²` are quadratic forms on the ambient space `Amb N`, so they
satisfy the parallelogram law.  Consequently, if `lam` is a lower bound for the
quadratic form `u ↦ dirForm W u - lam * l2Sq u` on the Dirichlet space
`Hsub N L`, then the set of points of `Hsub N L` at which the bound is attained
is closed under `+` and `-` (in fact it is the linear subspace on which that
nonnegative form vanishes).

The main theorem `minimiser_set_linear` is the resulting linearity statement:
the sum and the difference of two "minimisers" (points at which the lower bound
`lam * l2Sq` is attained) are again minimisers.

The proof is the usual parallelogram argument:
`f (p+q) + f (p-q) = 2 f p + 2 f q` for `f u = dirForm W u - lam * l2Sq u`,
while `f ≥ 0` on `Hsub N L` and `f p = f q = 0` force `f (p±q) = 0`.

The parallelogram law for `dirForm W` is assembled from the three
parallelogram laws for `gSq`, `potSq W` and `l2Sq`:

* `gSq` and `l2Sq` are sums of squared norms in `L²(Conf N)`, so their
  parallelogram laws are the inner-product-space parallelogram law
  (`parallelogram_law_with_norm`);
* `potSq W p = ∫ W · (p.1)²` with `W` bounded and a.e. measurable: writing
  `Wop` for `W` as an element of `Lp ℝ ⊤`, the identity
  `∫ W · a² = ⟪Wop • a, a⟫` (valid on representatives by `Lp.coeFn_lpSMul`)
  turns the parallelogram law for `potSq W` into the bilinearity of the inner
  product on `L²(Conf N)`.
-/

namespace Work.BoseSym.Minimiser

open MeasureTheory Filter
open scoped Topology Real ContDiff ENNReal

noncomputable section

set_option autoImplicit false

/-- The parallelogram law for the weighted quadratic form `potSq W`:
for a bounded a.e. measurable weight `W` and `p q : Amb N`,
`potSq W (p+q) + potSq W (p-q) = 2 * potSq W p + 2 * potSq W q`. -/
lemma potSq_parallelogram {N : ℕ} {W : Conf N → ℝ} {C : ℝ} (hW : BddBy N W C)
    (hWm : AEMeas N W) (p q : Amb N) :
    potSq W (p + q) + potSq W (p - q) = 2 * potSq W p + 2 * potSq W q := by
  -- `W` is a bounded a.e. measurable function, hence an element of `L^∞`
  have hWmem : MemLp W (⊤ : ℝ≥0∞) (volC N) :=
    memLp_top_of_bound hWm.aestronglyMeasurable C (Filter.Eventually.of_forall hW)
  let Wop : Lp ℝ (⊤ : ℝ≥0∞) (volC N) := hWmem.toLp W
  have hWop_ae : (Wop : Conf N → ℝ) =ᵐ[volC N] W := MemLp.coeFn_toLp hWmem
  -- the identity `∫ W · a² = ⟪Wop • a, a⟫`
  have hIdent : ∀ a : L2 N,
      (∫ x, W x * ((a : Conf N → ℝ) x) ^ 2) = inner ℝ (Wop • a : L2 N) a := by
    intro a
    rw [MeasureTheory.L2.inner_def]
    simp only [Real.inner_apply]
    refine integral_congr_ae ?_
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Wop a, hWop_ae]
      with x hx hWx
    simp only [hx, Pi.smul_apply', smul_eq_mul, hWx]
    ring
  have hpq : (p + q : Amb N).1 = p.1 + q.1 := rfl
  have hpq' : (p - q : Amb N).1 = p.1 - q.1 := rfl
  simp only [potSq, hpq, hpq']
  rw [hIdent (p.1 + q.1), hIdent (p.1 - q.1), hIdent p.1, hIdent q.1]
  rw [MeasureTheory.Lp.add_smul]
  have hsubsmul : (Wop • (p.1 - q.1) : L2 N) = Wop • p.1 - Wop • q.1 := by
    rw [eq_sub_iff_add_eq, ← MeasureTheory.Lp.add_smul, sub_add_cancel]
  rw [hsubsmul]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring

/-- The parallelogram law for the squared gradient norm `gSq`. -/
lemma gSq_parallelogram {N : ℕ} (p q : Amb N) :
    gSq (p + q) + gSq (p - q) = 2 * gSq p + 2 * gSq q := by
  have hterm : ∀ j : GIdx N, ‖(p + q).2 j‖ ^ 2 + ‖(p - q).2 j‖ ^ 2
      = 2 * ‖p.2 j‖ ^ 2 + 2 * ‖q.2 j‖ ^ 2 := by
    intro j
    have h := parallelogram_law_with_norm ℝ (p.2 j) (q.2 j)
    rw [show (p + q : Amb N).2 j = p.2 j + q.2 j from rfl,
      show (p - q : Amb N).2 j = p.2 j - q.2 j from rfl, h]
    ring
  simp only [gSq]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The parallelogram law for the squared `L²` norm `l2Sq`. -/
lemma l2Sq_parallelogram {N : ℕ} (p q : Amb N) :
    l2Sq (p + q) + l2Sq (p - q) = 2 * l2Sq p + 2 * l2Sq q := by
  simp only [l2Sq]
  rw [show (p + q : Amb N).1 = p.1 + q.1 from rfl,
    show (p - q : Amb N).1 = p.1 - q.1 from rfl,
    parallelogram_law_with_norm ℝ p.1 q.1]
  ring

/-- The parallelogram law for the Dirichlet form `dirForm W`, for a bounded
a.e. measurable weight `W`. -/
lemma dirForm_parallelogram {N : ℕ} {W : Conf N → ℝ} {C : ℝ} (hW : BddBy N W C)
    (hWm : AEMeas N W) (p q : Amb N) :
    dirForm W (p + q) + dirForm W (p - q) = 2 * dirForm W p + 2 * dirForm W q := by
  have hg := gSq_parallelogram p q
  have hp := potSq_parallelogram hW hWm p q
  simp only [dirForm]
  linarith

/-- **The minimiser set of the Dirichlet form is closed under `+` and `-`.**
If `lam` is a lower bound for `dirForm W - lam * l2Sq` on the Dirichlet space
`Hsub N L`, then the sum and the difference of two points of `Hsub N L` at
which the bound is attained are again such points. -/
theorem minimiser_set_linear {N : ℕ} (L : ℝ) {W : Conf N → ℝ} {C : ℝ} (hW : BddBy N W C)
    (hWm : AEMeas N W) {lam : ℝ}
    (hmin : ∀ p : Hsub N L, lam * l2Sq (p : Amb N) ≤ dirForm W (p : Amb N)) :
    ∀ p q : Hsub N L, dirForm W (p : Amb N) = lam * l2Sq (p : Amb N) →
      dirForm W (q : Amb N) = lam * l2Sq (q : Amb N) →
      dirForm W ((p + q : Hsub N L) : Amb N) = lam * l2Sq ((p + q : Hsub N L) : Amb N) ∧
      dirForm W ((p - q : Hsub N L) : Amb N) = lam * l2Sq ((p - q : Hsub N L) : Amb N) := by
  intro p q hp hq
  -- the coercions of the submodule operations are the ambient operations
  have hadd : ((p + q : Hsub N L) : Amb N) = (p : Amb N) + (q : Amb N) := rfl
  have hsub : ((p - q : Hsub N L) : Amb N) = (p : Amb N) - (q : Amb N) := rfl
  rw [hadd, hsub]
  -- parallelogram laws on `Amb N`
  have hpar := dirForm_parallelogram hW hWm (p : Amb N) (q : Amb N)
  have hparl := l2Sq_parallelogram (p : Amb N) (q : Amb N)
  -- nonnegativity of `dirForm W - lam * l2Sq` at `p ± q`
  have hplus : 0 ≤ dirForm W ((p : Amb N) + (q : Amb N))
      - lam * l2Sq ((p : Amb N) + (q : Amb N)) := by
    have h := hmin (p + q)
    rw [hadd] at h
    linarith
  have hminus : 0 ≤ dirForm W ((p : Amb N) - (q : Amb N))
      - lam * l2Sq ((p : Amb N) - (q : Amb N)) := by
    have h := hmin (p - q)
    rw [hsub] at h
    linarith
  -- `lam` times the parallelogram law for `l2Sq`
  have hparl' : lam * l2Sq ((p : Amb N) + (q : Amb N))
      + lam * l2Sq ((p : Amb N) - (q : Amb N))
      = 2 * (lam * l2Sq (p : Amb N)) + 2 * (lam * l2Sq (q : Amb N)) := by
    linear_combination lam * hparl
  -- `f (p+q) + f (p-q) = 2 f p + 2 f q = 0`
  have hz : (dirForm W ((p : Amb N) + (q : Amb N)) - lam * l2Sq ((p : Amb N) + (q : Amb N)))
      + (dirForm W ((p : Amb N) - (q : Amb N))
        - lam * l2Sq ((p : Amb N) - (q : Amb N))) = 0 := by
    linear_combination hpar - hparl' + 2 * hp + 2 * hq
  have hX : dirForm W ((p : Amb N) + (q : Amb N))
      - lam * l2Sq ((p : Amb N) + (q : Amb N)) = 0 := by
    linarith
  have hY : dirForm W ((p : Amb N) - (q : Amb N))
      - lam * l2Sq ((p : Amb N) - (q : Amb N)) = 0 := by
    linarith
  constructor <;> linarith

end

end Work.BoseSym.Minimiser
