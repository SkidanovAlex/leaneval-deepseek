/-
Copyright: work module for the Elgindi finite-time singularity project.

# One more `H^k`-derivative costs at most a `k`-derivative of `f`, `D_θ f`, `D_z f`

The pointwise "coercivity" step behind the inductive construction of the inner
products `ℋ^k` of the paper:

`HkIntegrand α (k+1) f ≤ HkIntegrand α k f + HkIntegrand α k (D_θ f) + HkIntegrand α k (D_z f)`

on the closed quadrant, for `SmoothNbhd f` and `k ≥ 1`.

Write `HkIntegrand α k f z θ = P_k + M_k`, where
`P_k = ∑_{i≤k} (D_z^i f · w/√sin^{η})²` is the *pure* family and
`M_k = ∑_{1≤i, i+j≤k} (D_z^j D_θ^i f · W)²` the *mixed* family.

* Pure part: `P_{k+1} = P_k + (D_z^{k+1} f)²`; the new term is the `i = k`
  summand of the pure family of `D_z f`, since `D_z^k (D_z f) = D_z^{k+1} f`.
* Mixed part: the summands with `i + j ≤ k` are literally summands of `M_k`;
  the remaining ones have `i + j = k+1`.  Because `D_z` and `D_θ` commute on the
  closed quadrant (`Work.Spaces.mixed_comm`, valid by `SmoothNbhd f`), the
  summand with `j ≥ 1` is the `(i, j-1)`-summand of `M_k(D_z f)` while the
  `j = 0` summand (`= D_θ^{k+1} f`, so `i = k+1`) is the `(k,0)`-summand of
  `M_k(D_θ f)`; here `1 ≤ k` is essential.

The combinatorial content of the mixed part is isolated in `mixed_index_sum_le`,
an abstract statement about nonnegative double sums over the triangle
`{(a,b) : 1 ≤ a, a+b ≤ k+1}`; the relevant index reshuffling is
`Work.Coercivity.SumRowShift_eq`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Coercivity.SumShiftZ_le
import Submission.Work.Coercivity.SumRowShift_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Elementary one-dimensional sum lemmas -/

/-- The pure `D_z` family grows by one summand in the obvious way: the sum over
`range (k+2)` is dominated by the sum over `range (k+1)` of the same terms plus the
sum over `range (k+1)` of the shifted terms `te (i+1)`. -/
private lemma sum_range_succ_le_self_add_shift (te : ℕ → ℝ) (h : ∀ i, 0 ≤ te i) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 2), te i)
      ≤ (∑ i ∈ Finset.range (k + 1), te i) + ∑ i ∈ Finset.range (k + 1), te (i + 1) := by
  rw [Finset.sum_range_succ (f := te) (n := k + 1)]
  have h1 : te (k + 1) ≤ ∑ i ∈ Finset.range (k + 1), te (i + 1) :=
    Finset.single_le_sum (f := fun i => te (i + 1)) (fun i _ => h (i + 1))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  linarith

/-- The `a = 1` row of a double sum restricted by `1 ≤ a ∧ a + b ≤ k` is the plain
sum `∑_{b<k} g b`: the extra index `b = k` of `range (k+1)` is killed by the bound. -/
private lemma row_one_ite_eq (g : ℕ → ℝ) (k : ℕ) :
    (∑ b ∈ Finset.range (k + 1), (if 1 ≤ (1 : ℕ) ∧ 1 + b ≤ k then g b else 0))
      = ∑ b ∈ Finset.range k, g b := by
  rw [Finset.sum_range_succ]
  have hz : (if 1 ≤ (1 : ℕ) ∧ 1 + k ≤ k then g k else 0) = 0 := by
    rw [ite_eq_right (by omega)]
  rw [hz, add_zero]
  exact Finset.sum_congr rfl (fun b hb => by
    rw [Finset.mem_range] at hb
    rw [ite_eq_left (by omega)])

/-- Splitting one term off a sum over `range (k+1)`: the head is bounded by the sum
over `range k` (the missing index `0` is present for `1 ≤ k`). -/
private lemma row_shift_union (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) (k : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ Finset.range (k + 1), g i)
      ≤ (∑ i ∈ Finset.range k, g i) + ∑ i ∈ Finset.range k, g (i + 1) := by
  rw [Finset.sum_range_succ']
  have h0 : g 0 ≤ ∑ i ∈ Finset.range k, g i :=
    Finset.single_le_sum (fun i _ => hg i) (Finset.mem_range.mpr (by omega))
  linarith

/-- The `a = 1` row (with `b < k` and the shift by one in the second index) is
dominated by the double triangle sum. -/
private lemma row_one_shift_le_double (G : ℕ → ℕ → ℝ) (hG : ∀ a b, 0 ≤ G a b) (k : ℕ)
    (hk : 1 ≤ k) :
    (∑ b ∈ Finset.range k, G 1 (b + 1))
      ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0) := by
  have h1 : (1 : ℕ) ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hsingle := Finset.single_le_sum
    (f := fun a => ∑ j ∈ Finset.range (k + 1), (if 1 ≤ a ∧ a + j ≤ k then G a (j + 1) else 0))
    (fun a _ => Finset.sum_nonneg fun j _ => by split_ifs with h; exact hG a (j + 1); exact le_refl 0)
    h1
  have heq : (∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ (1 : ℕ) ∧ 1 + j ≤ k then G 1 (j + 1) else 0))
      = ∑ b ∈ Finset.range k, G 1 (b + 1) :=
    row_one_ite_eq (fun b => G 1 (b + 1)) k
  rw [← heq]
  exact hsingle

/-- The `a = 1` row (with `b < k`) is dominated by the double triangle sum. -/
private lemma row_one_le_double (G : ℕ → ℕ → ℝ) (hG : ∀ a b, 0 ≤ G a b) (k : ℕ) (hk : 1 ≤ k) :
    (∑ b ∈ Finset.range k, G 1 b)
      ≤ ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
          (if 1 ≤ a ∧ a + b ≤ k then G a b else 0) := by
  have h1 : (1 : ℕ) ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hsingle := Finset.single_le_sum
    (f := fun a => ∑ b ∈ Finset.range (k + 1), (if 1 ≤ a ∧ a + b ≤ k then G a b else 0))
    (fun a _ => Finset.sum_nonneg fun b _ => by split_ifs with h; exact hG a b; exact le_refl 0) h1
  have heq : (∑ b ∈ Finset.range (k + 1),
        (if 1 ≤ (1 : ℕ) ∧ 1 + b ≤ k then G 1 b else 0))
      = ∑ b ∈ Finset.range k, G 1 b :=
    row_one_ite_eq (fun b => G 1 b) k
  rw [← heq]
  exact hsingle

/-! ## The abstract mixed-index inequality -/

/-- **Combinatorial core.**  For a nonnegative double sequence `G` and `k ≥ 1`, the
triangle sum over `{(a,b) : 1 ≤ a, a+b ≤ k+1}` is dominated by the sum of the
unshifted triangle `{(a,b) : 1 ≤ a, a+b ≤ k}` and the two shifted triangles
obtained by raising one index by one (`G i (j+1)` and `G (i+1) j`).

This is exactly the index reshuffling needed to compare `M_{k+1}` with
`M_k + M_k(D_z f) + M_k(D_θ f)`: the old part `a+b ≤ k` is the unshifted triangle,
while the new part `a+b = k+1` splits according to whether `b ≥ 1` (covered by the
`G i (j+1)` sum, via `SumShiftZ_le`-style shifting) or `b = 0` (covered by the
`G (i+1) j` sum). -/
theorem mixed_index_sum_le (k : ℕ) (hk : 1 ≤ k) (G : ℕ → ℕ → ℝ) (hG : ∀ a b, 0 ≤ G a b) :
    (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
        (if 1 ≤ a ∧ a + b ≤ k + 1 then G a b else 0))
    ≤ (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
        (if 1 ≤ a ∧ a + b ≤ k then G a b else 0))
      + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0))
      + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then G (i + 1) j else 0)) := by
  -- the triangle splits exactly into the `a = 1` row plus the shifted-in-`a` triangle
  have hrow : (∑ i ∈ Finset.range (k + 1), G 1 i)
      ≤ (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
            (if 1 ≤ a ∧ a + b ≤ k then G a b else 0))
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0)) := by
    have hc := row_shift_union (fun i => G 1 i) (fun i => hG 1 i) k hk
    have ha := row_one_le_double G hG k hk
    have hb := row_one_shift_le_double G hG k hk
    linarith
  have hkey := SumRowShift_eq k G
  linarith

/-! ## The target lemma -/

/-- **Coercivity of the `H^k`-integrand.**  For `SmoothNbhd f` and `k ≥ 1`, the
`(k+1)`-st `H`-integrand is pointwise dominated by the sum of the `k`-th integrands of
`f`, `D_θ f` and `D_z f`. -/
theorem HkIntegrand_succ_le_sum (α : ℝ) (k : ℕ) (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
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
  have hDzIter : ∀ i, Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ = Work.Spaces.DzIter (i + 1) f z θ :=
    fun i => by
      show Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DzIter i f) z θ
      rw [show Work.Spaces.DzIter i (Work.Spaces.Dz f)
            = Work.Spaces.Dz (Work.Spaces.DzIter i f) from by
          simpa using (Work.Spaces.DzIter_add_right i 1 f).symm]
  have hmixDz : ∀ j i, Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ :=
    fun j i => by simpa using Work.Spaces.mixed_comm f hsm j i 1 0 z θ hz hθ
  have hmixDth : ∀ j i, Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ = Work.Spaces.mixed j (i + 1) f z θ :=
    fun j i => by simpa using Work.Spaces.mixed_comm f hsm j i 0 1 z θ hz hθ
  -- rewrite the three summands of the right-hand side into the common index form
  have hBpure : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * A) ^ 2)
      = ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (i + 1) f z θ * A) ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; rw [hDzIter i]
  have hBmixed : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ * W) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hmixDz j i]
  have hCmixed : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * W) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j (i + 1) f z θ * W) ^ 2 else 0) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hmixDth j i]
  rw [hBpure, hBmixed, hCmixed]
  -- pure part: two consecutive levels of `D_z` cover `P_{k+1}`
  have hI := sum_range_succ_le_self_add_shift
    (fun i => (Work.Spaces.DzIter i f z θ * A) ^ 2) (fun i => sq_nonneg _) k
  -- mixed part: the combinatorial triangle inequality
  have hII := mixed_index_sum_le k hk
    (fun a b => (Work.Spaces.mixed b a f z θ * W) ^ 2) (fun a b => sq_nonneg _)
  -- the pure family of `D_θ f` only helps
  have hDthnonneg : 0 ≤ ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ * A) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

end Work.Coercivity
