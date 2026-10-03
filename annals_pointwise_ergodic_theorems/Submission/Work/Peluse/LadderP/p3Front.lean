import Mathlib
import Submission.Work.Peluse.Holds.LadderP
import Submission.Work.Peluse.Concat.boxNormPow_iteratedPeel

/-! # P3, the front end of the induction step: peel to the last pair and extract the mass

The first step of the proof of `Work.Peluse.LadderP.lemma51P_succ` (the induction step of Peluse's
Lemma 5.1, arXiv:1909.00309 ll. 1211–1220), in the frozen power-loss form of
`Submission/Work/Peluse/Holds/LadderP.lean`.

Given the level-`(t+1)` box norm of `f` at the arithmetic direction family
`i ↦ c(a + b i)[M₂]` at a *single* `a`:

* the iterated peel (`Work.LadderP.boxNormPow_lastTwo`) writes the `2^{t+1}`-th box-norm power as
  the `M₂^{-2(t-1)}`-weighted average, over the tuples of pairs of shifts from the first `t-1`
  direction sets, of the `4`-th box-norm power of the iterated difference `Δ'_{sh} f` at the **last
  pair** of direction sets;
* one Jensen step (`x ↦ x^{1/2^{t+1}}` is concave and `boxNorm ≤ 1`) converts the box norm of `f`
  into the *average of level-`2` box norms* of the composites;
* the threshold extraction (`Work.Peluse.LadderP.mass_ge_of_sum_ge`, with the trivial bound
  `boxNormPow 2 ≤ 1` for a `1`-bounded composite) turns "the average is `≫ γ^{O(1)}`" into "a
  positive proportion of the shift tuples carry `≫ γ^{O(1)}`".

Two auxiliary facts are used repeatedly downstream and are proved here:

* `iterDelta_shift_support`: the shifted composite `x ↦ Δ'_{sh}f (x - Σ (sh j).1)` is *supported in*
  `symIcc N` whenever `f` is (the unshifted composite is only supported in a translate of
  `symIcc N`); `Work.LadderP.boxNormPow_translate` then transfers the box norms.
* `card_shType` / `sum_weight_eq_one`: the index type of the peel carries total weight `1` in the
  normalisation of the peel identity.

The two-dimensional inverse theorem (`Work.LadderP.twoDimInverseReal`) is applied *per shift tuple*
in `p3Extract`; see `NOTES_P3_SESSION3.md` §4 for the `c`-uniformity constraint on its constant.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.LadderP

open Work.Peluse

noncomputable section

/-- The cardinality of the index type of the peel: a product of `m` copies of `A j × A j`. -/
lemma card_shType {m M : ℕ} (A : Fin m → Finset ℤ) (hA : ∀ j : Fin m, (A j).card = M) :
    Fintype.card ((j : Fin m) → ↥(A j) × ↥(A j)) = M ^ (2 * m) := by
  rw [Fintype.card_pi]
  have h1 : ∀ j : Fin m, Fintype.card (↥(A j) × ↥(A j)) = M ^ 2 := by
    intro j
    rw [Fintype.card_prod, Fintype.card_coe, hA j, ← pow_two]
  rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Nat.mul_comm]

/-- The weights of the peel sum to one: `(∏_j M⁻²) · #(index type) = 1`. -/
lemma prod_weight_mul_card {m M : ℕ} (A : Fin m → Finset ℤ) (hA : ∀ j : Fin m, (A j).card = M)
    (hM : 0 < M) :
    (∏ j : Fin m, ((M : ℝ))⁻¹ ^ 2)
      * (Fintype.card ((j : Fin m) → ↥(A j) × ↥(A j)) : ℝ) = 1 := by
  have hcard : (Fintype.card ((j : Fin m) → ↥(A j) × ↥(A j)) : ℝ) = ((M : ℝ) ^ 2) ^ m := by
    rw [card_shType A hA]
    push_cast
    rw [pow_mul]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcard, ← mul_pow]
  have hMne : ((M : ℝ)) ≠ 0 := by positivity
  have hinner : ((M : ℝ))⁻¹ ^ 2 * ((M : ℝ)) ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hMne, one_pow]
  rw [hinner, one_pow]

/-- Membership in the symmetric window in terms of `natAbs` (p3-local copy). -/
lemma mem_symIcc_iff_natAbs_p3 {N : ℕ} {x : ℤ} : x ∈ symIcc N ↔ x.natAbs ≤ N := by
  rw [symIcc, Finset.mem_Icc]
  constructor
  · intro h
    have h' : |x| ≤ (N : ℤ) := abs_le.mpr h
    rw [← Int.natCast_natAbs] at h'
    exact_mod_cast h'
  · intro h
    have h' : ((x.natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast h
    rw [Int.natCast_natAbs] at h'
    exact abs_le.mp h'

end

end Work.Peluse.LadderP
