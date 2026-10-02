import Mathlib
import Submission.Work.ThomBordism.Interface

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The assembly: `ThomRational` from `TransversalityCoreFamily` and `BoundarySigma`

This file proves the target from the two geometric inputs of `Work.ThomBordism.Interface` plus the
fundamental-class lemma, and nothing else:

* `Work.ThomBordism.TransversalityCoreFamily` — the Pontryagin–Thom chapter (the injectivity half of
  Thom's theorem: the Pontryagin numbers detect rational bordism), the only place
  `Work.Drive.StableStemsTorsion` is used;
* `Work.ThomBordism.BoundarySigma` — bordism invariance of the signature (Lefschetz duality);
* `Work.ThomBordism.Smooth8Fundamental` — the local-generator condition for the `Man8` data of a
  `Work.Drive.Smooth8` with non-vanishing class.

The whole argument is then arithmetic over explicit finite sums plus `BoundarySigma` applied to the
*family* `N × (Σ i, |w i| copies of the i-th manifold)`.  In particular:

* no additivity of `σ` over a disjoint union is used (so no finite-dimensionality of any cohomology
  is needed);
* no bordism invariance of the Pontryagin *numbers* is used — that statement, for a boundary whose
  identification is only a homeomorphism, would need Novikov's topological invariance of rational
  Pontryagin classes.  Here the Pontryagin numbers enter only through the *hypotheses* of
  `TransversalityCoreFamily`, which are computed on the manifolds themselves.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

namespace Work.ThomBordism

noncomputable section

/-! ## The empty `Man8`, and a `Smooth8` as a `Man8` -/

instance instTopologicalSpacePEmpty : TopologicalSpace PEmpty :=
  ⟨fun _ => True, trivial, fun _ _ _ _ => trivial, fun _ _ => trivial⟩

instance instCompactSpacePEmpty : CompactSpace PEmpty :=
  ⟨Set.finite_univ.isCompact⟩

instance instT2SpacePEmpty : T2Space PEmpty := inferInstance

instance instChartedSpacePEmpty : ChartedSpace (EuclideanSpace ℝ (Fin 8)) PEmpty where
  atlas := ∅
  chartAt := fun x => isEmptyElim x
  mem_chart_source := fun x => isEmptyElim x
  chart_mem_atlas := fun x => isEmptyElim x

instance instIsManifoldPEmpty : IsManifold (𝓡 8) ∞ PEmpty where
  compatible := fun {e} _ he _ => by
    rw [show (atlas (EuclideanSpace ℝ (Fin 8)) PEmpty) = (∅ : Set _) from rfl] at he
    rw [Set.mem_empty_iff_false] at he
    exact False.elim he

/-- **The empty closed oriented `8`-manifold**: the `Man8` with `pt := PEmpty`, used to dispose of
the degenerate `Work.Drive.Smooth8`s (those whose class vanishes: a closed *non-orientable*
`8`-manifold has `H₈ = 0`).  All three of its numbers vanish. -/
def Man8.empty : Man8 where
  pt := PEmpty
  c := 0
  c_fund := fun x => isEmptyElim x

@[simp] theorem Man8.empty_sigma : Man8.empty.sigma = 0 :=
  sigma_zero_fundamental _

@[simp] theorem Man8.empty_p1Sq : Man8.empty.p1Sq = 0 :=
  p₁SqNumber_zero_fundamental _ _

@[simp] theorem Man8.empty_p2Num : Man8.empty.p2Num = 0 :=
  p₂Number_zero_fundamental _ _

/-- **A `Work.Drive.Smooth8` as a `Man8`**: the manifold itself when its class does not vanish
(`Smooth8Fundamental` supplies the local-generator condition), and the empty manifold when it does
(in which case all three numbers vanish, so nothing is lost). -/
def smooth8ToMan8 (hfund : Smooth8Fundamental) (M : Work.Drive.Smooth8) : Man8 := by
  classical
  exact if h : M.c = 0 then Man8.empty else Man8.ofSmooth8 M (hfund M h)

theorem smooth8ToMan8_sigma (hfund : Smooth8Fundamental) (M : Work.Drive.Smooth8) :
    (smooth8ToMan8 hfund M).sigma = M.sigma := by
  unfold smooth8ToMan8
  split_ifs with h
  · rw [Man8.empty_sigma, Smooth8_sigma_eq_zero_of_c_eq_zero M h]
  · rfl

theorem smooth8ToMan8_p1Sq (hfund : Smooth8Fundamental) (M : Work.Drive.Smooth8) :
    (smooth8ToMan8 hfund M).p1Sq = M.p1Sq := by
  unfold smooth8ToMan8
  split_ifs with h
  · rw [Man8.empty_p1Sq, Smooth8_p1Sq_eq_zero_of_c_eq_zero M h]
  · rfl

theorem smooth8ToMan8_p2Num (hfund : Smooth8Fundamental) (M : Work.Drive.Smooth8) :
    (smooth8ToMan8 hfund M).p2Num = M.p2Num := by
  unfold smooth8ToMan8
  split_ifs with h
  · rw [Man8.empty_p2Num, Smooth8_p2Num_eq_zero_of_c_eq_zero M h]
  · rfl

/-! ## Arithmetic over signed copies -/

/-- The sum of a `neg`-antisymmetric integer function over `|w|` signed copies of `V`. -/
theorem sum_signedCopies (f : Man8 → ℤ) (hneg : ∀ W : Man8, f W.neg = -f W) (V : Man8) (w : ℤ) :
    (∑ _ : Fin w.natAbs, f (if 0 < w then V else V.neg)) = w * f V := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hw : 0 < w
  · rw [if_pos hw, Int.natAbs_of_nonneg hw.le]
  · rw [if_neg hw, hneg V, ← Int.natAbs_neg,
      Int.natAbs_of_nonneg (neg_nonneg_of_nonpos (not_lt.mp hw))]
    ring

/-- The sum of a `neg`-antisymmetric integer function over the family "`|w i|` signed copies of
`V i`" is `∑ i, w i * f (V i)`. -/
theorem sum_signedFamily (f : Man8 → ℤ) (hneg : ∀ W : Man8, f W.neg = -f W)
    (n : ℕ) (V : Fin n → Man8) (w : Fin n → ℤ) :
    (∑ j : (Σ i : Fin n, Fin (w i).natAbs), f (if 0 < w j.1 then V j.1 else (V j.1).neg))
      = ∑ i, w i * f (V i) := by
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun i _ => sum_signedCopies f hneg (V i) (w i)

/-- The sum over `N` copies of a family: `∑ k : Fin N × J, g k.2 = N * ∑ j, g j`. -/
theorem sum_prod_family (N : ℕ) (J : Type) [Fintype J] (g : J → ℤ) :
    (∑ k : Fin N × J, g k.2) = (N : ℤ) * ∑ j, g j := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## The assembly -/

/-- **Thom's theorem, rational form, from the two geometric inputs.**

Given the family form of the transversality core and bordism invariance of the signature (and the
local-generator lemma for the `Man8` data of a `Smooth8`), the target follows.  The proof is
arithmetic over the explicit finite sums below plus `BoundarySigma` applied to the family
`Fin N × (Σ i, |w i| copies of the i-th manifold)`. -/
theorem thomRational_of_transversalityCore (hT : TransversalityCoreFamily) (hσ : BoundarySigma)
    (hfund : Smooth8Fundamental) : Work.Drive.ThomRational := by
  intro n M w h1 h2
  -- the pieces, as `Man8`s (the empty manifold for the degenerate indices)
  let V : Fin n → Man8 := fun i => smooth8ToMan8 hfund (M i)
  -- the family of signed copies
  let F : (Σ i : Fin n, Fin (w i).natAbs) → Man8 :=
    fun j => if 0 < w j.1 then V j.1 else (V j.1).neg
  have hp1 : (∑ j, (F j).p1Sq) = 0 := by
    rw [show (∑ j, (F j).p1Sq)
        = ∑ i, w i * (V i).p1Sq from
      sum_signedFamily (fun W => W.p1Sq) (fun W => W.neg_p1Sq) n V w]
    rw [show (∑ i, w i * (V i).p1Sq) = ∑ i, w i * (M i).p1Sq from
      Finset.sum_congr rfl fun i _ => by rw [smooth8ToMan8_p1Sq]]
    exact h1
  have hp2 : (∑ j, (F j).p2Num) = 0 := by
    rw [show (∑ j, (F j).p2Num)
        = ∑ i, w i * (V i).p2Num from
      sum_signedFamily (fun W => W.p2Num) (fun W => W.neg_p2Num) n V w]
    rw [show (∑ i, w i * (V i).p2Num) = ∑ i, w i * (M i).p2Num from
      Finset.sum_congr rfl fun i _ => by rw [smooth8ToMan8_p2Num]]
    exact h2
  obtain ⟨N, hN, ⟨W⟩⟩ := hT (Σ i : Fin n, Fin (w i).natAbs) F hp1 hp2
  have h0 := hσ (Fin N × (Σ i : Fin n, Fin (w i).natAbs)) (fun k => F k.2) W
  have h0' : (N : ℤ) * (∑ j, (F j).sigma) = 0 := by
    rw [← sum_prod_family N (Σ i : Fin n, Fin (w i).natAbs) (fun j => (F j).sigma)]
    exact h0
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hfam : (∑ j, (F j).sigma) = 0 := (mul_eq_zero.mp h0').resolve_left hN'
  rw [show (∑ j, (F j).sigma)
      = ∑ i, w i * (V i).sigma from
    sum_signedFamily (fun W => W.sigma) (fun W => W.neg_sigma) n V w] at hfam
  rw [show (∑ i, w i * (V i).sigma) = ∑ i, w i * (M i).sigma from
    Finset.sum_congr rfl fun i _ => by rw [smooth8ToMan8_sigma]] at hfam
  exact hfam

end

end Work.ThomBordism
