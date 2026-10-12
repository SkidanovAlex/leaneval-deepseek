import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Word.integrable_pair_prod
import Submission.Work.BoseKinLoc.Word.pair_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Word.potWord_pair_prod`

The **pair-integral factorisation** of the potential word `potWordU` of FS
`eq:Def_HB` at the pure-bare parameters (`μ = 0`, one-body kernel `g = 0`):
for a smooth compactly supported one-body profile `θ`, a configuration weight
`∏ᵢ θ(xᵢ)²` and the localised two-body kernel `wLoc ℓ v u`,

    ∫_x (∏ᵢθ(xᵢ))² · potWordU n v 0 ℓ 0 u x
      = (n(n−1)/2) · (∫θ²)^{n−2} · ∫∫ θ(x)²θ(y)² wLoc ℓ v u x y .

At `μ = 0` the one-body (chemical-potential) part of `potWordU` vanishes and the
pair sum `Σ_{i<j} wLoc ℓ v u xᵢ xⱼ` remains.  The proof is the exact
`N`-body Fubini computation:

* `potWordU_eq_zero_of_le_one` / the `n ≤ 1` branches: the index type of the
  pair sum is empty, so the word vanishes;
* `pair_integral` (from `Work.BoseKinLoc.Word.pair_peel`, which splits the `n`-fold
  product measure over two singled-out slots): for `a < b`,
  `∫_x (∏ᵢ f(xᵢ)) g(x_a)(x_b) = (∫f)^(n-2) · ∫∫ f(x)f(y)g(x)(y)`;
* `integral_finsetSum` pushes the (finite!) pair sum out of the integral
  (`Work.BoseKinLoc.Word.integrable_pair_prod` supplies the per-term
  integrability: the integrand is measurable, bounded by `|wLoc| ≤ B`, and
  supported in the compact product of the support of `θ`);
* all `n(n−1)/2` pair integrals are equal, and the cardinality of
  `{i < j}` is `n.choose 2 = n(n−1)/2`.
-/

namespace Work.BoseKinLoc.Word

open MeasureTheory

set_option autoImplicit false

/-- The number of strictly ordered pairs of `Fin n` is `n.choose 2`
(equivalently `n(n−1)/2`). -/
lemma card_pair_subtype (n : ℕ) :
    Fintype.card {ij : Fin n × Fin n | ij.1 < ij.2} = n.choose 2 := by
  rw [Fintype.card_subtype]
  have h := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n)))
  simpa using h

/-- The real-valued pair count: `#{i < j} = n(n−1)/2`. -/
lemma card_pair_subtype_real (n : ℕ) :
    (Fintype.card {ij : Fin n × Fin n | ij.1 < ij.2} : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rcases n with _ | m
  · rw [card_pair_subtype]; norm_num
  · rw [card_pair_subtype, Nat.choose_two_right]
    have hdvd : 2 ∣ (m + 1) * ((m + 1) - 1) :=
      even_iff_two_dvd.mp (Nat.even_mul_pred_self (m + 1))
    rw [Nat.cast_div hdvd (by norm_num : ((2:ℕ):ℝ) ≠ 0)]
    rw [Nat.cast_mul, Nat.cast_pred (Nat.succ_pos m)]
    push_cast
    ring

/-- At `μ = 0` and `g = 0` the potential word is the bare pair sum; for `n ≤ 1`
there are no pairs and it vanishes identically. -/
lemma potWordU_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.potWordU n v (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ℓ (0:ℝ) u x = 0 := by
  rw [Work.BoseKinLoc.potWordU]
  simp only [neg_zero, zero_mul, zero_add]
  rw [← Finset.sum_subtype (s := Finset.univ.filter (fun q : Fin n × Fin n => q.1 < q.2))
        (by intro q; simp) (fun q => Submission.BoseGases.wLoc ℓ v u (x q.1) (x q.2))]
  rw [Finset.filter_eq_empty_iff.mpr (fun q _ hq => ?_), Finset.sum_empty]
  simp only [Fin.lt_def] at hq
  have h1 := q.1.isLt
  have h2 := q.2.isLt
  omega

/-- **Pair peel**: the two-body pair integral factorises — the `n`-fold product
measure integral of a weight depending on two singled-out slots `a < b` equals
the `(n−2)`-fold product of the one-body integral times the two-body integral. -/
lemma pair_integral {k : ℕ} (a b : Fin (k+2)) (hab : a < b)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ x : Submission.BoseGases.X (k+2), (∏ i : Fin (k+2), f (x i)) * g (x a) (x b))
      = (∫ z, f z) ^ k
        * (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), f p.1 * f p.2 * g p.1 p.2) := by
  have hlast : a ≠ Fin.last (k+1) := by
    intro h
    rw [h] at hab
    exact absurd hab (not_lt.mpr (Fin.le_last b))
  set b' : Fin (k+1) := (a.castPred hlast).predAbove b with hb'def
  have hkey : a.succAbove b' = b := by
    have h := Fin.succAbove_predAbove (p := a.castPred hlast) (i := b) (by
      rw [Fin.castSucc_castPred]; exact (ne_of_lt hab).symm)
    rwa [Fin.castSucc_castPred a hlast] at h
  have h := pair_peel (volume : Measure (EuclideanSpace ℝ (Fin 3))) k a b' f g
  rw [hkey] at h
  have h2 : (∫ x : Submission.BoseGases.X (k+2), (∏ i : Fin (k+2), f (x i)) * g (x a) (x b))
      = ∫ x : Fin (k+2) → EuclideanSpace ℝ (Fin 3), g (x a) (x b) * ∏ l, f (x l)
            ∂(Measure.pi (fun _ : Fin (k+2) => (volume : Measure (EuclideanSpace ℝ (Fin 3))))) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [h2, h]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  ring

theorem potWord_pair_prod {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : ContDiff ℝ (⊤ : ENat) v)
    (hbdd : ∃ B : ℝ, ∀ x y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wLoc ℓ v u x y| ≤ B)
    {θ : EuclideanSpace ℝ (Fin 3) → ℝ} (hθ : ContDiff ℝ (⊤ : ENat) θ) (hθcs : HasCompactSupport θ) :
    (∫ x : Submission.BoseGases.X n, (∏ i : Fin n, θ (x i)) ^ 2
        * Work.BoseKinLoc.potWordU n v (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ℓ (0 : ℝ) u x)
      = ((n : ℝ) * ((n : ℝ) - 1) / 2) * (∫ z : EuclideanSpace ℝ (Fin 3), (θ z) ^ 2) ^ (n - 2)
          * (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
              (θ p.1) ^ 2 * (θ p.2) ^ 2 * Submission.BoseGases.wLoc ℓ v u p.1 p.2) := by
  rcases n with _ | _ | k
  · have hz : (fun x : Submission.BoseGases.X 0 =>
        (∏ i : Fin 0, θ (x i)) ^ 2
          * Work.BoseKinLoc.potWordU 0 v (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ℓ (0:ℝ) u x)
        = fun _ => 0 := by
      funext x
      rw [potWordU_eq_zero_of_le_one (Nat.zero_le 1) v ℓ u x, mul_zero]
    rw [hz, integral_zero]
    norm_num
  · have hz : (fun x : Submission.BoseGases.X 1 =>
        (∏ i : Fin 1, θ (x i)) ^ 2
          * Work.BoseKinLoc.potWordU 1 v (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ℓ (0:ℝ) u x)
        = fun _ => 0 := by
      funext x
      rw [potWordU_eq_zero_of_le_one (by norm_num : 1 ≤ 1) v ℓ u x, mul_zero]
    rw [hz, integral_zero]
    norm_num
  · have hpt : ∀ x : Submission.BoseGases.X (k+2),
        (∏ i : Fin (k+2), θ (x i)) ^ 2
            * Work.BoseKinLoc.potWordU (k+2) v (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ℓ (0:ℝ) u x
          = ∑ ij : {ij : Fin (k+2) × Fin (k+2) | ij.1 < ij.2},
              (∏ i : Fin (k+2), (θ (x i))^2)
                * Submission.BoseGases.wLoc ℓ v u (x ij.1.1) (x ij.1.2) := by
      intro x
      rw [Work.BoseKinLoc.potWordU]
      simp only [neg_zero, zero_mul, zero_add]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ij _
      rw [← Finset.prod_pow]
    have hcongr : (∫ x : Submission.BoseGases.X (k+2),
          (∏ i : Fin (k+2), θ (x i)) ^ 2
            * Work.BoseKinLoc.potWordU (k+2) v (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ℓ (0:ℝ) u x)
        = ∫ x : Submission.BoseGases.X (k+2),
            ∑ ij : {ij : Fin (k+2) × Fin (k+2) | ij.1 < ij.2},
              (∏ i : Fin (k+2), (θ (x i))^2)
                * Submission.BoseGases.wLoc ℓ v u (x ij.1.1) (x ij.1.2) := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpt x
    rw [hcongr,
      integral_finsetSum Finset.univ (fun ij _ =>
        integrable_pair_prod hℓ u hv hbdd hθ hθcs ij.1.1 ij.1.2),
      Finset.sum_congr rfl (fun ij _ =>
        pair_integral ij.1.1 ij.1.2 ij.2 (fun z => (θ z)^2)
          (fun a b => Submission.BoseGases.wLoc ℓ v u a b)),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_pair_subtype_real]
    rw [show (k + 2 - 2 : ℕ) = k from by omega]
    ring

end Work.BoseKinLoc.Word
