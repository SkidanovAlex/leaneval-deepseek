import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.q2wordAux
import Submission.Work.BoseFixB3.CS.Pieces.aP_sym_box_weighted
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.n0MassWord_eq_sqSum`

The condensate-number mass row `n0MassWord ℓ Φ = Σ_j∫_{abox} (Σᵢ aPᵢ(aQ_jΦ))·(aQ_jΦ)·χ_ℓ(x_j)²`
of `pairRowWordParts` is the *sum of squares*

    Σ_j Σ_i ∫_{abox N ℓ} (aP ℓ i (aQ ℓ j Φ) x)²·(χ_ℓ(x_j))² .

**Mathematics.**  The two sides are term-by-term equal in `(i,j)`:

* `i = j`: `PⱼQⱼ = 0` (`Work.BoseFixB2.Sector.aP_aQ_self_eq_zero`), both terms vanish;
* `i ≠ j`: the weight `W(x) = χ_ℓ(x_j)²` is constant in slot `i`, so the *weighted*
  self-adjointness of the fibre mean over the box
  (`Work.BoseFixB3.CS.Pieces.aP_sym_box_weighted`) applied to the pair `(f, Pᵢf)` with
  `f = aQ ℓ j Φ` gives

      ∫ (Pᵢf)·(Pᵢf)·W = ∫ f·(Pᵢ(Pᵢf))·W = ∫ f·(Pᵢf)·W      (`Pᵢ(Pᵢf) = Pᵢf`),

  i.e. `∫ (Pᵢf)²W = ∫ (Pᵢf)·f·W`.

The finite sum is moved out of the integral with `MeasureTheory.integral_finsetSum` (every
summand is continuous, hence integrable on the compact box).
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The weight `(χ_ℓ(x_j))²` does not depend on the slot-`i` coordinate, for `i ≠ j`. -/
lemma chiScale_sq_update_eq {N : ℕ} {ℓ : ℝ} {i j : Fin N} (hij : i ≠ j)
    (x : Submission.BoseGases.X N) (z : E3) :
    (Submission.BoseGases.chiScale ℓ ((Function.update x i z) j)) ^ 2
      = (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 := by
  have hji : ¬(j = i) := fun h => hij h.symm
  rw [Function.update_apply, if_neg hji]

/-- **The per-slot mass-row identity.**  For every pair of slots `i j` and every continuous state
`Φ`,

    ∫_{abox N ℓ} (PᵢQⱼΦ)·(QⱼΦ)·χ_ℓ(x_j)²  =  ∫_{abox N ℓ} (PᵢQⱼΦ)²·χ_ℓ(x_j)² .

(`Qⱼ := aQ ℓ j`, `Pᵢ := aP ℓ i`.)  For `i = j` both sides vanish (`PⱼQⱼ = 0`); for `i ≠ j` this is
the weighted self-adjointness of `Pᵢ` against the slot-`i`-constant weight `χ_ℓ(x_j)²`, together
with the idempotency `PᵢPᵢ = Pᵢ`. -/
lemma aP_aQ_term_eq {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x
          * Submission.BoseGases.aQ ℓ j Φ x * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x) ^ 2
            * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 := by
  by_cases hij : i = j
  · -- `i = j`: the slot mean annihilates its own complement, both integrals vanish
    rw [hij]
    have hz : Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ j Φ) = 0 :=
      Work.BoseFixB2.Sector.aP_aQ_self_eq_zero hℓ j hΦc
    have hx : ∀ x : Submission.BoseGases.X N,
        Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ j Φ) x = 0 :=
      fun x => congrFun hz x
    rw [show (∫ x in Submission.BoseGases.abox N ℓ,
        Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ j Φ) x
          * Submission.BoseGases.aQ ℓ j Φ x * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2) = 0
        from by simp [hx],
      show (∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ j Φ) x) ^ 2
          * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2) = 0
        from by simp [hx]]
  · -- `i ≠ j`: weighted self-adjointness of `Pᵢ` against the slot-`i`-constant weight
    let f : Submission.BoseGases.X N → ℝ := Submission.BoseGases.aQ ℓ j Φ
    let W : Submission.BoseGases.X N → ℝ :=
      fun x => (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
    have hfc : Continuous f := hΦc.sub (Submission.BoseGases.aP_continuous hℓ j hΦc)
    have hWc : Continuous W :=
      ((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply j)).pow 2
    have hPfc : Continuous (Submission.BoseGases.aP ℓ i f) :=
      Submission.BoseGases.aP_continuous hℓ i hfc
    have hW : ∀ (x : Submission.BoseGases.X N) (z : E3),
        W (Function.update x i z) = W x := by
      intro x z
      exact chiScale_sq_update_eq hij x z
    change (∫ x in Submission.BoseGases.abox N ℓ,
        Submission.BoseGases.aP ℓ i f x * f x * W x)
      = ∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ i f x) ^ 2 * W x
    have hsym := Work.BoseFixB3.CS.Pieces.aP_sym_box_weighted (N := N) (ℓ := ℓ) hℓ i
      (W := W) hW hWc hfc hPfc
    have h1 : (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ i f x) ^ 2 * W x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            Submission.BoseGases.aP ℓ i f x * Submission.BoseGases.aP ℓ i f x * W x := by
      refine integral_congr_ae ?_
      filter_upwards with x
      ring
    have h2 : (∫ x in Submission.BoseGases.abox N ℓ,
            Submission.BoseGases.aP ℓ i f x * Submission.BoseGases.aP ℓ i f x * W x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            f x * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ i f) x * W x :=
      hsym
    have h3 : (∫ x in Submission.BoseGases.abox N ℓ,
            f x * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ i f) x * W x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            f x * Submission.BoseGases.aP ℓ i f x * W x := by
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [Submission.BoseGases.aP_idem hℓ i hfc x]
    have h4 : (∫ x in Submission.BoseGases.abox N ℓ,
            f x * Submission.BoseGases.aP ℓ i f x * W x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            Submission.BoseGases.aP ℓ i f x * f x * W x := by
      refine integral_congr_ae ?_
      filter_upwards with x
      ring
    exact (h1.trans (h2.trans (h3.trans h4))).symm

/-- **The per-`j` mass row.**  Distributing the finite sum `Σᵢ Pᵢ` out of the box integral and
applying `aP_aQ_term_eq` term by term,

    ∫_{abox} (Σᵢ Pᵢ(QⱼΦ))·(QⱼΦ)·χ_ℓ(x_j)²  =  Σᵢ ∫_{abox} (Pᵢ(QⱼΦ))²·χ_ℓ(x_j)² . -/
lemma massRow_eq_sqSum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (∑ i : Fin N, Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x)
          * Submission.BoseGases.aQ ℓ j Φ x * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2)
      = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x) ^ 2
            * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 := by
  have hfc : Continuous (Submission.BoseGases.aQ ℓ j Φ) :=
    hΦc.sub (Submission.BoseGases.aP_continuous hℓ j hΦc)
  have hwc : Continuous (fun x : Submission.BoseGases.X N =>
      (Submission.BoseGases.chiScale ℓ (x j)) ^ 2) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply j)).pow 2
  have hsumfun : (fun x : Submission.BoseGases.X N =>
      (∑ i : Fin N, Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x)
        * Submission.BoseGases.aQ ℓ j Φ x * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2)
      = fun x : Submission.BoseGases.X N => ∑ i : Fin N,
          Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x
            * Submission.BoseGases.aQ ℓ j Φ x
            * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 := by
    funext x
    rw [Finset.sum_mul, Finset.sum_mul]
  have hInt : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x
          * Submission.BoseGases.aQ ℓ j Φ x
          * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2)
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    refine Submission.BoseGases.integrableOn_abox_of_continuous hℓ ?_
    exact ((Submission.BoseGases.aP_continuous hℓ i hfc).mul hfc).mul hwc
  rw [hsumfun]
  rw [MeasureTheory.integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hInt i)]
  exact Finset.sum_congr rfl (fun i _ => aP_aQ_term_eq hℓ i j hΦc)

theorem n0MassWord_eq_sqSum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseBoxFock.n0MassWord (n := N) ℓ Φ
      = ∑ j : Fin N, ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x) ^ 2
            * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 := by
  rw [Work.BoseBoxFock.n0MassWord]
  exact Finset.sum_congr rfl (fun j _ => massRow_eq_sqSum hℓ j hΦc)

end Work.BoseBoxFock
