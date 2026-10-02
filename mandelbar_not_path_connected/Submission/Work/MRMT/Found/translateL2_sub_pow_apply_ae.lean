/-
Work.MRMT.Found — the `N`-th finite difference of a translation on `L²(ℂ)`.

`(τ_t - 1)^N` applied to `X` is the `N`-th forward difference of `X` in the direction `t`,
and the lemma expands it by the binomial theorem:

  `((τ_t - 1)^N X)(z) = ∑_{j=0}^{N} (-1)^{N-j} · C(N,j) · X(z - j t)`  for a.e. `z`.

The proof has three ingredients:
* the evaluation of a single translation on `L²`, `translateL2_apply_ae`, which is the
  `coeFn` lemma for `Lp.compMeasurePreserving`;
* its iterates, `translateL2_pow_apply_ae`, by induction (`τ_t^{n+1} = τ_t ∘ τ_t^n`);
* the binomial theorem `Commute.add_pow` in the algebra of continuous linear endomorphisms
  of `L²(ℂ)`, which linearises the operator power into a linear combination of powers of
  `τ_t`, combined with additivity and `ℂ`-homogeneity of the coercion `Lp → (ℂ → ℂ)`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unnecessarySimpa false

noncomputable section

open MeasureTheory Filter Complex
open scoped ENNReal

namespace Work.MRMT.Found

/-- The coercion of a finite sum in `L²(ℂ)` is a.e. the sum of the coercions. -/
private theorem Lp_coeFn_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Lp ℂ 2 (volume : Measure ℂ)) :
    ((∑ i ∈ s, f i : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume]
      fun z => ∑ i ∈ s, ((f i : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z := by
  classical
  induction s using Finset.induction with
  | empty =>
      filter_upwards [Lp.coeFn_zero (Lp ℂ 2 (volume : Measure ℂ)) 2 (volume : Measure ℂ)]
        with z hz
      simpa using hz
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with z h1 h2
      rw [h1]
      simp only [Pi.add_apply]
      rw [h2, Finset.sum_insert ha]

/-- A finite sum of a.e. equal functions is a.e. equal. -/
private theorem eventuallyEq_finset_sum {ι : Type*} (s : Finset ι) {f g : ι → ℂ → ℂ}
    (h : ∀ i ∈ s, f i =ᵐ[volume] g i) :
    (fun z => ∑ i ∈ s, f i z) =ᵐ[volume] fun z => ∑ i ∈ s, g i z := by
  filter_upwards [(Finset.eventually_all s).2 h] with z hz
  exact Finset.sum_congr rfl fun i hi => hz i hi

/-- Evaluation of a single translation on `L²(ℂ)`: `(τ_t f)(z) = f (z - t)` a.e. -/
theorem translateL2_apply_ae (t : ℂ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    (((translateL2 t) f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume]
      fun z => (f : ℂ → ℂ) (z - t) := by
  rw [show translateL2 t f = Lp.compMeasurePreserving (fun w : ℂ => w - t)
      (measurePreserving_sub_right volume t) f from rfl]
  simpa [Function.comp_def] using
    (Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume t))

/-- Iterates of a translation: `(τ_t^n f)(z) = f (z - n t)` a.e. -/
theorem translateL2_pow_apply_ae (t : ℂ) (X : Lp ℂ 2 (volume : Measure ℂ)) (n : ℕ) :
    ((((translateL2 t) ^ n) X : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume]
      fun z => (X : ℂ → ℂ) (z - (n : ℂ) * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      have h1 := translateL2_apply_ae t (((translateL2 t) ^ n) X)
      have h2 := (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae_eq_comp ih
      refine h1.trans (h2.trans ?_)
      filter_upwards with z
      simp only [Function.comp_apply]
      have h : (z - t) - (n : ℂ) * t = z - ((n + 1 : ℕ) : ℂ) * t := by push_cast; ring
      rw [h]

/-- The binomial expansion of the operator `(τ_t - 1)^N` in the algebra of continuous linear
endomorphisms of `L²(ℂ)`. -/
theorem translateL2_sub_one_pow_eq_sum (t : ℂ) (N : ℕ) :
    (translateL2 t - 1) ^ N
      = ∑ m ∈ Finset.range (N + 1),
          (((-1 : ℂ) ^ (N - m) * (N.choose m : ℂ))) •
            (translateL2 t) ^ m := by
  rw [sub_eq_add_neg,
    Commute.add_pow (Commute.neg_right (Commute.one_right (translateL2 t))) N]
  apply Finset.sum_congr rfl
  intro m _
  have hneg : (-1 : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ)) ^ (N - m)
      = ((-1 : ℂ) ^ (N - m)) •
        (1 : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ)) := by
    rw [show (-1 : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ))
        = algebraMap ℂ _ (-1) by simp, ← map_pow, Algebra.algebraMap_eq_smul_one]
  have hnat : (↑(N.choose m) :
        Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ))
      = ((N.choose m : ℂ)) •
        (1 : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ)) := by
    rw [show (↑(N.choose m) :
          Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ))
        = algebraMap ℂ _ (↑(N.choose m)) by simp, Algebra.algebraMap_eq_smul_one]
  rw [hneg, hnat]
  simp [mul_smul_comm, smul_smul, mul_comm]

theorem translateL2_sub_pow_apply_ae (N : ℕ) (t : ℂ)
    (X : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    ((((Work.MRMT.Found.translateL2 t - 1) ^ N) X : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ)
      =ᵐ[MeasureTheory.volume]
    fun z => ∑ j ∈ Finset.range (N+1), (-1 : ℂ) ^ (N - j) * (N.choose j : ℂ) * ((X : ℂ → ℂ) (z - (j : ℂ) * t)) := by
  rw [translateL2_sub_one_pow_eq_sum]
  rw [sum_apply]
  have hterm : ∀ m : ℕ,
      (((((-1 : ℂ) ^ (N - m) * (N.choose m : ℂ)) • (translateL2 t) ^ m) X :
          Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume]
        fun z => (-1 : ℂ) ^ (N - m) * (N.choose m : ℂ) *
          ((X : ℂ → ℂ) (z - (m : ℂ) * t)) := by
    intro m
    rw [smul_apply]
    filter_upwards [Lp.coeFn_smul ((-1 : ℂ) ^ (N - m) * (N.choose m : ℂ))
        (((translateL2 t) ^ m) X), translateL2_pow_apply_ae t X m] with z hz1 hz2
    rw [hz1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hz2]
  refine (Lp_coeFn_finset_sum (Finset.range (N + 1))
    (fun m => (((-1 : ℂ) ^ (N - m) * (N.choose m : ℂ)) • (translateL2 t) ^ m) X)).trans ?_
  exact eventuallyEq_finset_sum _ (fun m _ => hterm m)

end Work.MRMT.Found
