import Mathlib.MeasureTheory.Integral.Pi
import Submission.Commons.MeasureTheory.Integral.integral_fintype_prod_indicator_Ioi

open scoped BigOperators
open MeasureTheory

namespace Commons.MeasureTheory.Integral

private lemma hasCompactSupport_mul_shift {f g : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun s => f s * g s) :=
  (hf.isCompact).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_mul_subset_left (f := f) (g := g))

private lemma integrable_indicator_Ici_mul {f g : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (_hgc : HasCompactSupport g) :
    Integrable ((Set.Ici (0:ℝ)).indicator (fun s => f s * g s)) := by
  have hcont : Continuous (fun s => f s * g s) := hf.mul hg
  have hcs : HasCompactSupport (fun s => f s * g s) := hasCompactSupport_mul_shift hfc
  exact (hcont.integrable_of_hasCompactSupport hcs).indicator measurableSet_Ici

private lemma integrable_prod_indicator_Ici {ι : Type*} [Fintype ι] (F G : ι → ℝ → ℝ)
    (hFc : ∀ i, Continuous (F i)) (hFcs : ∀ i, HasCompactSupport (F i))
    (hGc : ∀ i, Continuous (G i)) (hGcs : ∀ i, HasCompactSupport (G i)) :
    Integrable (fun t : ι → ℝ => ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => F i s * G i s) (t i)) := by
  have h : ∀ i, Integrable ((Set.Ici (0:ℝ)).indicator (fun s => F i s * G i s))
      (volume : Measure ℝ) :=
    fun i => integrable_indicator_Ici_mul (hFc i) (hFcs i) (hGc i) (hGcs i)
  have h2 := Integrable.fintype_prod
    (f := fun i => (Set.Ici (0:ℝ)).indicator (fun s => F i s * G i s))
    (μ := fun _ : ι => (volume : Measure ℝ)) h
  have hvol : (volume : Measure (ι → ℝ)) = Measure.pi (fun _ : ι => (volume : Measure ℝ)) := by
    rw [MeasureTheory.volume_pi]
  rw [hvol]
  exact h2

private lemma prod_Ici_indicator_mul {ι : Type*} [Fintype ι] {J : ℕ}
    (H K : Fin J → ι → ℝ → ℝ) (t : ι → ℝ) (j j' : Fin J) :
    (∏ i, H j i (t i)) * (∏ i, K j' i (t i)) *
        (∏ i, (Set.Ici (0:ℝ)).indicator (fun _ => (1:ℝ)) (t i))
      = ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * K j' i s) (t i) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : t i ∈ Set.Ici (0:ℝ)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

theorem sum_integral_prod_eq_integral_mul {ι : Type*} [Fintype ι] {J : ℕ}
    (H K : Fin J → ι → ℝ → ℝ)
    (hHc : ∀ j i, Continuous (H j i)) (hHcs : ∀ j i, HasCompactSupport (H j i))
    (hKc : ∀ j i, Continuous (K j i)) (hKcs : ∀ j i, HasCompactSupport (K j i))
    (u v c d : Fin J → ℝ) :
    (∑ j : Fin J, ∑ j' : Fin J, c j * d j' * (u j * v j' *
        ∫ t : ι → ℝ,
          ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * K j' i s) (t i)))
      = ∫ t : ι → ℝ,
          (∑ j : Fin J, c j * u j * ∏ i, H j i (t i)) *
            (∑ j' : Fin J, d j' * v j' * ∏ i, K j' i (t i)) *
              ∏ i, (Set.Ici (0:ℝ)).indicator (fun _ => (1:ℝ)) (t i) := by
  have hint : ∀ j j', Integrable (fun t : ι → ℝ =>
      ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * K j' i s) (t i)) :=
    fun j j' => integrable_prod_indicator_Ici (H j) (K j') (fun i => hHc j i)
      (fun i => hHcs j i) (fun i => hKc j' i) (fun i => hKcs j' i)
  have htermint : ∀ j j', Integrable (fun t : ι → ℝ =>
      c j * d j' * (u j * v j' *
        ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * K j' i s) (t i))) :=
    fun j j' => ((hint j j').const_mul (u j * v j')).const_mul (c j * d j')
  have hpt : ∀ t : ι → ℝ,
      (∑ j : Fin J, c j * u j * ∏ i, H j i (t i)) *
        (∑ j' : Fin J, d j' * v j' * ∏ i, K j' i (t i)) *
          ∏ i, (Set.Ici (0:ℝ)).indicator (fun _ => (1:ℝ)) (t i)
      = ∑ j : Fin J, ∑ j' : Fin J, c j * d j' * (u j * v j' *
          ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * K j' i s) (t i)) := by
    intro t
    have hAB : (∑ j : Fin J, c j * u j * ∏ i, H j i (t i)) *
          (∑ j' : Fin J, d j' * v j' * ∏ i, K j' i (t i))
        = ∑ j : Fin J, ∑ j' : Fin J,
            (c j * u j * ∏ i, H j i (t i)) * (d j' * v j' * ∏ i, K j' i (t i)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    rw [hAB, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j' _
    rw [← prod_Ici_indicator_mul H K t j j']
    ring
  have hmain : (∫ t : ι → ℝ,
        (∑ j : Fin J, c j * u j * ∏ i, H j i (t i)) *
          (∑ j' : Fin J, d j' * v j' * ∏ i, K j' i (t i)) *
            ∏ i, (Set.Ici (0:ℝ)).indicator (fun _ => (1:ℝ)) (t i))
      = ∑ j : Fin J, ∑ j' : Fin J, c j * d j' * (u j * v j' *
          ∫ t : ι → ℝ, ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * K j' i s) (t i)) := by
    have hfun : (fun t : ι → ℝ =>
          (∑ j : Fin J, c j * u j * ∏ i, H j i (t i)) *
            (∑ j' : Fin J, d j' * v j' * ∏ i, K j' i (t i)) *
              ∏ i, (Set.Ici (0:ℝ)).indicator (fun _ => (1:ℝ)) (t i))
        = (fun t : ι → ℝ => ∑ j : Fin J, ∑ j' : Fin J, c j * d j' * (u j * v j' *
            ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * K j' i s) (t i))) :=
      funext hpt
    rw [hfun]
    rw [integral_finsetSum Finset.univ
      (fun j _ => integrable_finsetSum Finset.univ (fun j' _ => htermint j j'))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum Finset.univ (fun j' _ => htermint j j')]
    apply Finset.sum_congr rfl
    intro j' _
    rw [integral_const_mul, integral_const_mul]
  exact hmain.symm

end Commons.MeasureTheory.Integral