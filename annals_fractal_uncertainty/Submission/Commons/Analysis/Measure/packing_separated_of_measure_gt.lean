import Mathlib
import Submission.Commons.Measure.Real.separated_points_of_measure

namespace Commons.Analysis.Measure

open MeasureTheory
open scoped ENNReal

/-- Given a `δ`-separated family of points of `A` indexed by `Fin (n+1)`, one can list those
points in increasing order, obtaining a strictly monotone family whose consecutive terms are at
distance at least `δ`. -/
theorem exists_strictMono_of_separated {A : Set ℝ} {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (t : Fin (n + 1) → ℝ) (ht : ∀ i, t i ∈ A) (hsep : ∀ i j, i ≠ j → δ ≤ |t i - t j|) :
    ∃ x : Fin (n + 1) → ℝ, StrictMono x ∧ (∀ i, x i ∈ A) ∧
      ∀ i : Fin n, x (Fin.castSucc i) + δ ≤ x i.succ := by
  classical
  set s : Finset ℝ := Finset.univ.image t with hs
  have hinj : Function.Injective t := by
    intro i j hij
    by_contra hne
    have h := hsep i j hne
    rw [hij, sub_self, abs_zero] at h
    linarith
  have hcard : s.card = n + 1 := by
    rw [hs, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hle : n + 1 ≤ s.card := hcard.ge
  let f : Fin (n + 1) ↪o ℝ := s.orderEmbOfCardLe (k := n + 1) hle
  refine ⟨fun i => f i, ?_, ?_, ?_⟩
  · exact f.strictMono
  · intro i
    change f i ∈ A
    have hmem : f i ∈ s := Finset.orderEmbOfCardLe_mem s hle i
    rw [hs, Finset.mem_image] at hmem
    obtain ⟨j, -, hj⟩ := hmem
    rw [← hj]
    exact ht j
  · intro i
    change f (Fin.castSucc i) + δ ≤ f i.succ
    have hlt : f (Fin.castSucc i) < f i.succ := f.strictMono Fin.castSucc_lt_succ
    have hamem : f (Fin.castSucc i) ∈ s := Finset.orderEmbOfCardLe_mem s hle _
    have hbmem : f i.succ ∈ s := Finset.orderEmbOfCardLe_mem s hle _
    rw [hs, Finset.mem_image] at hamem hbmem
    obtain ⟨p, -, hp⟩ := hamem
    obtain ⟨q, -, hq⟩ := hbmem
    have hpq : p ≠ q := by
      intro hpq
      rw [hpq] at hp
      exact (ne_of_lt hlt) (hp.symm.trans hq)
    have h := hsep p q hpq
    rw [hp, hq] at h
    have habs : |f (Fin.castSucc i) - f i.succ| = f i.succ - f (Fin.castSucc i) := by
      rw [abs_of_neg (sub_neg.mpr hlt), neg_sub]
    rw [habs] at h
    linarith

theorem packing_separated_of_measure_gt (E : Set ℝ) (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (0:ℝ) 1)
    (Δ : ℝ) (hΔ : 0 < Δ) (N : ℕ) (hmeas : 2 * (N:ℝ) * Δ < (volume E).toReal) :
    ∃ x : Fin (N+1) → ℝ, StrictMono x ∧ (∀ i, x i ∈ E) ∧
      (∀ i : Fin N, x (Fin.castSucc i) + Δ ≤ x i.succ) := by
  have hfin : volume E ≠ ⊤ := by
    have hle : volume E ≤ (1 : ENNReal) := by
      calc volume E ≤ volume (Set.Icc (0:ℝ) 1) := measure_mono hEsub
        _ = ENNReal.ofReal ((1:ℝ) - 0) := Real.volume_Icc
        _ = 1 := by norm_num
    exact ne_of_lt (lt_of_le_of_lt hle (by norm_num))
  obtain ⟨t, ht, hsep⟩ :=
    Commons.Measure.Real.separated_points_of_measure E hE hfin N Δ hΔ.le hmeas
  exact exists_strictMono_of_separated hΔ t ht hsep

end Commons.Analysis.Measure
