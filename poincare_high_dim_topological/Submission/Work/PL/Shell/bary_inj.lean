import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic

namespace Work.PL.Shell

open Set Metric Finset
open scoped BigOperators

/-- The centroid of a finite set of points, as an affine combination:
`bary S` is the affine combination of the points of `S` with all weights `|S|⁻¹`. -/
theorem bary_inj {N : ℕ} {Δ : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {S T : Finset (PL.E N)} (hS : S.Nonempty) (hT : T.Nonempty)
    (hSΔ : S ⊆ Δ) (hTΔ : T ⊆ Δ) (h : Work.PL.Shell.bary S = Work.PL.Shell.bary T) : S = T := by
  classical
  -- The weight functions of the two centroids as affine combinations of `Δ`.
  set wS : PL.E N → ℝ := fun x => if x ∈ S then (S.card : ℝ)⁻¹ else 0 with hwS
  set wT : PL.E N → ℝ := fun x => if x ∈ T then (T.card : ℝ)⁻¹ else 0 with hwT
  -- Both weight functions have total weight `1` over `Δ`.
  have hsumS : ∑ i ∈ Δ, wS i = 1 := by
    rw [← Finset.sum_subset hSΔ (f := wS) (fun x _ hxS => by simp [hwS, hxS])]
    simp [hwS, Finset.sum_const]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt hS.card_pos))
  have hsumT : ∑ i ∈ Δ, wT i = 1 := by
    rw [← Finset.sum_subset hTΔ (f := wT) (fun x _ hxT => by simp [hwT, hxT])]
    simp [hwT, Finset.sum_const]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt hT.card_pos))
  -- Both weighted sums equal the corresponding centroid.
  have hvsumS : ∑ i ∈ Δ, wS i • i = bary S := by
    rw [← Finset.sum_subset hSΔ (f := fun i => wS i • i) (fun x _ hxS => by simp [hwS, hxS])]
    simp only [hwS, bary]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [ite_eq_left hx]
  have hvsumT : ∑ i ∈ Δ, wT i • i = bary T := by
    rw [← Finset.sum_subset hTΔ (f := fun i => wT i • i) (fun x _ hxT => by simp [hwT, hxT])]
    simp only [hwT, bary]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [ite_eq_left hx]
  -- Affine independence makes the weights unique.
  have hw : ∀ i ∈ Δ, wS i = wT i :=
    hΔ.eq_of_sum_eq_sum_subtype (by rw [hsumS, hsumT]) (by rw [hvsumS, hvsumT, h])
  -- Extract `S = T` from equality of weights.
  have hST : S ⊆ T := by
    intro x hxS
    have hxΔ : x ∈ Δ := hSΔ hxS
    have hwx := hw x hxΔ
    simp only [hwS, hwT] at hwx
    rw [ite_eq_left hxS] at hwx
    by_contra hxT
    rw [ite_eq_right hxT] at hwx
    exact (inv_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt hS.card_pos))) hwx
  have hTS : T ⊆ S := by
    intro x hxT
    have hxΔ : x ∈ Δ := hTΔ hxT
    have hwx := (hw x hxΔ).symm
    simp only [hwS, hwT] at hwx
    rw [ite_eq_left hxT] at hwx
    by_contra hxS
    rw [ite_eq_right hxS] at hwx
    exact (inv_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt hT.card_pos))) hwx
  exact Finset.Subset.antisymm hST hTS

end Work.PL.Shell
