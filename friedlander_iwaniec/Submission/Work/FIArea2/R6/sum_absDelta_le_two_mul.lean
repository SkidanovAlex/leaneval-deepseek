import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIPlan.Interface

namespace Work.FIArea2.R6

open Finset

/-- Fibrewise bound: if every fibre of `f : α → β` over `t` has at most `k` elements, and `g ≥ 0`,
then `∑_{x ∈ s} g (f x) ≤ k * ∑_{b ∈ t} g b`. -/
lemma sum_comp_le_card_mul {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β) (g : β → ℝ) (k : ℕ)
    (hmaps : ∀ x ∈ s, f x ∈ t)
    (hcard : ∀ b ∈ t, (s.filter (fun x => f x = b)).card ≤ k)
    (hg : ∀ b, 0 ≤ g b) :
    (∑ x ∈ s, g (f x)) ≤ k * ∑ b ∈ t, g b := by
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => g (f x))]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have hinner : ∑ x ∈ s.filter (fun x => f x = b), g (f x)
      = ∑ x ∈ s.filter (fun x => f x = b), g b := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hx.2]
  rw [hinner, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard b hb) (hg b)

theorem sum_absDelta_le_two_mul {z1 : GaussianInt} {P : Finset GaussianInt} {X : ℕ} (g : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n)
    (hinj : ∀ z ∈ P, ∀ z' ∈ P, Work.FIPlan.Delta z1 z = Work.FIPlan.Delta z1 z' → z = z')
    (hle : ∀ z ∈ P, Work.FIPlan.absDelta z1 z ≤ X) :
    (∑ z ∈ P, g (Work.FIPlan.absDelta z1 z)) ≤ 2 * ∑ n ∈ Finset.range (X + 1), g n := by
  apply sum_comp_le_card_mul P (Finset.range (X + 1))
    (fun z => Work.FIPlan.absDelta z1 z) g 2 ?_ ?_ hg
  · intro z hz
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hle z hz))
  · intro b hb
    set F : Finset GaussianInt := P.filter (fun z => Work.FIPlan.absDelta z1 z = b) with hF
    have hinjOn : Set.InjOn (Work.FIPlan.Delta z1) ↑F := by
      intro x hx y hy hxy
      rw [hF, Finset.mem_coe, Finset.mem_filter] at hx hy
      exact hinj x hx.1 y hy.1 hxy
    have hsub : F.image (Work.FIPlan.Delta z1) ⊆ ({(b : ℤ), -(b : ℤ)} : Finset ℤ) := by
      intro d hd
      rw [Finset.mem_image] at hd
      obtain ⟨z, hzF, rfl⟩ := hd
      rw [hF, Finset.mem_filter] at hzF
      have hb' : (Work.FIPlan.Delta z1 z).natAbs = b := hzF.2
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases Int.natAbs_eq (Work.FIPlan.Delta z1 z) with h | h
      · left; rw [h, hb']
      · right; rw [h, hb']
    calc F.card = (F.image (Work.FIPlan.Delta z1)).card :=
          (Finset.card_image_of_injOn hinjOn).symm
      _ ≤ ({(b : ℤ), -(b : ℤ)} : Finset ℤ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two

end Work.FIArea2.R6
