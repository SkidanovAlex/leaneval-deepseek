import Mathlib
import Submission.Work.FIArea4.WdyadSetup

namespace Work.FIArea4

open Finset

/-- For a nonnegative kernel `f`, summing `f d1 (a % d1) * f d2 (a % d2)` over a full
period `a < lcm d1 d2` costs at most the product of the two complete sums.

Indeed `a ↦ (a % d1, a % d2)` is injective on `range (lcm d1 d2)` (two values with the
same pair of residues differ by a multiple of both `d1` and `d2`, hence of their `lcm`,
which is impossible below `lcm`), and its image lies in `range d1 × range d2`; dropping
the remaining nonnegative terms gives the claim. -/
lemma sum_lcm_mod_mul_le (d1 d2 : ℕ) (f : ℕ → ℕ → ℝ)
    (h1 : 0 < d1) (h2 : 0 < d2) (hf : ∀ d x, 0 ≤ f d x) :
    (∑ a ∈ Finset.range (Nat.lcm d1 d2), f d1 (a % d1) * f d2 (a % d2))
      ≤ (∑ x ∈ Finset.range d1, f d1 x) * (∑ y ∈ Finset.range d2, f d2 y) := by
  classical
  have hx : Set.InjOn (fun a => (a % d1, a % d2)) ↑(Finset.range (Nat.lcm d1 d2)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    have hmod1 : a % d1 = b % d1 := congrArg Prod.fst hab
    have hmod2 : a % d2 = b % d2 := congrArg Prod.snd hab
    rcases le_total a b with hle | hle
    · by_contra hne
      have hlt : a < b := lt_of_le_of_ne hle hne
      have hd1 : d1 ∣ b - a := (Nat.modEq_iff_dvd' hle).mp hmod1
      have hd2 : d2 ∣ b - a := (Nat.modEq_iff_dvd' hle).mp hmod2
      have hdvd : Nat.lcm d1 d2 ∣ b - a := Nat.lcm_dvd hd1 hd2
      have hpos : 0 < b - a := Nat.sub_pos_of_lt hlt
      have hle' : Nat.lcm d1 d2 ≤ b - a := Nat.le_of_dvd hpos hdvd
      omega
    · by_contra hne
      have hlt : b < a := lt_of_le_of_ne hle (fun h => hne h.symm)
      have hd1 : d1 ∣ a - b := (Nat.modEq_iff_dvd' hle).mp hmod1.symm
      have hd2 : d2 ∣ a - b := (Nat.modEq_iff_dvd' hle).mp hmod2.symm
      have hdvd : Nat.lcm d1 d2 ∣ a - b := Nat.lcm_dvd hd1 hd2
      have hpos : 0 < a - b := Nat.sub_pos_of_lt hlt
      have hle' : Nat.lcm d1 d2 ≤ a - b := Nat.le_of_dvd hpos hdvd
      omega
  have hsub : (Finset.range (Nat.lcm d1 d2)).image (fun a => (a % d1, a % d2))
      ⊆ (Finset.range d1) ×ˢ (Finset.range d2) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.mod_lt a h1, Nat.mod_lt a h2⟩
  have hnn : ∀ p ∈ (Finset.range d1) ×ˢ (Finset.range d2),
      p ∉ (Finset.range (Nat.lcm d1 d2)).image (fun a => (a % d1, a % d2)) →
      0 ≤ f d1 p.1 * f d2 p.2 :=
    fun p _ _ => mul_nonneg (hf d1 p.1) (hf d2 p.2)
  calc
    (∑ a ∈ Finset.range (Nat.lcm d1 d2), f d1 (a % d1) * f d2 (a % d2))
        = ∑ p ∈ (Finset.range (Nat.lcm d1 d2)).image (fun a => (a % d1, a % d2)),
            f d1 p.1 * f d2 p.2 :=
          (Finset.sum_image (f := fun p : ℕ × ℕ => f d1 p.1 * f d2 p.2)
            (g := fun a => (a % d1, a % d2)) hx).symm
    _ ≤ ∑ p ∈ (Finset.range d1) ×ˢ (Finset.range d2), f d1 p.1 * f d2 p.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    _ = (∑ x ∈ Finset.range d1, f d1 x) * (∑ y ∈ Finset.range d2, f d2 y) := by
        rw [Finset.sum_product]
        exact (Finset.sum_mul_sum _ _ _ _).symm

theorem sigma_gamma_le (D : ℕ) (γ : ℕ → ℕ → ℂ) :
    (∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
      ≤ (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) ^ 2 := by
  classical
  have hpos : ∀ d ∈ Finset.Ioc D (2 * D), 0 < d := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    omega
  calc
    (∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
      ≤ ∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
          (∑ a ∈ Finset.range d1, Complex.normSq (γ a d1))
            * (∑ a ∈ Finset.range d2, Complex.normSq (γ a d2)) :=
        Finset.sum_le_sum (fun d1 hd1 => Finset.sum_le_sum (fun d2 hd2 =>
          sum_lcm_mod_mul_le d1 d2 (fun d x => Complex.normSq (γ x d))
            (hpos d1 hd1) (hpos d2 hd2) (fun d x => Complex.normSq_nonneg _)))
    _ = (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) ^ 2 := by
        rw [pow_two]
        exact (Finset.sum_mul_sum _ _ _ _).symm

end Work.FIArea4
