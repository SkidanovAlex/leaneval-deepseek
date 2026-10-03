import Mathlib
import Submission.Work.FIArea6Hecke.R.DiscDefs

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Casting `n.natAbs` to `ℝ` gives `|n|`. -/
lemma natAbs_cast_real (n : ℤ) : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  norm_num

/-- The Gaussian norm is the squared complex modulus. -/
lemma gnorm_coe_eq (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
  rw [Work.FIPlan.gnorm, GaussianInt.natCast_natAbs_norm, GaussianInt.intCast_real_norm]
  simp [Complex.normSq_apply, GaussianInt.intCast_re, GaussianInt.intCast_im, sq]

/-- Every Gaussian integer of norm `≤ X` (`X ≥ 0`) lies in the box `gBox ⌊√X⌋₊` of side
`2⌊√X⌋₊+1`. -/
lemma mem_gBox_of_gnorm_le {X : ℝ} {z : GaussianInt}
    (hz : (Work.FIPlan.gnorm z : ℝ) ≤ X) :
    z ∈ Work.FIPlan.gBox (⌊Real.sqrt X⌋₊) := by
  have hg : (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 = (Work.FIPlan.gnorm z : ℝ) :=
    (gnorm_coe_eq z).symm
  have hre2 : (z.re : ℝ) ^ 2 ≤ X := by nlinarith [sq_nonneg (z.im : ℝ), hg, hz]
  have him2 : (z.im : ℝ) ^ 2 ≤ X := by nlinarith [sq_nonneg (z.re : ℝ), hg, hz]
  have hre_abs : |(z.re : ℝ)| ≤ Real.sqrt X := Real.abs_le_sqrt hre2
  have him_abs : |(z.im : ℝ)| ≤ Real.sqrt X := Real.abs_le_sqrt him2
  have hnat : ∀ a : ℤ, |(a : ℝ)| ≤ Real.sqrt X → a.natAbs ≤ ⌊Real.sqrt X⌋₊ := by
    intro a ha
    apply Nat.le_floor
    rw [natAbs_cast_real a]
    exact ha
  have hre : (-(⌊Real.sqrt X⌋₊ : ℤ) ≤ z.re ∧ z.re ≤ (⌊Real.sqrt X⌋₊ : ℤ)) := by
    have h' : |z.re| ≤ ((⌊Real.sqrt X⌋₊ : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hnat z.re hre_abs
    exact abs_le.mp h'
  have him : (-(⌊Real.sqrt X⌋₊ : ℤ) ≤ z.im ∧ z.im ≤ (⌊Real.sqrt X⌋₊ : ℤ)) := by
    have h' : |z.im| ≤ ((⌊Real.sqrt X⌋₊ : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hnat z.im him_abs
    exact abs_le.mp h'
  rw [Work.FIPlan.gBox, Finset.mem_image]
  refine ⟨(z.re, z.im), ?_, ?_⟩
  · rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨hre, him⟩
  · exact Zsqrtd.ext rfl rfl

/-- The square box `gBox M` (`M : ℕ`) has `(2M+1)^2` elements. -/
lemma card_gBox_nat (M : ℕ) : (Work.FIPlan.gBox (M : ℤ)).card = (2 * M + 1) ^ 2 := by
  unfold Work.FIPlan.gBox
  rw [Finset.card_image_of_injective _ Work.FIPlan.gaussMk_injective]
  rw [Finset.product_eq_sprod, Finset.card_product, Int.card_Icc]
  have h : (((M : ℤ) + 1 - -(M : ℤ)).toNat) = 2 * M + 1 := by
    have h2 : ((M : ℤ) + 1 - -(M : ℤ)) = ((2 * M + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h2, Int.toNat_natCast]
  rw [h]
  ring

/-- **Trivial (cardinality) bound for the primary disc sum.** For `X ≥ 1` the sum of a coefficient-bounded function over the Gaussian integers of norm `≤ X` (in particular over the primary ones) is at most a constant times `X`: the disc `{z : |z|² ≤ X}` contains at most `(2√X+1)² ≤ 9X` lattice points. -/
theorem discSum_trivial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (chi : GaussianInt → ℂ), (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      ∀ X : ℝ, 1 ≤ X → ‖Work.FIArea6Hecke.R.discSum X chi‖ ≤ C * X := by
  refine ⟨9, by norm_num, ?_⟩
  intro chi hchi X hX
  classical
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  let S : Finset GaussianInt :=
    (Work.FIPlan.gBox ⌈X⌉₊).filter
      (fun z => Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X)
  have hS : S = (Work.FIPlan.gBox ⌈X⌉₊).filter
      (fun z => Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X) := rfl
  have hA : ‖Work.FIArea6Hecke.R.discSum X chi‖ ≤ (S.card : ℝ) := by
    change ‖∑ z ∈ Work.FIPlan.gBox ⌈X⌉₊,
        (if Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X then chi z else 0)‖
      ≤ (S.card : ℝ)
    refine le_trans (norm_sum_le (Work.FIPlan.gBox ⌈X⌉₊) _) ?_
    rw [hS, ← Finset.sum_boole
      (fun z => Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X)
      (Work.FIPlan.gBox ⌈X⌉₊)]
    refine Finset.sum_le_sum ?_
    intro z _
    by_cases hP : Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X
    · rw [if_pos hP, if_pos hP]; exact hchi z
    · simp [hP]
  have hsub : S ⊆ Work.FIPlan.gBox ⌊Real.sqrt X⌋₊ := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    exact mem_gBox_of_gnorm_le hz.2.2
  have hcard1 : (S.card : ℝ) ≤ ((Work.FIPlan.gBox ⌊Real.sqrt X⌋₊).card : ℝ) := by
    have h := Finset.card_le_card hsub
    exact_mod_cast h
  have hgcard : (Work.FIPlan.gBox ⌊Real.sqrt X⌋₊).card = (2 * ⌊Real.sqrt X⌋₊ + 1) ^ 2 :=
    card_gBox_nat ⌊Real.sqrt X⌋₊
  have hMle : ((⌊Real.sqrt X⌋₊ : ℕ) : ℝ) ≤ Real.sqrt X := Nat.floor_le (Real.sqrt_nonneg X)
  have hbound : (((2 * ⌊Real.sqrt X⌋₊ + 1) ^ 2 : ℕ) : ℝ) ≤ 9 * X := by
    have hcast : (((2 * ⌊Real.sqrt X⌋₊ + 1) ^ 2 : ℕ) : ℝ)
        = (2 * ((⌊Real.sqrt X⌋₊ : ℕ) : ℝ) + 1) ^ 2 := by push_cast; ring
    rw [hcast]
    nlinarith [hMle, Real.sq_sqrt hX0, Real.sqrt_nonneg X, hX, sq_nonneg (Real.sqrt X - 1)]
  calc ‖Work.FIArea6Hecke.R.discSum X chi‖ ≤ (S.card : ℝ) := hA
    _ ≤ ((Work.FIPlan.gBox ⌊Real.sqrt X⌋₊).card : ℝ) := hcard1
    _ = (((2 * ⌊Real.sqrt X⌋₊ + 1) ^ 2 : ℕ) : ℝ) := by rw [hgcard]
    _ ≤ 9 * X := hbound

end

end Work.FIArea6Hecke.R
