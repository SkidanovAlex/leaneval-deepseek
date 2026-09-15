import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Submission.Commons.Combinatorics.Transference.sum_biUnion_small_atoms
import Submission.Commons.Combinatorics.Transference.part_subset_biUnion_of_mem_atoms

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Green–Tao Proposition 6.6, the exceptional set `Ω`.**

Let `part` be the atoms of the join `⋁_j B_{ε,η}(𝒟F_j)` and suppose every atom has
`(ν−1)`-mass at most `δ`.  If `δ < |G|·θ` there is a `part`-saturated set `Ω` with
`(ν+1)`-mass at most `|G|θ·#atoms` such that outside `Ω` the conditional expectation of
`ν−1` on every atom is at most `2δ/(|G|θ − δ)`. -/
theorem bohr_sigma_Omega {p : ℕ} [Fact p.Prime] (part : ZMod p → Finset (ZMod p))
    (hmem : ∀ x, x ∈ part x) (heq : ∀ x y, y ∈ part x → part y = part x)
    (ν : ZMod p → ℝ) (hν : ∀ x, 0 ≤ ν x)
    {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (hηδ : δ < (Fintype.card (ZMod p) : ℝ) * θ)
    (hAtom : ∀ x, |∑ y ∈ part x, (ν y - 1)| ≤ δ) :
    ∃ Ω : Finset (ZMod p),
      (∑ x ∈ Ω, (ν x + 1) ≤ ((Fintype.card (ZMod p) : ℝ) * θ) *
        (((Finset.univ.image part)).card : ℝ)) ∧
      (∀ x ∈ Ω, part x ⊆ Ω) ∧
      ∀ x : ZMod p, x ∉ Ω → |((part x).card : ℝ)⁻¹ * ∑ y ∈ part x, (ν y - 1)|
          ≤ 2 * δ / ((Fintype.card (ZMod p) : ℝ) * θ - δ) := by
  classical
  set P : ℝ := (Fintype.card (ZMod p) : ℝ) with hP
  set η : ℝ := P * θ with hη
  set τ : ℝ := 2 * δ / (P * θ - δ) with hτ
  set atoms : Finset (Finset (ZMod p)) := Finset.univ.image part with hatoms
  set BadA : Finset (Finset (ZMod p)) :=
    atoms.filter (fun A => τ < |(A.card : ℝ)⁻¹ * ∑ y ∈ A, (ν y - 1)|) with hBadA
  set Small : Finset (Finset (ZMod p)) :=
    atoms.filter (fun A => ∑ y ∈ A, (ν y + 1) ≤ η) with hSmall
  have hden_pos : 0 < P * θ - δ := by rw [hP]; linarith
  have hτ_nonneg : 0 ≤ τ := by
    rw [hτ]; exact div_nonneg (by linarith) (le_of_lt hden_pos)
  have hη_nonneg : 0 ≤ η := by
    rw [hη]; exact mul_nonneg (by rw [hP]; positivity) (le_of_lt hθ)
  have hmem_atoms : ∀ x : ZMod p, part x ∈ atoms := by
    intro x; rw [hatoms]; exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  -- Split `∑ (ν+1)` into `∑ (ν-1)` plus twice the cardinality.
  have hMeq : ∀ A : Finset (ZMod p),
      ∑ y ∈ A, (ν y + 1) = (∑ y ∈ A, (ν y - 1)) + 2 * (A.card : ℝ) := by
    intro A
    have h1 : ∑ y ∈ A, (ν y + 1) = ∑ y ∈ A, ((ν y - 1) + 2) := by
      apply Finset.sum_congr rfl; intro y hy; ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  -- Every atom of `BadA` has `(ν+1)`-mass at most `η = P*θ`.
  have hbad_bound : ∀ A ∈ BadA, ∑ y ∈ A, (ν y + 1) ≤ η := by
    intro A hA
    rw [hBadA, Finset.mem_filter] at hA
    obtain ⟨hAatoms, hAbad⟩ := hA
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (hatoms ▸ hAatoms)
    have hSA : |∑ y ∈ A, (ν y - 1)| ≤ δ := by rw [← ha]; exact hAtom a
    have hcardpos : 0 < A.card := by
      rw [← ha]; exact Finset.card_pos.mpr ⟨a, hmem a⟩
    have hcpos : 0 < (A.card : ℝ) := by exact_mod_cast hcardpos
    have habs : |(A.card : ℝ)⁻¹ * ∑ y ∈ A, (ν y - 1)|
        = (A.card : ℝ)⁻¹ * |∑ y ∈ A, (ν y - 1)| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hcpos)]
    have hAbad' : τ < (A.card : ℝ)⁻¹ * |∑ y ∈ A, (ν y - 1)| := by
      rw [← habs]; exact hAbad
    have hmul : τ * (A.card : ℝ) < |∑ y ∈ A, (ν y - 1)| := by
      have h := mul_lt_mul_of_pos_right hAbad' hcpos
      have hcne : (A.card : ℝ) ≠ 0 := ne_of_gt hcpos
      have heq : (A.card : ℝ)⁻¹ * |∑ y ∈ A, (ν y - 1)| * (A.card : ℝ)
          = |∑ y ∈ A, (ν y - 1)| := by
        rw [mul_assoc, mul_comm (|∑ y ∈ A, (ν y - 1)|) (A.card : ℝ), ← mul_assoc,
          inv_mul_cancel₀ hcne, one_mul]
      rw [heq] at h; exact h
    have hτδ : τ * (A.card : ℝ) < δ := lt_of_lt_of_le hmul hSA
    have hδpos : 0 < δ :=
      lt_of_le_of_lt (mul_nonneg hτ_nonneg (le_of_lt hcpos)) hτδ
    have hkey : 2 * (A.card : ℝ) < P * θ - δ := by
      rw [hτ] at hτδ
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden_pos] at hτδ
      have h2 : δ * (2 * (A.card : ℝ)) < δ * (P * θ - δ) := by linarith
      exact lt_of_mul_lt_mul_left h2 (le_of_lt hδpos)
    rw [hMeq A, hη]
    have hSA' : (∑ y ∈ A, (ν y - 1)) ≤ δ := le_trans (le_abs_self _) hSA
    linarith
  -- `Ω` (the union of the bad atoms) is contained in the union of the small atoms.
  have hΩU : BadA.biUnion (fun A => A) ⊆ Small.biUnion (fun A => A) := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨A, hA, hxA⟩ := hx
    obtain ⟨hAatoms, hAbad⟩ := Finset.mem_filter.mp (hBadA ▸ hA)
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (hatoms ▸ hAatoms)
    have hxpa : x ∈ part a := by rw [ha]; exact hxA
    have hpx : part x = A := by rw [heq a x hxpa, ha]
    rw [Finset.mem_biUnion]
    refine ⟨part x, ?_, hmem x⟩
    rw [hSmall, Finset.mem_filter]
    exact ⟨hmem_atoms x, by rw [hpx]; exact hbad_bound A hA⟩
  have hsat : ∀ x ∈ BadA.biUnion (fun A => A), part x ⊆ BadA.biUnion (fun A => A) :=
    part_subset_biUnion_of_mem_atoms part heq
      (fun A hA => hatoms ▸ (Finset.mem_filter.mp (hBadA ▸ hA)).1)
  have houtside : ∀ x : ZMod p, x ∉ BadA.biUnion (fun A => A) →
      |((part x).card : ℝ)⁻¹ * ∑ y ∈ part x, (ν y - 1)|
        ≤ 2 * δ / ((Fintype.card (ZMod p) : ℝ) * θ - δ) := by
    intro x hx
    have hnotbad : ¬ (τ < |((part x).card : ℝ)⁻¹ * ∑ y ∈ part x, (ν y - 1)|) := by
      intro hb
      apply hx
      rw [Finset.mem_biUnion]
      refine ⟨part x, ?_, hmem x⟩
      rw [hBadA, Finset.mem_filter]
      exact ⟨hmem_atoms x, hb⟩
    have hle : |((part x).card : ℝ)⁻¹ * ∑ y ∈ part x, (ν y - 1)| ≤ τ :=
      not_lt.mp hnotbad
    rw [hτ] at hle
    rw [hP] at hle
    exact hle
  refine ⟨BadA.biUnion (fun A => A), ?_, hsat, houtside⟩
  have hmass_le : ∑ x ∈ Small.biUnion (fun A => A), (ν x + 1) ≤ η * (atoms.card : ℝ) := by
    have h := sum_biUnion_small_atoms part hmem heq ν hν hη_nonneg
    simpa [hSmall, hatoms] using h
  have hΩle : ∑ x ∈ BadA.biUnion (fun A => A), (ν x + 1) ≤ η * (atoms.card : ℝ) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hΩU
      (fun i _ _ => by linarith [hν i])) hmass_le
  simpa [hη, hP, hatoms] using hΩle

end Commons.Combinatorics.Transference