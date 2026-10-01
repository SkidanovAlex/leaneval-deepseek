import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.LinnikAreas.JMAux

open scoped BigOperators

/-- **A finite family of zero-pairs is dominated by the family zero-count.**
For a finite set `S` of pairs `(χ, ρ)` of Dirichlet characters and complex numbers with
`Re ρ ≥ σ` and `|Im ρ| ≤ T`, the multiplicity-weighted cardinality of `S` is at most
`∑_χ zeroCountIn χ σ T`.

Indeed every pair contributing to the left-hand side has `Re ρ < 1` (the zeros of the completed
`L`-function have real part `< 1`, `Work.LinnikAreas.zeroMult_re_lt_one`), so its point lies in
the box `σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T`; the zeros of a single character in that box are finite
(`Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box`), which lets the `finsum` defining
`zeroCountIn` be rewritten as a sum over that finite set before comparing termwise. -/
lemma FinsetSumLeFamilyZeroCount {q : ℕ} [NeZero q] {σ T : ℝ}
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hre : ∀ z ∈ S, σ ≤ z.2.re) (him : ∀ z ∈ S, |z.2.im| ≤ T) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
      ≤ ∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T := by
  classical
  rw [(Finset.sum_fiberwise S (fun z : DirichletCharacter ℂ q × ℂ => z.1)
        (fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))).symm]
  refine Finset.sum_le_sum fun χ _ => ?_
  -- the finite box of zeros of `χ` with `σ ≤ Re ≤ 1`, `|Im| ≤ T`
  set F : Finset ℂ := (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ σ T).toFinset with hF
  set g : ℂ → ℝ := fun ρ => if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
      then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0 with hg
  have hg_apply : ∀ ρ : ℂ, g ρ = if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
      then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0 := by
    intro ρ
    simp only [hg]
  have hg_nonneg : ∀ ρ, 0 ≤ g ρ := by
    intro ρ
    rw [hg_apply ρ]
    by_cases hP : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
    · rw [if_pos hP]; exact Nat.cast_nonneg _
    · rw [if_neg hP]
  have hmemF : ∀ ρ : ℂ, ρ ∈ F ↔ Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re
      ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T := by
    intro ρ
    simp only [hF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hcount : Work.LinnikAreas.zeroCountIn χ σ T = ∑ᶠ ρ : ℂ, g ρ := by
    simp only [Work.LinnikAreas.zeroCountIn, hg]
  rw [hcount]
  have hsupp : Function.support g ⊆ ↑F := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    by_cases hP : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
    · have hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0 := by
        intro h0
        rw [hg_apply ρ, if_pos hP, h0] at hρ
        simp at hρ
      exact (hmemF ρ).mpr ⟨hzm, hP⟩
    · rw [hg_apply ρ, if_neg hP] at hρ
      exact absurd rfl hρ
  rw [finsum_eq_sum_of_support_subset g hsupp]
  -- compare the fibre sum with the sum over the box
  have hterm : ∀ z ∈ S.filter (fun z => z.1 = χ),
      (Work.LinnikContract.zeroMult z.1 z.2 : ℝ) = g z.2 := by
    intro z hz
    have hz1 : z.1 = χ := (Finset.mem_filter.mp hz).2
    have hzS : z ∈ S := (Finset.mem_filter.mp hz).1
    rw [hg_apply z.2]
    by_cases hP : σ ≤ z.2.re ∧ z.2.re ≤ 1 ∧ |z.2.im| ≤ T
    · rw [if_pos hP, hz1]
    · rw [if_neg hP]
      have hle1 : ¬ (z.2.re ≤ 1) := fun h1 => hP ⟨hre z hzS, h1, him z hzS⟩
      have h0 : Work.LinnikContract.zeroMult χ z.2 = 0 := by
        by_contra hne
        exact absurd (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hne)
          (not_lt.mpr (le_of_lt (not_le.mp hle1)))
      simp [hz1, h0]
  have hinj : Set.InjOn (fun z : DirichletCharacter ℂ q × ℂ => z.2)
      ↑(S.filter (fun z => z.1 = χ)) := by
    intro z1 hz1 z2 hz2 heq
    have h1 : z1.1 = χ := (Finset.mem_filter.mp hz1).2
    have h2 : z2.1 = χ := (Finset.mem_filter.mp hz2).2
    exact Prod.ext (by rw [h1, h2]) heq
  have himage : ∑ ρ ∈ (S.filter (fun z => z.1 = χ)).image (fun z => z.2), g ρ
      = ∑ z ∈ S.filter (fun z => z.1 = χ), g z.2 := Finset.sum_image hinj
  have hzero : ∀ ρ ∈ (S.filter (fun z => z.1 = χ)).image (fun z => z.2), ρ ∉ F →
      g ρ = 0 := by
    intro ρ hρ hρF
    obtain ⟨z, hzT, hz2⟩ := Finset.mem_image.mp hρ
    rw [← hz2] at hρF ⊢
    rw [hg_apply z.2]
    by_cases hP : σ ≤ z.2.re ∧ z.2.re ≤ 1 ∧ |z.2.im| ≤ T
    · rw [if_pos hP]
      have h0 : Work.LinnikContract.zeroMult χ z.2 = 0 := by
        by_contra hne
        exact hρF ((hmemF z.2).mpr ⟨hne, hP⟩)
      simp [h0]
    · rw [if_neg hP]
  calc ∑ z ∈ S.filter (fun z => z.1 = χ), (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
      = ∑ z ∈ S.filter (fun z => z.1 = χ), g z.2 := Finset.sum_congr rfl hterm
    _ = ∑ ρ ∈ (S.filter (fun z => z.1 = χ)).image (fun z => z.2), g ρ := himage.symm
    _ = ∑ ρ ∈ ((S.filter (fun z => z.1 = χ)).image (fun z => z.2)) ∩ F, g ρ :=
        (Finset.sum_subset Finset.inter_subset_left (by
          intro x hxU hxnot
          exact hzero x hxU (fun hxF => hxnot (Finset.mem_inter.mpr ⟨hxU, hxF⟩)))).symm
    _ ≤ ∑ ρ ∈ F, g ρ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun ρ _ _ => hg_nonneg ρ)

lemma FinsetSumLeFamGe {q : ℕ} [NeZero q] (C A σ₀ : ℝ) (hσ₀ : 0 ≤ σ₀)
    (hfam : ∀ σ T : ℝ, σ₀ ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T
        ≤ C * ((q:ℝ) * T) ^ (A * (1 - σ)))
    {σ T : ℝ} (hσ : σ₀ ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T)
    {S : Finset (DirichletCharacter ℂ q × ℂ)}
    (h1 : ∀ z ∈ S, z.1 ≠ 1) (hre : ∀ z ∈ S, σ ≤ z.2.re) (him : ∀ z ∈ S, |z.2.im| ≤ T) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)) ≤ C * ((q:ℝ) * T) ^ (A * (1 - σ)) := by
  calc (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
      ≤ ∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T :=
        FinsetSumLeFamilyZeroCount S hre him
    _ ≤ C * ((q:ℝ) * T) ^ (A * (1 - σ)) := hfam σ T hσ hσ1 hT

end Work.LinnikAreas.JMAux
