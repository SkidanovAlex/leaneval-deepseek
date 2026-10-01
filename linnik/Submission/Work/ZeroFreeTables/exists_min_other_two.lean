import Mathlib
import Submission.Work.ZeroFreeTables.exists_min_other_wide

namespace Work.ZeroFreeTables

theorem exists_min_other_two {q : ℕ} [NeZero q] (H : ℝ) (hH : 0 ≤ H)
    (χ₁ χ₂ ψ₀ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hψ₀ : ψ₀ ≠ 1) (hψ₀₁ : ψ₀ ≠ χ₁) (hψ₀₁' : ψ₀ ≠ χ₁⁻¹) (hψ₀₂ : ψ₀ ≠ χ₂) (hψ₀₂' : ψ₀ ≠ χ₂⁻¹)
    (hρ : Work.LinnikContract.zeroMult ψ₀ ρ ≠ 0) (hρim : |ρ.im| ≤ H) :
    ∃ (χ₃ : DirichletCharacter ℂ q) (ρ₃ : ℂ),
      χ₃ ≠ 1 ∧ χ₃ ≠ χ₁ ∧ χ₃ ≠ χ₁⁻¹ ∧ χ₃ ≠ χ₂ ∧ χ₃ ≠ χ₂⁻¹ ∧
      Work.LinnikContract.zeroMult χ₃ ρ₃ ≠ 0 ∧ |ρ₃.im| ≤ H ∧
      Work.LinnikContract.lamOf q ρ₃ ≤ Work.LinnikContract.lamOf q ρ ∧
      ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
        |u.im| ≤ H → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ → ψ ≠ χ₂ → ψ ≠ χ₂⁻¹ →
        Work.LinnikContract.lamOf q ρ₃ ≤ Work.LinnikContract.lamOf q u := by
  classical
  -- At level `1` there is only one Dirichlet character, contradicting `ψ₀ ≠ 1`.
  by_cases hq1 : q = 1
  · subst hq1
    exact absurd (Subsingleton.elim ψ₀ 1) hψ₀
  · have hq0 : q ≠ 0 := NeZero.ne q
    have hlogpos : 0 < Real.log (q : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    -- the (finitely many) admissible characters: non-principal and outside both pairs
    set charsCand : Finset (DirichletCharacter ℂ q) :=
      Finset.univ.filter
        (fun χ => χ ≠ 1 ∧ χ ≠ χ₁ ∧ χ ≠ χ₁⁻¹ ∧ χ ≠ χ₂ ∧ χ ≠ χ₂⁻¹) with hchars
    have hmemchars : ∀ χ : DirichletCharacter ℂ q,
        χ ∈ charsCand ↔ χ ≠ 1 ∧ χ ≠ χ₁ ∧ χ ≠ χ₁⁻¹ ∧ χ ≠ χ₂ ∧ χ ≠ χ₂⁻¹ := by
      intro χ
      simp only [hchars, Finset.mem_filter, Finset.mem_univ, true_and]
    -- for each character, the finite set of its zeros in the box `Re ≥ Re ρ`, `|Im| ≤ H`
    set zeroCand : DirichletCharacter ℂ q → Finset ℂ := fun χ =>
      (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ ρ.re H).toFinset with hzeros
    have hmemzeros : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ),
        u ∈ zeroCand χ ↔
          Work.LinnikContract.zeroMult χ u ≠ 0 ∧ ρ.re ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ H := by
      intro χ u
      rw [hzeros]
      exact (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ ρ.re H).mem_toFinset
    -- the finite set of admissible pairs `(χ, ρ')`
    set pairCand : Finset (DirichletCharacter ℂ q × ℂ) :=
      charsCand.biUnion (fun χ => (zeroCand χ).image (fun u => (χ, u))) with hpair
    have hmemP : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ),
        (χ, u) ∈ pairCand ↔ χ ∈ charsCand ∧ u ∈ zeroCand χ := by
      intro χ u
      rw [hpair, Finset.mem_biUnion]
      constructor
      · rintro ⟨χ', hχ', huv⟩
        rw [Finset.mem_image] at huv
        obtain ⟨u', hu', hEq⟩ := huv
        simp only [Prod.mk.injEq] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        exact ⟨hχ', hu'⟩
      · rintro ⟨hχ, hu⟩
        exact ⟨χ, hχ, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
    -- the witness `(ψ₀, ρ)` is admissible
    have hmem_ne : (ψ₀, ρ) ∈ pairCand := by
      rw [hmemP]
      refine ⟨(hmemchars ψ₀).mpr ⟨hψ₀, hψ₀₁, hψ₀₁', hψ₀₂, hψ₀₂'⟩, ?_⟩
      exact (hmemzeros ψ₀ ρ).mpr
        ⟨hρ, le_rfl, le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one ψ₀ hρ), hρim⟩
    -- pick a minimiser of `λ` over the admissible pairs
    obtain ⟨⟨χ₃, ρ₃⟩, hρ₃mem, hmin⟩ :=
      Finset.exists_min_image pairCand
        (fun p : DirichletCharacter ℂ q × ℂ => Work.LinnikContract.lamOf q p.2)
        ⟨(ψ₀, ρ), hmem_ne⟩
    obtain ⟨hχ₃chars, hρ₃S⟩ := (hmemP χ₃ ρ₃).mp hρ₃mem
    obtain ⟨hχ₃1, hχ₃χ₁, hχ₃χ₁inv, hχ₃χ₂, hχ₃χ₂inv⟩ := (hmemchars χ₃).mp hχ₃chars
    obtain ⟨hzm₃, -, -, him₃⟩ := (hmemzeros χ₃ ρ₃).mp hρ₃S
    refine ⟨χ₃, ρ₃, hχ₃1, hχ₃χ₁, hχ₃χ₁inv, hχ₃χ₂, hχ₃χ₂inv, hzm₃, him₃, ?_, ?_⟩
    · exact hmin (ψ₀, ρ) hmem_ne
    · -- minimality among *all* admissible pairs
      intro ψ u hψ hzm him hψχ₁ hψχ₁inv hψχ₂ hψχ₂inv
      rcases lt_or_ge (Work.LinnikContract.lamOf q ρ) (Work.LinnikContract.lamOf q u) with hlt | hle
      · exact le_trans (hmin (ψ₀, ρ) hmem_ne) (le_of_lt hlt)
      · -- `λ u ≤ λ ρ` means `Re u ≥ Re ρ`, so `u` is in the restricted candidate set
        have hre : ρ.re ≤ u.re := by
          have h1 : (1 - u.re) * Real.log (q : ℝ) ≤ (1 - ρ.re) * Real.log (q : ℝ) := hle
          have h2 : 1 - u.re ≤ 1 - ρ.re := (mul_le_mul_iff_left₀ hlogpos).mp h1
          linarith
        have huS : u ∈ zeroCand ψ := (hmemzeros ψ u).mpr
          ⟨hzm, hre, le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one ψ hzm), him⟩
        exact hmin (ψ, u)
          ((hmemP ψ u).mpr
            ⟨(hmemchars ψ).mpr ⟨hψ, hψχ₁, hψχ₁inv, hψχ₂, hψχ₂inv⟩, huS⟩)

end Work.ZeroFreeTables
