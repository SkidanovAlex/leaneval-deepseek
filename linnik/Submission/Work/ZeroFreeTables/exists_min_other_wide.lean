import Mathlib
import Submission.Work.LinnikAreas.exists_minLam_zero
import Submission.Work.ZeroFreeTables.HBTable7_defs

namespace Work.ZeroFreeTables

/-- **Existence of a global `λ`-minimiser among the "other" characters.**

Given a non-principal character `ψ₀` distinct from `χ₁^{±1}` with a zero `ρ` of `|Im| ≤ H`, there
is a pair `(χ₂, ρ₂)` — `χ₂` non-principal and distinct from `χ₁^{±1}`, `ρ₂` a zero of `χ₂` with
`|Im ρ₂| ≤ H` — whose `λ`-value is minimal among *all* such pairs, and in particular `≤ λ(ρ)`.

The candidate set is finite: there are finitely many characters mod `q`, and for each of them the
zeros with `λ ≤ λ(ρ)` (i.e. `Re ≥ Re ρ`) lie in the compact box `|Im| ≤ H`, which contains only
finitely many zeros of the completed `L`-function
(`Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box`).  A minimiser of this restricted set is
automatically a minimiser of the whole set, since any pair with strictly smaller `λ` would already
satisfy `λ ≤ λ(ρ)` and hence lie in the restricted set. -/
theorem exists_min_other_wide {q : ℕ} [NeZero q] (H : ℝ) (hH : 0 ≤ H)
    (χ₁ : DirichletCharacter ℂ q) (ψ₀ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hψ₀ : ψ₀ ≠ 1) (hψ₀₁ : ψ₀ ≠ χ₁) (hψ₀₂ : ψ₀ ≠ χ₁⁻¹)
    (hρ : Work.LinnikContract.zeroMult ψ₀ ρ ≠ 0) (hρim : |ρ.im| ≤ H) :
    ∃ (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ),
      χ₂ ≠ 1 ∧ χ₂ ≠ χ₁ ∧ χ₂ ≠ χ₁⁻¹ ∧ Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 ∧ |ρ₂.im| ≤ H ∧
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ ∧
      ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
        |u.im| ≤ H → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ → Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u := by
  classical
  -- At level `1` there is only one Dirichlet character, contradicting `ψ₀ ≠ 1`.
  by_cases hq1 : q = 1
  · subst hq1
    exact absurd (Subsingleton.elim ψ₀ 1) hψ₀
  · have hq2 : 2 ≤ q := by
      have hq0 : q ≠ 0 := NeZero.ne q
      omega
    have hlogpos : 0 < Real.log (q : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    -- the (finitely many) admissible characters
    set charsCand : Finset (DirichletCharacter ℂ q) :=
      Finset.univ.filter (fun χ => χ ≠ 1 ∧ χ ≠ χ₁ ∧ χ ≠ χ₁⁻¹) with hchars
    have hmemchars : ∀ χ : DirichletCharacter ℂ q,
        χ ∈ charsCand ↔ χ ≠ 1 ∧ χ ≠ χ₁ ∧ χ ≠ χ₁⁻¹ := by
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
      refine ⟨(hmemchars ψ₀).mpr ⟨hψ₀, hψ₀₁, hψ₀₂⟩, ?_⟩
      exact (hmemzeros ψ₀ ρ).mpr
        ⟨hρ, le_rfl, le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one ψ₀ hρ), hρim⟩
    -- pick a minimiser of `λ` over the admissible pairs
    obtain ⟨⟨χ₂, ρ₂⟩, hρ₂mem, hmin⟩ :=
      Finset.exists_min_image pairCand
        (fun p : DirichletCharacter ℂ q × ℂ => Work.LinnikContract.lamOf q p.2) ⟨(ψ₀, ρ), hmem_ne⟩
    obtain ⟨hχ₂chars, hρ₂S⟩ := (hmemP χ₂ ρ₂).mp hρ₂mem
    obtain ⟨hχ₂1, hχ₂χ₁, hχ₂χ₁inv⟩ := (hmemchars χ₂).mp hχ₂chars
    obtain ⟨hzm₂, -, -, him₂⟩ := (hmemzeros χ₂ ρ₂).mp hρ₂S
    refine ⟨χ₂, ρ₂, hχ₂1, hχ₂χ₁, hχ₂χ₁inv, hzm₂, him₂, ?_, ?_⟩
    · exact hmin (ψ₀, ρ) hmem_ne
    · -- minimality among *all* admissible pairs
      intro ψ u hψ hzm him hψχ₁ hψχ₁inv
      rcases lt_or_ge (Work.LinnikContract.lamOf q ρ) (Work.LinnikContract.lamOf q u) with hlt | hle
      · exact le_trans (hmin (ψ₀, ρ) hmem_ne) (le_of_lt hlt)
      · -- `λ u ≤ λ ρ` means `Re u ≥ Re ρ`, so `u` is in the restricted candidate set
        have hre : ρ.re ≤ u.re := by
          have h1 : (1 - u.re) * Real.log (q : ℝ) ≤ (1 - ρ.re) * Real.log (q : ℝ) := hle
          have h2 : 1 - u.re ≤ 1 - ρ.re := (mul_le_mul_iff_left₀ hlogpos).mp h1
          linarith
        have huS : u ∈ zeroCand ψ := (hmemzeros ψ u).mpr
          ⟨hzm, hre, le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one ψ hzm), him⟩
        exact hmin (ψ, u) ((hmemP ψ u).mpr ⟨(hmemchars ψ).mpr ⟨hψ, hψχ₁, hψχ₁inv⟩, huS⟩)

end Work.ZeroFreeTables
