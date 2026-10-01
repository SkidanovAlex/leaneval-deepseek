/-
# `Work.A7.exists_isMin1` — HB §15 step 2: existence of an `IsMin1` pair

If some character `χ mod q` has a zero `ρ` in HB's working region `IsZ` (`χ ≠ 1`,
`zeroMult χ ρ ≠ 0`, `|Im ρ| ≤ 1`), then there is a pair `(χ₁, ρ₁)` for which `λ = (1 - Re)·log q`
is *minimal* among all such pairs (`IsMin1`).

The mathematical content is that the candidate set is finite:

* a zero in the working region is a zero of `L(·, χ*)` in the critical strip
  (`Commons.NumberTheory.Linnik.completedL_zero_strip` + the factorisation of `Λ` by the
  archimedean factor), and
* for each `χ ≠ 1` the zeros of `L(·, χ*)` in the critical strip with `|Im| ≤ 1` form a finite set
  (`Commons.NumberTheory.DirichletCharacter.lFunction_zeroSet_box_finite`).

The characters of level `q` form a finite type, so the union of these finite sets — the `Finset`
`zeroSet` assembled below — is finite and non-empty, and `Finset.exists_min_image` extracts a
minimal element of `λ`.
-/
import Mathlib
import Submission.Work.LinnikAreas.A7.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_zeroSet_box_finite

set_option linter.style.haveILetI false

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- The primitive character inducing a non-trivial `χ` is non-trivial. -/
lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h1
  have h := DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h
  exact hχ h.symm

/-- A zero in HB's working region is a zero of `L(·, χ*)` in the critical strip. -/
lemma isZ_LFunction_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    {ρ : ℂ} (h : Work.LinnikContract.IsZ χ ρ) :
    DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := by
  obtain ⟨hχ, hzm, -⟩ := h
  have hψ1 : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one hχ
  have hψprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hΛ : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 := by
    have h' := apply_eq_zero_of_analyticOrderNatAt_ne_zero hzm
    simpa [Work.LinnikContract.zeroMult] using h'
  have hstrip :=
    Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hψ1 hψprim hΛ
  have hρ0 : ρ ≠ 0 := by intro hh; rw [hh] at hstrip; simp at hstrip
  refine ⟨?_, hstrip.1, hstrip.2⟩
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.primitiveCharacter ρ (Or.inl hρ0),
    hΛ, zero_div]

/-- The finite candidate set of `ρ` for a character `χ mod q`: for `χ ≠ 1` the zeros of `L(·, χ*)`
in the critical strip with `|Im ρ| ≤ 1` (which by `mem_zeroSet` is exactly `{ρ | IsZ χ ρ}`), and
`∅` for the principal character. -/
def zeroSet {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Finset ℂ :=
  if h : χ = 1 then ∅
  else
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    (Commons.NumberTheory.DirichletCharacter.lFunction_zeroSet_box_finite χ.primitiveCharacter
      (primitiveCharacter_ne_one h) (DirichletCharacter.primitiveCharacter_isPrimitive χ)
      1).toFinset.filter (fun ρ => Work.LinnikContract.zeroMult χ ρ ≠ 0)

/-- Characterisation of the candidate set: `ρ ∈ zeroSet χ` iff `(χ, ρ)` lies in HB's working
region. -/
lemma mem_zeroSet {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ} :
    ρ ∈ zeroSet χ ↔ χ ≠ 1 ∧ Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 := by
  constructor
  · intro hmem
    rw [zeroSet] at hmem
    split at hmem
    · simp at hmem
    · rename_i hne
      rw [Finset.mem_filter] at hmem
      obtain ⟨hmem1, hzm⟩ := hmem
      rw [Set.Finite.mem_toFinset] at hmem1
      exact ⟨hne, hzm, hmem1.2.2.2⟩
  · rintro ⟨hne, hzm, him⟩
    rw [zeroSet]
    rw [dif_neg hne, Finset.mem_filter]
    refine ⟨?_, hzm⟩
    rw [Set.Finite.mem_toFinset]
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    obtain ⟨hL, hre0, hre1⟩ := isZ_LFunction_zero χ (ρ := ρ) ⟨hne, hzm, him⟩
    exact ⟨hL, hre0, hre1, him⟩

theorem exists_isMin1 {q : ℕ} [NeZero q]
    (h : ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ) :
    ∃ (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), Work.LinnikContract.IsMin1 χ₁ ρ₁ := by
  classical
  -- the finite set of pairs `(χ, ρ)` in HB's working region
  let cands : Finset (DirichletCharacter ℂ q × ℂ) :=
    Finset.univ.biUnion (fun χ => (zeroSet χ).image (fun ρ => (χ, ρ)))
  have hne : cands.Nonempty := by
    obtain ⟨χ₀, ρ₀, hZ⟩ := h
    refine ⟨(χ₀, ρ₀), ?_⟩
    simp only [cands, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨χ₀, ρ₀, mem_zeroSet.mpr ⟨hZ.1, hZ.2.1, hZ.2.2⟩, rfl⟩
  obtain ⟨p, hp_mem, hp_min⟩ := Finset.exists_min_image cands
    (fun p => Work.LinnikContract.lamOf q p.2) hne
  refine ⟨p.1, p.2, ?_, ?_⟩
  · -- the minimiser lies in the working region
    simp only [cands, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hp_mem
    obtain ⟨χ, ρ, hρ, hp_eq⟩ := hp_mem
    have hsub : p = (χ, ρ) := hp_eq.symm
    subst hsub
    obtain ⟨hne1, hzm, him⟩ := mem_zeroSet.mp hρ
    exact ⟨hne1, hzm, him⟩
  · -- minimality of `λ`
    intro χ ρ hZ
    have hmem : (χ, ρ) ∈ cands := by
      simp only [cands, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨χ, ρ, mem_zeroSet.mpr ⟨hZ.1, hZ.2.1, hZ.2.2⟩, rfl⟩
    exact hp_min (χ, ρ) hmem

end

end Work.A7
