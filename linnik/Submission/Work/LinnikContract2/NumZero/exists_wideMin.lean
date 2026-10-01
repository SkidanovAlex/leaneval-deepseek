/-
# `Work.LinnikContract2.NumZero.exists_wideMin`

If some character `χ mod q` has a zero `ρ` in HB's region at *height* `H`
(`IsZH H χ ρ`, i.e. `χ ≠ 1`, `zeroMult χ ρ ≠ 0`, `|Im ρ| ≤ H`), then there is a pair
`(χ₁, ρ₁)` in that region for which `λ = (1 - Re)·log q` is *minimal* among all such pairs:

    ∃ χ₁ ρ₁, IsZH H χ₁ ρ₁ ∧ ∀ χ u, IsZH H χ u → lamOf q ρ₁ ≤ lamOf q u.

The mathematical content is exactly as in `Work.A7.exists_isMin1` (the `H = 1` case): the
candidate set is finite, because

* a zero in the region is a zero of `L(·, χ*)` in the critical strip
  (`Commons.NumberTheory.Linnik.completedL_zero_strip` + the factorisation of `Λ` by the
  archimedean factor), and
* for each `χ ≠ 1` the zeros of `L(·, χ*)` in the critical strip with `|Im| ≤ H` form a finite
  set (`Commons.NumberTheory.DirichletCharacter.lFunction_zeroSet_box_finite`).

The characters of level `q` form a finite type, so the union of these finite sets is finite and
non-empty, and `Finset.exists_min_image` extracts a minimal element of `λ`.  Everything below is
the `H`-indexed version of that argument; nothing uses `H = 1`.
-/
import Mathlib
import Submission.Work.LinnikContract2.Defs
import Submission.Work.LinnikContract2.API
import Submission.Work.A7.exists_isMin1
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_zeroSet_box_finite

set_option linter.style.haveILetI false

namespace Work.LinnikContract2.NumZero

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

/-- A zero in HB's region at height `H` is a zero of `L(·, χ*)` in the critical strip. -/
lemma isZH_LFunction_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    {H : ℝ} {ρ : ℂ} (h : IsZH H χ ρ) :
    DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := by
  obtain ⟨hχ, hzm, -⟩ := h
  have hψ1 : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one hχ
  have hψprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hΛ : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 := by
    have h' := apply_eq_zero_of_analyticOrderNatAt_ne_zero hzm
    simpa [zeroMult] using h'
  have hstrip :=
    Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hψ1 hψprim hΛ
  have hρ0 : ρ ≠ 0 := by intro hh; rw [hh] at hstrip; simp at hstrip
  refine ⟨?_, hstrip.1, hstrip.2⟩
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.primitiveCharacter ρ
    (Or.inl hρ0), hΛ, zero_div]

/-- The finite candidate set of `ρ` for a character `χ mod q` at height `H`: for `χ ≠ 1` the
zeros of `L(·, χ*)` in the critical strip with `|Im ρ| ≤ H` (which by `mem_zeroSetH` is exactly
`{ρ | IsZH H χ ρ}`), and `∅` for the principal character. -/
def zeroSetH {q : ℕ} [NeZero q] (H : ℝ) (χ : DirichletCharacter ℂ q) : Finset ℂ :=
  if h : χ = 1 then ∅
  else
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    (Commons.NumberTheory.DirichletCharacter.lFunction_zeroSet_box_finite χ.primitiveCharacter
      (primitiveCharacter_ne_one h) (DirichletCharacter.primitiveCharacter_isPrimitive χ)
      H).toFinset.filter (fun ρ => zeroMult χ ρ ≠ 0)

/-- Characterisation of the candidate set: `ρ ∈ zeroSetH H χ` iff `(χ, ρ)` lies in HB's region
at height `H`. -/
lemma mem_zeroSetH {q : ℕ} [NeZero q] {H : ℝ} {χ : DirichletCharacter ℂ q} {ρ : ℂ} :
    ρ ∈ zeroSetH H χ ↔ χ ≠ 1 ∧ zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ H := by
  constructor
  · intro hmem
    rw [zeroSetH] at hmem
    split at hmem
    · simp at hmem
    · rename_i hne
      rw [Finset.mem_filter] at hmem
      obtain ⟨hmem1, hzm⟩ := hmem
      rw [Set.Finite.mem_toFinset] at hmem1
      exact ⟨hne, hzm, hmem1.2.2.2⟩
  · rintro ⟨hne, hzm, him⟩
    rw [zeroSetH]
    rw [dif_neg hne, Finset.mem_filter]
    refine ⟨?_, hzm⟩
    rw [Set.Finite.mem_toFinset]
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    obtain ⟨hL, hre0, hre1⟩ := isZH_LFunction_zero χ (H := H) (ρ := ρ) ⟨hne, hzm, him⟩
    exact ⟨hL, hre0, hre1, him⟩

/-- **Existence of the wide minimiser.**  If any pair lies in HB's region at height `H`, then a
`λ`-minimal such pair exists. -/
theorem exists_wideMin {q : ℕ} [NeZero q] {H : ℝ}
    (h : ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZH H χ ρ) :
    ∃ (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsZH H χ₁ ρ₁ ∧
        ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZH H χ u → lamOf q ρ₁ ≤ lamOf q u := by
  classical
  -- the finite set of pairs `(χ, ρ)` in HB's region at height `H`
  let cands : Finset (DirichletCharacter ℂ q × ℂ) :=
    Finset.univ.biUnion (fun χ => (zeroSetH H χ).image (fun ρ => (χ, ρ)))
  have hne : cands.Nonempty := by
    obtain ⟨χ₀, ρ₀, hZ⟩ := h
    refine ⟨(χ₀, ρ₀), ?_⟩
    simp only [cands, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨χ₀, ρ₀, mem_zeroSetH.mpr ⟨hZ.1, hZ.2.1, hZ.2.2⟩, rfl⟩
  obtain ⟨p, hp_mem, hp_min⟩ := Finset.exists_min_image cands
    (fun p => lamOf q p.2) hne
  refine ⟨p.1, p.2, ?_, ?_⟩
  · -- the minimiser lies in the region
    simp only [cands, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hp_mem
    obtain ⟨χ, ρ, hρ, hp_eq⟩ := hp_mem
    have hsub : p = (χ, ρ) := hp_eq.symm
    subst hsub
    obtain ⟨hne1, hzm, him⟩ := mem_zeroSetH.mp hρ
    exact ⟨hne1, hzm, him⟩
  · -- minimality of `λ`
    intro χ ρ hZ
    have hmem : (χ, ρ) ∈ cands := by
      simp only [cands, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨χ, ρ, mem_zeroSetH.mpr ⟨hZ.1, hZ.2.1, hZ.2.2⟩, rfl⟩
    exact hp_min (χ, ρ) hmem

end

end Work.LinnikContract2.NumZero
