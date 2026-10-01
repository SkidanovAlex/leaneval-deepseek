/-
# `Work.A7.lamChar_api` — the API of the invariant `λ^{(χ)} = lamChar χ`

The object `Work.LinnikContract.lamChar χ = sInf {λ(ρ) | ρ a zero of χ in HB's working region}`
(HB §6's `λ₀`, the *smallest* zero-parameter attached to `χ`) is used throughout HB §§11, 13, 15 as
the weight `w(λ^{(χ)})` of a character.  This file collects the elementary order-theoretic API:

* `lamChar χ` is a lower bound for the `λ`-value of every zero of `χ` in the region (`IsZ`);
* `lamChar χ ≥ 0` (with the convention `sInf ∅ = 0` when `χ` carries no zero at all);
* if `χ` carries a zero, `lamChar χ` is *attained*, and any `t ≥ lamChar χ` bounds some zero of `χ`;
* consequently, for a pair `(χ₁, ρ₁)` realising the minimal `λ` over *all* characters
  (`IsMin1`), the value `λ(ρ₁)` is a lower bound for every `lamChar χ` and for every `λ(ρ)`.

The only analytic input is `isZ_lambda_nonneg`: a zero in the working region of a non-principal
character of level `q ≥ 2` lies in the critical strip, hence has `λ = (1 - Re ρ) log q ≥ 0`.
The attainment claim uses the finiteness of the set of such zeros (`Work.A7.zeroSet`,
`Work.A7.mem_zeroSet`, `Work.A7.exists_isMin1`).

Everything here is sorry-free.
-/
import Mathlib
import Submission.Work.LinnikAreas.A7.Defs
import Submission.Work.A7.exists_isMin1
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

set_option linter.style.haveILetI false

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- The set of `λ`-values of the zeros of `χ` in HB's working region — the set whose `sInf` is
`lamChar χ`. -/
def lamSet {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Set ℝ :=
  {x : ℝ | ∃ ρ, Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ = x}

lemma lamChar_eq_sInf_lamSet {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Work.LinnikContract.lamChar χ = sInf (lamSet χ) := rfl

/-- `0` is a lower bound for the `λ`-values of the zeros of `χ` in the working region: they lie in
the critical strip, so `1 - Re ρ > 0` and `log q > 0` for `q ≥ 2`. -/
lemma lamSet_bddBelow {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) :
    BddBelow (lamSet χ) :=
  ⟨0, by
    rintro x ⟨ρ, hρ, hx⟩
    rw [← hx]
    exact Work.LinnikContract.API.isZ_lambda_nonneg hq hρ⟩

/-- `lamChar χ` is a lower bound for the `λ`-value of any zero of `χ` in the working region. -/
lemma lamChar_le_lamOf {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.LinnikContract.IsZ χ ρ) :
    Work.LinnikContract.lamChar χ ≤ Work.LinnikContract.lamOf q ρ := by
  rw [Work.LinnikContract.lamChar]
  exact csInf_le (lamSet_bddBelow hq χ) ⟨ρ, h, rfl⟩

/-- `lamChar χ ≥ 0`, with the convention `sInf ∅ = 0` when `χ` has no zero in the working region. -/
lemma lamChar_nonneg_of_hq {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) :
    0 ≤ Work.LinnikContract.lamChar χ := by
  by_cases h : ∃ ρ, Work.LinnikContract.IsZ χ ρ
  · obtain ⟨ρ, hρ⟩ := h
    rw [Work.LinnikContract.lamChar]
    exact le_csInf ⟨Work.LinnikContract.lamOf q ρ, ρ, hρ, rfl⟩
      (fun x ⟨ρ', hρ', hx⟩ => by
        rw [← hx]
        exact Work.LinnikContract.API.isZ_lambda_nonneg hq hρ')
  · have h' : ∀ ρ, ¬ Work.LinnikContract.IsZ χ ρ := fun ρ hρ => h ⟨ρ, hρ⟩
    have hemp : {x : ℝ | ∃ ρ, Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ = x} = ∅ := by
      ext x
      constructor
      · rintro ⟨ρ, hρ, -⟩
        exact absurd hρ (h' ρ)
      · intro hx
        exact absurd hx (Set.notMem_empty x)
    rw [Work.LinnikContract.lamChar, hemp, Real.sInf_empty]

/-- **Attainment.**  If `χ` has at least one zero in the working region then `lamChar χ` is the
`λ`-value of an actual zero of `χ`: the set of such zeros is finite (`Work.A7.zeroSet`), so the
`sInf` is a minimum. -/
lemma exists_lamChar_eq_lamOf {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (h : ∃ ρ, Work.LinnikContract.IsZ χ ρ) :
    ∃ ρ, Work.LinnikContract.IsZ χ ρ ∧
      Work.LinnikContract.lamChar χ = Work.LinnikContract.lamOf q ρ := by
  obtain ⟨ρ, hρ⟩ := h
  have hne : (zeroSet χ).Nonempty := ⟨ρ, mem_zeroSet.mpr ⟨hρ.1, hρ.2.1, hρ.2.2⟩⟩
  obtain ⟨ρ₁, hρ₁, hmin⟩ :=
    Finset.exists_min_image (zeroSet χ) (fun ρ => Work.LinnikContract.lamOf q ρ) hne
  have hZ : Work.LinnikContract.IsZ χ ρ₁ := mem_zeroSet.mp hρ₁
  refine ⟨ρ₁, hZ, ?_⟩
  have hlb : ∀ x ∈ lamSet χ, Work.LinnikContract.lamOf q ρ₁ ≤ x := by
    rintro x ⟨ρ', hρ', rfl⟩
    exact hmin ρ' (mem_zeroSet.mpr ⟨hρ'.1, hρ'.2.1, hρ'.2.2⟩)
  rw [Work.LinnikContract.lamChar]
  exact le_antisymm (csInf_le ⟨Work.LinnikContract.lamOf q ρ₁, hlb⟩ ⟨ρ₁, hZ, rfl⟩)
    (le_csInf ⟨Work.LinnikContract.lamOf q ρ₁, ρ₁, hZ, rfl⟩ hlb)

/-- If `(χ₁, ρ₁)` realises the minimal zero-parameter over all characters (`IsMin1`), then `λ(ρ₁)`
is a lower bound for `lamChar χ` for every `χ`; this needs the attainment of `lamChar χ`. -/
lemma isMin1_lamOf_le_lamChar {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) {χ : DirichletCharacter ℂ q}
    (h : ∃ ρ, Work.LinnikContract.IsZ χ ρ) :
    Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamChar χ := by
  obtain ⟨ρ, hρ⟩ := h
  rw [Work.LinnikContract.lamChar]
  exact le_csInf ⟨Work.LinnikContract.lamOf q ρ, ρ, hρ, rfl⟩
    (fun x ⟨ρ', hρ', hx⟩ => by
      rw [← hx]
      exact hmin.2 χ ρ' hρ')

theorem lamChar_api :
    (∀ {q : ℕ} [NeZero q], 2 ≤ q → ∀ {χ : DirichletCharacter ℂ q} {ρ : ℂ},
      Work.LinnikContract.IsZ χ ρ → Work.LinnikContract.lamChar χ ≤ Work.LinnikContract.lamOf q ρ) ∧
    (∀ {q : ℕ} [NeZero q], 2 ≤ q → ∀ (χ : DirichletCharacter ℂ q),
      0 ≤ Work.LinnikContract.lamChar χ) ∧
    (∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {t : ℝ},
      (∃ ρ : ℂ, Work.LinnikContract.IsZ χ ρ) → Work.LinnikContract.lamChar χ ≤ t →
      ∃ ρ : ℂ, Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ t) ∧
    (∀ {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ},
      Work.LinnikContract.IsMin1 χ₁ ρ₁ → ∀ {χ : DirichletCharacter ℂ q},
        (∃ ρ : ℂ, Work.LinnikContract.IsZ χ ρ) →
        Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamChar χ) ∧
    (∀ {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ},
      Work.LinnikContract.IsMin1 χ₁ ρ₁ → ∀ {χ : DirichletCharacter ℂ q} {ρ : ℂ},
        Work.LinnikContract.IsZ χ ρ → Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q _ hq χ ρ hZ
    exact lamChar_le_lamOf hq hZ
  · intro q _ hq χ
    exact lamChar_nonneg_of_hq hq χ
  · intro q _ χ t hne hle
    obtain ⟨ρ, hZ, heq⟩ := exists_lamChar_eq_lamOf hne
    exact ⟨ρ, hZ, by rw [← heq]; exact hle⟩
  · intro q _ χ₁ ρ₁ hmin χ hne
    exact isMin1_lamOf_le_lamChar hmin hne
  · intro q _ χ₁ ρ₁ hmin χ ρ hZ
    exact hmin.2 χ ρ hZ

end

end Work.A7
