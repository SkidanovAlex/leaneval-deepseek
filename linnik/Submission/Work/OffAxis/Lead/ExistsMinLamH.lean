/-
# OffAxis/Lead/ExistsMinLamH

**A `λ`-minimal zero at height `L` outside a set of characters.**  This is the height-`L`
(and `IsZAt`-based) version of `Work.ZeroFreeTables.OffAxis.exists_min_lam_avoiding`: the
candidate set is the finite `zeroSetH L χ`, so a `λ`-minimum exists.

It is the selection step of HB's §6 argument in `RectLam3` (choose `χ₂` realising the minimum of
`λ` outside the conjugate pair `{χ₁^{±1}}`, then `χ₃` outside `{χ₁^{±1}, χ₂^{±1}}`).  The proof
is that of `Work.ZeroFreeTables.OffAxis.exists_min_lam_avoiding_z4` of `RectC_Z4`, reproduced
here so that the selection step does not depend on the (large) `RectC_Z4` assembly.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.LinnikContract2.NumZero.exists_wideMin

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.OffAxis.Lead

open Work.ZeroFreeTables

/-- **A `λ`-minimal zero at height `L` outside a set of characters.** -/
theorem exists_min_lam_avoiding_H {q : ℕ} [NeZero q] (L : ℝ) (S : Set (DirichletCharacter ℂ q))
    (hne : ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZAt L χ ρ ∧ χ ∉ S) :
    ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZAt L χ ρ ∧ χ ∉ S ∧
      ∀ (χ' : DirichletCharacter ℂ q) (ρ' : ℂ), IsZAt L χ' ρ' → χ' ∉ S →
        Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamOf q ρ' := by
  classical
  set cands : Finset (DirichletCharacter ℂ q × ℂ) :=
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ∉ S)).biUnion
      (fun χ => (Work.LinnikContract2.NumZero.zeroSetH L χ).image (fun ρ => (χ, ρ))) with hcands
  have hmem : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      (χ, ρ) ∈ cands ↔ χ ∉ S ∧ IsZAt L χ ρ := by
    intro χ ρ
    rw [hcands, Finset.mem_biUnion]
    constructor
    · rintro ⟨χ', hχ', hmem'⟩
      rw [Finset.mem_filter] at hχ'
      obtain ⟨-, hχ'S⟩ := hχ'
      rw [Finset.mem_image] at hmem'
      obtain ⟨ρ', hρ', heq⟩ := hmem'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨hχ'S, Work.LinnikContract2.NumZero.mem_zeroSetH.mp hρ'⟩
    · rintro ⟨hχS, hZ⟩
      refine ⟨χ, ?_, ?_⟩
      · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ χ, hχS⟩
      · rw [Finset.mem_image]
        exact ⟨ρ, Work.LinnikContract2.NumZero.mem_zeroSetH.mpr hZ, rfl⟩
  have hne' : cands.Nonempty := by
    obtain ⟨χ₀, ρ₀, hZ, hS⟩ := hne
    exact ⟨(χ₀, ρ₀), (hmem χ₀ ρ₀).mpr ⟨hS, hZ⟩⟩
  obtain ⟨p, hp_mem, hp_min⟩ := Finset.exists_min_image cands
    (fun p : DirichletCharacter ℂ q × ℂ => Work.LinnikContract.lamOf q p.2) hne'
  obtain ⟨hpS, hpZ⟩ := (hmem p.1 p.2).mp hp_mem
  exact ⟨p.1, p.2, hpZ, hpS, fun χ' ρ' hZ' hS' =>
    hp_min (χ', ρ') ((hmem χ' ρ').mpr ⟨hS', hZ'⟩)⟩

end Work.ZeroFreeTables.OffAxis.Lead
