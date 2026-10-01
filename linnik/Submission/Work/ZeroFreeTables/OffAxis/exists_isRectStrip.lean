import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.LinnikContract2.NumZero.exists_wideMin

namespace Work.ZeroFreeTables.OffAxis

theorem exists_isRectStrip {q : ℕ} [NeZero q] {L : ℝ} (hL : 50 ≤ L)
    (hstrip : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ),
      Work.ZeroFreeTables.IsZAt (10 * L) χ u → L < |u.im| → 2 < Work.LinnikContract.lamOf q u)
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (hm : Work.LinnikContract2.IsMin1 χ₁ ρ₁) :
    ∃ (χ' : DirichletCharacter ℂ q) (ρ' : ℂ),
      Work.ZeroFreeTables.IsRectStrip L χ' ρ' ∧
        Work.LinnikContract.lamOf q ρ' ≤ Work.LinnikContract.lamOf q ρ₁ := by
  -- `ρ₁` lies in the height-`L` region (`IsZAt L` is `IsZH L`).
  have hmem : Work.LinnikContract2.IsZH L χ₁ ρ₁ :=
    Work.LinnikContract2.isZH_mono hL hm.1
  -- a `λ`-minimal pair over the height-`L` region exists
  obtain ⟨χ', ρ', hZ', hmin'⟩ :=
    Work.LinnikContract2.NumZero.exists_wideMin (H := L) ⟨χ₁, ρ₁, hmem⟩
  refine ⟨χ', ρ', ⟨hZ', ?_, hstrip⟩, hmin' χ₁ ρ₁ hmem⟩
  -- minimality over `IsZAt L` (definitionally the same region as `IsZH L`)
  intro χ u hu
  exact hmin' χ u hu

end Work.ZeroFreeTables.OffAxis
