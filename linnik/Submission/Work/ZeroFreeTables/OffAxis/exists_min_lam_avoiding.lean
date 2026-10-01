import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.LinnikContract2.NumZero.exists_wideMin

namespace Work.ZeroFreeTables.OffAxis

/-- **A `λ`-minimal zero outside an excluded set of characters.**  Given a *non-empty* family of
working-region zeros (`IsZ χ ρ`: `χ ≠ 1`, `ρ` a zero of multiplicity `≥ 1` of `L(·,χ)`, and
`|Im ρ| ≤ 1`) whose characters avoid a set `S ⊆ DirichletCharacter ℂ q`, there is such a pair
`(χ, ρ)` with `χ ∉ S` at which `λ = (1 - Re ·) log q` is minimal.  (The candidate pairs form a
finite set: for each character `χ ≠ 1` the zeros of `L(·,χ*)` in the critical strip with
`|Im| ≤ 1` are finite — `Work.LinnikContract2.NumZero.zeroSetH` /
`mem_zeroSetH` — and the characters of level `q` are finitely many.) -/
theorem exists_min_lam_avoiding {q : ℕ} [NeZero q] (S : Set (DirichletCharacter ℂ q))
    (hne : ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ ∧ χ ∉ S) :
    ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ ∧ χ ∉ S ∧
      ∀ (χ' : DirichletCharacter ℂ q) (ρ' : ℂ), Work.LinnikContract.IsZ χ' ρ' → χ' ∉ S →
        Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamOf q ρ' := by
  classical
  -- The finite candidate set of admissible pairs: characters outside `S`, with their working-region
  -- zeros (the finite set `zeroSetH 1 χ`).
  set cands : Finset (DirichletCharacter ℂ q × ℂ) :=
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ∉ S)).biUnion
      (fun χ => (Work.LinnikContract2.NumZero.zeroSetH 1 χ).image (fun ρ => (χ, ρ)))
    with hcands
  have hmem : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      (χ, ρ) ∈ cands ↔ χ ∉ S ∧ Work.LinnikContract.IsZ χ ρ := by
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
      exact ⟨hχ'S, Work.LinnikContract2.IsZH_one_iff_IsZ.mp
        (Work.LinnikContract2.NumZero.mem_zeroSetH.mp hρ')⟩
    · rintro ⟨hχS, hZ⟩
      refine ⟨χ, ?_, ?_⟩
      · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ χ, hχS⟩
      · rw [Finset.mem_image]
        exact ⟨ρ, Work.LinnikContract2.NumZero.mem_zeroSetH.mpr
          (Work.LinnikContract2.IsZH_one_iff_IsZ.mpr hZ), rfl⟩
  have hne' : cands.Nonempty := by
    obtain ⟨χ₀, ρ₀, hZ, hS⟩ := hne
    exact ⟨(χ₀, ρ₀), (hmem χ₀ ρ₀).mpr ⟨hS, hZ⟩⟩
  obtain ⟨p, hp_mem, hp_min⟩ := Finset.exists_min_image cands
    (fun p : DirichletCharacter ℂ q × ℂ => Work.LinnikContract.lamOf q p.2) hne'
  obtain ⟨hpS, hpZ⟩ := (hmem p.1 p.2).mp hp_mem
  exact ⟨p.1, p.2, hpZ, hpS, fun χ' ρ' hZ' hS' =>
    hp_min (χ', ρ') ((hmem χ' ρ').mpr ⟨hS', hZ'⟩)⟩

end Work.ZeroFreeTables.OffAxis
