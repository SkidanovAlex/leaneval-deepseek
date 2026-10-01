/-
# ZeroFreeTables/OffAxis — `offAxis_clauses_high`

The **high-`λ₁` branch** (`λ₁ ≥ 0.695`) of the off-axis assembly (`OFFAXIS_ROUTE_LEAD.md` §1,
last bullet).  For an off-axis pair `(χ₁, ρ₁)` whose `λ₁` sits above the last right end of the
Deuring–Heilbronn/Table rows, the five clauses `Z1`–`Z5` follow from the two rectangle-height
witness bounds `Lam2BoundH L χ' 0.701`, `Lam3BoundH L χ' 0.856` (stated for the *witness*
character `χ'`, on the height-`L` region `|Im| ≤ L`) together with the wide minimality of the
round-2 `IsMin1 χ₁ ρ₁`.

* `Z1` and `Z5` (both the §14 rows and the repulsion) are **vacuous**: their hypotheses require
  `λ₁ < 0.348` (resp. `λ₁ < 0.2`), while `0.695 ≤ λ₁`.
* `Z2` is immediate from `0.56 ≤ 0.695 ≤ λ₁`.
* `Z4` is **vacuous**: every right end of `rows15` is `≤ 0.6 < 0.695 ≤ λ₁`, so no row's
  `λ₁`-interval contains `λ₁` (`rows15_hi_le`).
* `Z3`: `Lam0Bound χ₁ ρ₁ 0.695` is *free* (minimality gives `λ₁ ≤ λ(u)` for every `IsZ` zero
  `u`, and multiplicity gives it at `ρ₁`); the other two conjuncts are the two transports
  `lam2Bound_transport`, `lam3Bound_transport`, which turn the height-`L` witness bounds at `χ'`
  into the contract's round-1 bounds at `χ₁` — no identification of `χ₁` with `χ'` is needed,
  because either `χ₁ ∈ {χ', χ'⁻¹}` (the excluded pairs coincide) or else `ρ₁` itself is an
  admissible height-`L` zero for the witness bound, forcing `λ₁` above the bound and leaving
  minimality to do the rest.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.LinnikContract2.API
import Submission.Work.ZeroFreeTables.OffAxis.offAxis_clauses_of_rectC
import Submission.Work.ZeroFreeTables.OffAxis.lam2Bound_transport
import Submission.Work.ZeroFreeTables.OffAxis.lam3Bound_transport

namespace Work.ZeroFreeTables.OffAxis

/-- Every right endpoint of the §15 (Table 8/10/9) table `rows15` is at most `6/10`:
the thirteen rows end at `0.36, 0.38, …, 0.60`. -/
theorem rows15_hi_le : ∀ r ∈ Work.LinnikContract.rows15, r.2.1 ≤ (6 : ℝ)/10 := by
  intro r hr
  simp only [Work.LinnikContract.rows15, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    · subst h; norm_num

theorem offAxis_clauses_high {q : ℕ} [NeZero q] {L : ℝ} (hL : 50 ≤ L) (lamS : ℝ)
    {χ₁ χ' : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hm : Work.LinnikContract2.IsMin1 χ₁ ρ₁)
    (h2 : Work.ZeroFreeTables.Lam2BoundH L χ' (701/1000))
    (h3 : Work.ZeroFreeTables.Lam3BoundH L χ' (856/1000))
    (hlam : 695/1000 ≤ Work.LinnikContract.lamOf q ρ₁) :
    Work.ZeroFreeTables.Z1 χ₁ ρ₁ ∧ Work.ZeroFreeTables.Z2 χ₁ ρ₁ ∧
      Work.ZeroFreeTables.Z3 χ₁ ρ₁ ∧ Work.ZeroFreeTables.Z4 χ₁ ρ₁ ∧
      Work.ZeroFreeTables.Z5 χ₁ ρ₁ lamS := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `Z1`: its hypothesis `lamOf q ρ₁ < 0.348` contradicts `hlam`.
    intro h
    exfalso
    linarith
  · -- `Z2`: `0.56 ≤ 0.695 ≤ λ₁`.
    intro _ _
    linarith
  · -- `Z3 = Lam0Bound χ₁ ρ₁ 0.695 ∧ Lam2Bound χ₁ 0.701 ∧ Lam3Bound χ₁ 0.856`.
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · -- `ρ₁` multiple ⇒ `0.695 ≤ λ₁` (the hypothesis `hlam`).
      intro _
      linarith
    · -- every other working-region zero of `χ₁` has `λ ≥ λ₁ ≥ 0.695` (wide minimality).
      intro ρ hZ _ _
      have hle : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ :=
        hm.2 χ₁ ρ ⟨hZ.1, hZ.2.1, hZ.2.2.trans (by norm_num)⟩
      linarith
    · -- `Lam2Bound χ₁ 0.701`, the `λ₂` transport at the witness character `χ'`.
      simpa only [show (0.701 : ℝ) = 701/1000 by norm_num]
        using lam2Bound_transport hL hm h2
    · -- `Lam3Bound χ₁ 0.856`, the `λ₃` transport at the witness character `χ'`.
      simpa only [show (0.856 : ℝ) = 856/1000 by norm_num]
        using lam3Bound_transport hL hm h3
  · -- `Z4`: no `rows15` interval contains `λ₁ ≥ 0.695`, since every right end is `≤ 0.6`.
    intro r hr _ hr2
    exfalso
    have := rows15_hi_le r hr
    linarith
  · -- `Z5 = Z5rows ∧ Z5rep`.
    refine ⟨?_, ?_⟩
    · -- `Z5rows`: every `rows14` row ends at `≤ 0.348 < 0.695 ≤ λ₁`.
      intro r hr _ _ hr2
      exfalso
      have := rows14_hi_le r hr
      linarith
    · -- `Z5rep`: its hypothesis `λ₁ < 0.2` contradicts `hlam`.
      intro _ h02
      exfalso
      linarith

end Work.ZeroFreeTables.OffAxis
