/-
# ZeroFreeTables/OffAxis — `offAxis_clauses_of_rectC`

The off-axis assembly (`OFFAXIS_ROUTE_LEAD.md` §3) abbreviates the height-`L` engine
(`RectCertC`, `RectCertS`) by supplying the *clauses* `Z1`–`Z5` for an off-axis pair
`(χ₁, ρ₁)` from the parts the engine actually proves.

Here we settle the trivial half of that reduction: an off-axis pair that already sits above
the `λ₁ ≥ 0.348` threshold (`RectCertC`'s conclusion) satisfies

* `Z1` and the repulsion half `Z5rep` of `Z5` **vacuously** — both are implications whose
  hypothesis `lamOf q ρ₁ < 0.348` (resp. `< 0.2`) contradicts `348/1000 ≤ lamOf q ρ₁`;
* `Z5rows` **vacuously** — every §14 row ends at or below `348/1000`, so no row can contain
  such a `λ₁` in its half-open interval;
* `Z2`, `Z3`, `Z4` are the hypotheses.

The only numerical input is `rows14_hi_le`: every right endpoint of the Deuring–Heilbronn
table `rows14` is `≤ 348/1000` (the four rows `(0.3,0.348]`, `(0.25,0.3]`, `(0.2,0.25]`,
`[0,0.2]`, a finite check).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs

namespace Work.ZeroFreeTables.OffAxis

/-- Every right endpoint of the §14 (Deuring–Heilbronn) table `rows14` is at most `348/1000`:
the four rows are `[0,0.2]`, `(0.2,0.25]`, `(0.25,0.3]`, `(0.3,0.348]`. -/
theorem rows14_hi_le : ∀ r ∈ Work.LinnikContract.rows14, r.2.1 ≤ (348 : ℝ)/1000 := by
  intro r hr
  simp only [Work.LinnikContract.rows14, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> norm_num

/-- **The `Z1`–`Z5` clauses for a `RectCertC` pair.**  If `λ₁ = lamOf q ρ₁ ≥ 0.348` and the
engine has already produced `Z2`, `Z3`, `Z4`, then `Z1` holds vacuously (its hypothesis
`λ₁ < 0.348` is false), the §14 rows `Z5rows` hold vacuously (every row ends at `≤ 0.348`),
and the repulsion `Z5rep` holds vacuously (its hypothesis `λ₁ < 0.2` is false). -/
theorem offAxis_clauses_of_rectC {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (lamS : ℝ) (h348 : 348/1000 ≤ Work.LinnikContract.lamOf q ρ₁)
    (h2 : Work.ZeroFreeTables.Z2 χ₁ ρ₁) (h3 : Work.ZeroFreeTables.Z3 χ₁ ρ₁)
    (h4 : Work.ZeroFreeTables.Z4 χ₁ ρ₁) :
    Work.ZeroFreeTables.Z1 χ₁ ρ₁ ∧ Work.ZeroFreeTables.Z2 χ₁ ρ₁ ∧
      Work.ZeroFreeTables.Z3 χ₁ ρ₁ ∧ Work.ZeroFreeTables.Z4 χ₁ ρ₁ ∧
      Work.ZeroFreeTables.Z5 χ₁ ρ₁ lamS := by
  refine ⟨?_, h2, h3, h4, ?_⟩
  · -- `Z1`: the hypothesis `lamOf q ρ₁ < 0.348` contradicts `h348`.
    intro h
    exfalso
    linarith
  · -- `Z5 = Z5rows ∧ Z5rep`.
    refine ⟨?_, ?_⟩
    · -- `Z5rows`: no §14 row contains a `λ₁ ≥ 0.348`.
      intro r hr _ _ hr2
      exfalso
      have := rows14_hi_le r hr
      linarith
    · -- `Z5rep`: the hypothesis `lamOf q ρ₁ < 0.2` contradicts `h348`.
      intro _ h02
      exfalso
      linarith

end Work.ZeroFreeTables.OffAxis
