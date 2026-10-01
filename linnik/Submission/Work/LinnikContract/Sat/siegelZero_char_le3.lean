import Mathlib
import Submission.Work.LinnikContract.Pre

namespace Work.LinnikContract.Sat

/-- Non-degeneracy of the hypothesis list of AREA 6 (`SiegelCase`):
(a) at level `q = 3` the character side of `SiegelZero` is realizable: there is a non-principal real
(quadratic) character mod 3, i.e. `χ ≠ 1` and `χ² = 1`;
(b) `SiegelZero q lamS` forces `q ≥ 2` (at level 1 every Dirichlet character is trivial,
`DirichletCharacter.level_one`), so the threshold `q₀ ≥ 2` used by `linnik_of_areas` loses nothing.

Prover notes: for (a), `MulChar.pow_card_eq_one` gives `χ ^ Fintype.card (ZMod 3)ˣ = 1` and
`Fintype.card (ZMod 3)ˣ = 2` (e.g. `ZMod.card_units_eq_totient`, `Nat.totient_prime`); for
`χ ≠ 1` use for instance `MulChar.ofUnitHom` with the nontrivial hom from the cyclic group
`(ZMod 3)ˣ ≅ C₂` (generator `↦ -1`), or `DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity`
at `a = 2 : ZMod 3` (`2 ≠ 1`, so `χ 2 ≠ 1` while the trivial character sends `2` to `1`).
No `native_decide`. -/
theorem siegelZero_char_le3 :
    (∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 ∧ χ ^ 2 = 1) ∧
    (∀ (q : ℕ) [NeZero q] {lamS : ℝ}, Work.LinnikContract.SiegelZero q lamS → 2 ≤ q) := by
  refine ⟨?_, ?_⟩
  · -- (a) a non-principal quadratic character mod 3 exists.
    -- Every character mod 3 is a square root of `1` since `(ZMod 3)ˣ` has order `2`.
    obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
      (n := 3) (a := 2) (by decide)
    refine ⟨χ, fun h => hχ ?_, ?_⟩
    · -- the trivial character takes the value `1` at the unit `2`
      rw [h]
      exact MulChar.one_apply (by decide)
    · -- `χ ^ Fintype.card (ZMod 3)ˣ = 1` and the unit group has two elements
      have h2 : χ ^ Fintype.card (ZMod 3)ˣ = 1 := MulChar.pow_card_eq_one χ
      rwa [show Fintype.card (ZMod 3)ˣ = 2 from by decide] at h2
  · -- (b) `SiegelZero` needs a non-principal character, which forces the level to be `≥ 2`.
    intro q _ lamS h
    obtain ⟨χ, hχ1, -, β, -, -, -⟩ := h
    by_contra hq
    have hqlt : q < 2 := not_le.mp hq
    have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hq1 : q = 1 := by omega
    exact hχ1 (DirichletCharacter.level_one' χ hq1)

end Work.LinnikContract.Sat
