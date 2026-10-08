import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.Lambda
import Submission.Work.BG.exists_unique_ne_one_of_natCard_eq_two
import Submission.Work.BG.units_sq_eq_one_eq_one_or_eq_neg_one

/-!
# Area BG: the dual of a two-element quotient (Bender–Glauberman Lemma 1.7(iii), `C₂`-case)

If `H₀/U` has order two — the case `[H₀ : U] = 2` of Bender–Glauberman's Hypothesis 1.2 in
which `Λ = {λ₁, λ₂}` is cyclic of order two — then `H₀/U` has exactly two linear characters
(the trivial one and `λ₂`), and the non-trivial one takes the value `-1` on every
non-identity element.  This is the "dual of the two-element quotient" fact used to analyse
the orbit sums `r(Λν)` in Lemma 1.7(iii).

The group theory is entirely that of a group of order two, isolated as
`Work.BG.exists_unique_ne_one_of_natCard_eq_two`; the only other input is that a unit of `ℂ`
with square `1` is `±1` (`Work.BG.units_sq_eq_one_eq_one_or_eq_neg_one`).
-/

namespace Work.BG

/-- **Dual of a two-element group.**  A group `X` with `Nat.card X = 2` has exactly two
characters `X →* ℂˣ`: the trivial one and `lam` (for any `lam ≠ 1`), and `lam` takes the
value `-1` on every non-identity element.  (The non-identity element `a` satisfies
`a ^ 2 = 1` and every element of `X` is `1` or `a`, whence `lam a ^ 2 = 1` and
`lam a ≠ 1`.) -/
theorem dualC2_generic {X : Type*} [Group X] (h2 : Nat.card X = 2)
    (lam : X →* ℂˣ) (hlam : lam ≠ 1) :
    (∀ β : X →* ℂˣ, β = 1 ∨ β = lam) ∧
      (∀ x : X, x ≠ 1 → ((lam x : ℂˣ) : ℂ) = -1) := by
  obtain ⟨a, _ha1, ha2, huniv⟩ := exists_unique_ne_one_of_natCard_eq_two h2
  -- the value of `lam` on the non-identity element
  have hlam_a : lam a = -1 := by
    have hsq : lam a ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
    rcases units_sq_eq_one_eq_one_or_eq_neg_one (lam a) hsq with h | h
    · exfalso
      apply hlam
      refine MonoidHom.ext fun x => ?_
      rcases huniv x with hx | hx
      · rw [hx, map_one, map_one]
      · rw [hx, h]; rfl
    · exact h
  constructor
  · intro β
    -- `β` is determined by `β a ∈ {1, -1}`
    have hsq : β a ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
    rcases units_sq_eq_one_eq_one_or_eq_neg_one (β a) hsq with h | h
    · left
      refine MonoidHom.ext fun x => ?_
      rcases huniv x with hx | hx
      · rw [hx, map_one, map_one]
      · rw [hx, h]; rfl
    · right
      refine MonoidHom.ext fun x => ?_
      rcases huniv x with hx | hx
      · rw [hx, map_one, map_one]
      · rw [hx, h, hlam_a]
  · intro x hx
    have hxa : x = a := (huniv x).elim (fun h => absurd h hx) fun h => h
    rw [hxa, hlam_a]
    rfl

/-- **Bender–Glauberman 1981, Lemma 1.7(iii), dual-`C₂` step.**  When `H₀/U` has order `2`,
its dual `Λ` consists of the trivial character and a unique non-trivial character `lam2`,
which is `-1` on every non-identity element of `H₀/U`. -/
theorem lemma17_iii_dualC2 {G : Type} [Group G] [Finite G] (P : Work.BG.Hyp12 G)
    [(P.U.subgroupOf P.H0).Normal]
    (h2 : Nat.card (Work.BG.quotGroup P) = 2) {lam2 : Work.BG.quotGroup P →* ℂˣ}
    (hlam2 : lam2 ≠ 1) :
    (∀ β : Work.BG.quotGroup P →* ℂˣ, β = 1 ∨ β = lam2) ∧
      (∀ x : Work.BG.quotGroup P, x ≠ 1 → ((lam2 x : ℂˣ) : ℂ) = -1) :=
  dualC2_generic h2 lam2 hlam2

end Work.BG
