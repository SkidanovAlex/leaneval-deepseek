import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic
import Submission.Work.ZASS.ncard_ne_inf
import Submission.Work.ZASS.ncard_fixed_ne_inf_le_one
import Submission.Work.ZASS.natCard_pairStab
import Submission.Work.ZASS.ncard_fiber
import Submission.Work.ZASS.ncard_fixers_eq_mul

namespace Work.ZASS

/-- **Z2 (blueprint §ZASS).** The elements of `B = G_∞` that fix a further point number
`1 + q * ((q-1)/2 - 1)`: double count the pairs `(g,x)` with `g ∈ B`, `x ≠ ∞`, `g • x = x`.
Counted by `x` the number is `q * (q-1)/2` (each `x ≠ ∞` contributes its stabilizer in `B`,
i.e. a two-point stabilizer of order `(q-1)/2`); counted by `g` it is `q` for the identity
plus one for each nonidentity element of `fixesSome`, because a nonidentity element of `B`
fixes at most one point `≠ ∞`.
(Hypothesis amended to `Work.GW2.ZassHyps2`, design pass 2.) -/
theorem ncard_fixesSome {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {q : ℕ} (h : Work.GW2.ZassHyps2 G X q) {inf zero : X} (hne : inf ≠ zero)
    (hB : Nat.card (Work.Zassenhaus.borel G inf) = q * ((q - 1) / 2)) :
    (Work.Zassenhaus.fixesSome G inf).ncard = 1 + q * ((q - 1) / 2 - 1) := by
  classical
  -- Note on `hB`: it is *not* needed for this statement.  The double count below counts
  -- nonidentity elements on both sides (`ncard_fixers_eq_mul`), so the full count
  -- `|B| = q * ((q-1)/2)` supplied by `hB` is never used.  (`hB` is a consequence of the
  -- transitivity of `B` on `X ∖ {∞}`, proved separately as `Work.ZASS.orbit_borel`.)
  -- `Y := X ∖ {∞}` has `q` elements.
  have hY : ({x : X | x ≠ inf} : Set X).ncard = q := ncard_ne_inf inf h.2.1
  -- The double count: `|B ∖ {1} fixing some x ∈ Y| = |Y| * ((q-1)/2 - 1)`.
  have key : ({g : G | g ∈ Work.Zassenhaus.borel G inf ∧ g ≠ 1 ∧
      ∃ x : X, x ≠ inf ∧ g • x = x} : Set G).ncard = q * ((q - 1) / 2 - 1) := by
    have hmain := ncard_fixers_eq_mul (G := G) (X := X) (Work.Zassenhaus.borel G inf)
      ({x : X | x ≠ inf}) (c := (q - 1) / 2 - 1)
      (fun g hg hg1 => ncard_fixed_ne_inf_le_one hg (h.2.2.2.1 g hg1))
      (fun x hx => ncard_fiber (hm := natCard_pairStab h hx))
    simpa only [Set.mem_ofPred_eq, SetLike.mem_coe, hY] using hmain
  -- The set counted above is `fixesSome ∖ {1}`.
  have hset : ({g : G | g ∈ Work.Zassenhaus.borel G inf ∧ g ≠ 1 ∧
      ∃ x : X, x ≠ inf ∧ g • x = x} : Set G)
      = Work.Zassenhaus.fixesSome G inf \ {1} := by
    ext g
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      Work.Zassenhaus.mem_fixesSome_iff]
    tauto
  have hone : (1 : G) ∈ Work.Zassenhaus.fixesSome G inf := by
    refine ⟨?_, zero, hne.symm, ?_⟩
    · simp only [MulAction.mem_stabilizer_iff, one_smul]
    · exact one_smul G zero
  have hcount : (Work.Zassenhaus.fixesSome G inf).ncard - 1 = q * ((q - 1) / 2 - 1) := by
    rw [← Set.ncard_sdiff_singleton_of_mem hone, ← hset]
    exact key
  have hpos : 1 ≤ (Work.Zassenhaus.fixesSome G inf).ncard := by
    have h1 : ({1} : Set G).ncard ≤ (Work.Zassenhaus.fixesSome G inf).ncard :=
      Set.ncard_le_ncard (fun g hg => by
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact hone)
    simpa only [Set.ncard_singleton] using h1
  have hfin : (Work.Zassenhaus.fixesSome G inf).ncard = q * ((q - 1) / 2 - 1) + 1 := by
    rw [← Nat.sub_add_cancel hpos, hcount]
  rw [hfin, Nat.add_comm]

end Work.ZASS
