import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.prop1a_descent

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

open LeanEval.GroupTheory.Defs

/-!
# Peterfalvi I Ch. II §4 Prop. 1 (a)

`Work.ThreePoints.even_card_centralizer_of_fixes_three` : under (B0)–(B2)
(`hS : Situation G`), for a strongly embedded `H ≤ G`, a subgroup `X ≤ M = H^g` with
`|Ω_X| ≥ 3` (`Ω = G ⧸ H`) has `|C_M(X)|` even.

## Structure of the proof (source: `REFS/peterfalvi_I_ch1_2.md`, p. 168)

* `prop1a_aux` — the source's strong induction on `|X|`: the base case `X = ⊥` is immediate
  (`C_M(⊥) = M = H^g` has even order), the step is
  `Work.ThreePoints.prop1a_descent` (the descent `Y = O^p(X)`, `F₁ = C_G(Y)·P`,
  Ch. I §4 Prop. 2 inside `F₁`, Theorem C, and the `p`-group quotient step).
* `even_card_centralizer_of_fixes_three` — the same statement, extracted from `prop1a_aux`.
-/

/-- **Peterfalvi I Ch. II §4 Prop. 1 (a)**, proved by strong induction on `Nat.card X`
(the source's induction, p. 168).  The induction step is
`Work.ThreePoints.prop1a_descent`. -/
theorem prop1a_aux {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) :
    ∀ (n : ℕ) (X M : Subgroup G), Nat.card X = n →
      (∃ g : G, M = Submission.Blueprint.conj g H) → X ≤ M →
      3 ≤ (Submission.Blueprint.fixedPts H X).ncard →
      Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X M hcard hM hXM hX3
    rcases eq_or_ne X ⊥ with hXbot | hXne
    · -- base case: `C_M(⊥) = M = H^g` has even order
      subst hXbot
      obtain ⟨g, hg⟩ := hM
      rw [hg]
      have hcz : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
        ext x
        simp [Subgroup.mem_centralizer_iff]
      rw [hcz, inf_top_eq]
      rw [Submission.Blueprint.conj, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hH.2.1
    · -- induction step
      refine prop1a_descent hFT hC hA hS hH hX3 hM hXM ?_ hXne
      intro X' M' hlt h3 hM' hXM'
      exact ih (Nat.card X') (by rw [← hcard]; exact hlt) X' M' rfl hM' hXM' h3

/-- Peterfalvi I Ch. II §4 Prop. 1 (a): under (B0)–(B2), if the subgroup `X` fixes at least three
points of `Ω = G ⧸ H` and `M` is one of them (`M = H^g ⊇ X`), then `C_M(X)` has even order.
Proved by induction on `|X|` from Theorem C (`hC`), Theorem A (`hA`) and FT. -/
theorem even_card_centralizer_of_fixes_three {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
  prop1a_aux hFT hC hA hS hH (Nat.card X) X M rfl hM hXM hX3

end Work.ThreePoints
