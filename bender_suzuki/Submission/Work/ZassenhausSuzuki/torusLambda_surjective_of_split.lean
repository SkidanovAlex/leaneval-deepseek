import Mathlib
import Submission.Work.ZassenhausSuzuki.frel_torus_all
import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Surjectivity of the torus map in the split rank-one configuration

This file isolates the "surjectivity of `λ ↦ d(λ)`" step of `Work.ZassenhausSuzuki.frel_torus_all`
with the hypotheses phrased exactly as in the split rank-one setting: `Q` is a 2-group
(`h2 : IsPGroup 2 Q`) and `K` is a field of characteristic two together with the coordinatisation
`e : Q ≃* A(K,θ)`.

Everything the surjectivity argument needs is a consequence of `e`:

* `K` is finite, because `SzA K θ ≃ Q` is finite;
* `Q ≠ ⊥`, because `A(K,θ)` is non-trivial;
* `|D| = |Kˣ|` (`|D| = #Inv Q = |K| - 1 = |Kˣ|`, the count of involutions of `A(K,θ)`).

The map `D → Kˣ` supplied by `TorusCoords` is then injective (`h_λ` determines `λ`, and `d` is
determined by its action on `Q`), hence bijective between finite sets of equal cardinality, hence
surjective.  The proof of that last step lives in `Work.ZassenhausSuzuki.torusLambda_surjective`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem torusLambda_surjective_of_split {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} {e : Q ≃* Work.ZassenhausSuzuki.SzA K θ}
    (htorus : Work.ZassenhausSuzuki.TorusCoords K θ H Q t e) (lam : Kˣ) :
    ∃ d ∈ Submission.Blueprint.twoPoint H t, ∀ x : Q,
      (((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ (lam : K) (e x)) : Q)) : G)
        = d * (x : G) * d⁻¹ := by
  classical
  haveI : Finite ↥Q := Subtype.finite
  haveI hSzA : Finite (SzA K θ) := Finite.of_equiv ↥Q e.toEquiv
  -- `K` is finite: it embeds into the finite group `A(K,θ)` as `k ↦ ⟨k,0⟩`.
  haveI hK : Finite K :=
    Finite.of_injective (fun k : K => (⟨k, 0⟩ : SzA K θ))
      (fun a b hab => by simpa using congrArg SzA.a hab)
  haveI hKunits : Finite Kˣ :=
    Finite.of_injective (fun u : Kˣ => (u : K)) (fun a b hab => Units.ext hab)
  -- `Q ≠ ⊥`: `A(K,θ)` is non-trivial (it contains `⟨1,0⟩ ≠ 1`).
  have hQ : Q ≠ ⊥ := by
    intro hbot
    have h1 : (e.symm (⟨1, 0⟩ : SzA K θ) : Q) = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.mp (hbot ▸ (e.symm (⟨1, 0⟩ : SzA K θ)).2)
    have h1' : (⟨1, 0⟩ : SzA K θ) = 1 := by
      have := congrArg (fun q : Q => e q) h1
      simpa using this
    have h10 : (1 : K) = 0 := by simpa using congrArg SzA.a h1'
    exact one_ne_zero h10
  -- `|D| = #Inv(Q) = |K| - 1 = |Kˣ|`.
  have hcard : Nat.card ↥(twoPoint H t) = Nat.card Kˣ := by
    rw [twoPoint_card_eq_involutions hsplit hzass h2]
    rw [show (involutions (Q : Set G)) = {x : G | x ∈ Q ∧ orderOf x = 2} from rfl]
    rw [ncard_involutions_of_mulEquiv (Q := Q) e]
    rw [SzA.ncard_orderOf_eq_two θ, Nat.card_units K]
  exact torusLambda_surjective (K := K) (θ := θ) (e := e) hsplit hzass htorus hQ hcard lam

end Work.ZassenhausSuzuki
