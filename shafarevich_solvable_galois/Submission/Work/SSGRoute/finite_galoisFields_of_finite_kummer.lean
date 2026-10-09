import Mathlib
import Submission.Work.SSGRoute.LocalFieldAPI
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Finitely many degree-`l` Galois extensions, from a finite Kummer class group** (`l` prime,
`k` containing a primitive `l`-th root of unity `ζ`, `K'` a separable closure of `k`).

Suggested route: `NK.LocalAnabelian.kummerFieldQuot_isGalois_finrank` and
`NK.LocalAnabelian.exists_ne_one_kummerFieldQuot_eq` (both in
`Submission.NK.LocalAnabelian.Kummer.Bridge`) give a *surjection*
`{x : KummerGroup l k // x ≠ 1} → {L // IsGalois k L ∧ Module.finrank k L = l}` (send `x` to the
Kummer field `kummerFieldQuot l x`); conclude with `Finite.of_surjective` and
`Finite.of_injective Subtype.val`.  (This is the finiteness half of the proof of
`NK.LocalAnabelian.natCard_galois_finrank_eq_p`, without the counting.) -/
theorem finite_galoisFields_of_finite_kummer {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (l : ℕ) (hl : l.Prime) (ζ : k) (hζ : IsPrimitiveRoot ζ l)
    [Finite (NK.LocalAnabelian.KummerGroup l k)] :
    Finite {L : IntermediateField k K' // IsGalois k L ∧ Module.finrank k L = l} := by
  haveI : Finite {x : NK.LocalAnabelian.KummerGroup l k // x ≠ 1} :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  let f : {x : NK.LocalAnabelian.KummerGroup l k // x ≠ 1} →
      {L : IntermediateField k K' // IsGalois k L ∧ Module.finrank k L = l} :=
    fun x => ⟨NK.LocalAnabelian.kummerFieldQuot l x.1,
      NK.LocalAnabelian.kummerFieldQuot_isGalois_finrank l hl hζ x.2⟩
  exact Finite.of_surjective f (fun b => by
    obtain ⟨x, hxne, hx⟩ := NK.LocalAnabelian.exists_ne_one_kummerFieldQuot_eq l hl hζ b
    exact ⟨⟨x, hxne⟩, Subtype.ext hx⟩)

end Work.SSGRoute
