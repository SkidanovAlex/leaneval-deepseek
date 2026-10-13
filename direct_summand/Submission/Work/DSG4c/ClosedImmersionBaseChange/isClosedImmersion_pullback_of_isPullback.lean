import Mathlib

namespace Work.DSG4c.ClosedImmersionBaseChange

open CategoryTheory AlgebraicGeometry Limits
universe u
/-- If `i : X ⟶ P` is a closed immersion and `P' = P ×_S S'` (witnessed by the pullback square
`h`), then the base change `X ×_S S'` is a closed subscheme of `P'` over `S'`.
Suggested route: let `Y := pullback i q`, which maps to `P'` by `pullback.snd i q` (a closed
immersion since closed immersions are stable under base change), and identify `Y` with
`pullback (i ≫ s) σ` by pasting `IsPullback.of_hasPullback i q` with `h`; then transport the
closed immersion along this isomorphism (`IsClosedImmersion` is stable under composition with
isomorphisms). -/
theorem isClosedImmersion_pullback_of_isPullback {X P P' S S' : Scheme.{u}}
    (i : X ⟶ P) (s : P ⟶ S) (q : P' ⟶ P) (s' : P' ⟶ S') (σ : S' ⟶ S)
    (h : IsPullback q s' s σ) [IsClosedImmersion i] :
    ∃ j : pullback (i ≫ s) σ ⟶ P', IsClosedImmersion j ∧ j ≫ s' = pullback.snd (i ≫ s) σ := by
  -- The square
  --   `pullback i q --fst--> X --i--> P`
  --   `     |                    |               |`
  --   `    snd                   i               s`
  --   `     v                    v               v`
  --   `    P' -------q-------->  P ---s------->  S`
  --   `     |                    |               |`
  --   `     s'                  s               σ`
  --   `     v                    v               v`
  --   `     S' -----σ--------->  S`
  -- is the vertical paste of the pullback square of `i` and `q` (top) with `h` (bottom).
  have H : IsPullback (pullback.fst i q) (pullback.snd i q ≫ s') (i ≫ s) σ :=
    (IsPullback.of_hasPullback i q).paste_vert h
  -- Hence `pullback i q ≅ pullback (i ≫ s) σ`, and transporting the closed immersion
  -- `pullback.snd i q : pullback i q ⟶ P'` (a base change of `i`) along this iso gives `j`.
  refine ⟨H.isoPullback.inv ≫ pullback.snd i q, inferInstance, ?_⟩
  rw [Category.assoc, H.isoPullback_inv_snd]

end Work.DSG4c.ClosedImmersionBaseChange
