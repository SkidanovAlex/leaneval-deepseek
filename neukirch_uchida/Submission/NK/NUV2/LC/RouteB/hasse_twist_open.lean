import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.level_kills_of_loc_eq_zero

/-!
# Route B, lemma `(H)`: the Hasse principle (`μ_p`-coefficients) at an open level

Let `p` be an odd prime, `K` a number field with separable closure `K'`, `ζ ∈ K'` a primitive `p`-th
root of unity and `V ≤ Gal(K'/K)` **open** with `V ≤ rootFix ζ` (`NK.NUV2.LC.RouteB.IsMuOpen`).
For `x ∈ H2Twist p V = H²(V, μ_p)` whose fine localisation vanishes at every place of `K'` over a
finite prime of `K`, we prove `x = 0`.

## Mathematical content

`F := K'^V` is a number field (openness of `V`) containing `ζ`, so `H2Twist p V ≅ Br(F)[p]` and the
fine localisation is the local invariant `Br(F)[p] → Br(F_v)[p]`.  For odd `p` the archimedean places
contribute nothing (`Br(ℂ) = 0`, `Br(ℝ)[odd] = 0`), so the statement is
`Br(F)[p] ↪ ∏_{v finite} Br(F_v)[p]`, i.e. Hasse's theorem for the number field `F`.

## Why the obvious level-wise formulation is *not* used

The level-wise statement "if *all* level localisations `locLevel p V A L a` vanish then `a = 0`" is
**FALSE** (it was returned as false by a prover of this session, and the same phenomenon is recorded
in `Submission/Work/NUV2/LC/coarseLocalisation.lean` and `NOTES_existsGuarded.md` §9): for an
everywhere unramified `(Z/p)²`-extension `L/K` the Künneth class `χ₁⌣χ₂` is non-zero while its
restriction to every cyclic decomposition group vanishes.  Likewise the *level-wise* finite support
of `locLevel` is infinite (all inert primes of `ℚ(i)` for `p = 2`).  See
`Submission/Work/NUV2/LC/RouteB/NOTES_hasse_twist_open_findings.md`.

The correct route therefore passes through the **units (Kummer) localisation**, where both the
level-wise Hasse principle (`NK.GlobalCFTdeep.hbnUnits`, = Milne CFT VII.7.1, PROVED) and finite
support (`NK.NUV2.LC.units_finite_support`, PROVED) are theorems: the Kummer image of `x` in
`H2Units V` is killed by the localisations (finite support + the hypothesis), hence is zero by
`hbnUnits` at a suitable finite level, and `NK.HassePrinciple.kummerColim_injective` (PROVED)
transports this back to `x`.  That route is exactly the delegated lemma
`NK.NUV2.LC.RouteB.level_kills_of_loc_eq_zero`.

## Main result

* `NK.NUV2.LC.RouteB.hasse_twist_open` — the statement itself, reduced to
  `NK.NUV2.LC.RouteB.level_kills_of_loc_eq_zero` and the colimit criterion `ofLevel_eq_iff`.
-/

set_option autoImplicit false

namespace NK.NUV2.LC.RouteB

open NK.BrauerTwist

/-- **Route B, lemma (H): the Hasse principle at an open level, `μ_p`-coefficients.**

A class of `H²(V, μ_p)` (for `V ≤ Gal(K'/K)` open, fixing the primitive `p`-th root of unity `ζ`,
`p` odd) whose localisation vanishes at every place of `K'` over a finite prime of `K` is zero. -/
theorem hasse_twist_open (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (hV : NK.NUV2.LC.RouteB.IsMuOpen (K := K) (K' := K') ζ V)
    (x : NK.BrauerTwist.H2Twist (K := K) (K' := K') p V)
    (h : ∀ A : NK.BrauerTwist.OverFinitePrime K K',
      NK.BrauerTwist.H2Twist.loc (K := K) (K' := K') p V x A = 0) :
    x = 0 := by
  -- represent `x` at a finite level
  obtain ⟨L, a, hx⟩ := NK.BrauerTwist.H2Twist.ofLevel_surjective (K := K) (K' := K') p V x
  have h' : ∀ A : NK.BrauerTwist.OverFinitePrime K K',
      NK.BrauerTwist.H2Twist.loc p V (NK.BrauerTwist.H2Twist.ofLevel p V L a) A = 0 := by
    intro A
    rw [hx]
    exact h A
  -- the colimit class dies at a deeper level
  obtain ⟨M, hLM, h0⟩ :=
    level_kills_of_loc_eq_zero (K := K) (K' := K') p hp hp2 ζ hζ V hV L a h'
  -- hence `x = ofLevel L a = ofLevel M (levelMap a) = ofLevel M 0 = 0`
  rw [← hx, ← NK.BrauerTwist.H2Twist.ofLevel_levelMap (K := K) (K' := K') p V hLM a, h0]
  exact NK.HasseTwist.H2Twist.ofLevel_zero p M

end NK.NUV2.LC.RouteB
