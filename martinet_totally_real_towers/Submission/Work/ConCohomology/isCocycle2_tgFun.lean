/-
Copyright: the martinet_totally_real_towers team.

# The raw transgression is a `2`-cocycle

Given a group extension `1 → N → G → Q → 1` (`GroupExt G Q N`), a section `s : Q → G` of `q`, and
a function `φ : N → M`, the raw transgression cocycle of `Extension.lean` is

  `tgFun E s hs φ (σ, τ) = φ (s σ · s τ · s (στ)⁻¹)`,

where the element `s σ · s τ · s (στ)⁻¹ ∈ ker q` is viewed as an element of `N` via `kerLift`.

The present file proves the main structural fact about it: if

* `N` acts trivially on `M` (`hcompN`),
* the `Q`-action on `M` is the `G`-action transported along the section `s` (`hcompQ`),
* `φ` is a `1`-cocycle for the `N`-action, which under `hcompN` simply means that `φ` is
  *additive*: `φ (a * b) = φ a + φ b`,
* `φ` is `G`-equivariant: `φ (conj g n) = g • φ n` (`hinv`), i.e. `φ` represents a class in
  `H¹(N,M)^G` (invariants under conjugation),

then `tgFun E s hs φ` is a `2`-cocycle for `Q` (this is the transgression
`H¹(N,M)^G → H²(Q,M)`).

The mathematical content is the classical relation in the group `N`

  `conj (s σ) (u (τ,ρ)) · u (σ, τρ) = u (σ,τ) · u (στ, ρ)`   where `u(x,y) = s x · s y · s(xy)⁻¹`,

which is checked inside `G` (where it is an immediate cancellation) and pulled back along the
injective `i : N → G`; additivity of `φ` then converts it into the coboundary identity, using that
`M` is abelian to regroup `φ a - φ b + φ c - φ d` as `(φ a + φ c) - (φ b + φ d)`.
-/

import Mathlib
import Submission.Work.ConCohomology.Extension

namespace Work.ConCohomology

open Function Classical

/-- The `N`-valued `2`-cochain attached to a section `s` of the extension: the "factor system"
`u x y = s x · s y · s (xy)⁻¹` of the section, viewed as an element of `N = ker q`.

`tgFun E s hs φ x y` is by definition `φ (tgArg E s hs x y)`. -/
noncomputable def tgArg {G Q N : Type*} [Group G] [Group Q] [Group N] (E : GroupExt G Q N)
    (s : Q → G) (hs : ∀ y : Q, E.q (s y) = y) (x y : Q) : N :=
  E.kerLift (s x * s y * (s (x * y))⁻¹) (by
    rw [map_mul, map_mul, map_inv, hs, hs, hs]
    simp)

/-- The defining property of `tgArg`: its image in `G` is the section factor system. -/
lemma i_tgArg {G Q N : Type*} [Group G] [Group Q] [Group N] (E : GroupExt G Q N)
    (s : Q → G) (hs : ∀ y : Q, E.q (s y) = y) (x y : Q) :
    E.i (tgArg E s hs x y) = s x * s y * (s (x * y))⁻¹ := E.i_kerLift _ _

/-- `tgFun` is `φ` applied to `tgArg` (`φ` is applied to an element of `N` after transporting the
factor system of the section along `kerLift`). -/
lemma tgFun_eq_tgArg {G Q N : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] (E : GroupExt G Q N) (s : Q → G)
    (hs : ∀ y : Q, E.q (s y) = y) (φ : N → M) (x y : Q) :
    tgFun E s hs φ (x, y) = φ (tgArg E s hs x y) := rfl

/-- **The raw transgression is a `2`-cocycle.**  If `N` acts trivially on `M`, the `Q`-action is
compatible with the `G`-action along a section `s`, `φ` is additive (a `1`-cocycle for the trivial
`N`-action) and `φ` is `G`-equivariant, then `tgFun E s hs φ` is a factor system on `Q`. -/
lemma isCocycle2_tgFun {G Q N : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    [DistribMulAction N M] [DistribMulAction Q M] (E : GroupExt G Q N)
    (hcompN : ∀ (n : N) (m : M), n • m = m) (s : Q → G)
    (hs : ∀ y : Q, E.q (s y) = y) (hcompQ : ∀ (y : Q) (m : M), y • m = s y • m)
    (φ : N → M) (hφ : IsCocycle1 φ)
    (hinv : ∀ (g : G) (n : N), φ (E.conj g n) = g • φ n) :
    IsCocycle2 (tgFun E s hs φ) := by
  intro σ τ ρ
  -- Under `hcompN` the `1`-cocycle `φ` is just an additive map `N → M`.
  have hφadd : ∀ a b : N, φ (a * b) = φ a + φ b := fun a b => by
    rw [hφ a b, hcompN a (φ b)]
  -- The factor system of the section is multiplicative in the sense of a `2`-cocycle.
  have hkey : E.conj (s σ) (tgArg E s hs τ ρ) * tgArg E s hs σ (τ * ρ)
      = tgArg E s hs σ τ * tgArg E s hs (σ * τ) ρ := by
    apply E.injective_i
    simp only [map_mul, GroupExt.i_conj, i_tgArg]
    group
  -- Regrouped additively, using commutativity of `M`.
  have hAC : φ (E.conj (s σ) (tgArg E s hs τ ρ)) + φ (tgArg E s hs σ (τ * ρ))
      = φ (tgArg E s hs (σ * τ) ρ) + φ (tgArg E s hs σ τ) := by
    calc φ (E.conj (s σ) (tgArg E s hs τ ρ)) + φ (tgArg E s hs σ (τ * ρ))
        = φ (E.conj (s σ) (tgArg E s hs τ ρ) * tgArg E s hs σ (τ * ρ)) := (hφadd _ _).symm
      _ = φ (tgArg E s hs σ τ * tgArg E s hs (σ * τ) ρ) := by rw [hkey]
      _ = φ (tgArg E s hs (σ * τ) ρ) + φ (tgArg E s hs σ τ) := by
            rw [hφadd (tgArg E s hs σ τ) (tgArg E s hs (σ * τ) ρ)]; abel
  -- Transport the `Q`-action on `φ (u τ ρ)` to the `G`-action via the section and `hinv`.
  have hA : σ • φ (tgArg E s hs τ ρ) = φ (E.conj (s σ) (tgArg E s hs τ ρ)) := by
    rw [hcompQ σ (φ (tgArg E s hs τ ρ))]
    exact (hinv (s σ) (tgArg E s hs τ ρ)).symm
  change σ • φ (tgArg E s hs τ ρ) - φ (tgArg E s hs (σ * τ) ρ)
      + φ (tgArg E s hs σ (τ * ρ)) - φ (tgArg E s hs σ τ) = 0
  have hmain : φ (E.conj (s σ) (tgArg E s hs τ ρ)) - φ (tgArg E s hs (σ * τ) ρ)
      + φ (tgArg E s hs σ (τ * ρ)) - φ (tgArg E s hs σ τ) = 0 := by
    rw [show φ (E.conj (s σ) (tgArg E s hs τ ρ)) - φ (tgArg E s hs (σ * τ) ρ)
        + φ (tgArg E s hs σ (τ * ρ)) - φ (tgArg E s hs σ τ)
        = (φ (E.conj (s σ) (tgArg E s hs τ ρ)) + φ (tgArg E s hs σ (τ * ρ)))
          - (φ (tgArg E s hs (σ * τ) ρ) + φ (tgArg E s hs σ τ)) from by abel,
      hAC, sub_self]
  rw [hA]
  exact hmain

end Work.ConCohomology
