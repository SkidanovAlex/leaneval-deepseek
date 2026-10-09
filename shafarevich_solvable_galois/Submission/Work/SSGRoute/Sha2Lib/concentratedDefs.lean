import Mathlib
import Submission.Work.SSGRoute.PTdualControl.C6_rankOneBrick
import Submission.Work.SSGRoute.TatePoitouRoute.exists_shapiro_c
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the "concentrated level" route to the rank-one brick

This file collects the two small definitions used to *state* the geometric input of the
non-invariant case of the rank-one brick (`Work.SSGRoute.Sha2Lib.rankOneBrick_algebraicClosure`).

The route (the `TPatom` design, `Submission/Work/SSGRoute/NOTE_TPatom_route.md`): for a nonzero
`D_w`-equivariant functional `μ` on the coinduced permutation module `M = coInd_N^Γ 𝔽_p` which kills
the constant vector, one picks

* a coset `N γ` with `μ` non-zero on its Dirac,
* the fixed field `K₁ := K^N` and a finite Galois level `L ⊇ K` over `k` which is the normal closure
  of `K` together with a cyclic degree-`p` extension `E/K₁` that is **inert** exactly at the place
  `(γ·q) ∩ K₁` of `K₁` over `q ∩ k` and split completely at all the other places over `q ∩ k`,
* an element `d ∈ D_{q'}` of the level's decomposition group generating
  `D_{q'}/(D_{q'} ∩ Gal(L/K₁))` (a cyclic quotient, `K₁/k` being unramified at `q ∩ k`), with
  `f = [D_{q'} : D_{q'} ∩ Gal(L/K₁)]`,
* the character `y` of `H = Gal(L/K₁)` that is the restriction to the Kummer field `E`; it kills the
  inertia and is non-trivial exactly on the conjugates of `d ^ f` coming from the `γ`-block.

`concSet` below is the index set of that last clause: the double coset `γ · D_w · N ⊆ Gal(K/k)`,
which indexes the places of `K₁ = K^N` over `q ∩ k` that lie over `γ·q`.
-/

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory

/-- The double coset `γ · D_w · N ⊆ Gal(K/k)` (`D_w = decompK w`).

As a set of elements of `Gal(K/k)`, it indexes the places of the fixed field `K^N` over `q ∩ k`
lying over the place `γ · q` of `K`: `x ∈ concSet k K w N γ` holds exactly for those `x` whose
associated place is in the `γ`-orbit. -/
def concSet (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    (w : NK.GlobalCFT.Place K) (N : Subgroup (K ≃ₐ[k] K)) (γ : K ≃ₐ[k] K) :
    Set (K ≃ₐ[k] K) :=
  {g | ∃ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w, ∃ n ∈ N, γ * (δ * n) = g}

/-- The constant vector `1` of the coinduced module `coInd_N^Γ 𝔽_p`; it is fixed by `Γ`. -/
noncomputable def constVec (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (N : Subgroup (K ≃ₐ[k] K)) :
    (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))).V :=
  ⟨fun _ => 1, fun _ _ => rfl⟩

end Work.SSGRoute.Sha2Lib
