import Mathlib.NumberTheory.NumberField.Basic
import Submission.Work.SSGRoute.PTdualControl.C6_rankOneBrick
import Submission.Work.SSGRoute.TatePoitouRoute.exists_shapiro_c
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the non-invariant level-cocycle datum (`TPatom` route)

Two small set-theoretic helpers used to *state* the geometric input
(`Work.SSGRoute.TPatom.exists_concentratedLevelData`) and its use in the assembly of
`Work.SSGRoute.TPatom.noninvariantLevelDatum`:

* `concSet w N γ` — the set `γ · D_w · N ⊆ Gal(K/k)`, the union of the `D_w`-orbit of the coset
  `Nγ` and its `N`-translates.  It indexes the blocks (places of `K₁ = K^N` over `q ∩ k`) detected by
  the concentrated character: `y (c x d^f) ≠ 1` exactly for `galRes x ∈ concSet w N γ`.
* `KummerCoeff M μ c` — the coefficient `μ (e_c)` of the coinduced module `M = coind_N^G 𝔽_p` at the
  `N`-coset `c` (the `Mackey`/orbit coefficient of `μ`); `μ ≠ 0` is equivalent to some coefficient
  being non-zero.
-/

namespace Work.SSGRoute.TPatom

open CategoryTheory

/-- The set `γ · D_w · N ⊆ Gal(K/k)`. -/
def concSet (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    (w : NK.GlobalCFT.Place K) (N : Subgroup (K ≃ₐ[k] K)) (γ : K ≃ₐ[k] K) :
    Set (K ≃ₐ[k] K) :=
  {g | ∃ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w, ∃ n ∈ N, γ * (δ * n) = g}

end Work.SSGRoute.TPatom
