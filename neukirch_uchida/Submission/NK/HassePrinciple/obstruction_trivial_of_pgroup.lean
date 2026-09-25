import Mathlib
import Submission.NK.HassePrinciple.Obstruction
import Submission.NK.HassePrinciple.H2_map_injective_of_coprime_index
import Submission.NK.HassePrinciple.finite_levelGroup
import Submission.NK.HassePrinciple.exists_subgroup_levelGroup_equiv_sylow
import Submission.NK.HassePrinciple.levelInclHom_injective
import Submission.NK.HassePrinciple.levelInclHom_mem_levelObstruction

namespace NK.HassePrinciple

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The Sylow reduction for the Hasse principle at the finite levels.**

If the level-wise Hasse principle — a class of a finite level that is locally trivial at its own
level is zero, i.e. `a ∈ levelObstruction p V L → a = 0` — holds at every level whose level group
`V/(V ⊓ Gal(K'/L))` is a `p`-group, then it holds at every level.

This is the finite-group (Sylow) reduction of the arithmetic input of the Hasse principle
(`the `p`-primary level-wise Hasse principle (now `Sha2Input.level`)`): only the `p`-primary levels are needed.  The
argument: let `P` be a Sylow `p`-subgroup of the finite level group `Γ = U/(U ⊓ Gal(K'/L))` and
`V ≤ U` its preimage in `U`; then `LevelGroup V L ≅* P`, the restriction
`H2.map (levelInclHom h L) : H²(Γ, Z/p) → H²(LevelGroup V L, Z/p)` carries the level obstruction
of `(U,L)` into that of `(V,L)` (compatibility of the localisation with the restriction), so the
hypothesis applied to `(V,L)` gives that it kills `a`, and the prime-to-`p` index of `P` in `Γ`
together with the transfer lemma `NK.HassePrinciple.H2_map_injective_of_coprime_index` gives
`a = 0`. -/
theorem obstruction_trivial_of_pgroup {p : ℕ} (hp : p.Prime)
    (h : ∀ (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K'),
      IsPGroup p (LevelGroup V L) → ∀ a : LevelH2 p V L, a ∈ levelObstruction p V L → a = 0) :
    ∀ (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
      a ∈ levelObstruction p U L → a = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro U L a ha
  -- A Sylow `p`-subgroup `Q` of the finite level group `Γ = U/(U ⊓ Gal(K'/L))`.
  obtain ⟨Q⟩ := Sylow.nonempty (p := p) (G := LevelGroup U L)
  -- Its preimage `V ≤ U` in `U`: `LevelGroup V L ≃* Q`, and `levelInclHom` has range `Q`.
  obtain ⟨V, hV, ⟨iso⟩, hrange⟩ := exists_subgroup_levelGroup_equiv_sylow U L Q
  -- The level group of `V` is a `p`-group, being isomorphic to the Sylow subgroup `Q`.
  have hP : IsPGroup p (LevelGroup V L) := IsPGroup.of_equiv Q.isPGroup' iso.symm
  -- Restriction carries the level obstruction of `(U,L)` into that of `(V,L)`.
  have hres : (H2.map (levelInclHom hV L)).hom a ∈ levelObstruction p V L :=
    levelInclHom_mem_levelObstruction p hV L ha
  -- Hence the `p`-primary input kills the restriction of `a`.
  have hzero : (H2.map (levelInclHom hV L)).hom a = 0 :=
    h V L hP ((H2.map (levelInclHom hV L)).hom a) hres
  -- The index of the Sylow subgroup is prime to `p`, so restriction is injective here.
  have hcop : Nat.Coprime (Subgroup.index (MonoidHom.range (levelInclHom hV L))) p := by
    rw [hrange, Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr Q.not_dvd_index
  exact H2_map_injective_of_coprime_index (p := p) (levelInclHom hV L)
    (levelInclHom_injective hV L) hcop
    (hzero.trans (map_zero ((H2.map (levelInclHom hV L)).hom)).symm)

end NK.HassePrinciple
