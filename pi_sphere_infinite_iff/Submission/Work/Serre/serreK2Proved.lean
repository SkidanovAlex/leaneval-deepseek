import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.serreE2b
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.cylRelPi
import Submission.Work.Serre.cylJoinedIncl
import Submission.Work.Serre.hZeroOfPiZero
import Submission.Work.Serre.serreK2Aux
import Submission.Work.Serre.RangeOne.Comparison
import Submission.Work.Serre.RangeOne.rangeWhitehead
import Submission.Work.Serre.serreAttachKillPi
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.RatHurewicz.compression_of_relPiVanishing

/-!
# K2: range-weak-equivalences induce rational homology isomorphisms

This file proves `Work.Serre.SerreK2`: if `f : X → Y` induces a bijection on `π_i` for all `i < N`
(at every base point), then it induces an isomorphism on rational homology in degrees `< N`.

## Route

Write `N = n + 2` (the case `N ≤ 1` is `Work.Serre.hZeroOfPiZero`).  The map `f` is replaced by

`f' = killIncl (n+1) Y ∘ f : X → KillCells (n+1) Y`,

where `KillCells (n+1) Y` is `Y` with an `(n+3)`-cell attached along *every* map `S^{n+2} → Y`
(`Submission/Work/Serre/serreAttachKillPi.lean`): the attached cells kill `π_{n+2}`
(`Work.Serre.killCells_step`) while leaving `π_1, …, π_{n+1}` unchanged.  Consequently

* `π_i(f')` is bijective for `i ≤ n + 1`, and
* `π_{n+2}` of the *target* of `f'` is trivial,

which is exactly the surplus of surjectivity that upgrades "(N-1)-connected pair" to "N-connected
pair": the relative homotopy groups of the pair `(cyl f', X)` vanish in degrees `≤ n + 1`
(`Work.Serre.cylRelPi_vanish`), hence — transferring to the subspace `Set.range (cylIncl f')`
(`Work.Serre.RangeOne.subsingleton_relPi_range_cylIncl`), by the compression property
(`Work.RatHurewicz.compression_of_relPiVanishing`) and the relative cone construction
(`Work.Serre.serreE2b`, `Work.Serre.isIso_ratHomologyMap_setIncl_of_compressRel`) —
`H_t(X;ℚ) ≅ H_t(cyl f';ℚ)` for `t < N`.  Since the cylinder is homotopy equivalent to its target
and `H_t(Y;ℚ) ≅ H_t(KillCells (n+1) Y;ℚ)` for `t < N`
(`Work.Serre.isIso_ratHomologyMap_attachIncl_aux`), the composite `killIncl ∘ f` is a rational
homology isomorphism below `N`, and `f` follows by cancellation.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- **K2 (blueprint ADDENDUM 2).**  An `N`-connected map induces an isomorphism on rational homology
in degrees `< N`. -/
theorem serreK2Proved : Work.Serre.SerreK2 := by
  intro X Y _ _ hne f N h j hj
  have x₀ : X := hne.some
  by_cases hN : N ≤ 1
  · have hj0 : j = 0 := by omega
    subst hj0
    exact hZeroOfPiZero f (fun x => h 0 (by omega) x)
  · have hN2 : 2 ≤ N := by omega
    obtain ⟨n, hn⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    subst hn
    -- `h : ∀ i, i < n + 2 → ∀ x, Bijective (piMapN f i x)`, `hj : j < n + 2`
    -- ### the `π`-data of `f' = killIncl (n+1) Y ∘ f`
    have hbij : ∀ i : ℕ, i ≤ n + 1 → ∀ x : X,
        Function.Bijective (piMapN ((killIncl (n + 1) Y).comp f) i x) := by
      intro i hi x
      have h1 : Function.Bijective (piMapN (killIncl (n + 1) Y) i (f x)) :=
        (killCells_step (n + 1) Y).1 i hi (f x)
      have h2 : Function.Bijective (piMapN f i x) := h i (by omega) x
      rw [show piMapN ((killIncl (n + 1) Y).comp f) i x
          = (piMapN (killIncl (n + 1) Y) i (f x)) ∘ (piMapN f i x) from
        funext fun a => piMapN_comp f (killIncl (n + 1) Y) i x a]
      exact h1.comp h2
    -- ### `π_{n+2}` of the target of the cylinder inclusion of `f'` is trivial
    have hsub : ∀ y : cyl ((killIncl (n + 1) Y).comp f),
        Subsingleton (HomotopyGroup (Fin (n + 2)) (cyl ((killIncl (n + 1) Y).comp f)) y) :=
      fun y => subsingleton_pi_cyl_of_subsingleton _ (n + 1) y
        ((killCells_step (n + 1) Y).2.1 (cylRetract ((killIncl (n + 1) Y).comp f) y))
    -- ### the relative groups of the cylinder inclusion of `f'` vanish below `n + 2`
    have hrel : ∀ x : X, ∀ k : ℕ, k ≤ n + 1 → Subsingleton
        (Work.RatHurewicz.RelHomotopyGroup (cylIncl ((killIncl (n + 1) Y).comp f)) x k) := by
      intro x k hk
      refine cylRelPi_vanish ((killIncl (n + 1) Y).comp f) x n ?_ ?_ ?_ k hk
      · -- geometric `π₀`-injectivity of `cylIncl f'`
        intro x' hx'
        have h1 : Joined ((killIncl (n + 1) Y) (f x)) ((killIncl (n + 1) Y) (f x')) := by
          obtain ⟨γ⟩ := hx'
          have h3 : cylRetract ((killIncl (n + 1) Y).comp f)
                (cylIncl ((killIncl (n + 1) Y).comp f) x)
              = (killIncl (n + 1) Y) (f x) := by
            simpa using congrArg (fun g : C(X, KillCells (n + 1) Y) => g x)
              (cylRetract_cylIncl ((killIncl (n + 1) Y).comp f))
          have h4 : cylRetract ((killIncl (n + 1) Y).comp f)
                (cylIncl ((killIncl (n + 1) Y).comp f) x')
              = (killIncl (n + 1) Y) (f x') := by
            simpa using congrArg (fun g : C(X, KillCells (n + 1) Y) => g x')
              (cylRetract_cylIncl ((killIncl (n + 1) Y).comp f))
          exact ⟨(γ.map (cylRetract ((killIncl (n + 1) Y).comp f)).continuous).cast h3 h4⟩
        have h2 : Joined (f x) (f x') :=
          joined_of_piMapN_zero_injective (killIncl (n + 1) Y) (f x)
            ((killCells_step (n + 1) Y).1 0 (by omega) (f x)).1 h1
        exact joined_of_piMapN_zero_injective f x (h 0 (by omega) x).1 h2
      · -- injectivity of `π_m(cylIncl f')` for `m ≤ n`
        intro m hm
        exact (bijective_piMapN_cylIncl ((killIncl (n + 1) Y).comp f) (m + 1) (by omega) x
          (hbij (m + 1) (by omega) x)).1
      · -- surjectivity of `π_m(cylIncl f')` for `m ≤ n + 1`
        intro m hm
        rcases lt_or_eq_of_le hm with hlt | heq
        · exact (bijective_piMapN_cylIncl ((killIncl (n + 1) Y).comp f) (m + 1) (by omega) x
            (hbij (m + 1) (by omega) x)).2
        · subst heq
          intro b
          exact ⟨1, (hsub (cylIncl ((killIncl (n + 1) Y).comp f) x)).elim _ _⟩
    -- ### transfer to the subspace `Set.range (cylIncl f')`
    have hset : ∀ a : ↥(Set.range (cylIncl ((killIncl (n + 1) Y).comp f))), ∀ k : ℕ, k ≤ n + 1 →
        Subsingleton (Work.RatHurewicz.RelHomotopyGroup
          (Work.RatHurewicz.setIncl
            (Set.range (cylIncl ((killIncl (n + 1) Y).comp f)))) a k) := by
      intro a k hk
      obtain ⟨x, hx⟩ := a.2
      have hEq : (⟨cylIncl ((killIncl (n + 1) Y).comp f) x, x, rfl⟩
          : ↥(Set.range (cylIncl ((killIncl (n + 1) Y).comp f)))) = a := Subtype.ext hx
      exact hEq ▸ (RangeOne.subsingleton_relPi_range_cylIncl ((killIncl (n + 1) Y).comp f) x k
        (hrel x k hk))
    -- ### compression of the pair `(cyl f', range (cylIncl f'))` in dimensions `≤ n + 2`
    have hcomp : ∀ d : ℕ, d ≤ n + 2 →
        Work.RatHurewicz.CompressRel (cyl ((killIncl (n + 1) Y).comp f))
          (Set.range (cylIncl ((killIncl (n + 1) Y).comp f))) d := by
      have h := Work.RatHurewicz.compression_of_relPiVanishing
        (Y := cyl ((killIncl (n + 1) Y).comp f))
        (A := Set.range (cylIncl ((killIncl (n + 1) Y).comp f))) (n + 1)
        (RangeOne.cyl_joined_range ((killIncl (n + 1) Y).comp f) x₀ (hbij 0 (by omega) x₀))
        (fun a k hk => hset a k hk)
      intro d hd
      exact h d (by omega)
    have hsetiso : ∀ t : ℕ, t < n + 2 → IsIso (ratHomologyMap
        (Work.RatHurewicz.setIncl
          (Set.range (cylIncl ((killIncl (n + 1) Y).comp f)))) t) :=
      fun t ht => isIso_ratHomologyMap_setIncl_of_compressRel hcomp t ht
    -- ### the homology isomorphism for the cylinder inclusion of `f'`
    obtain ⟨ec, hec⟩ := cylHomeoExplicit ((killIncl (n + 1) Y).comp f)
    have hcylincl : ∀ t : ℕ, t < n + 2 →
        IsIso (ratHomologyMap (cylIncl ((killIncl (n + 1) Y).comp f)) t) := by
      intro t ht
      let ecm : C(X, ↥(Set.range (cylIncl ((killIncl (n + 1) Y).comp f)))) :=
        ec.toHomotopyEquiv.toFun
      have hfact : (Work.RatHurewicz.setIncl
            (Set.range (cylIncl ((killIncl (n + 1) Y).comp f)))).comp ecm
          = cylIncl ((killIncl (n + 1) Y).comp f) :=
        ContinuousMap.ext (fun x => hec x)
      have hsplit : ratHomologyMap (cylIncl ((killIncl (n + 1) Y).comp f)) t
          = ratHomologyMap ecm t ≫ ratHomologyMap (Work.RatHurewicz.setIncl
              (Set.range (cylIncl ((killIncl (n + 1) Y).comp f)))) t := by
        rw [← ratHomologyMap_comp ecm
          (Work.RatHurewicz.setIncl
            (Set.range (cylIncl ((killIncl (n + 1) Y).comp f)))) t, hfact]
      rw [hsplit]
      have h1 : IsIso (ratHomologyMap ecm t) :=
        IsRatHomologyIso.of_homotopyEquiv ec.toHomotopyEquiv t
      have h2 : IsIso (ratHomologyMap (Work.RatHurewicz.setIncl
          (Set.range (cylIncl ((killIncl (n + 1) Y).comp f)))) t) := hsetiso t ht
      infer_instance
    -- ### the homology isomorphism for `f'` (retraction of the cylinder)
    have hisoF' : ∀ t : ℕ, t < n + 2 →
        IsIso (ratHomologyMap ((killIncl (n + 1) Y).comp f) t) := by
      intro t ht
      obtain ⟨E, hE⟩ := cylHomotopyEquivExplicit ((killIncl (n + 1) Y).comp f)
      have hret : IsIso (ratHomologyMap (cylRetract ((killIncl (n + 1) Y).comp f)) t) := by
        have h1 : IsIso (ratHomologyMap E.toFun t) := IsRatHomologyIso.of_homotopyEquiv E t
        rwa [hE] at h1
      have hff : ratHomologyMap ((killIncl (n + 1) Y).comp f) t
          = ratHomologyMap (cylIncl ((killIncl (n + 1) Y).comp f)) t
            ≫ ratHomologyMap (cylRetract ((killIncl (n + 1) Y).comp f)) t := by
        rw [← ratHomologyMap_comp (cylIncl ((killIncl (n + 1) Y).comp f))
          (cylRetract ((killIncl (n + 1) Y).comp f)) t,
          cylRetract_cylIncl ((killIncl (n + 1) Y).comp f)]
      rw [hff]
      have h1 := hcylincl t ht
      have h2 := hret
      infer_instance
    -- ### the homology isomorphism for `killIncl (n+1) Y`
    have hisoK : ∀ t : ℕ, t < n + 2 → IsIso (ratHomologyMap (killIncl (n + 1) Y) t) :=
      fun t ht => isIso_ratHomologyMap_attachIncl_aux (n + 1) Y
        (C(Work.RatHurewicz.cellSphere (n + 1), Y)) (fun g => g) t (by omega)
    -- ### conclude for `f`
    haveI h1 : IsIso (ratHomologyMap ((killIncl (n + 1) Y).comp f) j) := hisoF' j hj
    haveI h2 : IsIso (ratHomologyMap (killIncl (n + 1) Y) j) := hisoK j hj
    have h3 : ratHomologyMap ((killIncl (n + 1) Y).comp f) j
        ≫ inv (ratHomologyMap (killIncl (n + 1) Y) j) = ratHomologyMap f j := by
      rw [ratHomologyMap_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← h3]
    infer_instance

end

end Work.Serre
