import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.serreE3a
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.RatHurewicz.trackFibreHomeo
import Submission.Work.Serre.serreRangeEMVanAll
import Submission.Work.Serre.MapPathDefs
import Submission.Work.Serre.mpathQ_isSerreFibration
import Submission.Work.Serre.mpathQ_fibreHomeo
import Submission.Work.Serre.mpathFst_ratHomologyIso
import Submission.Work.Serre.strictFibre_ratH_homotopyFibre
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.OneCell.pathConnectedSpace_of_ratH_zero_iso

/-!
# The mapping theorem for an arbitrary map with rationally acyclic homotopy fibre

`Work.Serre.SerreE3a` is Serre's mapping theorem for a **Serre fibration** `p : E → B`: if the
homotopy fibre of `p` over `e₀` is rationally acyclic below `N`, then `p` is a rational homology
isomorphism in degrees `< N`.

The theorem proved here is the same statement for an **arbitrary continuous map** `f : A → X`
(so `Work.Serre.SerreE3a` itself is *not* applicable directly, `f` need not be a fibration).

The proof is the standard replacement of `f` by a fibration: the **mapping path space**

`mpath f = {x : A × C(I,X) // x.2 0 = f x.1}`,  `mpathQ f (a,γ) = γ 1`,

with the projection `mpathFst f (a,γ) = a`.  Then

* `mpathQ f` is a Serre fibration for *every* `f` (`Work.Serre.mpathQ_isSerreFibration`),
* `mpathFst f` is a homotopy equivalence (`Work.Serre.mpathFst_ratHomologyIso`),
* `f ∘ mpathFst f` is homotopic to `mpathQ f` (`Work.Serre.mpath_homotopic`), and
* the fibre of `mpathQ f` over `f a₀` is homeomorphic to the homotopy fibre of `f`
  (`Work.Serre.mpathQ_fibreHomeo`), while for a Serre fibration over a path connected base the
  strict fibre and the homotopy fibre have the same rational homology in every degree
  (`Work.Serre.strictFibre_ratH_homotopyFibre`).

Hence `SerreE3a` applies to `mpathQ f`, and the conclusion about `f` follows by functoriality of
`ratHomologyMap` and its homotopy invariance.
-/

namespace Work.Stems

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

set_option maxHeartbeats 800000

/-- **`H₀(X;ℚ) ≅ ℚ` makes `X → *` a rational isomorphism in degree `0`.**

`H₀(X;ℚ)` is the free `ℚ`-module on `π₀(X)`; being one-dimensional it forces `X` to be path
connected (`Work.Serre.OneCell.pathConnectedSpace_of_ratH_zero_iso`), and for a path connected space
the augmentation `H₀(X;ℚ) → ℚ` is an isomorphism
(`Work.Serre.isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0`). -/
theorem isIso_toPoint_zero_of_ratH_zero_iso {X : Type} [TopologicalSpace X]
    (h : Nonempty (Work.Serre.ratH (TopCat.of X) 0 ≅ ModuleCat.of ℚ ℚ)) :
    IsIso (Work.Serre.ratHomologyMap (Work.Serre.toPoint X) 0) := by
  haveI : PathConnectedSpace X := Work.Serre.OneCell.pathConnectedSpace_of_ratH_zero_iso h
  exact Work.Serre.isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 X (Classical.arbitrary X)
    (Work.Serre.subsingleton_pi0_of_pathConnectedSpace X _)

/-- **`RatAcyclicBelow` descends along a degreewise isomorphism of rational homology.**  If `X` is
rationally acyclic below `N` and `H_j(X;ℚ) ≅ H_j(Y;ℚ)` for all `j`, then `Y` is rationally acyclic
below `N`.  (The degree `0` condition is the only place where the isomorphism in degree `0` is
used beyond the vanishing statement.) -/
theorem ratAcyclicBelow_of_ratH_iso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {N : ℕ} (h : Work.Serre.RatAcyclicBelow X N)
    (e : ∀ j : ℕ, Nonempty (Work.Serre.ratH (TopCat.of X) j ≅ Work.Serre.ratH (TopCat.of Y) j)) :
    Work.Serre.RatAcyclicBelow Y N := by
  haveI : IsIso (Work.Serre.ratHomologyMap (Work.Serre.toPoint X) 0) := h.2
  refine ⟨fun t ht htN => IsZero.of_iso (h.1 t ht htN) (e t).some.symm, ?_⟩
  exact isIso_toPoint_zero_of_ratH_zero_iso
    ⟨(e 0).some.symm ≪≫
      (asIso (Work.Serre.ratHomologyMap (Work.Serre.toPoint X) 0) ≪≫
        (Work.Serre.ratH_zero_of_pathConnected PUnit).some)⟩

/-- **The mapping theorem for an arbitrary continuous map whose homotopy fibre is rationally
acyclic below `N`** (Serre's mapping theorem, without assuming that the map is a fibration).

Given `Work.Serre.SerreE3a` (the mapping theorem for Serre fibrations), an arbitrary map
`f : A → X` with `X` path connected, a base point `a₀ : A` and `N : ℕ`: if the homotopy fibre of
`f` over `a₀` is rationally acyclic below `N` (`H_t = 0` for `0 < t ≤ N` and `H_0 ≅ ℚ`), then
`H_i(A;ℚ) ≅ H_i(X;ℚ)` for every `i < N`.

Proof: apply `SerreE3a` to the fibration `mpathQ f : mpath f → X` of the mapping path space, whose
homotopy fibre at the canonical base point has the rational homology of the homotopy fibre of `f`
in every degree; then transport back along the homotopy equivalence `mpathFst f` and the homotopy
`f ∘ mpathFst f ~ mpathQ f`. -/
theorem mappingTheoremOfHomotopyFibreAcyclic (hE3a : Work.Serre.SerreE3a)
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X] [PathConnectedSpace X]
    (f : C(A, X)) (a₀ : A) (N : ℕ)
    (h : Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre f a₀) N) :
    ∀ i : ℕ, i < N → Nonempty (Work.Serre.ratH (TopCat.of A) i ≅ Work.Serre.ratH (TopCat.of X) i) := by
  intro i hi
  -- the mapping path space fibration
  have hp : Work.StemsB.IsSerreFibration (Work.Serre.mpathQ f) :=
    Work.Serre.mpathQ_isSerreFibration f
  -- its strict fibre over `f a₀` is the homotopy fibre of `f`, hence acyclic below `N`
  have hFib : Work.Serre.RatAcyclicBelow
      (Work.RatHurewicz.homotopyFibre (Work.Serre.mpathQ f) (Work.Serre.mpathOf f a₀)) N := by
    obtain ⟨e⟩ := Work.Serre.mpathQ_fibreHomeo f a₀
    refine ratAcyclicBelow_of_ratH_iso
      (Work.Serre.ratAcyclicBelow_of_homotopyEquiv e.toHomotopyEquiv h) (fun j => ?_)
    exact Work.Serre.strictFibre_ratH_homotopyFibre (Work.Serre.mpathQ f) hp
      (Work.Serre.mpathOf f a₀) (f a₀) inferInstance j
  -- the mapping theorem for the fibration `mpathQ f`
  have hiso : IsIso (Work.Serre.ratHomologyMap (Work.Serre.mpathQ f) i) :=
    hE3a (Work.Serre.mpath f) X (Work.Serre.mpathQ f) (Work.Serre.mpathOf f a₀) N hp
      inferInstance hFib i hi
  -- `mpathFst f` is a homotopy equivalence and `f ∘ mpathFst f ~ mpathQ f`
  haveI : IsIso (Work.Serre.ratHomologyMap (Work.Serre.mpathFst f) i) :=
    Work.Serre.mpathFst_ratHomologyIso f i
  have hcomp : Work.Serre.ratHomologyMap (f.comp (Work.Serre.mpathFst f)) i
      = Work.Serre.ratHomologyMap (Work.Serre.mpathFst f) i ≫ Work.Serre.ratHomologyMap f i :=
    Work.Serre.ratHomologyMap_comp (Work.Serre.mpathFst f) f i
  have heq : Work.Serre.ratHomologyMap (f.comp (Work.Serre.mpathFst f)) i
      = Work.Serre.ratHomologyMap (Work.Serre.mpathQ f) i :=
    Work.Serre.ratHomologyMap_eq_of_homotopic (Work.Serre.mpath_homotopic f).some i
  haveI h2 : IsIso (Work.Serre.ratHomologyMap (Work.Serre.mpathFst f) i ≫
      Work.Serre.ratHomologyMap f i) := by
    rw [← hcomp, heq]; exact hiso
  haveI : IsIso (Work.Serre.ratHomologyMap f i) :=
    IsIso.of_isIso_comp_left (Work.Serre.ratHomologyMap (Work.Serre.mpathFst f) i)
      (Work.Serre.ratHomologyMap f i)
  exact ⟨asIso (Work.Serre.ratHomologyMap f i)⟩

end

end Work.Stems
