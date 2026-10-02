import Mathlib
import Submission.Work.Stems.Engine.C2Range
import Submission.Work.RatHurewicz.oddCoverFreeTop
import Submission.Work.RatHurewicz.exists_bijective_piMapN_rangeModel
import Submission.Work.Serre.serreC0Range

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The free-top sphere route to the stable stems (odd spheres)

This module proves `Work.RatHurewicz.coverRouteFreeTop`, the free-top version of
`Work.Stems.Engine.coverRouteRange` (`Submission/Work/Stems/Engine/C2Range.lean`).  Two differences
from the range-form statement:

* the model of `K(ℤ,n)` is a **range model** (`Work.Serre.serreC0Range`, proved), not the unbounded
  `Work.Serre.SerreC0` (which is open: it would need an infinite cell attachment).  The bottom cell
  is `Work.RatHurewicz.exists_bijective_piMapN_rangeModel`;
* the odd step of `C2` is consumed in **free-top form** (`Work.RatHurewicz.OddCoverAcyclicUpTo`),
  with the acyclicity range of the cover as a free parameter, instead of the range-form
  `Work.Stems.Engine.C2oddRange` (whose range-capped producer is blocked: see
  `Submission/Work/Stems/EM_C2_RANGE_FINDING.md`).
-/

open CategoryTheory Limits
open Work.Serre
open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- **The homotopy fibre of a map to a `K(ℤ,n)` model is trivial in degrees `2 ≤ j ≤ n-2`**, with
the connectivity input restricted to the degrees below `n` — which is what a range model supplies.
(Proof copied from `Work.Serre.homotopyFibre_subsingleton_mid`, whose hypothesis is the unbounded
`∀ i, i ≠ n → …`.) -/
theorem homotopyFibre_subsingleton_mid_bd {X : Type} [TopologicalSpace X] {n : ℕ}
    (f : C(Sph n, X)) (s₀ : Sph n)
    (hX : ∀ i, i < n → Subsingleton (HomotopyGroup (Fin i) X (f s₀)))
    {j : ℕ} (hj : 2 ≤ j) (hjn : j + 1 < n) :
    Subsingleton (HomotopyGroup (Fin j) (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) := by
  have hkeq : (j-2) + 1 + 2 = j + 1 := by omega
  have hF : Subsingleton (HomotopyGroup (Fin ((j-2)+1+1)) (Work.RatHurewicz.fibreOf f s₀)
      (Work.RatHurewicz.fibreOfPt f s₀)) :=
    fibreOf_subsingleton f s₀ ((j-2)+1) (hX ((j-2)+1+2) (by rw [hkeq]; omega))
  have hidx : (j-2) + 1 + 1 = j := by omega
  have hE := Work.StemsB.les_exact_E (Work.RatHurewicz.homotopyFibreFst f s₀)
    (Work.RatHurewicz.homotopyFibreBasepoint f s₀) (Work.RatHurewicz.fibreHrel f s₀) (j-2)
  have hB : Subsingleton (HomotopyGroup (Fin ((j-2)+1+1)) (Sph n)
      ((Work.RatHurewicz.homotopyFibreFst f s₀)
        (Work.RatHurewicz.homotopyFibreBasepoint f s₀))) :=
    subsingleton_homotopyGroup_of_index_eq hidx.symm
      (Work.Stems.sphereConnectivity n j (by omega) s₀)
  have hsub : Subsingleton (HomotopyGroup (Fin ((j-2)+1+1)) (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) :=
    ⟨fun y z => by
      have hy : y ∈ Set.range (Work.StemsB.πmap
        (Work.StemsB.fibreIncl (Work.RatHurewicz.homotopyFibreFst f s₀)
          ((Work.RatHurewicz.homotopyFibreFst f s₀)
            (Work.RatHurewicz.homotopyFibreBasepoint f s₀)))
        ((j-2)+1) (Work.StemsB.fibrePoint (Work.RatHurewicz.homotopyFibreFst f s₀)
          (Work.RatHurewicz.homotopyFibreBasepoint f s₀))) :=
        (hE y).mp (hB.elim _ 1)
      have hz := (hE z).mp (hB.elim _ 1)
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      rw [← ha, ← hb]
      exact congrArg _ (hF.elim a b)⟩
  rwa [hidx] at hsub

/-- **The homotopy fibre of a map to a `K(ℤ,n)` model is trivial below `n-1`**, in the bounded form
(proof copied from `Work.Serre.homotopyFibre_subsingleton_of_lt`). -/
theorem homotopyFibre_subsingleton_of_lt_bd {X : Type} [TopologicalSpace X] {n : ℕ}
    (f : C(Sph n, X)) (s₀ : Sph n) (hn : 3 ≤ n)
    (hX : ∀ i, i < n → Subsingleton (HomotopyGroup (Fin i) X (f s₀)))
    {j : ℕ} (hj : j + 1 < n) :
    Subsingleton (HomotopyGroup (Fin j) (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) := by
  rcases j with _ | _ | j
  · exact subsingleton_pi0_homotopyFibre f s₀
      (fun a => (pathConnectedSpace_sph n (by omega)).joined s₀ a)
      (subsingleton_pi0_fibreOf f s₀ (hX 1 (by omega)))
  · haveI hF1 : Subsingleton (HomotopyGroup (Fin (0 + 1))
        (Work.StemsB.fibre (Work.RatHurewicz.homotopyFibreFst f s₀)
          ((Work.RatHurewicz.homotopyFibreFst f s₀)
            (Work.RatHurewicz.homotopyFibreBasepoint f s₀)))
        (Work.StemsB.fibrePoint (Work.RatHurewicz.homotopyFibreFst f s₀)
          (Work.RatHurewicz.homotopyFibreBasepoint f s₀))) := by
      haveI : Subsingleton (HomotopyGroup (Fin (0 + 2)) X (f s₀)) := hX 2 (by omega)
      exact (Work.RatHurewicz.pairShiftHom_bijective f s₀ 0).surjective.subsingleton
    haveI hB1 : Subsingleton (HomotopyGroup (Fin 1) (Sph n)
        ((Work.RatHurewicz.homotopyFibreFst f s₀)
          (Work.RatHurewicz.homotopyFibreBasepoint f s₀))) :=
      Work.Stems.sphereConnectivity n 1 (by omega) s₀
    exact (fibrationPiOne_surjective (Work.RatHurewicz.homotopyFibreFst f s₀)
      (Work.RatHurewicz.isSerreFibration_homotopyFibreFst f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀) hB1).subsingleton
  · exact homotopyFibre_subsingleton_mid_bd f s₀ hX (j := j + 2) (by omega) (by omega)

/-- **The free-top sphere route (odd spheres).**  This is `Work.Stems.Engine.coverRouteRange` with
the unbounded model replaced by a range model and `C2oddRange` by the free-top statement
`Work.RatHurewicz.OddCoverAcyclicUpTo`. -/
theorem coverRouteFreeTop (hC0 : Work.Serre.SerreC0Range)
    (hEM : Work.RatHurewicz.OddCoverAcyclicUpTo)
    (hS1 : Work.Serre.SerreS1)
    (n i : ℕ) (hn : 3 ≤ n) (hodd : Odd n) (hi : i + 5 ≤ n)
    (x₀ : Work.Serre.Sph n) :
    Work.Serre.PiTorsion (Work.Serre.Sph n) x₀ (n + i) := by
  obtain ⟨X, hXtop, pt, hXmodel⟩ :=
    hC0 (A := ℤ) n (4 * n + i + 4) (by omega) (by omega)
  letI : TopologicalSpace X := hXtop
  obtain ⟨s₀, f, hfs₀, hbij⟩ :=
    Work.RatHurewicz.exists_bijective_piMapN_rangeModel n (4 * n + i + 4) (by omega) X pt hXmodel
  set E := Work.RatHurewicz.homotopyFibre f s₀
  set e₀ := Work.RatHurewicz.homotopyFibreBasepoint f s₀
  -- the range model is trivial below `n`
  have hXlow : ∀ j, j < n → Subsingleton (HomotopyGroup (Fin j) X (f s₀)) :=
    fun j hj => hfs₀ ▸ hXmodel.2 j (by omega) (Or.inl hj)
  -- and (up to its range) above `n`
  have hXhigh : ∀ j, j ≠ n → j ≤ 4 * n + i + 4 →
      Subsingleton (HomotopyGroup (Fin j) X (f s₀)) :=
    fun j hj hjN => hfs₀ ▸ hXmodel.2 j hj (Or.inr hjN)
  -- the acyclicity of `E` (the free-top odd step of `C2`)
  have hvan : ∀ m : ℕ, n - 1 ≤ m + 1 → m + 1 ≤ 2 * (n - 1) - 2 →
      IsZero (ratH (TopCat.of E) (m + 1)) :=
    fun m hm1 hm2 => hEM n (2 * (n - 1) - 2) (4 * n + i + 4) hn hodd (by omega) X pt hXmodel
      s₀ f hbij (m + 1) (by omega) (by omega)
  -- `E` is `(n-2)`-connected
  have hconn : ∀ j < n - 1, Subsingleton (HomotopyGroup (Fin j) E e₀) :=
    fun j hj => homotopyFibre_subsingleton_of_lt_bd f s₀ hn hXlow (j := j) (by omega)
  have hEtors : PiTorsion E e₀ (n + i - 1 + 1) := by
    have h1 : n - 1 ≤ n + i - 1 + 1 + 1 := by omega
    have h2 : n + i - 1 + 1 + 1 ≤ 2 * (n - 1) - 2 := by omega
    exact hS1 (n - 1) (by omega) E e₀ hconn (2 * (n - 1) - 2) (by omega)
      (fun m h1' h2' => hvan m h1' h2') (n + i - 1 + 1) h1 h2
  -- the projection `E → Sⁿ` is onto in `π_{n+i+1}`
  have hF : Subsingleton (HomotopyGroup (Fin (n + i - 1 + 1)) (Work.RatHurewicz.fibreOf f s₀)
      (Work.RatHurewicz.fibreOfPt f s₀)) :=
    fibreOf_subsingleton f s₀ (n + i - 1)
      (subsingleton_homotopyGroup_of_index_eq (a := n + i + 1) (b := (n + i - 1) + 2)
        (by omega) (hXhigh (n + i + 1) (by omega) (by omega)))
  have hsurj := piMap_fst_surjective_of_fibre_trivial f s₀ (n + i - 1) hF
  have htor : PiTorsion (Sph n) (Work.RatHurewicz.homotopyFibreFst f s₀
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) (n + i - 1 + 1) :=
    piTorsion_of_surjective_hom (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀)
      (n + i - 1 + 1) (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) hsurj hEtors
  have htor' : PiTorsion (Sph n) (Work.RatHurewicz.homotopyFibreFst f s₀
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) (n + i) :=
    piTorsion_of_index_eq _ (by omega : n + i - 1 + 1 = n + i) htor
  exact piTorsion_of_joined (n + i)
    ((pathConnectedSpace_sph n (by omega)).joined s₀ x₀) htor'

end

end Work.RatHurewicz
