import Mathlib
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.RatHurewicz.coverRouteFreeTop
import Submission.Work.RatHurewicz.freudenthalTorsionTransfer
import Submission.Work.Stems.stableStemsTorsion_of_stable3

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The free-top route to the stable stems, on **range models**

`Work.RatHurewicz.coverRouteFreeTop` (`Submission/Work/RatHurewicz/coverRouteFreeTop.lean`) proves
the odd-sphere case of the stable-stems theorem from the *free-top* odd step of the `C2` layer,
`Work.RatHurewicz.OddCoverAcyclicUpTo`, which asks the cover of `Sⁿ` to be rationally acyclic in
**all** degrees up to its parameter `M`.

As it is stated, `M` is unbounded, and that is not what the engine can prove: the rational homology
of the fibre `ΩX = K(ℤ,n-1)` is known only through degree `2(n-1)-1 = 2n-3` (the bound `4j-1` of
`Work.Stems.Engine.C2evenRangeModel`, which is in turn the reach of the periodicity
`⌣e : H^m ≅ H^{m+2j}`), so the long exact sequence of the cover sees the fibre only up to degree
`2n-4`.  This file therefore works with the capped statement
`Work.Stems.Engine.OddCoverAcyclicRange` (`M ≤ 2n-4`, `N ≥ 2n-3`), which *is* the shape the sphere
route consumes (`M = 2(n-1)-2 = 2n-4`), and redoes the two bookkeeping lemmas of
`coverRouteFreeTop`/`sphereRouteAssembly` against it:

* `coverRouteFreeTopRange` — the odd-sphere case for `i + 5 ≤ n`;
* `piTorsion_sphere_of_freeTopInputs` — the whole stable-stems statement, with the even spheres and
  the boundary stems reached by Freudenthal suspensions.

The improvement over `Work.Stems.Engine.stableStemsTorsion_of_rangeInputs` is that the model of
`K(ℤ,n)` comes from `Work.Serre.SerreC0Range` (range models, **proved**) instead of the unbounded
`Work.Serre.SerreC0` (which would need an infinite cell attachment). -/

open CategoryTheory Limits
open Work.Serre
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems.Engine

noncomputable section

/-- **The free-top sphere route (odd spheres), for range models.**  `Work.RatHurewicz.coverRouteFreeTop`
with the free-top odd step replaced by the capped `Work.Stems.Engine.OddCoverAcyclicRange` (the
range the sphere route uses). -/
theorem coverRouteFreeTopRange (hC0 : Work.Serre.SerreC0Range)
    (hOdd : Work.Stems.Engine.OddCoverAcyclicRange)
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
  have hXlow : ∀ j, j < n → Subsingleton (HomotopyGroup (Fin j) X (f s₀)) :=
    fun j hj => hfs₀ ▸ hXmodel.2 j (by omega) (Or.inl hj)
  have hXhigh : ∀ j, j ≠ n → j ≤ 4 * n + i + 4 →
      Subsingleton (HomotopyGroup (Fin j) X (f s₀)) :=
    fun j hj hjN => hfs₀ ▸ hXmodel.2 j hj (Or.inr hjN)
  have hvan : ∀ m : ℕ, n - 1 ≤ m + 1 → m + 1 ≤ 2 * (n - 1) - 2 →
      IsZero (ratH (TopCat.of E) (m + 1)) :=
    fun m hm1 hm2 => hOdd n (2 * (n - 1) - 2) (4 * n + i + 4) hn hodd (by omega) (by omega)
      X pt hXmodel s₀ f hbij (m + 1) (by omega) (by omega)
  have hconn : ∀ j < n - 1, Subsingleton (HomotopyGroup (Fin j) E e₀) :=
    fun j hj => Work.RatHurewicz.homotopyFibre_subsingleton_of_lt_bd f s₀ hn hXlow (j := j)
      (by omega)
  have hEtors : PiTorsion E e₀ (n + i - 1 + 1) := by
    have h1 : n - 1 ≤ n + i - 1 + 1 + 1 := by omega
    have h2 : n + i - 1 + 1 + 1 ≤ 2 * (n - 1) - 2 := by omega
    exact hS1 (n - 1) (by omega) E e₀ hconn (2 * (n - 1) - 2) (by omega)
      (fun m h1' h2' => hvan m h1' h2') (n + i - 1 + 1) h1 h2
  have hF : Subsingleton (HomotopyGroup (Fin (n + i - 1 + 1)) (Work.RatHurewicz.fibreOf f s₀)
      (Work.RatHurewicz.fibreOfPt f s₀)) :=
    Work.Serre.fibreOf_subsingleton f s₀ (n + i - 1)
      (Work.Serre.subsingleton_homotopyGroup_of_index_eq (a := n + i + 1) (b := (n + i - 1) + 2)
        (by omega) (hXhigh (n + i + 1) (by omega) (by omega)))
  have hsurj := Work.Serre.piMap_fst_surjective_of_fibre_trivial f s₀ (n + i - 1) hF
  have htor : PiTorsion (Sph n) (Work.RatHurewicz.homotopyFibreFst f s₀
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) (n + i - 1 + 1) :=
    Work.Serre.piTorsion_of_surjective_hom (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀)
      (n + i - 1 + 1) (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) hsurj hEtors
  have htor' : PiTorsion (Sph n) (Work.RatHurewicz.homotopyFibreFst f s₀
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) (n + i) :=
    Work.Serre.piTorsion_of_index_eq _ (by omega : n + i - 1 + 1 = n + i) htor
  exact Work.Serre.piTorsion_of_joined (n + i)
    ((pathConnectedSpace_sph n (by omega)).joined s₀ x₀) htor'

/-- **The full stable-stems statement on spheres**, from the free-top sphere route on range models
and Freudenthal's suspension theorem. -/
theorem piTorsion_sphere_of_freeTopInputs (hC0 : Work.Serre.SerreC0Range)
    (hOdd : Work.Stems.Engine.OddCoverAcyclicRange)
    (hS1 : Work.Serre.SerreS1)
    (hF : Work.Stems.FreudenthalTorsionTransfer) :
    ∀ (i n : ℕ), i + 3 ≤ n → ∀ x₀ : Work.Serre.Sph n,
      Work.Serre.PiTorsion (Work.Serre.Sph n) x₀ (n + i) := by
  intro i n hn x₀
  have far : ∀ m : ℕ, i + 5 ≤ m → ∀ x₀ : Work.Serre.Sph m,
      Work.Serre.PiTorsion (Work.Serre.Sph m) x₀ (m + i) := by
    intro m hm5 x₀
    rcases Nat.even_or_odd m with he | ho
    · refine hF m i (by omega) (by omega) (fun y₀ => ?_) x₀
      exact Work.Serre.piTorsion_of_index_eq y₀ (by omega : (m + 1) + i = m + i + 1)
        (coverRouteFreeTopRange hC0 hOdd hS1 (m + 1) i (by omega)
          (Work.Serre.odd_succ_of_even he) (by omega) y₀)
    · exact coverRouteFreeTopRange hC0 hOdd hS1 m i (by omega) ho hm5 x₀
  by_cases h5 : i + 5 ≤ n
  · exact far n h5 x₀
  · by_cases h4 : i + 4 ≤ n
    · exact hF n i (by omega) (by omega)
        (fun y₀ => Work.Serre.piTorsion_of_index_eq y₀ (by omega : (n + 1) + i = n + i + 1)
          (far (n + 1) (by omega) y₀)) x₀
    · exact hF n i (by omega) (by omega)
        (fun y₀ => Work.Serre.piTorsion_of_index_eq y₀ (by omega : (n + 1) + i = n + i + 1)
          (hF (n + 1) i (by omega) (by omega)
            (fun z₀ => Work.Serre.piTorsion_of_index_eq z₀
              (by omega : (n + 2) + i = n + 1 + i + 1) (far (n + 2) (by omega) z₀)) y₀)) x₀

/-- **The drive's contract `Work.Drive.StableStemsTorsion` from the free-top inputs.** -/
theorem stableStemsTorsion_of_freeTopInputs (hC0 : Work.Serre.SerreC0Range)
    (hOdd : Work.Stems.Engine.OddCoverAcyclicRange)
    (hS1 : Work.Serre.SerreS1)
    (hF : Work.Stems.FreudenthalTorsionTransfer) :
    Work.Drive.StableStemsTorsion := by
  intro i hi n hn x₀ α
  exact piTorsion_sphere_of_freeTopInputs hC0 hOdd hS1 hF i n hn x₀ α

end

end Work.Stems.Engine
