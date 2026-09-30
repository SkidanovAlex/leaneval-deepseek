import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMODD.cohHomology
import Submission.Work.Pi6.EMODD.ssForcing
import Submission.Work.Pi6.EMODD.finDimField
import Submission.Work.Pi6.EMM2.SSKit
import Submission.Work.Pi6.EMM2.Final
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.StemsB.S0SubspaceRat
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.EMFG.emHomologyFG
import Submission.Work.SSS.serreFGThreeForTwo
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The loop step for `Work.Pi6.EMOdd`

If `X` is a range model of `K(ℤ/2,n+1)` through `N ≥ 10` and the mod-`p` homology of its loop space
`ΩX = Path x₀ x₀` vanishes in degrees `1, …, 8` (for an odd prime `p`), then so does the mod-`p`
homology of `X` in those degrees.

The proof uses the **path–loop fibration** `ΩX → PX → X`, whose total space is contractible and
whose strict fibre is the loop space.  The multiplicative Serre spectral sequence of that fibration
(`Work.Pi6.MSSHolds`, which the area takes as a hypothesis) together with the forcing lemma
`Work.Pi6.EMODD.ssForcing` part (A) gives the vanishing of the *cohomology* `H^s(X;𝔽_p)` for
`1 ≤ s ≤ 8`; the field-coefficient duality `Work.Pi6.EMODD.isZero_cohomology_iff_subsingleton_homology`
converts this back to the vanishing of the homology.

The input `MSSHolds` requires finite-dimensionality of the cohomology of the base and of the fibre
in the range: for the fibre this is immediate (the positive-degree groups vanish), for the base it
is `Work.Pi6.EMODD.finDimField`, from the finite generatedness of the integral homology of a range
model of `K(ℤ/2,n+1)` (`Work.EMFG.emHomologyFG`).
-/

set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMODD

theorem emOddLoop (p : ℕ) [Fact p.Prime] (hM : Work.Pi6.MSSHolds)
    (n N : ℕ) (hn : 2 ≤ n) (hN : 10 ≤ N) (X : Type) [TopologicalSpace X] (x₀ : X)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) (n + 1) (by omega) N X x₀)
    (hloop : ∀ i : ℕ, 0 < i → i ≤ 8 →
      Subsingleton (Work.Pi6.HR (ZMod p) (Path x₀ x₀) i)) :
    ∀ i : ℕ, 0 < i → i ≤ 8 → Subsingleton (Work.Pi6.HR (ZMod p) X i) := by
  classical
  -- ## The low homotopy groups of `X` and the basic spaces of the fibration
  have h0X : Subsingleton (HomotopyGroup (Fin 0) X x₀) := hX.2 0 (by omega) (Or.inl (by omega))
  have h1X : Subsingleton (HomotopyGroup (Fin 1) X x₀) := hX.2 1 (by omega) (Or.inl (by omega))
  haveI hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀ h0X
  haveI hcontrP : ContractibleSpace (Work.StemsB.PathSpace X x₀) :=
    Work.StemsB.contractible_pathSpace X x₀
  haveI hpcP : PathConnectedSpace (Work.StemsB.PathSpace X x₀) := inferInstance
  -- the total space, the base map, the base point and the fibre of the path–loop fibration
  let E := Work.StemsB.PathSpace X x₀
  let ev := Work.StemsB.evalOne X x₀
  let e₀ := Work.StemsB.constPath X x₀
  let F := Work.StemsB.fibre (Work.StemsB.evalOne X x₀) x₀
  have hev : Work.StemsB.IsSerreFibration ev := Work.StemsB.isSerreFibration_evalOne X x₀
  haveI hpcF : PathConnectedSpace F :=
    Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration ev hev x₀ hpcP hpcX h1X
  -- ## Vanishing of the mod-`p` cohomology of the fibre in degrees `1, …, 8`
  have hFibCoh : ∀ q : ℕ, 0 < q → q ≤ 8 → IsZero (Work.Pi6.Coh (ZMod p) F q) := by
    intro q hq hq8
    have h1 : IsZero (Work.Pi6.Coh (ZMod p) (Path x₀ x₀) q) :=
      (Work.Pi6.EMODD.isZero_cohomology_iff_subsingleton_homology (ZMod p) (Path x₀ x₀) q).mpr
        (hloop q hq hq8)
    exact IsZero.of_iso h1
      (Work.StemsB.cohomologyIsoOfHomeomorph (ZMod p) (Work.StemsB.fibreEvalOneHomeo X x₀) q).symm
  -- ## `H⁰` of the fibre is nontrivial
  have hFibNT : Nontrivial (↥(Work.Pi6.Coh (ZMod p) F 0)) := by
    obtain ⟨e⟩ := Work.Cohomology.singularCohomology_zero (ZMod p) (TopCat.of F)
    haveI : Nontrivial (↥(ModuleCat.of (ZMod p) (ZMod p))) := inferInstance
    exact Function.Injective.nontrivial (f := (⇑e.symm.toLinearEquiv)) e.symm.toLinearEquiv.injective
  -- ## Finiteness of the cohomology of the fibre in the range
  have hfinF : ∀ q : ℕ, q ≤ 8 → FiniteDimensional (ZMod p) (↥(Work.Pi6.Coh (ZMod p) F q)) := by
    intro q hq
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · subst h0
      obtain ⟨e⟩ := Work.Cohomology.singularCohomology_zero (ZMod p) (TopCat.of F)
      exact Module.Finite.equiv e.symm.toLinearEquiv
    · haveI : Subsingleton (↥(Work.Pi6.Coh (ZMod p) F q)) :=
        ModuleCat.subsingleton_of_isZero (hFibCoh q hpos hq)
      exact inferInstance
  -- ## Finiteness of the cohomology of `X` in the range, from `EMFG`
  have hFGX : Work.PiS.FGUpTo X 8 :=
    Work.EMFG.emHomologyFG Work.SSS.serreFGThreeForTwo (ZMod 2) (n + 1) (by omega) 8 X x₀
      (Work.Pi6.EMM2.emIsEMSpaceUpTo_mono (by omega : 9 ≤ N) hX)
  have hfinX : ∀ q : ℕ, q ≤ 8 → FiniteDimensional (ZMod p) (↥(Work.Pi6.Coh (ZMod p) X q)) :=
    Work.Pi6.EMODD.finDimField (ZMod p) (inferInstance) X 8 (fun i hi => hFGX i hi)
  -- ## The Serre spectral sequence of the path–loop fibration
  have hSC : Work.PiS.SimplyConn X x₀ := ⟨h0X, h1X⟩
  obtain ⟨S, hS⟩ := hM (ZMod p) E X ev e₀ 8 hev hSC
    hfinF hfinX
  -- ## The total space is contractible, so its cohomology vanishes in positive degrees
  have hTotSub : ∀ m : ℕ, 0 < m → m ≤ 8 → Subsingleton (↥(Work.Pi6.Coh (ZMod p) E m)) := by
    intro m hm0 _
    have hm : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
    have hz : IsZero (Work.Pi6.Coh (ZMod p) E m) := by
      rw [← hm]
      exact Work.Cohomology.contractible (ZMod p) (TopCat.of E) (m - 1)
    exact ModuleCat.subsingleton_of_isZero hz
  -- ## Forcing
  have hforc : ∀ s : ℕ, 0 < s → s ≤ 8 → IsZero (Work.Pi6.Coh (ZMod p) X s) :=
    (Work.Pi6.EMODD.ssForcing (𝕜 := ZMod p)).1 (p := ev) (e₀ := e₀) (N := 8) (S := S) hS
      hFibCoh hFibNT hTotSub
  -- ## Back to homology
  intro i hi0 hi8
  exact (Work.Pi6.EMODD.isZero_cohomology_iff_subsingleton_homology (ZMod p) X i).mp
    (hforc i hi0 hi8)

end Work.Pi6.EMODD
