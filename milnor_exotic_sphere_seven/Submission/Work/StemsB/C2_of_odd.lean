import Mathlib
import Submission.Work.StemsB.RangeModelPlan
import Submission.Work.StemsB.rangeModel_ratH_iso
import Submission.Work.Serre.serreC0Range
import Submission.Work.Stems.Engine.C2FreeTop
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.RatHurewicz.fibreRangeVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `C2RatSphereRange` from the **odd** free-top interface alone

`Work.StemsB.C2RatSphereRange` (the C2 input of this area's reduction of
`Work.RatHurewicz.RangeModelRatAcyclic`) is the fixed-top statement: for `k ≥ 1` and a *range model*
of `K(ℤ,k)` through `N ≥ 2k-1`, one has `H_k ≅ ℚ` and `H_i = 0` for `0 < i ≤ 2k-1`, `i ≠ k`.

The free-top interface of area STEMS (`Submission/Work/Stems/Engine/C2FreeTop.lean`) splits this
into an *even* and an *odd* obligation, `C2evenFree c` and `C2oddFree c`.  This file shows that the
**odd** one alone suffices:

```
Work.Stems.Engine.C2oddFree c  ⟹  Work.StemsB.C2RatSphereRange.
```

* **Odd `k`** is immediate: the fixed top `2k-1` is inside the odd interface, whose bound
  `N - c·k` can be made `≥ 2k` by passing to a range model with a larger top
  (`Work.StemsB.rangeModel_ratH_iso` transfers back, since the comparison is available in every
  degree below the *given* top).
* **Even `k`** is the path–loop fibration `ΩX → PX → X` of the enlarged model `X`: the total space
  is contractible, the base has connectivity `k`, and the fibre is `ΩX`, a range model of `K(ℤ,k-1)`
  through `top - 1` (`Work.Stems.isEMSpaceUpTo_loop'`) — hence, by the odd interface, a rational
  `S^{k-1}` through that degree.  The **pair comparison** in the stable range (proved:
  `Work.Serre.ratSerrePairComparison`, consumed through `Work.RatHurewicz.fibreRangeVanishing`)
  then gives the generator `H_k(X;ℚ) ≅ ℚ` and the vanishing `H_i(X;ℚ) = 0` for
  `1 ≤ i ≤ min (top-1-c(k-1)) (2k-2)`, `i ≠ k`, i.e. up to degree `2k-2`.
  The **remaining degree `2k-1`** (the only place where the pair comparison falls one degree short)
  is obtained by the *loop shift* to `K(ℤ,k+1)`: for a range model `Y` of `K(ℤ,k+1)`, the path–loop
  fibration of `Y` has base connectivity `k+1` and fibre parameter `k`, hence reaches
  `b + f - 1 = 2k` (`loopShiftIso` below), so `H_{2k-1}(X) ≅ H_{2k}(Y)`, and the odd interface for
  `Y` (index `k+1`, odd) gives `H_{2k}(Y;ℚ) = 0`.

No Euler class / Gysin statement (`Work.Serre.SerreE3b`, `GysinRangeFree`, `FibreRangeGysin`) is
used anywhere.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB

noncomputable section

/-- **A fixed-top instance transfers from a larger range model to the given one.** -/
theorem c2Transfer {k N : ℕ} (hk : 2 ≤ k) (hN : 2 * k - 1 ≤ N)
    {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (x : X) (x' : X')
    (hX : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) N X x)
    (hX' : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) N X' x')
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of X') k ≅ ModuleCat.of ℚ ℚ))
    (hvan : ∀ i : ℕ, 0 < i → i ≤ 2 * k - 1 → i ≠ k →
      IsZero (Work.Serre.ratH (TopCat.of X') i)) :
    Nonempty (Work.Serre.ratH (TopCat.of X) k ≅ ModuleCat.of ℚ ℚ) ∧
      ∀ i : ℕ, 0 < i → i ≤ 2 * k - 1 → i ≠ k →
        IsZero (Work.Serre.ratH (TopCat.of X) i) := by
  constructor
  · obtain ⟨e⟩ := rangeModel_ratH_iso ℤ k N hk X x hX X' x' hX' k (by omega)
    exact ⟨e ≪≫ hgen.some⟩
  · intro i hi1 hi2 hik
    obtain ⟨e⟩ := rangeModel_ratH_iso ℤ k N hk X x hX X' x' hX' i (by omega)
    exact IsZero.of_iso (hvan i hi1 hi2 hik) e

/-- **The loop-shift isomorphism in homology for range models.**  Let `Y` be a range model of
`K(ℤ,k+1)` through a top `T` (`k ≥ 2`) whose strict fibre of `evalOne` is rationally acyclic in
degrees `0 < j < k`, and `X` a range model of `K(ℤ,k)` through `N ≥ i`, with `N ≤ T - 1`.  Then

  `H_i(X;ℚ) ≅ H_{i+1}(Y;ℚ)`  for `i + 1 ≤ 2k`.

The isomorphism composes the comparison of the two range models of `K(ℤ,k)`
(`Work.StemsB.rangeModel_ratH_iso`), the identification of the strict fibre of `evalOne` with the
loop space (`Work.Serre.strictFibre_ratH_homotopyFibre`,
`Work.Stems.homotopyFibre_evalOne_equiv_loop`) and the two-step long exact sequence computation of
the path–loop fibration `H_j(Y) ≅ H_j(Y,{y}) ≅ H_j(PY, Fib) ≅ H_{j-1}(Fib)`, the pair comparison
being the *proved* `Work.Serre.ratSerrePairComparison` (through
`Work.RatHurewicz.ratPairComparison_proof`). -/
theorem loopShiftIso {k T N i : ℕ} (hk : 2 ≤ k) (hi : i + 1 ≤ 2 * k) (hi0 : 1 ≤ i)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (x : X) (y : Y)
    (hX : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) N X x)
    (hY : Work.Serre.IsEMSpaceUpTo ℤ (k + 1) (by omega) T Y y)
    (hT : i + 1 ≤ T - 1) (hN : i ≤ N) (hTN : N ≤ T - 1)
    (hf : ∀ j : ℕ, 0 < j → j < k →
      IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne Y y) y)) j)) :
    Nonempty (Work.Serre.ratH (TopCat.of X) i ≅ Work.Serre.ratH (TopCat.of Y) (i + 1)) := by
  have hm : 2 ≤ k + 1 := by omega
  -- the loop space of `Y` is a range model of `K(ℤ,k)` through `T - 1`
  have hLoop : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) (T - 1) (Path y y) (Path.refl y) := by
    convert Work.Stems.isEMSpaceUpTo_loop' (m := k + 1) hm y hY using 1
    omega
  have hLoopN : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) N (Path y y) (Path.refl y) :=
    ⟨hLoop.1, fun i' hi' hc' => hLoop.2 i' hi' (hc'.imp id (fun h => le_trans h hTN))⟩
  obtain ⟨ecmp⟩ := rangeModel_ratH_iso ℤ k N hk X x hX (Path y y) (Path.refl y) hLoopN i hN
  -- connectedness
  have hpcY : PathConnectedSpace Y :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero y
      (hY.2 0 (by omega) (Or.inl (by omega)))
  haveI hcontrPY : ContractibleSpace (Work.StemsB.PathSpace Y y) :=
    Work.StemsB.contractible_pathSpace Y y
  have hpcPY : PathConnectedSpace (Work.StemsB.PathSpace Y y) := inferInstance
  have hEvan : ∀ n : ℕ, 0 < n →
      IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.PathSpace Y y)) n) :=
    fun n hn => Work.Serre.RatAcyclic.isZero_ratH
      (Work.Serre.ratAcyclic_of_contractible (Work.StemsB.PathSpace Y y)) hn
  have hpt : ∀ n : ℕ, 0 < n → IsZero (Work.Serre.ratH (TopCat.of ↥({y} : Set Y)) n) :=
    fun n hn => Work.RatHurewicz.isZero_ratH_singleton y hn
  have hfib0 : PathConnectedSpace (Work.StemsB.fibre (Work.StemsB.evalOne Y y) y) :=
    Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration (Work.StemsB.evalOne Y y)
      (Work.StemsB.isSerreFibration_evalOne Y y) y hpcPY hpcY
      (hY.2 1 (by omega) (Or.inl (by omega)))
  -- the pair comparison at `b = k+1`, `f = k`
  obtain ⟨hpair, -⟩ := Work.RatHurewicz.ratPairComparison_proof (Work.StemsB.evalOne Y y)
    (Work.StemsB.isSerreFibration_evalOne Y y) y (k + 1) k (by omega) (by omega) hpcPY hpcY
    (fun i' hi' => hY.2 i' (by omega) (Or.inl hi')) hfib0 hf
  -- the two-step long exact sequence computation
  obtain ⟨e1⟩ := Work.RatHurewicz.nonempty_iso_cokernelπ_of_isZero (TopCat.of Y) ({y} : Set Y) i
    (hpt (i + 1) (by omega)) (hpt i (by omega))
  obtain ⟨e2⟩ := hpair (i + 1) (by omega)
  obtain ⟨e3⟩ := Work.RatHurewicz.nonempty_iso_relChainsRδ_of_isZero
    (TopCat.of (Work.StemsB.PathSpace Y y)) (Work.StemsB.evalOne Y y ⁻¹' {y}) i
    (hEvan (i + 1) (by omega)) (hEvan i (by omega))
  obtain ⟨e4⟩ := Work.Serre.strictFibre_ratH_homotopyFibre (Work.StemsB.evalOne Y y)
    (Work.StemsB.isSerreFibration_evalOne Y y) (Work.RatHurewicz.pathSpaceConst Y y) y hpcY i
  obtain ⟨heq⟩ := Work.Stems.homotopyFibre_evalOne_equiv_loop Y y
  haveI : IsIso (Work.Serre.ratHomologyMap heq.toFun i) :=
    Work.Serre.IsRatHomologyIso.of_homotopyEquiv heq i
  exact ⟨ecmp ≪≫ (asIso (Work.Serre.ratHomologyMap heq.toFun i)).symm ≪≫ e4.symm
    ≪≫ e3.symm ≪≫ e2 ≪≫ e1.symm⟩

/-- **`C2RatSphereRange` from the odd free-top interface alone.** -/
theorem C2RatSphereRange_of_C2oddFree (c : ℕ) (h : Work.Stems.Engine.C2oddFree c) :
    C2RatSphereRange := by
  intro k hk N hN X _ pt hX
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · -- `k = 1`: the odd interface applies to the given model, and the vanishing is vacuous
    have hk1' : k = 1 := hk1.symm
    subst hk1'
    have h1 := h 1 (le_refl 1) (by norm_num) N X pt hX
    exact ⟨h1.1, fun i hi hi2 hin => absurd (by omega) hin⟩
  · -- `k ≥ 2`
    have hck : c * (k - 1) ≤ c * k := Nat.mul_le_mul_left c (by omega)
    rcases Nat.even_or_odd k with hkE | hkO
    · -- even `k`
      have hodd : Odd (k - 1) := by
        obtain ⟨r, hr⟩ := hkE
        rw [hr] at hk2 ⊢
        exact ⟨r - 1, by omega⟩
      have hodd' : Odd (k + 1) := by
        obtain ⟨r, hr⟩ := hkE
        exact ⟨r, by omega⟩
      -- a range model of `K(ℤ,k)` with a large top, and one of `K(ℤ,k+1)`
      obtain ⟨X', tX', x₀, hX'⟩ :=
        Work.Serre.serreC0Range ℤ k (N + 4 * k + c * k + 4) (by omega) (by omega)
      letI : TopologicalSpace X' := tX'
      obtain ⟨Y, tY, y₀, hY⟩ :=
        Work.Serre.serreC0Range ℤ (k + 1) (N + 6 * k + c * (k + 1) + 6) (by omega) (by omega)
      letI : TopologicalSpace Y := tY
      have hX'N : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) N X' x₀ :=
        ⟨hX'.1, fun i hi hc => hX'.2 i hi (hc.imp id (fun h => by omega))⟩
      -- (A) the pair comparison of the path–loop fibration of `X'`
      have hLoop : Work.Serre.IsEMSpaceUpTo ℤ (k - 1) (by omega) (N + 4 * k + c * k + 4 - 1)
          (Path x₀ x₀) (Path.refl x₀) :=
        Work.Stems.isEMSpaceUpTo_loop' (m := k) hk2 x₀ hX'
      have hfib := h (k - 1) (by omega) hodd (N + 4 * k + c * k + 4 - 1)
        (Path x₀ x₀) (Path.refl x₀) hLoop
      have hpcX : PathConnectedSpace X' :=
        Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀
          (hX'.2 0 (by omega) (Or.inl (by omega)))
      haveI hcontrPX : ContractibleSpace (Work.StemsB.PathSpace X' x₀) :=
        Work.StemsB.contractible_pathSpace X' x₀
      have hpcPX : PathConnectedSpace (Work.StemsB.PathSpace X' x₀) := inferInstance
      have hfibVanish : ∀ n : ℕ, 0 < n →
          n < (N + 4 * k + c * k + 4 - 1) - c * (k - 1) → n ≠ k - 1 →
          IsZero (Work.Serre.ratH
            (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne X' x₀) x₀)) n) := by
        intro n hn hng hnne
        obtain ⟨heq⟩ := Work.Stems.homotopyFibre_evalOne_equiv_loop X' x₀
        have h1 : IsZero (Work.Serre.ratH (TopCat.of
            (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne X' x₀)
              (Work.RatHurewicz.pathSpaceConst X' x₀))) n) :=
          Work.Stems.isZero_ratH_of_homotopyEquiv heq n (hfib.2 n hn hng hnne)
        obtain ⟨estr⟩ := Work.Serre.strictFibre_ratH_homotopyFibre (Work.StemsB.evalOne X' x₀)
          (Work.StemsB.isSerreFibration_evalOne X' x₀) (Work.RatHurewicz.pathSpaceConst X' x₀)
          x₀ hpcX n
        exact IsZero.of_iso h1 estr
      have hfibGen : Nonempty (Work.Serre.ratH
          (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne X' x₀) x₀)) (k - 1) ≅
          ModuleCat.of ℚ ℚ) := by
        obtain ⟨heq⟩ := Work.Stems.homotopyFibre_evalOne_equiv_loop X' x₀
        have h1 := Work.Stems.isoRat_of_homotopyEquiv heq (k - 1) hfib.1
        obtain ⟨estr⟩ := Work.Serre.strictFibre_ratH_homotopyFibre (Work.StemsB.evalOne X' x₀)
          (Work.StemsB.isSerreFibration_evalOne X' x₀) (Work.RatHurewicz.pathSpaceConst X' x₀)
          x₀ hpcX (k - 1)
        exact ⟨estr ≪≫ h1.some⟩
      have hfib0 : PathConnectedSpace (Work.StemsB.fibre (Work.StemsB.evalOne X' x₀) x₀) :=
        Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration (Work.StemsB.evalOne X' x₀)
          (Work.StemsB.isSerreFibration_evalOne X' x₀) x₀ hpcPX hpcX
          (hX'.2 1 (by omega) (Or.inl (by omega)))
      obtain ⟨hpair, -⟩ := Work.RatHurewicz.ratPairComparison_proof (Work.StemsB.evalOne X' x₀)
        (Work.StemsB.isSerreFibration_evalOne X' x₀) x₀ k (k - 1) (by omega) (by omega) hpcPX hpcX
        (fun i hi => hX'.2 i (by omega) (Or.inl hi)) hfib0
        (fun n hn hnf => hfibVanish n hn (by omega) (by omega))
      have hmain := Work.RatHurewicz.fibreRangeVanishing (Work.StemsB.evalOne X' x₀) x₀ k (k - 1)
        (k - 1) ((N + 4 * k + c * k + 4 - 1) - c * (k - 1)) (by omega) (by omega) (by omega)
        (fun i hi hib => Work.Serre.serreE0Range X' x₀ (k - 1)
          (fun i' hi' => hX'.2 i' (by omega) (Or.inl (by omega))) i hi (by omega))
        (fun n hn => Work.Serre.RatAcyclic.isZero_ratH
          (Work.Serre.ratAcyclic_of_contractible (Work.StemsB.PathSpace X' x₀)) hn)
        (fun n hn hng hnne => hfibVanish n hn hng hnne)
        hfibGen (fun i hi => hpair i hi)
      -- (B) the top degree `2*k - 1`, by the loop shift to `K(ℤ,k+1)`
      have hYloc := h (k + 1) (by omega) hodd' (N + 6 * k + c * (k + 1) + 6) Y y₀ hY
      have hY2k : IsZero (Work.Serre.ratH (TopCat.of Y) (2 * k)) :=
        hYloc.2 (2 * k) (by omega) (by omega) (by omega)
      have hLoopY : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) (N + 6 * k + c * (k + 1) + 6 - 1)
          (Path y₀ y₀) (Path.refl y₀) := by
        convert Work.Stems.isEMSpaceUpTo_loop' (m := k + 1) (by omega) y₀ hY using 1
        omega
      -- the strict fibre of `evalOne Y y₀` is `(k-1)`-connected, hence rationally acyclic below `k`
      have hfibY : ∀ j : ℕ, 0 < j → j < k →
          IsZero (Work.Serre.ratH
            (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne Y y₀) y₀)) j) := by
        intro j hj hjk
        have hpcY : PathConnectedSpace Y :=
          Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero y₀
            (hY.2 0 (by omega) (Or.inl (by omega)))
        have hconn : ∀ i : ℕ, i ≤ k - 1 →
            Subsingleton (HomotopyGroup (Fin i) (Path y₀ y₀) (Path.refl y₀)) :=
          fun i hi => hLoopY.2 i (by omega) (Or.inl (by omega))
        have hvan : IsZero (Work.Serre.ratH (TopCat.of (Path y₀ y₀)) j) :=
          Work.Serre.serreE0Range (Path y₀ y₀) (Path.refl y₀) (k - 1) hconn j hj (by omega)
        obtain ⟨heq⟩ := Work.Stems.homotopyFibre_evalOne_equiv_loop Y y₀
        have h1 : IsZero (Work.Serre.ratH (TopCat.of
            (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne Y y₀)
              (Work.RatHurewicz.pathSpaceConst Y y₀))) j) :=
          Work.Stems.isZero_ratH_of_homotopyEquiv heq j hvan
        obtain ⟨estr⟩ := Work.Serre.strictFibre_ratH_homotopyFibre (Work.StemsB.evalOne Y y₀)
          (Work.StemsB.isSerreFibration_evalOne Y y₀) (Work.RatHurewicz.pathSpaceConst Y y₀)
          y₀ hpcY j
        exact IsZero.of_iso h1 estr
      have htop : IsZero (Work.Serre.ratH (TopCat.of X') (2 * k - 1)) :=
        IsZero.of_iso hY2k (Work.RatHurewicz.nonempty_iso_of_eq rfl
          (congrArg (Work.Serre.ratH (TopCat.of Y)) (by omega : (2 * k - 1) + 1 = 2 * k))
          (loopShiftIso (hk := hk2) (T := N + 6 * k + c * (k + 1) + 6) (N := N) (i := 2 * k - 1)
            (by omega) (by omega) x₀ y₀ hX'N hY (by omega) (by omega) (by omega) hfibY)).some
      -- assemble and transfer back
      refine c2Transfer hk2 hN pt x₀ hX hX'N
        (Work.RatHurewicz.nonempty_iso_of_eq
          (congrArg (Work.Serre.ratH (TopCat.of X')) (by omega : (k - 1) + 1 = k)) rfl
          hmain.2) ?_
      intro i hi1 hi2 hik
      by_cases hle : i ≤ 2 * k - 2
      · exact hmain.1 i hi1 (le_min (by omega) (by omega)) (fun hcontra => hik (by omega))
      · have hi_eq : i = 2 * k - 1 := by omega
        rw [hi_eq]
        exact htop
    · -- odd `k`: the odd interface applies directly to the enlarged model
      set top : ℕ := N + 4 * k + c * k + 4 with htop
      obtain ⟨X', tX', x₀, hX'⟩ := Work.Serre.serreC0Range ℤ k top (by omega) (by omega)
      letI : TopologicalSpace X' := tX'
      have hX'N : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) N X' x₀ :=
        ⟨hX'.1, fun i hi hc => hX'.2 i hi (hc.imp id (fun h => by omega))⟩
      have hmain := h k (by omega) hkO top X' x₀ hX'
      refine c2Transfer hk2 hN pt x₀ hX hX'N hmain.1 ?_
      intro i hi1 hi2 hik
      exact hmain.2 i hi1 (by omega) hik

end

end Work.StemsB
