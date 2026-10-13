import Mathlib
import Submission.Work.DSMX0U.ModelF
import Submission.Work.DSMX0U.stepData_exists
import Submission.Work.DSMX0U.baseCell_exists2
import Submission.Work.DSMX0U.isBddFinFree_towerModel
import Submission.Work.DSMX0U.exists_towerModelMap
import Submission.Work.DSMX0U.towerMap_quasiIsoAt_succ
import Submission.Work.DSMX0U.quasiIso_towerModelMap2
import Submission.Work.DSMX0U.exists_towerCoaug
import Submission.Work.DSMX0U.cell_d_comm

/-!
# DSMX0U — the engine: a bounded-above finite free model of a complex with f.g. cohomology

This file assembles the pieces of the area into the single analytic step that the node `MX0U`
needs beyond `F1`/`COH` (the "pseudo-coherence" step):

> a cochain complex `C` of `A`-modules over a Noetherian ring, with cohomology vanishing above
> `N` and finitely generated in every degree, admits a bounded-above complex `P` of finitely
> generated free `A`-modules with a quasi-isomorphism `P ⟶ C` carrying a prescribed coaugmentation
> `A ⟶ C⁰` to the coaugmentation of the model.

Only the *cohomology* of `C` is required to vanish above `N`: this matters for the application,
since Mathlib's Čech complex is the *unnormalized* alternating coface complex and therefore has
non-zero terms in every degree.

## The construction

Starting from `M := max N 0` (so that `N ≤ M` and `0 ≤ M`), one builds

* the base cell `s₀ : Cell A C c₀ (M+1)` (`baseCell_exists2`), whose differential is `0`;
* the step function `hstep : ∀ q s, StepData A s` (`stepData_exists`), and the tower
  `tower hstep M s₀`;
* the model complex `P := towerModel hstep M s₀ = (towerComplex …).extend (embeddingUpIntLE M)`,
  which is bounded above (`towerModel_isZero_of_gt`) with finitely generated free terms
  (`isBddFinFree_towerModel`);
* the chain map `φ : P ⟶ C` with prescribed components (`exists_towerModelMap`), a
  quasi-isomorphism (`quasiIso_towerModelMap2`, using the level-wise quasi-isomorphism
  `towerMap_quasiIsoAt_succ` and the vanishing of `H^i(C)` above `N`);
* the coaugmentation `ε : A ⟶ P⁰` (`exists_towerCoaug`), a cycle carrying `c₀`.
-/

namespace Work.DSMX0U

open CategoryTheory Limits
open scoped Classical

universe a

set_option maxHeartbeats 800000

/-- **The engine.** -/
theorem exists_finFreeModel_of_fgCoh {A : Type a} [CommRing A] [IsNoetherianRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {N : ℤ}
    (hhi : ∀ i : ℤ, N < i → IsZero (C.homology i))
    (hfg : ∀ i : ℤ, Module.Finite A (C.homology i))
    (c₀ : ModuleCat.of A A ⟶ C.X 0)
    (hc₀ : ∀ j : ℤ, CategoryTheory.CategoryStruct.comp c₀ (C.d 0 j) = 0) :
    ∃ (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0) (φ : P ⟶ C),
      DSMap.Mix.IsBddFinFree P ∧
        (∀ j : ℤ, CategoryTheory.CategoryStruct.comp ε (P.d 0 j) = 0) ∧
        QuasiIso φ ∧ CategoryTheory.CategoryStruct.comp ε (φ.f 0) = c₀ := by
  let M : ℤ := max N 0
  have hMN : N ≤ M := le_max_left N 0
  have hM0 : 0 ≤ M := le_max_right N 0
  have hfgM : Module.Finite A (C.homology M) := hfg M
  -- the step function
  have hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s := fun q s =>
    Classical.choice (stepData_exists (A := A) (C := C) (c₀ := c₀) (q := q) hc₀ s
      (hfg ((q - 1) - 1)))
  -- the base cell
  obtain ⟨s₀, hd0⟩ := baseCell_exists2 (A := A) (C := C) (c₀ := c₀) (M := M) hc₀ hfgM
  -- the base cell's map into `C` lands in the cycles
  have hd : TowerBaseCycle hstep M s₀ := by
    have h := cell_d_comm (A := A) (C := C) (c₀ := c₀) (q := M + 1) s₀
    rw [hd0, zero_comp] at h
    exact h.symm
  -- the model map
  obtain ⟨φ, hφ⟩ := exists_towerModelMap (A := A) (C := C) (c₀ := c₀) hstep M s₀ hd
  -- its quasi-isomorphism
  have hqiso : QuasiIso φ :=
    quasiIso_towerModelMap2 (A := A) (C := C) (c₀ := c₀) hstep M s₀
      (by rw [tower_zero]; exact hd0) φ hφ
      (fun k => towerMap_quasiIsoAt_succ (A := A) (C := C) (c₀ := c₀) hstep M s₀ k)
      (N := N) (fun i hi => hhi i hi) hMN
  -- the level whose degree is `0`
  have hk : levelDeg M (M.toNat) - 1 = 0 := by
    rw [levelDeg_cur]
    have h : ((M.toNat : ℤ)) = M := Int.toNat_of_nonneg hM0
    omega
  -- the coaugmentation
  obtain ⟨ε, hε, hεφ⟩ := exists_towerCoaug (A := A) (C := C) (c₀ := c₀) hstep M s₀ φ hφ (M.toNat) hk
  exact ⟨towerModel hstep M s₀, ε, φ, isBddFinFree_towerModel hstep M s₀, hε, hqiso, hεφ⟩

end Work.DSMX0U
