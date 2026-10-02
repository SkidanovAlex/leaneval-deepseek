import Mathlib
import Submission.Work.Serre.serreC0Main
import Submission.Work.Serre.serreC0HurewiczEquiv
import Submission.Work.Serre.serreC0WedgeHomology
import Submission.Work.Serre.serreC0KillHomology
import Submission.Work.Serre.serreC0CoproductFinsupp
import Submission.Work.Serre.serreC0Presentation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Moore space of an abelian group, and the C0 construction

`Work.Serre.exists_isEMSpaceUpTo_succ`: for `k ≥ 1`, an abelian group `A` and a range `M ≥ k+1`
there is a space whose `π_{k+1}` is `A` and whose `π_i` vanish for `i ≠ k+1`, `i ≤ M`.

The space is `⋁_A S^{k+1}` (whose `H_{k+1}` is the free abelian group on `A`) with `(k+2)`-cells
attached along representatives of the relations `e_{a+b} - e_a - e_b`; the homology computation is
`serreC0KillHomology`, the presentations are `serreC0WedgeHomology`, `serreC0CoproductFinsupp` and
`serreC0Presentation`, and the Hurewicz isomorphism `serreC0HurewiczEquiv` identifies `π_{k+1}` with
`H_{k+1}`.
-/

open scoped Topology unitInterval

namespace Work.Serre

/-- The relations of the canonical presentation of the abelian group `A` inside the free abelian
group `A →₀ ℤ` on its underlying set: `e_{a+b} - e_a - e_b`. -/
noncomputable def presRel (A : Type) [Add A] (p : A × A) : A →₀ ℤ :=
  Finsupp.single (p.1 + p.2) (1 : ℤ) - Finsupp.single p.1 (1 : ℤ) - Finsupp.single p.2 (1 : ℤ)

/-- **The C0 construction in degree `k+1 ≥ 2`**, together with its Postnikov truncation. -/
theorem exists_isEMSpaceUpTo_succ (A : Type) [AddCommGroup A] (k : ℕ) (hk : 1 ≤ k) (M : ℕ)
    (hkM : k + 1 ≤ M) :
    ∃ (X : Type) (_ : TopologicalSpace X) (x : X), IsEMSpaceUpTo A (k + 1) (by omega) M X x := by
  classical
  -- the wedge `⋁_A S^{k+1}`
  let W := wedgeSpace k A
  let w₀ : W := wedgeBase k A
  have hk1 : 1 ≤ k + 1 := by omega
  have hk2 : 2 ≤ k + 1 := by omega
  have hWconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) W w₀) := by
    intro j hj
    exact wedgeCells_connected k hk A j hj
  -- the isomorphism `H_{k+1}(W) ≅ A →₀ ℤ`
  obtain ⟨eW⟩ := serreC0WedgeHomology (n := k - 1) A
  have hidx : k - 1 + 2 = k + 1 := by omega
  have eW' : ((Work.Cohomology.singularChains ℤ (TopCat.of W)).homology (k + 1)) ≅
      (∐ fun _ : A => ModuleCat.of ℤ ℤ) := by
    rw [← hidx]
    exact eW
  obtain ⟨eCF⟩ := serreC0CoproductFinsupp A
  have φ : ((Work.Cohomology.singularChains ℤ (TopCat.of W)).homology (k + 1)) ≃ₗ[ℤ]
      (A →₀ ℤ) := (eW' ≪≫ eCF).toLinearEquiv
  -- the attaching maps: representatives of the relations
  have hchoose : ∀ p : A × A, ∃ g : C(Work.Stems.sphere (k + 1), W),
      Work.Stems.hurewiczClass (k + 1) hk1 g = φ.symm (presRel A p) := by
    intro p
    refine exists_sphereMap_hurewiczClass_eq (m := k + 1) hk2 w₀ ?_ (φ.symm (presRel A p))
    intro j hj
    exact hWconn j (by omega)
  let g : (A × A) → C(Work.RatHurewicz.cellSphere k, W) := fun p => Classical.choose (hchoose p)
  have hg : ∀ p : A × A,
      Work.Stems.hurewiczClass (k + 1) hk1 (g p) = φ.symm (presRel A p) := by
    intro p
    exact Classical.choose_spec (hchoose p)
  -- the relation submodules
  have hfun : (fun p : A × A => Work.Stems.hurewiczClass (k + 1) hk1 (g p)) =
      fun p => φ.symm (presRel A p) := funext hg
  have hsub : (Submodule.span ℤ (Set.range (fun p : A × A =>
        Work.Stems.hurewiczClass (k + 1) hk1 (g p)))).map (φ : _ →ₗ[ℤ] _) =
      Submodule.span ℤ (Set.range (presRel A)) := by
    rw [hfun, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨p, rfl⟩, rfl⟩
      refine ⟨p, ?_⟩
      show presRel A p = φ (φ.symm (presRel A p))
      exact (φ.apply_symm_apply _).symm
    · rintro ⟨p, rfl⟩
      refine ⟨φ.symm (presRel A p), ⟨p, rfl⟩, ?_⟩
      show φ (φ.symm (presRel A p)) = presRel A p
      exact φ.apply_symm_apply _
  -- the homology computation
  obtain ⟨eKill⟩ := serreC0KillHomology (n := k) (by omega) (Y := W) (A × A) g
  obtain ⟨ePres⟩ := serreC0Presentation A
  have eQuot : ((Work.Cohomology.singularChains ℤ (TopCat.of W)).homology (k + 1) ⧸
        Submodule.span ℤ (Set.range (fun p : A × A =>
          Work.Stems.hurewiczClass (k + 1) hk1 (g p)))) ≃ₗ[ℤ]
      ((A →₀ ℤ) ⧸ Submodule.span ℤ (Set.range (presRel A))) := by
    convert Submodule.Quotient.equiv
      (Submodule.span ℤ (Set.range (fun p : A × A =>
        Work.Stems.hurewiczClass (k + 1) hk1 (g p))))
      (Submodule.span ℤ (Set.range (presRel A))) φ hsub using 1
    all_goals first | rfl | exact Subsingleton.elim _ _
  have eA : ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.RatHurewicz.attachCells k W (A × A) g))).homology (k + 1)) ≃ₗ[ℤ] A :=
    (eKill.toLinearEquiv).trans (eQuot.trans ePres)
  -- connectivity and Hurewicz
  have hXconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j)
      (Work.RatHurewicz.attachCells k W (A × A) g)
      (Work.RatHurewicz.attachIncl k W (A × A) g w₀)) :=
    connected_attachCells (k := k) W w₀ (A × A) g hWconn
  have hconn : ∀ j : ℕ, j < k + 1 → Subsingleton (HomotopyGroup (Fin j)
      (Work.RatHurewicz.attachCells k W (A × A) g)
      (Work.RatHurewicz.attachIncl k W (A × A) g w₀)) := by
    intro j hj
    exact hXconn j (by omega)
  have hiso : Nonempty (HomotopyGroup (Fin (k + 1))
      (Work.RatHurewicz.attachCells k W (A × A) g)
      (Work.RatHurewicz.attachIncl k W (A × A) g w₀) ≃* Multiplicative A) :=
    serreC0HurewiczEquiv (m := k + 1) (by omega) _ hconn eA
  exact exists_isEMSpaceUpTo_of_piIso (A := A) (m := k + 1) (N := M) (by omega) hkM _ hconn hiso

end Work.Serre
