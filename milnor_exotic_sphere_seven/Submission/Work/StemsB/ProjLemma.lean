import Submission.Work.StemsB.ProjLemmaDefs
import Submission.Work.StemsB.SurjIntIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The projection lemma of the Serre exact sequence over a sphere

The projection `(q, y) ↦ (q, ())` from `↥(sphLoopBig n) × Y` onto `↥(sphLoopBig n) × PUnit`
induces an isomorphism on *relative* singular homology in every degree `k < n + f`, where `f` is a
vanishing range for the homology of `Y` (`H_j(Y) = 0` for `0 < j < f`) and `H_0(Y) ≅ ℤ`.

The proof uses no naturality of the collar Künneth: it computes source and target separately
(`serreSphere_collar_iso`, `serreSphere_collar_isZero`), observes that the map is a split
epimorphism (`sphSecRelMap_comp_sphProjRelMap`) and invokes the elementary algebra lemma
`Work.StemsB.bijective_of_surjective_of_int_iso` in the middle degree.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB

noncomputable section

/-- Transport of the homology of a chain complex along an equality of degrees. -/
noncomputable def homologyCongr {C : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j) :
    C.homology i ≅ C.homology j :=
  eqToIso (congrArg (fun t => C.homology t) h)

/-- The collar Künneth isomorphism `H_k(↥(sphLoopBig n) × Y, sphLoopCollarProd n Y) ≅ H_{k-n}(Y)`
in the degree that the projection lemma needs (i.e. with the index `k ≥ n` on the left). -/
theorem collarIsoAt (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y] (k : ℕ) (h : n ≤ k) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
        (sphLoopCollarProd n Y)).homology k) ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology (k - n)) := by
  obtain ⟨e⟩ := serreSphere_collar_iso n hn Y (k - n)
  exact ⟨homologyCongr (C := Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
      (sphLoopCollarProd n Y)) (i := k) (j := k - n + n) (Nat.sub_add_cancel h).symm ≪≫ e⟩

/-- **The projection lemma.** -/
theorem sphProjRelMap_isIso (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y]
    (f : ℕ) (hY0 : Nonempty Y)
    (hY : ∀ j : ℕ, 0 < j → j < f →
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology j))
    (hH0 : Nonempty (((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology 0) ≃ₗ[ℤ] ℤ))
    (k : ℕ) (hk : k < n + f) :
    IsIso (HomologicalComplex.homologyMap (sphProjRelMap n Y) k) := by
  rcases lt_or_ge k n with hklt | hkle
  · -- `k < n`: both sides are zero objects
    have hS : IsZero ((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
        (sphLoopCollarProd n Y)).homology k) := serreSphere_collar_isZero n hn Y k hklt
    have hT : IsZero ((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × PUnit))
        (sphLoopCollarProd n PUnit)).homology k) := serreSphere_collar_isZero n hn PUnit k hklt
    exact isIso_of_isZero_of_isZero hS hT
  · rcases lt_or_eq_of_le hkle with hkgt | hkeq
    · -- `n < k`: the source is `H_{k-n}(Y) = 0`, the target is `H_{k-n}(pt) = 0`
      have hj0 : 0 < k - n := Nat.sub_pos_of_lt hkgt
      have hjf : k - n < f := by omega
      obtain ⟨e⟩ := collarIsoAt n hn Y k hkle
      have hS : IsZero ((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
          (sphLoopCollarProd n Y)).homology k) :=
        IsZero.of_iso (hY (k - n) hj0 hjf) e
      obtain ⟨e'⟩ := collarIsoAt n hn PUnit k hkle
      have hT : IsZero ((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × PUnit))
          (sphLoopCollarProd n PUnit)).homology k) :=
        IsZero.of_iso (isZero_homology_punit (k - n) hj0) e'
      exact isIso_of_isZero_of_isZero hS hT
    · -- `k = n`: the middle degree
      subst hkeq
      obtain ⟨y₀⟩ := hY0
      -- the map is a split epimorphism
      have hsplit : HomologicalComplex.homologyMap (sphSecRelMap n Y y₀) n
            ≫ HomologicalComplex.homologyMap (sphProjRelMap n Y) n = 𝟙 _ := by
        rw [← HomologicalComplex.homologyMap_comp, sphSecRelMap_comp_sphProjRelMap n Y y₀,
          HomologicalComplex.homologyMap_id]
      have hsurj : Function.Surjective
          ((HomologicalComplex.homologyMap (sphProjRelMap n Y) n).hom : _ → _) := by
        intro b
        refine ⟨(HomologicalComplex.homologyMap (sphSecRelMap n Y y₀) n) b, ?_⟩
        have h := congrArg (fun φ => φ b) hsplit
        simpa [ModuleCat.comp_apply] using h
      -- the two groups are isomorphic to `ℤ`
      have hM : Nonempty (((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
          (sphLoopCollarProd n Y)).homology n) ≃ₗ[ℤ] ℤ) := by
        obtain ⟨e⟩ := collarIsoAt n hn Y n le_rfl
        obtain ⟨e0⟩ := hH0
        exact ⟨(Work.Cohomology.uctIsoToLinearEquiv
          (e ≪≫ homologyCongr (C := Work.Cohomology.singularChains ℤ (TopCat.of Y))
            (Nat.sub_self n))).trans e0⟩
      have hN : Nonempty (((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × PUnit))
          (sphLoopCollarProd n PUnit)).homology n) ≃ₗ[ℤ] ℤ) := by
        obtain ⟨e⟩ := collarIsoAt n hn PUnit n le_rfl
        obtain ⟨e0⟩ := nonempty_homology_zero_punit_linEquiv
        exact ⟨(Work.Cohomology.uctIsoToLinearEquiv
          (e ≪≫ homologyCongr (C := Work.Cohomology.singularChains ℤ (TopCat.of PUnit))
            (Nat.sub_self n))).trans e0⟩
      refine (ConcreteCategory.isIso_iff_bijective
        (HomologicalComplex.homologyMap (sphProjRelMap n Y) n)).mpr ?_
      exact bijective_of_surjective_of_int_iso hM hN
        (HomologicalComplex.homologyMap (sphProjRelMap n Y) n).hom hsurj

end

end Work.StemsB
