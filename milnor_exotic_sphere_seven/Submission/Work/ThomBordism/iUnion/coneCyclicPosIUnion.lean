import Mathlib
import Submission.Work.ThomBordism.iUnion.coneAux
import Submission.Work.ThomBordism.iUnion.coneSucc
import Submission.Work.ThomBordism.iUnion.coneZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Cyclicity of the cone over a union of pieces: the degree induction

`Work.ThomBordism.iUnion.coneCyclicPosIUnion`: over a chain `C` of open pieces on which the local
Thom map of the piece class `τ` is bijective, and for which the cone is cyclic at degree `0` over
the union of every subfamily (`hzero`), the cone is cyclic in **every** positive degree over the
union `⋃₀ D₀` of any subfamily `D₀ ⊆ C`.

The proof is the degree induction announced in the header of `coneCyclicPos_succ`:

* the degree-`0` case is `coneCyclicPos_zero` (`coneZero.lean`);
* the successor step is `coneCyclicPos_succ`, whose induction hypothesis is stated with an
  arbitrary proof of the inclusion `⋃₀ S ⊆ ⋃₀ C` so that it can be instantiated at every subfamily;
* the induction is carried out for **all** subfamilies simultaneously (that is what the Zorn
  argument inside the successor step consumes), and the target is then the instance `S = D₀`.
-/

namespace Work.ThomBordism.iUnion

theorem coneCyclicPosIUnion {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (n : ℕ) (hn : 1 ≤ n) (C : Set (Set B)) (hC : ∀ W ∈ C, IsOpen W)
    (hchainC : ∀ W ∈ C, ∀ W' ∈ C, W ⊆ W' ∨ W' ⊆ W)
    (τ : Work.Thom.PieceCoh Z (⋃₀ C) n)
    (h : ∀ W (hW : W ∈ C), ∀ k, Function.Bijective (Work.Thom.localThomMap Z n W
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' (⋃₀ C)) (Z.proj ⁻¹' W) (Set.preimage_mono (Set.subset_sUnion_of_mem hW)) n).hom τ) k))
    (hzero : ∀ (D : Set (Set B)) (hD : D ⊆ C),
        Work.ThomBordism.ConeCyclicZero Z n (⋃₀ C) τ (⋃₀ D) (Set.sUnion_mono hD))
    (D₀ : Set (Set B)) (hD₀ : D₀ ⊆ C) :
    ∀ m, Work.ThomBordism.ConeCyclicPos Z n (⋃₀ C) τ (⋃₀ D₀) (Set.sUnion_mono hD₀) m := by
  -- the induction is carried out for all subfamilies of `C` simultaneously
  have key : ∀ (k : ℕ) (S : Set (Set B)) (hS : S ⊆ C) (hinc : ⋃₀ S ⊆ ⋃₀ C),
      Work.ThomBordism.ConeCyclicPos Z n (⋃₀ C) τ (⋃₀ S) hinc k := by
    intro k
    induction k with
    | zero =>
      intro S hS hinc
      exact coneCyclicPos_zero Z n hn C hC hchainC τ h hzero S hS hinc
    | succ k ih =>
      intro S hS hinc
      exact coneCyclicPos_succ Z n hn C hC hchainC τ h k
        (fun S' hS' hinc' => ih S' hS' hinc') S hS hinc
  intro m
  exact key m D₀ hD₀ (Set.sUnion_mono hD₀)

end Work.ThomBordism.iUnion
