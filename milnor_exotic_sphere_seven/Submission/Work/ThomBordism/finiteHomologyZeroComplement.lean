import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.TangentClasses.Bundle
import Submission.Work.Thom.Basic
import Submission.Work.ThomBordism.Grassmann.Torsion.finiteCoverHomologyFinite
import Submission.Work.ThomBordism.Grassmann.Torsion.finiteTransfer
import Submission.Work.ThomBordism.Grassmann.Torsion.annulusFiniteness
import Submission.Work.Cohomology.punctured_homotopyEquiv_sphere

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 800000

namespace Work.ThomBordism

open Work.TangentClasses

noncomputable section

/-! ## Two elementary homeomorphism utilities -/

/-- **Re-association of a subtype of a conjunction**: the subtype of `{x // p x ∧ q x}` with the
subtype of `{x : {y // q y} // p x.1}`. -/
def subtypeConjHomeo {α : Type*} [TopologicalSpace α] {p q : α → Prop} :
    {x : α // p x ∧ q x} ≃ₜ {x : {y : α // q y} // p x.1} where
  toFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  invFun x := ⟨x.1.1, x.2, x.1.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun x => x.2.2)) (fun x => x.2.1)
  continuous_invFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
      (fun x => ⟨x.2, x.1.2⟩)

/-- **A subtype of a product**: `{q : s × F // q.2 ∈ t} ≃ₜ s × t`. -/
def prodSubtypeHomeo {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    (s : Set B) (t : Set F) : {q : ↥s × F // q.2 ∈ t} ≃ₜ ↥s × ↥t where
  toFun q := (q.1.1, ⟨q.1.2, q.2⟩)
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop


/-! ## Finiteness of the homology of the punctured model fibre -/

/-- **The punctured fibre `ℝ^k ∖ 0` has finitely generated homology.**  For `k = 0` the space is
empty; for `k ≥ 1` it is homeomorphic (through the identity of the underlying functions) to the
punctured Euclidean space, which is homotopy equivalent to the sphere `S^{k-1}` by radial
normalization (`Work.Cohomology.punctured_homotopyEquiv_sphere`), whose homology is finitely
generated (`sphereHomologyFiniteAmb`). -/
theorem finPiPunctHomologyFinite (k n : ℕ) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥({v : Fin k → ℝ | v ≠ 0}))).homology n) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hemp : ({v : Fin 0 → ℝ | v ≠ 0} : Set (Fin 0 → ℝ)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro v hv
      exact hv (Subsingleton.elim v 0)
    rw [hemp]
    exact fgch_moduleFinite_homology_of_contractibleOrEmpty ↥(∅ : Set (Fin 0 → ℝ))
      (fun hc => by obtain ⟨x, hx⟩ := hc; exact absurd hx (by simp)) n
  · -- `k ≥ 1`: the Euclidean version, then the `PiLp` transport
    have hE : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥({v : EuclideanSpace ℝ (Fin k) | v ≠ 0}))).homology n) := by
      obtain ⟨e⟩ := Work.Cohomology.punctured_homotopyEquiv_sphere (EuclideanSpace ℝ (Fin k))
      exact Work.ThomBordism.Grassmann.Torsion.moduleFinite_homology_of_homotopyEquivCM e.symm n
        (Work.ThomBordism.Grassmann.Torsion.sphereHomologyFiniteAmb hk n)
    have hsub : ↥({v : EuclideanSpace ℝ (Fin k) | v ≠ 0}) ≃ₜ
        ↥({v : Fin k → ℝ | v ≠ 0}) :=
      (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).subtype (p := fun v => v ≠ 0)
        (q := fun v => v ≠ 0) (fun v => by
          rw [show (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)) v = WithLp.ofLp v from rfl]
          simp)
    exact Work.ThomBordism.Grassmann.Torsion.moduleFinite_homology_of_homeomorphCM hsub n hE


/-! ## The punctured total space over a subset of a chart base set -/

/-- **Local triviality of the complement of the zero section.**  For a real bundle `Z` with a chart
`i` whose base set contains `W`, the part of the punctured total space lying over `W` is
homeomorphic to `W × (F ∖ 0)`: the local trivialization `Z.localTriv i` identifies the total space
over `W` with `W × F`, and it is fibrewise linear, so it carries the complement of the zero section
onto `W × {v | v ≠ 0}`. -/
theorem zeroComplementPieceHomeo {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (i : ι) {W : Set B} (hW : W ⊆ Z.baseSet i) :
    Nonempty (↥{p : ↥(Work.Thom.zeroComplement Z) | Z.proj p.1 ∈ W} ≃ₜ
      ↥W × ↥{v : F | v ≠ 0}) := by
  classical
  have hw : W ⊆ (Z.localTriv i).baseSet := by simpa using hW
  have hiff : ∀ p : ↥(Z.proj ⁻¹' W),
      (p.1 ∈ Work.Thom.zeroComplement Z) ↔
        (((Z.localTriv i).preimageHomeomorph hw) p).2 ≠ 0 := by
    intro p
    rw [Bundle.Trivialization.preimageHomeomorph_apply]
    have hkey : (Z.localTriv i p.1).2 = 0 ↔ (show F from p.1.2) = 0 := by
      have hp : p.1.1 ∈ Z.baseSet i := hW p.2
      have hb : p.1.1 ∈ (Z.localTriv i).baseSet := by simpa using hp
      have h1 : ((Z.localTriv i).linearEquivAt ℝ p.1.1 hb) (show F from p.1.2) =
          (Z.localTriv i p.1).2 :=
        Bundle.Trivialization.linearEquivAt_apply (e := Z.localTriv i) p.1.1 hb
          (show F from p.1.2)
      rw [← h1]
      exact LinearEquiv.map_eq_zero_iff _
    rw [Work.Thom.mem_zeroComplement]
    exact (not_iff_not.mpr hkey).symm
  refine ⟨(subtypeConjHomeo (p := fun x : Z.TotalSpace => Z.proj x ∈ W)
      (q := fun x : Z.TotalSpace => x ∈ Work.Thom.zeroComplement Z)).symm.trans ?_⟩
  refine (Homeomorph.setCongr ?_).trans
    ((subtypeConjHomeo (p := fun x : Z.TotalSpace => x ∈ Work.Thom.zeroComplement Z)
      (q := fun x : Z.TotalSpace => Z.proj x ∈ W)).trans ?_)
  · ext x
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  · exact (((Z.localTriv i).preimageHomeomorph hw).subtype
      (p := fun p : ↥(Z.proj ⁻¹' W) => p.1 ∈ Work.Thom.zeroComplement Z)
      (q := fun q : ↥W × F => q.2 ≠ 0) hiff).trans
      (prodSubtypeHomeo W {v : F | v ≠ 0})


/-! ## The main theorem -/

/-- **Finitely generated homology of the complement of the zero section.**  Let `Z` be a real
bundle over a `Man8` `V`, and let `U : Fin m → Set V.pt` be a finite *good* cover of `V.pt`
subordinate to the chart base sets of `Z` (each `U i` lies in `Z.baseSet (r i)`).  Then the
complement of the zero section of `Z` has finitely generated singular homology in every degree.

The cover `U` is pulled back along the bundle projection to a cover of the punctured total space; by
local triviality the part of the punctured total space over a nonempty finite intersection
`⋂ i ∈ S, U i` is homeomorphic to `(⋂ i ∈ S, U i) × (ℝ^k ∖ 0)`, hence has finitely generated
homology by `finPiPunctHomologyFinite` and `homologyFinite_prod_contractible` (the intersection is
contractible by goodness).  `finiteCoverHomologyFinite` then gives the conclusion. -/
theorem finiteHomologyZeroComplement {V : Work.ThomBordism.Man8} {k : ℕ} {ι : Type} {m : ℕ}
    (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι)
    (U : Fin m → Set V.pt) (r : Fin m → ι)
    (hopen : ∀ i, IsOpen (U i)) (hcov : (⋃ i, U i) = Set.univ)
    (hgood : ∀ S : Finset (Fin m), S.Nonempty → (⋂ i ∈ S, U i).Nonempty →
      ContractibleSpace ↥(⋂ i ∈ S, U i))
    (hsub : ∀ i, U i ⊆ Z.baseSet (r i)) (n : ℕ) :
    Module.Finite ℤ ↥((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(Work.Thom.zeroComplement Z))).homology n) := by
  classical
  let Wp : Fin m → Set ↥(Work.Thom.zeroComplement Z) := fun i => {p | Z.proj p.1 ∈ U i}
  have hWp : ∀ i, Wp i = {p : ↥(Work.Thom.zeroComplement Z) | Z.proj p.1 ∈ U i} := fun i => rfl
  have hWpInter : ∀ S : Finset (Fin m),
      (⋂ i ∈ S, Wp i) = {p : ↥(Work.Thom.zeroComplement Z) | Z.proj p.1 ∈ ⋂ i ∈ S, U i} := by
    intro S
    ext p
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, hWp]
  refine Work.ThomBordism.Grassmann.Torsion.finiteCoverHomologyFinite
    (X := TopCat.of ↥(Work.Thom.zeroComplement Z)) Wp (fun i => ?_) ?_ ?_ n
  · rw [hWp i]
    exact (hopen i).preimage (Z.continuous_proj.comp continuous_subtype_val)
  · rw [Set.eq_univ_iff_forall]
    intro p
    have hp : Z.proj p.1 ∈ ⋃ i, U i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro S hS d
    by_cases hne : (⋂ i ∈ S, U i).Nonempty
    · have hcontr : ContractibleSpace ↥(⋂ i ∈ S, U i) := hgood S hS hne
      obtain ⟨i₀, hi₀⟩ := hS
      have hWchart : (⋂ i ∈ S, U i) ⊆ Z.baseSet (r i₀) := fun x hx =>
        hsub i₀ (Set.mem_iInter₂.mp hx i₀ hi₀)
      obtain ⟨e⟩ := zeroComplementPieceHomeo Z (r i₀) hWchart
      have hprod : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
          (TopCat.of (↥(⋂ i ∈ S, U i) × ↥({v : Fin k → ℝ | v ≠ 0})))).homology d) :=
        Work.ThomBordism.Grassmann.Torsion.homologyFinite_prod_contractible
          (X := ↥(⋂ i ∈ S, U i)) (Y := ↥({v : Fin k → ℝ | v ≠ 0})) d
          (finPiPunctHomologyFinite k d)
      rw [hWpInter S]
      exact Work.ThomBordism.Grassmann.Torsion.moduleFinite_homology_of_homeomorphCM e.symm d hprod
    · have hbase : (⋂ i ∈ S, U i) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hemp : (⋂ i ∈ S, Wp i) = (∅ : Set ↥(Work.Thom.zeroComplement Z)) := by
        rw [hWpInter S, hbase]
        ext p
        simp
      rw [hemp]
      exact fgch_moduleFinite_homology_of_contractibleOrEmpty
        ↥(∅ : Set ↥(Work.Thom.zeroComplement Z))
        (fun hc => by obtain ⟨x, hx⟩ := hc; exact absurd hx (by simp)) d

end

end Work.ThomBordism
