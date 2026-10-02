import Submission.Work.Serre.ThmCylSigma.Basic
import Submission.Work.Serre.ThmCylSigma.Class
import Submission.Work.Serre.ThmCylSigma.Incl

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cochain complex of a `σ`-type

The relative cochains `C^n(Σ i, Y i, Σ i, A i)` are the product of the relative cochains
`C^n(Y i, A i)` of the pieces; the maps `Work.Serre.Sigma.restrRel` (restriction to a piece) and
`Work.Serre.Sigma.assembleRel` (assembly of a family of relative cochains) are mutually inverse
linear isomorphisms, compatible with the differentials and with the classes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

namespace Work.Serre.Sigma

noncomputable section

variable {ι : Type} {Y : ι → Type} [∀ i, TopologicalSpace (Y i)]


/-! ## A criterion for relative cochains

The relative cochains `C^n(X,A)` are the cochains vanishing on the chains supported in `A`, i.e.
on those singular simplices whose image is contained in `A`. -/

/-- **Lifting a simplex whose image lies in `A`**: it is the pushforward of a simplex of the
subspace `A`. -/
theorem exists_subtype_lift (X : TopCat) (A : Set X) (n : ℕ)
    (τ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (hτ : ∀ t, (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))) τ t ∈ A) :
    ∃ τ' : (TopCat.toSSet.obj (TopCat.of ↥A)).obj (Opposite.op (SimplexCategory.mk n)),
      (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)).app
        (Opposite.op (SimplexCategory.mk n)) τ' = τ := by
  refine ⟨(TopCat.toSSetObjEquiv (TopCat.of ↥A) (Opposite.op (SimplexCategory.mk n))).symm
    ⟨fun t => ⟨(TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))) τ t, hτ t⟩, ?_⟩, ?_⟩
  · exact ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))) τ).continuous.subtype_mk
      (fun t => hτ t)
  · apply (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).injective
    ext t
    rfl

/-- The restriction of a cochain, evaluated on a simplex of the subspace. -/
theorem genEval_restr_gen (R : Type) [CommRing R] (X : TopCat) (A : Set X) (n : ℕ)
    (β : Work.Cohomology.Cochain R (TopCat.toSSet.obj X) n)
    (τ : (TopCat.toSSet.obj (TopCat.of ↥A)).obj (Opposite.op (SimplexCategory.mk n))) :
    Work.Cohomology.genEval R (TopCat.toSSet.obj (TopCat.of ↥A))
        (((Work.Cohomology.restr R X A).f n).hom β) τ =
      Work.Cohomology.genEval R (TopCat.toSSet.obj X) β
        ((TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)).app
          (Opposite.op (SimplexCategory.mk n)) τ) := by
  simp only [Work.Cohomology.restr, Work.Cohomology.dualChainMap_f_hom,
    Work.Cohomology.cochainPullbackHom, ModuleCat.hom_ofHom]
  exact Work.Gen.genEval_cochainPullbackHom R (Work.Cohomology.subtypeIncl X A) β τ

/-- **A cochain is relative to `A` if and only if it vanishes on every simplex whose image lies in
`A`.** -/
theorem relKern_iff (R : Type) [CommRing R] (X : TopCat) (A : Set X) (n : ℕ)
    (α : Work.Cohomology.Cochain R (TopCat.toSSet.obj X) n) :
    α ∈ Work.Cohomology.relKern R X A n ↔
      ∀ (τ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))),
        (∀ t, (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))) τ t ∈ A) →
        Work.Cohomology.genEval R (TopCat.toSSet.obj X) α τ = 0 := by
  constructor
  · intro hα τ hτ
    obtain ⟨τ', rfl⟩ := exists_subtype_lift X A n τ hτ
    have h0 : ((Work.Cohomology.restr R X A).f n).hom α = 0 := hα
    have hz : Work.Cohomology.genEval R (TopCat.toSSet.obj (TopCat.of ↥A))
        (((Work.Cohomology.restr R X A).f n).hom α) τ' = 0 := by
      rw [h0]
      simp only [Work.Cohomology.genEval, LinearMap.zero_apply]
    exact (genEval_restr_gen R X A n α τ').symm.trans hz
  · intro h
    have h0 : ((Work.Cohomology.restr R X A).f n).hom α = 0 := by
      apply Work.Cohomology.genEval_ext
      intro τ'
      have hz : Work.Cohomology.genEval R (TopCat.toSSet.obj X) α
          ((TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)).app
            (Opposite.op (SimplexCategory.mk n)) τ') = 0 :=
        h _ (fun t => ((TopCat.toSSetObjEquiv (TopCat.of ↥A)
          (Opposite.op (SimplexCategory.mk n))) τ' t).2)
      exact (genEval_restr_gen R X A n α τ').trans hz
    exact h0

/-! ## The relative restriction -/

/-- **Restriction of a relative cochain to a piece.** -/
noncomputable def restrRel (R : Type) [CommRing R] (A : ∀ i, Set (Y i)) (i : ι) (n : ℕ) :
    Work.Cohomology.relKern R (TopCat.of (Σ i, Y i)) (sigmaSet A) n →ₗ[R]
      Work.Cohomology.relKern R (TopCat.of (Y i)) (A i) n :=
  @Work.Cohomology.relMapLM R _ (TopCat.of (Y i)) (TopCat.of (Σ i, Y i))
    (A i) (sigmaSet A) (pieceIncl (Y := Y) i)
    (fun x hx => pieceIncl_mem_sigmaSet A i x hx) n

/-- The underlying cochain of the relative restriction. -/
theorem restrRel_coe (R : Type) [CommRing R] (A : ∀ i, Set (Y i)) (i : ι) (n : ℕ)
    (v : Work.Cohomology.relKern R (TopCat.of (Σ i, Y i)) (sigmaSet A) n) :
    (restrRel R A i n v).1 = restr R i n v.1 := by
  rw [restrRel, Work.Cohomology.relMapLM_coe, Work.Cohomology.dualChainMap_f_hom]
  rfl

/-! ## The relative assembly -/

/-- **Assembly of a family of relative cochains.** -/
noncomputable def assembleRel (R : Type) [CommRing R] (A : ∀ i, Set (Y i)) (n : ℕ)
    (w : ∀ i, Work.Cohomology.relKern R (TopCat.of (Y i)) (A i) n) :
    Work.Cohomology.relKern R (TopCat.of (Σ i, Y i)) (sigmaSet A) n :=
  ⟨assemble R n (fun i => (w i).1), by
    rw [relKern_iff R (TopCat.of (Σ i, Y i)) (sigmaSet A) n]
    intro τ hτ
    rw [genEval_assemble (ι := ι) (Y := Y)]
    have hτ' : ∀ u, (TopCat.toSSetObjEquiv (TopCat.of (Y (split (Y := Y) n τ).1)) _)
        (split (Y := Y) n τ).2 u ∈ A (split (Y := Y) n τ).1 := by
      intro u
      have h1 := hτ u
      rw [← legs_split (ι := ι) (Y := Y) n τ] at h1
      rw [show (TopCat.toSSetObjEquiv (TopCat.of (Σ i, Y i)) _)
            (legs (ι := ι) (Y := Y) n (split (ι := ι) (Y := Y) n τ)) u
          = ⟨(split (Y := Y) n τ).1,
              (TopCat.toSSetObjEquiv (TopCat.of (Y (split (Y := Y) n τ).1)) _)
                (split (Y := Y) n τ).2 u⟩ from rfl] at h1
      exact h1
    exact (relKern_iff R (TopCat.of (Y (split (Y := Y) n τ).1))
      (A (split (Y := Y) n τ).1) n (w (split (Y := Y) n τ).1).1).mp
      (w (split (Y := Y) n τ).1).2 (split (Y := Y) n τ).2 hτ'⟩

/-- The underlying cochain of the relative assembly. -/
theorem assembleRel_coe (R : Type) [CommRing R] (A : ∀ i, Set (Y i)) (n : ℕ)
    (w : ∀ i, Work.Cohomology.relKern R (TopCat.of (Y i)) (A i) n) :
    (assembleRel R A n w).1 = assemble R n (fun i => (w i).1) := rfl

/-! ## The two relative maps are inverse to each other -/

/-- **The relative assembly is a right inverse of the relative restriction.** -/
theorem restrRel_assembleRel (R : Type) [CommRing R] (A : ∀ i, Set (Y i)) (n : ℕ)
    (w : ∀ i, Work.Cohomology.relKern R (TopCat.of (Y i)) (A i) n) (j : ι) :
    restrRel R A j n (assembleRel R A n w) = w j := by
  refine Subtype.ext ?_
  simp only [restrRel_coe, assembleRel_coe, restr_assemble]

/-- **The relative assembly is a left inverse of the relative restriction.** -/
theorem assembleRel_restrRel (R : Type) [CommRing R] (A : ∀ i, Set (Y i)) (n : ℕ)
    (v : Work.Cohomology.relKern R (TopCat.of (Σ i, Y i)) (sigmaSet A) n) :
    assembleRel R A n (fun i => restrRel R A i n v) = v := by
  refine Subtype.ext ?_
  rw [assembleRel_coe]
  simp only [restrRel_coe]
  exact assemble_restr (R := R) (Y := Y) n v.1

/-! ## Compatibility with the relative differentials -/

/-- The underlying cochain of the relative differential of an assembled family. -/
theorem relDiffLM_assembleRel_coe (R : Type) [CommRing R] (A : ∀ i, Set (Y i)) (n : ℕ)
    (w : ∀ i, Work.Cohomology.relKern R (TopCat.of (Y i)) (A i) n) :
    ((Work.Cohomology.relDiffLM R (TopCat.of (Σ i, Y i)) (sigmaSet A) n
        (assembleRel R A n w)).1 : Work.Cohomology.Cochain R (Ssig ι Y) (n + 1)) =
      assemble R (n + 1) (fun i =>
        ((Work.Cohomology.relDiffLM R (TopCat.of (Y i)) (A i) n (w i)).1
          : Work.Cohomology.Cochain R (Spiece ι Y i) (n + 1))) := by
  calc ((Work.Cohomology.relDiffLM R (TopCat.of (Σ i, Y i)) (sigmaSet A) n
          (assembleRel R A n w)).1 : Work.Cohomology.Cochain R (Ssig ι Y) (n + 1))
      = Work.Cohomology.cochainDiff R (Ssig ι Y) (assemble R n (fun i => (w i).1)) := by
        simp only [Work.Cohomology.relDiffLM_coe, Work.Cohomology.singularCochain_d_apply,
          assembleRel_coe]
    _ = assemble R (n + 1) (fun i =>
          Work.Cohomology.cochainDiff R (Spiece ι Y i) (w i).1) :=
        cochainDiff_assemble (ι := ι) (Y := Y) n (fun i => (w i).1)
    _ = assemble R (n + 1) (fun i =>
          ((Work.Cohomology.relDiffLM R (TopCat.of (Y i)) (A i) n (w i)).1
            : Work.Cohomology.Cochain R (Spiece ι Y i) (n + 1))) := by
        simp only [Work.Cohomology.relDiffLM_coe, Work.Cohomology.singularCochain_d_apply]

/-- The underlying cochain of the relative differential of a restricted cochain. -/
theorem relDiffLM_restrRel_coe (R : Type) [CommRing R] (A : ∀ i, Set (Y i)) (i : ι) (n : ℕ)
    (v : Work.Cohomology.relKern R (TopCat.of (Σ i, Y i)) (sigmaSet A) n) :
    ((Work.Cohomology.relDiffLM R (TopCat.of (Y i)) (A i) n (restrRel R A i n v)).1
        : Work.Cohomology.Cochain R (Spiece ι Y i) (n + 1)) =
      restr R i (n + 1) ((Work.Cohomology.relDiffLM R (TopCat.of (Σ i, Y i)) (sigmaSet A) n v).1
        : Work.Cohomology.Cochain R (Ssig ι Y) (n + 1)) := by
  calc ((Work.Cohomology.relDiffLM R (TopCat.of (Y i)) (A i) n (restrRel R A i n v)).1
        : Work.Cohomology.Cochain R (Spiece ι Y i) (n + 1))
      = Work.Cohomology.cochainDiff R (Spiece ι Y i) (restr R i n v.1) := by
        simp only [Work.Cohomology.relDiffLM_coe, Work.Cohomology.singularCochain_d_apply,
          restrRel_coe]
    _ = restr R i (n + 1) (Work.Cohomology.cochainDiff R (Ssig ι Y) v.1) :=
        cochainDiff_restr (ι := ι) (Y := Y) n i v.1
    _ = restr R i (n + 1)
          ((Work.Cohomology.relDiffLM R (TopCat.of (Σ i, Y i)) (sigmaSet A) n v).1
            : Work.Cohomology.Cochain R (Ssig ι Y) (n + 1)) := by
        simp only [Work.Cohomology.relDiffLM_coe, Work.Cohomology.singularCochain_d_apply]

/-- **The relative differential commutes with the relative restriction.** -/
theorem relDiffLM_restrRel (R : Type) [CommRing R] (A : ∀ i, Set (Y i)) (i : ι) (n : ℕ)
    (v : Work.Cohomology.relKern R (TopCat.of (Σ i, Y i)) (sigmaSet A) n) :
    Work.Cohomology.relDiffLM R (TopCat.of (Y i)) (A i) n (restrRel R A i n v) =
      restrRel R A i (n + 1)
        (Work.Cohomology.relDiffLM R (TopCat.of (Σ i, Y i)) (sigmaSet A) n v) := by
  refine Subtype.ext ?_
  rw [relDiffLM_restrRel_coe R A i n v]
  rw [restrRel_coe R A i (n + 1)
    (Work.Cohomology.relDiffLM R (TopCat.of (Σ i, Y i)) (sigmaSet A) n v)]

end

end Work.Serre.Sigma
