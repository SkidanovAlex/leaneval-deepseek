import Mathlib
import Submission.Work.CFTLib.ContCohomology.Setup
import Submission.Work.CFTLib.ContCohomology.evalIter_mem_homCochain
import Submission.Work.CFTLib.ContCohomology.exists_evalIter_eq

/-!
# The complex of invariants of the `coind₁`-resolution is the homogeneous cochain complex

Mathlib's `continuousCohomology n X` is the homology of the complex of invariants of the
`coind₁`-resolution `X → C(Γ, X) → ⋯`.  This file identifies that complex with the classical
homogeneous cochain complex `homCochain X •` of invariant continuous functions on the powers of
`Γ`, with the simplicial differential `homDiff`.

## Main results

* `evalIterEquiv` — the termwise linear equivalence.
* `evalIterEquiv_homDiff` — it intertwines the differentials.
* `homDiff_comp_homDiff` — the differential squares to zero.
-/

noncomputable section

open TopRep CategoryTheory

namespace Work.CFTLib.ContCohomology

variable {k Γ : Type} [CommRing k] [TopologicalSpace k] [Group Γ] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]

variable (X : TopRep k Γ)

/-- The `n`-th term of the complex of invariants of the `coind₁`-resolution maps, by iterated
evaluation, to the invariant continuous functions on `Γ^{n+1}`. -/
def evalIterMap (n : ℕ) :
    ↥((TopRep.resolutionX X (n+1)).ρ.invariants) →ₗ[k] ↥(homCochain X n) where
  toFun Φ := ⟨fun x => evalIter X (n+1) Φ.1 x, evalIter_mem_homCochain X n Φ.1 Φ.2⟩
  map_add' Φ Ψ := by ext x; simp [evalIter_add]
  map_smul' r Φ := by ext x; simp [evalIter_smul]

@[simp] lemma evalIterMap_apply (n : ℕ) (Φ : ↥((TopRep.resolutionX X (n+1)).ρ.invariants))
    (x : Fin (n+1) → Γ) :
    (evalIterMap X n Φ).1 x = evalIter X (n+1) Φ.1 x := rfl

/-- **The `n`-th term of the complex of invariants of the `coind₁`-resolution is the module of
invariant continuous functions on `Γ^{n+1}`.** -/
noncomputable def evalIterEquiv (n : ℕ) :
    ↥((TopRep.resolutionX X (n+1)).ρ.invariants) ≃ₗ[k] ↥(homCochain X n) :=
  LinearEquiv.ofBijective (evalIterMap X n)
    ⟨fun Φ Ψ h => by
      apply Subtype.ext
      refine evalIter_ext X (n+1) ?_
      funext x
      exact congrFun (congrArg Subtype.val h) x,
     fun f => by
      obtain ⟨Φ, hinv, hΦ⟩ := exists_evalIter_eq X n f
      exact ⟨⟨Φ, hinv⟩, Subtype.ext (funext hΦ)⟩⟩

@[simp] lemma evalIterEquiv_apply (n : ℕ) (Φ : ↥((TopRep.resolutionX X (n+1)).ρ.invariants))
    (x : Fin (n+1) → Γ) :
    (evalIterEquiv X n Φ).1 x = evalIter X (n+1) Φ.1 x := rfl

/-- **The differential of the `coind₁`-resolution is the simplicial differential.** -/
theorem evalIterEquiv_homDiff (n : ℕ) (Φ : ↥((TopRep.resolutionX X (n+1)).ρ.invariants)) :
    evalIterEquiv X (n+1) ((TopRep.invariantsFunctor k Γ).map (TopRep.d X (n+1)) Φ) =
      homDiff X n (evalIterEquiv X n Φ) := by
  apply Subtype.ext
  funext x
  rw [evalIterEquiv_apply, homDiff_apply]
  rw [show (((TopRep.invariantsFunctor k Γ).map (TopRep.d X (n+1))) Φ :
        ↥(TopRep.resolutionX X (n+2))) = (TopRep.d X (n+1)).hom Φ.1 from rfl]
  rw [evalIter_d]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [evalIterEquiv_apply]
  rfl

/-- **The homogeneous differential squares to zero.** -/
theorem homDiff_comp_homDiff (n : ℕ) (f : ↥(homCochain X n)) :
    homDiff X (n+1) (homDiff X n f) = 0 := by
  obtain ⟨Φ, hΦ⟩ := (evalIterEquiv X n).surjective f
  rw [← hΦ, ← evalIterEquiv_homDiff X n Φ,
    ← evalIterEquiv_homDiff X (n+1)
      ((TopRep.invariantsFunctor k Γ).map (TopRep.d X (n+1)) Φ)]
  have hzero : ((TopRep.invariantsFunctor k Γ).map (TopRep.d X (n+2)))
      (((TopRep.invariantsFunctor k Γ).map (TopRep.d X (n+1))) Φ) = 0 := by
    have hcomp : (TopRep.invariantsFunctor k Γ).map (TopRep.d X (n+1)) ≫
        (TopRep.invariantsFunctor k Γ).map (TopRep.d X (n+2)) = 0 := by
      rw [← Functor.map_comp, TopRep.d_comp_d, Functor.map_zero]
    have h := congrArg (fun (ψ : (TopRep.invariantsFunctor k Γ).obj (TopRep.resolutionX X (n+1)) ⟶
        (TopRep.invariantsFunctor k Γ).obj (TopRep.resolutionX X (n+3))) => ψ Φ) hcomp
    simpa using h
  rw [hzero, map_zero]

end Work.CFTLib.ContCohomology

namespace Work.CFTLib.ContCohomology

variable {k Γ : Type} [CommRing k] [TopologicalSpace k] [Group Γ] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]

/-- The short complex of homogeneous cochains in degrees `n, n+1, n+2`. -/
noncomputable def homShortComplex (X : TopRep k Γ) (n : ℕ) : ShortComplex (ModuleCat k) :=
  ShortComplex.mk (ModuleCat.ofHom (homDiff X n)) (ModuleCat.ofHom (homDiff X (n+1)))
    (by
      ext f x
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply]
      exact congrFun (congrArg Subtype.val (homDiff_comp_homDiff X n f)) x)

/-- The short complex of invariants of the `coind₁`-resolution, forgotten to `ModuleCat`. -/
noncomputable abbrev invariantsShortComplex (X : TopRep k Γ) (n : ℕ) : ShortComplex (ModuleCat k) :=
  ((TopRep.homogeneousCochains X).sc n).map (forget₂ (TopModuleCat k) (ModuleCat k))

end Work.CFTLib.ContCohomology
