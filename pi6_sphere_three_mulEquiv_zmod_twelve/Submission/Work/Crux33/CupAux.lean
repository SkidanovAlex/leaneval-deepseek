import Mathlib
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.Pullback

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

/-!
# Auxiliary lemmas for the two-factor cup-product crux `Work.Crux33.cupSph3Sph3_crux`

Two groups of lemmas:

* `Work.Crux33.mem_degenerate_of_not_injective` — a simplex obtained from a non-injective monotone
  self-map is degenerate.  This is the junk-killing step of the Eilenberg–Zilber shuffle
  computation (every shuffle other than `E E E N N N` produces a non-injective monotone map, hence
  a degenerate face, killed by a normalized cocycle).

* the mechanical **`β`-half** of the normalized-cocycle input: `PInf X n` is the degree-`n`
  component of `PInfty := SSet.toNormalizedChainComplex ≫ SSet.fromNormalizedChainComplex`; it is
  a chain map (`PInf_comm`), kills degenerate simplices (`PInf_degenerate`), and agrees with the
  identity on cycles (`PInf_apply_cycle_eq`, from the chain homotopy `homotopyHomInvId`).
  Hence `α ∘ PInfty` is a *normalized* cocycle with the same value as `α` on cycles
  (`exists_normalized_of_cycle_cocycle`).
-/

namespace Work.Cohomology

/-- Degree-`n` component of `PInfty := toNormalizedChainComplex ≫ fromNormalizedChainComplex`. -/
noncomputable abbrev PInf (X : SSet) (n : ℕ) :
    (X.chainComplex (ModuleCat.of ℤ ℤ)).X n →ₗ[ℤ] (X.chainComplex (ModuleCat.of ℤ ℤ)).X n :=
  ModuleCat.Hom.hom ((SSet.toNormalizedChainComplex X (ModuleCat.of ℤ ℤ) ≫
    SSet.fromNormalizedChainComplex X (ModuleCat.of ℤ ℤ)).f n)

/-- `PInfty` kills degenerate simplices. -/
lemma PInf_degenerate (X : SSet) (x : X _⦋3⦌) (hx : x ∈ X.degenerate 3) :
    PInf X 3 (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1)) = 0 := by
  have hto : (ModuleCat.Hom.hom (((SSet.toNormalizedChainComplex X (ModuleCat.of ℤ ℤ)).f 3)))
      (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1)) = 0 := by
    have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
        (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)).X 3) => g.hom 1)
      (SSet.ιChainComplex_toNormalizedChainComplex_f X (R := ModuleCat.of ℤ ℤ) x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, SSet.ιNormalizedChainComplex_eq_zero X (R := ModuleCat.of ℤ ℤ) x hx]
    simp
  simp only [PInf, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, hto,
    map_zero]

/-- `PInfty` commutes with the differentials (linear-map form of the chain-map property). -/
lemma PInf_comm (X : SSet) (i j : ℕ) :
    (((X.chainComplex (ModuleCat.of ℤ ℤ)).d i j).hom).comp (PInf X i) =
      (PInf X j).comp (((X.chainComplex (ModuleCat.of ℤ ℤ)).d i j).hom) := by
  have h := congrArg (fun (g : (X.chainComplex (ModuleCat.of ℤ ℤ)).X i ⟶
        (X.chainComplex (ModuleCat.of ℤ ℤ)).X j) => ModuleCat.Hom.hom g)
    (HomologicalComplex.Hom.comm (SSet.toNormalizedChainComplex X (ModuleCat.of ℤ ℤ) ≫
      SSet.fromNormalizedChainComplex X (ModuleCat.of ℤ ℤ)) i j)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp] at h
  simpa only [PInf, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_assoc]
    using h

/-- The coboundary of `α ∘ PInfty` vanishes for a cocycle `α`. -/
lemma cochainDiff_comp_PInf (X : SSet) (α : Cochain ℤ X 3) (hα : cochainDiff ℤ X α = 0) :
    cochainDiff ℤ X (α.comp (PInf X 3)) = 0 := by
  show (α.comp (PInf X 3)).comp (((X.chainComplex (ModuleCat.of ℤ ℤ)).d 4 3).hom) = 0
  rw [LinearMap.comp_assoc, ← PInf_comm X 4 3, ← LinearMap.comp_assoc]
  rw [show (α.comp (((X.chainComplex (ModuleCat.of ℤ ℤ)).d 4 3).hom))
      = cochainDiff ℤ X α from rfl, hα]
  simp

/-- On a cycle, `α ∘ PInfty` agrees with `α` for every cocycle `α`. -/
lemma PInf_apply_cycle_eq (X : SSet) (σ : X _⦋3⦌)
    (hσ : (((X.chainComplex (ModuleCat.of ℤ ℤ)).d 3 2).hom)
      (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)) = 0)
    (α : Cochain ℤ X 3) (hα : cochainDiff ℤ X α = 0) :
    α (PInf X 3 (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1))) =
      α (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)) := by
  set c := ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1) with hc
  set H := X.homotopyEquivNormalizedChainComplex (ModuleCat.of ℤ ℤ) with hH
  have hcomm := congrArg (fun (f : (X.chainComplex (ModuleCat.of ℤ ℤ)).X 3 ⟶
      (X.chainComplex (ModuleCat.of ℤ ℤ)).X 3) => f.hom c) (H.homotopyHomInvId.comm 3)
  rw [HomologicalComplex.comp_f] at hcomm
  simp only [ModuleCat.hom_add, LinearMap.add_apply] at hcomm
  have hD : (ModuleCat.Hom.hom ((dNext 3) H.homotopyHomInvId.hom)) c = 0 := by
    rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel 3 2 from rfl), ModuleCat.hom_comp]
    simp only [LinearMap.comp_apply, hσ, map_zero]
  rw [hD, zero_add] at hcomm
  rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel 4 3 from rfl)] at hcomm
  rw [ModuleCat.hom_comp] at hcomm
  simp only [LinearMap.comp_apply] at hcomm
  rw [show (ModuleCat.Hom.hom (((𝟙 (X.chainComplex (ModuleCat.of ℤ ℤ)) :
      X.chainComplex (ModuleCat.of ℤ ℤ) ⟶ X.chainComplex (ModuleCat.of ℤ ℤ))).f 3)) c = c
      from rfl] at hcomm
  have hhom : H.hom = X.toNormalizedChainComplex (ModuleCat.of ℤ ℤ) := by
    rw [hH]; exact SSet.homotopyEquivNormalizedChainComplex_hom X (ModuleCat.of ℤ ℤ)
  have hinv : H.inv = X.fromNormalizedChainComplex (ModuleCat.of ℤ ℤ) := by
    rw [hH]; exact SSet.homotopyEquivNormalizedChainComplex_inv X (ModuleCat.of ℤ ℤ)
  have hcomp : PInf X 3 c
      = (ModuleCat.Hom.hom (H.inv.f 3)) ((ModuleCat.Hom.hom (H.hom.f 3)) c) := by
    simp only [PInf, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      hhom, hinv]
  have hcomm' : (ModuleCat.Hom.hom (H.inv.f 3)) ((ModuleCat.Hom.hom (H.hom.f 3)) c)
      = ((X.chainComplex (ModuleCat.of ℤ ℤ)).d 4 3).hom
          ((H.homotopyHomInvId.hom 3 4) c) + c := by
    rw [hcomm, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hzero : α (((X.chainComplex (ModuleCat.of ℤ ℤ)).d 4 3).hom
      ((H.homotopyHomInvId.hom 3 4) c)) = 0 := by
    have h := congrArg (fun (g : (X.chainComplex (ModuleCat.of ℤ ℤ)).X 4 →ₗ[ℤ] ℤ) =>
      g ((H.homotopyHomInvId.hom 3 4) c)) hα
    simpa only [cochainDiff, LinearMap.comp_apply, LinearMap.zero_apply] using h
  rw [hcomp, hcomm', map_add, hzero, zero_add]

/-- **The `β`-half of the normalized-cocycle input.**  Given a *cyclic* `3`-simplex `σ` and a
`3`-cocycle `α` nonzero on `σ`, there is a normalized `3`-cocycle `β` (vanishing on every
degenerate `3`-simplex) with `β(σ) ≠ 0`: take `β := α ∘ PInfty`. -/
lemma exists_normalized_of_cycle_cocycle (X : SSet) (σ : X _⦋3⦌)
    (hσ : (((X.chainComplex (ModuleCat.of ℤ ℤ)).d 3 2).hom)
      (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)) = 0)
    (α : Cochain ℤ X 3) (hα : cochainDiff ℤ X α = 0)
    (hασ : α (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)) ≠ 0) :
    ∃ β : Cochain ℤ X 3,
      cochainDiff ℤ X β = 0 ∧
      (∀ x : X _⦋3⦌, x ∈ X.degenerate 3 →
        β (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1)) = 0) ∧
      β (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)) ≠ 0 :=
  ⟨α.comp (PInf X 3), cochainDiff_comp_PInf X α hα,
    fun x hx => by simp only [LinearMap.comp_apply, PInf_degenerate X x hx, map_zero],
    by rw [LinearMap.comp_apply, PInf_apply_cycle_eq X σ hσ α hα]; exact hασ⟩

end Work.Cohomology

namespace Work.Crux33

/-- **A simplex obtained from a non-injective monotone self-map is degenerate.**

If `f : ⦋n+1⦌ ⟶ ⦋n+1⦌` is not injective on vertices and `x` is an `(n+1)`-simplex of a simplicial
set `X`, then `X.map f.op x` lies in `X.degenerate (n+1)`:
`SimplexCategory.eq_σ_comp_of_not_injective` writes `f = σ i ≫ f'` through a degeneracy, and
degeneracies land in `X.degenerate` (`SSet.σ_mem_degenerate`). -/
lemma mem_degenerate_of_not_injective {X : SSet} (n : ℕ) (f : ⦋n + 1⦌ ⟶ ⦋n + 1⦌)
    (hf : ¬ Function.Injective f.toOrderHom) (x : X _⦋n + 1⦌) :
    X.map f.op x ∈ X.degenerate (n + 1) := by
  obtain ⟨i, f', hf'⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hf
  rw [hf', CategoryTheory.op_comp, Functor.map_comp]
  exact X.σ_mem_degenerate i (X.map f'.op x)

end Work.Crux33
