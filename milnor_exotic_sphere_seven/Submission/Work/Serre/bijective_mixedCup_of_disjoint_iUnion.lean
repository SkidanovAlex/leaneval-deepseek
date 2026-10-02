import Mathlib
import Submission.Work.Serre.ThmCylSigma.Main
import Submission.Work.Serre.ThmCylSigma.Assembly
import Submission.Work.Serre.ThmCylSigma.bijectiveSigmaCup
import Submission.Work.Serre.CellStep.sigmaHomeoApply
import Submission.Work.RatHurewicz.bijective_mixedCup_of_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Work.Serre

/-- **The local-to-global gluing of the mixed cup map over an arbitrary disjoint open cover.**

`Work.RatHurewicz.bijective_mixedCup_of_disjoint_pair` (the proved case of a cover by two disjoint
open sets) with the two pieces replaced by an arbitrary family `V : ι → Set Z` of pairwise disjoint
open sets covering `Z`.  This is what the Mayer–Vietoris assembly of the cellular step needs for an
**arbitrary** index type `ι` (the attaching family may be infinite).

Route: `Z ≅ Σ i, ↥(V i)` for a disjoint open cover; the σ-type machinery of
`Work.Serre.ThmCylSigma` gives both the product decomposition
(`Work.Serre.ThmCylSigma.relZero_of_restr_zero`, `…exists_relClass_sigma`, and the absolute
companions `Coh_sigma_eq_zero_of_restr_eq_zero`, `exists_Coh_sigma_of_restr`, all for arbitrary `ι`)
and the cup compatibility (`Work.Serre.ThmCylSigma.relCohMap_mixedCup_sigmaMap`); hence
`x ↦ x ⌣ U₀` is coordinatewise the local cup maps, and a coordinatewise (diagonal) map between
product decompositions is bijective iff each coordinate is. -/
theorem bijective_mixedCup_of_disjoint_iUnion {Z : Type} [TopologicalSpace Z] {ι : Type}
    (A : Set Z) (V : ι → Set Z) (hVopen : ∀ i, IsOpen (V i))
    (hcov : (⋃ i, V i) = Set.univ) (hVdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (n₀ K : ℕ) (hn₀ : 0 < n₀) (U₀ : Work.Thom.RelCoh ℚ n₀ Z A)
    (hloc : ∀ i, ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(V i) =>
      (Work.Thom.mixedCupC ℚ {y : ↥(V i) | (y : Z) ∈ A} m n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(V i), Z))
          {y : ↥(V i) | (y : Z) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀))) :
    ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m Z =>
      (Work.Thom.mixedCupC ℚ A m n₀) x U₀) := by
  classical
  -- the disjoint-union homeomorphism
  obtain ⟨e, he_val, he_idx⟩ :=
    Work.Serre.CellStep.sigmaHomeoApply V hVopen (fun i j hij => hVdisj i j hij) hcov
  -- the trace of A on the pieces
  let A' : ∀ i, Set ↥(V i) := fun i => {y | (y : Z) ∈ A}
  -- the inverse of the homeomorphism, pointwise
  have hsymm : ∀ p : Σ i, ↥(V i), e.symm p = (p.2 : Z) := by
    intro p
    have h := he_val (e.symm p)
    rw [e.apply_symm_apply p] at h
    exact h.symm
  -- the pair condition for the pushforward of U₀ along e.symm
  have hmem : ∀ x ∈ Work.Serre.Sigma.sigmaSet A', e.symm x ∈ A := by
    intro x hx
    rw [hsymm x]
    exact hx
  -- Uσ: the pushforward of U₀ to the disjoint union
  let Uσ : Work.Thom.RelCoh ℚ n₀ (Σ i, ↥(V i)) (Work.Serre.Sigma.sigmaSet A') :=
    (Work.Thom.relCohMap (e.symm : C(Σ i, ↥(V i), Z)) (Work.Serre.Sigma.sigmaSet A') A
      hmem ℚ n₀).hom U₀
  -- the restrictions of Uσ are the restrictions of U₀ to the pieces
  have hrestr : ∀ i, (Work.Thom.relCohMap
      (Work.Serre.Sigma.pieceIncl (Y := fun i => ↥(V i)) i).hom
      (A' i) (Work.Serre.Sigma.sigmaSet A')
      (fun x hx => Work.Serre.Sigma.pieceIncl_mem_sigmaSet A' i x hx) ℚ n₀).hom Uσ
      = (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(V i), Z)) (A' i) A
          (fun _ hy => hy) ℚ n₀).hom U₀ := by
    intro i
    have hcomp : (e.symm : C(Σ i, ↥(V i), Z)).comp
        ((Work.Serre.Sigma.pieceIncl (Y := fun i => ↥(V i)) i).hom) =
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(V i), Z)) := by
      ext y
      exact hsymm ⟨i, y⟩
    have hpi : ∀ x ∈ A' i, (Work.Serre.Sigma.pieceIncl (Y := fun i => ↥(V i)) i).hom x ∈
        Work.Serre.Sigma.sigmaSet A' :=
      fun x hx => Work.Serre.Sigma.pieceIncl_mem_sigmaSet A' i x hx
    have hgf : ∀ x ∈ A' i, ((e.symm : C(Σ i, ↥(V i), Z)).comp
        (Work.Serre.Sigma.pieceIncl (Y := fun i => ↥(V i)) i).hom) x ∈ A :=
      fun x hx => hmem _ (hpi x hx)
    have h1 := Work.Thom.relCohMap_compA_apply (A' i) (Work.Serre.Sigma.sigmaSet A') A
      ((Work.Serre.Sigma.pieceIncl (Y := fun i => ↥(V i)) i).hom)
      (e.symm : C(Σ i, ↥(V i), Z)) hpi hmem hgf ℚ n₀ U₀
    have hstep : (Work.Thom.relCohMap ((e.symm : C(Σ i, ↥(V i), Z)).comp
          (Work.Serre.Sigma.pieceIncl (Y := fun i => ↥(V i)) i).hom) (A' i) A hgf ℚ n₀).hom U₀
        = (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(V i), Z)) (A' i) A
            (fun _ hy => hy) ℚ n₀).hom U₀ :=
      congrArg (fun φ => φ.hom U₀)
        (Work.Thom.relCohMap_congrA (A' i) A hcomp hgf (fun _ hy => hy) ℚ n₀)
    exact h1.trans hstep
  -- the piecewise cup maps are the hypotheses
  have hU : ∀ i k, k + n₀ ≤ K → Function.Bijective
      (fun x : Work.Thom.Coh ℚ k ↥(V i) =>
        (Work.Thom.mixedCupC ℚ (A' i) k n₀)
          ((Work.Thom.CohMap (ContinuousMap.id ↥(V i)) ℚ k).hom x)
          ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(V i), Z))
            (A' i) A (fun _ hy => hy) ℚ n₀).hom U₀)) := by
    intro i k hk
    simpa using hloc i k hk
  -- the sigma-type cup map is bijective
  have hσ : ∀ k, k + n₀ ≤ K → Function.Bijective
      (fun x : Work.Thom.Coh ℚ k (Σ i, ↥(V i)) =>
        (Work.Thom.mixedCupC ℚ (Work.Serre.Sigma.sigmaSet A') k n₀) x Uσ) := by
    intro k hk
    have h := Work.Serre.ThmCylSigma.bijectiveSigmaCup A'
      (fun i => ContinuousMap.id ↥(V i)) n₀ K hn₀ Uσ
      (fun i => (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(V i), Z))
          (A' i) A (fun _ hy => hy) ℚ n₀).hom U₀) hrestr hU k hk
    have h2 : Work.Serre.Sigma.sigmaMap (fun i => ContinuousMap.id ↥(V i)) =
        ContinuousMap.id (Σ i, ↥(V i)) := ContinuousMap.ext fun z => rfl
    rw [h2] at h
    simpa only [Work.Thom.CohMap_id, ModuleCat.hom_id, LinearMap.id_apply] using h
  intro m hm
  have he : ∀ z : Z, z ∈ A ↔ e z ∈ Work.Serre.Sigma.sigmaSet A' := by
    intro z
    show z ∈ A ↔ ((e z).2 : Z) ∈ A
    rw [he_val z]
  have hb := Work.RatHurewicz.bijective_mixedCup_of_homeo e A
    (Work.Serre.Sigma.sigmaSet A') he m n₀ Uσ (hσ m hm)
  have hU₀eq : (Work.Thom.relCohMap (e : C(Z, Σ i, ↥(V i))) A
      (Work.Serre.Sigma.sigmaSet A') (fun x hx => (he x).mp hx) ℚ n₀).hom Uσ = U₀ := by
    have hf : ∀ x ∈ A, (e : C(Z, Σ i, ↥(V i))) x ∈ Work.Serre.Sigma.sigmaSet A' :=
      fun x hx => (he x).mp hx
    have hgf : ∀ x ∈ A, ((e.symm : C(Σ i, ↥(V i), Z)).comp (e : C(Z, Σ i, ↥(V i)))) x ∈ A :=
      fun x hx => hmem _ (hf x hx)
    have h1 := Work.Thom.relCohMap_compA_apply A (Work.Serre.Sigma.sigmaSet A') A
      (e : C(Z, Σ i, ↥(V i))) (e.symm : C(Σ i, ↥(V i), Z)) hf hmem hgf ℚ n₀ U₀
    have hcomp : (e.symm : C(Σ i, ↥(V i), Z)).comp (e : C(Z, Σ i, ↥(V i))) =
        ContinuousMap.id Z := ContinuousMap.ext fun z => e.symm_apply_apply z
    have hstep : (Work.Thom.relCohMap ((e.symm : C(Σ i, ↥(V i), Z)).comp
          (e : C(Z, Σ i, ↥(V i)))) A A hgf ℚ n₀).hom U₀ = U₀ := by
      have h2 : (Work.Thom.relCohMap ((e.symm : C(Σ i, ↥(V i), Z)).comp
            (e : C(Z, Σ i, ↥(V i)))) A A hgf ℚ n₀).hom U₀
          = (Work.Thom.relCohMap (ContinuousMap.id Z) A A (fun _ h => h) ℚ n₀).hom U₀ :=
        congrArg (fun φ => φ.hom U₀)
          (Work.Thom.relCohMap_congrA A A hcomp hgf (fun _ h => h) ℚ n₀)
      rw [h2, Work.Thom.relCohMap_idA A ℚ n₀]
      simp only [ModuleCat.hom_id, LinearMap.id_apply]
    exact h1.trans hstep
  rw [hU₀eq] at hb
  exact hb

end Work.Serre
