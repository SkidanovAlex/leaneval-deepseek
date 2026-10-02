import Mathlib
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.SphDefs
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.kronH_isIso
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.Chains

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A normalized detected pair on the sphere `Sᵖ`

This file proves `Work.KunnethEZ.normalizedDetectedPairSph`: on the sphere `Sᵖ = sphTop (p+1)`
(`p ≥ 1`) there is a `p`-cocycle `θ` which vanishes on every degenerate `p`-simplex, and a
`p`-cycle `u` with `θ u ≠ 0`.

The proof is the degree-`n` version of the general "normalized detected pair" construction used
elsewhere in the library (`Work.Sph3Disc.normalized_detected_pair` is the degree-`3` case):

* `Work.Cohomology.kronH_isIso` identifies `Hⁿ(X;ℤ)` with `Hom(Hₙ(X;ℤ), ℤ)` when the homology of
  `X` is degreewise free, so a nonzero class is detected by a cycle;
* `normP` is the degree-`n` component of `toNormalizedChainComplex ≫ fromNormalizedChainComplex`;
  composing a cocycle with it produces a normalized cocycle with the same value on cycles.

For the sphere both inputs are available: `Hₖ(Sᵖ)` is free in every degree
(`sphereHomology_aux` in degree `p`, `sphereVanishing_aux` elsewhere, path connectedness in
degree `0`) and `Hₚ(Sᵖ) ≅ ℤ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.KunnethEZ

noncomputable section

/-- `ℤ` as a module, spelled once. -/
abbrev ndpsR : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-! ## The projection onto the normalized chains in degree `n` -/

/-- Degree-`n` component of `PInfty := toNormalizedChainComplex ≫ fromNormalizedChainComplex`. -/
noncomputable abbrev normP (X : SSet) (n : ℕ) :
    (X.chainComplex ndpsR).X n →ₗ[ℤ] (X.chainComplex ndpsR).X n :=
  ModuleCat.Hom.hom ((SSet.toNormalizedChainComplex X ndpsR ≫
    SSet.fromNormalizedChainComplex X ndpsR).f n)

/-- `normP X n` kills degenerate `n`-simplices. -/
lemma normP_degenerate (X : SSet) (n : ℕ) (x : X _⦋n⦌) (hx : x ∈ X.degenerate n) :
    normP X n ((X.ιChainComplex (R := ndpsR) x).hom 1) = 0 := by
  have hto : (ModuleCat.Hom.hom ((SSet.toNormalizedChainComplex X ndpsR).f n))
      ((X.ιChainComplex (R := ndpsR) x).hom 1) = 0 := by
    have h := congrArg (fun (g : ndpsR ⟶ (X.normalizedChainComplex ndpsR).X n) => g.hom 1)
      (SSet.ιChainComplex_toNormalizedChainComplex_f X (R := ndpsR) x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, SSet.ιNormalizedChainComplex_eq_zero X (R := ndpsR) x hx]
    simp
  simp only [normP, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, hto,
    map_zero]

/-- `normP` commutes with the differentials (linear-map form of the chain-map property). -/
lemma normP_comm (X : SSet) (i j : ℕ) :
    (((X.chainComplex ndpsR).d i j).hom).comp (normP X i) =
      (normP X j).comp (((X.chainComplex ndpsR).d i j).hom) := by
  have h := congrArg (fun (g : (X.chainComplex ndpsR).X i ⟶ (X.chainComplex ndpsR).X j) =>
      ModuleCat.Hom.hom g)
    (HomologicalComplex.Hom.comm (SSet.toNormalizedChainComplex X ndpsR ≫
      SSet.fromNormalizedChainComplex X ndpsR) i j)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp] at h
  simpa only [normP, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_assoc] using h

/-- The coboundary of `α ∘ normP` vanishes for a cocycle `α`. -/
lemma cochainDiff_comp_normP (X : SSet) (n : ℕ) (α : Work.Cohomology.Cochain ℤ X n)
    (hα : Work.Cohomology.cochainDiff ℤ X α = 0) :
    Work.Cohomology.cochainDiff ℤ X (α.comp (normP X n)) = 0 := by
  show (α.comp (normP X n)).comp (((X.chainComplex ndpsR).d (n + 1) n).hom) = 0
  rw [LinearMap.comp_assoc, ← normP_comm X (n + 1) n, ← LinearMap.comp_assoc]
  rw [show (α.comp (((X.chainComplex ndpsR).d (n + 1) n).hom))
      = Work.Cohomology.cochainDiff ℤ X α from rfl, hα]
  simp

/-- On a cycle, `α ∘ normP` agrees with `α` for every cocycle `α`. -/
lemma normP_apply_cycle_eq (X : SSet) (n : ℕ) (hn : 1 ≤ n)
    (c : (X.chainComplex ndpsR).X n)
    (hc : ((X.chainComplex ndpsR).d n (n - 1)).hom c = 0)
    (α : Work.Cohomology.Cochain ℤ X n) (hα : Work.Cohomology.cochainDiff ℤ X α = 0) :
    α (normP X n c) = α c := by
  set H := X.homotopyEquivNormalizedChainComplex ndpsR with hH
  have hcomm := congrArg (fun (f : (X.chainComplex ndpsR).X n ⟶
      (X.chainComplex ndpsR).X n) => f.hom c) (H.homotopyHomInvId.comm n)
  rw [HomologicalComplex.comp_f] at hcomm
  simp only [ModuleCat.hom_add, LinearMap.add_apply] at hcomm
  have hD : (ModuleCat.Hom.hom ((dNext n) H.homotopyHomInvId.hom)) c = 0 := by
    rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel n (n - 1) from Nat.sub_add_cancel hn),
      ModuleCat.hom_comp]
    simp only [LinearMap.comp_apply, hc, map_zero]
  rw [hD, zero_add] at hcomm
  rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)] at hcomm
  rw [ModuleCat.hom_comp] at hcomm
  simp only [LinearMap.comp_apply] at hcomm
  rw [show (ModuleCat.Hom.hom (((𝟙 (X.chainComplex ndpsR) :
      X.chainComplex ndpsR ⟶ X.chainComplex ndpsR)).f n)) c = c from rfl] at hcomm
  have hhom : H.hom = X.toNormalizedChainComplex ndpsR := by
    rw [hH]; exact SSet.homotopyEquivNormalizedChainComplex_hom X ndpsR
  have hinv : H.inv = X.fromNormalizedChainComplex ndpsR := by
    rw [hH]; exact SSet.homotopyEquivNormalizedChainComplex_inv X ndpsR
  have hcomp : normP X n c
      = (ModuleCat.Hom.hom (H.inv.f n)) ((ModuleCat.Hom.hom (H.hom.f n)) c) := by
    simp only [normP, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      hhom, hinv]
  have hcomm' : (ModuleCat.Hom.hom (H.inv.f n)) ((ModuleCat.Hom.hom (H.hom.f n)) c)
      = ((X.chainComplex ndpsR).d (n + 1) n).hom
          ((H.homotopyHomInvId.hom n (n + 1)) c) + c := by
    rw [hcomm, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hzero : α (((X.chainComplex ndpsR).d (n + 1) n).hom
      ((H.homotopyHomInvId.hom n (n + 1)) c)) = 0 := by
    have h := congrArg (fun (g : (X.chainComplex ndpsR).X (n + 1) →ₗ[ℤ] ℤ) =>
      g ((H.homotopyHomInvId.hom n (n + 1)) c)) hα
    simpa only [Work.Cohomology.cochainDiff, LinearMap.comp_apply, LinearMap.zero_apply] using h
  rw [hcomp, hcomm', map_add, hzero, zero_add]

/-! ## From a nonzero cohomology class to a cycle/cocycle pair -/

/-- **A nonzero class of `Hⁿ` is detected by an `n`-cycle and an `n`-cocycle.** -/
theorem existsCycleEvalGen (X : TopCat) (n : ℕ)
    (hfree : ∀ k, Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ X).homology k))
    (γ : ↥((Work.Cohomology.singularCochainComplex ℤ X).homology n)) (hγ : γ ≠ 0) :
    ∃ (u : ((TopCat.toSSet.obj X).chainComplex ndpsR).X n)
      (β : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) n),
      Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) β = 0 ∧
      (((TopCat.toSSet.obj X).chainComplex ndpsR).d n (n - 1)).hom u = 0 ∧ β u ≠ 0 := by
  obtain ⟨β, hβ, hclass⟩ :=
    Work.Cohomology.exists_cohomologyClassOf ℤ (TopCat.toSSet.obj X) n γ
  have hbij := Work.Cohomology.kronH_isIso X hfree n
  have hk : Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) n γ ≠ 0 := fun h =>
    hγ (hbij.1 (h.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ : ∃ v, Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) n γ v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (LinearMap.ext h)
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((Work.Cohomology.singularChains ℤ X).homologyπ n)).mp inferInstance v
  refine ⟨((Work.Cohomology.singularChains ℤ X).iCycles n).hom w, β, hβ, ?_, ?_⟩
  · have h := congrArg (fun (g : (Work.Cohomology.singularChains ℤ X).cycles n ⟶
        (Work.Cohomology.singularChains ℤ X).X (n - 1)) => g.hom w)
      (HomologicalComplex.iCycles_d (Work.Cohomology.singularChains ℤ X) n (n - 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h
    exact h
  · have h2 := Work.Cohomology.kronH_apply (R := ℤ) (X := TopCat.toSSet.obj X)
      (α := β) hβ w
    rw [hclass] at h2
    exact fun h0 => hv (h2.trans h0)

/-- **A normalized `n`-cocycle and an `n`-cycle with nonzero evaluation**, for a space whose
singular homology is degreewise free and whose `n`-th homology is `ℤ`. -/
theorem normalizedDetectedPairGen (n : ℕ) (hn : 1 ≤ n) (X : TopCat)
    (hfree : ∀ k, Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ X).homology k))
    (e : ↥((Work.Cohomology.singularChains ℤ X).homology n) ≃ₗ[ℤ] ℤ) :
    ∃ (θ : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) n)
      (u : ((TopCat.toSSet.obj X).chainComplex ndpsR).X n),
      Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) θ = 0 ∧
      (∀ x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)),
        x ∈ (TopCat.toSSet.obj X).degenerate n →
        Work.Cohomology.genEval ℤ (TopCat.toSSet.obj X) θ x = 0) ∧
      (((TopCat.toSSet.obj X).chainComplex ndpsR).d n (n - 1)).hom u = 0 ∧
      θ u ≠ 0 := by
  have hbij := Work.Cohomology.kronH_isIso X hfree n
  obtain ⟨γ, hγeq⟩ := hbij.2 e.toLinearMap
  have hne : e.toLinearMap ≠ 0 := by
    intro h
    have h1 := congrArg (fun f => f (e.symm 1)) h
    simp only [LinearMap.zero_apply] at h1
    rw [show e.toLinearMap (e.symm 1) = e (e.symm 1) from rfl,
      LinearEquiv.apply_symm_apply] at h1
    exact one_ne_zero h1
  have hγ : γ ≠ 0 := by
    intro h0
    refine hne ?_
    rw [← hγeq, h0]
    exact map_zero _
  obtain ⟨u, α, hα, hu, hαu⟩ := existsCycleEvalGen X n hfree γ hγ
  refine ⟨α.comp (normP (TopCat.toSSet.obj X) n), u,
    cochainDiff_comp_normP (TopCat.toSSet.obj X) n α hα, ?_, hu, ?_⟩
  · intro x hx
    simp only [Work.Cohomology.genEval, LinearMap.comp_apply]
    rw [normP_degenerate (TopCat.toSSet.obj X) n x hx, map_zero]
  · rw [LinearMap.comp_apply,
      normP_apply_cycle_eq (TopCat.toSSet.obj X) n hn u hu α hα]
    exact hαu

/-! ## The sphere `Sᵖ` -/

/-- The singular homology of `Sᵖ = sphTop (p+1)` is degreewise free (`p ≥ 1`). -/
theorem freeHomologySphSph (p : ℕ) (hp : 1 ≤ p) (k : ℕ) :
    Module.Free ℤ
      ↥((Work.Cohomology.singularChains ℤ (Work.Cohomology.sphTop (p + 1))).homology k) := by
  rcases eq_or_ne k 0 with h0 | h0
  · subst h0
    haveI : PathConnectedSpace ↥(Work.Cohomology.sphSet (p + 1)) :=
      Work.Cohomology.pathConnected_sphSet (p + 1) (by omega)
    haveI : IsIso (TopCat.singularHomology₀ε (Work.Cohomology.sphTop (p + 1))
        (ModuleCat.of ℤ ℤ)) := inferInstance
    haveI : Module.Free ℤ ↥(ModuleCat.of ℤ ℤ) := inferInstance
    exact Module.Free.of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ)
      (Work.Cohomology.uctIsoToLinearEquiv
        (asIso (TopCat.singularHomology₀ε (Work.Cohomology.sphTop (p + 1))
          (ModuleCat.of ℤ ℤ)))).symm
  · rcases eq_or_ne k p with hk | hk
    · rw [hk]
      obtain ⟨e⟩ := Work.Cohomology.sphereHomology_aux p hp
      haveI : Module.Free ℤ ↥(ModuleCat.of ℤ ℤ) := inferInstance
      exact Module.Free.of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ)
        (Work.Cohomology.uctIsoToLinearEquiv e).symm
    · have hz := Work.Cohomology.sphereVanishing_aux p hp k h0 hk
      haveI : Subsingleton
          ↥((Work.Cohomology.singularChains ℤ (Work.Cohomology.sphTop (p + 1))).homology k) :=
        (ModuleCat.isZero_iff_subsingleton).mp hz
      exact Module.Free.of_subsingleton ℤ _

/-- **A normalized detected pair on the sphere `Sᵖ`** (`p ≥ 1`): there is a `p`-cocycle `θ` on
`sphTop (p+1)` which vanishes on every degenerate `p`-simplex, and a `p`-cycle `u` with
`θ u ≠ 0`. -/
theorem normalizedDetectedPairSph (p : ℕ) (hp : 1 ≤ p) :
    ∃ (θ : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (Work.Cohomology.sphTop (p+1))) p)
      (u : ((TopCat.toSSet.obj (Work.Cohomology.sphTop (p+1))).chainComplex (ModuleCat.of ℤ ℤ)).X p),
      Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (Work.Cohomology.sphTop (p+1))) θ = 0 ∧
      (∀ x : (TopCat.toSSet.obj (Work.Cohomology.sphTop (p+1))).obj (Opposite.op (SimplexCategory.mk p)),
        x ∈ (TopCat.toSSet.obj (Work.Cohomology.sphTop (p+1))).degenerate p →
        Work.Cohomology.genEval ℤ (TopCat.toSSet.obj (Work.Cohomology.sphTop (p+1))) θ x = 0) ∧
      (((TopCat.toSSet.obj (Work.Cohomology.sphTop (p+1))).chainComplex (ModuleCat.of ℤ ℤ)).d p (p-1)).hom u = 0 ∧
      θ u ≠ 0 := by
  obtain ⟨e⟩ := Work.Cohomology.sphereHomology_aux p hp
  exact normalizedDetectedPairGen p hp (Work.Cohomology.sphTop (p+1))
    (freeHomologySphSph p hp) (Work.Cohomology.uctIsoToLinearEquiv e)

end

end Work.KunnethEZ
