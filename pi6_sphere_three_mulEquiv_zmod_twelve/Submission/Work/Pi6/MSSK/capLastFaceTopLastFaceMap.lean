import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaBasic
import Submission.Work.Cohomology.cap_natural
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Cap naturality for the last-face pasting map

For a simplex `σ : Δ[t+1] ⟶ Sing B` and `T_σ = Δ[t+1] ×_{Sing B} Sing E`, let `δ` be the last face
inclusion `Δ[t] ⟶ Δ[t+1]`.  The pasting map
`Work.SSSR.lastFaceMap (sSingP p) t σ : T_{δ ≫ σ} ⟶ T_σ` identifies `T_{δ≫σ}` with the part of
`T_σ` over the last face of `Δ[t+1]`.

The cochain `lastFaceTop R p σ` on `T_σ` is the indicator of the simplices lying over the top
simplex of that last face; pulled back along the pasting map it is exactly `thetaTop R p (δ ≫ σ)`
— the indicator of the simplices of `T_{δ≫σ}` lying over the top simplex of `Δ[t]`.  Hence the cap
product with `lastFaceTop` commutes with the pasting map:

`((lastFaceMap)_* y) ⌢ lastFaceTop = (lastFaceMap)_* (y ⌢ thetaTop)`.

This is the naturality of the cap product (`Work.Cohomology.cap_natural`) applied to the identity of
cochains `lastFaceTop ∘ (lastFaceMap)^* = thetaTop`, which is proved on generators via
`lastFaceVal`/`thetaVal`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `lastFaceVal`, read through `SSet.stdSimplex.objEquiv`: it is `1` exactly on the simplices of
`T_σ` whose projection is (the top simplex of) the last face of `Δ[t+1]`. -/
lemma lastFaceVal_eq_ite' (R : Type) [CommRing R] {t : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (x : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t⦌) :
    lastFaceVal R p σ x
      = (if SSet.stdSimplex.objEquiv (proj p σ x)
            = SimplexCategory.δ (Fin.last (t+1)) then (1:R) else 0) := by
  rw [show lastFaceVal R p σ x
      = (if proj p σ x
            = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (Fin.last (t+1)))
          then (1:R) else 0) from rfl]
  by_cases h : SSet.stdSimplex.objEquiv (proj p σ x) = SimplexCategory.δ (Fin.last (t+1))
  · have h' : proj p σ x
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (Fin.last (t+1))) := by
      rw [← h, Equiv.symm_apply_apply]
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : ¬ (proj p σ x
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (Fin.last (t+1)))) := by
      intro hc; exact h (by rw [hc, Equiv.apply_symm_apply])
    rw [ite_eq_right h', ite_eq_right h]

/-- `thetaVal`, read through `SSet.stdSimplex.objEquiv`: it is `1` exactly on the simplices of
`T_σ` whose projection is the top simplex of `Δ[s]`. -/
lemma thetaVal_eq_ite' (R : Type) [CommRing R] {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (x : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s⦌) :
    thetaVal R p σ x
      = (if SSet.stdSimplex.objEquiv (proj p σ x)
            = 𝟙 (SimplexCategory.mk s) then (1:R) else 0) := by
  rw [show thetaVal R p σ x = (if proj p σ x = topS s then (1:R) else 0) from rfl]
  by_cases h : SSet.stdSimplex.objEquiv (proj p σ x) = 𝟙 (SimplexCategory.mk s)
  · have h' : proj p σ x = topS s := by
      rw [topS, ← h, Equiv.symm_apply_apply]
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : ¬ (proj p σ x = topS s) := by
      intro hc; exact h (by rw [hc, topS, Equiv.apply_symm_apply])
    rw [ite_eq_right h', ite_eq_right h]

/-- The coface `Δ[t] ⟶ Δ[t+1]` (the last one) acts on a `t`-simplex of `Δ[t]` by composition with
the corresponding monotone map, read through `SSet.stdSimplex.objEquiv`. -/
lemma objEquiv_coface_app {t : ℕ}
    (u : (SSet.stdSimplex.obj (SimplexCategory.mk t) : SSet.{0}) _⦋t⦌) :
    SSet.stdSimplex.objEquiv ((SSet.stdSimplex.δ (n := t) (Fin.last (t+1))).app (op ⦋t⦌) u)
      = SSet.stdSimplex.objEquiv u ≫ SimplexCategory.δ (Fin.last (t+1)) := by
  have h := SSet.stdSimplex.objEquiv_symm_comp (n := SimplexCategory.mk t)
      (n' := SimplexCategory.mk (t+1)) (m := op ⦋t⦌)
      (SSet.stdSimplex.objEquiv u) (SimplexCategory.δ (Fin.last (t+1)))
  rw [Equiv.symm_apply_apply] at h
  simp only [CosimplicialObject.δ] at h ⊢
  rw [← h, Equiv.apply_symm_apply]

/-- The last face inclusion of `Δ[t+1]` is a split monomorphism: composing an endomorphism `a` of
`⦋t⦌` with it gives back the inclusion exactly when `a` is the identity. -/
lemma objEquiv_coface_app_last (t : ℕ) (a : (⦋t⦌ : SimplexCategory) ⟶ ⦋t⦌) :
    a ≫ SimplexCategory.δ (n := t) (Fin.last (t+1)) = SimplexCategory.δ (n := t) (Fin.last (t+1))
      ↔ a = 𝟙 ⦋t⦌ := by
  constructor
  · intro h
    have hret : SimplexCategory.δ (n := t) (Fin.last (t+1)) ≫ SimplexCategory.σ (n := t) (Fin.last t)
        = 𝟙 ⦋t⦌ := by
      simpa using SimplexCategory.δ_comp_σ_succ (n := t) (i := Fin.last t)
    have h2 := congrArg (fun (g : ⦋t⦌ ⟶ ⦋t+1⦌) => g ≫ SimplexCategory.σ (n := t) (Fin.last t)) h
    simp only [Category.assoc] at h2
    rw [hret, Category.comp_id] at h2
    exact h2
  · intro h; subst h; rw [Category.id_comp]

/-- The projection of the image of a simplex under the last-face pasting map is the image of the
projection under the last face inclusion. -/
lemma proj_app_lastFaceMap {t : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)) _⦋t⦌) :
    proj p σ ((Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ).app (op ⦋t⦌) w)
      = (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))).app (op ⦋t⦌)
          (proj p (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) w) := by
  simp only [proj]
  rw [← NatTrans.comp_app_apply (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ)
        (pullback.fst σ (Work.SSSR.sSingP p)) (op ⦋t⦌) w,
      Work.SSSR.lastFaceMap_fst, NatTrans.comp_app_apply]

/-- **The key value computation**: a `t`-simplex of `T_σ` is carried by the pasting map into the
part over the top simplex of the last face of `Δ[t+1]` exactly when the simplex itself lies over the
top simplex of `Δ[t]`. -/
lemma lastFaceVal_lastFaceMap (R : Type) [CommRing R] [Nontrivial R] (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)) _⦋t⦌) :
    lastFaceVal R p σ ((Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ).app (op ⦋t⦌) w)
      = thetaVal R p (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) w := by
  rw [lastFaceVal_eq_ite', thetaVal_eq_ite']
  rw [proj_app_lastFaceMap p σ w, objEquiv_coface_app]
  by_cases h : SSet.stdSimplex.objEquiv
      (proj p (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) w) = 𝟙 ⦋t⦌
  · rw [ite_eq_left ((objEquiv_coface_app_last t _).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h ((objEquiv_coface_app_last t _).mp hc)), ite_eq_right h]

/-- The chain map induced by the pasting map on generators. -/
lemma chainComplexMap_ι_lastFaceMap (R : Type) [CommRing R] [Nontrivial R] (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)) _⦋t⦌) :
    (ModuleCat.Hom.hom ((SSet.chainComplexMap (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ)
        (ModuleCat.of R R)).f t))
      ((ModuleCat.Hom.hom
          ((Work.SSSR.pullAlong (Work.SSSR.sSingP p)
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)).ιChainComplex
            (R := ModuleCat.of R R) w))
        1)
      = (ModuleCat.Hom.hom
          ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).ιChainComplex (R := ModuleCat.of R R)
            ((Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ).app (op ⦋t⦌) w)))
        1 := by
  simpa only [Work.SSSR.pullAlong] using
    (Work.Cohomology.chainComplexMap_ιChainComplex_apply (R := R)
      (f := Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ) (k := t) (τ := w))

/-- The evaluation of the pullback of a cochain along the pasting map, on a generator. -/
lemma genEval_comp_lastFaceMap (R : Type) [CommRing R] [Nontrivial R] (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)) _⦋t⦌) :
    Work.Cohomology.genEval R
        (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
        ((lastFaceTop R p σ).comp
          ((SSet.chainComplexMap (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ)
            (ModuleCat.of R R)).f t).hom) w
      = Work.Cohomology.genEval R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (lastFaceTop R p σ)
          ((Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ).app (op ⦋t⦌) w) := by
  have key := chainComplexMap_ι_lastFaceMap R p σ w
  simp only [Work.Cohomology.genEval, LinearMap.comp_apply]
  exact congrArg (lastFaceTop R p σ) key

/-- **The pulled back `lastFaceTop` is `thetaTop`**: the indicator cochain of the simplices of
`T_σ` over the last face of `Δ[t+1]` pulls back along the pasting map to the indicator cochain of
the simplices of `T_{δ≫σ}` over the top simplex of `Δ[t]`. -/
lemma lastFaceTop_comp_lastFaceMap (R : Type) [CommRing R] [Nontrivial R] (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    (lastFaceTop R p σ).comp
        ((SSet.chainComplexMap (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ)
          (ModuleCat.of R R)).f t).hom
      = thetaTop R p (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) := by
  apply Work.Cohomology.genEval_ext
  intro w
  exact (genEval_comp_lastFaceMap R p σ w).trans
    ((genEval_lastFaceTop (R := R) p σ
        ((Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ).app (op ⦋t⦌) w)).trans
      ((lastFaceVal_lastFaceMap R p σ w).trans
        (genEval_thetaTop (R := R) p
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) w).symm))

end

theorem capLastFaceTopLastFaceMap (R : Type) [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {t K : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (y : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).X (t + K)) :
    Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.lastFaceTop R p σ) K
        ((Work.SSSR.sCCMap R (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ)).f (t + K) y)
      = (Work.SSSR.sCCMap R (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ)).f K
          (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
              (CategoryTheory.CategoryStruct.comp
                (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
            (Work.Pi6.MSSK.thetaTop R p (CategoryTheory.CategoryStruct.comp
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)) K y) := by
  have hcoch := lastFaceTop_comp_lastFaceMap R p σ
  have hnat := Work.Cohomology.cap_natural R (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ)
      (Work.Pi6.MSSK.lastFaceTop R p σ) y
  refine (hnat.symm).trans ?_
  exact congrArg (fun β => (Work.SSSR.sCCMap R
      (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ)).f K
    (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
      (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
      β K y)) hcoch

end

end Work.Pi6.MSSK
