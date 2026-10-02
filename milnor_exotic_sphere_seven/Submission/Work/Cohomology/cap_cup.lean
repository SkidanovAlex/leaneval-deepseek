import Mathlib
import Submission.Work.Cohomology.CapProduct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cap/cup compatibility: `c ⌢ (α ⌣ β) = (c ⌢ α) ⌢ β`

This file proves the cochain-level identity relating the cap product with the Alexander–Whitney
cup product: for cochains `α` of degree `p`, `β` of degree `q` and a chain `c` of degree
`(p+q)+m`,

  `c ⌢ (α ⌣ β) = (c ⌢ α) ⌢ β`,

where the two sides live in degrees `m` and `q+m` respectively, so the statement involves the
transport of `c` along `(p+q)+m = p+(q+m)`.

The proof reduces to generators of the simplicial chains, where it is the elementary identity
`(α ⌣ β)(σ_front) = α(σ_front) · β(σ_back)` together with the associativity of the vertices of a
simplex.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {R : Type} [CommRing R] {X : SSet}

/-! ## Transporting chains along an equality of degrees -/

/-- The linear map underlying the cast of chains along an equality of degrees. -/
def capCupCast {a b : ℕ} (h : a = b) :
    (↑((X.chainComplex (ModuleCat.of R R)).X a)) →ₗ[R]
      (↑((X.chainComplex (ModuleCat.of R R)).X b)) :=
  (LinearEquiv.cast (M := fun k => ↑((X.chainComplex (ModuleCat.of R R)).X k)) h).toLinearMap

lemma capCupCast_apply {a b : ℕ} (h : a = b)
    (x : ↑((X.chainComplex (ModuleCat.of R R)).X a)) :
    capCupCast (X := X) h x = h ▸ x := by
  cases h; simp [capCupCast]

/-- Linear maps on chains which agree on all generators are equal. -/
lemma capCupChainExt {N m : ℕ}
    {f g : (↑((X.chainComplex (ModuleCat.of R R)).X N)) →ₗ[R]
      (↑((X.chainComplex (ModuleCat.of R R)).X m))}
    (h : ∀ σ : X _⦋N⦌, f ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
      = g ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)) : f = g := by
  have key : (ModuleCat.ofHom f : (X.chainComplex (ModuleCat.of R R)).X N
        ⟶ (X.chainComplex (ModuleCat.of R R)).X m)
      = (ModuleCat.ofHom g : (X.chainComplex (ModuleCat.of R R)).X N
        ⟶ (X.chainComplex (ModuleCat.of R R)).X m) := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    have hr : (X.ιChainComplex (R := ModuleCat.of R R) σ).hom r
        = r • (X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1 := by
      simpa using LinearMap.map_smul (X.ιChainComplex (R := ModuleCat.of R R) σ).hom r (1 : R)
    rw [hr, map_smul, map_smul]
    exact congrArg (fun z => r • z) (h σ)
  simpa only [ModuleCat.hom_ofHom] using congrArg ModuleCat.Hom.hom key

/-! ## The morphism comparing the two associations of `p + q + m` -/

/-- The identification `⦋p + (q + m)⦌ ⟶ ⦋(p + q) + m⦌`, given by the equality of natural numbers
`(p + q) + m = p + (q + m)`. -/
def sop (p q m : ℕ) : ⦋p + (q + m)⦌ ⟶ ⦋(p + q) + m⦌ :=
  eqToHom (congrArg SimplexCategory.mk (Nat.add_assoc p q m)).symm

lemma sop_val (p q m : ℕ) (i : Fin (⦋p + (q + m)⦌.len + 1)) :
    ((ConcreteCategory.hom (sop p q m)) i).val = i.val :=
  coe_eqToHom_mk_symm (Nat.add_assoc p q m) i

/-! ## Faces of a mapped simplex -/

lemma frontFace_map {K N M : ℕ} (h : K ≤ N) (f : ⦋N⦌ ⟶ ⦋M⦌) (τ : X _⦋M⦌) :
    frontFace X K N h (X.map f.op τ) = X.map (frontIncl K N h ≫ f).op τ :=
  map_op_comp f (frontIncl K N h) τ

lemma backFace_map {K N M : ℕ} (f : ⦋K + N⦌ ⟶ ⦋M⦌) (τ : X _⦋M⦌) :
    backFace X K N (X.map f.op τ) = X.map (backIncl K N ≫ f).op τ :=
  map_op_comp f (backIncl K N) τ

/-! ## The three `SimplexCategory` identities -/

lemma frontIncl_frontIncl (p q m : ℕ) :
    frontIncl p (p + q) (by omega) ≫ frontIncl (p + q) ((p + q) + m) (by omega)
      = frontIncl p (p + (q + m)) (by omega) ≫ sop p q m := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, hom_frontIncl_val, sop_val]

lemma backIncl_frontIncl (p q m : ℕ) :
    backIncl p q ≫ frontIncl (p + q) ((p + q) + m) (by omega)
      = (frontIncl q (q + m) (by omega) ≫ backIncl p (q + m)) ≫ sop p q m := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, hom_frontIncl_val, hom_backIncl_val, sop_val]

lemma backIncl_backIncl (p q m : ℕ) :
    (backIncl q m ≫ backIncl p (q + m)) ≫ sop p q m = backIncl (p + q) m := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, hom_backIncl_val, sop_val]
  omega

/-! ## The three simplex identities -/

/-- The front `p`-face of the front `(p+q)`-face is the front `p`-face of the transported
simplex. -/
lemma frontFace_comp (p q m : ℕ) (σ : X _⦋(p + q) + m⦌) :
    frontFace X p (p + q) (by omega) (frontFace X (p + q) ((p + q) + m) (by omega) σ)
      = frontFace X p (p + (q + m)) (by omega) (X.map (sop p q m).op σ) := by
  simp only [frontFace]
  rw [map_op_comp, map_op_comp, frontIncl_frontIncl]

/-- The back `q`-face of the front `(p+q)`-face equals the front `q`-face of the back
`(q+m)`-face of the transported simplex. -/
lemma backFace_frontFace (p q m : ℕ) (σ : X _⦋(p + q) + m⦌) :
    backFace X p q (frontFace X (p + q) ((p + q) + m) (by omega) σ)
      = frontFace X q (q + m) (by omega)
          (backFace X p (q + m) (X.map (sop p q m).op σ)) := by
  simp only [frontFace, backFace]
  rw [map_op_comp, map_op_comp, map_op_comp, backIncl_frontIncl]

/-- The back `m`-face of the back `(q+m)`-face is the back `m`-face of the transported simplex. -/
lemma backFace_backFace (p q m : ℕ) (σ : X _⦋(p + q) + m⦌) :
    backFace X (p + q) m σ
      = backFace X q m (backFace X p (q + m) (X.map (sop p q m).op σ)) := by
  simp only [backFace]
  rw [map_op_comp, map_op_comp, backIncl_backIncl]

/-! ## The main identity -/

theorem cap_cup (R : Type) [CommRing R] (X : SSet) {p q m : ℕ}
    (α : Work.Cohomology.Cochain R X p) (β : Work.Cohomology.Cochain R X q)
    (c : (X.chainComplex (ModuleCat.of R R)).X ((p + q) + m)) :
    Work.Cohomology.cap R X (Work.Cohomology.cup R X α β) m c =
      Work.Cohomology.cap R X β m
        (Work.Cohomology.cap R X α (q + m) ((Nat.add_assoc p q m) ▸ c)) := by
  have key : cap R X (cup R X α β) m
      = (cap R X β m).comp ((cap R X α (q + m)).comp
          (capCupCast (X := X) (Nat.add_assoc p q m))) := by
    apply capCupChainExt
    intro σ
    have hcast : capCupCast (X := X) (Nat.add_assoc p q m)
        ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
        = (X.ιChainComplex (R := ModuleCat.of R R)
            (X.map (sop p q m).op σ)).hom 1 := by
      rw [capCupCast_apply]
      exact generator_transport (Nat.add_assoc p q m) σ
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hcast]
    rw [cap_apply R X (cup R X α β) σ]
    rw [cap_apply R X α (X.map (sop p q m).op σ)]
    rw [map_smul]
    rw [cap_apply R X β (backFace X p (q + m) (X.map (sop p q m).op σ))]
    rw [cup_apply' α β (frontFace X (p + q) ((p + q) + m) (by omega) σ)]
    rw [frontFace_comp, backFace_frontFace, backFace_backFace]
    rw [mul_smul]
  have hkey := LinearMap.congr_fun key c
  rw [hkey]
  simp only [LinearMap.comp_apply, capCupCast_apply]

end

end Work.Cohomology
