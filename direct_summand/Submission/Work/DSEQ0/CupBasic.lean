import Mathlib
import Submission.Work.DSMap.Map

/-!
# The Alexander–Whitney cup product on the Čech complex (API)

`DSMap.cech A X f U` is Mathlib's Čech cochain complex of the presheaf of `A`-modules
`DSMap.cechPresheaf A X f` along the family of opens `U`.  In degree `n` it is the product,
indexed by `z : Fin (n+1) → ι`, of the sections `Γ(X, sec z)` where `sec z = ∏ᶜ (U ∘ z)`.

This file sets up the componentwise API used to construct the Alexander–Whitney cup product
and to verify the Leibniz rule, unitality and associativity.

The main definitions are

* `cosimp`, the cosimplicial object whose alternating coface complex is `DSMap.cech A X f U`;
* `sec n z`, the open `∏ᶜ (U ∘ z)`;
* `frame n z`, the presheaf value at `sec n z` (a term of the Čech complex in degree `n`);
* `proj n z`, the projection of the `n`-th term onto the `z`-th factor;
* `incl z φ` / `res z φ`, the canonical inclusions of products of opens / restrictions of
  sections, for `φ : Fin (n+1) → Fin (m+1)` (an inclusion of index sets);
* `deltaMap n i`, the coface `Fin (n+1) → Fin (n+2)` deleting `i`;
* `frontIdx p q`, `backIdx p q`, the front/back inclusions used by the cup product;
* `cup p q`, the cup product itself.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped Simplicial

namespace Work.DSEQ0.Cup

universe a

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable (A : Type a) [CommRing A]

/-- The open attached to an index `z : Fin (n+1) → ι`: the intersection of the `U (z j)`. -/
abbrev sec (X : AlgebraicGeometry.Scheme.{a}) {ι : Type a} (U : ι → X.Opens) (n : ℕ)
    (z : Fin (n+1) → ι) : X.Opens :=
  ∏ᶜ (fun j : Fin (n+1) => U (z j))

/-- The `z`-th factor of the `n`-th term of the Čech complex. -/
abbrev frame (X : AlgebraicGeometry.Scheme.{a}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    {ι : Type a} (U : ι → X.Opens) (n : ℕ) : (Fin (n+1) → ι) → ModuleCat.{a} A :=
  fun z => (DSMap.cechPresheaf A X f).obj (Opposite.op (sec X U n z))

/-- The Čech cosimplicial object of the family `U` (whose alternating coface complex
is `DSMap.cech A X f U`). -/
def cosimp (X : AlgebraicGeometry.Scheme.{a}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    {ι : Type a} (U : ι → X.Opens) : CosimplicialObject (ModuleCat.{a} A) :=
  (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj
    (DSMap.cechPresheaf A X f)

/-- The projection of the `n`-th term of the Čech complex onto its `z`-th factor. -/
def proj (X : AlgebraicGeometry.Scheme.{a}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    {ι : Type a} (U : ι → X.Opens) (n : ℕ) (z : Fin (n+1) → ι) :
    (DSMap.cech A X f U).X n ⟶ frame A X f U n z :=
  Pi.π (frame A X f U n) z

/-- The canonical morphism of opens `∏ᶜ (U ∘ z) ⟶ ∏ᶜ (U ∘ z ∘ φ)` for
`φ : Fin (n+1) → Fin (m+1)`. -/
def incl (X : AlgebraicGeometry.Scheme.{a}) {ι : Type a} (U : ι → X.Opens) {m n : ℕ}
    (z : Fin (m+1) → ι) (φ : Fin (n+1) → Fin (m+1)) :
    sec X U m z ⟶ sec X U n (fun i => z (φ i)) :=
  Pi.lift (fun i => Pi.π (fun j : Fin (m+1) => U (z j)) (φ i))

/-- The restriction `Γ(X, sec (z ∘ φ)) ⟶ Γ(X, sec z)`. -/
def res (X : AlgebraicGeometry.Scheme.{a}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    {ι : Type a} (U : ι → X.Opens) {m n : ℕ} (z : Fin (m+1) → ι) (φ : Fin (n+1) → Fin (m+1)) :
    frame A X f U n (fun i => z (φ i)) ⟶ frame A X f U m z :=
  (DSMap.cechPresheaf A X f).map (incl X U z φ).op

/-- The reindexing isomorphism `Fin (((p+1)+q)+1) → Fin ((p+q)+1+1)` induced by
`(p+1)+q = (p+q)+1`, as it appears in `proj_XIsoOfEq`. -/
abbrev castIdx (p q : ℕ) : Fin (((p+1)+q)+1) → Fin (((p+q)+1)+1) :=
  Fin.cast (congrArg (fun t => t+1) (by omega : (p+1)+q = (p+q)+1))

/-- The coface `Fin (n+1) → Fin (n+2)` deleting `i`. -/
def deltaMap (n : ℕ) (i : Fin (n+2)) : Fin (n+1) → Fin (n+2) :=
  (SimplexCategory.δ i).toOrderHom.toFun

/-- The front inclusion `Fin (p+1) → Fin (p+q+1)`. -/
def frontIdx (p q : ℕ) : Fin (p+1) → Fin (p+q+1) := fun i => ⟨i.val, by omega⟩

/-- The back inclusion `Fin (q+1) → Fin (p+q+1)`, `j ↦ p + j`. -/
def backIdx (p q : ℕ) : Fin (q+1) → Fin (p+q+1) := fun j => ⟨p + j.val, by omega⟩

/-- The ring structure on the value of the Čech presheaf at an open `V` (the ring of sections
of the structure sheaf). -/
instance instPresheafCommRing (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) (V : X.Opens) :
    CommRing ↥((DSMap.cechPresheaf A X f).obj (Opposite.op V)) :=
  inferInstanceAs (CommRing ↥(X.presheaf.obj (Opposite.op V)))

/-- The `A`-algebra structure on the `z`-th factor of the Čech complex (via `phiU`). -/
instance instFrameAlgebra (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} (U : ι → X.Opens)
    (n : ℕ) (z : Fin (n+1) → ι) : Algebra A ↥(frame A X f U n z) :=
  (DSMap.phiU A X f (sec X U n z)).toAlgebra

end

noncomputable section

variable (A : Type a) [CommRing A]
variable (X : AlgebraicGeometry.Scheme.{a}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
  {ι : Type a} (U : ι → X.Opens)

lemma incl_comp {m n r : ℕ} (z : Fin (m+1) → ι) (φ : Fin (n+1) → Fin (m+1))
    (ψ : Fin (r+1) → Fin (n+1)) :
    incl X U z φ ≫ incl X U (fun i => z (φ i)) ψ = incl X U z (fun k => φ (ψ k)) := by
  simp only [incl]
  apply Pi.hom_ext
  intro j
  rw [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π, Pi.lift_comp_π]

lemma res_comp {m n r : ℕ} (z : Fin (m+1) → ι) (φ : Fin (n+1) → Fin (m+1))
    (ψ : Fin (r+1) → Fin (n+1)) :
    res A X f U (fun i => z (φ i)) ψ ≫ res A X f U z φ = res A X f U z (fun k => φ (ψ k)) := by
  simp only [res]
  rw [← Functor.map_comp]
  congr 1

lemma res_mul {m n : ℕ} (z : Fin (m+1) → ι) (φ : Fin (n+1) → Fin (m+1))
    (u v : ↥(frame A X f U n (fun i => z (φ i)))) :
    (res A X f U z φ).hom (u * v) = (res A X f U z φ).hom u * (res A X f U z φ).hom v := by
  show (X.presheaf.map (incl X U z φ).op).hom (u * v) = _
  rw [map_mul]
  rfl

lemma res_one {m n : ℕ} (z : Fin (m+1) → ι) (φ : Fin (n+1) → Fin (m+1)) :
    (res A X f U z φ).hom 1 = 1 := by
  show (X.presheaf.map (incl X U z φ).op).hom 1 = _
  rw [map_one]

lemma proj_apply_piIsoPi (n : ℕ) (z : Fin (n+1) → ι) (x : ↥((DSMap.cech A X f U).X n)) :
    ((ModuleCat.piIsoPi (frame A X f U n)).hom.hom x) z = (proj A X f U n z).hom x := by
  have h := congrArg (fun φ => φ.hom x)
    (ModuleCat.piIsoPi_hom_ker_subtype (frame A X f U n) z)
  exact h

lemma proj_ext {n : ℕ} {x y : ↥((DSMap.cech A X f U).X n)}
    (h : ∀ z : Fin (n+1) → ι, (proj A X f U n z).hom x = (proj A X f U n z).hom y) : x = y := by
  have key : (ModuleCat.piIsoPi (frame A X f U n)).hom.hom x
      = (ModuleCat.piIsoPi (frame A X f U n)).hom.hom y := by
    ext z
    rw [proj_apply_piIsoPi A X f U n z x, proj_apply_piIsoPi A X f U n z y]
    exact h z
  have hx : (ModuleCat.piIsoPi (frame A X f U n)).inv.hom
      ((ModuleCat.piIsoPi (frame A X f U n)).hom.hom x) = x := by
    have h2 := congrArg (fun φ => φ.hom x) (Iso.hom_inv_id (ModuleCat.piIsoPi (frame A X f U n)))
    exact h2
  have hy : (ModuleCat.piIsoPi (frame A X f U n)).inv.hom
      ((ModuleCat.piIsoPi (frame A X f U n)).hom.hom y) = y := by
    have h2 := congrArg (fun φ => φ.hom y) (Iso.hom_inv_id (ModuleCat.piIsoPi (frame A X f U n)))
    exact h2
  rw [← hx, ← hy, key]

lemma evalOp_map_π {C : Type*} [Category C] {B : Type*} [Category B] [HasProducts B]
    (P : Cᵒᵖ ⥤ B) {X Y : (FormalCoproduct C)ᵒᵖ} (g : X ⟶ Y) (j : Y.unop.I) :
    ((FormalCoproduct.evalOp C B).obj P).map g ≫
        Pi.π (fun j => P.obj (Opposite.op (Y.unop.obj j))) j
      = Pi.π (fun i => P.obj (Opposite.op (X.unop.obj i))) (g.unop.f j) ≫
          P.map (g.unop.φ j).op := by
  simp only [FormalCoproduct.evalOp, Pi.lift_comp_π]

lemma cosimp_map {m n : ℕ} (g : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (cosimp A X f U).map g
      = ((FormalCoproduct.evalOp X.Opens (ModuleCat.{a} A)).obj (DSMap.cechPresheaf A X f)).map
          (((FormalCoproduct.mk ι U).cech.rightOp).map g) := by
  simp only [cosimp, FormalCoproduct.cosimplicialObjectFunctor,
    CategoryTheory.Functor.whiskeringLeft_obj_obj, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.comp_map]

lemma proj_delta (n : ℕ) (i : Fin (n+2)) (z : Fin (n+2) → ι) :
    (cosimp A X f U).δ i ≫ proj A X f U (n+1) z
      = proj A X f U n (fun k => z (deltaMap n i k)) ≫ res A X f U z (deltaMap n i) := by
  rw [CosimplicialObject.δ, cosimp_map A X f U (SimplexCategory.δ i)]
  have h := evalOp_map_π (C := X.Opens) (B := ModuleCat.{a} A) (DSMap.cechPresheaf A X f)
    (g := (((FormalCoproduct.mk ι U).cech.rightOp).map (SimplexCategory.δ i))) z
  simp only [CategoryTheory.Functor.rightOp_obj, CategoryTheory.Functor.rightOp_map,
    FormalCoproduct.cech_obj, FormalCoproduct.cech_map, Quiver.Hom.unop_op, Opposite.unop_op,
    FormalCoproduct.mapPower_φ] at h
  simp only [proj, frame, res, incl, deltaMap]
  exact h

lemma cech_d (n : ℕ) :
    (DSMap.cech A X f U).d n (n+1) = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i:ℕ) • (cosimp A X f U).δ i := by
  have h := CochainComplex.of_d (X := fun m => (cosimp A X f U).obj (SimplexCategory.mk m))
    (d := fun m => AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp A X f U) m) n
  rw [show (DSMap.cech A X f U).d n (n+1) =
    AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp A X f U) n from h]
  rfl

lemma d_comp_proj (n : ℕ) (z : Fin (n+2) → ι) :
    (DSMap.cech A X f U).d n (n+1) ≫ proj A X f U (n+1) z
      = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i:ℕ) •
          (proj A X f U n (fun k => z (deltaMap n i k)) ≫ res A X f U z (deltaMap n i)) := by
  rw [cech_d A X f U n, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.zsmul_comp, proj_delta A X f U n i z]

/-- **Component formula for the Čech differential.** -/
lemma proj_d (n : ℕ) (z : Fin (n+2) → ι) (x : ↥((DSMap.cech A X f U).X n)) :
    (proj A X f U (n+1) z).hom (((DSMap.cech A X f U).d n (n+1)).hom x)
      = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i:ℕ) •
          (res A X f U z (deltaMap n i)).hom
            ((proj A X f U n (fun k => z (deltaMap n i k))).hom x) := by
  have h := congrArg (fun φ => φ.hom x) (d_comp_proj A X f U n z)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.comp_apply] at h
  rw [LinearMap.sum_apply] at h
  simp only [LinearMap.smul_apply, LinearMap.comp_apply] at h
  exact h

lemma smul_eq (V : X.Opens) (c : A) (u : ↥((DSMap.cechPresheaf A X f).obj (Opposite.op V))) :
    c • u = (show ↥((DSMap.cechPresheaf A X f).obj (Opposite.op V)) from DSMap.phiU A X f V c) * u :=
  rfl

lemma smul_mul (V : X.Opens) (c : A)
    (u v : ↥((DSMap.cechPresheaf A X f).obj (Opposite.op V))) :
    (c • u) * v = c • (u * v) := by
  rw [smul_eq A X f V c u, smul_eq A X f V c (u * v), mul_assoc]

lemma mul_smul (V : X.Opens) (c : A)
    (u v : ↥((DSMap.cechPresheaf A X f).obj (Opposite.op V))) :
    u * (c • v) = c • (u * v) := by
  rw [smul_eq A X f V c v, smul_eq A X f V c (u * v), ← mul_assoc,
    mul_comm u (show ↥((DSMap.cechPresheaf A X f).obj (Opposite.op V)) from DSMap.phiU A X f V c),
    mul_assoc]

/-- the component of the cup product at index `z` -/
def cupComp (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q))
    (z : Fin (p+q+1) → ι) : ↥(frame A X f U (p+q) z) :=
  (res A X f U z (frontIdx p q)).hom ((proj A X f U p (fun i => z (frontIdx p q i))).hom a) *
  (res A X f U z (backIdx p q)).hom ((proj A X f U q (fun j => z (backIdx p q j))).hom b)

/-- the cup product, on elements -/
def cupFun (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q)) :
    ↥((DSMap.cech A X f U).X (p+q)) :=
  (ModuleCat.piIsoPi (frame A X f U (p+q))).inv.hom (cupComp A X f U p q a b)

lemma proj_cup (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q))
    (z : Fin (p+q+1) → ι) :
    (proj A X f U (p+q) z).hom (cupFun A X f U p q a b) = cupComp A X f U p q a b z := by
  have h := congrArg (fun φ => φ.hom (cupComp A X f U p q a b))
    (ModuleCat.piIsoPi_inv_kernel_ι (frame A X f U (p+q)) z)
  exact h

lemma cupComp_add_left (p q : ℕ) (a₁ a₂ : ↥((DSMap.cech A X f U).X p))
    (b : ↥((DSMap.cech A X f U).X q)) :
    cupComp A X f U p q (a₁ + a₂) b = cupComp A X f U p q a₁ b + cupComp A X f U p q a₂ b := by
  ext z
  simp only [cupComp, Pi.add_apply, map_add, add_mul]

lemma cupComp_smul_left (p q : ℕ) (c : A) (a : ↥((DSMap.cech A X f U).X p))
    (b : ↥((DSMap.cech A X f U).X q)) :
    cupComp A X f U p q (c • a) b = c • cupComp A X f U p q a b := by
  ext z
  simp only [cupComp, Pi.smul_apply, map_smul, smul_mul]

lemma cupComp_add_right (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p))
    (b₁ b₂ : ↥((DSMap.cech A X f U).X q)) :
    cupComp A X f U p q a (b₁ + b₂) = cupComp A X f U p q a b₁ + cupComp A X f U p q a b₂ := by
  ext z
  simp only [cupComp, Pi.add_apply, map_add, mul_add]

lemma cupComp_smul_right (p q : ℕ) (c : A) (a : ↥((DSMap.cech A X f U).X p))
    (b : ↥((DSMap.cech A X f U).X q)) :
    cupComp A X f U p q a (c • b) = c • cupComp A X f U p q a b := by
  ext z
  simp only [cupComp, Pi.smul_apply, map_smul, mul_smul]

lemma cup_add_left (p q : ℕ) (a₁ a₂ : ↥((DSMap.cech A X f U).X p))
    (b : ↥((DSMap.cech A X f U).X q)) :
    cupFun A X f U p q (a₁ + a₂) b = cupFun A X f U p q a₁ b + cupFun A X f U p q a₂ b := by
  simp only [cupFun, cupComp_add_left, map_add]

lemma cup_smul_left (p q : ℕ) (c : A) (a : ↥((DSMap.cech A X f U).X p))
    (b : ↥((DSMap.cech A X f U).X q)) :
    cupFun A X f U p q (c • a) b = c • cupFun A X f U p q a b := by
  simp only [cupFun, cupComp_smul_left, map_smul]

lemma cup_add_right (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p))
    (b₁ b₂ : ↥((DSMap.cech A X f U).X q)) :
    cupFun A X f U p q a (b₁ + b₂) = cupFun A X f U p q a b₁ + cupFun A X f U p q a b₂ := by
  simp only [cupFun, cupComp_add_right, map_add]

lemma cup_smul_right (p q : ℕ) (c : A) (a : ↥((DSMap.cech A X f U).X p))
    (b : ↥((DSMap.cech A X f U).X q)) :
    cupFun A X f U p q a (c • b) = c • cupFun A X f U p q a b := by
  simp only [cupFun, cupComp_smul_right, map_smul]

/-- The Alexander–Whitney cup product on the Čech complex. -/
def cup (p q : ℕ) : ↥((DSMap.cech A X f U).X p) →ₗ[A]
    ↥((DSMap.cech A X f U).X q) →ₗ[A] ↥((DSMap.cech A X f U).X (p+q)) :=
  LinearMap.mk₂ A (cupFun A X f U p q)
    (cup_add_left A X f U p q) (cup_smul_left A X f U p q)
    (cup_add_right A X f U p q) (cup_smul_right A X f U p q)

lemma cup_apply (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q)) :
    (cup A X f U p q) a b = cupFun A X f U p q a b := rfl

lemma proj_cup_apply (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q))
    (z : Fin (p+q+1) → ι) :
    (proj A X f U (p+q) z).hom ((cup A X f U p q) a b) = cupComp A X f U p q a b z := by
  rw [cup_apply A X f U p q a b, proj_cup A X f U p q a b z]

lemma proj_XIsoOfEq {m n : ℕ} (h : m = n) (z : Fin (n+1) → ι)
    (x : ↥((DSMap.cech A X f U).X m)) :
    (proj A X f U n z).hom ((HomologicalComplex.XIsoOfEq (DSMap.cech A X f U) h).hom x)
      = (res A X f U z (Fin.cast (congrArg (fun t => t+1) h))).hom
          ((proj A X f U m (fun i => z (Fin.cast (congrArg (fun t => t+1) h) i))).hom x) := by
  cases h
  have h1 : incl X U z (Fin.cast (congrArg (fun t => t+1) (rfl : m = m))) = 𝟙 (sec X U m z) :=
    Subsingleton.elim _ _
  have hres : res A X f U z (Fin.cast (congrArg (fun t => t+1) (rfl : m = m))) =
      𝟙 (frame A X f U m z) := by
    rw [res, h1, op_id]
    simp
  rw [hres]
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, ModuleCat.id_apply]
  rfl
end

end Work.DSEQ0.Cup
