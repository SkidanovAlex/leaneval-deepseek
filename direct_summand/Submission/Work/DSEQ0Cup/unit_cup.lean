import Mathlib
import Submission.Work.DSEQ0.CupBasic

/-!
# Unitality of the Alexander–Whitney cup product on the Čech complex

The cup product with the unit of the coaugmentation (the class of `1`) is the identity, after
identifying the degrees `0 + q` and `q` by `XIsoOfEq`.  This is the `q`-indexed family of
identities in the list of properties of the Alexander–Whitney cup product on
`DSMap.cech A X f U` (see `Work.DSEQ0.exists_cech_cup`).

The proof is a componentwise computation.  For an index `z : Fin (q+1) → ι` one uses

* `Cup.proj_XIsoOfEq`, to compute the `z`-component of `XIsoOfEq`-transported elements;
* `Cup.proj_cup_apply` and `Cup.cupComp`, the component formula for the cup product;
* `Cup.res_mul` and `Cup.res_comp`, multiplicativity/composition of the restriction maps;
* `proj_coaug0`: the component of the coaugmentation unit is `1`, and `res_id`: the restriction
  along the identity reindexing is the identity.

The two remaining points are elementary but needed for the degree bookkeeping: the reindexing
`unitIdx q` (induced by `0 + q = q`) sends `backIdx 0 q j` to `j`, and restriction along an
index map which is pointwise the identity is the transport morphism (`res_pointwise`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.DSEQ0Cup

universe a

open CategoryTheory AlgebraicGeometry Limits

namespace UnitCup

/-- The reindexing `Fin (0 + q + 1) → Fin (q + 1)` induced by `0 + q = q`. -/
abbrev unitIdx (q : ℕ) : Fin (0 + q + 1) → Fin (q + 1) :=
  Fin.cast (congrArg (fun t => t + 1) (Nat.zero_add q))

/-- `unitIdx q` sends `backIdx 0 q j` to `j`. -/
lemma unitIdx_backIdx (q : ℕ) (j : Fin (q + 1)) :
    unitIdx q (Work.DSEQ0.Cup.backIdx 0 q j) = j := by
  apply Fin.ext
  rw [Fin.val_cast]
  simp [Work.DSEQ0.Cup.backIdx]

/-- `eqToHom` only depends on the two objects. -/
lemma eqToHom_irrel {C : Type*} [Category C] {V W : C} (h h' : V = W) :
    eqToHom h = eqToHom h' := by
  rw [Subsingleton.elim h h']

variable (A : Type a) [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} (U : ι → X.Opens)

/-- The component computation for `res` along an index map which is pointwise the identity:
the restriction of the `(z ∘ Θ)`-component of an element is its `z`-component. -/
lemma res_pointwise (m : ℕ) (z : Fin (m + 1) → ι) (Θ : Fin (m + 1) → Fin (m + 1))
    (hΘ : ∀ i, Θ i = i) (b : ↥((DSMap.cech A X f U).X m)) :
    (Work.DSEQ0.Cup.res A X f U z Θ).hom
      ((Work.DSEQ0.Cup.proj A X f U m (fun i => z (Θ i))).hom b) =
      (Work.DSEQ0.Cup.proj A X f U m z).hom b := by
  have hw : (fun i => z (Θ i)) = z := funext fun i => congrArg z (hΘ i)
  have eOp : Work.DSEQ0.Cup.sec X U m (fun i => z (Θ i)) = Work.DSEQ0.Cup.sec X U m z :=
    congrArg (Work.DSEQ0.Cup.sec X U m) hw
  have E : Work.DSEQ0.Cup.frame A X f U m (fun i => z (Θ i)) =
      Work.DSEQ0.Cup.frame A X f U m z :=
    congrArg (Work.DSEQ0.Cup.frame A X f U m) hw
  -- `X.Opens` is a partial order, hence a thin category: `incl` is the transport morphism.
  have hincl : Work.DSEQ0.Cup.incl X U z Θ = eqToHom eOp.symm := Subsingleton.elim _ _
  have hres : Work.DSEQ0.Cup.res A X f U z Θ = eqToHom E := by
    rw [Work.DSEQ0.Cup.res, hincl, eqToHom_op, eqToHom_map]
  have hproj : Work.DSEQ0.Cup.proj A X f U m (fun i => z (Θ i)) ≫ eqToHom E =
      Work.DSEQ0.Cup.proj A X f U m z := by
    have h := Pi.π_comp_eqToHom (f := Work.DSEQ0.Cup.frame A X f U m) hw
    rw [eqToHom_irrel _ E] at h
    exact h
  calc (Work.DSEQ0.Cup.res A X f U z Θ).hom
        ((Work.DSEQ0.Cup.proj A X f U m (fun i => z (Θ i))).hom b)
      = ((Work.DSEQ0.Cup.proj A X f U m (fun i => z (Θ i))) ≫
          (Work.DSEQ0.Cup.res A X f U z Θ)).hom b := by
        rw [ModuleCat.hom_comp]
        rfl
    _ = ((Work.DSEQ0.Cup.proj A X f U m (fun i => z (Θ i))) ≫ eqToHom E).hom b := by
        rw [hres]
    _ = (Work.DSEQ0.Cup.proj A X f U m z).hom b := by
        rw [hproj]

/-- The value of the Čech presheaf of `𝒪_X` at `⊤` is a ring and its maps are ring maps. -/
lemma cechPresheaf_map_one {V W : X.Opens} (g : W ⟶ V) :
    ((DSMap.cechPresheaf A X f).map g.op).hom
      (1 : ↥((DSMap.cechPresheaf A X f).obj (Opposite.op V))) = 1 := by
  change (X.presheaf.map g.op).hom 1 = 1
  rw [map_one]

/-- The unit of `A` maps to the unit of `Γ(X, ⊤)` under the structure map `A → Γ(X, ⊤)`. -/
lemma unitTop_one : (DSMap.unitTop A X f).hom (1 : A) = 1 := by
  rw [show ∀ x : A, (DSMap.unitTop A X f).hom x = DSMap.phiU A X f ⊤ x from fun x => rfl]
  exact map_one _

/-- The component of the Čech coaugmentation unit `coaug0 1` is `1`. -/
lemma proj_coaug0 (w : Fin 1 → ι) :
    (Work.DSEQ0.Cup.proj A X f U 0 w).hom ((DSMap.coaug0 A X f U).hom 1) = 1 := by
  simp only [Work.DSEQ0.Cup.proj, DSMap.coaug0]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  erw [Limits.Pi.lift_comp_π]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, unitTop_one]
  exact cechPresheaf_map_one A X f (homOfLE le_top)

/-- The restriction along the identity reindexing is the identity. -/
lemma res_id (m : ℕ) (z : Fin (m + 1) → ι) (y : ↥(Work.DSEQ0.Cup.frame A X f U m z)) :
    (Work.DSEQ0.Cup.res A X f U z (fun i => i)).hom y = y := by
  simp only [Work.DSEQ0.Cup.res, Work.DSEQ0.Cup.incl, Limits.Pi.lift_π, op_id]
  rw [CategoryTheory.Functor.map_id, ModuleCat.id_apply]

end UnitCup

open UnitCup

theorem unit_cup (A : Type a) [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} (U : ι → X.Opens) (q : ℕ)
    (b : ↥((DSMap.cech A X f U).X q)) :
    ((DSMap.cech A X f U).XIsoOfEq (Nat.zero_add q)).hom
        (((Work.DSEQ0.Cup.cup A X f U 0 q) ((DSMap.coaug0 A X f U).hom 1)) b) = b := by
  apply Work.DSEQ0.Cup.proj_ext A X f U
  intro z
  rw [Work.DSEQ0.Cup.proj_XIsoOfEq A X f U (Nat.zero_add q) z]
  rw [Work.DSEQ0.Cup.proj_cup_apply A X f U 0 q ((DSMap.coaug0 A X f U).hom 1) b
        (fun i => z (unitIdx q i))]
  rw [Work.DSEQ0.Cup.cupComp]
  have h1 : (Work.DSEQ0.Cup.res A X f U z (unitIdx q)).hom
      ((Work.DSEQ0.Cup.res A X f U (fun i => z (unitIdx q i))
          (Work.DSEQ0.Cup.frontIdx 0 q)).hom
        ((Work.DSEQ0.Cup.proj A X f U 0
            (fun i => z (unitIdx q (Work.DSEQ0.Cup.frontIdx 0 q i)))).hom
          ((DSMap.coaug0 A X f U).hom 1))) = 1 := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Work.DSEQ0.Cup.res_comp]
    rw [proj_coaug0 A X f U, Work.DSEQ0.Cup.res_one]
  have h2 : (Work.DSEQ0.Cup.res A X f U z (unitIdx q)).hom
      ((Work.DSEQ0.Cup.res A X f U (fun i => z (unitIdx q i))
          (Work.DSEQ0.Cup.backIdx 0 q)).hom
        ((Work.DSEQ0.Cup.proj A X f U q
            (fun j => z (unitIdx q (Work.DSEQ0.Cup.backIdx 0 q j)))).hom b)) =
      (Work.DSEQ0.Cup.proj A X f U q z).hom b := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Work.DSEQ0.Cup.res_comp]
    refine res_pointwise A X f U q z
      (fun k => unitIdx q (Work.DSEQ0.Cup.backIdx 0 q k)) (fun i => unitIdx_backIdx q i) b
  rw [Work.DSEQ0.Cup.res_mul, h1, h2, one_mul]

end Work.DSEQ0Cup
