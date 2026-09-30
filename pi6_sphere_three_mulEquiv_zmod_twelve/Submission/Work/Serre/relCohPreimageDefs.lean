import Mathlib
import Submission.Work.Serre.C1Cyl

/-!
# The collar coordinate of a mapping cylinder

For a continuous map `q : C(X,Γ)` the mapping cylinder `cyl q` is the quotient of
`(X × I) ⊕ Γ` by the relation `(x,1) ~ q x`.  This file introduces the **collar coordinate**

`cylLam q : C(cyl q, I)`,  `cylLam q (x,t) = t` on `X × I`,  `cylLam q z = 1` on the target copy,

the open **collar** `cylCollar q = {y | (cylLam q y : ℝ) < 1}` (the part of the cylinder below the
top), and the bottom copy `cylBot q = range (cylIncl q) = {λ = 0}`.

The point of the collar coordinate is that on the collar the quotient map `cylMk q` is injective
(`cylCollar_injective`), so that the collar is the "honest" product `X × [0,1)` (the homeomorphism
`cylCollarHomeo` proved in `Submission/Work/Serre/cylCollarHomeo.lean`) and one can push the collar
down onto the bottom copy (the *shrink*, in `Submission/Work/Serre/cylShrink.lean`).  This is the
input for the vanishing of the relative cohomology of the collar pair, hence for
`Work.Serre.relCoh_pair_preimage_iso`.
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]

/-! ## The collar coordinate -/

/-- The collar coordinate on the presenting disjoint union `(X × I) ⊕ Γ`: the height `t` on the
cylinder part and `1` on the target copy. -/
def cylLamFun (q : C(X, Γ)) : (X × unitInterval) ⊕ Γ → unitInterval :=
  Sum.elim (fun p => p.2) (fun _ => 1)

@[simp] lemma cylLamFun_inl (q : C(X, Γ)) (x : X) (t : unitInterval) :
    cylLamFun q (Sum.inl (x, t)) = t := rfl

@[simp] lemma cylLamFun_inr (q : C(X, Γ)) (γ : Γ) : cylLamFun q (Sum.inr γ) = 1 := rfl

/-- The collar coordinate is constant on the equivalence classes of the mapping cylinder. -/
theorem cylLamFun_rel (q : C(X, Γ)) : ∀ a b : (X × unitInterval) ⊕ Γ,
    Relation.EqvGen (cylRel q) a b → cylLamFun q a = cylLamFun q b := by
  have hgen : ∀ a b : (X × unitInterval) ⊕ Γ, cylRel q a b →
      cylLamFun q a = cylLamFun q b := by
    rintro a b ⟨p, rfl, rfl⟩
    rfl
  intro a b hab
  induction hab with
  | rel x y h => exact hgen x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The collar coordinate** `λ : cyl q → I` of a mapping cylinder: the height in the cylinder
part, and `1` on the target copy. -/
def cylLam (q : C(X, Γ)) : C(cyl q, unitInterval) where
  toFun := Quotient.lift (cylLamFun q) (cylLamFun_rel q)
  continuous_toFun :=
    (continuous_snd.sumElim continuous_const).quotient_lift (cylLamFun_rel q)

@[simp] lemma cylLam_cylMk (q : C(X, Γ)) (z : (X × unitInterval) ⊕ Γ) :
    cylLam q (cylMk q z) = cylLamFun q z := rfl

@[simp] lemma cylLam_inl (q : C(X, Γ)) (x : X) (t : unitInterval) :
    cylLam q (cylMk q (Sum.inl (x, t))) = t := rfl

@[simp] lemma cylLam_inr (q : C(X, Γ)) (γ : Γ) :
    cylLam q (cylMk q (Sum.inr γ)) = 1 := rfl

@[simp] lemma cylLam_cylIncl (q : C(X, Γ)) (x : X) : cylLam q (cylIncl q x) = 0 := rfl

@[simp] lemma cylLam_cylInr (q : C(X, Γ)) (γ : Γ) : cylLam q (cylInr q γ) = 1 := rfl

/-! ## The collar and the bottom copy -/

/-- **The collar** of the mapping cylinder: the part of the cylinder below the top. -/
def cylCollar (q : C(X, Γ)) : Set (cyl q) := {y | (cylLam q y : ℝ) < 1}

/-- The collar is open. -/
theorem isOpen_cylCollar (q : C(X, Γ)) : IsOpen (cylCollar q) :=
  isOpen_lt (continuous_subtype_val.comp (cylLam q).continuous) continuous_const

/-- **The bottom copy** of the source inside the mapping cylinder. -/
def cylBot (q : C(X, Γ)) : Set (cyl q) := Set.range (cylIncl q)

/-- The bottom copy is contained in the collar. -/
theorem cylBot_subset_cylCollar (q : C(X, Γ)) : cylBot q ⊆ cylCollar q := by
  rintro y ⟨x, rfl⟩
  show ((cylLam q (cylIncl q x) : unitInterval) : ℝ) < 1
  rw [cylLam_cylIncl]
  norm_num

/-- The collar is the preimage of the open half interval `[0,1)`. -/
theorem cylCollar_eq_preimage (q : C(X, Γ)) :
    cylCollar q = cylLam q ⁻¹' {t : unitInterval | (t : ℝ) < 1} := rfl

theorem mem_cylCollar_iff (q : C(X, Γ)) (y : cyl q) :
    y ∈ cylCollar q ↔ (cylLam q y : ℝ) < 1 := Iff.rfl

/-! ## Points of the collar and of the bottom copy -/

/-- **The collar consists of the points `⟦inl (x,t)⟧` with `t < 1`**: a point of the collar has a
representative of the form `inl (x,t)` (it is not a target point), with `t < 1`. -/
theorem exists_eq_cylMk_of_mem_cylCollar (q : C(X, Γ)) {y : cyl q} (hy : y ∈ cylCollar q) :
    ∃ (x : X) (t : unitInterval), (t : ℝ) < 1 ∧ y = cylMk q (Sum.inl (x, t)) := by
  induction y using Quotient.inductionOn with
  | h z =>
    cases z with
    | inl p =>
      refine ⟨p.1, p.2, ?_, rfl⟩
      have hy' : ((cylLam q (cylMk q (Sum.inl p)) : unitInterval) : ℝ) < 1 := hy
      rw [cylLam_cylMk, cylLamFun_inl] at hy'
      exact hy'
    | inr γ =>
      have hy' : ((cylLam q (cylMk q (Sum.inr γ)) : unitInterval) : ℝ) < 1 := hy
      rw [cylLam_cylMk, cylLamFun_inr] at hy'
      exact absurd hy' (lt_irrefl 1)

/-- **The collar is injective for `cylMk`**: two points of the collar with the same image in the
mapping cylinder are equal. -/
theorem cylCollar_injective (q : C(X, Γ)) {x x' : X} {t t' : unitInterval}
    (ht : (t : ℝ) < 1) (h : cylMk q (Sum.inl (x, t)) = cylMk q (Sum.inl (x', t'))) :
    x = x' ∧ t = t' := by
  have hrel : Relation.EqvGen (cylRel q) (Sum.inl (x, t)) (Sum.inl (x', t')) :=
    Quotient.exact h
  have ht1 : t ≠ 1 := by
    intro h1; rw [h1] at ht; exact lt_irrefl 1 ht
  have h' : (Sum.inl (x', t') : (X × unitInterval) ⊕ Γ) = Sum.inl (x, t) :=
    (eqvGen_inl_iff q ht1 hrel).mp rfl
  refine ⟨?_, ?_⟩
  · exact (congrArg Prod.fst (Sum.inl.inj h')).symm
  · exact (congrArg Prod.snd (Sum.inl.inj h')).symm

/-- A point of the collar has a unique representative of the form `inl (x,t)`. -/
theorem eq_of_cylMk_eq_cylMk (q : C(X, Γ)) {x x' : X} {t t' : unitInterval}
    (ht : (t : ℝ) < 1) (h : cylMk q (Sum.inl (x, t)) = cylMk q (Sum.inl (x', t'))) :
    Sum.inl (x, t) = (Sum.inl (x', t') : (X × unitInterval) ⊕ Γ) := by
  obtain ⟨h1, h2⟩ := cylCollar_injective q ht h
  rw [h1, h2]

/-- A point of the bottom copy is `cylIncl q x` for a unique `x` (the embedding property). -/
theorem cylIncl_injective' (q : C(X, Γ)) : Function.Injective (cylIncl q) :=
  cylIncl_injective q

/-- The half-open interval `[0,1)` of the unit interval. -/
abbrev CollT := ↥{t : unitInterval | (t : ℝ) < 1}

theorem coe_unitIntervalMulSub (s t : unitInterval) :
    ((unitIntervalMulSub s t : unitInterval) : ℝ) = (1 - (s : ℝ)) * (t : ℝ) := rfl

theorem coe_unitIntervalMulSub_lt_one (s : unitInterval) {t : unitInterval}
    (ht : (t : ℝ) < 1) : ((unitIntervalMulSub s t : unitInterval) : ℝ) < 1 := by
  rw [coe_unitIntervalMulSub]
  nlinarith [s.2.1, t.2.1, ht]

/-- The *shrink* of the collar, in the product model: `(x,t) ↦ (x, (1-s)t)`. -/
def collarShrinkProd (s : unitInterval) :
    C(X × CollT, X × CollT) :=
  ⟨fun p => (p.1, (⟨unitIntervalMulSub s p.2.1, coe_unitIntervalMulSub_lt_one s p.2.2⟩ : CollT)),
   by
    refine Continuous.prodMk continuous_fst ?_
    refine (continuous_induced_rng (f := (Subtype.val : CollT → unitInterval))).2 ?_
    refine (continuous_induced_rng (f := (Subtype.val : unitInterval → ℝ))).2 ?_
    show Continuous fun p : X × CollT => (1 - (s : ℝ)) * ((p.2 : CollT) : ℝ)
    fun_prop⟩

@[simp] theorem collarShrinkProd_apply (s : unitInterval) (p : X × CollT) :
    (collarShrinkProd (X := X) s p).1 = p.1 := rfl

@[simp] theorem collarShrinkProd_snd_apply (s : unitInterval) (p : X × CollT) :
    ((collarShrinkProd (X := X) s p).2 : unitInterval) = unitIntervalMulSub s p.2.1 := rfl

/-- The joint version of `collarShrinkProd`. -/
def collarShrinkProdPair : C(unitInterval × (X × CollT), X × CollT) :=
  ⟨fun q => collarShrinkProd q.1 q.2, by
    refine Continuous.prodMk (continuous_fst.comp continuous_snd) ?_
    refine (continuous_induced_rng (f := (Subtype.val : CollT → unitInterval))).2 ?_
    refine (continuous_induced_rng (f := (Subtype.val : unitInterval → ℝ))).2 ?_
    show Continuous fun q : unitInterval × (X × CollT) => (1 - (q.1 : ℝ)) * ((q.2.2 : CollT) : ℝ)
    fun_prop⟩

/-- **The shrink homotopy in the product model**: a homotopy from the identity to the projection
onto `X × {0}`. -/
noncomputable def collarShrinkProdHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id (X × CollT)) (collarShrinkProd 1) where
  toContinuousMap := collarShrinkProdPair
  map_zero_left := fun p => by
    show collarShrinkProd (0 : unitInterval) p = p
    refine Prod.ext (collarShrinkProd_apply 0 p) ?_
    refine Subtype.ext ?_
    rw [collarShrinkProd_snd_apply, unitIntervalMulSub_zero_left]
  map_one_left := fun p => rfl

theorem collarShrinkProdHomotopy_apply (s : unitInterval) (p : X × CollT) :
    collarShrinkProdHomotopy (s, p) = collarShrinkProd s p := rfl

/-- The shrink homotopy fixes the bottom copy `X × {0}`. -/
theorem collarShrinkProdHomotopy_bot (s : unitInterval) (x : X)
    (t₀ : CollT) (ht : (t₀ : unitInterval) = 0) :
    collarShrinkProdHomotopy (s, (x, t₀)) = (x, t₀) := by
  rw [collarShrinkProdHomotopy_apply]
  refine Prod.ext (collarShrinkProd_apply s (x, t₀)) ?_
  refine Subtype.ext ?_
  rw [collarShrinkProd_snd_apply, ht]
  apply Subtype.ext
  rw [coe_unitIntervalMulSub]
  norm_num

/-- The part of the mapping cylinder lying over `S ⊆ Γ`: the preimage of `S` under the retraction. -/
abbrev cylPre (q : C(X, Γ)) (S : Set Γ) : Set (cyl q) := (cylRetract q) ⁻¹' S

/-! ## The retraction on the presenting space -/

@[simp] theorem cylRetract_cylMk (q : C(X, Γ)) (z : (X × unitInterval) ⊕ Γ) :
    cylRetract q (cylMk q z) = cylRetractFun q z := rfl

@[simp] theorem cylRetractFun_inl (q : C(X, Γ)) (x : X) (t : unitInterval) :
    cylRetractFun q (Sum.inl (x, t)) = q x := rfl

@[simp] theorem cylRetractFun_inr (q : C(X, Γ)) (γ : Γ) :
    cylRetractFun q (Sum.inr γ) = γ := rfl

@[simp] theorem cylRetract_cylIncl_eq (q : C(X, Γ)) (x : X) :
    cylRetract q (cylIncl q x) = q x := rfl

@[simp] theorem cylIncl_eq_cylMk (q : C(X, Γ)) (x : X) :
    cylIncl q x = cylMk q (Sum.inl (x, 0)) := rfl

end

end Work.Serre
