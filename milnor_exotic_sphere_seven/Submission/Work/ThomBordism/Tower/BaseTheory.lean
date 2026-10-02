import Mathlib
import Submission.Work.ThomBordism.Tower.Defs
import Submission.Work.Cohomology.isZero_dualComplex_empty

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The absolute cochain tower: `baseRes` and its theory

The absolute cochains `BaseC W k = C^k(W)` of a piece `W ⊆ B` form a tower under the restrictions
`Work.ThomBordism.baseRes`; this module develops the facts that the tower argument for
`Work.ThomBordism.tower_surj` needs: `baseRes` commutes with the differential, is **surjective**,
compatible families of absolute cochains **glue** to the union, and the resulting gluing is
separating.

The trick that makes all of this cheap is the identification of the absolute cochains of `W` with
the *relative* cochains of `W` modulo the empty set: `rcKern (∅ : Set B) W k` is the kernel of the
restriction of a cochain to the cochains of the *empty* space, which is a zero module, so the
kernel is everything (`absMem`).  Under this identification `baseRes` is `rcResLM (∅ : Set B)`
(`baseRes_eq`), and the whole `rcKern` toolkit (`rcResLM_comm`, `rcResLM_comp`,
`rcResLM_surjective`, `rcKern_iUnion_limit`) transfers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology
open scoped Simplicial

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The empty relative set: membership is automatic -/

/-- The singular simplices of the empty (in `W`) space form an empty type. -/
theorem isEmpty_simplices_empty (W : Set B) (k : ℕ) :
    IsEmpty ((TopCat.toSSet.obj (TopCat.of {z : W // (z : B) ∈ (∅ : Set B)})).obj
      (Opposite.op ⦋k⦌)) :=
  ⟨fun x => by
    have hx := (TopCat.toSSetObjEquiv (TopCat.of {z : W // (z : B) ∈ (∅ : Set B)})
      (Opposite.op ⦋k⦌)) x
    exact (hx (Classical.arbitrary _)).2⟩

/-- The chains of the empty (in `W`) space are a subsingleton. -/
theorem chainsSubsingleton (W : Set B) (k : ℕ) :
    Subsingleton (↑((singularChains ℤ (TopCat.of {z : W // (z : B) ∈ (∅ : Set B)})).X k)) := by
  haveI : IsEmpty ((TopCat.toSSet.obj (TopCat.of {z : W // (z : B) ∈ (∅ : Set B)})).obj
      (Opposite.op ⦋k⦌)) := isEmpty_simplices_empty W k
  haveI : IsZero ((singularChains ℤ (TopCat.of {z : W // (z : B) ∈ (∅ : Set B)})).X k) :=
    isZero_coproduct_of_isEmpty (fun _ : ((TopCat.toSSet.obj
      (TopCat.of {z : W // (z : B) ∈ (∅ : Set B)})).obj (Opposite.op ⦋k⦌)) => ModuleCat.of ℤ ℤ)
  exact ModuleCat.subsingleton_of_isZero this

/-- **Every absolute cochain is a relative cochain modulo the empty set.** -/
theorem absMem (W : Set B) (k : ℕ) (a : BaseC W k) : a ∈ rcKern (∅ : Set B) W k := by
  rw [rcKern, relKern, LinearMap.mem_ker, restr, dualChainMap_f_hom]
  apply LinearMap.ext
  intro y
  have hy : y = 0 := @Subsingleton.elim _ (chainsSubsingleton W k) y 0
  rw [hy, map_zero]
  rfl

/-- The absolute cochains of a piece, as relative cochains modulo the empty set. -/
def toAbs (W : Set B) (k : ℕ) : BaseC W k → ↥(rcKern (∅ : Set B) W k) :=
  fun a => ⟨a, absMem W k a⟩

/-- The inverse of `toAbs`. -/
def ofAbs {W : Set B} {k : ℕ} : ↥(rcKern (∅ : Set B) W k) → BaseC W k := fun x => x.1

@[simp] theorem ofAbs_toAbs (W : Set B) (k : ℕ) (a : BaseC W k) : ofAbs (toAbs W k a) = a := rfl

@[simp] theorem toAbs_ofAbs {W : Set B} {k : ℕ} (x : ↥(rcKern (∅ : Set B) W k)) :
    toAbs W k (ofAbs x) = x := Subtype.ext rfl

@[simp] theorem toAbs_zero (W : Set B) (k : ℕ) : toAbs W k (0 : BaseC W k) = 0 := Subtype.ext rfl

/-- **`baseRes` is the relative-cochain restriction modulo the empty set.** -/
theorem baseRes_eq {W W' : Set B} (h : W ⊆ W') (k : ℕ) (a : BaseC W' k) :
    baseRes h k a = (rcResLM (∅ : Set B) h k (toAbs W' k a)).1 := by
  rw [baseRes, rcResLM_coe]
  rfl

/-- **`toAbs` intertwines `baseRes` with the relative restriction.** -/
theorem toAbs_of_rcResLM {W W' : Set B} (h : W ⊆ W') (k : ℕ) (a : BaseC W' k) :
    toAbs W k (baseRes h k a) = rcResLM (∅ : Set B) h k (toAbs W' k a) :=
  Subtype.ext (baseRes_eq h k a).symm

/-! ## The differentials -/

/-- The cochain differential of the singular cochain complex of a piece is `cochainDiffLM`. -/
theorem cochainDiff_eq_d (W : Set B) (k : ℕ) (a : BaseC W k) :
    cochainDiffLM ℤ (baseSSet W) k a
      = ((SSetCochainComplex ℤ (baseSSet W)).d k (k + 1)).hom a := by
  have h2 : cochainDiffLM ℤ (baseSSet W) k
      = ((SSetCochainComplex ℤ (baseSSet W)).d k (k + 1)).hom := by
    rw [SSetCochainComplex_d]
    rfl
  rw [h2]
  rfl

/-- `baseRes` commutes with the differentials, in the `singularCochainComplex` presentation
(this is `HomologicalComplex.Hom.comm` for the transposed chain map). -/
theorem baseRes_comm_sing {W W' : Set B} (h : W ⊆ W') (k : ℕ) (a : BaseC W' k) :
    baseRes h (k + 1) (((singularCochainComplex ℤ (TopCat.of W')).d k (k + 1)).hom a)
      = ((singularCochainComplex ℤ (TopCat.of W)).d k (k + 1)).hom (baseRes h k a) := by
  have hcomm := congrArg ModuleCat.Hom.hom (HomologicalComplex.Hom.comm
    (dualChainMap ℤ (TopCat.of W) (TopCat.of W') (pdIncl (M := TopCat.of B) W' W h)) k (k + 1))
  simp only [ModuleCat.hom_comp] at hcomm
  have h2 := LinearMap.congr_fun hcomm a
  simp only [LinearMap.comp_apply] at h2
  exact h2.symm

/-- **`baseRes` commutes with the differential.** -/
theorem baseRes_comm {W W' : Set B} (h : W ⊆ W') (k : ℕ) (a : BaseC W' k) :
    baseRes h (k + 1) (cochainDiffLM ℤ (baseSSet W') k a)
      = cochainDiffLM ℤ (baseSSet W) k (baseRes h k a) := by
  rw [cochainDiff_eq_d W' k a, cochainDiff_eq_d W k (baseRes h k a)]
  exact baseRes_comm_sing h k a

/-- Functoriality of `baseRes` in the inclusion. -/
theorem baseRes_comp {S S' T : Set B} (h : S ⊆ S') (h' : S' ⊆ T) (k : ℕ) :
    (baseRes h k).comp (baseRes h' k) = baseRes (h.trans h') k := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply]
  have h1 : (rcResLM (∅ : Set B) (h.trans h') k (toAbs T k a)).1
      = (rcResLM (∅ : Set B) h k (rcResLM (∅ : Set B) h' k (toAbs T k a))).1 :=
    (congrArg Subtype.val (LinearMap.congr_fun (rcResLM_comp (∅ : Set B) h h' k)
      (toAbs T k a))).symm
  rw [baseRes_eq (h.trans h') k a, h1, ← toAbs_of_rcResLM h' k a,
    ← baseRes_eq h k (baseRes h' k a)]

/-! ## Surjectivity -/

/-- **The restriction of absolute cochains is surjective.** -/
theorem baseRes_surjective {W W' : Set B} (h : W ⊆ W') (k : ℕ) :
    Function.Surjective (baseRes h k) := by
  intro a
  obtain ⟨y, hy⟩ := rcResLM_surjective (∅ : Set B) h k (toAbs W k a)
  refine ⟨y.1, ?_⟩
  rw [baseRes_eq h k y.1]
  change (rcResLM (∅ : Set B) h k (toAbs W' k (ofAbs y))).1 = a
  rw [toAbs_ofAbs]
  exact congrArg Subtype.val hy

/-! ## Gluing and separation -/

/-- **Gluing of a compatible family of absolute cochains.**  A family of absolute cochains on the
pieces of an increasing open family, compatible under the restrictions `baseRes`, is the family of
restrictions of a *unique* cochain on the union. -/
theorem baseGlue {J : Type} [LinearOrder J] [WellFoundedLT J] (V : J → Set B)
    (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V) (k : ℕ) (f : (j : J) → BaseC (V j) k)
    (hf : ∀ i j (hij : i ≤ j), baseRes (hmono hij) k (f j) = f i) :
    ∃! g : BaseC (⋃ j, V j) k, ∀ j, baseRes (Set.subset_iUnion V j) k g = f j := by
  have hf' : ∀ i j (hij : i ≤ j),
      rcResLM (∅ : Set B) (hmono hij) k (toAbs (V j) k (f j)) = toAbs (V i) k (f i) := by
    intro i j hij
    apply Subtype.ext
    show (rcResLM (∅ : Set B) (hmono hij) k (toAbs (V j) k (f j))).1 = f i
    rw [← baseRes_eq (hmono hij) k (f j)]
    exact hf i j hij
  obtain ⟨g', hg', hguniq⟩ := (rcKern_iUnion_limit (∅ : Set B) V hopen hmono k
    (fun j => toAbs (V j) k (f j))).mpr hf'
  refine ⟨ofAbs g', ?_, ?_⟩
  · intro j
    rw [baseRes_eq (Set.subset_iUnion V j) k (ofAbs g')]
    change (rcResLM (∅ : Set B) (Set.subset_iUnion V j) k (toAbs (⋃ j, V j) k (ofAbs g'))).1 = f j
    rw [toAbs_ofAbs]
    exact congrArg Subtype.val (hg' j)
  · intro y hy
    have hy' : ∀ j, rcResLM (∅ : Set B) (Set.subset_iUnion V j) k (toAbs (⋃ j, V j) k y)
        = toAbs (V j) k (f j) := by
      intro j
      apply Subtype.ext
      show (rcResLM (∅ : Set B) (Set.subset_iUnion V j) k (toAbs (⋃ j, V j) k y)).1 = f j
      rw [← baseRes_eq (Set.subset_iUnion V j) k y]
      exact hy j
    have huniq : toAbs (⋃ j, V j) k y = g' := hguniq _ hy'
    rw [← huniq]
    rfl

/-- **Separation.**  Two absolute cochains on the union of an increasing open family which restrict
to the same cochain on every piece are equal. -/
theorem baseRes_eq_of_forall {J : Type} [LinearOrder J] [WellFoundedLT J] (V : J → Set B)
    (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V) (k : ℕ)
    {x y : BaseC (⋃ j, V j) k}
    (h : ∀ j, baseRes (Set.subset_iUnion V j) k x = baseRes (Set.subset_iUnion V j) k y) :
    x = y := by
  have hcompat : ∀ i j (hij : i ≤ j),
      rcResLM (∅ : Set B) (hmono hij) k (rcResLM (∅ : Set B) (Set.subset_iUnion V j) k
        (toAbs (⋃ j, V j) k x))
        = rcResLM (∅ : Set B) (Set.subset_iUnion V i) k (toAbs (⋃ j, V j) k x) := by
    intro i j hij
    have hirr : ((hmono hij).trans (Set.subset_iUnion V j)) = (Set.subset_iUnion V i) :=
      Subsingleton.elim _ _
    rw [← LinearMap.comp_apply, rcResLM_comp, hirr]
  obtain ⟨g, hg, hguniq⟩ := (rcKern_iUnion_limit (∅ : Set B) V hopen hmono k
    (fun j => rcResLM (∅ : Set B) (Set.subset_iUnion V j) k (toAbs (⋃ j, V j) k x))).mpr hcompat
  have hsame : ∀ j, rcResLM (∅ : Set B) (Set.subset_iUnion V j) k (toAbs (⋃ j, V j) k y)
      = rcResLM (∅ : Set B) (Set.subset_iUnion V j) k (toAbs (⋃ j, V j) k x) := by
    intro j
    apply Subtype.ext
    show (rcResLM (∅ : Set B) (Set.subset_iUnion V j) k (toAbs (⋃ j, V j) k y)).1
        = (rcResLM (∅ : Set B) (Set.subset_iUnion V j) k (toAbs (⋃ j, V j) k x)).1
    rw [← baseRes_eq (Set.subset_iUnion V j) k y, ← baseRes_eq (Set.subset_iUnion V j) k x, h j]
  have h1 : toAbs (⋃ j, V j) k y = g := hguniq _ hsame
  have h2 : toAbs (⋃ j, V j) k x = g := hguniq _ (fun j => rfl)
  exact congrArg Subtype.val (h2.trans h1.symm)

end

end Work.ThomBordism
