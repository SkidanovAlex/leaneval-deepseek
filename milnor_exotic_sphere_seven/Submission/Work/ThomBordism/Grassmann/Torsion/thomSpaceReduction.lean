import Mathlib
import Submission.Work.Thom.Continuous
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.Torsion.ModelGeom
import Submission.Work.ThomBordism.Grassmann.Torsion.RadialDefs
import Submission.Work.ThomBordism.Grassmann.Torsion.contractibleFar
import Submission.Work.ThomBordism.Grassmann.Torsion.mvFiniteness
import Submission.Work.ThomBordism.Grassmann.Torsion.mvFinitenessZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-!
# Reduction of the finiteness of `H_*(Th γ)` to the base and the annulus

The Thom space `T = OnePoint E` of the tautological bundle is covered by the two open sets
`near 2 = {fibN < 2}` and `far 1 = {fibN > 1} ∪ {∞}`.  The Mayer–Vietoris finiteness lemma
(`moduleFinite_homology_of_mv`) therefore reduces the finite generation of `H_n(T;ℤ)` to that of

* `H_n(near 2)`, which is that of the Grassmannian `OG k m` (the zero section is a homotopy inverse
  of the bundle projection restricted to `near 2`);
* `H_n(far 1)`, which is finitely generated because `far 1` is contractible (`contractibleFar`);
* `H_n(near 2 ∩ far 1) = H_n({1 < fibN < 2})`, the annulus (identified with `annSet k m`).

The main result is `thomSpaceHomologyFinite_of_inputs`.
-/

open CategoryTheory

namespace Work.ThomBordism.Grassmann.Torsion

open Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## The disc `{fibN < 2}` is homotopy equivalent to the Grassmannian -/

/-- The **projection of the disc `{fibN < 2}` to the Grassmannian**. -/
def discProj (k m : ℕ) : C(↥{p : TM k m | fibN k m p < 2}, OG k m) :=
  ⟨fun q => q.1.proj, (tautologicalBundle k m).continuous_proj.comp continuous_subtype_val⟩

/-- The **zero section** of the tautological bundle, as a map into the disc `{fibN < 2}`. -/
def discZero (k m : ℕ) : C(OG k m, ↥{p : TM k m | fibN k m p < 2}) :=
  ⟨fun x => ⟨⟨x, 0⟩, by
      change fibN k m (⟨x, (0 : Amb k)⟩ : TM k m) < 2
      have h : fibN k m (⟨x, (0 : Amb k)⟩ : TM k m) = 0 :=
        (fibN_eq_zero_iff k m _).mpr rfl
      rw [h]; norm_num⟩,
    (Bundle.Trivialization.continuous_zeroSection ℝ).subtype_mk _⟩

/-- The radial homotopy contracting the disc `{fibN < 2}` onto the zero section. -/
def discHomotopy (k m : ℕ) :
    C(unitInterval × ↥{p : TM k m | fibN k m p < 2},
      ↥{p : TM k m | fibN k m p < 2}) :=
  ⟨fun q => ⟨⟨q.2.1.proj, (q.1 : ℝ) • q.2.1.snd⟩, by
      change fibN k m ⟨(q.2.1).proj, (q.1 : ℝ) • (q.2.1).snd⟩ < 2
      have hl : (0 : ℝ) ≤ q.1 := q.1.2.1
      have hu : (q.1 : ℝ) ≤ 1 := q.1.2.2
      rw [fibN_smul k m hl]
      calc (q.1 : ℝ) * fibN k m q.2.1 ≤ 1 * fibN k m q.2.1 :=
            mul_le_mul_of_nonneg_right hu (fibN_nonneg k m _)
        _ = fibN k m q.2.1 := one_mul _
        _ < 2 := q.2.2⟩,
    (Work.Thom.continuous_smul_section (tautologicalBundle k m)
      ⟨fun q : unitInterval × ↥{p : TM k m | fibN k m p < 2} => q.2.1,
        continuous_subtype_val.comp continuous_snd⟩
      ⟨fun q => (q.1 : ℝ), continuous_subtype_val.comp continuous_fst⟩).subtype_mk _⟩

/-! ## Finite generation of the disc `{fibN < 2}` from the Grassmannian -/

/-- **Finite generation of `H_*(near 2)` from finite generation of `H_*(OG k m)`.**  The bundle
projection restricted to the disc and the zero section are mutually inverse up to the radial
homotopy `discHomotopy`. -/
theorem moduleFinite_homology_of_disc (k m n : ℕ)
    (hG : Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of (OG k m))).homology n)) :
    Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥{p : TM k m | fibN k m p < 2})).homology n) := by
  have hcomp₁ : TopCat.Homotopy
      (CategoryTheory.CategoryStruct.comp (TopCat.ofHom (discZero k m))
        (TopCat.ofHom (discProj k m))) (CategoryTheory.CategoryStruct.id (TopCat.of (OG k m))) :=
    { toContinuousMap :=
        ⟨fun q : unitInterval × OG k m => discProj k m (discZero k m q.2),
          (discProj k m).continuous.comp ((discZero k m).continuous.comp continuous_snd)⟩
      map_zero_left := fun x => rfl
      map_one_left := fun x => rfl }
  have hcomp₂ : TopCat.Homotopy
      (CategoryTheory.CategoryStruct.comp (TopCat.ofHom (discProj k m))
        (TopCat.ofHom (discZero k m)))
      (CategoryTheory.CategoryStruct.id (TopCat.of ↥{p : TM k m | fibN k m p < 2})) :=
    { toContinuousMap := discHomotopy k m
      map_zero_left := fun q => by
        refine Subtype.ext ?_
        change (⟨q.1.proj, (0 : ℝ) • q.1.snd⟩ : TM k m) =
          (⟨q.1.proj, (0 : Amb k)⟩ : TM k m)
        rw [zero_smul]
      map_one_left := fun q => by
        refine Subtype.ext ?_
        change (⟨q.1.proj, (1 : ℝ) • q.1.snd⟩ : TM k m) = q.1
        rw [one_smul] }
  exact moduleFinite_homology_of_homotopyEquiv _ _ hcomp₁ hcomp₂ n hG

/-! ## A trivial homotopy from an equality of maps -/

/-- Two equal continuous maps are homotopic (by the constant homotopy). -/
noncomputable def topCatHomotopy_of_eq {X Y : TopCat} {f g : X ⟶ Y} (h : f = g) :
    TopCat.Homotopy f g := by
  subst h
  exact { toContinuousMap :=
            ⟨fun q : unitInterval × X => f q.2, by fun_prop⟩
          map_zero_left := fun x => rfl
          map_one_left := fun x => rfl }

/-! ## Finite generation for a homeomorphic copy -/

/-- Finite generation of homology transfers along a homeomorphism of topological spaces. -/
theorem moduleFinite_homology_of_homeomorph {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ)
    (hfin : Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology n)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology n) :=
  moduleFinite_homology_of_homotopyEquiv (TopCat.ofHom ⟨⇑e, e.continuous⟩)
    (TopCat.ofHom ⟨⇑e.symm, e.symm.continuous⟩)
    (topCatHomotopy_of_eq (by ext x; exact e.symm_apply_apply x))
    (topCatHomotopy_of_eq (by ext x; exact e.apply_symm_apply x)) n hfin

/-! ## The reduction -/

/-- **Finite generation of `H_*(Th γ)`** from finite generation of the two pieces of the
Mayer–Vietoris cover: the disc `near 2`, and the annulus `annSet k m`. -/
theorem thomSpaceHomologyFinite_of_inputs (k m : ℕ)
    (hU : ∀ n, Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(near k m 2))).homology n))
    (hK : ∀ n, Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(annSet k m))).homology n))
    (n : ℕ) : Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of (TautologicalThomSpace k m))).homology n) := by
  -- the homeomorphism `annSet k m ≃ₜ near 2 ∩ far 1`
  have hann : OnePoint.some '' (annSet k m : Set (TM k m)) = near k m 2 ∩ far k m 1 :=
    (near_inter_far k m).symm
  let e : ↥(annSet k m) ≃ₜ ↥(near k m 2 ∩ far k m 1) :=
    (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage (annSet k m)).trans
      (Homeomorph.setCongr hann)
  have hVi : ∀ j, Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(far k m 1))).homology j) :=
    fun j => Work.ThomBordism.fgch_moduleFinite_homology_of_contractibleOrEmpty ↥(far k m 1)
      (fun _ => contractibleFar k m) j
  have hUVi : ∀ j, Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(near k m 2 ∩ far k m 1))).homology j) :=
    fun j => moduleFinite_homology_of_homeomorph e j (hK j)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact mvFinitenessZero (X := TopCat.of (TautologicalThomSpace k m)) (near k m 2) (far k m 1)
      (isOpen_near k m 2) (isOpen_far_one k m)
      (near_union_far k m (by norm_num)) (hU 0) (hVi 0) (hUVi 0)
  · exact moduleFinite_homology_of_mv (X := TopCat.of (TautologicalThomSpace k m))
      (near k m 2) (far k m 1) (isOpen_near k m 2) (isOpen_far_one k m)
      (near_union_far k m (by norm_num)) hU hVi hUVi hn

end

end Work.ThomBordism.Grassmann.Torsion
