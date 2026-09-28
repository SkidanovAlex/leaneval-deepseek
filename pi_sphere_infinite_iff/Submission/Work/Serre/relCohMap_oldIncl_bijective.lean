import Mathlib
import Submission.Work.Serre.fibreExcisionIso
import Submission.Work.Thom.relCohHomeomorph

/-!
# Excision: the bottom copy of a mapping cylinder can be added to a preimage part

For `q : C(X, Γ)`, a subset `S ⊆ Γ`, the mapping cylinder `cyl q` with bottom copy
`cylBot q = range (cylIncl q)` and the preimage part `M = (cylRetract q) ⁻¹' S`, this file proves
that the inclusion of pairs

  `(M, M ∩ cylBot q)  ↪  (M ∪ cylBot q, cylBot q)`

induces an isomorphism of relative rational cohomology

  `H^k(M ∪ cylBot q, cylBot q; ℚ)  ≅  H^k(M, M ∩ cylBot q; ℚ)`,

i.e. `Work.Serre.relCohMap_oldIncl_bijective`.

The proof is an excision/deformation chain.  Write `N = M ∪ cylBot q`, and let `U = N ∩ cylCollar q`
be the collar of `N` over the bottom copy, `V = N ∩ M`, `A = N ∩ cylBot q`, `AM = M ∩ cylBot q`,
`UM = M ∩ cylCollar q`, `VU = V ∩ U`.

* `H^k(N, A) ≅ H^k(N, U)` and `H^k(M, AM) ≅ H^k(M, UM)`: the collar shrink
  `cylShrink q` retracts `U` (resp. `UM`) onto `A` (resp. `AM`) through maps fixing the target
  pointwise, so the two pairs are homotopy equivalent
  (`Work.Serre.isIso_relCohMap_id_of_deformationRetract`).
* `H^k(M, UM) ≅ H^k(V, VU)`: `V ≅ M` is a homeomorphism of pairs
  (`Work.Thom.bijective_relCohMap_of_homeomorphA`).
* `H^k(V, VU) ≅ H^k(N, U)`: excision — `N ∖ V ⊆ cylBot q` is closed and lies in the interior of the
  open collar `U` (`Work.Serre.isIso_relCohMap_excision_of_interior`).

Composing (which is functoriality of `relCohMap`, `Work.Thom.relCohMap_compA`) expresses
`H^k(N, A) → H^k(M, AM)` as a composite with all but the last factor an isomorphism, whence it is
one itself.

The closedness hypothesis `IsClosed S` in the statement of the target is not needed: only the
bottom copy (always closed) and the collar (always open) are used.
-/

set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {B : Type} [TopologicalSpace B] {E : Type} [TopologicalSpace E]

/-- The collar shrink preserves the preimage part `(cylRetract p) ⁻¹' S`. -/
lemma oldIncl_shrink_mem_preimage (p : C(E, B)) (S : Set B) (t : unitInterval)
    {y : ↥(cylCollar p)}
    (hy : (y : cyl p) ∈ (cylRetract p) ⁻¹' S) :
    (cylShrink p t y : cyl p) ∈ (cylRetract p) ⁻¹' S := by
  rw [Set.mem_preimage] at hy ⊢
  rw [cylRetract_cylShrink]
  exact hy

/-- The collar shrink preserves the union `(cylRetract p) ⁻¹' S ∪ cylBot p`. -/
lemma oldIncl_shrink_mem_union (p : C(E, B)) (S : Set B) (t : unitInterval)
    {y : ↥(cylCollar p)}
    (hy : (y : cyl p) ∈ (cylRetract p) ⁻¹' S ∪ Set.range (cylIncl p)) :
    (cylShrink p t y : cyl p) ∈ (cylRetract p) ⁻¹' S ∪ Set.range (cylIncl p) := by
  rcases hy with h | h
  · exact Or.inl (oldIncl_shrink_mem_preimage p S t h)
  · refine Or.inr ?_
    rw [cylShrink_fixes_bot p t h]
    exact h

/-- **The collar shrink retracts the collar part of `↥Z` onto its bottom part**, for any `Z`
preserved by the shrink: the map `Hⁿ(↥Z, collar ∩ Z) → Hⁿ(↥Z, bottom ∩ Z)` is an isomorphism. -/
lemma oldIncl_isIso_relCohMap_shrink (p : C(E, B)) {Z : Set (cyl p)}
    (hZ : ∀ (t : unitInterval) (y : ↥(cylCollar p)),
      (y : cyl p) ∈ Z → (cylShrink p t y : cyl p) ∈ Z)
    (n : ℕ) :
    CategoryTheory.IsIso (Thom.relCohMap (ContinuousMap.id ↥Z)
      {x : ↥Z | (x : cyl p) ∈ cylBot p}
      {x : ↥Z | (x : cyl p) ∈ cylCollar p}
      (fun x hx => cylBot_subset_cylCollar p hx) ℚ n) := by
  have hAB : {x : ↥Z | (x : cyl p) ∈ cylBot p} ⊆
      {x : ↥Z | (x : cyl p) ∈ cylCollar p} :=
    fun x hx => cylBot_subset_cylCollar p hx
  let W : Set ↥Z := {x : ↥Z | (x : cyl p) ∈ cylCollar p}
  let ι : C(↥W, ↥(cylCollar p)) :=
    ⟨fun y => ⟨y.1.1, y.2⟩,
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)⟩
  let φP : C(unitInterval × ↥W, ↥W) :=
    ⟨fun q => ⟨⟨(cylShrink p q.1 (ι q.2) : cyl p),
        hZ q.1 (ι q.2) q.2.1.2⟩, (cylShrink p q.1 (ι q.2)).2⟩,
      Continuous.subtype_mk (Continuous.subtype_mk
        (continuous_subtype_val.comp ((cylShrinkHomotopy p).continuous.comp
          (continuous_fst.prodMk (ι.continuous.comp continuous_snd))))
        (fun q => hZ q.1 (ι q.2) q.2.1.2)) (fun q => (cylShrink p q.1 (ι q.2)).2)⟩
  let φ : C(↥W, ↥W) := φP.comp ⟨fun y => (1, y), continuous_const.prodMk continuous_id⟩
  refine isIso_relCohMap_id_of_deformationRetract _ _ hAB φ ?_ ?_ ?_ n
  · refine ⟨φP, ?_, ?_⟩
    · intro y
      dsimp only [φP]
      refine Subtype.ext (Subtype.ext ?_)
      show (cylShrink p 0 (ι y) : cyl p) = (y.1.1 : cyl p)
      rw [← cylShrinkHomotopy_apply p 0 (ι y)]
      exact congrArg Subtype.val ((cylShrinkHomotopy p).map_zero_left (ι y))
    · intro y
      rfl
  · intro t y hy
    dsimp only [φP]
    refine Subtype.ext (Subtype.ext ?_)
    show (cylShrink p t (ι y) : cyl p) = (y.1.1 : cyl p)
    exact congrArg Subtype.val
      (cylShrink_fixes_bot p t (y := ι y) hy)
  · intro y
    dsimp only [φ]
    show (cylShrink p 1 (ι y) : cyl p) ∈ cylBot p
    exact cylShrink_one_mem_cylBot p (ι y)

/-- **Excision for the union of the bottom copy with a preimage part.** -/
theorem oldIncl_iso {B : Type} [TopologicalSpace B] {E : Type} [TopologicalSpace E]
    (p : C(E, B)) (S : Set B) (n : ℕ) :
    CategoryTheory.IsIso (Thom.relCohMap
      (⟨fun x => ⟨(x : cyl p), Set.subset_union_left x.2⟩,
        Continuous.subtype_mk continuous_subtype_val _⟩ :
        C(↥((cylRetract p) ⁻¹' S),
          ↥((cylRetract p) ⁻¹' S ∪ Set.range (cylIncl p))))
      {x : ↥((cylRetract p) ⁻¹' S) |
        (x : cyl p) ∈ Set.range (cylIncl p)}
      {x : ↥((cylRetract p) ⁻¹' S ∪ Set.range (cylIncl p)) |
        (x : cyl p) ∈ Set.range (cylIncl p)}
      (fun x hx => hx) ℚ n) := by
  classical
  set M : Set (cyl p) := (cylRetract p) ⁻¹' S with hM
  set N : Set (cyl p) := M ∪ Set.range (cylIncl p) with hN
  have hMN : M ⊆ N := Set.subset_union_left
  set A : Set ↥N := {x : ↥N | (x : cyl p) ∈ cylBot p} with hA
  set U : Set ↥N := {x : ↥N | (x : cyl p) ∈ cylCollar p} with hU
  set V : Set ↥N := {x : ↥N | (x : cyl p) ∈ M} with hV
  set AM : Set ↥M := {x : ↥M | (x : cyl p) ∈ cylBot p} with hAM
  set UM : Set ↥M := {x : ↥M | (x : cyl p) ∈ cylCollar p} with hUM
  set VU : Set ↥V := {x : ↥V | (x : ↥N) ∈ U} with hVU
  let e : ↥V ≃ₜ ↥M :=
    { toFun := fun y => ⟨(y : ↥N).1, y.2⟩
      invFun := fun x => ⟨⟨x.1, hMN x.2⟩, x.2⟩
      left_inv := fun y => by ext <;> rfl
      right_inv := fun x => by ext <;> rfl
      continuous_toFun :=
        Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _ }
  -- named maps
  set incl : C(↥M, ↥N) :=
    ⟨fun x => ⟨(x : cyl p), hMN x.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩
    with hincl
  set subV : C(↥V, ↥N) := ⟨Subtype.val, continuous_subtype_val⟩ with hsubV
  set esymm : C(↥M, ↥V) := (e.symm : C(↥M, ↥V)) with hesymm
  -- the A-part bookkeeping
  have hf₁ : ∀ x ∈ AM, incl x ∈ A := fun x hx => hx
  have hg₁ : ∀ y ∈ A, (ContinuousMap.id ↥N) y ∈ U :=
    fun y hy => cylBot_subset_cylCollar p hy
  have hfg : ∀ x ∈ AM, incl x ∈ U :=
    fun x hx => cylBot_subset_cylCollar p hx
  have hgf₁ : ∀ x ∈ AM, (ContinuousMap.id ↥N) (incl x) ∈ U := hfg
  have he' : ∀ x : ↥M, x ∈ UM ↔ (esymm : C(↥M, ↥V)) x ∈ VU := fun x => Iff.rfl
  have hf₂ : ∀ x ∈ UM, (esymm : C(↥M, ↥V)) x ∈ VU := fun x hx => (he' x).mp hx
  have hg₂ : ∀ y ∈ VU, (subV : C(↥V, ↥N)) y ∈ U := fun y hy => hy
  have hmid : ∀ x ∈ UM, ((subV : C(↥V, ↥N)).comp (esymm : C(↥M, ↥V))) x ∈ U :=
    fun x hx => (he' x).mp hx
  have hf₃ : ∀ x ∈ AM, (ContinuousMap.id ↥M) x ∈ UM :=
    fun x hx => cylBot_subset_cylCollar p hx
  have hg₃ : ∀ y ∈ UM, ((subV : C(↥V, ↥N)).comp (esymm : C(↥M, ↥V))) y ∈ U :=
    fun y hy => (he' y).mp hy
  have hgf₃ : ∀ x ∈ AM,
      ((subV : C(↥V, ↥N)).comp (esymm : C(↥M, ↥V))) ((ContinuousMap.id ↥M) x) ∈ U :=
    fun x hx => cylBot_subset_cylCollar p hx
  -- the isomorphisms
  have hZ_N : ∀ (t : unitInterval) (y : ↥(cylCollar p)),
      (y : cyl p) ∈ N → (cylShrink p t y : cyl p) ∈ N :=
    fun t y hy => oldIncl_shrink_mem_union p S t hy
  have hZ_M : ∀ (t : unitInterval) (y : ↥(cylCollar p)),
      (y : cyl p) ∈ M → (cylShrink p t y : cyl p) ∈ M :=
    fun t y hy => oldIncl_shrink_mem_preimage p S t hy
  haveI h1 : CategoryTheory.IsIso (Thom.relCohMap (ContinuousMap.id ↥N) A U hg₁ ℚ n) :=
    oldIncl_isIso_relCohMap_shrink p (Z := N) hZ_N n
  haveI h4 : CategoryTheory.IsIso (Thom.relCohMap (ContinuousMap.id ↥M) AM UM hf₃ ℚ n) :=
    oldIncl_isIso_relCohMap_shrink p (Z := M) hZ_M n
  haveI h3 : CategoryTheory.IsIso
      (Thom.relCohMap (esymm : C(↥M, ↥V)) UM VU hf₂ ℚ n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Thom.bijective_relCohMap_of_homeomorphA UM VU e.symm he' ℚ n)
  have hUopen : IsOpen U := (isOpen_cylCollar p).preimage continuous_subtype_val
  have hAclosed : IsClosed A := (isClosed_cylBot p).preimage continuous_subtype_val
  have hcompl : ({x : ↥N | x ∉ ({y : ↥N | y ∉ V} : Set ↥N)} : Set ↥N) = V := by
    ext x; by_cases hx : x ∈ V <;> simp [hx]
  have hclos : closure ({y : ↥N | y ∉ V} : Set ↥N) ⊆ interior U := by
    have h1 : ({y : ↥N | y ∉ V} : Set ↥N) ⊆ A := by
      intro y hy
      rcases y.2 with h | h
      · exact absurd h hy
      · exact h
    calc closure ({y : ↥N | y ∉ V} : Set ↥N) ⊆ closure A := closure_mono h1
      _ = A := hAclosed.closure_eq
      _ ⊆ interior U := by
            rw [hUopen.interior_eq]
            exact fun x hx => cylBot_subset_cylCollar p hx
  haveI h2 : CategoryTheory.IsIso
      (Thom.relCohMap (subV : C(↥V, ↥N)) VU U hg₂ ℚ n) :=
    isIso_relCohMap_excision_of_interior ℚ U V
      (by
        rw [← hcompl]
        exact Work.Cohomology.univ_eq_interior_union_compl (X := TopCat.of ↥N)
          U {y : ↥N | y ∉ V} hclos) n
  -- the composite identity of maps
  have hcomp : (subV : C(↥V, ↥N)).comp (esymm : C(↥M, ↥V)) = incl := by
    ext x
    show ((e.symm x : ↥V) : cyl p) = ((incl x : ↥N) : cyl p)
    rfl
  -- the middle map
  have hstep₁ : (Thom.relCohMap (ContinuousMap.id ↥N) A U hg₁ ℚ n)
      ≫ (Thom.relCohMap incl AM A hf₁ ℚ n)
      = Thom.relCohMap incl AM U hfg ℚ n := by
    rw [Thom.relCohMap_compA AM A U incl (ContinuousMap.id ↥N) hf₁ hg₁ hgf₁ ℚ n]
    exact Thom.relCohMap_congr' (f := (ContinuousMap.id ↥N).comp incl) (f' := incl) AM U
      (by ext x; rfl) hgf₁ hfg ℚ n
  have hstep₂ : (Thom.relCohMap (subV : C(↥V, ↥N)) VU U hg₂ ℚ n)
      ≫ (Thom.relCohMap (esymm : C(↥M, ↥V)) UM VU hf₂ ℚ n)
      = Thom.relCohMap (((subV : C(↥V, ↥N)).comp (esymm : C(↥M, ↥V)))) UM U hmid ℚ n :=
    Thom.relCohMap_compA UM VU U (esymm : C(↥M, ↥V)) (subV : C(↥V, ↥N)) hf₂ hg₂ hmid ℚ n
  have hstep₃ : (Thom.relCohMap (((subV : C(↥V, ↥N)).comp (esymm : C(↥M, ↥V))))
        UM U hmid ℚ n)
      ≫ (Thom.relCohMap (ContinuousMap.id ↥M) AM UM hf₃ ℚ n)
      = Thom.relCohMap incl AM U hfg ℚ n := by
    rw [Thom.relCohMap_compA AM UM U (ContinuousMap.id ↥M)
      (((subV : C(↥V, ↥N)).comp (esymm : C(↥M, ↥V)))) hf₃ hg₃ hgf₃ ℚ n]
    exact Thom.relCohMap_congr'
      (f := ((subV : C(↥V, ↥N)).comp (esymm : C(↥M, ↥V))).comp (ContinuousMap.id ↥M))
      (f' := incl) AM U (by rw [ContinuousMap.comp_id, hcomp]) hgf₃ hfg ℚ n
  haveI hWiso : CategoryTheory.IsIso (Thom.relCohMap incl AM U hfg ℚ n) := by
    rw [← hstep₃, ← hstep₂]
    infer_instance
  haveI hcompiso : CategoryTheory.IsIso
      ((Thom.relCohMap (ContinuousMap.id ↥N) A U hg₁ ℚ n)
        ≫ (Thom.relCohMap incl AM A hf₁ ℚ n)) := by
    rw [hstep₁]
    exact hWiso
  show CategoryTheory.IsIso (Thom.relCohMap incl AM A hf₁ ℚ n)
  exact CategoryTheory.IsIso.of_isIso_comp_left
    (Thom.relCohMap (ContinuousMap.id ↥N) A U hg₁ ℚ n)
    (Thom.relCohMap incl AM A hf₁ ℚ n)

/-- **The inclusion of the pair `(old, A ∩ old)` into `(new, A)` induces a bijection on relative
rational cohomology.** -/
theorem relCohMap_oldIncl_bijective {Γ X : Type} [TopologicalSpace Γ] [TopologicalSpace X]
    (q : C(X, Γ)) (S : Set Γ) (hS : IsClosed S) (k : ℕ) :
    Function.Bijective (fun u : Work.Thom.RelCoh ℚ k
        ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q))
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q)) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} =>
      (Work.Thom.relCohMap
        (⟨fun x => ⟨x.1, Or.inl x.2⟩, by continuity⟩ :
          C(↥((Work.Serre.cylRetract q) ⁻¹' S),
            ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q))))
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' S) | (x : Work.Serre.cyl q) ∈
          Set.range (Work.Serre.cylIncl q)}
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q)) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
        (fun _ hx => hx) ℚ k).hom u) := by
  exact (ConcreteCategory.isIso_iff_bijective _).mp (oldIncl_iso q S k)

end

end Work.Serre
