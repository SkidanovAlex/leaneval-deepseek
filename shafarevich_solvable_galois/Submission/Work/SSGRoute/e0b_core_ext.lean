import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ext` via a projective resolution, with the hom universe decoupled from the object universe

Copies of `Submission/Work/SSGRoute/ExtBridge.lean` and
`Submission/Work/SSGRoute/projRes_homologyAddEquiv_extMk.lean`, verbatim except that the universe
`v` of the *morphisms* of `C` is no longer forced to be the universe of `C` itself.  The originals
state everything with `[Category.{u} C]` for `C : Type u`, which is **not satisfiable** for
`C = Rep.{0} Coeff G`: there `C : Type 1` (objects in `Rep.{0} Coeff G : Type 1`) while the homs
`A ⟶ B` live in `Type 0`, so the required `Category.{1,1} (Rep.{0} Coeff G)` does not exist.  With
the relaxation the results apply to the representation categories that `PTDefs` uses, which is what
node `E0b` needs.
-/

namespace Work.SSGRoute.E0bCore

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type*} [Ring k] [Linear k C]
  {X Y : C}

/-- The underlying morphism `R.complex.X n ⟶ Y` of an element of the `n`-cycles of the complex
`Hom(R_•, Y) = R.complex.linearYonedaObj k Y`. -/
@[irreducible] noncomputable def cycHom (R : ProjectiveResolution X) (n : ℕ)
    (z : (R.complex.linearYonedaObj k Y).cycles n) : R.complex.X n ⟶ Y :=
  (R.complex.linearYonedaObj k Y).iCycles n z

variable [HasExt.{v} C]

set_option linter.unusedSectionVars false

lemma cycHom_add (R : ProjectiveResolution X) (n : ℕ)
    (z w : (R.complex.linearYonedaObj k Y).cycles n) :
    cycHom R n (z + w) = cycHom R n z + cycHom R n w := by
  unfold cycHom
  exact map_add (ModuleCat.Hom.hom ((R.complex.linearYonedaObj k Y).iCycles n)) z w

lemma cycHom_smul (R : ProjectiveResolution X) (n : ℕ) (r : k)
    (z : (R.complex.linearYonedaObj k Y).cycles n) :
    cycHom R n (r • z) = r • cycHom R n z := by
  unfold cycHom
  exact map_smul (ModuleCat.Hom.hom ((R.complex.linearYonedaObj k Y).iCycles n)) r z

lemma cycHom_zero (R : ProjectiveResolution X) (n : ℕ) :
    cycHom R n (0 : (R.complex.linearYonedaObj k Y).cycles n) = 0 := by
  unfold cycHom
  exact map_zero (ModuleCat.Hom.hom ((R.complex.linearYonedaObj k Y).iCycles n))

/-- Every element of the `n`-cycles gives a morphism `R.complex.X n ⟶ Y` satisfying the cocycle
condition of `ProjectiveResolution.extMk`. -/
lemma cycHom_cocycle (R : ProjectiveResolution X) (n : ℕ)
    (z : (R.complex.linearYonedaObj k Y).cycles n) :
    R.complex.d (n + 1) n ≫ cycHom R n z = 0 := by
  unfold cycHom
  have h := ConcreteCategory.congr_hom ((R.complex.linearYonedaObj k Y).iCycles_d n (n+1)) z
  rw [ConcreteCategory.comp_apply] at h
  change (R.complex.linearYonedaObj k Y).d n (n+1)
    ((R.complex.linearYonedaObj k Y).iCycles n z) = 0 at h
  change R.complex.d (n+1) n ≫ ((R.complex.linearYonedaObj k Y).iCycles n z) = 0
  exact h

/-- On the `n`-cycles produced by `HomologicalComplex.cyclesMk` out of a cocycle `f`, `cycHom`
returns `f`. -/
lemma cycHom_cyclesMk (R : ProjectiveResolution X) (n : ℕ) (f : R.complex.X n ⟶ Y)
    (hK : (R.complex.linearYonedaObj k Y).d n (n+1) f = 0) :
    cycHom R n ((R.complex.linearYonedaObj k Y).cyclesMk f (n+1)
        (ComplexShape.next_eq' (c := ComplexShape.up ℕ) rfl) hK) = f := by
  unfold cycHom
  have hK' : (ConcreteCategory.hom ((forget₂ (ModuleCat k) Ab).map ((R.complex.linearYonedaObj k Y).d n (n+1)))) f = 0 := hK
  exact HomologicalComplex.i_cyclesMk (R.complex.linearYonedaObj k Y) f (n+1)
    (ComplexShape.next_eq' (c := ComplexShape.up ℕ) rfl) hK'

/-- The differential of `Hom(K_•, Y)` is precomposition with the differential of `K`. -/
lemma linearYonedaObj_d_apply (K : ChainComplex C ℕ) (Y : C) {i j : ℕ} (hij : i + 1 = j)
    (f : K.X i ⟶ Y) :
    (K.linearYonedaObj k Y).d i j f = (K.d j i) ≫ f := by
  subst hij
  rfl

/-- On the boundaries `K.toCycles i n x`, `cycHom` returns the composite with the differential. -/
lemma cycHom_toCycles (R : ProjectiveResolution X) (n : ℕ)
    (x : (R.complex.linearYonedaObj k Y).X ((ComplexShape.up ℕ).prev n))
    (hp : (ComplexShape.up ℕ).prev n + 1 = n) :
    cycHom R n ((R.complex.linearYonedaObj k Y).toCycles ((ComplexShape.up ℕ).prev n) n x)
      = R.complex.d n ((ComplexShape.up ℕ).prev n) ≫ x := by
  let K := R.complex.linearYonedaObj k Y
  unfold cycHom
  have h := ConcreteCategory.congr_hom (K.toCycles_i ((ComplexShape.up ℕ).prev n) n) x
  rw [ConcreteCategory.comp_apply] at h
  change K.iCycles n (K.toCycles ((ComplexShape.up ℕ).prev n) n x)
    = K.d ((ComplexShape.up ℕ).prev n) n x at h
  rw [h]
  exact linearYonedaObj_d_apply R.complex Y hp x

/-- In degree `0` the boundary map `K.toCycles (prev 0) 0` is the zero map, so `cycHom` vanishes
on its image. -/
lemma cycHom_toCycles_zero (R : ProjectiveResolution X)
    (x : (R.complex.linearYonedaObj k Y).X ((ComplexShape.up ℕ).prev 0)) :
    cycHom R 0 ((R.complex.linearYonedaObj k Y).toCycles ((ComplexShape.up ℕ).prev 0) 0 x) = 0 := by
  let K := R.complex.linearYonedaObj k Y
  unfold cycHom
  have h := ConcreteCategory.congr_hom (K.toCycles_i ((ComplexShape.up ℕ).prev 0) 0) x
  rw [ConcreteCategory.comp_apply] at h
  change K.iCycles 0 (K.toCycles ((ComplexShape.up ℕ).prev 0) 0 x)
    = K.d ((ComplexShape.up ℕ).prev 0) 0 x at h
  rw [h]
  rw [HomologicalComplex.shape]
  · rfl
  · rw [ComplexShape.up_Rel]
    omega

/-- `extMk` only depends on the morphism, not on the proof of the cocycle condition. -/
lemma extMk_congr (R : ProjectiveResolution X) {n : ℕ} {f g : R.complex.X n ⟶ Y} (h : f = g)
    (hf : R.complex.d (n + 1) n ≫ f = 0) (hg : R.complex.d (n + 1) n ≫ g = 0) :
    R.extMk f (n + 1) rfl hf = R.extMk g (n + 1) rfl hg := by
  subst h
  simp only [ProjectiveResolution.extMk]



open CategoryTheory Limits CochainComplex

section

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type*} [Ring k] [Linear k C]
  {X Y : C} [HasExt.{v} C]

set_option linter.unusedSectionVars false

/-- The inclusion of the cycles of `Hom(R_•, Y)` is `cycHom`. -/
lemma iCycles_eq_cycHom (R : ProjectiveResolution X) (n : ℕ)
    (z : (R.complex.linearYonedaObj k Y).cycles n) :
    (R.complex.linearYonedaObj k Y).iCycles n z = cycHom R n z := by
  unfold cycHom
  rfl

/-- `extMk` vanishes in degree `0` only on `0`. -/
lemma extMk_deg_zero_eq_zero (R : ProjectiveResolution X) (f : R.complex.X 0 ⟶ Y)
    (hf : R.complex.d 1 0 ≫ f = 0) : R.extMk f 1 rfl hf = 0 → f = 0 := by
  intro h
  have h1 : R.extEquivCohomologyClass (R.extMk f 1 rfl hf) = 0 := by
    rw [h, ProjectiveResolution.extEquivCohomologyClass_zero]
  rw [ProjectiveResolution.extEquivCohomologyClass_extMk R f 1 rfl hf] at h1
  rw [CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff] at h1
  simp only [CochainComplex.HomComplex.Cocycle.toSingleMk_mem_coboundaries_iff] at h1
  obtain ⟨g, hg⟩ := h1
  have hg0 : g = 0 :=
    (CochainComplex.isZero_of_isStrictlyLE R.cochainComplex 0 (-↑0 + 1) (by norm_num)).eq_of_src g 0
  rw [hg0, Limits.comp_zero] at hg
  refine (cancel_epi (R.cochainComplexXIso (-↑0) 0 (by norm_num)).hom).mp ?_
  simpa using hg.symm

/-- `extMk` vanishes on the boundary of the last step of a resolution. -/
lemma extMk_toCycles_prev_eq_zero (R : ProjectiveResolution X) (n : ℕ) (hn : 0 < n)
    (x : (R.complex.linearYonedaObj k Y).X ((ComplexShape.up ℕ).prev n)) :
    R.extMk (cycHom R n ((R.complex.linearYonedaObj k Y).toCycles ((ComplexShape.up ℕ).prev n) n x))
      (n + 1) rfl (cycHom_cocycle R n _) = 0 := by
  have hp : (ComplexShape.up ℕ).prev n + 1 = n := by
    have hr : (ComplexShape.up ℕ).Rel (n - 1) n := by rw [ComplexShape.up_Rel]; omega
    have h2 := ComplexShape.prev_eq' (c := ComplexShape.up ℕ) hr
    omega
  rw [ProjectiveResolution.extMk_eq_zero_iff R
    (cycHom R n ((R.complex.linearYonedaObj k Y).toCycles ((ComplexShape.up ℕ).prev n) n x))
    (n + 1) rfl (cycHom_cocycle R n _) ((ComplexShape.up ℕ).prev n) hp]
  exact ⟨x, (cycHom_toCycles R n x hp).symm⟩

set_option maxHeartbeats 2000000 in
/-- **E0b-core.** `Extⁿ(X,Y)` is computed by the homology of `Hom(R_•, Y)`, via `extMk`. -/
theorem extHAddEquivHomology (R : ProjectiveResolution X) (n : ℕ) :
    ∃ Φ : (R.complex.linearYonedaObj k Y).homology n ≃+ Abelian.Ext.{v} X Y n,
      ∀ (f : R.complex.X n ⟶ Y) (hf : R.complex.d (n + 1) n ≫ f = 0),
        Φ ((R.complex.linearYonedaObj k Y).homologyπ n
            ((R.complex.linearYonedaObj k Y).cyclesMk f (n + 1) (by simp) (by
              change R.complex.d (n + 1) n ≫ f = 0
              exact hf))) =
          R.extMk f (n + 1) rfl hf := by
  let K := R.complex.linearYonedaObj k Y
  have hsmul (r : k) (z : K.cycles n)
      (hp : R.complex.d (n + 1) n ≫ (r • cycHom R n z) = 0) :
      r • R.extMk (cycHom R n z) (n + 1) rfl (cycHom_cocycle R n z) =
        R.extMk (r • cycHom R n z) (n + 1) rfl hp := by
    have h1 := Abelian.Ext.smul_eq_comp_mk₀
      (R.extMk (cycHom R n z) (n + 1) rfl (cycHom_cocycle R n z)) r
    have h2 := ProjectiveResolution.extMk_comp_mk₀ R (cycHom R n z) (n + 1) rfl
      (cycHom_cocycle R n z) (r • 𝟙 Y)
    have h3 : (cycHom R n z) ≫ (r • 𝟙 Y) = r • cycHom R n z :=
      (Linear.comp_smul _ _ _ (cycHom R n z) r (𝟙 Y)).trans (by rw [Category.comp_id])
    exact (h1.trans h2).trans (extMk_congr R h3 _ _)
  let Ψl : K.cycles n →ₗ[k] Abelian.Ext.{v} X Y n :=
    { toFun := fun z => R.extMk (cycHom R n z) (n + 1) rfl (cycHom_cocycle R n z)
      map_add' := fun z w => by
        have h1 : R.complex.d (n + 1) n ≫ (cycHom R n z + cycHom R n w) = 0 := by
          rw [Preadditive.comp_add, cycHom_cocycle R n z, cycHom_cocycle R n w, add_zero]
        exact (extMk_congr R (cycHom_add R n z w) (cycHom_cocycle R n (z + w)) h1).trans
          (ProjectiveResolution.add_extMk R (cycHom R n z) (cycHom R n w) (n + 1) rfl _ _).symm
      map_smul' := fun r z => by
        have h2 : R.complex.d (n + 1) n ≫ (r • cycHom R n z) = 0 :=
          (Linear.comp_smul _ _ _ _ _ _).trans (by rw [cycHom_cocycle R n z, smul_zero])
        exact (extMk_congr R (cycHom_smul R n r z) (cycHom_cocycle R n (r • z)) h2).trans
          (hsmul r z h2).symm }
  let Ψ : K.cycles n ⟶ ModuleCat.of k (Abelian.Ext.{v} X Y n) := ModuleCat.ofHom Ψl
  have hΨ : K.toCycles ((ComplexShape.up ℕ).prev n) n ≫ Ψ = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h1 : (ModuleCat.Hom.hom (K.toCycles ((ComplexShape.up ℕ).prev n) n ≫ Ψ)) x
        = Ψl (K.toCycles ((ComplexShape.up ℕ).prev n) n x) := by
      rw [ModuleCat.hom_comp]
      rfl
    rw [h1]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine (extMk_congr R (cycHom_toCycles_zero R x) (cycHom_cocycle R 0 _) (by simp)).trans ?_
      exact ProjectiveResolution.extMk_zero R 1 rfl
    · exact extMk_toCycles_prev_eq_zero R n hn x
  have hcomm : K.toCycles ((ComplexShape.up ℕ).prev n) n ≫ Ψ = 0 ≫ Ψ := by
    rw [hΨ, Limits.zero_comp]
  let Φm : K.homology n ⟶ ModuleCat.of k (Abelian.Ext.{v} X Y n) :=
    Cofork.IsColimit.desc (K.homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl) Ψ hcomm
  have hΦπ : ∀ z : K.cycles n, Φm (K.homologyπ n z) = Ψl z := by
    intro z
    have h1 := Cofork.IsColimit.π_desc' (K.homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl) Ψ hcomm
    have h2 := ConcreteCategory.congr_hom h1 z
    exact (ConcreteCategory.comp_apply (K.homologyπ n) Φm z).symm.trans h2
  have hsurj : Function.Surjective (fun x : K.homology n => Φm x) := by
    intro y
    obtain ⟨f, hf, hfy⟩ := ProjectiveResolution.extMk_surjective R y (n + 1) rfl
    have hfK : K.d n (n + 1) f = 0 := hf
    refine ⟨K.homologyπ n (K.cyclesMk f (n + 1) (by simp) hfK), ?_⟩
    exact (hΦπ (K.cyclesMk f (n + 1) (by simp) hfK)).trans
      ((extMk_congr R (cycHom_cyclesMk R n f hfK)
        (cycHom_cocycle R n (K.cyclesMk f (n + 1) (by simp) hfK)) hf).trans hfy)
  have hker : ∀ z : K.cycles n, Ψl z = 0 → K.homologyπ n z = 0 := by
    intro z hz
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hf0 : cycHom R 0 z = 0 :=
        extMk_deg_zero_eq_zero R (cycHom R 0 z) (cycHom_cocycle R 0 z) hz
      have hz0 : z = 0 := by
        apply (ModuleCat.mono_iff_injective (K.iCycles 0)).1 inferInstance
        show K.iCycles 0 z = K.iCycles 0 (0 : K.cycles 0)
        exact (iCycles_eq_cycHom R 0 z).trans
          (hf0.trans (map_zero (ModuleCat.Hom.hom (K.iCycles 0))).symm)
      rw [hz0, map_zero]
    · have hp : (ComplexShape.up ℕ).prev n + 1 = n := by
        have hr : (ComplexShape.up ℕ).Rel (n - 1) n := by rw [ComplexShape.up_Rel]; omega
        have h2 := ComplexShape.prev_eq' (c := ComplexShape.up ℕ) hr
        omega
      obtain ⟨g, hg⟩ := (ProjectiveResolution.extMk_eq_zero_iff R (cycHom R n z) (n + 1) rfl
          (cycHom_cocycle R n z) ((ComplexShape.up ℕ).prev n) hp).1 hz
      have hzi : z = K.toCycles ((ComplexShape.up ℕ).prev n) n g := by
        apply (ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance
        show K.iCycles n z = K.iCycles n (K.toCycles ((ComplexShape.up ℕ).prev n) n g)
        have h4 : K.iCycles n (K.toCycles ((ComplexShape.up ℕ).prev n) n g)
            = K.d ((ComplexShape.up ℕ).prev n) n g :=
          (ConcreteCategory.comp_apply (K.toCycles ((ComplexShape.up ℕ).prev n) n) (K.iCycles n) g).symm.trans
            (ConcreteCategory.congr_hom (K.toCycles_i ((ComplexShape.up ℕ).prev n) n) g)
        have h5 : K.d ((ComplexShape.up ℕ).prev n) n g
            = R.complex.d n ((ComplexShape.up ℕ).prev n) ≫ g :=
          linearYonedaObj_d_apply R.complex Y hp g
        rw [h4, h5]
        exact (iCycles_eq_cycHom R n z).trans hg.symm
      rw [hzi]
      refine ((ConcreteCategory.comp_apply (K.toCycles ((ComplexShape.up ℕ).prev n) n)
        (K.homologyπ n) g).symm).trans ?_
      rw [K.toCycles_comp_homologyπ]
      exact LinearMap.zero_apply g
  have hinj : Function.Injective (fun x : K.homology n => Φm x) := by
    intro x y hxy
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance x
    obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance y
    simp only [] at hxy
    rw [hΦπ z, hΦπ w] at hxy
    have hzw : Ψl (z - w) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 := hker (z - w) hzw
    simpa only [map_sub, sub_eq_zero] using h0
  exact ⟨AddEquiv.ofBijective (ModuleCat.Hom.hom Φm) ⟨hinj, hsurj⟩, by
    intro f hf
    have hfK : K.d n (n + 1) f = 0 := hf
    exact (hΦπ (K.cyclesMk f (n + 1) (by simp) hfK)).trans
      ((extMk_congr R (cycHom_cyclesMk R n f hfK)
        (cycHom_cocycle R n (K.cyclesMk f (n + 1) (by simp) hfK)) hf).trans rfl)⟩

end

end Work.SSGRoute.E0bCore
