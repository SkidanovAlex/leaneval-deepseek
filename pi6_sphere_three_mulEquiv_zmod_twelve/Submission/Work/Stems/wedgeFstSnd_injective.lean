import Mathlib
import Submission.Work.Stems.WedgeFstSndAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The folds separate the two summands of `Hₙ(Sⁿ ∨ Sⁿ)`

This file proves `Work.Stems.wedgeFstSnd_injective`: the pair of folds
`(wedgeFst, wedgeSnd) : Sⁿ ∨ Sⁿ → Sⁿ × Sⁿ` induces an *injective* map
`Hₙ(Sⁿ ∨ Sⁿ) → Hₙ(Sⁿ) ⊕ Hₙ(Sⁿ)`.

The wedge `W = Sⁿ ∨ Sⁿ` is covered by the two open pieces
`U = {z | z₁ ≠ q}` and `V = {z | z₂ ≠ q}` (`WedgeFstSndAux.lean`), whose intersection is
contractible (`wfsUV_contractible`).  The Mayer–Vietoris map
`wfsMV : Hₙ(U) ⊞ Hₙ(V) → Hₙ(W)` is therefore an isomorphism.  On `U` the *second* projection
`wfsUsnd` is a homotopy equivalence (`wfsUsnd_homotopic`, with the section `sec_U(z) = (b, z₂)`),
while the *first* projection `wfsUfst` is nullhomotopic because its image lies in the punctured
sphere (`wfsUfst_nullhomotopic`); the two roles are swapped on `V`.  Hence the composite of `wfsMV`
with the pair of folds is injective (`wfsMV_injective`), and since `wfsMV` is surjective the pair of
folds itself is injective.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

/-! ## Functoriality of `hm` (local copies, named to avoid clashes) -/

theorem wfs_hm_comp (n : ℕ) {A B D : Type} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace D] (f : C(B, D)) (g : C(A, B)) :
    hm (f.comp g) n = (hm f n).comp (hm g n) := by
  have h1 : Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of D) (TopCat.ofHom (f.comp g))
      = Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) (TopCat.ofHom g)
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of B) (TopCat.of D) (TopCat.ofHom f) := by
    simp only [Work.Cohomology.chainMap]
    rw [TopCat.ofHom_comp g f, CategoryTheory.Functor.map_comp]
  simp only [hm, h1, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]

theorem wfs_hm_congr (n : ℕ) {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(A, B)} (h : ContinuousMap.Homotopic f g) : hm f n = hm g n := by
  have hh : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) := h.some
  have hcongr := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor hh
    (ModuleCat.of ℤ ℤ) n
  simp only [hm]
  rw [hcongr]

theorem wfs_hm_id (n : ℕ) {A : Type} [TopologicalSpace A] :
    hm (ContinuousMap.id A) n = LinearMap.id := by
  have h1 : Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of A)
        (TopCat.ofHom (ContinuousMap.id A)) = 𝟙 _ := by
    rw [TopCat.ofHom_id, Work.Cohomology.chainMap, CategoryTheory.Functor.map_id]
  simp only [hm, h1, HomologicalComplex.homologyMap_id, ModuleCat.hom_id]

/-- A constant map induces the zero map on positive-degree homology (general codomain). -/
theorem wfs_hm_const' (n : ℕ) {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (b : B)
    (hn : 1 ≤ n) : hm (ContinuousMap.const A b) n = 0 := by
  have h1 : ContinuousMap.const A b
      = (ContinuousMap.const PUnit b).comp (ContinuousMap.const A PUnit.unit) := by
    ext x; rfl
  rw [h1, wfs_hm_comp]
  have hz0 : CategoryTheory.Limits.IsZero ((chains (TopCat.of PUnit)).homology n) :=
    Work.Cohomology.homologyContractible n hn
  have hz : HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of PUnit)
        (TopCat.ofHom (ContinuousMap.const A PUnit.unit))) n = 0 :=
    hz0.eq_zero_of_tgt _
  simp only [hm, hz, ModuleCat.hom_zero, LinearMap.comp_zero]

/-! ## The punctured sphere and the corestrictions -/

/-- The inclusion of the punctured sphere `Sⁿ ∖ {q}` in `Sⁿ`. -/
def wfsPunctIncl (n : ℕ) (hn : 1 ≤ n) : C(punctSph n hn, sphere n) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The corestriction of the first fold on `U` to the punctured sphere. -/
def wfsUcore (n : ℕ) (hn : 1 ≤ n) : C(↥(wfsU n hn), punctSph n hn) :=
  ⟨fun z => ⟨z.1.1.1, z.2⟩, by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (continuous_subtype_val)).fst⟩

/-- The corestriction of the second fold on `V` to the punctured sphere. -/
def wfsVcore (n : ℕ) (hn : 1 ≤ n) : C(↥(wfsV n hn), punctSph n hn) :=
  ⟨fun z => ⟨z.1.1.2, z.2⟩, by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (continuous_subtype_val)).snd⟩

theorem wfsUfst_eq_core (n : ℕ) (hn : 1 ≤ n) :
    wfsUfst n hn = (wfsPunctIncl n hn).comp (wfsUcore n hn) := by
  ext z; rfl

theorem wfsVsnd_eq_core (n : ℕ) (hn : 1 ≤ n) :
    wfsVsnd n hn = (wfsPunctIncl n hn).comp (wfsVcore n hn) := by
  ext z; rfl

theorem wfsUfst_nullhomotopic (n : ℕ) (hn : 1 ≤ n) : (wfsUfst n hn).Nullhomotopic := by
  rw [wfsUfst_eq_core]
  have hcore : (wfsUcore n hn).Nullhomotopic := by
    have hc : (ContinuousMap.id (punctSph n hn)).Nullhomotopic := id_nullhomotopic _
    have h2 := hc.comp_left (wfsUcore n hn)
    simpa only [ContinuousMap.id_comp] using h2
  exact hcore.comp_right (wfsPunctIncl n hn)

theorem wfsVsnd_nullhomotopic (n : ℕ) (hn : 1 ≤ n) : (wfsVsnd n hn).Nullhomotopic := by
  rw [wfsVsnd_eq_core]
  have hcore : (wfsVcore n hn).Nullhomotopic := by
    have hc : (ContinuousMap.id (punctSph n hn)).Nullhomotopic := id_nullhomotopic _
    have h2 := hc.comp_left (wfsVcore n hn)
    simpa only [ContinuousMap.id_comp] using h2
  exact hcore.comp_right (wfsPunctIncl n hn)

theorem wfs_hm_wfsUfst_eq_zero (n : ℕ) (hn : 1 ≤ n) : hm (wfsUfst n hn) n = 0 := by
  obtain ⟨c, hc⟩ := wfsUfst_nullhomotopic n hn
  have h1 : hm (wfsUfst n hn) n = hm (ContinuousMap.const (↥(wfsU n hn)) c) n :=
    wfs_hm_congr n hc
  have h2 : hm (ContinuousMap.const (↥(wfsU n hn)) c) n = 0 :=
    wfs_hm_const' (A := ↥(wfsU n hn)) n c hn
  exact h1.trans h2

theorem wfs_hm_wfsVsnd_eq_zero (n : ℕ) (hn : 1 ≤ n) : hm (wfsVsnd n hn) n = 0 := by
  obtain ⟨c, hc⟩ := wfsVsnd_nullhomotopic n hn
  have h1 : hm (wfsVsnd n hn) n = hm (ContinuousMap.const (↥(wfsV n hn)) c) n :=
    wfs_hm_congr n hc
  have h2 : hm (ContinuousMap.const (↥(wfsV n hn)) c) n = 0 :=
    wfs_hm_const' (A := ↥(wfsV n hn)) n c hn
  exact h1.trans h2

end

end Work.Stems

namespace Work.Stems

noncomputable section

/-! ## The homotopy `sec_U ∘ snd_U ≃ id_U` -/

/-- The homotopy from the identity of `U` to `sec_U ∘ snd_U`: move the first coordinate along the
contraction of the punctured sphere. -/
noncomputable def wfsUhom (n : ℕ) (hn : 1 ≤ n) : C(I × ↥(wfsU n hn), ↥(wfsU n hn)) :=
  ⟨fun p =>
    ⟨⟨((punctContraction n hn (p.1, ⟨p.2.1.1.1, p.2.2⟩)), p.2.1.1.2), by
        rcases p.2.1.2 with hb | hb
        · refine Or.inl ?_
          have h : (⟨p.2.1.1.1, p.2.2⟩ : punctSph n hn) = punctBase n hn := Subtype.ext hb
          rw [h, punctContraction_apply_base]
          rfl
        · exact Or.inr hb⟩,
      (punctContraction n hn (p.1, ⟨p.2.1.1.1, p.2.2⟩)).2⟩, by
      have hval : Continuous (fun p : I × ↥(wfsU n hn) =>
          (((punctContraction n hn (p.1, ⟨p.2.1.1.1, p.2.2⟩)) : punctSph n hn) : sphere n)) :=
        ((punctContraction n hn).continuous.comp
          (Continuous.prodMk continuous_fst (Continuous.subtype_mk
            ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).fst)
            (fun p => p.2.2)))).subtype_val
      have hsnd : Continuous (fun p : I × ↥(wfsU n hn) => p.2.1.1.2) :=
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).snd
      exact Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk hval hsnd)
          (fun p => by
            rcases p.2.1.2 with hb | hb
            · refine Or.inl ?_
              have h : (⟨p.2.1.1.1, p.2.2⟩ : punctSph n hn) = punctBase n hn := Subtype.ext hb
              rw [h, punctContraction_apply_base]
              rfl
            · exact Or.inr hb))
          (fun p => (punctContraction n hn (p.1, ⟨p.2.1.1.1, p.2.2⟩)).2)⟩

theorem wfsUhom_zero (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsU n hn)) :
    wfsUhom n hn (0, z) = ContinuousMap.id ↥(wfsU n hn) z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · show (((punctContraction n hn (0, (⟨z.1.1.1, z.2⟩ : punctSph n hn))) : punctSph n hn) : sphere n) = z.1.1.1
    rw [punctContraction_apply_zero]
  · rfl

theorem wfsUhom_one (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsU n hn)) :
    wfsUhom n hn (1, z) = ((wfsUsec n hn).comp (wfsUsnd n hn)) z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · show (((punctContraction n hn (1, (⟨z.1.1.1, z.2⟩ : punctSph n hn))) : punctSph n hn) : sphere n) = sphBase n hn
    rw [punctContraction_apply_one]
    rfl
  · rfl

theorem wfsUsnd_homotopic (n : ℕ) (hn : 1 ≤ n) :
    ContinuousMap.Homotopic ((wfsUsec n hn).comp (wfsUsnd n hn))
      (ContinuousMap.id ↥(wfsU n hn)) :=
  (show ContinuousMap.Homotopic (ContinuousMap.id ↥(wfsU n hn))
      ((wfsUsec n hn).comp (wfsUsnd n hn)) from
    ⟨⟨wfsUhom n hn, wfsUhom_zero n hn, wfsUhom_one n hn⟩⟩).symm

/-! ## The homotopy `sec_V ∘ fst_V ≃ id_V` -/

/-- The homotopy from the identity of `V` to `sec_V ∘ fst_V`. -/
noncomputable def wfsVhom (n : ℕ) (hn : 1 ≤ n) : C(I × ↥(wfsV n hn), ↥(wfsV n hn)) :=
  ⟨fun p =>
    ⟨⟨(p.2.1.1.1, (punctContraction n hn (p.1, ⟨p.2.1.1.2, p.2.2⟩))), by
        rcases p.2.1.2 with hb | hb
        · exact Or.inl hb
        · refine Or.inr ?_
          have h : (⟨p.2.1.1.2, p.2.2⟩ : punctSph n hn) = punctBase n hn := Subtype.ext hb
          rw [h, punctContraction_apply_base]
          rfl⟩,
      (punctContraction n hn (p.1, ⟨p.2.1.1.2, p.2.2⟩)).2⟩, by
      have hval : Continuous (fun p : I × ↥(wfsV n hn) =>
          (((punctContraction n hn (p.1, ⟨p.2.1.1.2, p.2.2⟩)) : punctSph n hn) : sphere n)) :=
        ((punctContraction n hn).continuous.comp
          (Continuous.prodMk continuous_fst (Continuous.subtype_mk
            ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).snd)
            (fun p => p.2.2)))).subtype_val
      have hfst : Continuous (fun p : I × ↥(wfsV n hn) => p.2.1.1.1) :=
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).fst
      exact Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk hfst hval)
          (fun p => by
            rcases p.2.1.2 with hb | hb
            · exact Or.inl hb
            · refine Or.inr ?_
              have h : (⟨p.2.1.1.2, p.2.2⟩ : punctSph n hn) = punctBase n hn := Subtype.ext hb
              rw [h, punctContraction_apply_base]
              rfl))
          (fun p => (punctContraction n hn (p.1, ⟨p.2.1.1.2, p.2.2⟩)).2)⟩

theorem wfsVhom_zero (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsV n hn)) :
    wfsVhom n hn (0, z) = ContinuousMap.id ↥(wfsV n hn) z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show (((punctContraction n hn (0, (⟨z.1.1.2, z.2⟩ : punctSph n hn))) : punctSph n hn) : sphere n) = z.1.1.2
    rw [punctContraction_apply_zero]

theorem wfsVhom_one (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsV n hn)) :
    wfsVhom n hn (1, z) = ((wfsVsec n hn).comp (wfsVfst n hn)) z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show (((punctContraction n hn (1, (⟨z.1.1.2, z.2⟩ : punctSph n hn))) : punctSph n hn) : sphere n) = sphBase n hn
    rw [punctContraction_apply_one]
    rfl

theorem wfsVfst_homotopic (n : ℕ) (hn : 1 ≤ n) :
    ContinuousMap.Homotopic ((wfsVsec n hn).comp (wfsVfst n hn))
      (ContinuousMap.id ↥(wfsV n hn)) :=
  (show ContinuousMap.Homotopic (ContinuousMap.id ↥(wfsV n hn))
      ((wfsVsec n hn).comp (wfsVfst n hn)) from
    ⟨⟨wfsVhom n hn, wfsVhom_zero n hn, wfsVhom_one n hn⟩⟩).symm

/-! ## Injectivity of `snd_U` and `fst_V` on homology -/

theorem wfs_hm_wfsUsnd_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (hm (wfsUsnd n hn) n) := by
  have hcomp : hm ((wfsUsec n hn).comp (wfsUsnd n hn)) n = LinearMap.id := by
    rw [wfs_hm_congr n (wfsUsnd_homotopic n hn), wfs_hm_id]
  have h1 : hm ((wfsUsec n hn).comp (wfsUsnd n hn)) n
      = (hm (wfsUsec n hn) n).comp (hm (wfsUsnd n hn) n) := wfs_hm_comp n _ _
  rw [h1] at hcomp
  have hfix : ∀ x, hm (wfsUsec n hn) n (hm (wfsUsnd n hn) n x) = x := by
    intro x
    have h2 := congrArg (fun (g : _ →ₗ[_] _) => g x) hcomp
    simpa [LinearMap.comp_apply] using h2
  intro x y hxy
  exact (hfix x).symm.trans
    (((congrArg (fun z => hm (wfsUsec n hn) n z) hxy).trans (hfix y)))

theorem wfs_hm_wfsVfst_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (hm (wfsVfst n hn) n) := by
  have hcomp : hm ((wfsVsec n hn).comp (wfsVfst n hn)) n = LinearMap.id := by
    rw [wfs_hm_congr n (wfsVfst_homotopic n hn), wfs_hm_id]
  have h1 : hm ((wfsVsec n hn).comp (wfsVfst n hn)) n
      = (hm (wfsVsec n hn) n).comp (hm (wfsVfst n hn) n) := wfs_hm_comp n _ _
  rw [h1] at hcomp
  have hfix : ∀ x, hm (wfsVsec n hn) n (hm (wfsVfst n hn) n x) = x := by
    intro x
    have h2 := congrArg (fun (g : _ →ₗ[_] _) => g x) hcomp
    simpa [LinearMap.comp_apply] using h2
  intro x y hxy
  exact (hfix x).symm.trans
    (((congrArg (fun z => hm (wfsVsec n hn) n z) hxy).trans (hfix y)))

end

end Work.Stems

namespace Work.Stems

noncomputable section

open CategoryTheory.Limits

/-- The base point of `U ∩ V`. -/
def wfsUVbase (n : ℕ) (hn : 1 ≤ n) : ↥(wfsU n hn ∩ wfsV n hn) :=
  Subtype.mk (wedgeBase (sphBase n hn) : ↥(wfsW n hn))
    (And.intro (show ((wedgeBase (sphBase n hn) : ↥(wfsW n hn)) : sphere n × sphere n).1 ≠ sphOther n hn
        from (sphOther_ne_sphBase n hn).symm)
      (show ((wedgeBase (sphBase n hn) : ↥(wfsW n hn)) : sphere n × sphere n).2 ≠ sphOther n hn
        from (sphOther_ne_sphBase n hn).symm))

/-- The contraction of `U ∩ V` to the base point, moving both coordinates along the contraction of
the punctured sphere. -/
noncomputable def wfsUVhom (n : ℕ) (hn : 1 ≤ n) :
    C(I × ↥(wfsU n hn ∩ wfsV n hn), ↥(wfsU n hn ∩ wfsV n hn)) :=
  ⟨fun p =>
    ⟨⟨((((punctContraction n hn (p.1, ⟨p.2.1.1.1, p.2.2.1⟩)) : punctSph n hn) : sphere n),
        (((punctContraction n hn (p.1, ⟨p.2.1.1.2, p.2.2.2⟩)) : punctSph n hn) : sphere n)), by
          rcases p.2.1.2 with hb | hb
          · refine Or.inl ?_
            have h : (⟨p.2.1.1.1, p.2.2.1⟩ : punctSph n hn) = punctBase n hn := Subtype.ext hb
            rw [h, punctContraction_apply_base]; rfl
          · refine Or.inr ?_
            have h : (⟨p.2.1.1.2, p.2.2.2⟩ : punctSph n hn) = punctBase n hn := Subtype.ext hb
            rw [h, punctContraction_apply_base]; rfl⟩,
      ⟨(punctContraction n hn (p.1, ⟨p.2.1.1.1, p.2.2.1⟩)).2,
       (punctContraction n hn (p.1, ⟨p.2.1.1.2, p.2.2.2⟩)).2⟩⟩, by
      have hchain : Continuous (fun p : I × ↥(wfsU n hn ∩ wfsV n hn) =>
          (p.2.1.1 : sphere n × sphere n)) :=
        continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
      have hc1 : Continuous (fun p : I × ↥(wfsU n hn ∩ wfsV n hn) =>
          (((punctContraction n hn (p.1, ⟨p.2.1.1.1, p.2.2.1⟩)) : punctSph n hn) : sphere n)) :=
        ((punctContraction n hn).continuous.comp (Continuous.prodMk continuous_fst
          (Continuous.subtype_mk hchain.fst (fun p => p.2.2.1)))).subtype_val
      have hc2 : Continuous (fun p : I × ↥(wfsU n hn ∩ wfsV n hn) =>
          (((punctContraction n hn (p.1, ⟨p.2.1.1.2, p.2.2.2⟩)) : punctSph n hn) : sphere n)) :=
        ((punctContraction n hn).continuous.comp (Continuous.prodMk continuous_fst
          (Continuous.subtype_mk hchain.snd (fun p => p.2.2.2)))).subtype_val
      exact Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk hc1 hc2)
          (fun p => by
            rcases p.2.1.2 with hb | hb
            · refine Or.inl ?_
              have h : (⟨p.2.1.1.1, p.2.2.1⟩ : punctSph n hn) = punctBase n hn := Subtype.ext hb
              rw [h, punctContraction_apply_base]; rfl
            · refine Or.inr ?_
              have h : (⟨p.2.1.1.2, p.2.2.2⟩ : punctSph n hn) = punctBase n hn := Subtype.ext hb
              rw [h, punctContraction_apply_base]; rfl))
          (fun p => ⟨(punctContraction n hn (p.1, ⟨p.2.1.1.1, p.2.2.1⟩)).2,
            (punctContraction n hn (p.1, ⟨p.2.1.1.2, p.2.2.2⟩)).2⟩)⟩

theorem wfsUVhom_zero (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsU n hn ∩ wfsV n hn)) :
    wfsUVhom n hn (0, z) = ContinuousMap.id ↥(wfsU n hn ∩ wfsV n hn) z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · show (((punctContraction n hn (0, (⟨z.1.1.1, z.2.1⟩ : punctSph n hn))) : punctSph n hn) : sphere n)
      = z.1.1.1
    rw [punctContraction_apply_zero]
  · show (((punctContraction n hn (0, (⟨z.1.1.2, z.2.2⟩ : punctSph n hn))) : punctSph n hn) : sphere n)
      = z.1.1.2
    rw [punctContraction_apply_zero]

theorem wfsUVhom_one (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsU n hn ∩ wfsV n hn)) :
    wfsUVhom n hn (1, z) = wfsUVbase n hn := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · show (((punctContraction n hn (1, (⟨z.1.1.1, z.2.1⟩ : punctSph n hn))) : punctSph n hn) : sphere n)
      = sphBase n hn
    rw [punctContraction_apply_one]
    rfl
  · show (((punctContraction n hn (1, (⟨z.1.1.2, z.2.2⟩ : punctSph n hn))) : punctSph n hn) : sphere n)
      = sphBase n hn
    rw [punctContraction_apply_one]
    rfl

theorem wfsUV_contractible (n : ℕ) (hn : 1 ≤ n) :
    ContractibleSpace ↥(wfsU n hn ∩ wfsV n hn) := by
  refine (contractible_iff_id_nullhomotopic _).mpr ⟨wfsUVbase n hn, ?_⟩
  refine ⟨⟨wfsUVhom n hn, fun z => wfsUVhom_zero n hn z, fun z => ?_⟩⟩
  exact wfsUVhom_one n hn z

/-- The singular chain complex of `U`. -/
abbrev wfsChU (n : ℕ) (hn : 1 ≤ n) : ChainComplex (ModuleCat ℤ) ℕ :=
  Work.Cohomology.singularChains ℤ (TopCat.of ↥(wfsU n hn))

/-- The singular chain complex of `V`. -/
abbrev wfsChV (n : ℕ) (hn : 1 ≤ n) : ChainComplex (ModuleCat ℤ) ℕ :=
  Work.Cohomology.singularChains ℤ (TopCat.of ↥(wfsV n hn))

/-- The Mayer–Vietoris map `Hₙ(U) ⊞ Hₙ(V) → Hₙ(Sⁿ ∨ Sⁿ)`. -/
abbrev wfsMV (n : ℕ) (hn : 1 ≤ n) :
    Work.Cohomology.HBiprod (wfsU n hn) (wfsV n hn) n ⟶ (chains (wfsW n hn)).homology n :=
  Work.Cohomology.mvRightX (wfsU n hn) (wfsV n hn) (isOpen_wfsU n hn) (isOpen_wfsV n hn)
    (wfsU_union_wfsV n hn) n

theorem wfsMV_isIso (n : ℕ) (hn : 1 ≤ n) : IsIso (wfsMV n hn) := by
  haveI : ContractibleSpace ↥(wfsU n hn ∩ wfsV n hn) := wfsUV_contractible n hn
  exact Work.Cohomology.isIso_mvRightX_of_contractible (wfsU n hn) (wfsV n hn) (isOpen_wfsU n hn)
    (isOpen_wfsV n hn) (wfsU_union_wfsV n hn) n hn

theorem wfs_total (n : ℕ) (hn : 1 ≤ n) (w : Work.Cohomology.HBiprod (wfsU n hn) (wfsV n hn) n) :
    (HomologicalComplex.homologyMap (biprod.inl (X := wfsChU n hn) (Y := wfsChV n hn)) n)
        ((HomologicalComplex.homologyMap (biprod.fst (X := wfsChU n hn) (Y := wfsChV n hn)) n) w)
      + (HomologicalComplex.homologyMap (biprod.inr (X := wfsChU n hn) (Y := wfsChV n hn)) n)
        ((HomologicalComplex.homologyMap (biprod.snd (X := wfsChU n hn) (Y := wfsChV n hn)) n) w) = w := by
  have h := congrArg (fun (g : (wfsChU n hn ⊞ wfsChV n hn).homology n
      ⟶ (wfsChU n hn ⊞ wfsChV n hn).homology n) => g w)
    (Work.Cohomology.homologyMap_total' (wfsChU n hn) (wfsChV n hn) n)
  simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] using h

theorem wfsMV_inl_apply (n : ℕ) (hn : 1 ≤ n) (y : (wfsChU n hn).homology n) :
    wfsMV n hn
        ((HomologicalComplex.homologyMap (biprod.inl (X := wfsChU n hn) (Y := wfsChV n hn)) n) y)
      = hm (wfsUIncl n hn) n y := by
  rw [wfsMV, Work.Cohomology.mvRightX, ConcreteCategory.comp_apply]
  have h1 : (HomologicalComplex.homologyMap
        (Work.Cohomology.mvRight (wfsU n hn) (wfsV n hn)) n)
      ((HomologicalComplex.homologyMap (biprod.inl (X := wfsChU n hn) (Y := wfsChV n hn)) n) y)
      = (HomologicalComplex.homologyMap
          (Work.Cohomology.smallOfU (wfsU n hn) (wfsV n hn)) n) y := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
      show biprod.inl (X := wfsChU n hn) (Y := wfsChV n hn) ≫ Work.Cohomology.mvRight (wfsU n hn) (wfsV n hn)
        = Work.Cohomology.smallOfU (wfsU n hn) (wfsV n hn) from by
          rw [Work.Cohomology.mvRight, biprod.inl_desc]]
  rw [h1]
  rw [show (Work.Cohomology.smallIso (wfsU n hn) (wfsV n hn) (isOpen_wfsU n hn)
      (isOpen_wfsV n hn) (wfsU_union_wfsV n hn) n).hom
      = HomologicalComplex.homologyMap
          (Work.Cohomology.smallToSing (wfsU n hn) (wfsV n hn)) n from rfl]
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
    Work.Cohomology.smallOfU_comp_smallToSing]
  rfl

theorem wfsMV_inr_apply (n : ℕ) (hn : 1 ≤ n) (y : (wfsChV n hn).homology n) :
    wfsMV n hn
        ((HomologicalComplex.homologyMap (biprod.inr (X := wfsChU n hn) (Y := wfsChV n hn)) n) y)
      = - hm (wfsVIncl n hn) n y := by
  rw [wfsMV, Work.Cohomology.mvRightX, ConcreteCategory.comp_apply]
  have h1 : (HomologicalComplex.homologyMap
        (Work.Cohomology.mvRight (wfsU n hn) (wfsV n hn)) n)
      ((HomologicalComplex.homologyMap (biprod.inr (X := wfsChU n hn) (Y := wfsChV n hn)) n) y)
      = - ((HomologicalComplex.homologyMap
          (Work.Cohomology.smallOfV (wfsU n hn) (wfsV n hn)) n) y) := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
      show biprod.inr (X := wfsChU n hn) (Y := wfsChV n hn) ≫ Work.Cohomology.mvRight (wfsU n hn) (wfsV n hn)
        = -(Work.Cohomology.smallOfV (wfsU n hn) (wfsV n hn)) from by
          rw [Work.Cohomology.mvRight, biprod.inr_desc]]
    rw [HomologicalComplex.homologyMap_neg]
    rfl
  rw [h1]
  rw [show (Work.Cohomology.smallIso (wfsU n hn) (wfsV n hn) (isOpen_wfsU n hn)
      (isOpen_wfsV n hn) (wfsU_union_wfsV n hn) n).hom
      (- ((HomologicalComplex.homologyMap
          (Work.Cohomology.smallOfV (wfsU n hn) (wfsV n hn)) n) y))
      = - ((Work.Cohomology.smallIso (wfsU n hn) (wfsV n hn) (isOpen_wfsU n hn)
          (isOpen_wfsV n hn) (wfsU_union_wfsV n hn) n).hom
          ((HomologicalComplex.homologyMap
            (Work.Cohomology.smallOfV (wfsU n hn) (wfsV n hn)) n) y)) from by simp]
  rw [neg_inj]
  rw [show (Work.Cohomology.smallIso (wfsU n hn) (wfsV n hn) (isOpen_wfsU n hn)
      (isOpen_wfsV n hn) (wfsU_union_wfsV n hn) n).hom
      = HomologicalComplex.homologyMap
          (Work.Cohomology.smallToSing (wfsU n hn) (wfsV n hn)) n from rfl]
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
    Work.Cohomology.smallOfV_comp_smallToSing]
  rfl

theorem wfsMV_apply (n : ℕ) (hn : 1 ≤ n) (w : Work.Cohomology.HBiprod (wfsU n hn) (wfsV n hn) n) :
    wfsMV n hn w
      = hm (wfsUIncl n hn) n
            ((HomologicalComplex.homologyMap (biprod.fst (X := wfsChU n hn) (Y := wfsChV n hn)) n) w)
        - hm (wfsVIncl n hn) n
            ((HomologicalComplex.homologyMap (biprod.snd (X := wfsChU n hn) (Y := wfsChV n hn)) n) w) := by
  conv_lhs => rw [← wfs_total n hn w]
  rw [map_add, wfsMV_inl_apply, wfsMV_inr_apply, sub_eq_add_neg]

theorem wfs_hm_fst_mv (n : ℕ) (hn : 1 ≤ n)
    (w : Work.Cohomology.HBiprod (wfsU n hn) (wfsV n hn) n) :
    hm (wedgeFst (sphBase n hn)) n (wfsMV n hn w)
      = - hm (wfsVfst n hn) n
          ((HomologicalComplex.homologyMap (biprod.snd (X := wfsChU n hn) (Y := wfsChV n hn)) n) w) := by
  rw [wfsMV_apply n hn w, map_sub]
  have h1 : hm (wedgeFst (sphBase n hn)) n
      (hm (wfsUIncl n hn) n
        ((HomologicalComplex.homologyMap (biprod.fst (X := wfsChU n hn) (Y := wfsChV n hn)) n) w)) = 0 := by
    rw [← LinearMap.comp_apply, ← wfs_hm_comp,
      show (wedgeFst (sphBase n hn)).comp (wfsUIncl n hn) = wfsUfst n hn from rfl,
      wfs_hm_wfsUfst_eq_zero, LinearMap.zero_apply]
  have h2 : hm (wedgeFst (sphBase n hn)) n
      (hm (wfsVIncl n hn) n
        ((HomologicalComplex.homologyMap (biprod.snd (X := wfsChU n hn) (Y := wfsChV n hn)) n) w))
      = hm (wfsVfst n hn) n
        ((HomologicalComplex.homologyMap (biprod.snd (X := wfsChU n hn) (Y := wfsChV n hn)) n) w) := by
    rw [← LinearMap.comp_apply, ← wfs_hm_comp,
      show (wedgeFst (sphBase n hn)).comp (wfsVIncl n hn) = wfsVfst n hn from rfl]
  rw [h1, h2, zero_sub]

theorem wfs_hm_snd_mv (n : ℕ) (hn : 1 ≤ n)
    (w : Work.Cohomology.HBiprod (wfsU n hn) (wfsV n hn) n) :
    hm (wedgeSnd (sphBase n hn)) n (wfsMV n hn w)
      = hm (wfsUsnd n hn) n
          ((HomologicalComplex.homologyMap (biprod.fst (X := wfsChU n hn) (Y := wfsChV n hn)) n) w) := by
  rw [wfsMV_apply n hn w, map_sub]
  have h1 : hm (wedgeSnd (sphBase n hn)) n
      (hm (wfsUIncl n hn) n
        ((HomologicalComplex.homologyMap (biprod.fst (X := wfsChU n hn) (Y := wfsChV n hn)) n) w))
      = hm (wfsUsnd n hn) n
        ((HomologicalComplex.homologyMap (biprod.fst (X := wfsChU n hn) (Y := wfsChV n hn)) n) w) := by
    rw [← LinearMap.comp_apply, ← wfs_hm_comp,
      show (wedgeSnd (sphBase n hn)).comp (wfsUIncl n hn) = wfsUsnd n hn from rfl]
  have h2 : hm (wedgeSnd (sphBase n hn)) n
      (hm (wfsVIncl n hn) n
        ((HomologicalComplex.homologyMap (biprod.snd (X := wfsChU n hn) (Y := wfsChV n hn)) n) w)) = 0 := by
    rw [← LinearMap.comp_apply, ← wfs_hm_comp,
      show (wedgeSnd (sphBase n hn)).comp (wfsVIncl n hn) = wfsVsnd n hn from rfl,
      wfs_hm_wfsVsnd_eq_zero, LinearMap.zero_apply]
  rw [h1, h2, sub_zero]

theorem wfsMV_injective (n : ℕ) (hn : 1 ≤ n)
    (w : Work.Cohomology.HBiprod (wfsU n hn) (wfsV n hn) n)
    (h1 : hm (wedgeFst (sphBase n hn)) n (wfsMV n hn w) = 0)
    (h2 : hm (wedgeSnd (sphBase n hn)) n (wfsMV n hn w) = 0) : w = 0 := by
  have hb : (HomologicalComplex.homologyMap (biprod.snd (X := wfsChU n hn) (Y := wfsChV n hn)) n) w = 0 := by
    have hz : hm (wfsVfst n hn) n
        ((HomologicalComplex.homologyMap (biprod.snd (X := wfsChU n hn) (Y := wfsChV n hn)) n) w) = 0 := by
      have hh := wfs_hm_fst_mv n hn w
      rw [h1] at hh
      exact neg_eq_zero.mp hh.symm
    exact wfs_hm_wfsVfst_injective n hn (by rw [hz, map_zero])
  have ha : (HomologicalComplex.homologyMap (biprod.fst (X := wfsChU n hn) (Y := wfsChV n hn)) n) w = 0 := by
    have hz : hm (wfsUsnd n hn) n
        ((HomologicalComplex.homologyMap (biprod.fst (X := wfsChU n hn) (Y := wfsChV n hn)) n) w) = 0 := by
      have hh := wfs_hm_snd_mv n hn w
      rw [h2] at hh
      exact hh.symm
    exact wfs_hm_wfsUsnd_injective n hn (by rw [hz, map_zero])
  rw [← wfs_total n hn w, ha, hb, map_zero, map_zero, add_zero]

theorem wedgeFstSnd_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (fun x : (chains (TopCat.of (wedgeSet (sphBase n hn)))).homology n =>
      (hm (wedgeFst (sphBase n hn)) n x, hm (wedgeSnd (sphBase n hn)) n x)) := by
  haveI hiso : IsIso (wfsMV n hn) := wfsMV_isIso n hn
  have hsurj : Function.Surjective (wfsMV n hn).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  intro x y hxy
  have h1 : hm (wedgeFst (sphBase n hn)) n x = hm (wedgeFst (sphBase n hn)) n y :=
    congrArg Prod.fst hxy
  have h2 : hm (wedgeSnd (sphBase n hn)) n x = hm (wedgeSnd (sphBase n hn)) n y :=
    congrArg Prod.snd hxy
  have hpair : hm (wedgeFst (sphBase n hn)) n (x - y) = 0 ∧
      hm (wedgeSnd (sphBase n hn)) n (x - y) = 0 := by
    rw [map_sub, map_sub, h1, h2, sub_self, sub_self]
    exact ⟨rfl, rfl⟩
  obtain ⟨w, hw⟩ := hsurj (x - y)
  have hw0 : w = 0 := wfsMV_injective n hn w (by rw [hw]; exact hpair.1)
    (by rw [hw]; exact hpair.2)
  have hsub : x - y = 0 := by rw [← hw, hw0, map_zero]
  exact sub_eq_zero.mp hsub

end

end Work.Stems
