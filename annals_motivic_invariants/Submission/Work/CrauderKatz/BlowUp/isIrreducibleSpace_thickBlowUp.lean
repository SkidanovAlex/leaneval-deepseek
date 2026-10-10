/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.BlowUp.ThickDefs
import Submission.Work.CrauderKatz.BlowUp.ThickGlue
import Submission.Work.CrauderKatz.BlowUp.isPrime_nilradical_thickRing
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.BlowUp.isIrreducibleSpace_thickBlowUp`

The thickened blow-up `thickBlowUp 𝕜 = colimit (diag 𝕜)` of the affine plane at the origin is
glued from the two affine charts `chartS 𝕜 = Spec 𝕜[x,t,ε]/(ε², x·ε)` along the overlap
`ovS 𝕜 = Spec 𝕜[x,t^{±1},ε]/(ε², x·ε)` (through the two open immersions `ovToChart₁` and
`ovToChart₂`).  We prove that it is an **irreducible topological space**, which is the
`IrreducibleSpace` instance a caller needs in order to speak of the *generic point* of the
thickened blow-up (e.g. the generic point of the thickened exceptional curve, or the function
field of the source of the modification).

The argument is in two steps.

* Each chart is irreducible: `𝕜[x,t,ε]/(ε², x·ε)` has prime nilradical
  (`isPrime_nilradical_thickRing`), so `Spec` of it is an irreducible space; irreducibility is
  transported along the open immersions `chart₁`, `chart₂` to their images.
* The two chart images are open subsets of `thickBlowUp 𝕜` whose union is everything and whose
  intersection is nonempty.  The union statement is the standard "gluing computes the colimit"
  fact: by `Scheme.IsLocallyDirected.ι_jointly_surjective` (available because all the arrows of
  `diag 𝕜` are open immersions) every point of the colimit comes from `ovS 𝕜`, from the first
  chart or from the second chart, and the image of `ovS 𝕜` lies in the image of either chart by
  the cocone condition `ovToChart₁ ≫ chart₁ = colimit.ι none`.  The intersection is nonempty
  because a point of the (nonempty) overlap is mapped to the same point of the colimit through
  either chart, again by the cocone condition.

Two general topological lemmas do the bookkeeping:

* `irreducible_inter_nonempty_of_open_of_subset`: in an irreducible subspace `U`, two nonempty
  open subsets of `U` (presented as open subsets of the ambient space contained in `U`) meet;
* `irreducibleSpace_of_open_union`: a space covered by two open irreducible subspaces with
  nonempty intersection is irreducible.  (Both openness *and* the nonempty intersection are
  needed: the union of two closed lines meeting in a point is the standard counterexample.)
-/

set_option autoImplicit false
set_option linter.unusedVariables false
-- `haveI` is used deliberately: the local `IrreducibleSpace` instances are needed as
-- typeclass arguments.
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Work.CrauderKatz.BlowUp

noncomputable section

/-! ### Two general topological lemmas -/

/-- In an irreducible subspace `U`, two nonempty open subsets of `U` — presented as open subsets
`S`, `T` of the ambient space with `S ⊆ U`, `T ⊆ U` — have nonempty intersection. -/
theorem irreducible_inter_nonempty_of_open_of_subset {X : Type*} [TopologicalSpace X] {U S T : Set X}
    [IrreducibleSpace U] (hS : IsOpen S) (hT : IsOpen T) (hSU : S ⊆ U) (hTU : T ⊆ U)
    (hSn : S.Nonempty) (hTn : T.Nonempty) : (S ∩ T).Nonempty := by
  have h := nonempty_preirreducible_inter (X := U) (s := Subtype.val ⁻¹' S) (t := Subtype.val ⁻¹' T)
    (hS.preimage continuous_subtype_val) (hT.preimage continuous_subtype_val)
    (by obtain ⟨x, hx⟩ := hSn; exact ⟨⟨x, hSU hx⟩, hx⟩)
    (by obtain ⟨x, hx⟩ := hTn; exact ⟨⟨x, hTU hx⟩, hx⟩)
  obtain ⟨u, hu⟩ := h
  exact ⟨u.1, hu.1, hu.2⟩

/-- A topological space covered by two open irreducible subspaces with nonempty intersection is
irreducible. -/
theorem irreducibleSpace_of_open_union {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) [IrreducibleSpace U] [IrreducibleSpace V]
    (hUV : U ∪ V = Set.univ) (hne : (U ∩ V).Nonempty) : IrreducibleSpace X := by
  have hUne : U.Nonempty := hne.mono Set.inter_subset_left
  haveI : PreirreducibleSpace X :=
    PreirreducibleSpace.of_forall_nonempty_inter fun A B hA hB hAn hBn => by
    have hAU : A ⊆ U ∪ V := by rw [hUV]; exact Set.subset_univ A
    have hBU : B ⊆ U ∪ V := by rw [hUV]; exact Set.subset_univ B
    by_cases hAU' : (A ∩ U).Nonempty
    · by_cases hBU' : (B ∩ U).Nonempty
      · obtain ⟨x, hx⟩ := irreducible_inter_nonempty_of_open_of_subset (U := U) (hA.inter hU)
          (hB.inter hU) Set.inter_subset_right Set.inter_subset_right hAU' hBU'
        exact ⟨x, hx.1.1, hx.2.1⟩
      · have hBV' : B ⊆ V := by
          intro x hx
          rcases hBU hx with h | h
          · exact absurd ⟨x, hx, h⟩ hBU'
          · exact h
        have hBVn : (B ∩ V).Nonempty := ⟨hBn.some, hBn.some_mem, hBV' hBn.some_mem⟩
        by_cases hAV' : (A ∩ V).Nonempty
        · obtain ⟨x, hx⟩ := irreducible_inter_nonempty_of_open_of_subset (U := V) (hA.inter hV)
            (hB.inter hV) Set.inter_subset_right Set.inter_subset_right hAV' hBVn
          exact ⟨x, hx.1.1, hx.2.1⟩
        · exfalso
          have hAVe : A ∩ V = ∅ := Set.not_nonempty_iff_eq_empty.mp hAV'
          have hAUe : A ∩ U = A := by
            apply Set.Subset.antisymm Set.inter_subset_left
            intro x hx
            rcases hAU hx with h | h
            · exact ⟨hx, h⟩
            · have hmem : x ∈ A ∩ V := ⟨hx, h⟩
              rw [hAVe] at hmem
              exact absurd hmem (Set.notMem_empty x)
          obtain ⟨x, hx⟩ := irreducible_inter_nonempty_of_open_of_subset (U := U) (hA.inter hU)
            (hU.inter hV) Set.inter_subset_right Set.inter_subset_left (by rw [hAUe]; exact hAn) hne
          exact hAV' ⟨x, hx.1.1, hx.2.2⟩
    · have hAV' : A ⊆ V := by
        intro x hx
        rcases hAU hx with h | h
        · exact absurd ⟨x, hx, h⟩ hAU'
        · exact h
      have hAVn : (A ∩ V).Nonempty := ⟨hAn.some, hAn.some_mem, hAV' hAn.some_mem⟩
      by_cases hBV' : (B ∩ V).Nonempty
      · obtain ⟨x, hx⟩ := irreducible_inter_nonempty_of_open_of_subset (U := V) (hA.inter hV)
          (hB.inter hV) Set.inter_subset_right Set.inter_subset_right hAVn hBV'
        exact ⟨x, hx.1.1, hx.2.1⟩
      · exfalso
        have hBVe : B ∩ V = ∅ := Set.not_nonempty_iff_eq_empty.mp hBV'
        have hBUe : B ∩ U = B := by
          apply Set.Subset.antisymm Set.inter_subset_left
          intro x hx
          rcases hBU hx with h | h
          · exact ⟨hx, h⟩
          · have hmem : x ∈ B ∩ V := ⟨hx, h⟩
            rw [hBVe] at hmem
            exact absurd hmem (Set.notMem_empty x)
        obtain ⟨x, hx⟩ := irreducible_inter_nonempty_of_open_of_subset (U := U) (hB.inter hU)
          (hU.inter hV) Set.inter_subset_right Set.inter_subset_left (by rw [hBUe]; exact hBn) hne
        exact hBV' ⟨x, hx.1.1, hx.2.2⟩
  exact IrreducibleSpace.mk ⟨hUne.some⟩

/-! ### The ring `R 𝕜[1/t]` of the overlap is nontrivial, hence `ovS 𝕜` is nonempty -/

variable (𝕜 : Type) [Field 𝕜]

/-- The overlap ring `ovRing 𝕜 = R 𝕜[1/t]` is nontrivial: it receives a ring homomorphism from
the chart ring (with `x ↦ 1`, `t ↦ 1`, `ε ↦ 0`) *and* a ring homomorphism to `𝕜` (the induced
map out of the localization, well defined since `t ↦ 1` is a unit in `𝕜`). -/
theorem nontrivial_ovRing : Nontrivial (ovRing 𝕜) := by
  let f : Fin 3 → 𝕜 := fun i => if i = 0 then 1 else if i = 1 then 1 else 0
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = 1 := by simp [f]
  have hf2 : f 2 = 0 := by simp [f]
  have hker : ∀ a ∈ thickI 𝕜, MvPolynomial.eval f a = 0 := by
    intro a ha
    rw [thickI, Ideal.mem_span_pair] at ha
    obtain ⟨A, B, hAB⟩ := ha
    rw [← hAB]
    simp only [map_add, map_mul, map_pow, MvPolynomial.eval_X, hf0, hf2]
    first | refl_ring1 | ring
  let psi : thickRing 𝕜 →+* 𝕜 := Ideal.Quotient.lift (thickI 𝕜) (MvPolynomial.eval f) hker
  have hpsi : psi (thickT 𝕜) = 1 := by
    show Ideal.Quotient.lift (thickI 𝕜) (MvPolynomial.eval f) hker
      (Ideal.Quotient.mk (thickI 𝕜) (MvPolynomial.X 1)) = 1
    rw [Ideal.Quotient.lift_mk, MvPolynomial.eval_X, hf1]
  exact (IsLocalization.Away.lift (thickT 𝕜) (g := psi)
    (by rw [hpsi]; exact isUnit_one)).domain_nontrivial

/-- The overlap `ovS 𝕜 = Spec R 𝕜[1/t]` is nonempty. -/
theorem nonempty_ovS : Nonempty (ovS 𝕜) :=
  haveI := nontrivial_ovRing 𝕜
  inferInstance

/-! ### The two charts cover the thickened blow-up -/

/-- The two charts of `thickBlowUp 𝕜` cover it: the open subschemes `chart₁.opensRange` and
`chart₂.opensRange` have join `⊤`.  Indeed, every point of the colimit is in the image of
`ovS 𝕜`, of `chart₁` or of `chart₂` (`Scheme.IsLocallyDirected.ι_jointly_surjective`), and the
image of `ovS 𝕜` is contained in the image of the first chart thanks to the cocone condition
`ovToChart₁ ≫ chart₁ = colimit.ι none`. -/
theorem opensRange_chart₁_sup_opensRange_chart₂ :
    (chart₁ 𝕜).opensRange ⊔ (chart₂ 𝕜).opensRange = ⊤ := by
  rw [eq_top_iff]
  intro x hx
  obtain ⟨i, xi, hxi⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diag 𝕜) x
  rcases i with _ | j
  · have hmap : (diag 𝕜).map (WidePushoutShape.Hom.init (0 : Fin 2)) = ovToChart₁ 𝕜 := by
      simp only [diag, WidePushoutShape.wideSpan_map]
      simp
    have h0 : colimit.ι (diag 𝕜) none = ovToChart₁ 𝕜 ≫ chart₁ 𝕜 := by
      rw [← colimit.w (diag 𝕜) (WidePushoutShape.Hom.init (0 : Fin 2)), hmap]
      rfl
    have hxU : x ∈ (chart₁ 𝕜).opensRange := by
      refine Scheme.Hom.mem_opensRange.mpr ⟨ovToChart₁ 𝕜 xi, ?_⟩
      rw [← hxi, h0]
      rfl
    exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hxU)
  · fin_cases j
    · have hxU : x ∈ (chart₁ 𝕜).opensRange := Scheme.Hom.mem_opensRange.mpr ⟨xi, hxi⟩
      exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hxU)
    · have hxU : x ∈ (chart₂ 𝕜).opensRange := Scheme.Hom.mem_opensRange.mpr ⟨xi, hxi⟩
      exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr hxU)

/-- Both open immersions of the overlap `ovS 𝕜` into the colimit agree: a point `y` of the
overlap maps to the same point of `thickBlowUp 𝕜` through the first and through the second
chart.  This is the cocone condition of the colimit along the two arrows `ovToChart₁`,
`ovToChart₂`. -/
theorem chart₁_ovToChart₁_eq_chart₂_ovToChart₂ (y : ovS 𝕜) :
    chart₁ 𝕜 (ovToChart₁ 𝕜 y) = chart₂ 𝕜 (ovToChart₂ 𝕜 y) := by
  have hw1 : (diag 𝕜).map (WidePushoutShape.Hom.init (0 : Fin 2)) = ovToChart₁ 𝕜 := by
    simp only [diag, WidePushoutShape.wideSpan_map]
    simp
  have hw2 : (diag 𝕜).map (WidePushoutShape.Hom.init (1 : Fin 2)) = ovToChart₂ 𝕜 := by
    simp only [diag, WidePushoutShape.wideSpan_map]
    simp
  have h1 : ovToChart₁ 𝕜 ≫ chart₁ 𝕜 = colimit.ι (diag 𝕜) none := by
    rw [← colimit.w (diag 𝕜) (WidePushoutShape.Hom.init (0 : Fin 2)), hw1]
    rfl
  have h2 : ovToChart₂ 𝕜 ≫ chart₂ 𝕜 = colimit.ι (diag 𝕜) none := by
    rw [← colimit.w (diag 𝕜) (WidePushoutShape.Hom.init (1 : Fin 2)), hw2]
    rfl
  have e1 : chart₁ 𝕜 (ovToChart₁ 𝕜 y) = colimit.ι (diag 𝕜) none y := by
    rw [← h1]; rfl
  have e2 : colimit.ι (diag 𝕜) none y = chart₂ 𝕜 (ovToChart₂ 𝕜 y) := by
    rw [← h2]; rfl
  exact e1.trans e2

/-! ### The main statement -/

/-- **The thickened blow-up of the plane is irreducible.** -/
theorem isIrreducibleSpace_thickBlowUp (𝕜 : Type) [Field 𝕜] : IrreducibleSpace (Work.CrauderKatz.BlowUp.thickBlowUp 𝕜) := by
  -- each chart is irreducible
  have hchart : IrreducibleSpace (chartS 𝕜) :=
    (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical).mpr (isPrime_nilradical_thickRing 𝕜)
  haveI hU₁ : IrreducibleSpace ↥((chart₁ 𝕜).opensRange) :=
    ((chart₁ 𝕜).isoOpensRange.hom.homeomorph.irreducibleSpace_iff).mp hchart
  haveI hU₂ : IrreducibleSpace ↥((chart₂ 𝕜).opensRange) :=
    ((chart₂ 𝕜).isoOpensRange.hom.homeomorph.irreducibleSpace_iff).mp hchart
  -- the two charts cover `thickBlowUp 𝕜`
  have hcov := opensRange_chart₁_sup_opensRange_chart₂ 𝕜
  -- and their images meet in the image of the (nonempty) overlap
  have hne : ((↑((chart₁ 𝕜).opensRange) : Set (thickBlowUp 𝕜)) ∩
      ↑((chart₂ 𝕜).opensRange)).Nonempty := by
    obtain ⟨y⟩ := nonempty_ovS 𝕜
    refine ⟨chart₁ 𝕜 (ovToChart₁ 𝕜 y), ?_, ?_⟩
    · exact Scheme.Hom.mem_opensRange.mpr ⟨ovToChart₁ 𝕜 y, rfl⟩
    · rw [chart₁_ovToChart₁_eq_chart₂_ovToChart₂ 𝕜 y]
      exact Scheme.Hom.mem_opensRange.mpr ⟨ovToChart₂ 𝕜 y, rfl⟩
  exact irreducibleSpace_of_open_union (U := ↑((chart₁ 𝕜).opensRange))
    (V := ↑((chart₂ 𝕜).opensRange)) ((chart₁ 𝕜).opensRange.isOpen) ((chart₂ 𝕜).opensRange.isOpen)
    (by rw [← TopologicalSpace.Opens.coe_sup, hcov, TopologicalSpace.Opens.coe_top]) hne

end

end Work.CrauderKatz.BlowUp
