import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero
import Submission.Work.ThomBordism.evaluation_kernel_torsion_of_pd

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A class of the normal total space whose zero-section pullback pairs to `1`

The target `Work.ThomBordism.exists_zeroSection_pairing_one` asks for a degree-`8` cohomology
class `w` of the normal total space `ν = NormalTotal E` of an embedding `E : V ↪ ℝ^{8+k}` of a
connected closed oriented smooth `8`-manifold whose pullback along the zero section pairs to `1`
with the fundamental class `V.c`:

  `⟨(zeroSection)^* w, V.c⟩ = 1`.

This is strictly stronger than the non-vanishing
`Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero`; the integrality "up to sign" is what the
downstream last-mile arguments consume.

The proof is a two-step reduction.

* **The zero section is split by the projection.**  `normalProjTotal E : ν → V` satisfies
  `proj ∘ zeroSection = id`, hence `(zeroSection)^* proj^* = id` on `H^8(V)`.  So it suffices to
  find a class `u ∈ H^8(V)` with `⟨u, V.c⟩ = 1`.
* **A primitive functional exists on `H₈(V)`.**  `V.c` is a fundamental class: at every point `x`
  its local class `loc V.c ∈ H₈(V, V∖{x}) ≅ ℤ` *generates* (`V.c_fund x`).  Composing the
  localisation with the isomorphism `e : H₈(V, V∖{x}) ≅ ℤ` gives a functional
  `η • (e ∘ loc) : H₈(V) → ℤ` whose value on `V.c` is `η * η = 1` (`η = ±1` being a generator of
  `ℤ`).  Since the Kronecker pairing `kronH : H⁸(V) → Hom(H₈(V), ℤ)` is surjective
  (`Work.ThomBordism.kronH_surjective`, from the universal coefficient theorem and the freeness of
  the singular chains), every such functional is realised by a cohomology class.
-/

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.ThomBordism

noncomputable section

open CategoryTheory AlgebraicTopology

/-- **A degree-`8` cohomology class of a connected closed oriented `8`-manifold pairs to `1` with
the fundamental class.**  This is the primitive form of
`Work.ThomBordism.exists_fundPairing_ne_zero`: the existence of the local degrees of a fundamental
class (the field `Man8.c_fund`) forces the Kronecker pairing `⟨·, V.c⟩` to be *surjective* (there is
a functional on `H₈(V)` with value `1` on `V.c`, and every functional on homology is a Kronecker
pairing by `Work.ThomBordism.kronH_surjective`). -/
theorem exists_fundPairing_one (V : Work.ThomBordism.Man8) [ConnectedSpace V.pt] :
    ∃ u : Work.Thom.Coh ℤ 8 (TopCat.of V.pt),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8 u V.c = 1 := by
  classical
  set X : SSet := TopCat.toSSet.obj (TopCat.of V.pt) with hX
  obtain ⟨x⟩ := (inferInstance : Nonempty V.pt)
  -- the local group at `x` is `ℤ`
  obtain ⟨e⟩ := Work.ThomBordism.RelH_point_iso 8 (by norm_num) (TopCat.of V.pt) x
  -- the localisation `H₈(V) → H₈(V, V∖{x})`
  let loc : (Work.Cohomology.chainC ℤ X).homology 8 →ₗ[ℤ]
      ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)) :=
    (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of V.pt)
        {y : V.pt | y ≠ x})) 8).hom
  have hloc : loc V.c = Work.Orient.locClass (TopCat.of V.pt) 8 V.c x := rfl
  -- the local class of the fundamental class generates the local group
  have hspan : Submodule.span ℤ {loc V.c} = ⊤ := by rw [hloc]; exact V.c_fund x
  let η : ℤ := e.hom.hom (loc V.c)
  -- `η` generates `ℤ`, i.e. `η = ±1`
  have hone : (1 : ℤ) ∈ Submodule.span ℤ {η} := by
    have hmap : Submodule.map (e.hom.hom) (Submodule.span ℤ {loc V.c})
        = Submodule.span ℤ {η} := by
      rw [Submodule.map_span, Set.image_singleton]
    have htop : Submodule.map (e.hom.hom) (⊤ : Submodule ℤ
        ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt))) = ⊤ := by
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.mpr (ConcreteCategory.bijective_of_isIso e.hom).2
    rw [← hmap, hspan, htop]
    trivial
  have hunit : IsUnit η := by
    obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp hone
    exact isUnit_iff_exists_inv.mpr ⟨m, by rw [mul_comm]; exact hm⟩
  have heta : η = 1 ∨ η = -1 := Int.isUnit_iff.mp hunit
  -- the primitive functional `η • (e ∘ loc)`, with value `η * η = 1` on `V.c`
  let χ : (Work.Cohomology.chainC ℤ X).homology 8 →ₗ[ℤ] ℤ := η • (e.hom.hom.comp loc)
  have h1 : χ V.c = η * η := rfl
  have hχ : χ V.c = 1 := by
    rcases heta with h | h <;> rw [h1, h] <;> norm_num
  -- every functional on homology is a Kronecker pairing
  obtain ⟨γ, hγ⟩ := Work.ThomBordism.kronH_surjective X 8
    (fun k => Work.Cohomology.singularChains_free (TopCat.of V.pt) k) χ
  refine ⟨γ, ?_⟩
  rw [show Work.Cohomology.kronH ℤ X 8 γ = χ from hγ]
  exact hχ

theorem exists_zeroSection_pairing_one {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    (k : ℕ) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    ∃ w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1 := by
  obtain ⟨u, hu⟩ := exists_fundPairing_one V
  refine ⟨(Work.Thom.CohMap (Work.ThomBordism.normalProjTotal E) ℤ 8).hom u, ?_⟩
  have hcoe : (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom
      ((Work.Thom.CohMap (Work.ThomBordism.normalProjTotal E) ℤ 8).hom u) = u := by
    rw [Work.Thom.CohMap_comp_apply (Work.Tubular.zeroSectionNormal E)
        (Work.ThomBordism.normalProjTotal E) ℤ 8 u,
      Work.ThomBordism.normalProjTotal_comp_zeroSection, Work.Thom.CohMap_id]
    rfl
  rw [hcoe]
  exact hu

end

end Work.ThomBordism
