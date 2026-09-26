import Mathlib
import Submission.Work.Modular.Poisson.Std
import Submission.Work.Poisson.covolume_intLatticeE

/-!
# The covolume of a lattice presented as a preimage of `ℤⁿ`

The main result of this file, `Work.Poisson.covolume_eq_det_inv`, computes the covolume of a
`ℤ`-submodule `L ⊆ EuclideanSpace ℝ (Fin n)` that is the pullback of the standard integer lattice
`Work.Modular.intLatticeE (Fin n) = ℤⁿ` under a real linear equivalence `d`:
`covolume L = |det d|⁻¹`.

The mathematical content is the scaling of covolume under a linear equivalence: a fundamental
domain of `L = d⁻¹(ℤⁿ)` is the preimage under `d` of a fundamental domain `F` of `ℤⁿ`, and the
Haar measure of a preimage under a linear equivalence `e` is `|det e.symm| • μ`, i.e.
`|det e|⁻¹ • μ` (`MeasureTheory.Measure.addHaar_preimage_linearEquiv`). Combined with the known
value `covolume (ℤⁿ) = 1` (`Work.Poisson.covolume_intLatticeE`), this gives the claim.

The auxiliary lemma `Work.Poisson.covolume_comap_of_linearEquiv` is the general scaling statement for an
arbitrary full `ℤ`-lattice `M` in place of `ℤⁿ`; it is proved by transporting a fundamental domain
of `M` (`ZSpan.fundamentalDomain`, from a `ℤ`-basis of `M`) along the equivalence
`IsAddFundamentalDomain.preimage_of_equiv`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory

namespace Work.Poisson

/-- Membership in the pullback `ZLattice.comap ℝ M e` of a submodule is membership of the image
under `e`. -/
lemma zLattice_comap_mem_iff {n : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ ZLattice.comap ℝ M e.toLinearMap ↔ e x ∈ M := by
  show x ∈ Submodule.comap (e.toLinearMap.restrictScalars ℤ) M ↔ e x ∈ M
  rw [Submodule.mem_comap]
  rfl

/-- **Covolume scales by the inverse absolute determinant.** For a full `ℤ`-lattice `M` in
`EuclideanSpace ℝ (Fin n)` and a real linear equivalence `e`, the covolume of the pullback lattice
`e ⁻¹ M` is `|det e|⁻¹` times the covolume of `M`. -/
theorem covolume_comap_of_linearEquiv {n : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology M] [IsZLattice ℝ M]
    (e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ZLattice.covolume (ZLattice.comap ℝ M e.toLinearMap) volume
      = |LinearMap.det e.toLinearMap|⁻¹ * ZLattice.covolume M volume := by
  -- the pullback lattice is again a full `ℤ`-lattice
  haveI hdisc : DiscreteTopology (ZLattice.comap ℝ M e.toLinearMap) :=
    ZLattice.comap_discreteTopology ℝ M
      (LinearMap.continuous_of_finiteDimensional e.toLinearMap) e.injective
  haveI hlat : IsZLattice ℝ (ZLattice.comap ℝ M e.toLinearMap) :=
    ⟨ZLattice.comap_span_top ℝ M IsZLattice.span_top fun x hx => ⟨e.symm x, by simp⟩⟩
  -- a fundamental domain of `M`
  let b := Module.Free.chooseBasis ℤ M
  have hF : IsAddFundamentalDomain ↥M (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ M)) volume :=
    ZLattice.isAddFundamentalDomain b volume
  -- the group isomorphism `M ≅ e ⁻¹ M`, `m ↦ e.symm m`
  let φ : ↥M → ↥(ZLattice.comap ℝ M e.toLinearMap) := fun m =>
    ⟨e.symm (m : EuclideanSpace ℝ (Fin n)), by
      rw [zLattice_comap_mem_iff]
      simp⟩
  -- `e` is quasi-measure-preserving for the Lebesgue measure
  have hqmp : Measure.QuasiMeasurePreserving (⇑e) volume volume := by
    refine ⟨(LinearMap.continuous_of_finiteDimensional e.toLinearMap).measurable, ?_⟩
    have hdet : LinearMap.det e.toLinearMap ≠ 0 := (LinearEquiv.isUnit_det' e).ne_zero
    have hmap :=
      Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (f := e.toLinearMap) hdet
    rw [show Measure.map (⇑e) volume
          = ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| • volume by
      rw [← hmap]
      rfl]
    exact Measure.smul_absolutelyContinuous
  have hbij : Function.Bijective φ := by
    constructor
    · intro m m' h
      have h1 : e.symm (m : EuclideanSpace ℝ (Fin n))
          = e.symm (m' : EuclideanSpace ℝ (Fin n)) := by
        simpa [φ] using congrArg Subtype.val h
      exact Subtype.ext (e.symm.injective h1)
    · intro l
      refine ⟨⟨e (l : EuclideanSpace ℝ (Fin n)), l.2⟩, ?_⟩
      simp only [φ]
      exact Subtype.ext (e.symm_apply_apply _)
  -- the preimage of a fundamental domain of `M` is a fundamental domain of the pullback
  have hFD : IsAddFundamentalDomain ↥(ZLattice.comap ℝ M e.toLinearMap)
      ((⇑e) ⁻¹' ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ M)) volume :=
    hF.preimage_of_equiv hqmp hbij (fun m x => by
      simp only [φ, Submodule.vadd_def, vadd_eq_add]
      rw [map_add, LinearEquiv.apply_symm_apply])
  -- compute both covolumes as the volumes of these fundamental domains
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hFD,
      ZLattice.covolume_eq_measure_fundamentalDomain M volume hF,
      Measure.real_def, Measure.real_def,
      Measure.addHaar_preimage_linearEquiv volume e
        (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ M)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      LinearEquiv.det_coe_symm, abs_inv]

theorem covolume_eq_det_inv {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hspan : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊤)
    (d : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hd : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ L ↔ d x ∈ Work.Modular.intLatticeE (Fin n)) :
    Work.Modular.covolume L = |LinearMap.det d.toLinearMap|⁻¹ := by
  haveI hM1 : DiscreteTopology (Work.Modular.intLatticeE (Fin n)) := inferInstanceAs
    (DiscreteTopology (ZLattice.comap ℝ (Work.Modular.stdLattice (Fin n))
      (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap))
  haveI hM2 : IsZLattice ℝ (Work.Modular.intLatticeE (Fin n)) := inferInstanceAs
    (IsZLattice ℝ (ZLattice.comap ℝ (Work.Modular.stdLattice (Fin n))
      (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap))
  have hL : L = ZLattice.comap ℝ (Work.Modular.intLatticeE (Fin n)) d.toLinearMap := by
    ext x
    rw [zLattice_comap_mem_iff]
    exact hd x
  rw [Work.Modular.covolume, hL, covolume_comap_of_linearEquiv (Work.Modular.intLatticeE (Fin n)) d,
    Work.Poisson.covolume_intLatticeE, mul_one]

end Work.Poisson
