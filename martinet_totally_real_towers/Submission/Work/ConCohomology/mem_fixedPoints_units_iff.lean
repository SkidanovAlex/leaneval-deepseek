import Mathlib
import Submission.Work.ConCohomology.GaloisUnits

namespace Work.ConCohomology

/-- The `Gal(L/K)`-invariants of `Additive Lˣ` are exactly the units of `L` coming from units of
`K`.  This is the unit form of the fundamental theorem of (infinite) Galois theory: the fixed
field of `Gal(L/K)` is `K`. -/
lemma mem_fixedPoints_units_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (x : Additive Lˣ) :
    x ∈ fixedPoints (Gal(L/K)) (Additive Lˣ) ↔
      ∃ y : Kˣ, x = Additive.ofMul (Units.map (algebraMap K L).toMonoidHom y) := by
  constructor
  · intro hx
    -- `x` is fixed by all `K`-automorphisms of `L`, hence its underlying element is fixed, hence
    -- lies in `K`.
    have hfix : ∀ f : Gal(L/K), f (x.toMul : L) = (x.toMul : L) := by
      intro f
      have h1 : f • x = x := hx f
      have h2 : f • (x.toMul : Lˣ) = x.toMul := by
        have h1' : (f • x).toMul = x.toMul := congrArg Additive.toMul h1
        rwa [toMul_smul_additiveUnits] at h1'
      have h3 := congrArg (fun u : Lˣ => (u : L)) h2
      simpa [AlgEquiv.smul_units_def, Units.coe_map] using h3
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (x.toMul : L)).mpr hfix
    -- `k` is a unit of `K` since its image is a unit of `L`.
    have hk0 : k ≠ 0 := by
      intro h
      have hz : (algebraMap K L k : L) = 0 := by rw [h, map_zero]
      rw [hk] at hz
      exact (x.toMul).ne_zero hz
    refine ⟨Units.mk0 k hk0, ?_⟩
    have hunit : Units.map (algebraMap K L).toMonoidHom (Units.mk0 k hk0) = x.toMul := by
      apply Units.ext
      rw [Units.coe_map, Units.val_mk0]
      exact hk
    rw [hunit]
    exact (Equiv.apply_symm_apply Additive.ofMul x).symm
  · rintro ⟨y, rfl⟩ σ
    -- Elements of `K` are fixed by every `K`-automorphism of `L`.
    apply Additive.toMul.injective
    rw [toMul_smul_additiveUnits]
    have hu : (σ • Units.map (algebraMap K L).toMonoidHom y : Lˣ) =
        Units.map (algebraMap K L).toMonoidHom y := by
      apply Units.ext
      rw [AlgEquiv.smul_units_def, Units.coe_map, Units.coe_map]
      exact AlgEquiv.commutes σ (y : K)
    exact hu

end Work.ConCohomology
