import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero

set_option linter.style.haveILetI false

namespace Work.HP.Lat

/-- Every `ℤ`-linear functional on a saturated sublattice `L ⊆ ℤ^ι` is the restriction of the
functional `z ↦ ∑ i, v i * z i` for some integer vector `v`.

Suggested route: `ℤ^ι / L` is torsion free by saturation, hence free (finitely generated module over
a PID), so the exact sequence `0 → L → ℤ^ι → ℤ^ι/L → 0` splits and `φ` extends to
`ψ : ℤ^ι →ₗ[ℤ] ℤ`; then `v i := ψ (Pi.single i 1)`.  A concrete alternative avoiding the
splitting lemma: this is only used with `L = latOrth x` for primitive `x`, where one can take
`z₀` with `⟨x,z₀⟩ = 1` (Bézout) and set `ψ z = φ (⟨x,z₀⟩ • z - ⟨x,z⟩ • z₀)`. -/
theorem exists_int_extends {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℤ)) (hL : IsSat L)
    (φ : L →ₗ[ℤ] ℤ) :
    ∃ v : ι → ℤ, ∀ z : L, φ z = ∑ i, v i * (z : ι → ℤ) i := by
  classical
  -- `ℤ^ι / L` is torsion free, since `L` is saturated.
  haveI : Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ L) :=
    Module.IsTorsionFree.of_smul_eq_zero (fun r m hr => by
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective L m
      rw [← map_smul] at hr
      by_cases hr0 : r = 0
      · exact Or.inl hr0
      · right
        have hmem : r • y ∈ L := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hr
          exact hr
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hL y ⟨r, hr0, hmem⟩)
  -- Being finitely generated and torsion free over the PID `ℤ`, the quotient is free.
  obtain ⟨n, hb⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := (ι → ℤ) ⧸ L)
  -- Lift the basis of the quotient to elements of `ℤ^ι`, giving a linear section.
  choose w hw using fun i => Submodule.mkQ_surjective L (hb i)
  let s : ((ι → ℤ) ⧸ L) →ₗ[ℤ] (ι → ℤ) := hb.constr ℤ w
  have hs : (Submodule.mkQ L).comp s = LinearMap.id := by
    refine hb.ext (fun i => ?_)
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [show s (hb i) = w i from by simp [s]]
    exact hw i
  -- The resulting projection onto `L` retracts the inclusion.
  have hmem_s : ∀ m : ι → ℤ, m - s (Submodule.mkQ L m) ∈ L := by
    intro m
    have hzero : Submodule.mkQ L (m - s (Submodule.mkQ L m)) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hs, LinearMap.id_apply, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero
    exact hzero
  let proj : (ι → ℤ) →ₗ[ℤ] L := LinearMap.codRestrict L
    ((LinearMap.id : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)) - s.comp (Submodule.mkQ L))
    (fun m => by simpa [LinearMap.sub_apply] using hmem_s m)
  have hproj : ∀ z : L, proj z = z := by
    intro z
    apply Subtype.ext
    have hz : Submodule.mkQ L (z : ι → ℤ) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact z.2
    simp only [proj, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply]
    rw [hz, map_zero, sub_zero]
  -- `φ` extends to `ℤ^ι` along the retraction.
  let ψ : (ι → ℤ) →ₗ[ℤ] ℤ := φ.comp proj
  have hψ : ∀ z : L, ψ (z : ι → ℤ) = φ z := by
    intro z
    simp only [ψ, LinearMap.comp_apply]
    rw [hproj z]
  refine ⟨fun i => ψ (Pi.single i (1:ℤ)), fun z => ?_⟩
  rw [← hψ z]
  have hzb : (z : ι → ℤ) = ∑ i, (z : ι → ℤ) i • (Pi.single i (1:ℤ) : ι → ℤ) := by
    ext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  have hexp : ψ (z : ι → ℤ) = ∑ i, (z : ι → ℤ) i • ψ (Pi.single i (1:ℤ) : ι → ℤ) := by
    conv_lhs => rw [hzb]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => map_smul ψ _ _)
  rw [hexp]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_eq_mul, mul_comm]

end Work.HP.Lat
