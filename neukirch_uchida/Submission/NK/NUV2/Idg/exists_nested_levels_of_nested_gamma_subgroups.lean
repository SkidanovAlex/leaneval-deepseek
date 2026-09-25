import Mathlib
import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.galToGamma
import Submission.NK.Reconstruct.galToGamma_continuous
import Submission.NK.Reconstruct.denseRange_galToGamma
import Submission.NK.Reconstruct.exists_gammaEquivOfPhi

/-!
# Nested levels realising a nested chain of open subgroups of `Γ_K`

Let `K` be a number field, `Ω` a separable closure of `K`, and

  `γ : Gal(Ω/K) →* Γ_K`,  `Γ_K = lim_{L} (Gal(L/K)^{ab})^{(2)}`,

the canonical map of `NK.Reconstruct.galToGamma` (the second component of the ℓ-primary part of
the abelianised restriction), whose range is dense in `Γ_K`
(`NK.Reconstruct.denseRange_galToGamma`).

The main result of this file, `exists_nested_levels_of_nested_gamma_subgroups`, says that a
**decreasing** sequence of **open** subgroups `W n ≤ Γ_K` with `Γ_K / W n ≅ (ℤ/2^n)^r` is realised
by a **nested tower of finite Galois levels** `L n` of `Ω/K` with `Gal(L n/K) ≅ (ℤ/2^n)^r`.

The construction is the Galois correspondence, not the class field theory:

* `H n := γ⁻¹(W n)` is an open normal subgroup of `Gal(Ω/K)` (openness is continuity of `γ`, the
  quotient `Γ_K ⧸ W n` being discrete; normality because `Γ_K` is abelian);
* the fixed field `L n := Ω^{H n}` is finite over `K` and Galois over `K`, with
  `Gal(L n/K) ≅ Gal(Ω/K) ⧸ H n` (`InfiniteGalois.normalAutEquivQuotient`);
* `Gal(Ω/K) ⧸ H n ≅ Γ_K ⧸ W n` (`quotientEquiv_of_open_subgroup`): the induced map is injective by
  construction, and surjective because `Gal(Ω/K)` has dense image in `Γ_K`, so it meets every
  translate `x·W n`;
* `W (n+1) ≤ W n` gives `H (n+1) ≤ H n`, and the anti-monotonicity of the fixed-field
  correspondence gives `L n ≤ L (n+1)`.

This is the "level realisation" step used in the idempotent/`Idg` part of the reconstruction of the
Neukirch–Uchida theorem.
-/

set_option linter.style.haveILetI false

namespace NK.NUV2.Idg

open scoped Pointwise

/-- **The quotient of `Gal(Ω/K)` by the preimage of an open subgroup of `Γ_K` is the quotient of
`Γ_K` by that subgroup.**

The canonical map `γ = galToGamma 2 : Gal(Ω/K) →* Γ_K` induces a homomorphism
`Gal(Ω/K) ⧸ γ⁻¹(U) →* Γ_K ⧸ U`; it is injective because the kernel of `γ` composed with the
quotient is exactly `γ⁻¹(U)`, and it is surjective because the range of `γ` is dense in `Γ_K`: it
therefore meets the translate `x·U`, which is an open neighbourhood of `x` as `U` is open. -/
theorem quotientEquiv_of_open_subgroup {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω]
    (U : Subgroup (NK.Reconstruct.Gamma K Ω 2))
    (hopen : IsOpen (U : Set (NK.Reconstruct.Gamma K Ω 2))) :
    Nonempty (Gal(Ω/K) ⧸ (U.comap (NK.Reconstruct.galToGamma (K := K) (K' := Ω) 2)) ≃*
      (NK.Reconstruct.Gamma K Ω 2) ⧸ U) := by
  classical
  set γ := NK.Reconstruct.galToGamma (K := K) (K' := Ω) 2 with hγ
  haveI hUn : U.Normal := Subgroup.normal_of_isMulCommutative U
  haveI hHn : (U.comap γ).Normal := Subgroup.Normal.comap hUn γ
  have hlift : U.comap γ ≤ ((QuotientGroup.mk' U).comp γ).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr hg
  refine ⟨MulEquiv.ofBijective
    (QuotientGroup.lift (U.comap γ) ((QuotientGroup.mk' U).comp γ) hlift) ⟨?_, ?_⟩⟩
  · -- injectivity: read the equation in `Γ_K ⧸ U`, i.e. modulo `U`, on representatives
    intro a b hab
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
    rw [QuotientGroup.lift_mk', QuotientGroup.lift_mk'] at hab
    simp only [MonoidHom.comp_apply] at hab
    apply QuotientGroup.eq.mpr
    change γ (g⁻¹ * h) ∈ U
    rw [map_mul, map_inv]
    exact (QuotientGroup.eq.mp hab)
  · -- surjectivity: the range of `γ` is dense and `x·U` is an open neighbourhood of `x`
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hd : DenseRange ⇑γ := by rw [hγ]; exact NK.Reconstruct.denseRange_galToGamma 2
    have hU : IsOpen {z : NK.Reconstruct.Gamma K Ω 2 | x⁻¹ * z ∈ U} :=
      hopen.preimage (continuous_const.mul continuous_id)
    have hne : ({z : NK.Reconstruct.Gamma K Ω 2 | x⁻¹ * z ∈ U}).Nonempty := ⟨x, by simp⟩
    obtain ⟨z, hzU, g, hgz⟩ := hd.inter_open_nonempty
      {z : NK.Reconstruct.Gamma K Ω 2 | x⁻¹ * z ∈ U} hU hne
    refine ⟨QuotientGroup.mk g, ?_⟩
    rw [QuotientGroup.lift_mk', MonoidHom.comp_apply]
    apply QuotientGroup.eq.mpr
    have h2 : (x⁻¹ * z)⁻¹ ∈ U := U.inv_mem hzU
    rw [mul_inv_rev, inv_inv] at h2
    rw [hgz]
    exact h2

set_option maxHeartbeats 800000 in
/-- **A nested chain of open quotients of `Γ_K` by `(ℤ/2^n)^r` is realised by a nested tower of
finite Galois number-field levels `L n/K` with `Gal(L n/K) ≅ (ℤ/2^n)^r`.**

The levels are the fixed fields of the open normal subgroups `γ⁻¹(W n) ≤ Gal(Ω/K)`, where
`γ : Gal(Ω/K) →* Γ_K` is the canonical map (`NK.Reconstruct.galToGamma`). -/
theorem exists_nested_levels_of_nested_gamma_subgroups (r : ℕ)
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω]
    (W : ℕ → Subgroup (NK.Reconstruct.Gamma K Ω 2))
    (hanti : ∀ n, W (n+1) ≤ W n)
    (hopen : ∀ n, IsOpen ((W n : Set (NK.Reconstruct.Gamma K Ω 2))))
    (hlev : ∀ n, Nonempty ((NK.Reconstruct.Gamma K Ω 2 ⧸ W n) ≃*
        Multiplicative (Fin r → ZMod (2^n)))) :
    ∃ L : ℕ → NK.Reconstruct.FrobLevel K Ω,
      (∀ n, (L n).L ≤ (L (n+1)).L) ∧
      (∀ n, IsGalois K ↥(L n).L) ∧
      (∀ n, Nonempty (Gal(↥(L n).L/K) ≃* Multiplicative (Fin r → ZMod (2^n)))) := by
  classical
  set γ := NK.Reconstruct.galToGamma (K := K) (K' := Ω) 2 with hγ
  have hγc : Continuous ⇑γ := by rw [hγ]; exact NK.Reconstruct.galToGamma_continuous 2
  -- the open normal subgroups of `Gal(Ω/K)` cut out by the `W n`
  let H : ℕ → ClosedSubgroup Gal(Ω/K) := fun n =>
    ⟨(W n).comap γ, (Subgroup.isClosed_of_isOpen (W n) (hopen n)).preimage hγc⟩
  have hHcoe : ∀ n, ((H n : ClosedSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) = (W n).comap γ :=
    fun n => rfl
  have hHnormal : ∀ n, (((H n : ClosedSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))).Normal := fun n => by
    rw [hHcoe n]
    exact Subgroup.Normal.comap (Subgroup.normal_of_isMulCommutative (W n)) γ
  -- the levels
  let Lf : ℕ → IntermediateField K Ω := fun n => IntermediateField.fixedField (H n).1
  -- they are finite and Galois over `K`
  have hfg : ∀ n, FiniteDimensional K ↥(Lf n) ∧ IsGalois K ↥(Lf n) := fun n => by
    have hfix : (Lf n).fixingSubgroup = (H n).1 :=
      InfiniteGalois.fixingSubgroup_fixedField (H n)
    have hop : IsOpen ((Lf n).fixingSubgroup : Set Gal(Ω/K)) := by
      rw [hfix]
      exact (hopen n).preimage hγc
    have hnor : (Lf n).fixingSubgroup.Normal := by
      rw [hfix]; exact hHnormal n
    exact (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (Lf n)).mp ⟨hop, hnor⟩
  -- the Galois group of the `n`-th level is `Γ_K ⧸ W n`
  have hquot : ∀ n, Nonempty ((Gal(Ω/K) ⧸ (H n : Subgroup Gal(Ω/K))) ≃*
      (NK.Reconstruct.Gamma K Ω 2) ⧸ W n) := fun n => by
    haveI : ((H n : Subgroup Gal(Ω/K))).Normal := hHnormal n
    exact quotientEquiv_of_open_subgroup (W n) (hopen n)
  refine ⟨fun n => ⟨Lf n, (hfg n).1, (hfg n).2.to_normal,
      by haveI : FiniteDimensional K ↥(Lf n) := (hfg n).1; exact inferInstance⟩, ?_, ?_, ?_⟩
  · -- nesting, from `W (n+1) ≤ W n` and the anti-monotonicity of `fixedField`
    intro n
    apply IntermediateField.fixedField_le
    intro g hg
    exact hanti n hg
  · intro n
    exact (hfg n).2
  · -- the Galois group of the `n`-th level, via the infinite Galois correspondence
    intro n
    haveI : ((H n : Subgroup Gal(Ω/K))).Normal := hHnormal n
    obtain ⟨e⟩ := hlev n
    obtain ⟨q⟩ := hquot n
    exact ⟨(InfiniteGalois.normalAutEquivQuotient (H n)).symm.trans (q.trans e)⟩

end NK.NUV2.Idg
