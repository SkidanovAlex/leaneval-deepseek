import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSGRoute.PinnedTwin.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The congruence subgroup `U(𝔪)` is stable under `Gal(K/k)`

For a modulus `𝔪` with `𝔪.pos = ∅` whose finite part is invariant under `ρ ∈ Gal(K/k)`
(`𝔪.exps (ρ • q) = 𝔪.exps q`), the congruence subgroup `U(𝔪) ≤ 𝕀 K` is stable under the action of
`ρ`: if `x ∈ U(𝔪)` then `ρ • x ∈ U(𝔪)`.

This is the `∀`-form of the pointwise statement (`Work.SSGRoute.PinnedTwin.congSubgroup_smul_mem`);
it is proved here directly, so that the statement is available with exactly this binder shape.

The proof is a pointwise computation at the finite places.  At a place `q`, the idèle `ρ • x` is
the transport of the component of `x` at `ρ⁻¹q` along the canonical local isomorphism
`K_{ρ⁻¹q} ≃+* K_q`; that isomorphism is an isometry for the `Valued.v` valuations
(`globalCFT_adicCongrEquiv_valued`), which makes it preserve both the "local unit" condition and
the congruence condition `IsCongAt`, the level at `q` being the level at `ρ⁻¹q` by hypothesis.
The archimedean conditions are vacuous because `𝔪.pos = ∅`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped NumberField

namespace Work.SSGRoute.PinnedTwin

open NK.GlobalCFT

section Helpers

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- The canonical local isomorphism `K_q ≃+* K_{ρ⁻¹q}` (transported through its inverse) is an
isometry: it preserves `Valued.v`. -/
private lemma valued_adicCongr_symm (ρ : K ≃ₐ[k] K) (q : HeightOneSpectrum (𝓞 K))
    (y : (Place.smulHeightOneSpectrum ρ⁻¹ q).adicCompletion K) :
    Valued.v (((Galois.globalCFT_adicCongrEquiv ρ⁻¹ q).symm y :
      q.adicCompletion K)) = Valued.v y := by
  have h := Galois.globalCFT_adicCongrEquiv_valued ρ⁻¹ q
    ((Galois.globalCFT_adicCongrEquiv ρ⁻¹ q).symm y)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- The canonical local isomorphism commutes with `- 1`. -/
private lemma adicCongr_symm_sub_one (ρ : K ≃ₐ[k] K) (q : HeightOneSpectrum (𝓞 K))
    (y : (Place.smulHeightOneSpectrum ρ⁻¹ q).adicCompletion K) :
    (((Galois.globalCFT_adicCongrEquiv ρ⁻¹ q).symm y : q.adicCompletion K) - 1)
      = ((Galois.globalCFT_adicCongrEquiv ρ⁻¹ q).symm (y - 1) : q.adicCompletion K) := by
  rw [map_sub, map_one]

/-- The isometry preserves the distance to `1`. -/
private lemma valued_adicCongr_symm_sub_one (ρ : K ≃ₐ[k] K) (q : HeightOneSpectrum (𝓞 K))
    (y : (Place.smulHeightOneSpectrum ρ⁻¹ q).adicCompletion K) :
    Valued.v ((((Galois.globalCFT_adicCongrEquiv ρ⁻¹ q).symm y :
        q.adicCompletion K) - 1)) = Valued.v (y - 1) := by
  rw [adicCongr_symm_sub_one ρ q y]
  exact valued_adicCongr_symm ρ q (y - 1)

end Helpers

theorem rhoStableCongSubgroup {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (𝔪 : NK.NUV2.RouteB.Modulus K) (hpos : 𝔪.pos = ∅)
    (hstab : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q) :
    ∀ x : NK.GlobalCFT.Idele K, x ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪 →
      ρ • x ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
  intro x hx
  classical
  rw [NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff] at hx ⊢
  obtain ⟨hxfin, _⟩ := hx
  refine ⟨fun q => ?_, fun w hw hmem => by simp [hpos] at hmem⟩
  -- The component of `x` at the preimage place `ρ⁻¹q`.
  obtain ⟨hval, hcong⟩ := hxfin (Place.smulHeightOneSpectrum ρ⁻¹ q)
  -- The component of `ρ • x` at `q`, as the transport of the `ρ⁻¹q`-component of `x`.
  have hcoe : (((ρ • x) (Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K)
      = (Galois.globalCFT_adicCongrEquiv ρ⁻¹ q).symm
          (((x (Place.ofFinite (Place.smulHeightOneSpectrum ρ⁻¹ q)) :
              ((Place.smulHeightOneSpectrum ρ⁻¹ q).adicCompletion K)ˣ)) :
            (Place.smulHeightOneSpectrum ρ⁻¹ q).adicCompletion K) := by
    rw [NK.GlobalCFT.Idele.smul_apply]
    simp only [Place.smul_ofFinite]
    rfl
  -- `ρ` transports the level at `q` to the level at `ρ⁻¹q`, so the two exponents agree.
  have hexp : 𝔪.exps (Place.smulHeightOneSpectrum ρ⁻¹ q) = 𝔪.exps q := by
    have hqinv : Place.smulHeightOneSpectrum ρ (Place.smulHeightOneSpectrum ρ⁻¹ q) = q := by
      rw [Galois.smulHeightOneSpectrum_mul ρ⁻¹ ρ q, mul_inv_cancel,
        NK.GlobalCFT.Inclusion.smulHeightOneSpectrum_one]
    have h := hstab (Place.smulHeightOneSpectrum ρ⁻¹ q)
    rw [NK.GlobalCFT.Inclusion.globalCFT_placeSmul_eq_smulHeightOneSpectrum ρ
      (Place.smulHeightOneSpectrum ρ⁻¹ q), hqinv] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · -- The "local unit" condition.
    rw [hcoe]
    exact (valued_adicCongr_symm ρ q _).trans hval
  · -- The congruence condition.
    rw [NK.NUV2.RouteB.IsCongAt] at hcong ⊢
    rw [hexp] at hcong
    rw [hcoe]
    exact (valued_adicCongr_symm_sub_one ρ q _).trans_le hcong

end Work.SSGRoute.PinnedTwin
