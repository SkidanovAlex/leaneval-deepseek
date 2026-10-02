import Mathlib
import Submission.Work.MRMT.Beurling.Defs
import Submission.Work.MRMT.Beurling.exists_mul_left_L2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Beurling

open MeasureTheory

theorem beurling_l2_isometry :
    ∃ S : MeasureTheory.Lp ℂ 2 MeasureTheory.volume →L[ℂ] MeasureTheory.Lp ℂ 2 MeasureTheory.volume,
      (∀ f, ‖S f‖ = ‖f‖) ∧
      ∀ f : MeasureTheory.Lp ℂ 2 MeasureTheory.volume,
        (((MeasureTheory.Lp.fourierTransformₗᵢ ℂ ℂ) (S f) : MeasureTheory.Lp ℂ 2 MeasureTheory.volume) : ℂ → ℂ)
          =ᵐ[MeasureTheory.volume]
          (fun ξ => beurlingSymbol ξ * (((MeasureTheory.Lp.fourierTransformₗᵢ ℂ ℂ) f : MeasureTheory.Lp ℂ 2 MeasureTheory.volume) : ℂ → ℂ) ξ) := by
  -- The multiplication operator on `L²` by the a.e. bounded symbol `beurlingSymbol`.
  obtain ⟨T, _hTnorm, hT⟩ :=
    exists_mul_left_L2 beurlingSymbol aestronglyMeasurable_beurlingSymbol
      (Filter.Eventually.of_forall norm_beurlingSymbol_le)
  -- Conjugation of `T` by the (unitary) Fourier transform.
  let F := MeasureTheory.Lp.fourierTransformₗᵢ ℂ ℂ
  let S : MeasureTheory.Lp ℂ 2 MeasureTheory.volume →L[ℂ] MeasureTheory.Lp ℂ 2 MeasureTheory.volume :=
    (F.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (T.comp F.toContinuousLinearEquiv.toContinuousLinearMap)
  have hSf : ∀ f : MeasureTheory.Lp ℂ 2 MeasureTheory.volume, S f = F.symm (T (F f)) := by
    intro f; rfl
  -- `T` is an isometry of `L²`: its symbol is unimodular a.e.
  have hTnorm_eq : ∀ g : MeasureTheory.Lp ℂ 2 MeasureTheory.volume, ‖T g‖ = ‖g‖ := by
    intro g
    have hnorm : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
        ‖((T g : MeasureTheory.Lp ℂ 2 MeasureTheory.volume) : ℂ → ℂ) ξ‖ = ‖(g : ℂ → ℂ) ξ‖ := by
      filter_upwards [hT g, ae_norm_beurlingSymbol] with ξ h1 h2
      rw [h1, norm_mul, h2, one_mul]
    exact le_antisymm
      (MeasureTheory.Lp.norm_le_norm_of_ae_le
        (by filter_upwards [hnorm] with ξ h; exact le_of_eq h))
      (MeasureTheory.Lp.norm_le_norm_of_ae_le
        (by filter_upwards [hnorm] with ξ h; exact le_of_eq h.symm))
  refine ⟨S, ?_, ?_⟩
  · -- `S = 𝓕⁻¹ ∘ T ∘ 𝓕` is an isometry as a composition of isometries.
    intro f
    rw [hSf f, LinearIsometryEquiv.norm_map, hTnorm_eq, LinearIsometryEquiv.norm_map]
  · -- The Fourier transform intertwines `S` with multiplication by the symbol.
    intro f
    have hFS : F (S f) = T (F f) := by
      rw [hSf f]
      exact LinearIsometryEquiv.apply_symm_apply F (T (F f))
    rw [hFS]
    exact hT (F f)

end Work.MRMT.Beurling
