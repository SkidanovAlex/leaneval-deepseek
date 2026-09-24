import Mathlib
import Submission.Work.GM.Affine.FarMass_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.farEst_v2_aux

/-!
# GM §9, region II, far part: the sharp `M₃ ≤ Mbig` estimate (`supf`-form)

This is `Work.GM.Affine.far_est_M3_le_Mbig` (v1) with the extra hypothesis `supf f ≤ Λ` — the
honest `supf`-form of GM's Fourier-decay hypothesis, since the bare `Λ`-form of v1 is false for
narrow needles (see `NOTES_T1_BOUND_defect.md`).

The mathematical content (the sharp far estimate of GM §9 region II) is established in
`Work.GM.Affine.farEst_v2_aux`, which combines:

* the far-mass/window-mass comparison `FarMass K f M₂ M₃ ≤ C · WinMass f M₂ M₃`
  (`bsum_far_le_winmass`, proved via the trigonometric far-sampling crux
  `far_sampling_crux_fixed` and the assembly `winmass_reduction`);
* a coherence-aware treatment of the far pairs `(m₁, ℓ)` of the expansion
  `ghatFar ξ = Σ_{m₁∈R1} |m₁|⁻¹ Bsum(ξ/m₁) Wfar(ξ/m₁)` — the naive Cauchy–Schwarz over the
  far pairs would give the (false) sharp bound `C T^ε (M₁+M₃) FarMass`, because the far
  `m₁`-sum is coherent; the correct treatment accounts for the coherence gain, which the
  far-mass/window-mass comparison cancels.  See
  `Submission/Work/GM/Affine/NOTES_far_est_v2_COHERENCE.md` for the full analysis.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

theorem far_est_M3_le_Mbig_v2 {C₀ K T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        supf f ≤ Λ →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        1 ≤ Mbig → 1 ≤ M₃ → 0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → M₃ ≤ Mbig →
        Mbig ≤ T ^ 4 →
        (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
            \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
            ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ :=
  farEst_v2_aux (C₀ := C₀) (K := K) (T₀ := T₀) hC₀ hK hT₀ c δ hδ

end Work.GM.Affine
