import Mathlib
import Submission.Work.Asymptotics.KhatE1.ZAtomsSecondOrder
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresZAtoms

/-!
# High-order truncations of the `z`-atoms of the sharp `8`-dimensional residual

`ZAtomsSecondOrder` already contains the four "high-order" expansions of the `z`-atoms that
the sharp `8`-dimensional residual needs:

* `E4sqThirdOrder`  : `E₄(z)²  = 1 + 480 q(z) + 61920 q(z)² + O(‖q(z)‖³)`,
* `E4E6ThirdOrder`  : `E₄E₆(z) = 1 - 264 q(z) - 135432 q(z)² + O(‖q(z)‖³)`,
* `WfunSixthH`      : `W(z)    = 1 - 8u + 24u² - 32u³ + 24u⁴ - 48u⁵ + O(‖u‖⁶)`,
* `UVSqSixthH`      : `(U²-V²)(z) = 1 + 16u - 144u² + 448u³ - 912u⁴ + 2016u⁵ + O(‖u‖⁶)`,

where `q(z) = qParamFun z = e^{2πiz}` and `u = Ept z = e^{πiz}` (so `q = u²`).

The first two are stated there in the `IsSmallT 1 · 3` vocabulary (`O(‖q‖³)` on `{1 ≤ Im z}`),
the last two in the `IsSmH 6 ·` vocabulary (`O(‖u‖⁶)` on `{1 ≤ Im z}`, with the threshold already
normalised to `1`).  All four are of the *exact* shape requested --- same norm, same truncation
polynomial, same power of `q` / `u` --- up to the single substitution `q = u²` (and one
`ring`-normalisation of the polynomial).  This file performs those rewrites so that the target
type is met literally.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `E₄(z)² = 1 + 480 q(z) + 61920 q(z)² + O(‖q(z)‖³)`. -/
theorem E4sq_highTrunc :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖(Work.Kernels.E4Fun z) ^ 2
            - (1 + 480 * Work.Kernels.qParamFun z
                + 61920 * (Work.Kernels.qParamFun z) ^ 2)‖
          ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, hf⟩ := E4sqThirdOrder
  refine ⟨1, C, le_refl 1, hC, fun z hz => ?_⟩
  have h := hf z hz
  change ‖Work.Kernels.E4Fun z ^ 2 - 1 - 480 * Work.Kernels.qParamFun z
      - 61920 * (Work.Kernels.qParamFun z) ^ 2‖
      ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 at h
  have htrunc : Work.Kernels.E4Fun z ^ 2 - 1 - 480 * Work.Kernels.qParamFun z
      - 61920 * (Work.Kernels.qParamFun z) ^ 2
      = Work.Kernels.E4Fun z ^ 2 - (1 + 480 * Work.Kernels.qParamFun z
          + 61920 * (Work.Kernels.qParamFun z) ^ 2) := by ring
  rwa [htrunc] at h

/-- `E₄E₆(z) = 1 - 264 q(z) - 135432 q(z)² + O(‖q(z)‖³)`. -/
theorem E4E6_highTrunc :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖Work.Kernels.E4Fun z * Work.Kernels.E6Fun z
            - (1 - 264 * Work.Kernels.qParamFun z
                - 135432 * (Work.Kernels.qParamFun z) ^ 2)‖
          ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, hf⟩ := E4E6ThirdOrder
  refine ⟨1, C, le_refl 1, hC, fun z hz => ?_⟩
  have h := hf z hz
  change ‖Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - 1
      + 264 * Work.Kernels.qParamFun z
      + 135432 * (Work.Kernels.qParamFun z) ^ 2‖
      ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 at h
  have htrunc : Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - 1
      + 264 * Work.Kernels.qParamFun z
      + 135432 * (Work.Kernels.qParamFun z) ^ 2
      = Work.Kernels.E4Fun z * Work.Kernels.E6Fun z
          - (1 - 264 * Work.Kernels.qParamFun z
              - 135432 * (Work.Kernels.qParamFun z) ^ 2) := by ring
  rwa [htrunc] at h

/-- `W(z) = 1 - 8u + 24q - 32u³ + 24q² - 48u⁵ + O(‖u‖⁶)`, where `u = Ept z` and
`q = qParamFun z = u²`. -/
theorem Wfun_highTrunc :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖Work.Kernels.WFun z
            - (1 - 8 * Work.Residues.Ept z
                + 24 * Work.Kernels.qParamFun z
                - 32 * (Work.Residues.Ept z) ^ 3
                + 24 * (Work.Kernels.qParamFun z) ^ 2
                - 48 * (Work.Residues.Ept z) ^ 5)‖
          ≤ C * ‖Work.Residues.Ept z‖ ^ 6 := by
  obtain ⟨C, hC, hf⟩ := WfunSixthH
  refine ⟨1, C, le_refl 1, hC, fun z hz => ?_⟩
  have h := hf z hz
  change ‖Work.Kernels.WFun z
      - (1 - 8 * Work.Residues.Ept z + 24 * (Work.Residues.Ept z) ^ 2
          - 32 * (Work.Residues.Ept z) ^ 3 + 24 * (Work.Residues.Ept z) ^ 4
          - 48 * (Work.Residues.Ept z) ^ 5)‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 6 at h
  have htrunc : (1 : ℂ) - 8 * Work.Residues.Ept z
      + 24 * Work.Kernels.qParamFun z - 32 * (Work.Residues.Ept z) ^ 3
      + 24 * (Work.Kernels.qParamFun z) ^ 2 - 48 * (Work.Residues.Ept z) ^ 5
      = 1 - 8 * Work.Residues.Ept z + 24 * (Work.Residues.Ept z) ^ 2
          - 32 * (Work.Residues.Ept z) ^ 3 + 24 * (Work.Residues.Ept z) ^ 4
          - 48 * (Work.Residues.Ept z) ^ 5 := by
    rw [show Work.Kernels.qParamFun z = (Work.Residues.Ept z) ^ 2 from
      Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
    ring
  rw [htrunc]
  exact h

/-- `(U²-V²)(z) = 1 + 16u - 144q + 448u³ - 912q² + 2016u⁵ + O(‖u‖⁶)`, where `u = Ept z` and
`q = qParamFun z = u²`. -/
theorem UVsq_highTrunc :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖(Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
            - (1 + 16 * Work.Residues.Ept z
                - 144 * Work.Kernels.qParamFun z
                + 448 * (Work.Residues.Ept z) ^ 3
                - 912 * (Work.Kernels.qParamFun z) ^ 2
                + 2016 * (Work.Residues.Ept z) ^ 5)‖
          ≤ C * ‖Work.Residues.Ept z‖ ^ 6 := by
  obtain ⟨C, hC, hf⟩ := UVSqSixthH
  refine ⟨1, C, le_refl 1, hC, fun z hz => ?_⟩
  have h := hf z hz
  change ‖(Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
      - (1 + 16 * Work.Residues.Ept z - 144 * (Work.Residues.Ept z) ^ 2
          + 448 * (Work.Residues.Ept z) ^ 3 - 912 * (Work.Residues.Ept z) ^ 4
          + 2016 * (Work.Residues.Ept z) ^ 5)‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 6 at h
  have htrunc : (1 : ℂ) + 16 * Work.Residues.Ept z
      - 144 * Work.Kernels.qParamFun z + 448 * (Work.Residues.Ept z) ^ 3
      - 912 * (Work.Kernels.qParamFun z) ^ 2 + 2016 * (Work.Residues.Ept z) ^ 5
      = 1 + 16 * Work.Residues.Ept z - 144 * (Work.Residues.Ept z) ^ 2
          + 448 * (Work.Residues.Ept z) ^ 3 - 912 * (Work.Residues.Ept z) ^ 4
          + 2016 * (Work.Residues.Ept z) ^ 5 := by
    rw [show Work.Kernels.qParamFun z = (Work.Residues.Ept z) ^ 2 from
      Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
    ring
  rw [htrunc]
  exact h

/-- The four high-order truncations of the `z`-atoms, in the literal shape consumed by the
floor computation. -/
theorem Kdev8WresHighTrunc :
    (∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖(Work.Kernels.E4Fun z) ^ 2
            - (1 + 480 * Work.Kernels.qParamFun z
                + 61920 * (Work.Kernels.qParamFun z) ^ 2)‖
          ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3)
    ∧ (∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖Work.Kernels.E4Fun z * Work.Kernels.E6Fun z
            - (1 - 264 * Work.Kernels.qParamFun z
                - 135432 * (Work.Kernels.qParamFun z) ^ 2)‖
          ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3)
    ∧ (∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖Work.Kernels.WFun z
            - (1 - 8 * Work.Residues.Ept z
                + 24 * Work.Kernels.qParamFun z
                - 32 * (Work.Residues.Ept z) ^ 3
                + 24 * (Work.Kernels.qParamFun z) ^ 2
                - 48 * (Work.Residues.Ept z) ^ 5)‖
          ≤ C * ‖Work.Residues.Ept z‖ ^ 6)
    ∧ (∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖(Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
            - (1 + 16 * Work.Residues.Ept z
                - 144 * Work.Kernels.qParamFun z
                + 448 * (Work.Residues.Ept z) ^ 3
                - 912 * (Work.Kernels.qParamFun z) ^ 2
                + 2016 * (Work.Residues.Ept z) ^ 5)‖
          ≤ C * ‖Work.Residues.Ept z‖ ^ 6) :=
  ⟨E4sq_highTrunc, E4E6_highTrunc, Wfun_highTrunc, UVsq_highTrunc⟩

end

end Work.Asymptotics.KhatE1
