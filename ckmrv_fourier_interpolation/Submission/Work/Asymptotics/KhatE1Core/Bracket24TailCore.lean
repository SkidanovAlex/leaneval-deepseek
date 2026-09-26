import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2PrimeDefs
import Submission.Work.Asymptotics.KhatE1.ShBracketAux
import Submission.Work.Asymptotics.KMFDDefs
import Submission.Work.Asymptotics.KhatE1.Kdev24Base

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

/-!
# The `Sh`-cleared `d = 24` bracket: the two-group splitting

The cleared bracket of `KhatE1.Sh_mul_Bracket24` is a sum of

* the `K₊`-group `- c z² (Sm1 + … + Sm5)`, and
* the `K₋`-group `(3456π)⁻¹ (brMinus + Sh·br0 - Sh·Ept z·(E1combo24 + Am24))`,

the `R24`-terms having cancelled against `Sh·Tref24 = Sh·Ept z·R24 = brMinus + Sh·br0 - Sh·Dev24Sum`.
The second group is `(3456π)⁻¹` times the reference bracket `kmfd_BR + kmfd_dev` minus
`Sh·Ept z·(E1combo24+Am24)`.

This module records the splitting (`Sh_mul_Bracket24_master`) and reduces the requested tail
bound `Bracket24Tail'` to a bound on the two groups.
-/

noncomputable section

/-- The `K₊`-group of the `Sh`-cleared `d = 24` bracket. -/
def KPlus24Group (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2
      * (Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
          + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
          + Work.Asymptotics.K24F.Sm5 τ z))

/-- The `K₋`-group of the `Sh`-cleared `d = 24` bracket. -/
def KMinus24Group (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
    * (Work.Asymptotics.Compact.brMinus ℓ 24 τ z
        + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 24 ℓ τ z
        - Work.Asymptotics.Compact.Sh τ z * Work.Residues.Ept z
            * (Work.Asymptotics.E1combo24 ℓ τ + Work.Asymptotics.KhatE1.Am24 ℓ τ))

/-- The same group with the bracket replaced by its reference-plus-deviation form
`kmfd_BR + kmfd_dev`. -/
def KMinus24Group' (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
    * (Work.Asymptotics.kmfd_BR ℓ τ z + Work.Asymptotics.kmfd_dev ℓ τ z
        - Work.Asymptotics.Compact.Sh τ z * Work.Residues.Ept z
            * (Work.Asymptotics.E1combo24 ℓ τ + Work.Asymptotics.KhatE1.Am24 ℓ τ))

theorem KMinus24Group_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    KMinus24Group ℓ τ z = KMinus24Group' ℓ τ z := by
  rw [KMinus24Group, KMinus24Group', Work.Asymptotics.kmfd_bracket_decomp]

/-- **The master splitting**: the `Sh`-cleared bracket is the sum of the `K₊`- and `K₋`-groups. -/
theorem Sh_mul_Bracket24_master (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hE4 : Work.Kernels.E4Fun z ≠ 0) (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.KhatE1.Bracket24 ℓ τ z
      = KPlus24Group ℓ τ z + KMinus24Group ℓ τ z := by
  have hDev : Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.Dev24Sum ℓ τ z
      = Work.Asymptotics.Compact.brMinus ℓ 24 τ z
        + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 24 ℓ τ z
        - Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.Tref24 ℓ τ z := by
    have h3 : Work.Asymptotics.Compact.Sh τ z
        * ((Work.Asymptotics.Compact.Sh τ z)⁻¹
            * (Work.Asymptotics.Compact.brMinus ℓ 24 τ z
              + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 24 ℓ τ z))
        = Work.Asymptotics.Compact.Sh τ z
            * (Work.Asymptotics.Compact.Tref24 ℓ τ z
              + Work.Asymptotics.Compact.Dev24Sum ℓ τ z) := by
      rw [Work.Asymptotics.Compact.decomp24_sum ℓ τ z hSh]
    rw [← mul_assoc, mul_inv_cancel₀ hSh, one_mul, mul_add] at h3
    rw [h3]; ring
  have hTref : Work.Residues.Ept z * Work.Asymptotics.Compact.R24 ℓ τ z
      = Work.Asymptotics.Compact.Tref24 ℓ τ z := (Work.Asymptotics.Compact.Tref24_eq ℓ τ z).symm
  have hRp0 : Work.Asymptotics.Compact.R24_p0 ℓ τ = Work.Asymptotics.E1combo24 ℓ τ :=
    Work.Asymptotics.KhatE1.R24_p0_eq_e1combo24' ℓ τ
  have hinner : Work.Asymptotics.Compact.Sh τ z
        * (Work.Residues.Ept z
            * (Work.Asymptotics.Compact.R24 ℓ τ z - Work.Asymptotics.Compact.R24_p0 ℓ τ)
          + Work.Asymptotics.Compact.Dev24Sum ℓ τ z
          - Work.Asymptotics.KhatE1.Am24 ℓ τ * Work.Residues.Ept z)
      = Work.Asymptotics.Compact.brMinus ℓ 24 τ z
        + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 24 ℓ τ z
        - Work.Asymptotics.Compact.Sh τ z * Work.Residues.Ept z
            * (Work.Asymptotics.E1combo24 ℓ τ + Work.Asymptotics.KhatE1.Am24 ℓ τ) := by
    have h1 : Work.Residues.Ept z
        * (Work.Asymptotics.Compact.R24 ℓ τ z - Work.Asymptotics.Compact.R24_p0 ℓ τ)
        = Work.Asymptotics.Compact.Tref24 ℓ τ z
          - Work.Residues.Ept z * Work.Asymptotics.E1combo24 ℓ τ := by
      rw [mul_sub, hTref, hRp0]
    rw [h1]
    linear_combination hDev
  have hbase := Work.Asymptotics.KhatE1.Sh_mul_Bracket24 ℓ τ z hE4 hSh
  rw [hbase, KPlus24Group, KMinus24Group]
  calc -(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2
          * (Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
              + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
              + Work.Asymptotics.K24F.Sm5 τ z))
        + Work.Asymptotics.Compact.Sh τ z
            * (((3456 : ℂ) * (Real.pi : ℂ))⁻¹
                * (Work.Residues.Ept z
                    * (Work.Asymptotics.Compact.R24 ℓ τ z
                      - Work.Asymptotics.Compact.R24_p0 ℓ τ)
                  + Work.Asymptotics.Compact.Dev24Sum ℓ τ z
                  - Work.Asymptotics.KhatE1.Am24 ℓ τ * Work.Residues.Ept z))
      = -(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2
          * (Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
              + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
              + Work.Asymptotics.K24F.Sm5 τ z))
        + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * (Work.Asymptotics.Compact.Sh τ z
            * (Work.Residues.Ept z
                * (Work.Asymptotics.Compact.R24 ℓ τ z
                  - Work.Asymptotics.Compact.R24_p0 ℓ τ)
              + Work.Asymptotics.Compact.Dev24Sum ℓ τ z
              - Work.Asymptotics.KhatE1.Am24 ℓ τ * Work.Residues.Ept z)) := by ring
    _ = _ := by rw [hinner]

/-- `E₄ z ≠ 0` on the funnel strip. -/
theorem E4_ne_zero_strip (τ z : ℍ) (t : ℝ) (hF : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ t) (hz : z.im = t) : Work.Kernels.E4Fun z ≠ 0 := by
  have hz3 : (3 : ℝ) ≤ z.im := by have := Work.Asymptotics.Funnel.im_two hF; rw [hz]; linarith
  have h := Work.FunnelNumerics.E4_funnel_bounds.2 z hz3
  intro h0
  rw [h0, norm_zero] at h
  linarith

/-- **The core obligation in the split form**: the bound on the sum of the two groups after
subtracting the explicit `E(z)²`-coefficient. -/
def Bracket24TailCore (ℓ : Work.Kernels.LogLambdaData) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖KPlus24Group ℓ τ z + KMinus24Group ℓ τ z
          - (Work.Residues.Ept z) ^ 2 * Bracket24E2' ℓ τ z‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp (-(2 * Real.pi * t))

/-- **The split form implies the tail bound.** -/
theorem Bracket24Tail'_of_core (ℓ : Work.Kernels.LogLambdaData)
    (h : Bracket24TailCore ℓ) : Bracket24Tail' ℓ := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, ?_⟩
  intro τ z t hF ht hz0 hz1 hzim
  have hE4 : Work.Kernels.E4Fun z ≠ 0 := E4_ne_zero_strip τ z t hF ht hzim
  have hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0 := by
    have htz : τ.im + 1 ≤ z.im := by rw [hzim]; exact ht
    exact Work.Asymptotics.KhatE1.Sh_ne_zero_strip τ z hF htz
  rw [Sh_mul_Bracket24_master ℓ τ z hE4 hSh]
  exact hb τ z t hF ht hz0 hz1 hzim

end

end Work.Asymptotics.KhatE1Core
