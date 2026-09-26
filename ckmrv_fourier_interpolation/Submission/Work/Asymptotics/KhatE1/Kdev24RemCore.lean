import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Asymptotics.KhatE1.Kdev24Base
import Submission.Work.Asymptotics.KhatE1.Kdev24Lead

/-!
# The sharp remainder of the funnel deviation in dimension `24`

The target `Kdev24RemCore` bounds the sharp remainder of the `d = 24` funnel deviation
`Kdev ℓ 24 τ z = K̂^{(24)}(τ,z) - (𝒢₊^{(24)} - 𝒢₋^{(24)})/2` after its leading `E(z)¹`-term
`KdevLead24 ℓ τ · Ept z` has been subtracted, where

* `E(z) = Ept z` and `KdevLead24 ℓ τ = (E1combo24 ℓ τ + Am24 ℓ τ)/(6912π)`,
* `E1combo24 = Compact.R24_p0` is the `E(z)¹`-coefficient of the `K₋`-reference bracket
  (`KhatE1.R24_p0_eq_e1combo24'`, `KhatE1.E1combo24_bound`), and
* `Am24 ℓ τ = -73728 Δ(τ) - 384 (ψ₂(τ)E₁₀(τ) - ψ₄(τ)E₈(τ))` is the `E(z)¹`-coefficient of the
  `K₋`-side deviation sum `Dev24Sum` (`(Sh)⁻¹(br + Sh·br0) = Tref24 + Dev24Sum`,
  `KhatE1.Dev24Sum_E1`).

The definitions, the coefficient bounds and the exact splitting `Kdev24RemCore_key` (the
target's left-hand side is `2 · (Kdev ℓ 24 τ z - KdevLead24 ℓ τ · Ept z)` on the strip) live in
`KhatE1/Kdev24Base.lean`; the sharp remainder statement `Kdev24LeadProp` is proved in
`KhatE1/Kdev24Lead.lean` (through the `Sh`-cleared `d = 24` chain
`KhatE1Core/Bracket24SharpCleared_hold`, `KhatE1Core/Bracket24TailCore_proof`,
`KhatE1/Bracket24E2Prime_bound`, …), and the target follows from it by the reduction
`Kdev24RemCore_of_lead`.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- **The sharp remainder statement** for the `d = 24` funnel deviation: `Kdev ℓ 24 τ z` differs
from its leading term `KdevLead24 ℓ τ · Ept z` by `O(‖q(τ)‖ (scale τ)^N (1+t)^M e^{-2πt})` on the
funnel strip.  This is the single remaining ingredient of `Kdev24RemCore`. -/
def Kdev24LeadProp (ℓ : Work.Kernels.LogLambdaData) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖Work.Asymptotics.Kdev ℓ 24 τ z - KdevLead24 ℓ τ * Work.Residues.Ept z‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp (-(2 * Real.pi * t))

/-- **The reduction of the target to the sharp remainder statement.**  Given `Kdev24LeadProp`,
the target `Kdev24RemCore` follows by the exact identity `Kdev24RemCore_key`. -/
theorem Kdev24RemCore_of_lead (ℓ : Work.Kernels.LogLambdaData) (h : Kdev24LeadProp ℓ) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖(Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z)
          + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
              (Work.Residues.Ept z * (Work.Asymptotics.Compact.R24 ℓ τ z
                  - Work.Asymptotics.Compact.R24_p0 ℓ τ)
                + Work.Asymptotics.Compact.Dev24Sum ℓ τ z
                - (-73728 * Work.Kernels.DeltaFun τ
                    - 384 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
                              - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ))
                  * Work.Residues.Ept z)‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨2 * C, N, M, by positivity, hN, hM, ?_⟩
  intro τ z t hF ht hz0 hz1 hzim
  have hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0 :=
    Sh_ne_zero_of_im_ge' τ z hF.2 (by rw [hzim]; exact ht)
  have hkey := Kdev24RemCore_key ℓ τ z hSh
  have hAm : (-73728 * Work.Kernels.DeltaFun τ
        - 384 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
            - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ)) = Am24 ℓ τ := rfl
  rw [hAm, hkey]
  have hcore := hb τ z t hF ht hz0 hz1 hzim
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [norm_mul, h2]
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hs0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
    Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N
  have h1t : (0 : ℝ) ≤ 1 + t := by have := hF.2; linarith
  have hM0 : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg h1t M
  have he0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
  have hbase : (0 : ℝ) ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t)) := by positivity
  calc 2 * ‖Work.Asymptotics.Kdev ℓ 24 τ z - KdevLead24 ℓ τ * Work.Residues.Ept z‖
      ≤ 2 * (C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp (-(2 * Real.pi * t))) := by linarith
    _ = 2 * C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(2 * Real.pi * t)) := by ring

/-- **The target.**  The sharp remainder of the `d = 24` funnel deviation, in the explicit
bracket form: the left-hand side is `2 · (Kdev - KdevLead24 · Ept z)` (`Kdev24RemCore_key`), and
the bound is the sharp remainder statement `Kdev24LeadProp`.

The proof is `Kdev24RemCore_of_lead` applied to the sibling theorem
`KhatE1.Kdev24Lead` (module `Submission.Work.Asymptotics.KhatE1.Kdev24Lead`), which proves
`Kdev24LeadProp ℓ` for every `ℓ`. -/
theorem Kdev24RemCore (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖(Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z)
          + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
              (Work.Residues.Ept z * (Work.Asymptotics.Compact.R24 ℓ τ z
                  - Work.Asymptotics.Compact.R24_p0 ℓ τ)
                + Work.Asymptotics.Compact.Dev24Sum ℓ τ z
                - (-73728 * Work.Kernels.DeltaFun τ
                    - 384 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
                              - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ))
                  * Work.Residues.Ept z)‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) :=
  Kdev24RemCore_of_lead ℓ (Kdev24Lead ℓ)

end

end Work.Asymptotics.KhatE1
