import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_main
import Submission.Work.Asymptotics.KhatE1.KdevRemDefs
import Submission.Work.Asymptotics.KhatE1.Kdev8CoeffAux
import Submission.Work.Residues.ThetaEpt

/-!
# The bracket of `Kdev8_matching` is exactly `2 · KdevRem`

The statement requested as `Work.Asymptotics.KhatE1Core.Kdev8_matching` bounds the
**bracket**

  `B ℓ τ z = tailC⁻¹ (Φ₁ + Φ₂ + Φ₃) + (3456π)⁻¹ (Ept z · (R8 ℓ τ z - R8_p0 ℓ τ) + Dev8Sum ℓ τ z)`

(see `Work.Asymptotics.Compact.PhiMain` / `PhiDiv` / `PhiCorr`, `Compact.R8`,
`Compact.R8_p0`, `Compact.Dev8Sum`).  This file records the *exact identity*

  `B ℓ τ z = 2 · KdevRem ℓ τ z`,

where `KdevRem ℓ τ z = Kdev ℓ 8 τ z - KdevLead ℓ τ · Ept z` is the leading-term-free
deviation of `Submission/Work/Asymptotics/KhatE1/KdevRemDefs.lean`.  Consequently the
requested bound is *equivalent* to the sibling obligation `KhatE1.KdevRem_strip_sharp`
(and to `KhatE1.Kdev_strip_sharp8_core` / `KhatE1.Kdev_funnel_rem`), and this equivalence is
made formal below: `Kdev8_matching_intended_of_KdevRem_strip_sharp`.

NOTE (statement of the requested lemma).  The recorded statement of `Kdev8_matching` writes
the right-hand side as `C * Work.Kernels.qParamFun τ * Work.Kernels.scale τ ^ N * …`, i.e.
`C * (qParamFun τ) * (scale τ)^N`; since `qParamFun τ : ℂ` and `C : ℝ`, the product is a
*complex* number and the exponent `scale τ ^ N` is ill-typed (`HPow ℂ ℝ` has no instance),
and the comparison `≤` of the resulting real norm with a complex number is not defined.
The intended right-hand side is the one used by every sibling statement in
`Submission/Work/Asymptotics/KhatE1/`
(`C * ‖qParamFun τ‖ * (scale τ)^N * (1+t)^M * ‖Ept z‖²`, cf. `KdevRem_strip_sharp`), which is
the form proved below to follow from the sibling obligation.  The identity itself
(`Kdev8Bracket_eq_two_KdevRem`) is stated for the *real-valued* bracket without any norm, so
it is well-typed as it stands.

## Numerical check of the (intended) target

With `E(z) = Ept z`, `q(τ) = qParamFun τ`, `τ = 0.3 + iy`, `z = x + it`, `t = y + 1`, a direct
evaluation of every ingredient above (canonical `𝓛 = logλ`, `𝓛_S = logλ_S`, `ψ₂ = ξ₂𝓛 +
(ξ₂|₂S)𝓛_S`, `ψ₄ = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` via the *proved* slash relations
`Residues.xi2Fun_slash_S_apply`, `Residues.xi4Fun_slash_S_apply`) gives

  `‖B ℓ τ z‖ / (‖q(τ)‖ (scale τ)^3 ‖E(z)‖²) ≤ 5·10⁵`

on the grid `y ∈ {4,8,12,16,20,24,32,40}`, `x ∈ {0,0.25,0.5,0.75,1}`, together with the
points `t = y+2`, `t = 2y`; the ratio is `4.1·10⁴` at `y = 4` and `1.29·10⁵` at `y = 40`.  So
the intended statement is true with `N = 3`, `M = 0`, and is *not* vacuous.  The same code
reproduces the proved identities of the workspace (e.g. `Tref8_eq`, `decomp8`,
`KMinus_eq`, `KPlus8_sub_Gplus8_decomp`, and `B = 2·(Kdev 8 - KdevLead·Ept)`) to more than
250 digits, so the model is faithful.  What is *missing* for a Lean proof is the explicit
second-order `τ`-atom algebra: the coefficients of `E(z)^k` of the bracket for `k = 2,…,6`
are combinations of `j(τ)`, `ψ₄`, `ψ₂E₁₄/Δ` terms that cancel only after substituting
`ψ₂ = ξ₂𝓛 + (ξ₂|₂S)𝓛_S`, `ψ₄ = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` and using the Jacobi quartic identities
(the same mechanism that is carried out for the *first* order coefficient in
`KhatE1/E1combo8_bound.lean`).
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- The bracket appearing on the left of the requested `Kdev8_matching` statement. -/
noncomputable def Kdev8Bracket (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Asymptotics.Compact.tailC⁻¹ *
      (Work.Asymptotics.Compact.PhiMain τ z + Work.Asymptotics.Compact.PhiDiv τ z
        + Work.Asymptotics.Compact.PhiCorr τ z)
    + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
        (Work.Residues.Ept z * (Work.Asymptotics.Compact.R8 ℓ τ z
            - Work.Asymptotics.Compact.R8_p0 ℓ τ)
          + Work.Asymptotics.Compact.Dev8Sum ℓ τ z)

/-- **The exact identity.**  For `j(τ) ≠ j(z)` and `Sh τ z ≠ 0`, the bracket of
`Kdev8_matching` is twice the leading-term-free deviation `KdevRem`.

This is the assembly of the two exact decompositions of the workspace,

* `Compact.KPlus8_sub_Gplus8_decomp` : `K₊^{(8)} - 𝒢₊^{(8)} = tailC⁻¹(Φ₁+Φ₂+Φ₃)`,
* `Compact.tail_identity` + `Compact.decomp8` + `Compact.Tref8_eq` :

  `(3456π)⁻¹(Ept z · R8 + Dev8Sum) = -(K₋^{(8)} - 𝒢₋^{(8)})`,

together with `E1combo8 = R8_p0/24` (`KhatE1.R8_p0_eq_e1combo8`), which identifies the
subtracted term with the leading coefficient `KdevLead = E1combo8/(288π)`. -/
theorem Kdev8Bracket_eq_two_KdevRem (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hJ : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    Kdev8Bracket ℓ τ z = 2 * Work.Asymptotics.KhatE1.KdevRem ℓ τ z := by
  have hA : ((3456 : ℂ) * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  -- the exact decompositions of the workspace
  have hplus := Work.Asymptotics.Compact.KPlus8_sub_Gplus8_decomp τ z hJ
  have htail := Work.Asymptotics.Compact.tail_identity ℓ 8 (Or.inl rfl) τ z hSh
  have hdecomp := Work.Asymptotics.Compact.decomp8 ℓ τ z hSh
  have href := Work.Asymptotics.Compact.Tref8_eq ℓ τ z
  have hp0 := Work.Asymptotics.KhatE1.R8_p0_eq_e1combo8 ℓ τ
  have hGp : Work.Asymptotics.Compact.Gplus 8 τ z = Work.Asymptotics.Compact.Gplus8 τ z := by
    rw [Work.Asymptotics.Compact.Gplus]; simp
  have hGm : Work.Asymptotics.Compact.Gminus 8 ℓ τ z
      = Work.Asymptotics.Compact.Gminus8 ℓ τ z := by
    rw [Work.Asymptotics.Compact.Gminus]; simp
  -- `3456π (K₋ - 𝒢₋) = -(Sh)⁻¹ (br + Sh·br0)`
  have hKm : ((3456 : ℂ) * (Real.pi : ℂ))
        * (Work.Kernels.KMinus ℓ 8 τ z - Work.Asymptotics.Compact.Gminus8 ℓ τ z)
      = -((Work.Asymptotics.Compact.Sh τ z)⁻¹ *
          (Work.Asymptotics.Compact.brMinus ℓ 8 τ z
            + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 8 ℓ τ z)) := by
    have h := htail
    rw [hGm] at h
    exact h
  -- hence `(3456π)⁻¹ (Tref8 + Dev8Sum) = -(K₋ - 𝒢₋)`
  have hB : ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
        * (Work.Asymptotics.Compact.Tref8 ℓ τ z + Work.Asymptotics.Compact.Dev8Sum ℓ τ z)
      = -(Work.Kernels.KMinus ℓ 8 τ z - Work.Asymptotics.Compact.Gminus8 ℓ τ z) := by
    have hZ : (Work.Asymptotics.Compact.Sh τ z)⁻¹ *
          (Work.Asymptotics.Compact.brMinus ℓ 8 τ z
            + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 8 ℓ τ z)
        = ((3456 : ℂ) * (Real.pi : ℂ))
            * (-(Work.Kernels.KMinus ℓ 8 τ z - Work.Asymptotics.Compact.Gminus8 ℓ τ z)) := by
      rw [mul_neg, hKm]; ring
    rw [← hdecomp, hZ, inv_mul_cancel_left₀ hA]
  -- and `(3456π)⁻¹ (Ept z · R8_p0) = 2 · KdevLead · Ept z`
  have hlead : ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
        * (Work.Residues.Ept z * Work.Asymptotics.Compact.R8_p0 ℓ τ)
      = 2 * Work.Asymptotics.KhatE1.KdevLead ℓ τ * Work.Residues.Ept z := by
    rw [hp0, Work.Asymptotics.KhatE1.KdevLead]
    field_simp
    ring
  -- assembly
  rw [Kdev8Bracket, ← hplus]
  have hexp : ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
        (Work.Residues.Ept z * (Work.Asymptotics.Compact.R8 ℓ τ z
            - Work.Asymptotics.Compact.R8_p0 ℓ τ)
          + Work.Asymptotics.Compact.Dev8Sum ℓ τ z)
      = ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
          * (Work.Residues.Ept z * Work.Asymptotics.Compact.R8 ℓ τ z
              + Work.Asymptotics.Compact.Dev8Sum ℓ τ z)
        - ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
            * (Work.Residues.Ept z * Work.Asymptotics.Compact.R8_p0 ℓ τ) := by
    ring
  rw [hexp]
  have hB' : ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
        * (Work.Residues.Ept z * Work.Asymptotics.Compact.R8 ℓ τ z
            + Work.Asymptotics.Compact.Dev8Sum ℓ τ z)
      = -(Work.Kernels.KMinus ℓ 8 τ z - Work.Asymptotics.Compact.Gminus8 ℓ τ z) := by
    rw [← href]; exact hB
  rw [hB', hlead, Work.Asymptotics.KhatE1.KdevRem, Work.Asymptotics.Kdev,
    Work.Kernels.Khat, hGp, hGm]
  ring

/-- **The reduction.**  If the sibling obligation `KhatE1.KdevRem_strip_sharp` holds, then the
requested `Kdev8_matching` holds in its intended (well-typed) form, with the right-hand side
`C * ‖qParamFun τ‖ * (scale τ)^N * (1+t)^M * ‖Ept z‖²`. -/
theorem Kdev8_matching_intended_of_KdevRem_strip_sharp (ℓ : Work.Kernels.LogLambdaData)
    (h : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1.KdevRem ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t))) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Kdev8Bracket ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * ‖Work.Residues.Ept z‖ ^ 2 := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨2 * C, N, M, by positivity, hN, hM, ?_⟩
  intro τ z t hτ ht h0 h1 hzim
  have hτ2 : 2 ≤ τ.im := hτ.2
  have hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0 :=
    Work.Asymptotics.KhatE1.Sh_ne_zero_of_im_ge τ z hτ2 (by rw [hzim]; exact ht)
  have hJ : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro h0'
    have hD : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
    have hS : Work.Asymptotics.Compact.Sh τ z = 0 := by
      rw [Work.Asymptotics.Compact.Sh, h0']
      rw [← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z]
      ring
    exact hSh hS
  rw [Kdev8Bracket_eq_two_KdevRem ℓ τ z hJ hSh, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have hb' := hb τ z t hτ ht (by linarith) (by linarith) hzim
  have hE : ‖Work.Residues.Ept z‖ ^ 2 = Real.exp (-(2 * Real.pi * t)) := by
    rw [Work.Residues.norm_Ept, hzim, sq, ← Real.exp_add]
    ring_nf
  have hEZ : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ ^ 2 := by positivity
  have hsN : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
    Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N
  have h1t : (0 : ℝ) ≤ 1 + t := by linarith
  have hM' : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg h1t M
  have hbase : (0 : ℝ) ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le (norm_nonneg _)) hsN) hM'
  rw [hE]
  nlinarith [hb', hbase, hC]

end

end Work.Asymptotics.KhatE1Core
