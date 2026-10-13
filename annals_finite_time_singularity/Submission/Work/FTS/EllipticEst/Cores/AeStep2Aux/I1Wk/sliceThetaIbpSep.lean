import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_trunc
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_identity
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.SliceThetaIbpDefs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.hasDerivAt_Gfun
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.intervalIntegrable_pieces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false

/-- **The θ-slice identity `S2` with a θ-cutoff `ψ`** (`η = Work.Spaces.eta = 99/100`,
`v ∈ C²((0,π/2))`, `ψ ∈ C²(ℝ)` with `tsupport ψ ⊆ (a,b) ⊂ (0,π/2)`):

`∫_θ sin(2θ)^{-η} ψ v v'' = -2η∫σψv² - κ∫σψ(v')² - (2η/(1+η))∫σψ(v' - (1+η)v cos2θ/sin2θ)² + (1/2)∫σψ''v²`

(`σ = sin(2θ)^{-η}`, `κ = (1-η)/(1+η)`), all integrals over `(0,π/2)`.

This is the exact angular IBP underlying `I1Wk.truncThetaIbp` (there in the integrated, 2-D form
against `χ z · w z ^ 2`).  Note that **the statement is only true with the `tsupport` hypothesis**:
with mere `Function.support ψ ⊆ Ioo 0 (π/2)` (or without any separation of `ψ` from the corners)
the angular boundary bracket `B θ = σθ ψθ vθ v'θ - η σθ cos2θ/sin2θ ψθ vθ² - (1/2)σθ ψ'θ vθ²`
need not vanish and the identity fails (see `I1Wk/NOTES_truncThetaIbp_FALSE.md`).

Route.  (i) `S2` is a *slice-level* consequence of the pointwise identity already proved in
`Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_identity` (or its sibling
`sst_hasDerivAt_Phi` in `slice_second_trunc.lean`): with
`Φ v = σ v v' - cos(2θ)·σ₁ v²`, `Ψ v = 2σ v² + (1-η²)cos²(2θ) σ₂ v² + σ₂ (v' sin2θ - (1+η) cos2θ v)²`
and `σ_k = sin(2θ)^{-k}` one has `σ θ (v θ v'' θ) = (Φ v)' θ - Ψ v θ`, so that
`σ v v'' = (Φ v)' - Ψ v` pointwise on `(0,π/2)`.
(ii) Multiply by `ψ` and integrate over `[a,b]` by the FTC (`ψ` is `C²`, `v` is `C²` on a
neighbourhood of `[a,b]`); `[ψ Φ v]_a^b = 0` because `ψ` vanishes *on a neighbourhood* of `a` and
`b` (that is what `tsupport ψ ⊆ (a,b)` gives: `tsupport` is closed).
(iii) Integrate `-∫_a^b ψ' Φ v` by parts twice: `∫ψ' σ v v' = (1/2)∫(ψ'σ)'v²` and
`∫ψ' c σ₁ v² = -∫(cσ₁)' ψ v² - 2∫cσ₁ ψ v v'`, all boundary terms vanishing because `ψ` and `ψ'`
are `0` near `a` and `b`.  Use `σ' = -2η (cos2θ) σ₁`, `(cσ₁)' = -2(1+η)cos²(2θ)σ₂ - 2σ`,
`σ₂ = σ/sin²(2θ)`.
(iv) Expand `Ψ` and finish with `field_simp; ring` (the `sin(2θ)^{-k}` relations are best
rewritten with `← Real.rpow_add`/`Real.rpow_sub` first, cf. `ssi_sig1_eq_div`, `ssi_sig2_eq_div`
in `slice_second_identity.lean`).
No integrability hypothesis is needed: every integrand is supported in `[a,b]`, where `σ`, `σ₂`,
`v`, `v'`, `v''`, `ψ`, `ψ'`, `ψ''` are all continuous.

The implementation follows the plan above with *one* total derivative instead of three partial
integrations by parts: the boundary primitive
`Gfun v ψ θ = ψ θ · (σ θ v θ v' θ - η (cos2θ σ₁ θ) v θ²) - (1/2) ψ' θ σ θ v θ²`
has `(Gfun v ψ)' = Lfun v ψ - RHSfun v ψ` on `(0,π/2)` (that is `hasDerivAt_Gfun`, whose proof
is a product-rule computation reducing to the algebraic identity `theta_alg` of
`SliceThetaIbpDefs`), and `Gfun v ψ` vanishes at `a` and `b` because `ψ` and `ψ'` do.  The
Fundamental Theorem of Calculus over `[a,b]` then gives `∫_a^b (Lfun - RHSfun) = 0`, and all five
integrals over `(0,π/2)` are equal to the corresponding integrals over `[a,b]` because every
integrand is supported there. -/
theorem sliceThetaIbpSep (v ψ : ℝ → ℝ)
    (hv : ContDiffOn ℝ 2 v (Set.Ioo 0 (Real.pi / 2)))
    (hψ : ContDiff ℝ 2 ψ)
    (hsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (v θ * deriv (deriv v) θ))
      = -2 * Work.Spaces.eta * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (v θ) ^ 2)
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (deriv v θ) ^ 2)
        - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ
              * (deriv v θ - (1 + Work.Spaces.eta) * v θ * Real.cos (2 * θ)
                  * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) ^ 2)
        + (1 / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * deriv (deriv ψ) θ * (v θ) ^ 2) := by
  obtain ⟨a, b, ha, hab, hb, hsupp⟩ := hsep
  have hab' : a ≤ b := le_of_lt hab
  -- `[a,b]` sits inside the open interval
  have hsub : Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi / 2) := by
    rw [Set.uIcc_of_le hab']
    intro θ hθ
    exact ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
  -- `ψ` and its derivatives vanish at and beyond the ends of `[a,b]`
  have hnotmem : ∀ {θ : ℝ}, θ ∉ Set.Ioo a b → θ ∉ tsupport ψ := fun hx h => hx (hsupp h)
  have hψa : ψ a = 0 := image_eq_zero_of_notMem_tsupport (hnotmem (by simp))
  have hψb : ψ b = 0 := image_eq_zero_of_notMem_tsupport (hnotmem (by simp))
  have hdψa : deriv ψ a = 0 := deriv_eq_zero_of_notMem_tsupport (hnotmem (by simp))
  have hdψb : deriv ψ b = 0 := deriv_eq_zero_of_notMem_tsupport (hnotmem (by simp))
  have key : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → θ ∉ tsupport ψ := by
    intro θ _ _ h3 h
    have h4 := hsupp h
    rcases h3 with h3 | h3 <;> linarith [h4.1, h4.2]
  -- support facts for the five integrands
  have hL0 : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → Lfun v ψ θ = 0 := by
    intro θ h1 h2 h3
    have hz := image_eq_zero_of_notMem_tsupport (key θ h1 h2 h3)
    simp only [Lfun]
    rw [hz]
    ring
  have hA0 : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → Afun v ψ θ = 0 := by
    intro θ h1 h2 h3
    have hz := image_eq_zero_of_notMem_tsupport (key θ h1 h2 h3)
    simp only [Afun]
    rw [hz]
    ring
  have hB0 : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → Bfun v ψ θ = 0 := by
    intro θ h1 h2 h3
    have hz := image_eq_zero_of_notMem_tsupport (key θ h1 h2 h3)
    simp only [Bfun]
    rw [hz]
    ring
  have hC0 : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → Cfun v ψ θ = 0 := by
    intro θ h1 h2 h3
    have hz := image_eq_zero_of_notMem_tsupport (key θ h1 h2 h3)
    simp only [Cfun]
    rw [hz]
    ring
  have hD0 : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → Dfun v ψ θ = 0 := by
    intro θ h1 h2 h3
    have hz := deriv_deriv_eq_zero_of_notMem_tsupport (key θ h1 h2 h3)
    simp only [Dfun]
    rw [hz]
    ring
  -- convert every integral to an interval integral over `[a,b]`
  have hLc := setIntegral_Ioo_eq_intervalIntegral_of_support (f := Lfun v ψ) ha hb hab' hL0
  have hAc := setIntegral_Ioo_eq_intervalIntegral_of_support (f := Afun v ψ) ha hb hab' hA0
  have hBc := setIntegral_Ioo_eq_intervalIntegral_of_support (f := Bfun v ψ) ha hb hab' hB0
  have hCc := setIntegral_Ioo_eq_intervalIntegral_of_support (f := Cfun v ψ) ha hb hab' hC0
  have hDc := setIntegral_Ioo_eq_intervalIntegral_of_support (f := Dfun v ψ) ha hb hab' hD0
  -- integrability
  obtain ⟨iL, iA, iB, iC, iD, iRHS, iGd⟩ := intervalIntegrable_pieces v ψ hv hψ ha hb hab'
  -- the FTC identity for `Gfun`
  have hFTC : (∫ θ in a..b, (Lfun v ψ θ - RHSfun v ψ θ)) = Gfun v ψ b - Gfun v ψ a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ hθ => hasDerivAt_Gfun v ψ hv hψ (hsub hθ)) iGd
  have hGa : Gfun v ψ a = 0 := by simp [Gfun, hψa, hdψa]
  have hGb : Gfun v ψ b = 0 := by simp [Gfun, hψb, hdψb]
  have hzero : (∫ θ in a..b, (Lfun v ψ θ - RHSfun v ψ θ)) = 0 := by
    rw [hFTC, hGb, hGa, sub_zero]
  have hEq : (∫ θ in a..b, Lfun v ψ θ) = ∫ θ in a..b, RHSfun v ψ θ := by
    have hsplit : (∫ θ in a..b, (Lfun v ψ θ - RHSfun v ψ θ))
        = (∫ θ in a..b, Lfun v ψ θ) - ∫ θ in a..b, RHSfun v ψ θ :=
      intervalIntegral.integral_sub iL iRHS
    linarith [hsplit, hzero]
  -- decompose the RHS integrand into its four pieces
  have hA' : IntervalIntegrable (fun θ => -2 * Work.Spaces.eta * Afun v ψ θ) volume a b :=
    iA.const_mul (-2 * Work.Spaces.eta)
  have hB' : IntervalIntegrable
      (fun θ => ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * Bfun v ψ θ) volume a b :=
    iB.const_mul _
  have hC' : IntervalIntegrable
      (fun θ => (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * Cfun v ψ θ) volume a b :=
    iC.const_mul _
  have hD' : IntervalIntegrable (fun θ => (1 / 2) * Dfun v ψ θ) volume a b :=
    iD.const_mul (1 / 2)
  have hAB : IntervalIntegrable (fun θ => -2 * Work.Spaces.eta * Afun v ψ θ
      - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * Bfun v ψ θ) volume a b :=
    hA'.sub hB'
  have hABC : IntervalIntegrable (fun θ => -2 * Work.Spaces.eta * Afun v ψ θ
      - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * Bfun v ψ θ
      - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * Cfun v ψ θ) volume a b :=
    hAB.sub hC'
  have hcombine : (∫ θ in a..b, RHSfun v ψ θ)
      = -2 * Work.Spaces.eta * (∫ θ in a..b, Afun v ψ θ)
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ θ in a..b, Bfun v ψ θ)
        - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * (∫ θ in a..b, Cfun v ψ θ)
        + (1 / 2) * (∫ θ in a..b, Dfun v ψ θ) := by
    simp only [RHSfun]
    rw [intervalIntegral.integral_add hABC hD', intervalIntegral.integral_sub hAB hC',
      intervalIntegral.integral_sub hA' hB', intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hmain := hEq
  rw [hcombine] at hmain
  rw [← hLc, ← hAc, ← hBc, ← hCc, ← hDc] at hmain
  simpa only [Lfun, Afun, Bfun, Cfun, Dfun, sig] using hmain

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
