import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.Asymptotics.rectInt_eq_residue
import Submission.Work.Residues.ResidueSecondVariable
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.LayerCont.Right.Defs
import Submission.Work.Asymptotics.kerFormDefs
import Submission.Work.Asymptotics.kerFormAux
import Submission.Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two
import Submission.Work.Asymptotics.HalfFunnel.localAgreementNF
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.Kaxis_local_tail
import Submission.Work.Asymptotics.FunnelAsm.aexpClosed
import Submission.Work.Asymptotics.paperLayer_agreement
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.Aexp_gauss_integrable
import Submission.Work.CKFinal.LineDecay.vertical_ray_shift
import Submission.Work.CKFinal.LineDecay.Kfun_second_limits
import Submission.Work.CKFinal.LineDecay.Kfun_strip_bound
import Submission.Work.CKFinal.LineDecay.paperLayer_eq_P1_add_sinSqC_B0
import Submission.Work.CKFinal.LineDecay.P3_eq_two_B0_sub_Bm_sub_Bp
import Submission.Work.CKFinal.LineDecay.P2_eq_neg_I_f1_add_I_f2
import Submission.Work.CKFinal.LineDecay.shift_f1_half
import Submission.Work.CKFinal.LineDecay.shift_f1_neg_half
import Submission.Work.CKFinal.LineDecay.shift_f2_neg_half
import Submission.Work.CKFinal.LineDecay.F2Half
import Submission.Work.CKFinal.LineDecay.ray_integrable
-- import Submission.Work.CKFinal.LineDecay.ray_integrable
-- import Submission.Work.CKFinal.LineDecay.shift_f1_half
-- import Submission.Work.CKFinal.LineDecay.shift_f1_neg_half
-- import Submission.Work.CKFinal.LineDecay.shift_f2_half
-- import Submission.Work.CKFinal.LineDecay.shift_f2_neg_half

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

/-- `sinSqC` in terms of the two exponential factors. -/
theorem sinSqC_eq_two_sub_kerExp (r : ℝ) :
    Work.Asymptotics.sinSqC r
      = 2 - Work.Asymptotics.kerExp r (1:ℂ) - Work.Asymptotics.kerExp r ((-1:ℂ)) := by
  rw [sinSqC_eq_two_sub_exp]
  have h1 : Work.Asymptotics.kerExp r (1:ℂ) = Complex.exp (Real.pi * Complex.I * (r:ℂ)^2) := by
    simp only [Work.Asymptotics.kerExp]; congr 1; ring
  have h2 : Work.Asymptotics.kerExp r ((-1:ℂ)) = Complex.exp (-(Real.pi * Complex.I * (r:ℂ)^2)) := by
    simp only [Work.Asymptotics.kerExp]; congr 1; ring
  rw [h1, h2]

/-- The value of `P₂` on the line `Re τ = 1/2`, given the two contour-shift identities:
this is the `I`-algebra of CKMRV §5.3 with `sinSqC r = 2 - q - q⁻¹`, using `I² = -1`. -/
theorem P2_eq_gaussTerm_add_tails_half (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (τ : UpperHalfPlane) (r : ℝ)
    (h1 : (∫ x in (0 : ℝ)..1,
        f1fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I))
      = 2 * (Real.pi : ℂ) * Complex.I * (Work.Kernels.gaussTerm τ r / (2 * Real.pi))
        - Complex.I * Work.Asymptotics.kerExp r (1 : ℂ)
            * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)
        + Complex.I * (∫ t in Set.Ioi 1, Amfun ℓ d τ r t))
    (h2 : (∫ x in (-1 : ℝ)..0,
        f2fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I))
      = - Complex.I * (∫ t in Set.Ioi 1, Apfun ℓ d τ r t)
        + Complex.I * Work.Asymptotics.kerExp r ((-1 : ℂ))
            * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)) :
    Work.CKFinal.P2 (Work.Kernels.Kfun ℓ d) r τ
      = Work.Kernels.gaussTerm τ r
        + (Work.Asymptotics.sinSqC r - 2) * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)
        + (∫ t in Set.Ioi 1, Amfun ℓ d τ r t)
        + (∫ t in Set.Ioi 1, Apfun ℓ d τ r t) := by
  rw [P2_eq_neg_I_f1_add_I_f2 ℓ d τ r, h1, h2]
  have hG : 2 * (Real.pi : ℂ) * Complex.I * (Work.Kernels.gaussTerm τ r / (2 * Real.pi))
      = Complex.I * Work.Kernels.gaussTerm τ r := by
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero]
    field_simp
  rw [hG, sinSqC_eq_two_sub_kerExp]
  linear_combination (Work.Asymptotics.kerExp r (1 : ℂ) * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)
      - Work.Kernels.gaussTerm τ r
      - (∫ t in Set.Ioi 1, Amfun ℓ d τ r t)
      - (∫ t in Set.Ioi 1, Apfun ℓ d τ r t)
      + Work.Asymptotics.kerExp r ((-1 : ℂ))
        * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)) * Complex.I_mul_I

/-- The value of `P₂` on the line `Re τ = -1/2`, given the two contour-shift identities. -/
theorem P2_eq_gaussTerm_add_tails_neg_half (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (τ : UpperHalfPlane) (r : ℝ)
    (h1 : (∫ x in (0 : ℝ)..1,
        f1fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I))
      = - Complex.I * Work.Asymptotics.kerExp r (1 : ℂ)
            * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)
        + Complex.I * (∫ t in Set.Ioi 1, Amfun ℓ d τ r t))
    (h2 : (∫ x in (-1 : ℝ)..0,
        f2fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I))
      = - Complex.I * Work.Kernels.gaussTerm τ r
        - Complex.I * (∫ t in Set.Ioi 1, Apfun ℓ d τ r t)
        + Complex.I * Work.Asymptotics.kerExp r ((-1 : ℂ))
            * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)) :
    Work.CKFinal.P2 (Work.Kernels.Kfun ℓ d) r τ
      = Work.Kernels.gaussTerm τ r
        + (Work.Asymptotics.sinSqC r - 2) * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)
        + (∫ t in Set.Ioi 1, Amfun ℓ d τ r t)
        + (∫ t in Set.Ioi 1, Apfun ℓ d τ r t) := by
  rw [P2_eq_neg_I_f1_add_I_f2 ℓ d τ r, h1, h2, sinSqC_eq_two_sub_kerExp]
  linear_combination (Work.Asymptotics.kerExp r (1 : ℂ) * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)
      - Work.Kernels.gaussTerm τ r
      - (∫ t in Set.Ioi 1, Amfun ℓ d τ r t)
      - (∫ t in Set.Ioi 1, Apfun ℓ d τ r t)
      + Work.Asymptotics.kerExp r ((-1 : ℂ))
        * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)) * Complex.I_mul_I

/-- The final algebraic step of the shift identity: `paperLayer = P₁ + sinSqC·B₀`,
`P₂ = gaussTerm + (sinSqC - 2)·B₀ + B_m + B_p` and `P₃ = 2B₀ - B_m - B_p` combine to
`gaussTerm + paperLayer = P₁ + P₂ + P₃`. -/
theorem shift_identity_algebra (G P1 s B0 Bm Bp : ℂ) :
    G + (P1 + s * B0) = P1 + (G + (s - 2) * B0 + Bm + Bp) + (2 * B0 - Bm - Bp) := by
  ring

/-- **The shift identity on the line `Re τ = 1/2`, reduced to the two contour-shift
identities.**  All the integral linearity, the paper's `paperLayer = P₁ + sinSqC·B₀`, the
identity `P₃ = 2B₀ - B_m - B_p` and the `I`-algebra of `P₂` are done here; the two hypotheses
are exactly the two boundary-shift identities of CKMRV §5.3 on this line. -/
theorem shift_identity_kfun_of_shifts_half (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r ^ 2)
    (hD : τ ∈ Work.Asymptotics.DomainD) (hre1 : τ.re = 1 / 2) (him : 12 ≤ τ.im)
    (hA0I : MeasureTheory.IntegrableOn (A0fun ℓ d τ r) (Set.Ioi 1))
    (hAmI : MeasureTheory.IntegrableOn (Amfun ℓ d τ r) (Set.Ioi 1))
    (hApI : MeasureTheory.IntegrableOn (Apfun ℓ d τ r) (Set.Ioi 1))
    (hs1 : (∫ x in (0 : ℝ)..1, f1fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I))
      = 2 * (Real.pi : ℂ) * Complex.I * (Work.Kernels.gaussTerm τ r / (2 * Real.pi))
        - Complex.I * Work.Asymptotics.kerExp r (1 : ℂ)
            * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)
        + Complex.I * (∫ t in Set.Ioi 1, Amfun ℓ d τ r t))
    (hs2 : (∫ x in (-1 : ℝ)..0, f2fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I))
      = - Complex.I * (∫ t in Set.Ioi 1, Apfun ℓ d τ r t)
        + Complex.I * Work.Asymptotics.kerExp r ((-1 : ℂ))
            * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)) :
    Work.Kernels.gaussTerm τ r
        + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
      = Work.CKFinal.P1 (Work.Kernels.Kfun ℓ d) r τ
        + Work.CKFinal.P2 (Work.Kernels.Kfun ℓ d) r τ
        + Work.CKFinal.P3 (Work.Kernels.Kfun ℓ d) r τ := by
  have hA := paperLayer_eq_P1_add_sinSqC_B0 ℓ d hd τ hr hD (Or.inl hre1) him
  have hB := P3_eq_two_B0_sub_Bm_sub_Bp ℓ d τ r hA0I hAmI hApI
  have hP2 := P2_eq_gaussTerm_add_tails_half ℓ d τ r hs1 hs2
  rw [hA, hP2, hB]
  exact shift_identity_algebra _ _ _ _ _ _

/-- **The shift identity on the line `Re τ = -1/2`, reduced to the two contour-shift
identities.** -/
theorem shift_identity_kfun_of_shifts_neg_half (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r ^ 2)
    (hD : τ ∈ Work.Asymptotics.DomainD) (hre2 : τ.re = -1 / 2) (him : 12 ≤ τ.im)
    (hA0I : MeasureTheory.IntegrableOn (A0fun ℓ d τ r) (Set.Ioi 1))
    (hAmI : MeasureTheory.IntegrableOn (Amfun ℓ d τ r) (Set.Ioi 1))
    (hApI : MeasureTheory.IntegrableOn (Apfun ℓ d τ r) (Set.Ioi 1))
    (hs1 : (∫ x in (0 : ℝ)..1, f1fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I))
      = - Complex.I * Work.Asymptotics.kerExp r (1 : ℂ)
            * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)
        + Complex.I * (∫ t in Set.Ioi 1, Amfun ℓ d τ r t))
    (hs2 : (∫ x in (-1 : ℝ)..0, f2fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I))
      = - Complex.I * Work.Kernels.gaussTerm τ r
        - Complex.I * (∫ t in Set.Ioi 1, Apfun ℓ d τ r t)
        + Complex.I * Work.Asymptotics.kerExp r ((-1 : ℂ))
            * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)) :
    Work.Kernels.gaussTerm τ r
        + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
      = Work.CKFinal.P1 (Work.Kernels.Kfun ℓ d) r τ
        + Work.CKFinal.P2 (Work.Kernels.Kfun ℓ d) r τ
        + Work.CKFinal.P3 (Work.Kernels.Kfun ℓ d) r τ := by
  have hA := paperLayer_eq_P1_add_sinSqC_B0 ℓ d hd τ hr hD (Or.inr hre2) him
  have hB := P3_eq_two_B0_sub_Bm_sub_Bp ℓ d τ r hA0I hAmI hApI
  have hP2 := P2_eq_gaussTerm_add_tails_neg_half ℓ d τ r hs1 hs2
  rw [hA, hP2, hB]
  exact shift_identity_algebra _ _ _ _ _ _

theorem shift_identity_kfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r ^ 2) :
    (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → 12 ≤ τ.im →
    Work.Kernels.gaussTerm τ r + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
      = Work.CKFinal.P1 (Work.Kernels.Kfun ℓ d) r τ
        + Work.CKFinal.P2 (Work.Kernels.Kfun ℓ d) r τ
        + Work.CKFinal.P3 (Work.Kernels.Kfun ℓ d) r τ := by
  intro hre him
  have hD : τ ∈ Work.Asymptotics.DomainD := mem_DomainD_of_line τ hre him
  have hA0I : MeasureTheory.IntegrableOn (A0fun ℓ d τ r) (Set.Ioi 1) :=
    integrableOn_A0fun ℓ d hd τ hr hD
  have hAmI : MeasureTheory.IntegrableOn (Amfun ℓ d τ r) (Set.Ioi 1) :=
    integrableOn_Kax_ray ℓ d hd τ hr hre him (Or.inl rfl)
  have hApI : MeasureTheory.IntegrableOn (Apfun ℓ d τ r) (Set.Ioi 1) :=
    integrableOn_Kax_ray ℓ d hd τ hr hre him (Or.inr rfl)
  rcases hre with hre1 | hre2
  · exact shift_identity_kfun_of_shifts_half ℓ d hd τ hr hD hre1 him hA0I hAmI hApI
      (shift_f1_half ℓ d hd τ hr hre1 him)
      (shift_f2_half ℓ d hd τ hr hre1 him)
  · exact shift_identity_kfun_of_shifts_neg_half ℓ d hd τ hr hD hre2 him hA0I hAmI hApI
      (shift_f1_neg_half ℓ d hd τ hr hre2 him)
      (shift_f2_neg_half ℓ d hd τ hr hre2 him)

end Work.CKFinal.LineDecay
