import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.zsliceSmooth
import Submission.Work.FTS.EllipticEst.Honest.zIBP_compact
import Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.VnWeighted
import Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.AeSetup
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.H2W.AeLeftClean
import Submission.Work.FTS.EllipticEst.H2W.AeStep1Leaves.AeHkMemU
import Submission.Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.Bridges
import Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.hkIntegrand0Prod
import Submission.Work.FTS.EllipticEst.weight_algebra_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TT/AeDzDefs` -- the vocabulary of the `TT.AeDzNorm` proof

The `σ`-masses of a slice (`AeDz.mass`, `AeDz.dzMass`, `AeDz.lzMass`, `AeDz.srcMass`), the
per-`θ` radial integration-by-parts identity `AeDz.perThetaIBP`, the identification of
`HkSq α 0 g` with the `z`-integral of `mass g`, and the coefficient bounds `AeDz.vnCoeffBounds`
for the truncated weight `Vn n · φ`.  Split off from `TT/aeDzNorm.lean` so that the helper
modules delegated from that file (`TT.truncIntegrable`, `TT.truncId`) can import the vocabulary
without importing the final theorem.
-/
namespace Work.FTS.EllipticEst.TT

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

namespace AeDz

/-- The angular weight `σ θ = sin(2θ)^{-η}`. -/
abbrev sig (θ : ℝ) : ℝ := Work.FTS.EllipticEst.sEta θ

/-- The squared radial weight `φ z = w z ²`. -/
abbrev phi (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

/-- The `σ`-mass of a `θ`-slice of `g`: `∫_θ (g z θ)² σ θ`. -/
abbrev mass (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * sig θ

/-- The `σ`-mass of the `z`-derivative of a `θ`-slice of `g`: `∫_θ (∂_z g z θ)² σ θ`. -/
abbrev dzMass (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz g z θ) ^ 2 * sig θ

/-- The `σ`-pairing of a slice with the angular part `L₀`: `∫_θ Lzero1 (u z ·) θ · u z θ · σ θ`. -/
abbrev lzMass (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ * sig θ

/-- The `σ`-pairing of a slice with the source: `∫_θ G z θ · u z θ · σ θ`. -/
abbrev srcMass (G u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, G z θ * u z θ * sig θ

/-- `σ ≥ 0` on `Iθ`. -/
theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sig θ := by
  rw [sig, Work.FTS.EllipticEst.sEta]
  refine Real.rpow_nonneg ?_ _
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `1 ≤ σ` on `(0, π/2)`. -/
theorem one_le_sig {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ sig θ := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.Honest.sin_two_pos_of_Iθo hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  rw [sig, Work.FTS.EllipticEst.sEta]
  calc (1 : ℝ) = (1 : ℝ) ^ (-Work.Spaces.eta) := (Real.one_rpow _).symm
    _ ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
        Real.rpow_le_rpow_of_nonpos hs hs1 (by norm_num [Work.Spaces.eta])

/-- `φ ≥ 0`. -/
theorem phi_nonneg (z : ℝ) : 0 ≤ phi z := by rw [phi]; positivity

/-- The level-`0` integrand is `w²` times the `σ`-weighted square. -/
theorem hkIntegrand_eq (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ = Work.Spaces.w z ^ 2 * (g z θ ^ 2 * sig θ) :=
  Work.FTS.EllipticEst.H2W.AeProof.ae.hkIntegrand_zero α g hθ

/-- The `θ`-slice of `Lzero` is `Lzero1` applied to the slice. -/
theorem Lzero1_slice_eq (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ = Work.Elliptic.Lzero u z θ := by
  simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-- **The per-`θ` radial integration by parts** (`Honest.zIBP_compact` in the notation of this
file): for a `C²` radial weight `ψ` supported in `[a,b] ⊂ (0,∞)` and every `θ ∈ (0,π/2)`, the
pairing of the radial part of `bslOp` with `u` against `ψ` equals the two transferred terms. -/
theorem perThetaIBP {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (ψ : ℝ → ℝ) (hψd : ContDiffOn ℝ 2 ψ (Set.Ioi 0))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hψs : ∀ z, z ∉ Set.Icc a b → ψ z = 0)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Set.Ioi 0, ψ z * (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + α * (5 + α) * z * Work.Spaces.pz u z θ) * u z θ)
      = -α ^ 2 * (∫ z in Set.Ioi 0, ψ z * (z * Work.Spaces.pz u z θ) ^ 2)
        + (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
            deriv (deriv (fun z => ψ z * z ^ 2)) z * (u z θ) ^ 2)
        - (α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
            deriv (fun z => ψ z * z) z * (u z θ) ^ 2) := by
  have hΦ : ContDiffOn ℝ 2 (fun z : ℝ => u z θ) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.H2W.AeProof.ae.zsliceSmooth (hsm 2) hθ
  have h := Work.FTS.EllipticEst.Honest.zIBP_compact α ψ (fun z : ℝ => u z θ) ha hab hψs hψd hΦ
  -- rewrite `zIBP_compact` into the notation of this file
  have hL : (∫ z in Set.Ioi (0 : ℝ), ψ z * (α ^ 2 * z ^ 2
        * deriv (deriv (fun z : ℝ => u z θ)) z
        + (α * (5 + α) * z) * deriv (fun z : ℝ => u z θ) z) * u z θ)
      = ∫ z in Set.Ioi (0 : ℝ), ψ z * (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + α * (5 + α) * z * Work.Spaces.pz u z θ) * u z θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  have hR1 : (∫ z in Set.Ioi (0 : ℝ), ψ z * (z * deriv (fun z : ℝ => u z θ) z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), ψ z * (z * Work.Spaces.pz u z θ) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    simp only [Work.Spaces.pz]
  have hR2 : (∫ z in Set.Ioi (0 : ℝ),
        deriv (deriv (fun z : ℝ => z ^ 2 * ψ z)) z * (u z θ) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ),
        deriv (deriv (fun z : ℝ => ψ z * z ^ 2)) z * (u z θ) ^ 2 := by
    have hfun : (fun z : ℝ => z ^ 2 * ψ z) = fun z : ℝ => ψ z * z ^ 2 := by
      funext z; ring
    rw [hfun]
  have hR3 : (∫ z in Set.Ioi (0 : ℝ),
        deriv (fun z : ℝ => z * ψ z) z * (u z θ) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ),
        deriv (fun z : ℝ => ψ z * z) z * (u z θ) ^ 2 := by
    have hfun : (fun z : ℝ => z * ψ z) = fun z : ℝ => ψ z * z := by
      funext z; ring
    rw [hfun]
  rw [hL, hR1, hR2, hR3] at h
  linarith [h]

/-! ## `HkSq` in the `mass` notation -/

/-- The `θ`-integral of the level-`0` integrand is `φ · mass g`. -/
theorem integral_hkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) = phi z * mass g z := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  exact hkIntegrand_eq α g hθ

/-- The level-`0` square norm as a single `z`-integral of the slice `σ`-mass. -/
theorem HkSq_eq_w_sq_mass (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * mass g z := by
  simp only [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  exact hkIntegrand_eq α g hθ

/-! ## The coefficient bounds for the truncated weight `Vn n · φ` -/

/-- The two integration-by-parts coefficients of the truncated weight `ψ_n = Vn n · φ` are
bounded by a universal multiple of `φ`, uniformly in `n`, on `(0,∞)`. -/
theorem vnCoeffBounds : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ z : ℝ, 0 < z →
    |deriv (deriv (fun z => Work.FTS.EllipticEst.H2W.AeProof.ae.Vn n z * phi z * z ^ 2)) z|
        ≤ C * phi z ∧
      |deriv (fun z => Work.FTS.EllipticEst.H2W.AeProof.ae.Vn n z * phi z * z) z|
        ≤ C * phi z := by
  obtain ⟨C, hC, h1, h2, -, -⟩ := Work.FTS.EllipticEst.H2W.AeProof.ae.VnWeighted
  refine ⟨C, hC, fun n z hz => ⟨?_, ?_⟩⟩
  · have h := h1 n z hz
    have hfun : (fun y : ℝ => y ^ 2
          * Work.FTS.EllipticEst.H2W.AeProof.ae.Vn n y * (Work.Spaces.w y) ^ 2)
        = fun y : ℝ => Work.FTS.EllipticEst.H2W.AeProof.ae.Vn n y
          * (Work.Spaces.w y) ^ 2 * y ^ 2 := by
      funext y; ring
    rw [hfun] at h
    simpa only [phi] using h
  · have h := h2 n z hz
    have hfun : (fun y : ℝ => y
          * Work.FTS.EllipticEst.H2W.AeProof.ae.Vn n y * (Work.Spaces.w y) ^ 2)
        = fun y : ℝ => Work.FTS.EllipticEst.H2W.AeProof.ae.Vn n y
          * (Work.Spaces.w y) ^ 2 * y := by
      funext y; ring
    rw [hfun] at h
    simpa only [phi] using h


end AeDz

end

end Work.FTS.EllipticEst.TT
