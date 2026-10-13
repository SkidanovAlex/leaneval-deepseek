/-
# Smoothness of the angular moment `F_*` for the data of `EllHyp`

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021.

**Statement.**  For every `α : ℝ`, `k : ℕ` and data `(F,Ψ)` with `EllHyp α k F Ψ`, the angular
moment `F_* = Work.Elliptic.Fstar F`, `F_*(z) = ∫_θ F(z,θ) sinθcos²θ dθ`, is `C^m` on `(0,∞)`
for every `m`.

**Why this is not immediate.**  `EllHyp` does *not* assume that `F` is smooth (nor even that
`F` is defined on a neighbourhood of the closed quadrant in a useful way): it only says that
`F` agrees with `bslOp α Ψ` on the *open* quadrant, with `Ψ` smooth on a neighbourhood of the
closed quadrant.  One would like to replace `F` in the integral by the smooth function
`bslOp α Ψ`, but that function is *not* smooth near `θ = π/2`: the term `∂_θ(tan θ · Ψ)` jumps
there (in Lean `Real.tan (π/2) = 0` by totalised division, whereas `tan θ · Ψ z θ` tends to
`-∂_θΨ z (π/2)` as `θ → π/2⁻`).

**The resolution.**  Only the product with the angular weight is integrated, and the weight
`sinθcos²θ` kills the pole:

  `∂_θ(tan θ Ψ)·sinθcos²θ = (Ψ/cos²θ + tanθ ∂_θΨ) sinθcos²θ = sinθ·Ψ + sin²θ cosθ·∂_θΨ`.

So with the *smooth* integrand `FstarInt α Ψ` of `FstarSmooth/Defs.lean` (the `bslOp`-bracket
without the `tan`-term, times the weight, plus the cancelled `tan`-term) one has

  `F_*(z) = ∫_θ FstarInt α Ψ z θ`  for `z > 0`

(the two integrands agree off the two endpoints of `Iθ`, and both integrals only see the open
interval), and `FstarInt α Ψ` is smooth on a neighbourhood of the closed quadrant, so its
parametric integral over the compact interval `Iθ` is smooth in `z`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Fstar_contDiffOn
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Defs
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.FstarInt_smoothNbhd
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Fstar_eq_integral_FstarInt
import Submission.Work.Coercivity.slice_ibp
import Submission.Work.FTS.EllipticEst.Mine.CutoffPieces.SmoothIntSliceDifferentiableAt
import Submission.Work.FTS.EllipticEst.Mine.CutoffPieces.FstarEqIntegralFstarIntOfSmoothInt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false

/-- **The parametric integral of `FstarInt` is smooth on `(0,∞)`.**  Immediate from the
parametric-integral lemma `contDiffOn_infty_integral_Itheta_Ioi_neg_one` applied with the
constant angular weight `1` (the weight is already built into `FstarInt`). -/
theorem contDiffOn_integral_FstarInt (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hG : Work.Spaces.SmoothNbhd (FstarInt α Ψ)) (m : ℕ) :
    ContDiffOn ℝ m (fun z => ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ) (Set.Ioi 0) := by
  have h := Work.FTS.EllipticEst.contDiffOn_infty_integral_Itheta_Ioi_neg_one
    (FstarInt α Ψ) (fun _ : ℝ => (1 : ℝ)) hG continuousOn_const
  have h2 : ContDiffOn ℝ m (fun z => ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ)
      (Set.Ioi (-1)) := by
    have h3 := contDiffOn_infty.mp h m
    simpa only [mul_one] using h3
  exact h2.mono (Set.Ioi_subset_Ioi (by norm_num))

/-- The requested lemma: for the data of `EllHyp`, the angular moment `F_*` is `C^m` on
`(0,∞)` for every `m`. -/
theorem Fstar_smooth_of_EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) := by
  intro m
  -- `FstarInt` is smooth on a neighbourhood of the closed quadrant, so its parametric
  -- integral over `Iθ` is smooth on `(0,∞)`
  have hG : Work.Spaces.SmoothNbhd (FstarInt α Ψ) :=
    Work.FTS.EllipticEst.Cert.FstarSmooth.FstarInt_smoothNbhd α Ψ hHyp.smoothNbhd
  have hint := contDiffOn_integral_FstarInt α Ψ hG m
  -- on the open quadrant, `F` is `bslOp α Ψ`, and multiplying by the weight gives `FstarInt`
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ = FstarInt α Ψ z θ := by
    intro z θ hz hθ0 hθ1
    refine bslOp_mul_sinCos2_eq α Ψ (hcos := ?_) (hd := ?_)
    · refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
      · have := Real.pi_pos; linarith
      · linarith
    · exact Work.FTS.EllipticEst.Mine.CutoffPieces.SmoothIntSliceDifferentiableAt Ψ hHyp.smooth hz ⟨hθ0, hθ1⟩
  -- the two integrals over `Iθ` agree
  have hmain : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z
      = ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ :=
    Work.FTS.EllipticEst.Mine.CutoffPieces.FstarEqIntegralFstarIntOfSmoothInt α F Ψ hHyp.smooth hHyp.sol
  exact hint.congr fun z hz => hmain z hz

end Work.FTS.EllipticEst.Cert
