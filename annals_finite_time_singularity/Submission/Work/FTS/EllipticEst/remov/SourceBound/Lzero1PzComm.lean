import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceShiftedDecomposition

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Lzero1` commutes with `∂_z` on slices

`Lzero1PzComm`: the angular operator `Lzero1` of `Work.FTS.EllipticEst.StraightDefs`
commutes with the radial derivative `∂_z` on the slices of a function `C^∞` on the open
quadrant.  The proof is the slice-level analogue of the `Lzero`-commutation
`pz_Lzero_eq` of `sliceShiftedDecomposition.lean`: `Lzero1` applied to the `z`-slice of
`Φ` is (definitionally) `Work.Elliptic.Lzero Φ` evaluated at the same point
(`Lzero1_slice_eq`), and `∂_z` commutes with each of the three summands of `Lzero` — the
pure angular term by iterated Clairaut (`pz_pthIter_two_eq`), the `tan θ·Φ` term by
Clairaut for the smooth function `tan θ·Φ` (`pz_pth_tanMulS_eq`), and the identity term
trivially.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Auxiliary vocabulary and elementary facts -/

/-- `tan θ · g` as a two-variable function: the angular factor of `Work.Elliptic.Lzero`. -/
private def tanMulS (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Real.tan θ * g z θ

/-- `∂_z` commutes with multiplication by `tan θ`. -/
private lemma pz_tanMulS (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (tanMulS g) = tanMulS (Work.Spaces.pz g) := by
  funext z θ
  simp only [tanMulS, Work.Spaces.pz]
  rw [deriv_const_mul_field]

/-- `ContDiffAt`-form of `SmoothOpen` at an interior point of the open quadrant. -/
private lemma smoothOpen_contDiffAt_two'' {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  (hf.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))

/-- `SmoothOpen` of `(z,θ) ↦ tan θ · Ψ z θ` (the angular factor `tan` is smooth on the
open quadrant). -/
private lemma smoothOpen_tanMulS {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (tanMulS Ψ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (tanMulS Ψ))
    Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (tanMulS Ψ)
      = fun p : ℝ × ℝ => Real.tan p.2 * Ψ p.1 p.2 from rfl]
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 := by
    have hs : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 := by
      change ContDiffOn ℝ Work.Stability.smoothOrder (Real.sin ∘ Prod.snd)
        Work.FTS.EllipticEst.Q0
      exact Real.contDiff_sin.comp_contDiffOn contDiffOn_snd
    have hc : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 := by
      change ContDiffOn ℝ Work.Stability.smoothOrder (Real.cos ∘ Prod.snd)
        Work.FTS.EllipticEst.Q0
      exact Real.contDiff_cos.comp_contDiffOn contDiffOn_snd
    have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
      intro p hp
      obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h1], h2⟩)
    have hdiv : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
      hs.div hc hne
    refine hdiv.congr (fun p _ => ?_)
    rw [Real.tan_eq_sin_div_cos]
  have hΨ' : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 := hΨ
  exact htan.mul hΨ'

/-! ## Commutation of `∂_z` with the summands of `Lzero` -/

/-- `∂_z ∂_θ² Φ = ∂_θ² ∂_z Φ` on the open quadrant (two instances of Clairaut). -/
private lemma pz_pthIter_two_eq {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Φ) z θ := by
  have hV : IsOpen (Work.FTS.EllipticEst.Q0) := Work.FTS.EllipticEst.isOpen_Q0
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Φ)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Φ)) z θ :=
    Work.Spaces.pz_pth_comm (smoothOpen_contDiffAt_two'' hΦ.pth hz hθ)
  have heqon : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth Φ)))
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz Φ))) Work.FTS.EllipticEst.Q0 := by
    intro p hp'
    obtain ⟨hz', hθ'1, hθ'2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp'
    exact Work.Spaces.pz_pth_comm (smoothOpen_contDiffAt_two'' hΦ hz' ⟨hθ'1, hθ'2⟩)
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Φ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Φ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen hV heqon hp
  show Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Φ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Φ)) z θ
  rw [h1, h2]

/-- `∂_z ∂_θ(tan θ · Φ) = ∂_θ ∂_z(tan θ · Φ)` on the open quadrant. -/
private lemma pz_pth_tanMulS_eq {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pth (tanMulS Φ)) z θ
      = Work.Spaces.pth (tanMulS (Work.Spaces.pz Φ)) z θ := by
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hC2 : ContDiffAt ℝ 2 (Function.uncurry (tanMulS Φ)) (z, θ) :=
    ((smoothOpen_tanMulS hΦ).forall 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  rw [Work.Spaces.pz_pth_comm hC2, pz_tanMulS]

/-! ## The commutation theorem -/

/-- **`Lzero1` commutes with `∂_z` on slices.**

Let `Φ : ℝ → ℝ → ℝ` be `C^∞` on the open quadrant, `z > 0`, `0 < θ < π/2`.  Then the angular
operator `Lzero1 u = -u'' + (tan·u)' - 6u` applied to the `z`-derivative of the slice equals the
`z`-derivative of `Lzero1` applied to the slice:

`Lzero1 (fun t => pz Φ z t) θ = deriv (fun z' => Lzero1 (fun t => Φ z' t) θ) z`.

Note for the prover: the same identity (with the two sides swapped and `Lzero` on a slice in
place of `Lzero1`) is ALREADY proved in `remov/SourceBound/sliceShiftedDecomposition.lean`, as the
private helper `pz_Lzero_eq` (line 159, with `hasDerivAt_Lzero_slice` at line 131) under the
hypothesis `hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ` and `hz : 0 < z`, `hθ ∈ Ioo 0 (π/2)`; that
file is axiom-clean, so the present statement can be obtained by adapting that proof (only the
`rfl`-identification `Lzero Ψ z x = Lzero1 (fun t => Ψ z t) x` and the swapped sides are needed),
using `Work.FTS.EllipticEst.smoothOpen_of_forall hsmooth`.  Alternatively, redo the Clairaut
argument directly with `Work.Spaces.pz_pth_comm`. -/
theorem Lzero1PzComm {Φ : ℝ → ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Φ z t) θ
      = deriv (fun z' => Work.FTS.EllipticEst.Lzero1 (fun t => Φ z' t) θ) z := by
  have hΦ : Work.FTS.EllipticEst.SmoothOpen Φ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsmooth
  have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hθ2⟩
  have htanmul : Work.FTS.EllipticEst.SmoothOpen (tanMulS Φ) := smoothOpen_tanMulS hΦ
  have hd1 : HasDerivAt (fun z' => Work.Spaces.pthIter 2 Φ z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ) z :=
    (hΦ.pth.pth).hasDerivAt_slice hθm hz
  have hd2 : HasDerivAt (fun z' => Work.Spaces.pth (tanMulS Φ) z' θ)
      (Work.Spaces.pz (Work.Spaces.pth (tanMulS Φ)) z θ) z :=
    htanmul.pth.hasDerivAt_slice hθm hz
  have hd3 : HasDerivAt (fun z' => Φ z' θ) (Work.Spaces.pz Φ z θ) z :=
    hΦ.hasDerivAt_slice hθm hz
  have hsum : HasDerivAt (fun z' => -(Work.Spaces.pthIter 2 Φ z' θ)
        + Work.Spaces.pth (tanMulS Φ) z' θ - 6 * Φ z' θ)
      ((-(Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (tanMulS Φ)) z θ) - 6 * Work.Spaces.pz Φ z θ) z :=
    (hd1.neg.add hd2).sub (hd3.const_mul 6)
  have hval : ((-(Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (tanMulS Φ)) z θ) - 6 * Work.Spaces.pz Φ z θ)
      = Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Φ z t) θ := by
    rw [pz_pthIter_two_eq hΦ hz hθm, pz_pth_tanMulS_eq hΦ hz hθm, Lzero1_slice_eq]
    rfl
  rw [hval] at hsum
  have hmain : HasDerivAt (fun z' => Work.Elliptic.Lzero Φ z' θ)
      (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Φ z t) θ) z :=
    hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z' => rfl))
  have hmain2 : HasDerivAt (fun z' => Work.FTS.EllipticEst.Lzero1 (fun t => Φ z' t) θ)
      (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Φ z t) θ) z :=
    hmain.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z' => (Lzero1_slice_eq Φ z' θ).symm))
  exact hmain2.deriv.symm

end Work.FTS.EllipticEst.remov.SourceBound
