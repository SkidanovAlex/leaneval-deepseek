import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The two ingredients of the argument

The proof of the target is a two-line consequence of the two lemmas below.

* `integrableOn_pz_mul_sinCos2` extracts the `i = 1` slot of `HkMem` for `∂_z g` and absorbs the
  angular profile `sinθcos²θ` into the weighted `L²`-integrand of `ℋ^k`.  It is the same
  "absorbtion" mechanism as `Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted` (the pointwise
  bound `|a·sinθcos²θ| ≤ (a·W)² + 1`, `W = w/sin(2θ)^{η/2}`) combined with
  `Work.Spaces.sq_le_HkIntegrand_z` for the `i = 1` summand and the identity
  `D_z g = z · ∂_z g`, which removes the factor `z²` (the only place where `z > 0` enters).

* `aesm_slice_mul_sinCos2`, `aesm_slice_pz_F`, `aesm_slice_pz_zsq_pzIter2` supply the a.e. strong
  measurability that `Integrable.mono'` needs: the slices are continuous on the open quadrant,
  and for `F` (which is only known to equal the smooth `bslOp α Ψ` there) the identification is
  transported by the locality of `deriv` on the open interval. -/

/-- The angular profile `sinθ·cos²θ` as a continuous function of the pair `(z,θ)`. -/
private lemma continuous_snd_sinCos2 :
    Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
  simp only [Work.Elliptic.sinCos2]
  exact (Real.continuous_sin.comp continuous_snd).mul
    ((Real.continuous_cos.comp continuous_snd).pow 2)

/-- **A.e. strong measurability of the angular slice `θ ↦ A z θ · sinθcos²θ`** for a function
`A` continuous on the open quadrant and `z > 0`: the slice map `θ ↦ (z,θ)` lands in the open
quadrant, so the slice is continuous on `(0,π/2)`, which differs from `Iθ` by the null set
`{0, π/2}`. -/
theorem aesm_slice_mul_sinCos2 {A : ℝ → ℝ → ℝ}
    (hA : ContinuousOn (Function.uncurry A) Work.FTS.EllipticEst.Q0) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => A z θ * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => A p.1 p.2 * Work.Elliptic.sinCos2 p.2)
    (hA.mul continuous_snd_sinCos2.continuousOn) hz

/-- **Honesty of the slice `θ ↦ ∂_z g (z,θ) · sinθcos²θ` from one `H^k`-slot.**

If `g ∈ ℋ^k` with `1 ≤ k` and the slice is a.e. strongly measurable, then it is integrable on
`Iθ` for every `z > 0`.

The pointwise bound is the paper's "absorbtion" estimate
`|a·sinθcos²θ| ≤ (a·W)² + 1` with `W = w z/sin(2θ)^{η/2}` (`abs_mul_sinCos2_le_weighted`),
followed by `(∂_z g · W)² = z^{-2}·(D_z g · W)² ≤ z^{-2}·HkIntegrand α k g z ·`
(`Work.Spaces.sq_le_HkIntegrand_z` for `i = 1`), which is integrable on the slice by `HkMem`. -/
theorem integrableOn_pz_mul_sinCos2 {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) (hk : 1 ≤ k) {z : ℝ} (hz : 0 < z)
    (haesm : AEStronglyMeasurable
      (fun θ => Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hz2ne : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  have hvol : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  refine MeasureTheory.Integrable.mono'
    (((hmem.1 z hzI).const_mul ((z ^ 2)⁻¹)).add
      (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol)) haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
  rw [Real.norm_eq_abs]
  -- the pointwise absorbtion estimate
  have h1 := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
    (f := fun θ => Work.Spaces.pz g z θ) hz hθ
  -- and the `i = 1` slot of the `ℋ^k`-integrand
  have hq := Work.Spaces.sq_le_HkIntegrand_z α k g z θ 1 hk
  set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hW
  have hDz : Work.Spaces.DzIter 1 g z θ = z * Work.Spaces.pz g z θ := rfl
  have hid : (Work.Spaces.pz g z θ * W) ^ 2
      = (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ * W) ^ 2) := by
    rw [hDz]
    have : (z * Work.Spaces.pz g z θ * W) ^ 2
        = z ^ 2 * (Work.Spaces.pz g z θ * W) ^ 2 := by ring
    rw [this, inv_mul_cancel_left₀ hz2ne]
  have hz2inv : (0 : ℝ) ≤ (z ^ 2)⁻¹ := by positivity
  calc |Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ|
      ≤ (Work.Spaces.pz g z θ * W) ^ 2 + 1 := h1
    _ = (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ * W) ^ 2) + 1 := by rw [hid]
    _ ≤ (z ^ 2)⁻¹ * Work.Spaces.HkIntegrand α k g z θ + 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hq hz2inv) le_rfl

/-- **A.e. strong measurability of the slice `θ ↦ ∂_z F(z,θ)·sinθcos²θ`.**

The hypothesis class only relates `F` to the smooth function `bslOp α Ψ` on the *open* quadrant,
so the slice of `∂_z F` is identified with the continuous slice of `∂_z (bslOp α Ψ)` for almost
every `θ` (the two endpoints of `Iθ` are null): for `θ ∈ (0,π/2)` the `z`-slices of `F` and of
`bslOp α Ψ` agree on the neighbourhood `(0,∞)` of `z > 0`, and `deriv` is local. -/
theorem aesm_slice_pz_F {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → AEStronglyMeasurable
      (fun θ => Work.Spaces.pz F z θ * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hbsl : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hS
  intro z hz
  refine (aesm_slice_mul_sinCos2 (A := Work.Spaces.pz (Work.Elliptic.bslOp α Ψ))
    (hbsl.pz).continuousOn hz).congr ?_
  show ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    Work.Spaces.pz (Work.Elliptic.bslOp α Ψ) z θ * Work.Elliptic.sinCos2 θ
      = Work.Spaces.pz F z θ * Work.Elliptic.sinCos2 θ
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  have hslice : (fun z' : ℝ => F z' θ) =ᶠ[𝓝 z]
      (fun z' : ℝ => Work.Elliptic.bslOp α Ψ z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact (h.eq z' hz' θ hθ.1 hθ.2).symm
  rw [show Work.Spaces.pz (Work.Elliptic.bslOp α Ψ) z θ = Work.Spaces.pz F z θ from
    hslice.deriv_eq.symm]

/-- **A.e. strong measurability of the slice `θ ↦ ∂_z (z²∂_z²Ψ)(z,θ)·sinθcos²θ`.**

Here no a.e. identification is needed: `z²∂_z²Ψ` is `C^∞` on the open quadrant as soon as `Ψ`
is (`Cert.smoothOpen_mul_bsl`), hence so is its `∂_z`, and the slice is continuous on `(0,π/2)`. -/
theorem aesm_slice_pz_zsq_pzIter2 {Ψ : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z, 0 < z → AEStronglyMeasurable
      (fun θ => Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        * Work.Elliptic.sinCos2 θ) (volume.restrict Work.Spaces.Iθ) := by
  have hG : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hS.pzIter 2)
  intro z hz
  exact aesm_slice_mul_sinCos2
    (A := Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hG.pz).continuousOn hz

/-- **Slice honesty of `∂_z F` and of `∂_z (z² ∂_z²Ψ)`.**

For a datum of the weak class `EllWeakPos α k F Ψ` (with `k ≥ 2`) and every `z > 0`, the angular
slices `θ ↦ pz F z θ * sinCos2 θ` and
`θ ↦ pz (fun z θ => z ^ 2 * pzIter 2 Ψ z θ) z θ * sinCos2 θ` are integrable on `Iθ`.

Proof sketch.  The `i = 1` summand of the first sum of `HkIntegrand` for `g` is exactly
`(DzIter 1 g * (w z / sin(2θ)^(η/2)))^2 = (z * pz g * (w z / sin(2θ)^(η/2)))^2`, and by
`Work.Spaces.sq_le_HkIntegrand_z` it is bounded by `HkIntegrand`, which is integrable on `Iθ` by
`HkMem`.  Hence `∫ (pz g z θ * W)^2 < ∞` with `W = w z / sin(2θ)^(η/2)`, and Cauchy–Schwarz
against `θ ↦ sin(2θ)^(η/2) * sinCos2 θ / W = sin(2θ)^(η/2) * sinCos2 θ * z^2 / (1+z)^2`
(whose square is integrable on `Iθ`) gives `∫ |pz g z θ * sinCos2 θ| < ∞`.  Applying this to
`g = F` and to `g = fun z θ => z^2 * pzIter 2 Ψ z θ` (both in `HkMem α k` by `EllWeakPos`) gives
the two claims.  A.e. strong measurability comes from the smoothness: `F = bslOp α Ψ` on the open
quadrant, so both `F` and `z² ∂_z²Ψ` have smooth `θ`-slices there. -/
theorem weakSliceDeriv {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    (∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) ∧
    (∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hk1 : 1 ≤ k := by omega
  exact ⟨fun z hz => integrableOn_pz_mul_sinCos2 h.memF hk1 hz (aesm_slice_pz_F h z hz),
    fun z hz => integrableOn_pz_mul_sinCos2 h.memA hk1 hz (aesm_slice_pz_zsq_pzIter2 hS z hz)⟩

end

end Work.FTS.EllipticEst.remov.SourceBound
