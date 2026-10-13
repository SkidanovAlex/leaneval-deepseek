import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.integrable_mul_sinCos2
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.EllWeakAux

/-- **`F_*` subtracts on sources of the weak class.**

If `G = bslOp α Ψ` and `H = bslOp α Φ` are two sources of the weak class `EllWeakPos` (so that
both angular moments `F_*(G)(z) = ∫_θ G z θ · sinθcos²θ dθ` and `F_*(H)(z)` vanish for `z > 0`),
then the source `G - H` of the difference is again orthogonal to `sinθcos²θ`:

  `F_*(G - H)(z) = 0`  for every `z > 0`.

The content is the linearity `F_*(G - H) = F_*(G) - F_*(H)` of the angular moment on the
relevant slices.  It is not available for free (`F_*` is a Bochner integral, additive only on
integrable functions), so the proof establishes the integrability of the two slices
`θ ↦ G z θ · sinθcos²θ` and `θ ↦ H z θ · sinθcos²θ`:

* a *source* of the weak class is a priori neither smooth nor even known to have measurable
  angular slices — it only satisfies the weighted `L²` hypothesis `HkMem α k G`, whose
  integrand contains the single `D_z`-summand with `i = 0`, i.e.
  `(G z θ · w z / sin(2θ)^{η/2})²`.  Splitting that summand off (all summands are squares) gives
  the `L²(Iθ)` control of the weighted slice;
* measurability of the slice comes from the *equation*: on the open quadrant `G = bslOp α Ψ`
  with `Ψ` of class `C^∞` there, hence `G` agrees a.e. on `Iθ` with the slice of the smooth
  function `bslOp α Ψ` (`SmoothOpen_bslOp_of_smoothOpen`), which is a.e. strongly measurable by
  continuity (`aesm_slice_of_continuousOn_Qd`);
* `LamEst.integrable_mul_sinCos2` then converts the weighted `L²` control plus that
  measurability into the `L¹`-integrability against `sinθcos²θ`.

The final step is `integral_sub` on `volume.restrict Iθ` plus the two moment hypotheses. -/
theorem Fstar_source_sub (k : ℕ) {α : ℝ} {G H Ψ Φ : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.TT.EllWeakPos α k G Ψ)
    (hH : Work.FTS.EllipticEst.TT.EllWeakPos α k H Φ) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (fun z θ => G z θ - H z θ) z = 0 := by
  intro z hz
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  -- `Ψ` and `Φ` are `C^∞` on the open quadrant, hence so are `bslOp α Ψ` and `bslOp α Φ`.
  have hsoΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mpr (hG.smooth)
  have hsoΦ : Work.FTS.EllipticEst.SmoothOpen Φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mpr (hH.smooth)
  have hsoB : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hsoΨ
  have hsoB' : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Φ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hsoΦ
  -- On the open interval the slices of the sources are those of the smooth representatives.
  have haeG : (fun θ => G z θ) =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Elliptic.bslOp α Ψ z θ) := by
    rw [show MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) from
      (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))).symm]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    exact (hG.eq z hz θ hθ.1 hθ.2).symm
  have haeH : (fun θ => H z θ) =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Elliptic.bslOp α Φ z θ) := by
    rw [show MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) from
      (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))).symm]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    exact (hH.eq z hz θ hθ.1 hθ.2).symm
  -- A.e. strong measurability of the two slices.
  have haesmG : MeasureTheory.AEStronglyMeasurable (fun θ => G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd
      (Function.uncurry (Work.Elliptic.bslOp α Ψ)) hsoB.continuousOn hz).congr haeG.symm
  have haesmH : MeasureTheory.AEStronglyMeasurable (fun θ => H z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd
      (Function.uncurry (Work.Elliptic.bslOp α Φ)) hsoB'.continuousOn hz).congr haeH.symm
  -- The angular weight factor `φ θ = w z / sin(2θ)^{η/2}` is measurable.
  have hφmeas : Measurable (fun θ : ℝ => Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
    measurable_const.div
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _)
  -- The `i = 0` summand of the `ℋ^k`-integrand is the weighted square of the slice.
  have hsqG : MeasureTheory.Integrable (fun θ => (G z θ * (Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hG.memF.1 z hzI).mono' ((haesmG.mul hφmeas.aestronglyMeasurable).pow 2)
      (Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_z α k G z θ 0 (Nat.zero_le k))
  have hsqH : MeasureTheory.Integrable (fun θ => (H z θ * (Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hH.memF.1 z hzI).mono' ((haesmH.mul hφmeas.aestronglyMeasurable).pow 2)
      (Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_z α k H z θ 0 (Nat.zero_le k))
  -- Integrability of the two slices against `sinθcos²θ`.
  have hIntG : MeasureTheory.Integrable (fun θ => G z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.PhiStar.Honesty.CptApp.LamEst.integrable_mul_sinCos2 hz haesmG hsqG
  have hIntH : MeasureTheory.Integrable (fun θ => H z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.PhiStar.Honesty.CptApp.LamEst.integrable_mul_sinCos2 hz haesmH hsqH
  -- `F_*(G - H) = F_*(G) - F_*(H) = 0 - 0 = 0`.
  rw [Work.Elliptic.Fstar]
  rw [show (∫ θ in Work.Spaces.Iθ, (G z θ - H z θ) * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (G z θ * Work.Elliptic.sinCos2 θ
          - H z θ * Work.Elliptic.sinCos2 θ) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_sub hIntG hIntH]
  rw [show (∫ θ in Work.Spaces.Iθ, G z θ * Work.Elliptic.sinCos2 θ)
        = Work.Elliptic.Fstar G z from rfl,
    show (∫ θ in Work.Spaces.Iθ, H z θ * Work.Elliptic.sinCos2 θ)
        = Work.Elliptic.Fstar H z from rfl]
  rw [hG.orthF z hz, hH.orthF z hz, sub_zero]

end Work.FTS.PhiStar.Honesty.EllWeakAux
